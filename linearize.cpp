#include <llvm/IR/PassManager.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/PassPlugin.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/PostDominators.h>

#include <llvm/Support/Debug.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/RandomNumberGenerator.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

#include <algorithm>
#include <utility>
#include <vector>
#include <list>
#include <unordered_map>

using namespace llvm;

namespace {

enum labelkind {
	LBL_FALLTHROUGH,
	LBL_FRESH,
};

struct label {
	labelkind kind;
	size_t fresh;
};

struct Linearize : public PassInfoMixin<Linearize> {
	PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);
	bool runOnFunction(Function &F);

	std::pair<size_t, Align> getDiscardSizeAlign(Function &F, const DataLayout &DataLayout);
	size_t getLabels(Function &F);
	void shuffleBlocks(Function &F, size_t numlbl);
	void eliminatePhis(Function &F);
	void resolveContinuityErrors(Function &F);
	Value *prepareBlock(BasicBlock &bb, Value *on, AllocaInst *selector, label label, AllocaInst *discard);

	template <typename T>
	void linearizeIns(T *ins, Value *on, AllocaInst *discard);

	std::unordered_map<BasicBlock *, struct label> labels;
	std::unique_ptr<RandomNumberGenerator> rng;
	Function *NopFun;
};
}

void Linearize::resolveContinuityErrors(Function &F) {
	SmallVector<Instruction *> tofix;
	for (auto it = ++F.begin(); it != F.end(); ++it) {
		BasicBlock *home = &*it;
		for (Instruction &ins : *it) {
			for (Use &u : ins.uses()) {
				Instruction *iu = cast<Instruction>(u.getUser());
				PHINode *pu = dyn_cast<PHINode>(iu);
				if (pu) {
					if (pu->getIncomingBlock(u) == home) {
						continue;
					}
					tofix.push_back(&ins);
					break;
				}
				if (iu->getParent() == home)
					continue;
				tofix.push_back(&ins);
				break;
			}
		}
	}

	Instruction *first_ins = F.begin()->getFirstNonPHIOrDbg();
	SmallVector<Use *> uses;
	std::unordered_map<BasicBlock *, LoadInst *> bbLoadMap;
	bbLoadMap.reserve(100);
	for (Instruction *ins : tofix) {
		dbgs() << "fixing ";
		ins->print(dbgs());
		dbgs() << "\n";
		Type *ty = ins->getType();
		BasicBlock *home = ins->getParent();
		AllocaInst *alloc = new AllocaInst(ty, 0, Twine(ins->getName(), ".ins.rewrite"), first_ins);

		new StoreInst(ins, alloc, ins->getNextNonDebugInstruction());

		uses.clear();
		bbLoadMap.clear();
		for (Use &u : ins->uses()) {
			Instruction *iu = cast<Instruction>(u.getUser());
			assert(!isa<PHINode>(iu));

			if (iu->getParent() != home)
				uses.push_back(&u);
		}

		for (Use *u : uses) {
			Instruction *uins = cast<Instruction>(u->getUser());
			dbgs() << "rewriting use ";
			uins->print(dbgs());
			LoadInst *load = nullptr;
			BasicBlock *bb = uins->getParent();
			auto it = bbLoadMap.find(bb);
			if (it != bbLoadMap.end()) {
				load = it->second;
				dbgs() << "in " << bb->getName() << " (shared)\n";
			} else {
				load = new LoadInst(ty, alloc, Twine(ins->getName(), ".ins.use"), cast<Instruction>(bb->getFirstNonPHIOrDbg()));
				bbLoadMap.emplace(bb, load);
				dbgs() << "in " << bb->getName() << " (fresh)\n";
			}
			assert(load != nullptr);
			u->set(load);
		}
	}
}

/**
 * Rewrites phi nodes as memory allocation + access
 * needs to be run before memory access are rewritten
 */
void Linearize::eliminatePhis(Function &F) {
	std::vector<PHINode *> phis;
	for (BasicBlock &bb : F) {
		for (Instruction &ins : bb) {
			PHINode *phi = dyn_cast<PHINode>(&ins);
			if (phi)
				phis.push_back(phi);
		}
	}

	Instruction *first_ins = F.begin()->getFirstNonPHI();

	SmallVector<Use *> uses;
	std::unordered_map<BasicBlock *, LoadInst *> bbLoadMap;
	bbLoadMap.reserve(100);
	for (PHINode *phi : phis) {
		Type *ty = phi->getType();
		dbgs() << "rewriting ";
		phi->print(dbgs());
		dbgs() << "\n";
		AllocaInst *alloc = new AllocaInst(ty, 0, Twine(phi->getName(), ".phi.rewrite"), first_ins);
		for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
			// skip duplicate edges
			BasicBlock *bb = phi->getIncomingBlock(i);
			if (phi->getBasicBlockIndex(bb) != i) continue;
			Value *v = phi->getIncomingValue(i);
			// ignore self references
			if (dyn_cast<PHINode>(v) == phi) continue;
			// store will be rewritten using on later on
			new StoreInst(v, alloc, bb->getTerminator());
		}

		LoadInst *phi_replace = new LoadInst(ty, alloc, phi->getName(), phi);
		phi->replaceAllUsesWith(phi_replace);
		phi->eraseFromParent();
	}
}

void Linearize::shuffleBlocks(Function &F, size_t numlbl) {
	std::vector<BasicBlock*> bbs;
	std::vector<std::pair<BasicBlock *, BasicBlock*> > fallthroughs;
	bbs.reserve(numlbl);
	fallthroughs.reserve(F.size() - numlbl);
	BasicBlock *last = nullptr;

	dbgs() << "shuffling\n";

	for (auto it = ++F.begin(); it != F.end(); ++it) {
		if (labels.at(&*it).kind == LBL_FRESH) {
			bbs.emplace(bbs.begin() + ((*rng)() % (bbs.size() + 1)), &*it);
		} else {
			fallthroughs.emplace_back(&*it, last);
		}
		last = &*it;
	}

	dbgs() << "shuffled\n";

	BasicBlock *ip = &*--F.end();
	for (BasicBlock *bb : bbs) {
		bb->moveBefore(ip);
	}
	for (std::pair<BasicBlock *, BasicBlock *> &ft : fallthroughs) {
		ft.first->moveAfter(ft.second);
	}
}

size_t Linearize::getLabels(Function &F) {
	labels.reserve(F.size());

	BasicBlock *last = nullptr;

	size_t numlbl = 0;

	auto it = std::next(F.begin());

	bool first = true;
	for (; it != F.end(); ++it) {
		BasicBlock *bb = &*it;
		if (first) {
			dbgs() << bb->getName() << ": fresh\n";
			labels[bb] = label{LBL_FRESH, (*rng)()};
			last = bb;
			first = false;
			++numlbl;
			continue;
		}

		if (last == bb->getUniquePredecessor()) {
			dbgs() << bb->getName() << ": fallthrough\n";
			labels[bb] = label{LBL_FALLTHROUGH};
			last = bb;
			continue;
		}

		dbgs() << bb->getName() << ": fresh\n";
		labels[bb] = label{LBL_FRESH, (*rng)()};
		last = bb;
		++numlbl;
	}

	return numlbl;
}

template <>
void Linearize::linearizeIns<LoadInst>(LoadInst *ins, Value *on, AllocaInst *discard) {
	Value *ptr = ins->getPointerOperand();
	if (!isa<Instruction>(ptr))
		return;
	if (isa<AllocaInst>(ptr))
		return;
	IRBuilder<> Builder(ins);
	*ins->op_begin() = Builder.CreateSelect(
		on,
		ins->getPointerOperand(),
		Builder.CreatePointerCast(discard, ins->getPointerOperandType()));
}

template <>
void Linearize::linearizeIns<StoreInst>(StoreInst *ins, Value *on, AllocaInst *discard) {
	IRBuilder<> Builder(ins);
	*std::next(ins->op_begin()) = Builder.CreateSelect(
		on,
		ins->getPointerOperand(),
		Builder.CreatePointerCast(discard, ins->getPointerOperandType()));
}

template <>
void Linearize::linearizeIns<AtomicCmpXchgInst>(AtomicCmpXchgInst *ins, Value *on, AllocaInst *discard) {
	IRBuilder<> Builder(ins);
	*ins->op_begin() = Builder.CreateSelect(
		on,
		ins->getPointerOperand(),
		Builder.CreatePointerCast(discard, ins->getPointerOperand()->getType()));
}

template <>
void Linearize::linearizeIns<AtomicRMWInst>(AtomicRMWInst *ins, Value *on, AllocaInst *discard) {
	IRBuilder<> Builder(ins);
	*ins->op_begin() = Builder.CreateSelect(
		on,
		ins->getPointerOperand(),
		Builder.CreatePointerCast(discard, ins->getPointerOperand()->getType()));
}

template <>
void Linearize::linearizeIns<CallInst>(CallInst *ins, Value *on, AllocaInst *discard) {
	IRBuilder<> Builder(ins);
	ins->setCalledOperand(
		Builder.CreateSelect(on,
			ins->getCalledOperand(),
			Builder.CreatePointerCast(NopFun, ins->getCalledOperand()->getType())));
}

template <>
void Linearize::linearizeIns<GetElementPtrInst>(GetElementPtrInst *ins, Value *on, AllocaInst *discard) {
	ins->setIsInBounds(false);
}

template <>
void Linearize::linearizeIns<BinaryOperator>(BinaryOperator *op, Value *on, AllocaInst *discard) {
	IRBuilder<> Builder(op);
	Type *typ = op->getType();
	switch(op->getOpcode()) {
	case Instruction::SDiv:
	case Instruction::UDiv:
	case Instruction::SRem:
	case Instruction::URem:
		if (isa<Constant>(op->getOperand(1))) return;
		op->setOperand(1,
			Builder.CreateOr(op->getOperand(1),
				Builder.CreateZExtOrTrunc(
					Builder.CreateXor(on, ConstantInt::getTrue(on->getType()))
					, typ)));
		break;
	case Instruction::Shl:
	case Instruction::AShr:
	case Instruction::LShr:
		if (isa<Constant>(op->getOperand(1))) return;
		op->setOperand(1,
			Builder.CreateAnd(op->getOperand(1), ConstantInt::get(typ, typ->getIntegerBitWidth() - 1)));
		break;
	default:
		break;
	}
}

Value *Linearize::prepareBlock(BasicBlock &bb, Value *on, AllocaInst *selector, label label, AllocaInst *discard) {
	std::vector<Instruction *> todo;
	std::vector<CallInst *> lifetimeMarker;
	for (Instruction &ins : bb) {
		// TODO elaborate intrinsic handling
		CallInst *ci = dyn_cast<CallInst>(&ins);
		if (ci && (ci->getIntrinsicID() == Intrinsic::lifetime_start ||
				ci->getIntrinsicID() == Intrinsic::lifetime_end)) {
			lifetimeMarker.push_back(ci);
			dbgs() << "removing Lifetime Marker ";
			ci->print(dbgs());
			dbgs() << "\n";
			continue;
		} else if (ci && ci->getIntrinsicID() != Intrinsic::not_intrinsic) {
			bool removed = false;
			for (Use &u : ci->args()) {
				if (isa<MetadataAsValue>(u.get())) {
					dbgs() << "removing intrinsic with metadata parameter: \n\t";
					ci->print(dbgs());
					dbgs() << "\n";
					lifetimeMarker.push_back(ci);
					removed = true;
					break;
				}
			}
			if (removed)
				continue;

			dbgs() << "intrinsic was not removed: \n\t";
			ci->print(dbgs());
			dbgs() << "\n";
//			llvm_unreachable("call to intrinsic within function");
		}

		if (isa<LoadInst>(&ins) ||
			isa<StoreInst>(&ins) ||
			isa<AtomicCmpXchgInst>(&ins) ||
			isa<AtomicRMWInst>(&ins) ||
			isa<GetElementPtrInst>(&ins) ||
			//isa<PHINode>(&ins) ||
			(ci && ci->getIntrinsicID() == Intrinsic::not_intrinsic) ||
//			ci ||
			ins.getOpcode() == Instruction::SDiv ||
			ins.getOpcode() == Instruction::UDiv ||
			ins.getOpcode() == Instruction::URem ||
			ins.getOpcode() == Instruction::SRem ||
			ins.getOpcode() == Instruction::Shl ||
			ins.getOpcode() == Instruction::AShr ||
			ins.getOpcode() == Instruction::LShr) {
			todo.push_back(&ins);
		}
	}

	for (CallInst *ins : lifetimeMarker) {
		ins->eraseFromParent();
	}

	if (label.kind == LBL_FRESH) {
		IRBuilder<> Builder(bb.getFirstNonPHIOrDbgOrLifetime());
		on = Builder.CreateICmpEQ(
			Builder.CreateLoad(selector->getAllocatedType(), selector),
			Builder.getInt64(label.fresh), Twine(bb.getName(), ".on"));
	}

	for (Instruction *ins : todo) {
		LoadInst *li = dyn_cast<LoadInst>(ins);
		if (li) {
			linearizeIns(li, on, discard);
			continue;
		}

		StoreInst *si = dyn_cast<StoreInst>(ins);
		if (si) {
			linearizeIns(si, on, discard);
			continue;
		}

		AtomicCmpXchgInst *xchg = dyn_cast<AtomicCmpXchgInst>(ins);
		if (xchg) {
			linearizeIns(xchg, on, discard);
			continue;
		}

		AtomicRMWInst *rmw = dyn_cast<AtomicRMWInst>(ins);
		if (rmw) {
			linearizeIns(rmw, on, discard);
			continue;
		}

		CallInst *call = dyn_cast<CallInst>(ins);
		if (call) {
			linearizeIns(call, on, discard);
			continue;
		}

		BinaryOperator *bop = dyn_cast<BinaryOperator>(ins);
		if (bop) {
			linearizeIns(bop, on, discard);
			continue;
		}

		GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(ins);
		if (gep) {
			linearizeIns(gep, on ,discard);
			continue;
		}
	}

	return on;
}

std::pair<size_t, Align> Linearize::getDiscardSizeAlign(Function &F, const DataLayout &DataLayout) {
	size_t size = DataLayout.getPointerSize();
	Align align = DataLayout.getPointerPrefAlignment();
	for (BasicBlock &bb : F) {
		for (Instruction &ins : bb) {
			StoreInst *si = dyn_cast<StoreInst>(&ins);
			if (si) {
				si->print(dbgs());
				dbgs() << "\n";
				Type *t = si->getValueOperand()->getType();
				size_t tmp = DataLayout.getTypeAllocSize(t);
				Align tmpalign = DataLayout.getValueOrABITypeAlignment(si->getAlign(), t);
				if (tmp > size)
					size = tmp;
				if (tmpalign > align)
					align = tmpalign;
				continue;
			}

			LoadInst *li = dyn_cast<LoadInst>(&ins);
			if (li) {
				li->print(dbgs());
				dbgs() << "\n";
				size_t tmp = DataLayout.getTypeAllocSize(li->getType());
				Align tmpalign = DataLayout.getValueOrABITypeAlignment(li->getAlign(), li->getType());
				if (tmp > size)
					size = tmp;
				if (tmpalign > align)
					align = tmpalign;
				continue;
			}

			AtomicCmpXchgInst *cmpXchg = dyn_cast<AtomicCmpXchgInst>(&ins);
			if (cmpXchg) {
				cmpXchg->print(dbgs());
				dbgs() << "\n";
				Type *t = cmpXchg->getNewValOperand()->getType();
				size_t tmp = DataLayout.getTypeAllocSize(t);
				Align tmpalign = DataLayout.getValueOrABITypeAlignment(cmpXchg->getAlign(), t);
				if (tmp > size)
					size = tmp;
				if (tmpalign > align)
					align = tmpalign;
				continue;
			}

			AtomicRMWInst *rmw = dyn_cast<AtomicRMWInst>(&ins);
			if (rmw) {
				rmw->print(dbgs());
				dbgs() << "\n";
				size_t tmp = DataLayout.getTypeAllocSize(rmw->getType());
				Align tmpalign = DataLayout.getValueOrABITypeAlignment(rmw->getAlign(), rmw->getType());
				if (tmp > size)
					size = tmp;
				if (tmpalign > align)
					align = tmpalign;
			}
		}
	}

	return {size, align};
}

bool Linearize::runOnFunction(Function &F) {
	dbgs() << "linearizing " << F.getName() << "\n";
	labels.clear();

	auto it = F.getEntryBlock().begin();
	while(isa<AllocaInst>(it) ||
		(isa<CallInst>(it) && cast<CallInst>(it)->getIntrinsicID() != Intrinsic::not_intrinsic) ||
		isa<StoreInst>(it)) {
		++it;
	}

	// check state of function
	// check terminators
	for (BasicBlock &bb : F) {
		Instruction *ins = bb.getTerminator();
		if (!isa<BranchInst>(ins) &&
			!isa<ReturnInst>(ins)) {
			dbgs() << "incompatible terminator: ";
			ins->print(dbgs());
			return false;
		}

	}

	// search for allocas within the function body
	for (auto it2 = it; it2 != F.getEntryBlock().end(); ++it2) {
		if (isa<AllocaInst>(&*it2)) {
			dbgs() << "found alloca within function body, aborting\n";
			return false;
		}
	}

	for (auto it = ++F.begin(); it != F.end(); ++it) {
		for (Instruction &ins : *it) {
			if (isa<AllocaInst>(&ins)) {
				dbgs() << "found alloca within function body, aborting\n";
				return false;
			}
		}
	}

	// TODO: eliminate phis
	eliminatePhis(F);

	// create auxiliary local variables
	std::pair<size_t, Align> discardSizeAlign = getDiscardSizeAlign(F, F.getParent()->getDataLayout());

	Instruction *split = &*it;
	AllocaInst *discard;
	AllocaInst *selector;
	AllocaInst *retval;
	{
		IRBuilder<> Builder(F.begin()->getFirstNonPHI());
		discard = Builder.CreateAlloca(ArrayType::get(Builder.getInt8Ty(), discardSizeAlign.first), nullptr, "discard");
		discard->setAlignment(discardSizeAlign.second);
		selector = Builder.CreateAlloca(Builder.getInt64Ty(), nullptr, "selector");
		if (!F.getReturnType()->isVoidTy())
			retval = Builder.CreateAlloca(F.getReturnType(), nullptr, "retval");
	}

	SplitBlock(&F.getEntryBlock(), split);

	F.print(dbgs());
	dbgs() << "\n";

	size_t numlbl = getLabels(F);

	// TODO: shuffle blocks
	shuffleBlocks(F, numlbl);

	resolveContinuityErrors(F);

	F.print(dbgs());
	dbgs() << "\n";

	size_t finlbl = (*rng)();
	Value *on = nullptr;
	for (auto bbit = ++F.begin(); bbit != F.end(); ++bbit) {
		on = prepareBlock(*bbit, on, selector, labels[&*bbit], discard);
		dbgs() << "fixing continuation in " << bbit->getName() << "\n";
		BranchInst *br = dyn_cast<BranchInst>(bbit->getTerminator());
		IRBuilder<> Builder(bbit->getTerminator());
		if (br) {
			label tl = labels[br->getSuccessor(0)];
			if (br->isConditional()) {
				label fl = labels[br->getSuccessor(1)];
				if (tl.kind != LBL_FALLTHROUGH && fl.kind != LBL_FALLTHROUGH) {
					Builder.CreateStore(
						Builder.CreateSelect(
							br->getCondition(),
							Builder.getInt64(tl.fresh),
							Builder.getInt64(fl.fresh)),
						Builder.CreateSelect(
							on,
							selector,
							Builder.CreatePointerCast(discard, Builder.getInt64Ty()->getPointerTo())));
					continue;
				}
				Value *ptr;
				size_t val;
				if (tl.kind == LBL_FRESH) {
					ptr = Builder.CreateSelect(Builder.CreateAnd(br->getCondition(), on)
						, selector
						, Builder.CreatePointerCast(discard, Builder.getInt64Ty()->getPointerTo()));
					val = tl.fresh;
					on = Builder.CreateAnd(on, Builder.CreateNot(br->getCondition()));
				} else {
					assert(fl.kind == LBL_FRESH);
					ptr = Builder.CreateSelect(Builder.CreateOr(br->getCondition(), Builder.CreateNot(on))
						, Builder.CreatePointerCast(discard, Builder.getInt64Ty()->getPointerTo())
						, selector);
					val = fl.fresh;
					on = Builder.CreateAnd(on, br->getCondition());
				}

				Builder.CreateStore(Builder.getInt64(val), ptr);
				continue;
			}

			if (tl.kind == LBL_FRESH && on == nullptr) {
				Builder.CreateStore(Builder.getInt64(tl.fresh), selector);
				continue;
			}

			if (tl.kind == LBL_FRESH) {
				Builder.CreateStore(Builder.getInt64(tl.fresh),
					Builder.CreateSelect(
						on,
						selector,
						Builder.CreatePointerCast(discard, Builder.getInt64Ty()->getPointerTo())));
				continue;
			}

			assert(tl.kind == LBL_FALLTHROUGH);
			continue;
		}

		dbgs() << "rewriting return instruction\n";
		ReturnInst *ret = cast<ReturnInst>(bbit->getTerminator());
		Value *rv = ret->getReturnValue();
		if (rv) {
			Builder.CreateStore(rv,
				Builder.CreateSelect(on, retval, Builder.CreatePointerCast(discard, rv->getType()->getPointerTo())));
		}
		Builder.CreateStore(Builder.getInt64(finlbl),
			Builder.CreateSelect(on, selector, Builder.CreatePointerCast(discard, Builder.getInt64Ty()->getPointerTo())));
	}

	// create common exit block
	BasicBlock *commonFin = BasicBlock::Create(F.getParent()->getContext(), "fin", &F);
	{
		IRBuilder<> Builder(commonFin);
		if (F.getReturnType()->isVoidTy()) {
			Builder.CreateRetVoid();
		} else {
			Builder.CreateRet(
				Builder.CreateLoad(F.getReturnType(), retval, "retval"));
		}
	}

	// merge fallthroughs
	{
		BasicBlock *last = &*++F.begin();
		SmallVector<BasicBlock *, 64> todel;

		for (auto it = ++++F.begin(); it != --F.end(); ++it) {
			if (labels[&*it].kind == LBL_FRESH) {
				last = &*it;
				continue;
			}

			dbgs() << "merging fallthrough " << it->getName() << " into " << last->getName() << "\n";

			// merge bb
			last->getTerminator()->eraseFromParent();
			last->getInstList().splice(last->end(), it->getInstList(), it->begin(), it->end());
			todel.push_back(&*it);
		}

		for (BasicBlock *bb : todel)
			bb->eraseFromParent();
	}

	// merge bbs
	{
		std::vector<BasicBlock*> bbs;
		bbs.reserve(F.size() - 2);

		// accumulate instruction in it
		BasicBlock *tar = BasicBlock::Create(F.getParent()->getContext(), "merged", &F, &*std::next(F.begin()));

		// rewire branch from entry block
		new StoreInst(
			ConstantInt::get(IntegerType::get(F.getParent()->getContext(), 64), labels[F.begin()->getSingleSuccessor()].fresh, false)
			, selector
			, F.begin()->getTerminator());
		cast<BranchInst>(F.begin()->getTerminator())->setSuccessor(0, tar);

		std::list<BasicBlock *> bblist;
		size_t num_inst = 0;
		for (auto it = std::next(std::next(F.begin())); std::next(it) != F.end(); ++it) {
			it->getTerminator()->eraseFromParent();
			num_inst += it->size();
			bblist.push_back(&*it);
		}

//		dbgs() << "built list\n";

		while (num_inst) {
//			dbgs() << "instructions left: " << num_inst << "\n";
			auto it = bblist.begin();
			size_t pos = (*rng)() % num_inst;
			while (pos > (*it)->size()) {
//				dbgs() << "instructions left (" << (*it)->getName() << "): " << (*it)->size() << "\n";
				pos -= (*it)->size();
				++it;
			}
			/*
			for (size_t pos = (*rng)() % num_inst; pos > (*it)->size(); pos -= (*it)->size()) {
				++it;
			}*/
			size_t left = (*it)->size();
			size_t num = std::min(left, 3 + (*rng)() % 3);
//			dbgs() << "taking " << num << " instructions from " << (*it)->getName() << "\n";
			auto ei = (*it)->begin();
			for (size_t i = 0; i < num; ++i) {
				assert(ei != (*it)->end());
				ei = std::next(ei);
			}
			//std::advance(ei, num);
			tar->getInstList().splice(tar->end(), (*it)->getInstList(), (*it)->begin(), ei);
			num_inst -= num;
			if (num == left) {
//				dbgs() << "block " << (*it)->size() << " is depelted - erasing\n";
				BasicBlock *todel = *it;
				bblist.erase(it);
				todel->eraseFromParent();
			}
		}

		IRBuilder<> Builder(tar);
		Builder.CreateCondBr(
			Builder.CreateICmpEQ(
				Builder.getInt64(finlbl),
				Builder.CreateLoad(Builder.getInt64Ty(), selector, "tag"),
				"isExit"),
			commonFin,
			tar);
	}

	F.print(dbgs());
	dbgs() << "\n";

	return true;
}

PreservedAnalyses Linearize::run(Module &M, ModuleAnalysisManager &MAM) {
	SmallString<64> rngstr = {"obf.linearize"};
	rng = M.createRNG(rngstr);

	NopFun = Function::Create(FunctionType::get(IntegerType::get(M.getContext(), 8)->getPointerTo(), {}, true), GlobalValue::LinkOnceODRLinkage, "__obf_nop", M);
	NopFun->setVisibility(GlobalValue::HiddenVisibility);

	for (Function &F : M) {
		if (F.isDeclaration())
			continue;

		runOnFunction(F);
	}

	{
		BasicBlock *bb = BasicBlock::Create(M.getContext(), "entry", NopFun);
		ReturnInst::Create(M.getContext(), Constant::getNullValue(NopFun->getReturnType()), bb);
	}

	return PreservedAnalyses::none();
}

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
	return {LLVM_PLUGIN_API_VERSION, "linearize-oot", "0.3", [](PassBuilder &PB) {
		PB.registerOptimizerLastEPCallback([](ModulePassManager &MPM, OptimizationLevel Ol) {
			MPM.addPass(Linearize());
		});
	}};
}
