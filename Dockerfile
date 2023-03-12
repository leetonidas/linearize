FROM debian:bullseye as builder

RUN apt-get update && \
    apt-get install --no-install-recommends -y \
    	build-essential \
    	ca-certificates \
    	git \
    	python3 \
    	cmake \
    	ninja-build \
    && rm -rf /var/lib/apt/lists/*

RUN useradd -ms /bin/bash user
USER user
WORKDIR /home/user

RUN git clone --depth 1 --branch llvmorg-15.0.6 https://github.com/llvm/llvm-project.git && \
    mkdir llvm-project/build && \
    cd llvm-project/build && \
    cmake -DLLVM_ENABLE_PROJECTS=clang -DLLVM_ENABLE_DOXYGEN=OFF -DLLVM_TARGETS_TO_BUILD="X86;ARM;AArch64;RISCV;WebAssembly" \
        -DCMAKE_INSTALL_PREFIX="/home/user/.local" -DCMAKE_BUILD_TYPE=Release \
        -DLLVM_ENABLE_ASSERTIONS=ON -G Ninja ../llvm && \
    ninja

ADD linearize_in_tree.patch llvm-project

RUN cd llvm-project && patch -p1 < linearize_in_tree.patch

RUN cd llvm-project/build && \
    ninja rebuild_cache && \
    ninja install

#ADD linearize /home/user/linearize
#
#RUN mkdir build && \
#	cd build && \
#	cmake -DLLVM_DIR=/home/user/.local/lib/cmake/llvm \
#		-DCMAKE_INSTALL_PREFIX="/home/user/.local" -G Ninja ../linearize && \
#	ninja install

FROM debian:bullseye as obfuscator
RUN apt-get update && \
    apt-get install --no-install-recommends -y \
    	build-essential \
    	ca-certificates \
    	git \
    	python3 \
    	cmake \
    	ninja-build \
    && rm -rf /var/lib/apt/lists/*

RUN useradd -ms /bin/bash user
USER user
WORKDIR /home/user

COPY --from=builder /home/user/.local /home/user/.local
ENV PATH="/home/user/.local/bin:$PATH"
ENV LD_LIBRARY_PATH="/home/user/.local/lib:$LD_LIBRARY_PATH"
