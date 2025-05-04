# linearize

This Plugin performs Control Flow Linearization

## Building

For building the obfuscator you habe two options:
1. build into llvm
2. standalone pass plugin

This obfuscation has only been tested on linux.
both ways of building the obfuscation may work on Mac as well.
On Windows only building the pass into llvm has a chance to succeed as to my knowledge pass plugins are not supported on windows in general.

### build into llvm

First checkout version 20.1.4 of [llvm-project](https://github.com/llvm/llvm-project).
Then apply linearize\_in\_tree.patch in llvm-project, run cmake, and lastly build using ninja.

```Bash
git clone --depth 1 --branch llvmorg-20.1.4 https://github.com/llvm/llvm-project
cd llvm-project
patch -p1 < ../linearize_in_tree.patch
cd -
mkdir build
cd build
cmake -DLLVM_ENABLE_PROJECTS=clang -DLLVM_ENABLE_ASSERTIONS=ON -G Ninja ../llvm-project/llvm
ninja
ninja install
```

### build as pass plugin

Make sure you have llvm version 20.1.4 installed (minor version missmatches often times don't matter).
If multiple llvm version are installed find the path to the cmake directory of llvm 20.1.4.
Replace the path of the LLVM\_DIR option with the pass to your installation

```Bash
mkdir build
cd build
cmake -DLLVM_DIR=/usr/lib/cmake/llvm/ -G Ninja ..
ninja
ninja install
```

## Usage

Usage depends on the build type

### build into llvm

Just invoke clang with the `-flinearize-cfg` option on `O1` or higher.
In `opt` the pass is named `--linearize`.

Path application should be immediatly visible as the pass is very noise currently

### pass plugin

Just invoke clang with the `-fpass-plugin=Linearize.so` option on `O1` or higher.
If plugin is not found you may need to use the full path to the plugin or make sure
the directory containing the plugin is part of the library search path `LD_LIBRARY_PATH`
