# KLEE-Rocq
This tool is an extension of KLEE, which generates safety proof in Rocq.
When the symbolic execution of the given program is exhaustive, our tool generates an additional Rocq file (_.v_ file),
in which the main theorem states that the program under test is safe with respect to the concrete LLVM semantics.
To validate the generated proof, one can use _coqc_.

_Note: The current version supports a subset of LLVM with integers._

## Build
The current version was tested with LLVM 13 (and should work with earlier versions as well).

To build our extension of KLEE:
```
mkdir <klee-build-dir>
cd <klee-build-dir>
CXXFLAGS="-fno-rtti -g" cmake \
    -DENABLE_SOLVER_STP=ON \
    -DENABLE_POSIX_RUNTIME=ON \
    -DKLEE_UCLIBC_PATH=<klee-uclibc-dir> \
    -DKLEE_RUNTIME_BUILD_TYPE=Release+Asserts \
    -DENABLE_UNIT_TESTS=OFF \
    -DENABLE_SYSTEM_TESTS=ON \
    -DENABLE_TCMALLOC=ON \
    ../<klee-src-dir>
make -j4
```

## Usage
To run our tool with proof generation, use the following command-line:
```
klee \
  -libc=klee \
  -search=dfs \
  -kdalloc=0 \
  -linear-deterministic-allocation \
  -allocate-external-objects=0 \
  -allocate-function-objects=0 \
  -allocate-global-objects=1 \
  -rewrite-equalities=0 \
  -simplify-using-equalities=0 \
  -generate-proof \
  -optimize-proof \
  -cache-pc-expr \
  -cache-register-expr \
  -cache-stack-expr \
  -cache-sym-names \
  <bc_file>
```
This will create a well-known `<klee-out>` directory,
and the generated proof will be located at `<klee-out>/proof.v`.
To validate the proof, run the following command:
```
coqc -Q <klee-src-dir>/coq SE <klee-out>/proof.v
```
