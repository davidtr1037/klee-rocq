# KLEE-Rocq
This tool is an extension of KLEE, which generates safety proof in Rocq.
When the symbolic execution of the given program is exhaustive, our tool generates an additional Rocq file (.v file),
in which the main theorem states that the program under test is safe with respect to the concrete LLVM semantics.
To validate the generated proof, one can use _coqc_.

_Note: The current version supports a subset of LLVM with integers._

## Build
The current version was tested with LLVM 13 (and should work with earlier versions as well).
The install the dependencies, follow the instructions [here](https://klee-se.org/build/build-from-source/).
To build our extension of KLEE:
```
mkdir <klee-build-dir>
cd <klee-build-dir>
CXXFLAGS="-std=c++17" cmake \
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
To build our Rocq project, run the following command-line:
```
cd <klee-src-dir>/rocq
make
```

## Usage
Consider the following program:
```
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

#define N 100

bool is_prime_naive(unsigned n) {
    if (n < 2) {
        return false;
    }

    for (int i = 2; i < n; i++) {
        if (n % i == 0) {
            return false;
        }
    }

    return true;
}

bool is_prime_fast(unsigned n) {
    if (n < 4) {
        return n == 2 || n == 3;
    }
    
    if (n % 2 == 0 || n % 3 == 0)  {
        return false;
    }

    for (int i = 5; i * i <= n; i += 2) {
        if (n % i == 0) {
            return false;
        }
    }

    return true;
}

int main() {
    unsigned n = klee_make_symbolic_int32();
    klee_assume_bool(n < N);
    assert(is_prime_naive(n) == is_prime_fast(n));

    return 0;
}
```
To compile it, use the following command-line:
```
clang -c -g -emit-llvm -Xclang -disable-O0-optnone -I <klee-src-dir>/include <c_file> -o <bc_file>
opt -mem2reg <bc_file> -o <bc_file>
```
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
