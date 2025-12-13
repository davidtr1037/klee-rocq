#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>

#include <klee/klee.h>

void f1(unsigned x) {
    unsigned y = x & 10;
}

void f2() {
    unsigned x = klee_make_symbolic_int32();
    unsigned y = x & 10;
}

void f3() {
    unsigned x = klee_make_symbolic_int32();
    unsigned y = 10 & x;
}

int main() {
    f1(100);
    f2();
    f3();
    return 0;
}
