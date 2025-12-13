#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>

#include <klee/klee.h>

void f1() {
    uint32_t x = 0;
    uint32_t y = klee_make_symbolic_int32();
    uint64_t a;
    a = x;
    a = y;
}

void f2() {
    int32_t x = 0;
    int32_t y = klee_make_symbolic_int32();
    int64_t a;
    a = x;
    a = y;
}

int main() {
    f1();
    f2();
    return 0;
}
