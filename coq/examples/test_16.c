#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>

#include <klee/klee.h>

void test_ashr_1(int x) {
    int y = x >> 2;
}

void test_ashr_2() {
    int x = klee_make_symbolic_int32();
    int y = x >> 7;
}

void test_lshr_1(unsigned x) {
    unsigned y = x >> 2;
}

void test_lshr_2() {
    unsigned x = klee_make_symbolic_int32();
    unsigned y = x >> 7;
}

int main() {
    test_ashr_1(100);
    test_ashr_2();
    test_lshr_1(100);
    test_lshr_2();
    return 0;
}
