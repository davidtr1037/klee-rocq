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

void test_ashr_3(int x) {
    int y = 1 >> x;
}

void test_ashr_4() {
    int x = klee_make_symbolic_int32();
    klee_assume_bool(x < 32);
    klee_assume_bool(x >= 0);
    int y = 1 >> x;
}

void test_lshr_1(unsigned x) {
    unsigned y = x >> 2;
}

void test_lshr_2() {
    unsigned x = klee_make_symbolic_int32();
    unsigned y = x >> 7;
}

void test_lshr_3(unsigned x) {
    unsigned y = (unsigned)(1) >> x;
}

void test_lshr_4() {
    unsigned x = klee_make_symbolic_int32();
    klee_assume_bool(x < 32);
    klee_assume_bool(x >= 0);
    unsigned y = 1 >> x;
}

int main() {
    test_ashr_1(100);
    test_ashr_2();
    test_ashr_3(10);
    test_ashr_4();
    test_lshr_1(100);
    test_lshr_2();
    test_lshr_3(10);
    test_lshr_4();
    return 0;
}
