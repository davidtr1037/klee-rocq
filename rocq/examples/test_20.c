#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>

#include <klee/klee.h>

void test_udiv_1(unsigned x) {
    unsigned y = x / 2;
}

void test_udiv_2() {
    unsigned x = klee_make_symbolic_int32();
    unsigned y = x / 2;
}

void test_udiv_3(unsigned x) {
    unsigned y = 2 / x;
}

void test_udiv_4() {
    unsigned x = klee_make_symbolic_int32();
    klee_assume_bool(x > 0);
    unsigned y = 2 / x;
}

void test_sdiv_1(int x) {
    int y = x / 2;
}

void test_sdiv_2() {
    int x = klee_make_symbolic_int32();
    int y = x / 2;
}

void test_sdiv_3(unsigned x) {
    int y = 2 / x;
}

void test_sdiv_4() {
    int x = klee_make_symbolic_int32();
    klee_assume_bool(x > 0);
    int y = 2 / x;
}

void test_sdiv_5() {
    int x = klee_make_symbolic_int32();
    klee_assume_bool(x != 0);
    int y = 100 / x;
}

void test_sdiv_6() {
    int x = klee_make_symbolic_int32();
    klee_assume_bool(x != 0);
    klee_assume_bool(x != -1);
    int y = INT32_MIN / x;
}

void test_sdiv_7() {
    int x = klee_make_symbolic_int32();
    klee_assume_bool(x != INT32_MIN);
    int y = x / -1;
}

void test_sdiv_8() {
    int x = klee_make_symbolic_int32();
    int y = klee_make_symbolic_int32();
    klee_assume_bool(x != INT32_MIN);
    klee_assume_bool(y != 0);
    klee_assume_bool(y != -1);
    int z = x / y;
}

int main() {
    test_udiv_1(100);
    test_udiv_2();
    test_udiv_3(100);
    test_udiv_4();

    test_sdiv_1(100);
    test_sdiv_2();
    test_sdiv_3(100);
    test_sdiv_4();
    test_sdiv_5();
    test_sdiv_6();
    test_sdiv_7();
    test_sdiv_8();

    return 0;
}
