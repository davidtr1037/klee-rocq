#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

void test_urem_1() {
    unsigned x = 3;
    unsigned y = 2;
    unsigned a = x % y;
    unsigned n = klee_make_symbolic_int32();
    unsigned b = n % a;
}

void test_urem_2(unsigned x) {
    unsigned y = 3 % x;
}

void test_urem_3() {
    unsigned x = klee_make_symbolic_int32();
    klee_assume_bool(x != 0);
    unsigned y = 3 % x;
}

void test_srem_1() {
    int x = 3;
    int y = 2;
    int a = x % y;
    int n = klee_make_symbolic_int32();
    int b = n % a;
}

void test_srem_2(int x) {
    int y = 3 % x;
}

void test_srem_3() {
    int x = klee_make_symbolic_int32();
    klee_assume_bool(x != 0);
    int y = 3 % x;
}

int main() {
    test_urem_1();
    test_urem_2(10);
    test_urem_3();
    test_srem_1();
    test_srem_2(10);
    test_srem_3();
    return 0;
}
