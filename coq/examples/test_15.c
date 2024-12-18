#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>

#include <klee/klee.h>

void f1(int x) {
    int y = x << 2;
}

void f2() {
    int x = klee_make_symbolic_int32();
    int y = x << 2;
}

void f3(unsigned x) {
    int y = 10 << x;
}

void f4() {
    unsigned x = klee_make_symbolic_int32();
    klee_assume_bool(x < 32);
    int y = 10 << x;
}

int main() {
    f1(100);
    f2();
    f3(10);
    f4();
    return 0;
}
