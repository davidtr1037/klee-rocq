#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

/* TODO: test */
void f1() {
    unsigned x = 3;
    unsigned y = 2;
    unsigned n = klee_make_symbolic_int32();
    unsigned b = n % x;
}

/* TODO: test */
void f2(unsigned x, unsigned y) {
    unsigned a = x % y;
}

void f3() {
    unsigned n = klee_make_symbolic_int32();
    unsigned a = n % 1;
}

int main() {
    f1();
    //f2(2, 3);
    //f3();
    return 0;
}
