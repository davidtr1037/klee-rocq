#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>

#include <klee/klee.h>

void f1(int y) {
    char c = y;
    c = c + 1;
}

void f2() {
    int y = klee_make_symbolic_int32();
    char c = y;
    c = c + 1;
}

int main() {
    f1(1);
    f2();
    return 0;
}
