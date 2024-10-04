#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

void f(int x, int y) {
    unsigned n = klee_make_symbolic_int32();
    int a = x % y;
    int b = n % a;
}

int main() {
    f(3, 2);
    return 0;
}
