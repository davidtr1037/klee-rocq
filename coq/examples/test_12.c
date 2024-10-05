#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

int main() {
    unsigned x = 3;
    unsigned y = 2;
    unsigned n = klee_make_symbolic_int32();
    unsigned a = x % y;
    unsigned b = n % x;
    return 0;
}
