#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

#define N 5

int main() {
    unsigned n = klee_make_symbolic_int32();
    int a = n * 2;
    if (a == 0) {
        return 1;
    } else {
        return 0;
    }
}
