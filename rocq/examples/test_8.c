#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

#define N 5

int main() {
    int n = klee_make_symbolic_int32();
    klee_assume_bool(n <= N);

    int i = 0;
    while (i < n) {
        i++;
    }
    return 0;
}
