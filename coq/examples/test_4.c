#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

int main() {
    int x = 0;
    int n = klee_make_symbolic_int32();
    if (n > 7) {
        x = 1;
    }
    return x;
}
