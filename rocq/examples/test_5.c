#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

int main() {
    int n = klee_make_symbolic_int32();
    klee_assume_bool(n > 7);
    assert(n > 0);

    if (n < 3) {
        return 1;
    } else {
        return 0;
    }
}
