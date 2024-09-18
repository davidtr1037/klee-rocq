#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

int custom_sqrt(int n) {
    int r = n;
    int s = r * r;
    while (s > n) {
        r = r - 1;
        s = r * r;
    }

    return r;
}

void sqrt_spec(int n) {
    int r = custom_sqrt(n);
    int s1 = r * r;
    int s2 = (r + 1) * (r + 1);
    assert(s1 <= n && n <= s2);
}

int main() {
    int n = klee_make_symbolic_int32();
    klee_assume_bool(n > 0);
    klee_assume_bool(n < 10);
    sqrt_spec(n);
    return 0;
}
