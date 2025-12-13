#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

#define N 5

int main() {
    int n = 0;
    while (n < N) {
        n++;
    }
    return 0;
}
