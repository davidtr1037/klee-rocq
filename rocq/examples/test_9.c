#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

int main() {
    int x = 10;
    int y = 20;
    int z = x * y;
    return z - 7;
}
