#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <klee/klee.h>

int g(int x) {
    return x + 1;
}

int f(int x) {
    int a = g(1);
    int b = g(2);
    return a + b;
}

int main() {
    int x = f(1);
    return 0;
}
