#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

int foo(int x, int y) {
    return x + y;
}

int main() {
    int a = 1;
    int b = a++;
    return foo(a, b);
}
