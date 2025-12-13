#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

int foo(int x, int y) {
    return x + y;
}

int main() {
    int a = 1;
    int b = a + 1;
    return foo(a + 1, b);
}
