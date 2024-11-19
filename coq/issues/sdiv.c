#include <stdio.h>

void f(int x, int y) {
    int z = x / y;
    printf("%d\n", z);
}

int main() {
    f(-2147483648, -1);
    return 0;
}
