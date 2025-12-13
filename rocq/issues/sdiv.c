#include <stdio.h>
#include <stdint.h>

void f(int32_t x, int32_t y) {
    int32_t z = x / y;
    printf("%d\n", z);
}

int main() {
    f(-2147483648, -1);
    return 0;
}
