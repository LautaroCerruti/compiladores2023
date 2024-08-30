#include <stdio.h>

// Función de Ackermann
int ackermann(int m, int n) {
    if (m == 0) {
        return n + 1;
    } else if (n == 0) {
        return ackermann(m - 1, 1);
    } else {
        return ackermann(m - 1, ackermann(m, n - 1));
    }
}

int main() {
    printf("ackermann en 3 11 es %d\n", ackermann(3, 11));
    return 0;
}