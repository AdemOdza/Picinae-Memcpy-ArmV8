#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>

uint64_t while_true_break(uint64_t n) {
    while (true) {
        if ((uint64_t)n + (uint64_t)n >= (uint64_t)n * (uint64_t)n)
            break;

        n--;
    }

    return n;
}

int main(int argc, char* argv[]) {
    for (int i = 0; i < 1000; i++) {
    	while_true_break(i);
    }
}
