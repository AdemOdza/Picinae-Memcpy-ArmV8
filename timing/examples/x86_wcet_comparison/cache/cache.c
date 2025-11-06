#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <x86intrin.h>

int __attribute__ ((noinline)) sum(int* arr, uint64_t size) {
    int x = 0;
    for (int i = 0; i < size; i++) {
        x += arr[i];
    }
    return x;
}

int __attribute__ ((noinline)) stuff(int* arr, int size) {
    uint64_t sum_cycles = 0;

    int extra_cycles = 0;
    int sum_acc = 0;
    int iters =100000;
    
    for (int j = 0; j < iters; j++) {
    	for(int i = 0; i < size; i++) {
	        arr[i] = rand();
	    }

        uint64_t start, end, cycles1, cycles2;

        start = __rdtsc();
        end = __rdtsc();
        extra_cycles += end - start;
	
	    start = __rdtsc();
        int s1 = sum(arr, size);
        end = __rdtsc();
        cycles1 = end - start;

        start = __rdtsc();
        int s2 = sum(arr, size);
        end = __rdtsc();
        cycles2 = end - start;

        sum_acc += s1 + s2;

        sum_cycles += cycles1 + cycles2;
    }

    int extra = extra_cycles / iters;
    printf("Avg: %ld\n", (sum_cycles / 2) / (iters / 2) - extra);

    return sum_acc;
}

int main(int argc, char* argv[]) {
    int arr[1000];

    printf("%d\n", stuff(arr, 0));

    return 0;
}
