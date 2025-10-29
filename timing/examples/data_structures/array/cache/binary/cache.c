#include "../../../../timing_experiments.h"

uint32_t sum(uint32_t* arr, uint32_t size) {
    int x = 0;
    for (int i = 0; i < size; i++) {
        x += arr[i];
    }
    return x;
}

uint32_t cached_sum(uint32_t* arr1, uint32_t* arr2, uint32_t size) {
    uint32_t x = sum(arr1, 1000);
    x += sum(arr2, 1000);
    return x;
}
