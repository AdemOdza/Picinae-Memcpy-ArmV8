#include "binary_search.h"

uint32_t binary_search(uint32_t *arr, size_t size, uint32_t target) {
    int left = 0;
    int right = size - 1;

    while (left <= right) {
        int mid = left + (right - left) / 2;

        int mid_val = arr[mid];
        if (mid_val == target) {
            return mid; // Target found, return its index
        }

        // branchless updates to left, right
        asm volatile (
            "sltu  t0, %2, %3\n\t"        // t0 = (mid_val < target)
            "sltu  t1, %3, %2\n\t"        // t1 = (target < mid_val)
            // new_left  = t0 ? mid+1 : left
            "addi  t2, %4, 1\n\t"         // t2 = mid+1
            "neg   t3, t0\n\t"            // t3 = (t0 ? -1 : 0)
            "and   t2, t2, t3\n\t"        // t2 = (t0 ? mid+1 : 0)
            "andn  t4, %0, t3\n\t"        // t4 = (t0 ? 0 : left)
            "or    %0, t2, t4\n\t"        // left = selected result

            // new_right = t1 ? mid-1 : right
            "addi  t2, %4, -1\n\t"        // t2 = mid-1
            "neg   t3, t1\n\t"            // t3 = (t1 ? -1 : 0)
            "and   t2, t2, t3\n\t"        // t2 = (t1 ? mid-1 : 0)
            "andn  t4, %1, t3\n\t"        // t4 = (t1 ? 0 : right)
            "or    %1, t2, t4\n\t"        // right = selected result
            : "+r"(left), "+r"(right)
            : "r"(mid_val), "r"(target), "r"(mid)
            : "t0", "t1", "t2", "t3", "t4"
        );
    }

    return -1; // Target not found
}
