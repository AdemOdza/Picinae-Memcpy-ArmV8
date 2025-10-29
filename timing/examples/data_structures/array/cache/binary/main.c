#include "cache.h"

int main(int argc, char* argv[]) {
    uint32_t arr[1000];
    
    for (uint32_t j = 0; j < 100; j++) {
    	for(uint32_t i = 0; i < 1000; i++) {
	        arr[i] = rand();
	    }
	
	    printf("%d\n", cached_sum(arr, arr, 1000));
    }

    return 0;
}
