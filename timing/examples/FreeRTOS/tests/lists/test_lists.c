#include "../../../timing_experiments.h"
//#include "FreeRTOS.h"
//#include "list.h"
#include <stdlib.h>
#include <stdio.h>

#define NUM_ITEMS 64

#define List_t uint32_t *
#define ListItem_t uint32_t *
#define UBaseType_t uint32_t

// Forward declarations of the assembly functions
extern void vListInitialise(List_t *pxList);
extern void vListInitialiseItem(ListItem_t *pxItem);
extern void vListInsert(List_t *pxList, ListItem_t *pxNewListItem);
extern void vListInsertEnd(List_t *pxList, ListItem_t *pxNewListItem);
extern UBaseType_t uxListRemove(ListItem_t *pxItem);

int main(void) {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);

    srand(42);

    List_t testList;
    ListItem_t items[NUM_ITEMS];

    puts("Starting FreeRTOS list operation timing tests...\n");

    // Initialize list and all items
    vListInitialise(&testList);
    for (uint32_t i = 0; i < NUM_ITEMS; ++i) {
        vListInitialiseItem(&items[i]);
	*(items[i] + 4) = rand(); // set value
    }

    for (uint32_t op = 0; op < 4; op++) {
    for (uint32_t iter = 0; iter < 200; ++iter) {
        uint32_t idx = rand() % NUM_ITEMS;

        START_TIMER;
        switch (op) {
        case 0:
            // Insert by sorted order
            vListInsert(&testList, &items[idx]);
            break;
        case 1:
            // Insert at end
            vListInsertEnd(&testList, &items[idx]);
            break;
        case 2:
            // Remove if linked
            uxListRemove(&items[idx]);
            break;
        case 3:
            // Reinitialize (like clearing)
            vListInitialise(&testList);
            break;
        }
        PRINT_TIMER;

        char buf[64];
        itoa(iter, buf, 10);
        puts("Iteration "); puts(buf);
        puts(": operation "); itoa(op, buf, 10); puts(buf);
        puts("\n");
    }}

    puts("Timing tests complete.\n");
    return 0;
}

