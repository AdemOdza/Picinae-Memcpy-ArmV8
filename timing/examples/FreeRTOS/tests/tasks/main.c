#include "../../../timing_experiments.h"

uint32_t uxSchedulerSuspended = 0;
uint32_t xYieldPendings = 0;
uint32_t uxTopReadyPriority = 0;
void *pxCurrentTCB = 0;
void *pxReadyTasksLists[10];

