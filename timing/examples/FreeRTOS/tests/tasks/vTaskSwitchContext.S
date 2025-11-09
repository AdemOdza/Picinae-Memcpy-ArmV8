    .section .data
    .globl uxSchedulerSuspended
    .globl xYieldPendings
    .globl uxTopReadyPriority
    .globl pxCurrentTCB
    .globl pxReadyTasksLists
    
    .section .text
    .globl vTaskSwitchContext
    .type vTaskSwitchContext, @function
vTaskSwitchContext:
    lw	a4,uxSchedulerSuspended
    beqz	a4,80001390
    addi	a4,zero,1
    sw	a4,xYieldPendings
    ret
80001390:
    addi	sp,sp,-16
    sw	zero,xYieldPendings
    sw	s0,8(sp)
    lw	a5,pxCurrentTCB
    lui	a4,0xa5a5a
    sw	ra,12(sp)
    lw	a5,48(a5)
    addi	a4,a4,1445
    lw	a2,0(a5)
    bne	a2,a4,800013d0
    lw	a3,4(a5)
    bne	a3,a2,800013d0
    lw	a4,8(a5)
    bne	a4,a3,800013d0
    lw	a5,12(a5)
    beq	a5,a4,800013e0
800013d0:
    lw	a1,pxCurrentTCB
    lw	a0,pxCurrentTCB
    addi	a1,a1,52
    jal	8000e7ec
800013e0:
    lw	a5,uxTopReadyPriority
    addi	a3,zero,31
    clz	a5,a5
    sub	a3,a3,a5
    addi	a5,zero,20
    mul	a5,a3,a5
    addi	a0,gp,-924
    addi	a4,gp,-924
    add	a2,a0,a5
    lw	a1,4(a2)
    addi	a5,a5,8
    add	a5,a5,a0
    lw	a1,4(a1)
    sw	a1,4(a2)
    bne	a1,a5,80001424
    lw	a5,12(a2)
    sw	a5,4(a2)
80001424:
    addi	a5,zero,20
    mul	a3,a3,a5
    lw	ra,12(sp)
    add	a4,a4,a3
    lw	a5,4(a4)
    lw	a5,12(a5)
    sw	a5,pxCurrentTCB
    lw	a5,pxCurrentTCB
    lw	s0,8(sp)
    addi	sp,sp,16
    ret

    .size vTaskSwitchContext, .-vTaskSwitchContext
