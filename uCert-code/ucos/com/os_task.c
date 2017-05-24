/*
*********************************************************************************************************
*                                                uC/OS-II
*                                          The Real-Time Kernel
*                                            TASK MANAGEMENT
*
*                          (c) Copyright 1992-2002, Jean J. Labrosse, Weston, FL
*                                           All Rights Reserved
*
* File : OS_TASK.C
* By   : Jean J. Labrosse
*********************************************************************************************************
*/

#ifndef  OS_MASTER_FILE
#include "includes.h"
#endif



/*
*********************************************************************************************************
*                                        CHANGE PRIORITY OF A TASK
*
* Description: This function allows you to change the priority of a task dynamically.  Note that the new
*              priority MUST be available.
*
* Arguments  : oldp     is the old priority
*
*              newp     is the new priority
*
* Returns    : OS_NO_ERR        is the call was successful
*              OS_PRIO_INVALID  if the priority you specify is higher that the maximum allowed
*                               (i.e. >= OS_LOWEST_PRIO)
*              OS_PRIO_EXIST    if the new priority already exist.
*              OS_PRIO_ERR      there is no task with the specified OLD priority (i.e. the OLD task does
*                               not exist.
*********************************************************************************************************
*/

#if OS_TASK_CREATE_EN > 0
INT8U  OSTaskCreate (void (*task)(void *pd), void *pdata, INT8U prio)
{
#if OS_CRITICAL_METHOD == 3                  /* Allocate storage for CPU status register               */
    OS_CPU_SR  cpu_sr;
#endif
    OS_STK_BLK  *pblk;
    OS_STK    *ptos;
    OS_STK    *psp;
    INT8U      err;

    
#if OS_ARG_CHK_EN > 0
    if (prio > OS_LOWEST_PRIO) {             /* Make sure priority is within allowable range           */
        return (OS_PRIO_INVALID);
    }
#endif
    OS_ENTER_CRITICAL();
    if (OSTCBPrioTbl[prio] == (OS_TCB *)0) { /* Make sure task doesn't already exist at this priority  */
        OSTCBPrioTbl[prio] = (OS_TCB *)1;    /* Reserve the priority to prevent others from doing ...  */
                                             /* ... the same thing until task is created.              */    
	
	if (OSSTKFreeList != (OS_STK_BLK *)0)
	{	     
	    pblk=OSSTKFreeList;
	    ptos=OSSTKFreeList->taskstk;
	    OSSTKFreeList=OSSTKFreeList->nextblk;
	}
	else 
	{
	    return (OS_NO_MORE_TCB);
	}
	OS_EXIT_CRITICAL();
  	
        psp = (OS_STK *)OSTaskStkInit(task, pdata, &ptos[TASK_STK_SIZE-1], 0);    /* Initialize the task's stack         */
     
        err = OS_TCBInit(prio, psp, (OS_STK *)0, pblk, 0, 0, (void *)0, 0);
	
        if (err == OS_NO_ERR) {
            OS_ENTER_CRITICAL();
            OSTaskCtr++;                                        /* Increment the #tasks counter        */
            
            if (OSRunning == TRUE) {         /* Find highest priority task if multitasking has started */
		OS_EXIT_CRITICAL();
                OS_Sched();
            }
	    else 
		OS_EXIT_CRITICAL();	
        } else {
            OS_ENTER_CRITICAL();
            OSTCBPrioTbl[prio] = (OS_TCB *)0;/* Make this priority available to others                 */
            OS_EXIT_CRITICAL();
        }
        return (err);
    }
    OS_EXIT_CRITICAL();
    return (OS_PRIO_EXIST);
}
#endif
/*$PAGE*/
/*
*********************************************************************************************************
*                                            DELETE A TASK
*
* Description: This function allows you to delete a task.  The calling task can delete itself by
*              its own priority number.  The deleted task is returned to the dormant state and can be
*              re-activated by creating the deleted task again.
*
* Arguments  : prio    is the priority of the task to delete.  Note that you can explicitely delete
*                      the current task without knowing its priority level by setting 'prio' to
*                      OS_PRIO_SELF.
*
* Returns    : OS_NO_ERR           if the call is successful
*              OS_TASK_DEL_IDLE    if you attempted to delete uC/OS-II's idle task
*              OS_PRIO_INVALID     if the priority you specify is higher that the maximum allowed
*                                  (i.e. >= OS_LOWEST_PRIO) or, you have not specified OS_PRIO_SELF.
*              OS_TASK_DEL_ERR     if the task you want to delete does not exist
*              OS_TASK_DEL_ISR     if you tried to delete a task from an ISR
*
* Notes      : 1) To reduce interrupt latency, OSTaskDel() 'disables' the task:
*                    a) by making it not ready
*                    b) by removing it from any wait lists
*                    c) by preventing OSTimeTick() from making the task ready to run.
*                 The task can then be 'unlinked' from the miscellaneous structures in uC/OS-II.
*              2) The function OS_Dummy() is called after OS_EXIT_CRITICAL() because, on most processors,
*                 the next instruction following the enable interrupt instruction is ignored.  
*              3) An ISR cannot delete a task.
*              4) The lock nesting counter is incremented because, for a brief instant, if the current
*                 task is being deleted, the current task would not be able to be rescheduled because it
*                 is removed from the ready list.  Incrementing the nesting counter prevents another task
*                 from being schedule.  This means that an ISR would return to the current task which is
*                 being deleted.  The rest of the deletion would thus be able to be completed.
*********************************************************************************************************
*/
/*$PAGE*/
#if OS_TASK_DEL_EN > 0
INT8U  OSTaskDel (INT8U prio)
{
#if OS_CRITICAL_METHOD == 3                      /* Allocate storage for CPU status register           */
    OS_CPU_SR     cpu_sr;
#endif

#if OS_EVENT_EN > 0
    OS_EVENT     *pevent;
#endif    
#if (OS_VERSION >= 251) && (OS_FLAG_EN > 0) && (OS_MAX_FLAGS > 0)
    OS_FLAG_NODE *pnode;
#endif
    OS_TCB       *ptcb;
//    BOOLEAN       self;

//		self = self;

//    if (OSIntNesting > 0) {                                     /* See if trying to delete from ISR    */
//        return (OS_TASK_DEL_ISR);
//    }
#if OS_ARG_CHK_EN > 0
    if (prio == OS_IDLE_PRIO) {                                 /* Not allowed to delete idle task     */
        return (OS_TASK_DEL_IDLE);
    }
    if (prio >= OS_LOWEST_PRIO && prio != OS_PRIO_SELF) {       /* Task priority valid ?               */
        return (OS_PRIO_INVALID);
    }
#endif
    OS_ENTER_CRITICAL();
    if (prio == OS_PRIO_SELF) {                                 /* See if requesting to delete self    */
        prio = OSTCBCur->OSTCBPrio;                             /* Set priority to delete to current   */
    }
    ptcb = OSTCBPrioTbl[prio];
    if (ptcb != (OS_TCB *)0) {                                       /* Task to delete must exist      */
        if ((OSRdyTbl[ptcb->OSTCBY] &= ~ptcb->OSTCBBitX) == 0x00) {  /* Make task not ready            */
            OSRdyGrp &= ~ptcb->OSTCBBitY;
        }
#if OS_EVENT_EN > 0
        pevent = ptcb->OSTCBEventPtr;
        if (pevent != (OS_EVENT *)0) {                          /* If task is waiting on event         */
            if ((pevent->OSEventTbl[ptcb->OSTCBY] &= ~ptcb->OSTCBBitX) == 0) { /* ... remove task from */
                pevent->OSEventGrp &= ~ptcb->OSTCBBitY;                        /* ... event ctrl block */
            }
        }
#endif
        ptcb->OSTCBDly  = 0;                                    /* Prevent OSTimeTick() from updating  */
        ptcb->OSTCBStat = OS_STAT_RDY;                          /* Prevent task from being resumed     */
	//	if (OSLockNesting < 255) {
    //        OSLockNesting++;
	//	}
    //    OS_EXIT_CRITICAL();                                     /* Enabling INT. ignores next instruc. */
    //    OS_Dummy();                                             /* ... Dummy ensures that INTs will be */
    //    OS_ENTER_CRITICAL();                                    /* ... disabled HERE!                  */
	//	if (OSLockNesting > 0) {
    //       OSLockNesting--;
	//	}
        OSTaskDelHook(ptcb);                                    /* Call user defined hook              */
        OSTaskCtr--;                                            /* One less task being managed         */
        OSTCBPrioTbl[prio] = (OS_TCB *)0;                       /* Clear old priority entry            */

	

        if (ptcb->OSTCBPrev == (OS_TCB *)0) {                   /* Remove from TCB chain               */
            ptcb->OSTCBNext->OSTCBPrev = (OS_TCB *)0;
            OSTCBList                  = ptcb->OSTCBNext;
        } else {
            ptcb->OSTCBPrev->OSTCBNext = ptcb->OSTCBNext;
            ptcb->OSTCBNext->OSTCBPrev = ptcb->OSTCBPrev;
        }
	(ptcb->OSTCBStkBlk)->nextblk = OSSTKFreeList;		/* free task stk          */
	OSSTKFreeList = ptcb->OSTCBStkBlk;
        ptcb->OSTCBNext = OSTCBFreeList;                        /* Return TCB to free TCB list         */
        OSTCBFreeList   = ptcb;
        OS_EXIT_CRITICAL();
        OS_Sched();                                             /* Find new highest priority task      */
        return (OS_NO_ERR);
    }
    OS_EXIT_CRITICAL();
    return (OS_TASK_DEL_ERR);
}
#endif
/*$PAGE*/

