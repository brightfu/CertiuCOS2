Require Export include_frm.

(* identifiers *)
Definition OSRunning : ident := 0%Z.
Definition OSRdyGrp : ident := 1%Z.
Definition OSUnMapTbl: ident := 2%Z.
Definition OSRdyTbl: ident := 3%Z.
Definition OSPrioHighRdy: ident := 4%Z.
Definition OSPrioCur: ident := 5%Z.
Definition OSStartHighRdy: ident := 6%Z.
Definition OSIntNesting: ident := 7%Z.
Definition OSIntExitY: ident := 8%Z.
Definition OSCtxSwCtr: ident := 9%Z.
Definition OSInitHookBegin: ident := 10%Z.
Definition OSInitHookEnd: ident := 11%Z.
Definition OS_InitMisc := 12%Z.
Definition OS_InitRdyList := 13%Z.
Definition OS_InitSTKList := 14%Z.
Definition OS_InitTCBList := 15%Z.
Definition OS_InitEventList := 16%Z.
Definition OS_QInit := 17%Z.
Definition OS_SemInit := 18%Z.
Definition OS_InitTaskIdle := 19%Z.
Definition OS_TCBInit := 20%Z.
Definition OSStatRdy: ident := 21%Z.
Definition OSMapTbl: ident := 22%Z.
Definition OSEventGrp: ident := 23%Z.
Definition OSEventCnt: ident := 24%Z.
Definition OSEventTbl: ident := 25%Z.
Definition OSEventListPtr: ident := 36%Z.
Definition OSTCBEventPtr: ident := 26%Z.
Definition OSEventType: ident := 27%Z.
Definition OSEventPtr: ident := 28%Z.
Definition OSEventFreeList: ident := 29%Z.
Definition OS_EventWaitListInit := 30%Z.
Definition OS_EventTO := 31%Z.
Definition OS_EventTaskRdy := 32%Z.
Definition OS_EventTaskWait := 33%Z.
Definition OSQPtr: ident := 34%Z.
Definition OSEventList: ident := 35%Z.
Definition OSIntToyCount: ident := 500%Z.
Definition OSQStart: ident := 37%Z.
Definition OSQEnd: ident := 38%Z.
Definition OSQIn: ident := 39%Z.
Definition OSQOut: ident := 40%Z.
Definition OSQSize: ident := 41%Z.
Definition OSQEntries: ident := 42%Z.
Definition OSQFreeBlk: ident := 43%Z.
Definition OSQFreeBlkTbl: ident := 44%Z.
Definition OSQFreeList: ident := 45%Z.
Definition OSQTbl: ident := 46%Z.
Definition qfreeblk: ident := 47%Z.
Definition nextblk: ident := 48%Z.
Definition OSTCBDly: ident := 51%Z.
Definition OSTCBMsg: ident := 52%Z.
Definition OSTCBStat: ident := 53%Z.
Definition OSTCBTbl: ident := 54%Z.
Definition OSTCBNext: ident := 55%Z.
Definition OSTCBPrev: ident := 56%Z.
Definition OSTCBFreeList: ident := 57%Z.
Definition OSTCBPrioTbl: ident := 58%Z.
(*
Definition OSTCBHighRdy: ident := 59%Z.
*)
Definition OSTCBList: ident := 61%Z.
Definition OSTCBPrio: ident := 62%Z.
Definition OSTCBBitY: ident := 63%Z.
Definition OSTCBY: ident := 64%Z.
Definition OSTCBX: ident := 65%Z.
Definition OSTCBBitX: ident := 66%Z.
Definition OSTCBflag :ident :=300%Z.
 Definition OS_Sched := 67%Z.
Definition OSLockNesting: ident := 68%Z.
Definition OSTaskCtr: ident := 69%Z.
Definition OSTaskCreate := 70%Z.
Definition OS_TaskIdle := 71%Z.
Definition OSSTKTbl: ident := 72%Z.
Definition OSSTKFreeList: ident := 73%Z.
Definition OSTimeTick := 74%Z.
Definition OSTime: ident := 75%Z.
Definition OSIntExit := 76%Z.
Definition OSIdleCtr: ident := 77%Z.
Definition OSIdleCtrRun: ident := 78%Z.
Definition OSIdleCtrMax: ident := 79%Z.
Definition OSPlaceHolder: ident := 80%Z.
(*Definition OS_SemPtrAdd := 80%Z.
Definition OS_SemPtrRemove := 81%Z.
Definition OS_SemPtrSearch := 82%Z.*)
(*Definition OS_EventPtrAdd := 83%Z.*)
Definition OS_EventRemove := 84%Z.
Definition OS_EventSearch := 85%Z.
Definition os_event: ident := 86%Z.
Definition os_q: ident := 87%Z.
Definition os_q_freeblk: ident := 88%Z.
Definition msgqueuetbl: ident := 89%Z.
Definition os_tcb: ident := 90%Z.
Definition OS_IsSomeMutexOwner := 933%Z.
Definition os_tcb_flag: ident := 190%Z.

Definition os_stk_blk: ident := 91%Z.
Definition taskstk: ident := 92%Z.
Definition os_q_ptr: ident := 93%Z.
Definition os_sem_ptr: ident := 94%Z.
Definition qeventptr: ident := 95%Z.
Definition next: ident := 96%Z.
Definition x : ident := 97%Z.
Definition y : ident := 98%Z.
Definition ptcb : ident := 99%Z.
Definition pevent : ident := 100%Z.
(*Definition msg : ident := 101%Z.*)
Definition message : ident := 101%Z.
Definition msk : ident := 102%Z.
Definition bitx : ident := 103%Z.
Definition bity : ident := 104%Z.
Definition prio : ident := 105%Z.
Definition ptbl : ident := 106%Z.
Definition i : ident := 107%Z.
Definition pevent1 : ident := 108%Z.
Definition pevent2 : ident := 109%Z.
Definition prdytbl : ident := 110%Z.
Definition pstk1 : ident := 111%Z.
Definition pstk2 : ident := 112%Z.
Definition ptcb1 : ident := 113%Z.
Definition ptcb2 : ident := 114%Z.
Definition task : ident := 115%Z.
Definition pdata : ident := 116%Z.
Definition p : ident := 117%Z.
Definition p1 : ident := 118%Z.
Definition p2 : ident := 119%Z.
Definition pq : ident := 120%Z.
Definition pqblk : ident := 121%Z.
Definition start : ident := 122%Z.
Definition err : ident := 123%Z.
Definition tasks_waiting : ident := 124%Z.
Definition timeout : ident := 125%Z.
Definition size : ident := 126%Z.
Definition cnt : ident := 127%Z.
Definition self : ident := 128%Z.
Definition ticks : ident := 129%Z.
Definition legal : ident := 130%Z.
Definition pqptr : ident := 131%Z.
Definition p3 : ident := 132%Z.
Definition pip : ident := 133%Z.
Definition mprio : ident := 134%Z.
Definition isrdy : ident := 140%Z.
Definition tcb_flag: ident := 500%Z.
(* constants *)
  (* in file 'os_cfg.h' *)
Definition OS_MAX_EVENTS := 10%Z.
Definition OS_MAX_QS := 10%Z.
Definition OS_MAX_SEM := 10%Z.
Definition OS_MAX_Q_SIZE := 20%Z.
Definition OS_MAX_TASKS := 30%Z.
Definition OS_LOWEST_PRIO := 63%Z.
Definition TASK_STK_SIZE := 1024%Z.

  (* in file 'ucos_ii.h' *)
Definition OS_PRIO_SELF := 255%Z.
Definition OS_N_SYS_TASKS := 2%Z.
Definition OS_IDLE_PRIO := OS_LOWEST_PRIO.
Definition OS_EVENT_TBL_SIZE := 8%Z. (* OS_LOWEST_PRIO / 8 + 1*)
Definition OS_RDY_TBL_SIZE := 8%Z. (* OS_LOWEST_PRIO / 8 + 1 *)

Definition OS_STAT_RDY := 0%Z.
Definition OS_STAT_SEM := 1%Z.
Definition OS_STAT_MBOX := 2%Z.
Definition OS_STAT_Q := 4%Z.
Definition OS_STAT_SUSPEND := 8%Z.
Definition OS_STAT_MUTEX := 16%Z.
Definition OS_STAT_FLAG := 32%Z.

Definition OS_EVENT_TYPE_UNUSED := 0%Z.
Definition OS_EVENT_TYPE_MBOX := 1%Z.
Definition OS_EVENT_TYPE_Q := 2%Z.
Definition OS_EVENT_TYPE_SEM := 3%Z.
Definition OS_EVENT_TYPE_MUTEX := 4%Z.

Definition OS_NO_ERR := 0%Z.
Definition OS_ERR_EVENT_TYPE := 1%Z.
Definition OS_ERR_PEND_ISR := 2%Z.
Definition OS_ERR_POST_NULL_PTR :=3%Z.
Definition OS_ERR_PEVENT_NULL := 4%Z.
Definition OS_ERR_TASK_WAITING := 8%Z.
Definition OS_TIMEOUT := 10%Z.
Definition OS_Q_FULL := 30%Z.
Definition OS_STAT_ERR := 31%Z.
Definition OS_ERR_NOT_MUTEX_OWNER := 120%Z.
Definition OS_ERR_MUTEX_PRIO := 121%Z.
Definition OS_ERR_PEVENT_NO_EX := 122%Z.
Definition OS_ERR_IDLE := 123%Z.
Definition OS_ERR_STAT := 124%Z.
Definition OS_ERR_OWN := 125%Z.
Definition OS_ERR_MUTEXPR_NOT_HOLDER := 126%Z.
Definition OS_ERR_ORIGINAL_NOT_HOLDER := 127%Z.
Definition OS_ERR_MUTEX_WL_HIGHEST_PRIO := 128%Z.
Definition OS_PRIO_EXIST := 40%Z.
Definition OS_PRIO_ERR := 41%Z.
Definition OS_PRIO_INVALID := 42%Z.
Definition OS_ERR_NEST:= 1000%Z.
Definition OS_ERR_MUTEX_DEADLOCK := 1001%Z.
Definition OS_ERR_MUTEX_IDLE := 1002%Z.

Definition OS_SEM_OVF := 50%Z.

Definition OS_TASK_DEL_ERR := 60%Z.
Definition OS_TASK_DEL_IDLE := 61%Z.
Definition OS_TASK_DEL_SOME_MUTEX_OWNER := 62%Z.
Definition OS_TASK_DEL_HAS_NO_NEXT := 64%Z. 
Definition OS_TASK_DEL_ISR := 63%Z.

Definition OS_NO_MORE_TCB := 70%Z.
Definition OS_ERR_DEL_ISR := 140%Z.

Definition OS_VERSION := 252%Z.

Definition OS_MUTEX_KEEP_LOWER_8 := 255%Z.
Definition OS_MUTEX_KEEP_UPPER_8 := 65280%Z.
Definition OS_MUTEX_AVAILABLE := 255%Z.


Definition OS_PrioChange := 400%Z.
Definition OSInit := 253%Z.
Definition OSStart := 254%Z.
Definition OSIntEnter := 255%Z.
Definition OSVersion := 256%Z.
Definition OSQAccept := 257%Z.
Definition OSQCreate := 258%Z.
Definition OSQDel := 259%Z.
Definition OSQPend := 260%Z.
Definition OSQGetMsg := 261%Z.
Definition OSQPost := 262%Z.
Definition OSSemAccept := 263%Z.
Definition OSSemCreate := 264%Z.
Definition OSSemDel := 265%Z.
Definition OSSemPend := 266%Z.
Definition OSTaskDel := 267%Z.
Definition OSTimeDly := 268%Z.
Definition OSTimeGet := 269%Z.
Definition OSSemPost := 270%Z.
Definition OSMboxCreate := 271%Z.
Definition OSMboxDel := 272%Z.
Definition OSMboxPend := 273%Z.
Definition OSMboxPost := 274%Z.
Definition OSMboxAccept := 275%Z.
Definition OSMutexCreate := 276%Z.
Definition OSMutexDel := 277%Z.
Definition OSMutexPend := 278%Z.
Definition OSMutexPost := 279%Z.
Definition OSMutexAccept := 280%Z.
Definition OSTickISR := 0.
Definition OSToyISR := 1.

(* mailbox definitions *)

Definition SOME_P_NOT_LEGAL_ERR     := 1312%Z.

Definition MBOX_DEL_NULL_ERR        := OS_ERR_PEVENT_NULL.
Definition MBOX_DEL_P_NOT_LEGAL_ERR := SOME_P_NOT_LEGAL_ERR.
Definition MBOX_DEL_WRONG_TYPE_ERR  := OS_ERR_EVENT_TYPE.
Definition MBOX_DEL_TASK_WAITING_ERR := OS_ERR_TASK_WAITING.
Definition MBOX_DEL_SUCC       := OS_NO_ERR.

Definition MBOX_POST_NULL_ERR := OS_ERR_PEVENT_NULL.
Definition MBOX_POST_MSG_NULL_ERR := OS_ERR_POST_NULL_PTR.
Definition MBOX_POST_P_NOT_LEGAL_ERR := SOME_P_NOT_LEGAL_ERR.
Definition MBOX_POST_WRONG_TYPE_ERR := OS_ERR_EVENT_TYPE.
Definition MBOX_POST_TASK_WT_ERR := OS_ERR_TASK_WAITING.
Definition MBOX_POST_FULL_ERR := OS_Q_FULL.
Definition MBOX_POST_SUCC := OS_NO_ERR.

Definition MBOX_PEND_NULL_ERR := OS_ERR_PEVENT_NULL.
Definition MBOX_PEND_P_NOT_LEGAL_ERR := SOME_P_NOT_LEGAL_ERR.
Definition MBOX_PEND_WRONG_TYPE_ERR := OS_ERR_EVENT_TYPE.
Definition MBOX_PEND_FROM_IDLE_ERR := 1313%Z.
Definition MBOX_PEND_NOT_READY_ERR := 1314%Z.
Definition MBOX_PEND_TIMEOUT_ERR := OS_TIMEOUT.
Definition MBOX_PEND_SUCC := OS_NO_ERR.

