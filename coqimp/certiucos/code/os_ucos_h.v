Require Import os_code_defs.
Require Import code_notations.

Open Scope code_scope.

Definition OS_EVENT : type := 
  STRUCT os_event ­{ 
                    ⌞OSEventType @ Int8u;
                    OSEventGrp @ Int8u; 
                    OSEventCnt @ Int16u; 
                    OSEventPtr @ (Void ∗);
                    OSEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE);
                    OSEventListPtr @ STRUCT os_event ⋆⌟
                   }­.


Definition OS_Q_FREEBLK : type :=
  STRUCT os_q_freeblk ­{
                        ⌞nextblk @ STRUCT os_q_freeblk ⋆ ; 
                        msgqueuetbl @ (Tarray (Void ∗) ∘OS_MAX_Q_SIZE)⌟
                       }­.


Definition OS_Q : type := 
    STRUCT os_q ­{
                  ⌞OSQPtr @ Void ∗;
                  OSQStart @ Void ∗ ∗;
                  OSQEnd @ Void ∗ ∗;
                  OSQIn @ Void ∗ ∗;
                  OSQOut @ Void ∗ ∗;
                  OSQSize @ Int16u ;
                  OSQEntries @ Int16u ;
                  qfreeblk @ OS_Q_FREEBLK ∗⌟
                 }­.

Definition OS_TCB : type := 
  STRUCT os_tcb ­{
                  ⌞OSTCBNext @ STRUCT os_tcb ⋆;
                  OSTCBPrev @ STRUCT os_tcb ⋆ ;
                  OSTCBEventPtr @ OS_EVENT ∗ ; 
                  OSTCBMsg @ Void ∗ ;
                  OSTCBDly @ Int16u ;
                  OSTCBStat @ Int8u ;
                  OSTCBPrio @ Int8u ;
                  OSTCBX @ Int8u ;
                  OSTCBY @ Int8u ; 
                  OSTCBBitX @ Int8u;
                  OSTCBBitY @ Int8u;
                  OSTCBflag @ Int8u ⌟
                 }­.




Definition OS_STK : type := Int32.

Definition OS_STK_BLK : type := 
  STRUCT os_stk_blk ­{
                      ⌞nextblk @ Void ∗;
                      taskstk @ (Tarray OS_STK ∘TASK_STK_SIZE)⌟
                     }­.


 
Definition gvarlist1 : decllist := 
             ⌞ 
              OSCtxSwCtr @ Int32u ;
              OSEventList @ OS_EVENT ∗ ;
              OSEventFreeList @ OS_EVENT ∗ ;
              OSEventTbl @ (Tarray OS_EVENT ∘OS_MAX_EVENTS);
              OSIntNesting @ Int8u;                                       
              OSIntExitY @ Int8u;
              OSPrioCur @ Int8u;
              OSPrioHighRdy @ Int8u;
              OSRdyGrp @ Int8u;
              OSRdyTbl @ (Tarray Int8u ∘OS_RDY_TBL_SIZE);
              OSRunning @ Int8u                                       
             ⌟.

Definition gvarlist2 :decllist := 
             ⌞ 
              OSTaskCtr @ Int8u;
              OSIdleCtr @ Int32u;
              OSTCBCur @ OS_TCB ∗;
              OSTCBFreeList @ OS_TCB ∗;
              OSTCBHighRdy @ OS_TCB ∗; 
              OSTCBList @ OS_TCB;                                       
              OSTCBPrioTbl @ (Tarray (OS_TCB ∗ ) ∘(OS_LOWEST_PRIO + 1)%Z );
              OSTCBTbl @ (Tarray OS_TCB ∘(OS_LOWEST_PRIO + 1));
              OSQFreeBlk @ OS_Q_FREEBLK ∗;
              OSQFreeBlkTbl @ (Tarray OS_Q_FREEBLK ∘OS_MAX_QS)
            ⌟.

Definition gvarlist3 :decllist := 
             ⌞
              OSQFreeList @ OS_Q ∗;
              OSQTbl @ (Tarray OS_Q ∘OS_MAX_QS);
              OSTime @ Int32u;
              OSMapTbl @ (Tarray Int8u 8);                                                   OSUnMapTbl @ (Tarray Int8u 256)
             ⌟.


Fixpoint plus_decl  (d1 d2 : decllist) {struct d1} :=
    match d1 with
     | dnil => d2
     | dcons x t d1' => dcons x t (plus_decl d1' d2)
    end.


Definition GlobalVariables := 
  plus_decl (plus_decl gvarlist1 gvarlist2) gvarlist3.

Close Scope code_scope.
