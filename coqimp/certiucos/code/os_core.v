Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

Definition OSInit_impl :=
 Void ·OSInit·(⌞ ⌟)··{
       ⌞ ⌟;
        
      OSInitHookBegin(­);ₛ
      OS_InitMisc(­);ₛ
      OS_InitRdyList(­);ₛ
      OS_InitSTKList(­);ₛ
      OS_InitTCBList(­);ₛ
      OS_InitEventList(­);ₛ
      OS_QInit(­);ₛ
      OS_SemInit(­);ₛ
      OS_InitTaskIdle(­);ₛ
      OSInitHookEnd(­);ₛ
      RETURN 
 }·.

 
Definition OSStart_impl:= 
 Void ·OSStart·(⌞ ⌟)··{
       ⌞
        y @ Int8u;
        x @ Int8u
       ⌟;

       If (OSRunning′ ==ₑ CFalse) {
           y′ =ₑ OSUnMapTbl′[OSRdyGrp′];ₛ
           x′ =ₑ OSUnMapTbl′[OSRdyTbl′[y′]];ₛ
           OSPrioHighRdy′ =ₑ 〈Int8u〉 ((y′ ≪ ′3) +ₑ x′);ₛ
           OSPrioCur′ =ₑ OSPrioHighRdy′;ₛ
           OSTCBHighRdy′ =ₑ OSTCBPrioTbl′[OSPrioHighRdy′];ₛ
           OSTCBCur′ =ₑ OSTCBHighRdy′;ₛ
           OSStartHighRdy(­)
       };ₛ
       RETURN
 }·.


Definition OSIntEnter_impl := 
 Void ·OSIntEnter·(⌞ ⌟)··{
       ⌞ ⌟;

       If (OSRunning′ ==ₑ CTrue) {
           If (OSIntNesting′ <ₑ ′255){
                ++ OSIntNesting′
           }
       };ₛ
       RETURN
 }·.

Definition OSVersion_impl :=
 Int32 ·OSVersion·(⌞ ⌟)··{
       ⌞ ⌟;

       RETURN ′OS_VERSION 
 }·.



Definition OSIntExit_impl := 
 Void ·OSIntExit·(⌞ ⌟)··{
       ⌞x @ Int32⌟;
        
         ENTER_CRITICAL;ₛ
         x <- CHECKIS;ₛ
         If (x′ ==ₑ ′1){                
               OSIntExitY′ =ₑ OSUnMapTbl′[OSRdyGrp′];ₛ
               OSPrioHighRdy′ =ₑ  (OSIntExitY′ ≪ ′3) +ₑ
                                                        OSUnMapTbl′[OSRdyTbl′[OSIntExitY′]];ₛ
                                                                                               OSPrioCur′ =ₑ OSTCBCur′→OSTCBPrio;ₛ 
               If (OSPrioHighRdy′ !=ₑ OSPrioCur′) {
                   OSTCBHighRdy′ =ₑ OSTCBPrioTbl′[OSPrioHighRdy′];ₛ
                   ++OSCtxSwCtr′;ₛ
                   SWITCH
               };ₛ
               EXIT_CRITICAL;ₛ
               RETURN
          };ₛ
          EXIT_CRITICAL;ₛ
          RETURN
 }·.


Definition OSTimeTick_impl := 
 Void ·OSTimeTick·(⌞ ⌟)··{
        ⌞ptcb @ OS_TCB∗;
         pevent @ OS_EVENT∗;
         ptbl @ Tptr Int8u⌟;
         
        ++OSTime′;ₛ
        ptcb′ =ₑ OSTCBList′;ₛ
        WHILE (ptcb′ !=ₑ NULL) {
          If (ptcb′→ OSTCBDly !=ₑ ′0){
               ptcb′→OSTCBDly =ₑ (ptcb′→OSTCBDly) − ′1;ₛ
               If (ptcb′→OSTCBDly ==ₑ ′0) {
                 OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ ptcb′→OSTCBBitY;ₛ
                 OSRdyTbl′[ptcb′→OSTCBY] =ₑ OSRdyTbl′[ptcb′→OSTCBY] |ₑ ptcb′→OSTCBBitX;ₛ
                 ptcb′→OSTCBStat =ₑ ′OS_STAT_RDY;ₛ
                 pevent′ =ₑ ptcb′→OSTCBEventPtr;ₛ
                 If (pevent′ !=ₑ NULL){
                   ptbl′ =ₑ pevent′→OSEventTbl;ₛ
                   ptbl′[ptcb′→OSTCBY] =ₑ 
                           ptbl′[ptcb′→OSTCBY] &ₑ (∼ptcb′→OSTCBBitX);ₛ
                   If (ptbl′[ptcb′→OSTCBY] ==ₑ ′0) {
                     pevent′→OSEventGrp &=  ∼ptcb′→OSTCBBitY
                   };ₛ
                   ptcb′→OSTCBEventPtr =ₑ NULL
                 }
               }
           };ₛ
           ptcb′ =ₑ ptcb′→OSTCBNext
        };ₛ
        RETURN
 }·.

(*
Definition OS_EventTaskRdy_impl := 
Int8u ·OS_EventTaskRdy·(⌞pevent @ OS_EVENT∗; message @ Void∗ ;  msk @ Int8u⌟)··{
       ⌞
        ptcb @ OS_TCB∗;
        x @ Int8u;
        y @ Int8u;
        bitx @ Int8u;
        bity @ Int8u;
        prio @ Int8u
       ⌟;

       y′ =ₑ OSUnMapTbl′[pevent′→OSEventGrp];ₛ
       bity′ =ₑ OSMapTbl′[y′];ₛ
       x′ =ₑ OSUnMapTbl′[pevent′→OSEventTbl[y′]];ₛ
       bitx′ =ₑ OSMapTbl′[x′];ₛ
       prio′ =ₑ ((y′ ≪ ′3) +ₑ x′);ₛ
       pevent′→OSEventTbl[y′] =ₑ pevent′→OSEventTbl[y′] &ₑ (∼bitx′);ₛ
       If (pevent′→OSEventTbl[y′] ==ₑ ′0) {
           pevent′→OSEventGrp =ₑ pevent′→OSEventGrp &ₑ (∼bity′)
       };ₛ
       ptcb′ =ₑ OSTCBPrioTbl′[prio′];ₛ
       ptcb′→OSTCBDly =ₑ ′0;ₛ
       ptcb′→OSTCBEventPtr =ₑ  NULL;ₛ
       ptcb′→OSTCBMsg =ₑ message′;ₛ
       ptcb′→OSTCBStat =ₑ (ptcb′→OSTCBStat) &ₑ (∼msk′);ₛ
       If (ptcb′→OSTCBStat ==ₑ ′OS_STAT_RDY){
         OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ bity′;ₛ
         OSRdyTbl′[y′] =ₑ OSRdyTbl′[y′] |ₑ bitx′
       };ₛ
       RETURN prio′
 }·.
 *)

Definition OS_EventTaskRdy_impl :=
Int8u ·OS_EventTaskRdy·(⌞pevent @ OS_EVENT∗; message @ Void∗ ;  msk @ Int8u⌟)··{
       ⌞
        ptcb @ OS_TCB∗;
        x @ Int8u;
        y @ Int8u;
        bitx @ Int8u;
        bity @ Int8u;
        prio @ Int8u
       ⌟;

       y′ =ₑ OSUnMapTbl′[pevent′→OSEventGrp];ₛ
       bity′ =ₑ OSMapTbl′[y′];ₛ
       x′ =ₑ OSUnMapTbl′[pevent′→OSEventTbl[y′]];ₛ
       bitx′ =ₑ OSMapTbl′[x′];ₛ
       prio′ =ₑ ((y′ ≪ ′3) +ₑ x′);ₛ
       pevent′→OSEventTbl[y′] =ₑ pevent′→OSEventTbl[y′] &ₑ (∼bitx′);ₛ
       If (pevent′→OSEventTbl[y′] ==ₑ ′0) {
           pevent′→OSEventGrp =ₑ pevent′→OSEventGrp &ₑ (∼bity′)
       };ₛ
       ptcb′ =ₑ OSTCBPrioTbl′[prio′];ₛ
       ptcb′→OSTCBDly =ₑ ′0;ₛ
       ptcb′→OSTCBEventPtr =ₑ NULL;ₛ
       ptcb′→OSTCBMsg =ₑ message′;ₛ
       ptcb′→OSTCBStat =ₑ (ptcb′→OSTCBStat) &ₑ (∼msk′);ₛ
       OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ bity′;ₛ
       OSRdyTbl′[y′] =ₑ OSRdyTbl′[y′] |ₑ bitx′;ₛ
       RETURN prio′
 }·.



Definition OS_EventTaskWait_impl := 
Void ·OS_EventTaskWait·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞ ⌟;

       OSTCBCur′→OSTCBEventPtr =ₑ pevent′;ₛ
       OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ 
                 OSRdyTbl′[OSTCBCur′→OSTCBY] &ₑ (∼OSTCBCur′→OSTCBBitX);ₛ
       If (OSRdyTbl′[OSTCBCur′→OSTCBY] ==ₑ ′0) {
           OSRdyGrp′ =ₑ OSRdyGrp′ &ₑ (∼OSTCBCur′→OSTCBBitY)
       };ₛ
       pevent′→OSEventTbl[OSTCBCur′→OSTCBY] =ₑ 
               pevent′→OSEventTbl[OSTCBCur′→OSTCBY] |ₑ OSTCBCur′→OSTCBBitX;ₛ
       pevent′→OSEventGrp =ₑ pevent′→OSEventGrp |ₑ OSTCBCur′→OSTCBBitY;ₛ
       RETURN
}·.    

Definition OS_EventTO_impl :=
Void ·OS_EventTO·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞ ⌟;

       pevent′→OSEventTbl[OSTCBCur′→OSTCBY] =ₑ 
          pevent′→OSEventTbl[OSTCBCur′→OSTCBY] &ₑ (∼OSTCBCur′→OSTCBBitX);ₛ
       If (pevent′→OSEventTbl[OSTCBCur′→OSTCBY] ==ₑ ′0) {
          pevent′→OSEventGrp &=  ∼OSTCBCur′→OSTCBBitY
       };ₛ
       OSTCBCur′→OSTCBStat =ₑ ′OS_STAT_RDY;ₛ
       OSTCBCur′→OSTCBEventPtr =ₑ NULL;ₛ
       RETURN
}·.    


Definition OS_Sched_impl := 
Void ·OS_Sched·(⌞ ⌟)··{
       ⌞y @ Int8u⌟;

        ENTER_CRITICAL;ₛ
        y′ =ₑ OSUnMapTbl′[OSRdyGrp′];ₛ
        OSPrioHighRdy′ =ₑ  ((y′ ≪ ′3) +ₑ OSUnMapTbl′[OSRdyTbl′[y′]]);ₛ
        OSPrioCur′ =ₑ OSTCBCur′→OSTCBPrio;ₛ             
        If (OSPrioHighRdy′ !=ₑ OSPrioCur′) {
            OSTCBHighRdy′ =ₑ OSTCBPrioTbl′[OSPrioHighRdy′];ₛ
            ++ OSCtxSwCtr′;ₛ
            SWITCH
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN
}·. 



Definition OS_TaskIdle_impl :=
Void · OS_TaskIdle·(⌞ ⌟)··{
       ⌞ ⌟;

       WHILE(′1) {
           ENTER_CRITICAL;ₛ
           OSIdleCtr′ =ₑ OSIdleCtr′ +ₑ ′1;ₛ
           EXIT_CRITICAL
       };ₛ
       RETURN
}·. 


Definition OS_EventWaitListInit_impl  :=
Void · OS_EventWaitListInit·(⌞pevent @ OS_EVENT∗ ⌟)··{
       ⌞ptbl @ Int8u∗⌟;

       pevent′→OSEventGrp =ₑ ′0;ₛ
       ptbl′ =ₑ &ₐ pevent′→OSEventTbl[′0];ₛ
       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ∗ptbl′ =ₑ ′0;ₛ
       RETURN
}·. 


Definition OS_InitEventList_impl := 
Void ·OS_InitEventList·(⌞⌟)··{
      ⌞ 
      i @ Int16u;
      pevent1 @ OS_EVENT∗;
      pevent2 @ OS_EVENT∗
     ⌟;

      pevent1′ =ₑ &ₐ OSEventTbl′[′0];ₛ
      pevent2′ =ₑ &ₐ OSEventTbl′[′1];ₛ
      i′ =ₑ ′0;ₛ
      WHILE (i′ <ₑ (′OS_MAX_EVENTS − ′1)) {
          pevent1′→OSEventType =ₑ ′OS_EVENT_TYPE_UNUSED;ₛ
          pevent1′→OSEventListPtr =ₑ pevent2′;ₛ
          pevent1′→OSEventPtr =ₑ NULL;ₛ
          ++ pevent1′;ₛ
          ++ pevent2′;ₛ
          ++ i′
      };ₛ
      pevent1′→OSEventType =ₑ ′OS_EVENT_TYPE_UNUSED;ₛ
      pevent1′→OSEventPtr =ₑ NULL;ₛ
      pevent1′→OSEventListPtr =ₑ NULL;ₛ
      OSEventFreeList′ =ₑ &ₐ OSEventTbl′[′0];ₛ
      OSEventList′ =ₑ NULL;ₛ
      RETURN
}·.


Definition OS_InitMisc_impl :=
 Void ·OS_InitMisc·(⌞ ⌟)··{
       ⌞ ⌟;

       OSTime′ =ₑ ′0;ₛ
(*       OSIntNesting′ =ₑ ′0;ₛ *)
(*       OSLockNesting′ =ₑ ′0;ₛ *)
       OSTaskCtr′ =ₑ ′0;ₛ
       OSRunning′ =ₑ CFalse;ₛ
       OSCtxSwCtr′ =ₑ ′0;ₛ
       OSIdleCtr′ =ₑ ′0;ₛ
       OSIdleCtrRun′ =ₑ ′0;ₛ
       OSIdleCtrMax′ =ₑ  ′0;ₛ
       OSStatRdy′ =ₑ CFalse;ₛ
       RETURN
 }·.

Definition OS_InitRdyList_impl :=
 Void ·OS_InitRdyList·(⌞ ⌟)··{
       ⌞i @ Int16u; prdytbl @ Int8u∗⌟;

        OSRdyGrp′ =ₑ ′0;ₛ
        prdytbl′ =ₑ &ₐ OSRdyTbl′[′0];ₛ
        i′ =ₑ ′0;ₛ
        WHILE (i′ <ₑ ′OS_RDY_TBL_SIZE) {
          ∗prdytbl′ =ₑ ′0 ;ₛ 
           ++ prdytbl′;ₛ
           ++ i′
        };ₛ
        OSPrioCur′ =ₑ ′0;ₛ
        OSPrioHighRdy′ =ₑ ′0;ₛ
        OSTCBHighRdy′ =ₑ NULL;ₛ
        OSTCBCur′ =ₑ NULL;ₛ
        RETURN
 }·.


Definition OS_InitTaskIdle_impl :=
 Void ·OS_InitTaskIdle·(⌞ ⌟)··{
       ⌞ ⌟;
    
       OSTaskCreate(­OS_TaskIdle′, NULL, ′OS_IDLE_PRIO ­);ₛ
       RETURN
 }·.


Definition OS_InitSTKList_impl := 
 Void ·OS_InitSTKList·(⌞ ⌟)··{
       ⌞
        i @ Int8u; 
        pstk1 @ OS_STK_BLK∗;
        pstk2 @ OS_STK_BLK∗ 
       ⌟;
    
        pstk1′ =ₑ &ₐOSSTKTbl′[′0];ₛ
        pstk2′ =ₑ  &ₐOSSTKTbl′[′1];ₛ
        i′ =ₑ ′0;ₛ
        WHILE (i′ <ₑ (′OS_MAX_TASKS +ₑ ′OS_N_SYS_TASKS)) {
            pstk1′→nextblk =ₑ pstk2′;ₛ
            ++pstk1′;ₛ
            ++pstk2′;ₛ
            ++i′
        };ₛ
        pstk1′→nextblk =ₑ NULL;ₛ
        OSSTKFreeList′ =ₑ &ₐ OSSTKTbl′[′0];ₛ
        RETURN
}· .

Definition OS_InitTCBList_impl :=
Void ·OS_InitTCBList·(⌞ ⌟)··{
       ⌞
        i @ Int8u; 
        ptcb1 @ OS_TCB∗;
        ptcb2 @ OS_TCB∗ 
       ⌟;
       
       OSTCBList′ =ₑ NULL;ₛ
       i′ =ₑ ′0;ₛ
       WHILE (i′ <ₑ (′OS_LOWEST_PRIO +ₑ ′1)){
           OSTCBPrioTbl′[i′] =ₑ NULL;ₛ
           ++i′
       };ₛ
       ptcb1′ =ₑ  &ₐ OSTCBTbl′[′0];ₛ
       ptcb2′ =ₑ  &ₐ OSTCBTbl′[′1];ₛ
       i′ =ₑ ′0;ₛ
       WHILE (i′ <ₑ (′OS_MAX_TASKS +ₑ ′OS_N_SYS_TASKS − ′1)) {
           ptcb1′→OSTCBNext =ₑ ptcb2′;ₛ
           ++ptcb1′;ₛ
           ++ptcb2′;ₛ
           ++i′
       };ₛ
       ptcb1′→OSTCBNext =ₑ NULL;ₛ
       OSTCBFreeList′ =ₑ &ₐ OSTCBTbl′[′0];ₛ
       RETURN
}·.


Definition OS_TCBInit_impl  :=
 Int8u ·OS_TCBInit·(⌞prio @ Int8u (*; task @ Int32 ;  pdata @ Void∗ *)⌟)··{
        ⌞ptcb @ OS_TCB∗⌟;
 
        ptcb′ =ₑ OSTCBFreeList′;ₛ
        If (ptcb′ !=ₑ NULL) {
            OSTCBFreeList′ =ₑ ptcb′→OSTCBNext;ₛ
            ptcb′→OSTCBPrio =ₑ (*〈Int8u〉*) prio′;ₛ
            ptcb′→OSTCBStat =ₑ ′OS_STAT_RDY;ₛ
            ptcb′→OSTCBDly =ₑ ′0;ₛ
            ptcb′→OSTCBY =ₑ prio′ ≫ ′3;ₛ
            ptcb′→OSTCBBitY =ₑ OSMapTbl′[ptcb′→OSTCBY];ₛ
            ptcb′→OSTCBX =ₑ prio′ &ₑ ′7;ₛ
            ptcb′→OSTCBBitX =ₑ OSMapTbl′[ptcb′→OSTCBX];ₛ
            ptcb′→OSTCBEventPtr =ₑ NULL;ₛ
            ptcb′→OSTCBMsg =ₑ NULL;ₛ
            OSTCBPrioTbl′[prio′] =ₑ ptcb′;ₛ
            ptcb′→OSTCBNext =ₑ OSTCBList′;ₛ
            ptcb′→OSTCBPrev =ₑ NULL;ₛ

                        
            OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ ptcb′→OSTCBBitY;ₛ
            OSRdyTbl′[ptcb′→OSTCBY] =ₑ 
                    OSRdyTbl′[ptcb′→OSTCBY] |ₑ ptcb′→OSTCBBitX;ₛ
                                      
            If(OSTCBList′ !=ₑ NULL) {
                OSTCBList′→OSTCBPrev =ₑ ptcb′
            };ₛ
            OSTCBList′ =ₑ ptcb′;ₛ
            (*set flag to 1*)                
            ptcb′→OSTCBflag =ₑ ′1;ₛ
                          
            RETURN ′OS_NO_ERR 
        };ₛ

        RETURN ′OS_NO_MORE_TCB         
 }·.



Definition OS_EventRemove_impl :=
Void ·OS_EventRemove·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞p @ OS_EVENT∗; x @ Int8u; p1 @ OS_EVENT∗⌟;

       p′ =ₑ OSEventList′;ₛ
       p1′ =ₑ OSEventList′;ₛ
       x′ =ₑ ′0;ₛ
       If (p′ ==ₑ pevent′){
           OSEventList′ =ₑ OSEventList′→OSEventListPtr;ₛ
           RETURN
       };ₛ

       WHILE (p′ !=ₑ NULL &&ₑ x′ ==ₑ ′0) {
         p1′ =ₑ p′→OSEventListPtr;ₛ
         IF (p1′ !=ₑ pevent′){
             p′ =ₑ p1′ 
         }ELSE{
             x′ =ₑ ′1
         }
       };ₛ
          
       If (x′ ==ₑ ′1){
           p′→OSEventListPtr =ₑ p1′→OSEventListPtr
       };ₛ
       RETURN
}·.


Definition OS_EventSearch_impl := 
Int8u ·OS_EventSearch·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞p @ OS_EVENT∗; x @ Int8u; p1 @ OS_EVENT∗⌟;

       p′ =ₑ OSEventList′;ₛ
       x′ =ₑ ′0;ₛ
       WHILE (p′ !=ₑ NULL &&ₑ x′ ==ₑ ′0) {
         p1′ =ₑ p′→OSEventListPtr;ₛ
         IF (p′ !=ₑ pevent′){
             p′ =ₑ p1′ 
         }ELSE{
             x′ =ₑ ′1
         }
       };ₛ
       RETURN x′ 
}·.


(*Definition OS_IsSomeMutexOwner_impl := 
Int8u ·OS_IsSomeMutexOwner·(⌞ptcb @ OS_TCB∗⌟)··{
       ⌞p @ OS_EVENT∗; x @ Int8u; p1 @ OS_EVENT∗⌟;
       (* If (ptcb ′ ==ₑ NULL){
        *   RETURN ′ 2 
        * };ₛ *)

       p′ =ₑ OSEventList′;ₛ
       x′ =ₑ ′0;ₛ
       WHILE (p′ !=ₑ NULL &&ₑ x′ ==ₑ ′0) {
         p1′ =ₑ p′→OSEventListPtr;ₛ
         IF (p′ → OSEventPtr !=ₑ ptcb′ ||ₑ p′ → OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX ){
             p′ =ₑ p1′ 
         }ELSE{
             x′ =ₑ ′1
         }
       };ₛ
       RETURN x′ 
}·.
     (* (get ecbls eid = Some (absmutexsem pr (Some (tid, opr)), wls)) ->
      * tid <> ptcb *)
*)

Definition OS_IsSomeMutexOwner_impl := 
Int8u ·OS_IsSomeMutexOwner·(⌞ptcb @ OS_TCB∗⌟)··{
       ⌞p @ OS_EVENT∗; x @ Int8u⌟;
       p′ =ₑ OSEventList′;ₛ
       x′ =ₑ ′0;ₛ
       WHILE (p′ !=ₑ NULL &&ₑ x′ ==ₑ ′0) {
         IF (p′ → OSEventPtr !=ₑ ptcb′ ||ₑ p′ → OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX ){
             p′ =ₑ p′→OSEventListPtr
         }ELSE{
             x′ =ₑ ′1
         }
       };ₛ
       RETURN x′ 
}·.


Close Scope code_scope.


