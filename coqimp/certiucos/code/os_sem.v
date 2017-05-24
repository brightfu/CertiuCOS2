Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.


(*os_sem.c*)
Open Scope code_scope.

Definition OSSemAccept_impl := 
Int16u ·OSSemAccept·(⌞pevent @ OS_EVENT∗⌟)··{
        ⌞
         cnt @ Int16u; 
         legal @ Int8u
        ⌟;

        If (pevent′ ==ₑ NULL){
             RETURN  ′0
        };ₛ
        ENTER_CRITICAL;ₛ
        legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
        If (legal′ ==ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN  ′0
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
            EXIT_CRITICAL;ₛ
            RETURN  ′0
        };ₛ
        cnt′ =ₑ pevent′→OSEventCnt;ₛ
        If (cnt′ >ₑ ′0){
            −−pevent′→OSEventCnt
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN  cnt′
}· .

Definition OSSemCreate_impl := 
OS_EVENT∗ ·OSSemCreate·(⌞cnt @ Int16u⌟)··{
           ⌞pevent @ OS_EVENT∗⌟;

            ENTER_CRITICAL;ₛ
            pevent′ =ₑ OSEventFreeList′;ₛ
            If (OSEventFreeList′ !=ₑ NULL){
                OSEventFreeList′ =ₑ  〈OS_EVENT∗〉 OSEventFreeList′→OSEventListPtr
            };ₛ
           If (pevent′ !=ₑ NULL) {
               OS_EventWaitListInit(­pevent′­);ₛ
               pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_SEM;ₛ
               pevent′→OSEventCnt =ₑ cnt′;ₛ
               pevent′→OSEventPtr =ₑ NULL;ₛ
               pevent′→OSEventListPtr =ₑ OSEventList′;ₛ
               OSEventList′ =ₑ pevent′
           };ₛ
           EXIT_CRITICAL;ₛ
           RETURN  pevent′
 }·.


Definition OSSemDel_impl :=
Int8u ·OSSemDel·(⌞pevent @ OS_EVENT∗⌟)··{
           ⌞
             tasks_waiting @ Int8u ;
             legal @ Int8u
           ⌟;

            If (pevent′ ==ₑ NULL){
                RETURN  ′OS_ERR_PEVENT_NULL
            };ₛ
            ENTER_CRITICAL;ₛ
            legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
            If (legal′ ==ₑ ′0){
                EXIT_CRITICAL;ₛ
                RETURN  ′OS_ERR_PEVENT_NULL
            };ₛ
            If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
                EXIT_CRITICAL;ₛ
                RETURN  ′OS_ERR_EVENT_TYPE
            };ₛ
            IF (pevent′→OSEventGrp !=ₑ ′0){
                tasks_waiting′ =ₑ ′1
            }ELSE{
                tasks_waiting′ =ₑ ′0
            };ₛ
            IF (tasks_waiting′ ==ₑ ′0){
                OS_EventRemove(­pevent′­);ₛ
                pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_UNUSED;ₛ
                pevent′→OSEventListPtr =ₑ OSEventFreeList′;ₛ
                OSEventFreeList′ =ₑ pevent′;ₛ
                EXIT_CRITICAL;ₛ
                RETURN  ′OS_NO_ERR 
            }ELSE{
                EXIT_CRITICAL;ₛ
                RETURN  ′OS_ERR_TASK_WAITING
            }
}·.


Definition OSSemPend_impl  :=
Int8u ·OSSemPend·(⌞pevent @ OS_EVENT∗; timeout @ Int16u⌟)··{
       ⌞legal @ Int8u⌟;


        If (pevent′ ==ₑ NULL){
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ
        ENTER_CRITICAL;ₛ
        legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
        If (legal′ ==ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ
        If (OSTCBCur′→OSTCBPrio ==ₑ ′OS_IDLE_PRIO){
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ
        If ( (OSTCBCur′→OSTCBStat  !=ₑ ′OS_STAT_RDY) ||ₑ (OSTCBCur′→OSTCBDly  !=ₑ ′0)){
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ     
        If (pevent′→OSEventCnt >ₑ ′0){
            −−pevent′→OSEventCnt;ₛ
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_NO_ERR
        };ₛ
        If (OSTCBCur′→OSTCBMsg !=ₑ NULL) {
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_PEVENT_NULL 
        };ₛ
        OSTCBCur′→OSTCBStat =ₑ ′OS_STAT_SEM;ₛ
        OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ
        OS_EventTaskWait(­pevent′­);ₛ 
        EXIT_CRITICAL;ₛ
        OS_Sched(­);ₛ
        ENTER_CRITICAL;ₛ
        If (OSTCBCur′→OSTCBMsg ==ₑ NULL) {
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_TIMEOUT
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN  ′OS_NO_ERR
}· .


Definition OSSemPost_impl := 
Int8u ·OSSemPost·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞
         legal @ Int8u;
         x  @ Int8u
       ⌟;


        If (pevent′ ==ₑ NULL){
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ
        ENTER_CRITICAL;ₛ
        legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
        If (legal′ ==ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ
        If (pevent′→OSEventGrp !=ₑ ′0){
            x′ =ₑ ′OS_STAT_SEM;ₛ 
            OS_EventTaskRdy(­pevent′, 〈Void ∗〉 pevent′, x′­);ₛ
            EXIT_CRITICAL;ₛ
            OS_Sched(­);ₛ
            RETURN  ′OS_NO_ERR
        };ₛ
        If (pevent′→OSEventCnt <ₑ ′65535){
            pevent′→OSEventCnt =ₑ pevent′→OSEventCnt +ₑ ′1;ₛ
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_NO_ERR
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN  ′OS_SEM_OVF
}·.

Close Scope code_scope.
