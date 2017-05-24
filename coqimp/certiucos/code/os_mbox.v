Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

(*os_mbox.c*)
Open Scope code_scope.

Definition OSMboxCreate_impl := 
OS_EVENT ∗ ·OSMboxCreate·(⌞message @ Void ∗⌟)··{
           ⌞
              pevent @ OS_EVENT∗
           ⌟;

            ENTER_CRITICAL;ₛ
            pevent′ =ₑ OSEventFreeList′;ₛ
            If (OSEventFreeList′ !=ₑ NULL){
                OSEventFreeList′ =ₑ  〈OS_EVENT∗〉 OSEventFreeList′→OSEventListPtr
            };ₛ
           If (pevent′ !=ₑ NULL) {
               OS_EventWaitListInit(­pevent′­);ₛ
               pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_MBOX;ₛ
               pevent′→OSEventCnt =ₑ ′0;ₛ
               pevent′→OSEventPtr =ₑ message′;ₛ
               pevent ′ → OSEventListPtr =ₑ OSEventList ′;ₛ
               OSEventList′ =ₑ pevent′
           };ₛ
           EXIT_CRITICAL;ₛ
           RETURN pevent′
}·.

Definition OSMboxDel_impl := 
 Int8u ·OSMboxDel·(⌞ pevent @ OS_EVENT ∗⌟)··{
        ⌞ 
         tasks_waiting @ Int8u;
         legal @ Int8u
        ⌟; 
         
        If (pevent′ ==ₑ  NULL){
             RETURN  ′MBOX_DEL_NULL_ERR
        };ₛ
        ENTER_CRITICAL;ₛ
        legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
        If (legal′ ==ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN  ′MBOX_DEL_P_NOT_LEGAL_ERR
        };ₛ 
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MBOX){
            EXIT_CRITICAL;ₛ
            RETURN  ′MBOX_DEL_WRONG_TYPE_ERR
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
            RETURN  ′MBOX_DEL_SUCC
        }ELSE{
            EXIT_CRITICAL;ₛ
            RETURN  ′MBOX_DEL_TASK_WAITING_ERR
        }    
 }· . 

Definition OSMboxAccept_impl := 
 Void ∗ ·OSMboxAccept·(⌞pevent @ OS_EVENT∗⌟)··{
        ⌞ 
          message @ Void ∗;
          legal @ Int8u
        ⌟; 
               
          If(pevent′ ==ₑ NULL){
              RETURN  〈Void ∗〉 NULL 
          };ₛ
          ENTER_CRITICAL;ₛ
          legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
          If (legal′ ==ₑ ′0){
              EXIT_CRITICAL;ₛ
              RETURN 〈Void ∗〉 NULL 
          };ₛ
          If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MBOX){
            EXIT_CRITICAL;ₛ
            RETURN 〈Void ∗〉 NULL 
          };ₛ
          message′ =ₑ pevent′→OSEventPtr;ₛ
          pevent′→OSEventPtr =ₑ NULL;ₛ
          EXIT_CRITICAL;ₛ
          RETURN  message′ 
 }· .


Definition OSMboxPost_impl := 
 Int8u ·OSMboxPost·(⌞pevent @ OS_EVENT∗ ;  message @ Void∗⌟)··{
         ⌞ 
                 legal @ Int8u
         ⌟; 
         If (pevent′ ==ₑ NULL){
                 RETURN  ′OS_ERR_PEVENT_NULL
         };ₛ
         If (message′ ==ₑ NULL){
                 RETURN  ′OS_ERR_POST_NULL_PTR
         };ₛ
         ENTER_CRITICAL;ₛ
         legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
         If (legal′ ==ₑ ′0){
                 EXIT_CRITICAL;ₛ
                 RETURN  ′MBOX_POST_P_NOT_LEGAL_ERR
         };ₛ
         If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MBOX){
                 EXIT_CRITICAL;ₛ
                 RETURN  ′OS_ERR_EVENT_TYPE
         };ₛ
         If (pevent′→OSEventGrp !=ₑ ′0) {
                 legal′ =ₑ ′OS_STAT_MBOX;ₛ 
                 OS_EventTaskRdy(­pevent′, message′, legal′ (* ′OS_STAT_MBOX *) ­);ₛ
                 EXIT_CRITICAL;ₛ
                 OS_Sched(­);ₛ
                 RETURN  ′OS_NO_ERR 
         };ₛ
         If (pevent′→OSEventPtr !=ₑ  NULL) {
                 EXIT_CRITICAL;ₛ
                 RETURN  ′ MBOX_POST_FULL_ERR
         };ₛ
         pevent′→OSEventPtr =ₑ  message′;ₛ
         EXIT_CRITICAL;ₛ
         RETURN  ′OS_NO_ERR 
 }· .

 
Definition OSMboxPend_impl :=
 Int8u ·OSMboxPend·(⌞ pevent @ OS_EVENT ∗; timeout @ Int16u ⌟)··{
         ⌞ 
         message @ Void∗;
         legal @ Int8u
        ⌟; 

        If (pevent′ ==ₑ  NULL){
             RETURN  ′MBOX_PEND_NULL_ERR
        };ₛ
        ENTER_CRITICAL;ₛ
        legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
        If (legal′ ==ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN  ′MBOX_PEND_P_NOT_LEGAL_ERR
        };ₛ 
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MBOX){
            EXIT_CRITICAL;ₛ
            RETURN  ′MBOX_PEND_WRONG_TYPE_ERR
        };ₛ
        If (OSTCBCur′→OSTCBPrio ==ₑ ′OS_IDLE_PRIO){
            EXIT_CRITICAL;ₛ
            RETURN  ′MBOX_PEND_FROM_IDLE_ERR
        };ₛ
        If ( (OSTCBCur′→OSTCBStat  !=ₑ ′OS_STAT_RDY) ||ₑ (OSTCBCur′→OSTCBDly  !=ₑ ′0)){
            EXIT_CRITICAL;ₛ
            RETURN  ′MBOX_PEND_NOT_READY_ERR
        };ₛ     
        message′ =ₑ pevent′→OSEventPtr;ₛ
        If (message′ !=ₑ NULL) {
            pevent′→OSEventPtr =ₑ NULL;ₛ
            OSTCBCur′→OSTCBMsg =ₑ message′;ₛ
            EXIT_CRITICAL;ₛ
            RETURN  ′MBOX_PEND_SUCC 
        };ₛ
        OSTCBCur′→OSTCBMsg =ₑ NULL;ₛ
        OSTCBCur′→OSTCBStat =ₑ ′OS_STAT_MBOX;ₛ
        OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ
        OS_EventTaskWait(­pevent′­);ₛ
        EXIT_CRITICAL;ₛ
        OS_Sched(­);ₛ
        ENTER_CRITICAL;ₛ
        message′ =ₑ OSTCBCur′→OSTCBMsg;ₛ                                 
        If (message′ !=ₑ NULL){
          
            EXIT_CRITICAL;ₛ
            RETURN  ′MBOX_PEND_SUCC
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN  ′MBOX_PEND_TIMEOUT_ERR
  }· .

Close Scope code_scope.
