Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.


Open Scope code_scope.



Definition OSTimeDly_impl := 
      Void ·OSTimeDly·(⌞ticks @ Int16u⌟)··{
             ⌞ ⌟;

             If (ticks′ >ₑ ′0)
             {
               ENTER_CRITICAL;ₛ
               If (OSTCBCur′→OSTCBPrio ==ₑ ′OS_IDLE_PRIO){
                 EXIT_CRITICAL;ₛ
                 RETURN                
               };ₛ
               IF ((OSTCBCur′→OSTCBStat  ==ₑ ′OS_STAT_RDY) &&ₑ (OSTCBCur′→OSTCBDly  ==ₑ ′0)){
                 OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ OSRdyTbl′[OSTCBCur′→OSTCBY]&ₑ(∼OSTCBCur′→OSTCBBitX);ₛ
                 If (OSRdyTbl′[OSTCBCur′→OSTCBY] ==ₑ ′0)
                 {
                   OSRdyGrp′ =ₑ OSRdyGrp′ &ₑ (∼OSTCBCur′→OSTCBBitY)
                 };ₛ
                 OSTCBCur′→OSTCBDly =ₑ ticks′;ₛ
                 EXIT_CRITICAL;ₛ
                 OS_Sched(­)
               }ELSE{
                 EXIT_CRITICAL
               }
             };ₛ
             RETURN
           }·.

Definition OSTimeGet_impl :=
       Int32u ·OSTimeGet·(⌞⌟)··{
              ⌞ 
                ticks @ Int32u
              ⌟;

              ENTER_CRITICAL;ₛ
              ticks′ =ₑ OSTime′;ₛ
              EXIT_CRITICAL;ₛ
              RETURN ticks′
       }·.

Close Scope code_scope.
