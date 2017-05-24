Require Import os_code_defs.
Require Import os_ucos_h.

Local Open Scope code_scope.

Definition PlaceHolder:= &ₐ OSPlaceHolder′.
                          
(*
Definition OSTaskChangePrio_impl :=
Int32 ·OSTaskChangePrio·(⌞oldprio @ Int8u; newprio @ Int8u⌟)··{
      ⌞
        ptcb @ OS_TCB∗;
        x @ Int8u;
        y @ Int8u;
        bitx @ Int8u;
        bity @ Int8u
      ⌟;

      If( (oldprio′ ≥ ′OS_LOWEST_PRIO &&ₑ oldprio′ !=ₑ ′OS_PRIO_SELF) ||ₑ (newprio′ ≥ ′OS_LOWEST_PRIO) )
      {
        RETURN ′OS_PRIO_INVALID
      };ₛ
          
      ENTER_CRITICAL;ₛ
      If (OSTCBPrioTbl′[newprio′] !=ₑ NULL) (*newprio exist or newprio is vhold*)
      {
        EXIT_CRITICAL;ₛ
        RETURN ′OS_PRIO_EXIST
      };ₛ

      If (oldprio′ ==ₑ ′OS_PRIO_SELF)
      {
        oldprio′ =ₑ OSTCBCur′→OSTCBPrio
      };ₛ

      If (OSTCBPrioTbl′[oldprio′] ==ₑ NULL)
      {
        EXIT_CRITICAL;ₛ
        RETURN ′OS_PRIO_ERR
      };ₛ

      If (OSTCBPrioTbl′[oldprio′] ==ₑ PlaceHolder)
      {
        EXIT_CRITICAL;ₛ
        RETURN ′OS_PRIO_ERR
      };ₛ

      y′ =ₑ ′newprio ≫ ′3;ₛ
      bity′ =ₑ ′OSMapTbl[′y];ₛ
      x′ =ₑ ′newprio &ₑ ′7;ₛ
      bitx′ =ₑ ′OSMapTbl[′x];ₛ
                    
      ptcb′ =ₑ OSTCBPrioTbl′[oldprio′];ₛ
      OSTCBPrioTbl′[oldprio′] =ₑ NULL;ₛ

      IF((OSRdyTbl′[ptcb′→OSTCBY] &&ₑ ptcb′→OSTCBBitX) !=ₑ ′0)
      {
        OS_RdyTblClearBit(­ptcb′­);ₛ
        OSRdyGrp′ =ₑ ′OSRdyGrp |ₑ ′bity;ₛ
        OSRdyTbl′[y′] =ₑ ′OSRdyTbl[y′] |ₑ ′bitx
      }
      ELSE
      {
        pevent′ =ₑ ′ptcb→OSTCBEventPtr;ₛ
        If(pevent′ !=ₑ NULL)
        {
          pevent′→OSEventTbl[ptcb′→OSTCBY] &= ∼ptcb′→OSTCBBitX;ₛ
          If(pevent′→OSEventTbl[ptcb′→OSTCBY] ==ₑ ′0)
          {
            pevent′→OSEventGrp &= ′ptcb→OSTCBBitY
          };ₛ
          pevent′→OSEventGrp =ₑ pevent′→OSEventGrp |ₑ ′bity;ₛ
          pevent′→OSEventTbl[y′] =ₑ pevent′→OSEventTbl[y′] |ₑ ′bitx
        }        
      };ₛ

      OSTCBPrioTbl′[newprio′] =ₑ ′ptcb;ₛ
      ptcb′→OSTCBPrio =ₑ ′newprio;ₛ
      ptcb′→OSTCBY =ₑ ′y;ₛ
      ptcb′→OSTCBX =ₑ ′x;ₛ
      ptcb′→OSTCBBitY =ₑ ′bity;ₛ
      ptcb′→OSTCBBitX =ₑ ′bitx;ₛ

      EXIT_CRITICAL;ₛ
      OS_Sched(­);ₛ
      RETURN ′OS_NO_ERR
 }·.
*)
Definition STKINIT (a : expr * expr * expr ) :=
  let ( vt, v3 ) := a in let (v1, v2) := vt in  sprim (stkinit v1 v2 v3).

Definition OSTaskCreate_impl :=
Int8u ·OSTaskCreate·(⌞task @ Void∗; pdata @ Void∗; prio @ Int8u⌟)··{
       ⌞ err @ Int8u⌟;

       If(prio′ >ₑ ′OS_LOWEST_PRIO) {
           RETURN ′OS_PRIO_INVALID
       };ₛ
           
       ENTER_CRITICAL;ₛ
       If (OSTCBPrioTbl′[prio′] ==ₑ NULL){
           (*OSTCBPrioTbl′[prio′] =ₑ ′ 1;ₛ (*Fix Me*)
           EXIT_CRITICAL;ₛ *)
         
           err′ =ᶠ OS_TCBInit(·prio′ (*, task′, pdata′*) ·);ₛ
           IF (err′ ==ₑ ′OS_NO_ERR) {
               (*ENTER_CRITICAL;ₛ*)
               STKINIT (task′, pdata′,  OSTCBPrioTbl′[prio′ ]);ₛ
               (* ++ OSTaskCtr′;ₛ *)
               EXIT_CRITICAL;ₛ
               (* If (OSRunning′ ==ₑ CTrue) { *)
                OS_Sched(­)
               (* } *)
           }ELSE{
               (*ENTER_CRITICAL;ₛ*)
               (* OSTCBPrioTbl′[prio′] =ₑ NULL;ₛ *)
               EXIT_CRITICAL
           };ₛ
           RETURN  err′ 
       };ₛ
       EXIT_CRITICAL;ₛ
       RETURN  ′OS_PRIO_EXIST
}·.

Definition STKFREE (a : expr ) :=
  sprim (stkfree a).
 
Require Import inline_definitions.
Require Import inline_bittblfunctions.

Definition OSTaskDel_impl := 
Int8u ·OSTaskDel·(⌞prio @ Int8u⌟)··{
      ⌞
        pevent @ OS_EVENT∗;
        ptcb @ OS_TCB∗;
        self @ Int8u;
        x @ OS_TCB∗
      ⌟;
(*      
      If (OSIntNesting′ >ₑ ′0){
          RETURN (OSTaskDel) ′OS_TASK_DEL_ISR
      };ₛ
*)

      If (prio′ ==ₑ ′OS_IDLE_PRIO) {
          RETURN ′OS_TASK_DEL_IDLE
      };ₛ
      If (prio′ ≥ ′OS_LOWEST_PRIO (* &&ₑ prio′ !=ₑ ′OS_PRIO_SELF *)){
          RETURN ′OS_PRIO_INVALID
      };ₛ
      ENTER_CRITICAL;ₛ
      (* If(prio′ ==ₑ ′OS_PRIO_SELF)
       * {
       *     prio′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
       *     If (prio′ ==ₑ ′OS_IDLE_PRIO)
       *     {
       *       EXIT_CRITICAL;ₛ
       *       RETURN ′OS_TASK_DEL_IDLE
       *     }
       * };ₛ        *)
      ptcb′ =ₑ OSTCBPrioTbl′[prio′];ₛ

     If (ptcb′ ==ₑ NULL){
        EXIT_CRITICAL;ₛ
        RETURN ′OS_TASK_DEL_ERR
      };ₛ
      If (ptcb′ ==ₑ PlaceHolder){
        EXIT_CRITICAL;ₛ
        RETURN ′OS_TASK_DEL_ERR
      };ₛ
      self′ =ᶠ OS_IsSomeMutexOwner(·ptcb′·);ₛ
      If (self′==ₑ ′ 1){
        EXIT_CRITICAL;ₛ
        RETURN ′OS_TASK_DEL_SOME_MUTEX_OWNER
      };ₛ
      If (ptcb′→OSTCBNext ==ₑ NULL){
        EXIT_CRITICAL;ₛ
        RETURN ′OS_TASK_DEL_HAS_NO_NEXT
      };ₛ
 
      (* If (ptcb′ !=ₑ NULL){ *)

      inline_call inline_bittbl_clearbit ((OSRdyGrp ′):: (OSRdyTbl ′)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil);ₛ


      (* OSRdyTbl′[ptcb′→OSTCBY] &= ∼ptcb′→OSTCBBitX;ₛ
       * If(OSRdyTbl′[ptcb′→OSTCBY] ==ₑ ′0){
       *     OSRdyGrp′  &= ∼ptcb′→OSTCBBitY
       * };ₛ *)
      pevent′ =ₑ ptcb′→OSTCBEventPtr;ₛ
      If (pevent′ !=ₑ NULL){

          inline_call inline_bittbl_clearbit ((pevent′→OSEventGrp):: (pevent′→OSEventTbl)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil)
          (* pevent′→OSEventTbl[ptcb′→OSTCBY] =ₑ pevent′→OSEventTbl[ptcb′→OSTCBY] &ₑ (∼ptcb′→OSTCBBitX);ₛ
           * If(pevent′→OSEventTbl[ptcb′→OSTCBY] ==ₑ ′0){
           *     pevent′→OSEventGrp =ₑ pevent′→OSEventGrp &ₑ (∼ptcb′→OSTCBBitY)
           * } *)
      };ₛ
      ptcb′→OSTCBDly =ₑ ′0;ₛ
      ptcb′→OSTCBStat =ₑ ′OS_STAT_RDY;ₛ
      (* −−OSTaskCtr′;ₛ *)
      OSTCBPrioTbl′[prio′] =ₑ NULL;ₛ
      ptcb′→OSTCBEventPtr =ₑ NULL;ₛ
      IF (ptcb′→OSTCBPrev ==ₑ NULL){
          x ′=ₑ ptcb′→OSTCBNext;ₛ
          x′→OSTCBPrev =ₑ NULL;ₛ
          OSTCBList′ =ₑ x′
      }ELSE{
          x′ =ₑ ptcb′→OSTCBPrev;ₛ
          x′→OSTCBNext =ₑ ptcb′→OSTCBNext;ₛ
          x′ =ₑ ptcb′→OSTCBNext;ₛ
          x′→OSTCBPrev =ₑ ptcb′→OSTCBPrev
      };ₛ
      ptcb′→OSTCBNext =ₑ OSTCBFreeList′;ₛ
      OSTCBFreeList′ =ₑ ptcb′;ₛ
      STKFREE (    ptcb′  );ₛ
      ptcb′→OSTCBflag =ₑ ′0;ₛ
      EXIT_CRITICAL;ₛ
      OS_Sched(­);ₛ
      RETURN ′OS_NO_ERR
      (* };ₛ *)
      (* EXIT_CRITICAL;ₛ *)
      (* RETURN ′OS_TASK_DEL_ERR *)
}·. 


(* ** ac: Check (inline_call inline_bittbl_clearbit ((OSRdyGrp ′):: (OSRdyTbl ′)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil)) . *)
(* ** ac: Eval simpl in (inline_call inline_bittbl_clearbit ((OSRdyGrp ′):: (OSRdyTbl ′)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil)). *)

(* Eval simpl in (          inline_call inline_bittbl_clearbit ((pevent′→OSEventGrp):: (pevent′→OSEventTbl)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil) *)
(*               ). *)
