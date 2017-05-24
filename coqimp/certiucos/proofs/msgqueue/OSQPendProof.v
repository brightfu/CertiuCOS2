(**********************************  uc/OS-II  *****************************************)
(************************************ OS_Q.C *******************************************)
(*******Proofs for API Function: INT8U OSQPend (OS_EVENT *pevent, INT16U timeout)*******)
(************************************ Code: ********************************************)
(* 
INT8U OSQPend(INT16U timeout, OS_EVENT *pevent)
{
    void      *msg;
    OS_Q      *pq;
    BOOLEAN    legal;

     
1   if (pevent == NULL) {       
2       return (OS_ERR_PEVENT_NULL);
    }
3   OS_ENTER_CRITICAL();
   
4   legal = OS_QPtrSearch(pevent);
5   if (!legal){
6       OS_EXIT_CRITICAL();
7       return (OS_ERR_PEVENT_NULL);
    }
8   if (pevent->OSEventType != OS_EVENT_TYPE_Q){
9       OS_EXIT_CRITICAL();
10      return (OS_ERR_PEVENT_NULL);
    }
    if (OSTCBCur -> OSTCBPrio == OS_IDLE_PRIO)
    {
       OS_EXIT_CRITICAL();
       RETURN  (OSQPend)′OS_ERR_PEVENT_NULL;
    }
    if (OSTCBCur -> OSTCBStat != OS_STAT_RDY || OSTCBCur -> OSTCBDly != 0)
    {
       OS_EXIT_CRITICAL();
       RETURN  (OSQPend)′OS_ERR_PEVENT_NULL;
    }
11  OSTCBCur->OSTCBMsg = NULL; 
12  pq = ( OS_Q * ) pevent->OSEventPtr;             
13  if (pq->OSQEntries > 0) {                  
14      msg = *pq->OSQOut++;                  
15      pq->OSQEntries--;                      
16      if (pq->OSQOut == pq->OSQEnd) {        
17          pq->OSQOut = pq->OSQStart;
        }
18	OSTCBCur->OSTCBMsg=msg;
19      OS_EXIT_CRITICAL();
20      return (OS_NO_ERR);                         
    }
21  OSTCBCur->OSTCBStat  = OS_STAT_Q;          
22  OSTCBCur->OSTCBDly   = timeout;            
23  OS_EventTaskWait(pevent);                  
24  OS_EXIT_CRITICAL();
25  OS_Sched();                             
26  OS_ENTER_CRITICAL();
27  msg = OSTCBCur->OSTCBMsg;

28  if (msg != NULL) {                    
29      OS_EXIT_CRITICAL();
30      return (OS_NO_ERR);                 
    }
31  OS_EXIT_CRITICAL();
32  return (OS_TIMEOUT);
                 
}
*)

Require Import ucos_include.
Require Import OSQPendPure.
Require Import msgq_absop_rules.
Require Import linv_solver.
(*Require Import lab.*)
(*Require Import gen_lemmas.*)

Open Scope int_scope.
Open Scope Z_scope.
Open Scope code_scope.


Ltac tl_vl_match_solver := simpl; repeat (erewrite if_true_false_eq_true_intro;eauto);
                           try eapply Zle_imp_le_bool; eauto. 



(*******************************************************************)
Lemma isptr_zh :
  forall x, isptr x ->
            match x with
              | Vundef => false
              | Vnull => true
              | Vint32 _ => false
              | Vptr _ => true
            end = true.
Proof.
  intros.
  unfolds in H; destruct H.
  substs; auto.
  destruct H; substs; auto.
Qed.


Definition gen_OSQPendRightPart2 := forall (
  i : int32 )(
  H1 : Int.unsigned i <= 65535 )(
  v' v'0 v'1 : val)(
  v'2 v'3 v'4 : list vallist)(
  v'5 : list EventData)(
  v'6 : list os_inv.EventCtr)(
  v'7 : vallist)(
  v'8 v'9 : val)(
  v'10 : list vallist)(
  v'11 : vallist)(
  v'12 : list vallist)(
  v'13 : vallist)(
  v'14 : val)(
  v'15 : EcbMod.map)(
  v'16 : TcbMod.map)(
  v'17 : int32)(
  v'18 : addrval)(
  v'19 : val)(
  v'20 : list vallist)(
  v'23 v'24 : list os_inv.EventCtr)(
  v'25 v'26 : list EventData)(
  v'28 : vallist)(
  v'29 : val)(
  v'31 v'33 : list vallist)(
  v'34 : vallist)(
  v'35 : val)(
  v'36 : EcbMod.map)(
  v'37 : TcbMod.map)(
  v'39 : val)(
  v'41 v2 : vallist)(
  v'43 : val)(
  v'44 v'45 v'46 : EcbMod.map)(
  v'47 : absecb.B)(
  v'48 : addrval)(
  H2 : ECBList_P v'43 Vnull v'24 v'26 v'45 v'37)(
  H22 : EcbMod.join v'44 v'46 v'36)(
  H11 : length v'23 = length v'25)(
  v'49 : addrval)(
  v'51 : block)(
  H15 : array_type_vallist_match Int8u v'41)(
  H19 : length v'41 = ∘ OS_EVENT_TBL_SIZE)(
  H20 : isptr v'43)(
  x3 : val)(
  i0 : int32)(
  H10 : Int.unsigned i0 <= 255)(
  i2 : int32)(
  H21 : Int.unsigned i2 <= 65535)(
  H18 : RL_Tbl_Grp_P v'41 (Vint32 i0))(
  H24 : isptr v'43)(
  H14 : val_inj (val_eq (V$ 1) (V$ 0)) = Vint32 Int.zero \/
        val_inj (val_eq (V$ 1) (V$ 0)) = Vnull )(
  H0 : ECBList_P v'39 (Vptr (v'51, Int.zero)) v'23 v'25 v'44 v'37 )(
  H5 : EcbMod.joinsig (v'51, Int.zero) v'47 v'45 v'46)(
  H16 : id_addrval' (Vptr (v'51, Int.zero)) OSEventTbl os_ucos_h.OS_EVENT = Some v'49)(
  v'21 v'22 : val)(
  v'27 v'38 : TcbMod.map)(
  v'40 : val)(
  v'50 : block)(
  H26 : v'29 <> Vnull)(
  H27 : join v'27 v'38 v'37)(
  H28 : TCBList_P v'29 v'31 v'34 v'27)(
  H25 : Vptr (v'50, Int.zero) <> Vnull)(
  x8 x9 : val )(
  H32 : isptr x9 )(
  H33 : isptr x8)(
  i9 : int32) (
  H34 : Int.unsigned i9 <= 65535)(
  i8 : int32)(
  H35 : Int.unsigned i8 <= 255)(
  i7 : int32)(
  H36 : Int.unsigned i7 <= 255)(
  i6 : int32)(
  H37 : Int.unsigned i6 <= 255)(
  i5 : int32)(
  H38 : Int.unsigned i5 <= 255)(
  i4 : int32)(
  H39 : Int.unsigned i4 <= 255)(
  i3 : int32)(
  H40 : Int.unsigned i3 <= 255)(
  H31 : isptr v'21)(
  H12 : isptr v'40)(
  H29 : TCBList_P (Vptr (v'50, Int.zero))
          ((v'40
            :: v'21
               :: x9
                  :: x8
                     :: Vint32 i9
                        :: Vint32 i8
                           :: Vint32 i7
                              :: Vint32 i6
                                 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: nil)
           :: v'33) v'34 v'38 )(
  H6 : RH_TCBList_ECBList_P v'36 v'37 (v'50, Int.zero))(
  H7 : RH_CurTCB (v'50, Int.zero) v'37)(
  Hnidle : Int.eq i7 ($ OS_IDLE_PRIO) = false)(
  Hstrdy : Int.eq i8 ($ OS_STAT_RDY) = true)(
  Hdly0 : Int.eq i9 ($ 0) = true)(
  v'32 : block)(
  v'42 : block * int32)(
  v'52 : block)(
  H45 : length v2 = ∘ OS_MAX_Q_SIZE)(
  H41 : id_addrval' (Vptr (v'52, Int.zero)) msgqueuetbl os_ucos_h.OS_Q_FREEBLK =
        Some v'42 )(
  x x0 x1 x7 x10 : val)(
  H30 : isptr x10)(
  H42 : isptr x7)(
  H46 : isptr x)(
  H48 : isptr x0)(
  H49 : isptr x1)(
  i11 : int32)(
  H50 : Int.unsigned i11 <= 65535)(
  i10 : int32)(
  H51 : Int.unsigned i10 <= 65535)(
  x11 x12 : val)(
  H47 : isptr x11)(
  H52 : isptr (Vptr (v'52, Int.zero))) (
  H43 : WellformedOSQ
          (x10
           :: x7
              :: x
                 :: x0
                    :: x1 :: Vint32 i11 :: Vint32 i10 :: Vptr (v'52, Int.zero) :: nil) )(
  H3 : RLH_ECBData_P
         (DMsgQ (Vptr (v'32, Int.zero))
            (x10
             :: x7
                :: x
                   :: x0
                      :: x1
                         :: Vint32 i11 :: Vint32 i10 :: Vptr (v'52, Int.zero) :: nil)
            (x11 :: x12 :: nil) v2) v'47 )(
  H23 : isptr (Vptr (v'32, Int.zero)))(
  H9 : Int.unsigned ($ OS_EVENT_TYPE_Q) <= 255)(
  H8 : val_inj
         (notint
            (val_inj
               (if Int.eq ($ OS_EVENT_TYPE_Q) ($ OS_EVENT_TYPE_Q)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
       val_inj
         (notint
            (val_inj
               (if Int.eq ($ OS_EVENT_TYPE_Q) ($ OS_EVENT_TYPE_Q)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) = Vnull )(
  H4 : R_ECB_ETbl_P (v'51, Int.zero)
         (V$ OS_EVENT_TYPE_Q
          :: Vint32 i0 :: Vint32 i2 :: Vptr (v'32, Int.zero) :: x3 :: v'43 :: nil,
         v'41) v'37 )(
  H : ECBList_P v'39 Vnull
        (v'23 ++
         ((V$ OS_EVENT_TYPE_Q
           :: Vint32 i0 :: Vint32 i2 :: Vptr (v'32, Int.zero) :: x3 :: v'43 :: nil,
          v'41) :: nil) ++ v'24)
        (v'25 ++
         (DMsgQ (Vptr (v'32, Int.zero))
            (x10
             :: x7
                :: x
                   :: x0
                      :: x1
                         :: Vint32 i11 :: Vint32 i10 :: Vptr (v'52, Int.zero) :: nil)
            (x11 :: x12 :: nil) v2 :: nil) ++ v'26) v'36 v'37
),
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (v'50, Int.zero) init_lg **
    ((EX v0 : val, LV timeout @ Int16u |-> v0) **
     (EX v0 : val, LV pevent @ os_ucos_h.OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV message @ (Void) ∗ |-> v0) **
     (EX v0 : val, LV pq @ os_ucos_h.OS_Q ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, os_ucos_h.OS_EVENT ∗)
         :: (message, (Void) ∗) :: (pq, os_ucos_h.OS_Q ∗) :: (legal, Int8u) :: nil),
   Afalse|}|- (v'50, Int.zero)
   {{( <|| qpend (Vptr (v'51, Int.zero) :: Vint32 i :: nil) ||>  **
      LV pq @ os_ucos_h.OS_Q ∗ |-> Vptr (v'32, Int.zero) **
      A_dom_lenv
        ((timeout, Int16u)
         :: (pevent, os_ucos_h.OS_EVENT ∗)
            :: (message, (Void) ∗) :: (pq, os_ucos_h.OS_Q ∗) :: (legal, Int8u) :: nil) **
      GV OSTCBCur @ os_ucos_h.OS_TCB ∗ |-r-> Vptr (v'50, Int.zero) **
      Astruct (v'50, Int.zero) OS_TCB_flag
        (v'40
         :: v'21
            :: x9
               :: Vnull
                  :: Vint32 i9
                     :: Vint32 i8
                        :: Vint32 i7
                           :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: nil) **
      Astruct (v'52, Int.zero) os_ucos_h.OS_Q_FREEBLK (x11 :: x12 :: nil) **
      Aarray v'42 (Tarray (Void) ∗ ∘ OS_MAX_Q_SIZE) v2 **
      Astruct (v'32, Int.zero) os_ucos_h.OS_Q
        (x10
         :: x7
            :: x
               :: x0
                  :: x1 :: Vint32 i11 :: Vint32 i10 :: Vptr (v'52, Int.zero) :: nil) **
      dllseg v'40 (Vptr (v'50, Int.zero)) v'22 Vnull v'33 OS_TCB_flag
        (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
      GV OSTCBList @ os_ucos_h.OS_TCB ∗ |-> v'29 **
      dllseg v'29 Vnull v'21 (Vptr (v'50, Int.zero)) v'31 OS_TCB_flag
        (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
      Astruct (v'51, Int.zero) os_ucos_h.OS_EVENT
        (V$ OS_EVENT_TYPE_Q
         :: Vint32 i0 :: Vint32 i2 :: Vptr (v'32, Int.zero) :: x3 :: v'43 :: nil) **
      Aarray v'49 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'41 **
      Aie false **
      Ais nil **
      Acs (true :: nil) **
      Aisr empisr **
      GV OSEventList @ os_ucos_h.OS_EVENT ∗ |-> v'39 **
      evsllseg v'39 (Vptr (v'51, Int.zero)) v'23 v'25 **
      evsllseg v'43 Vnull v'24 v'26 **
      A_isr_is_prop **
      tcbdllflag v'29
        (v'31 ++
         (v'40
          :: v'21
             :: x9
                :: x8
                   :: Vint32 i9
                      :: Vint32 i8
                         :: Vint32 i7
                            :: Vint32 i6
                               :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: nil) :: v'33) **
      AOSRdyTblGrp v'34 v'35 **
      AOSTCBPrioTbl v'28 v'34 v'37 v'48 **
      HECBList v'36 **
      HTCBList v'37 **
      HCurTCB (v'50, Int.zero) **
      p_local OSLInv (v'50, Int.zero) init_lg **
      LV legal @ Int8u |-> (V$ 1) **
      AOSEventFreeList v'2 **
      AOSQFreeList v'3 **
      AOSQFreeBlk v'4 **
      AOSMapTbl **
      AOSUnMapTbl **
      AOSIntNesting **
      AOSTCBFreeList v'19 v'20 **
      AOSTime (Vint32 v'17) **
      HTime v'17 **
      AGVars **
      atoy_inv' **
      LV message @ (Void) ∗ |-> v' **
      LV timeout @ Int16u |-> Vint32 i **
      LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr (v'51, Int.zero)) **
     [|val_inj
         (if Int.ltu ($ 0) i10 then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) =
       Vint32 Int.zero \/
       val_inj
         (if Int.ltu ($ 0) i10 then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) =
       Vnull|]}} OSTCBCur ′ → OSTCBStat =ₑ ′ OS_STAT_Q;ₛ
   OSTCBCur ′ → OSTCBDly =ₑ timeout ′;ₛ
   OS_EventTaskWait (­ pevent ′­);ₛ
   EXIT_CRITICAL;ₛ
   OS_Sched (­);ₛ
   ENTER_CRITICAL;ₛ
   message ′ =ₑ OSTCBCur ′ → OSTCBMsg;ₛ
   If(message ′ !=ₑ NULL)
        {EXIT_CRITICAL;ₛ
        RETURN ′ OS_NO_ERR}  ;ₛ
   EXIT_CRITICAL;ₛ
   RETURN ′ OS_TIMEOUT {{Afalse}}.
        

Lemma OSQPendRightPart2 : gen_OSQPendRightPart2.
Proof.
  unfolds.
  intros.
  hoare_split_pure_all.
  lets Hentries: qentries_eq_zero H13.
  hoare forward.
 
  hoare forward.
  go.
  clear - H1; pauto.
  
  hoare lifts (17::15::21::nil)%nat pre.
  eapply backward_rule1.
  intros.
  apply a_isr_is_prop_split in H17.
  exact H17.
  unfold  AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  hoare_split_pure_all.
  destruct H17 as (Hrtblmatch&Hrtbllen).
  rename H44 into Hrgrpmatch.
  destruct H53 as (Hrtblgrp&Hidleintbl).
  
  hoare forward.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  instantiate (2:=DMsgQ (Vptr (v'32, Int.zero))
                 (x10
        :: x7
           :: x
              :: x0
                 :: x1
                    :: Vint32 i11
                       :: Vint32 i10 :: Vptr (v'52, Int.zero) :: nil)
                  (x11 :: x12 :: nil) v2).
  unfold AEventNode.
  unfold AEventData.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold AMsgData.
  unfold AOSQCtr, AOSQBlk.
  unfold node.
  unfold  AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Astruct.  
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aop.
  sep cancel Aie.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Ais.
  eauto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  eauto.
  unfolds;simpl;auto.
  eauto.
  auto.

  simpl;splits;auto.
  clear -H10; pauto.
  clear -H21; pauto.
  apply isptr_zh; auto.

  
  unfolds;simpl;auto.

  simpl;splits;auto; try (apply isptr_zh; auto).
  clear -H50; pauto.
  auto.
  
  simpl;splits;auto.
  apply isptr_zh; auto.
   
  simpl;splits; auto; try (apply isptr_zh; auto).
  clear -H1; pauto.
  splits.
  clear -H36; pauto.
  clear -H37; pauto.
  clear -H38; pauto.
  clear -H39; pauto.
  clear -H40; pauto.
  auto.
   
  
  splits; simpl; eauto.
  eexists; splits; unfolds; simpl;eauto.
  eapply tcblist_p_node_rl;eauto.
 
  go.
  linv_solver.
  linv_solver.
  
  (* OS_EventTaskWait post *)
  hoare_ex_intro.
  unfold OS_EventTaskWaitPost.

  unfold OS_EventTaskWaitPost'.
  unfold getasrt.

  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  inverts H17.
  unfold V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSEventGrp in H53.
  simpl in H53.
  simpljoin1.
  inverts H53.
  inverts H55.
  inverts H56.
  inverts H61.
  simpl in H44;inverts H44.

  (* high level step *)
  lets Hmsgnil: RLH_ECBData_P_impl_high_ecb_msg_nil H3.
  destruct Hmsgnil as [maxlen [wl Hmsgnil]].
  subst v'47.
  assert (EcbMod.get v'36 (v'51, Int.zero) = Some (absmsgq nil maxlen, wl)).
  eapply EcbMod.join_joinsig_get;eauto.
  simpljoin1.
  assert (exists m,
            TcbMod.get v'38 (v'50, Int.zero) = Some (i7, rdy, m)) as Hget.
  eapply TCBList_P_impl_high_tcbcur_rdy' with (i9:=i8) (rtbl:=v'54) (tcbls:=v'38); eauto.

  unfold V_OSTCBPrio; simpl.
  auto.
  destruct Hget as  [m Hget].
  assert (TcbMod.get v'37 (v'50, Int.zero) = Some (i7, rdy, m)).
  eapply TcbMod.join_get_get_r; eauto.
  
  hoare abscsq.
  apply noabs_oslinv.
  eapply OSQPend_high_step_block; eauto.
  go.
  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  assert (prio_neq_cur v'37 (v'50, Int.zero) (i7)).
  eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.  
  simpl  TCBList_P in H29.
  destruct H29 as (td & vv & tcblss & asbs & Hveq & Hnes & Htcj & Htp & Htlis).
  unfolds in Htp.
  destruct asbs.
  destruct p.
  destruct Htp as (_ & _ & Hrsl & _).
  funfold Hrsl; eauto.

  
  (* L24 : excrit *)
(*  eapply seq_rule.
  hoare lift 2%nat pre.
  eapply excrit1_rule'_ISnil_ISRemp'.
  intros;unfold OSInv; unfold A_isr_is_prop; sep pauto. *)
  
  eapply backward_rule1 with (p:=  A_isr_is_prop **
                                   PV v'48 @ Int8u |-> v'34 **
    <||
   isched;;
   (qpend_to (|Vptr (v'51, Int.zero) :: Vint32 i :: nil|)
    ?? qpend_block_get (|Vptr (v'51, Int.zero) :: Vint32 i :: nil|)) ||>  **
   HECBList
     (EcbMod.set v'36 (v'51, Int.zero) (absmsgq nil maxlen, (v'50, Int.zero) :: wl)) **
   HTCBList
     (TcbMod.set v'37 (v'50, Int.zero)
        (i7, wait (os_stat_q (v'51, Int.zero)) i, Vnull)) **
   HTime v'17 **
   HCurTCB (v'50, Int.zero) **
   Aie false **
   Ais nil **
   Acs (true :: nil) **
   Aisr empisr **
   GV OSTCBCur @ os_ucos_h.OS_TCB ∗ |-r-> Vptr (v'50, Int.zero) **
   node (Vptr (v'50, Int.zero))
     (v'40
      :: v'21
         :: Vptr (v'51, Int.zero)
            :: Vnull
               :: Vint32 i
                  :: V$ OS_STAT_Q
                     :: Vint32 i7
                        :: Vint32 i6
                           :: Vint32 v'65 :: Vint32 v'66 :: Vint32 v'67 :: nil)
     OS_TCB_flag **
   AOSRdyTblGrp
     (update_nth_val ∘ (Int.unsigned v'65) v'54 (Vint32 (v'68&ᵢInt.not v'66)))
     (Vint32 v'62) **
   AEventNode (Vptr (v'51, Int.zero))
     (V$ OS_EVENT_TYPE_Q
      :: Vint32 (Int.or v'70 v'67)
         :: Vint32 i2 :: Vptr (v'32, Int.zero) :: x3 :: v'43 :: nil)
     (update_nth_val ∘ (Int.unsigned v'65) v'58 (Vint32 (Int.or v'69 v'66)))
     (DMsgQ (Vptr (v'32, Int.zero))
        (x10
         :: x7
            :: x
               :: x0
                  :: x1
                     :: Vint32 i11 :: Vint32 Int.zero :: Vptr (v'52, Int.zero) :: nil)
        (x11 :: x12 :: nil) v2) **
   p_local OSLInv (v'50, Int.zero) init_lg **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, os_ucos_h.OS_EVENT ∗)
         :: (message, (Void) ∗) :: (pq, os_ucos_h.OS_Q ∗) :: (legal, Int8u) :: nil) **
   LV pq @ os_ucos_h.OS_Q ∗ |-> Vptr (v'32, Int.zero) **
   dllseg v'40 (Vptr (v'50, Int.zero)) v'22 Vnull v'33 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GV OSTCBList @ os_ucos_h.OS_TCB ∗ |-> v'29 **
   dllseg v'29 Vnull v'21 (Vptr (v'50, Int.zero)) v'31 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GV OSEventList @ os_ucos_h.OS_EVENT ∗ |-> v'39 **
   evsllseg v'39 (Vptr (v'51, Int.zero)) v'23 v'25 **
   evsllseg v'43 Vnull v'24 v'26 **
   tcbdllflag v'29
     (v'31 ++
      (v'40
       :: v'21
          :: x9
             :: x8
                :: Vint32 i9
                   :: Vint32 i8
                      :: Vint32 i7
                         :: Vint32 i6
                            :: Vint32 v'65 :: Vint32 v'66 :: Vint32 v'67 :: nil)
      :: v'33) **
   GAarray OSTCBPrioTbl (Tarray os_ucos_h.OS_TCB ∗ 64) v'28 **
   G& OSPlaceHolder @ Int8u == v'48 **
   LV legal @ Int8u |-> (V$ 1) **
   AOSEventFreeList v'2 **
   AOSQFreeList v'3 **
   AOSQFreeBlk v'4 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSIntNesting **
   AOSTCBFreeList v'19 v'20 **
   AOSTime (Vint32 v'17) **
   AGVars **
   atoy_inv' **
   LV message @ (Void) ∗ |-> v' **
   LV timeout @ Int16u |-> Vint32 i **
   LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr (v'51, Int.zero)
                             ).

  
  intros.
  sep lifts (10::8::nil)%nat in H60.
  sep lifts (11::9::1::nil)%nat.
  eapply add_a_isr_is_prop; eauto.
  hoare forward prim.

  (* AOSTCBList *)
  unfold AOSTCBList.
  
  sep pauto.
  unfold tcbdllseg.
  unfold dllseg at 2.
  fold dllseg.
  sep pauto.
  repeat (sep cancel dllseg).
  sep cancel node.
  (* AOSPrioTbl *)
  unfold AOSTCBPrioTbl.
  sep pauto.
  (* AECBList *)
  unfold AECBList.

  
(*  instantiate (1:= A_dom_lenv
                       ((timeout, Int16u)
                          :: (pevent, OS_EVENT ∗)
                          :: (message, (Void) ∗)
                          :: (pq, OS_Q ∗) :: (legal, Int8u) :: nil) **
                       LV pq @ OS_Q ∗ |-> Vptr (v'32, Int.zero) **
                       LV message @ (Void) ∗ |-> v' **
                       LV legal @ Int8u |-> (V$1) **  LV timeout @ Int16u |-> Vint32 i **
                       LV pevent @ OS_EVENT ∗ |-> Vptr (v'51, Int.zero)). *)
(*  assert (EcbMod.joinsig (v'51, Int.zero) (absmsgq nil maxlen, wl) v'45
                         (EcbMod.set v'46 (v'51, Int.zero) (absmsgq nil maxlen, (v'50, Int.zero) :: wl))).
  (* admit. *)
  assert (EcbMod.join v'44
   (EcbMod.set v'46 (v'51, Int.zero) (absmsgq nil maxlen, (v'50, Int.zero) :: wl))
   (EcbMod.set v'36 (v'51, Int.zero) (absmsgq nil maxlen, (v'50, Int.zero) :: wl))).
  (* admit. *)
*)  
  sep pauto.
  eapply evsllseg_compose.
  instantiate (2:=V$OS_EVENT_TYPE_Q
      :: Vint32 (Int.or v'70 v'67)
         :: Vint32 i2 :: Vptr (v'32, Int.zero) :: x3 :: v'43 :: nil).
  unfold V_OSEventListPtr; simpl;  auto. 
  auto.  
  auto.
  repeat (sep cancel evsllseg).

(*  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AOSRdyTblGrp. *)
  instantiate (5:= DMsgQ (Vptr (v'32, Int.zero))
                         (x10
                            :: x7
                            :: x
                            :: x0
                            :: x1
                            :: Vint32 i11
                            :: Vint32 Int.zero :: Vptr (v'52, Int.zero) :: nil)
             (x11 :: x12 :: nil) v2).
(*  sep semiauto;eauto. *)
  sep cancel 1%nat 2%nat.
  sep cancel 1%nat 1%nat.
  sep cancel OSPlaceHolder.
  eapply tcbdllflag_hold.
  eapply tcbdllflag_hold_middle.
  instantiate (1 := (v'40
               :: v'21
                  :: x9
                     :: x8
                        :: Vint32 i9
                           :: Vint32 i8
                              :: Vint32 i7
                                 :: Vint32 i6
                                    :: Vint32 v'65
                                       :: Vint32 v'66 :: Vint32 v'67 :: nil) ).
  unfolds; simpl.
  splits; eauto.
  sep cancel tcbdllflag.
  eauto.

  lets Hnewjoin: ecb_get_set_join_join H17 H5 H22.
  simpljoin1.
  eapply msgqlist_p_compose.
  5:apply H61.
  5:apply H62.
  simpl TCBList_P in H29.
  destruct H29 as (td & vv & tcblss & asbs & Hveq & Hnes & Htcj & Htp & Htlis).
  unfolds in Htp.
  destruct asbs.
  destruct p.
  destruct Htp as (_ & _ & Hrsl & _).
  funfold Hrsl.
  eapply R_ECB_ETbl_P_high_tcb_block_hold; eauto.
  eapply ECBList_P_high_tcb_block_hold; eauto.
  clear - H22 H17 H5.
  pose proof H22 (v'51, Int.zero).
  pose proof H5 (v'51, Int.zero).
  rewrite H17 in H.
  rewrite EcbMod.get_sig_some in H0.
  destruct (EcbMod.get v'44 (v'51, Int.zero));
    destruct (EcbMod.get v'45 (v'51, Int.zero));
    destruct (EcbMod.get v'46 (v'51, Int.zero));
    tryfalse; auto.
  eapply ECBList_P_high_tcb_block_hold; eauto.
  clear - H5.
  pose proof H5 (v'51, Int.zero).
  rewrite EcbMod.get_sig_some in H.
  destruct (EcbMod.get v'45 (v'51, Int.zero)); tryfalse.
  auto.

  clear -H3.
  unfolds in H3.
  unfolds.
  simpljoin1; splits; eauto.
  unfolds.
  split;intros;tryfalse;auto.
  
  eapply TcbMod_set_R_PrioTbl_P_hold; eauto.
  eapply rtbl_remove_RL_RTbl_PrioTbl_P_hold with (prio:=Int.unsigned i7); eauto.
  clear - H29.
  unfold TCBList_P in H29; fold TCBList_P in H29; simpljoin1.
(*  int auto.*)
  unfold TCBNode_P in H2; destruct x2; destruct p; simpljoin1.
  unfolds in H5; simpljoin1.
  unfolds in H5; inverts H5; auto.
  
  clear - H29.
  unfold TCBList_P in H29; fold TCBList_P in H29; simpljoin1.
  unfold TCBNode_P in H2; destruct x2; destruct p; simpljoin1.
  unfolds in H5; simpljoin1.
  unfolds in H8; inverts H8; auto.
  unfolds in H5.
  simpl in H5; inverts H5.
  rewrite Int.repr_unsigned; auto.
    
  clear - H29.
  unfold TCBList_P in H29; fold TCBList_P in H29; simpljoin1. 
  unfold TCBNode_P in H2; destruct x2; destruct p; simpljoin1.
  unfolds in H5; simpljoin1. 
  unfolds in H5; inverts H5.
  unfolds in H9; inverts H9.
  rewrite Int.repr_unsigned; auto.

  unfold V_OSTCBPrev; simpl nth_val; auto.
  unfold V_OSTCBNext; simpl nth_val; auto.
 
  eapply TCBList_P_tcb_block_hold; eauto.
  eapply TcbMod_join_impl_prio_neq_cur_r; eauto.


  eapply TCBList_P_tcb_block_hold' with (prio:= i7) (tcs:=v'38); eauto.
 
  clear - H29.
  unfold TCBList_P in H29; fold TCBList_P in H29; simpljoin1.
  (*int auto.*)
  unfold TCBNode_P in H2; destruct x2; destruct p; simpljoin1.
  unfolds in H5; simpljoin1.
  unfolds in H5; inverts H5; auto.

  clear - H29.
  unfold TCBList_P in H29; fold TCBList_P in H29; simpljoin1.
  unfold TCBNode_P in H2; destruct x2; destruct p; simpljoin1.
  unfolds in H5; simpljoin1.
  unfolds in H8; inverts H8; auto.
  unfolds in H5. 
  simpl in H5; inverts H5.
  auto.

  clear - H29.
  unfold TCBList_P in H29; fold TCBList_P in H29; simpljoin1. 
  unfold TCBNode_P in H2; destruct x2; destruct p; simpljoin1.
  unfolds in H5; simpljoin1. 
  unfolds in H5; inverts H5.
  unfolds in H9; inverts H9.
  auto.
  
  eapply TcbMod_join_impl_prio_neq_cur_l; eauto.
  eapply TcbMod.join_set_r; eauto.
  eapply TcbMod.get_indom. eexists; eauto.
  eapply RH_CurTCB_high_block_hold; eauto.
  eapply RH_TCBList_ECBList_P_high_block_hold; eauto.
  unfold isr_is_prop.
  intros;unfold empisr;auto. 
  go.
  (*apply GoodaOSQPend.*)
  
  (* L25 : OS_Sched() *)
  hoare forward.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aop.
  sep cancel p_local.
  eauto.
  (*  apply H60. *)
  unfolds; auto.
  go.
  linv_solver.
  linv_solver.
  unfold OS_SchedPost.  
  unfold OS_SchedPost'.
  unfold getasrt.
  hoare_ex_intro. 
  hoare_split_pure_all.
  inverts H60.
  
  (* L26-28 *)
  hoare forward prim.
  hoare unfold.
  hoare forward.
  go.
  hoare forward.
  apply isptr_zh; auto.
  pauto. pauto.
  hoare_split_pure_all.
 
  assert (x16 <> Vnull).
  red. intro. subst x16.
  simpl in H63.
  destruct H63.
  unfold Int.notbool in H63.  
  rewrite Int.eq_false in H63.
  apply H63; auto. 
  discriminate.
 
  (* high level step *)

  assert (exists prio st,
         TcbMod.get  v'83 (v'50, Int.zero) = Some (prio, st, x16)).
  eapply low_stat_q_impl_high_stat_q; eauto.
  simpljoin1.
  (*
  unfold V_OSTCBMsg; simpl; eauto. 
  subst i11; unfold V_OSTCBStat; simpl; eauto.
  mytac.
   *)
  assert (TcbMod.get v'75 (v'50, Int.zero) = Some (x2, x4, x16) ).

  eapply TcbMod.join_get_get_r; eauto.

  hoare abscsq.
  apply noabs_oslinv.
  eapply OSQPend_high_step_block_get; eauto.
  go.

  
  (* L29 : excrit *)
  hoare forward prim.
  (* AOSTCBList *)
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  unfold dllseg at 2.
  fold dllseg.
  unfold node.
  sep pauto.
  repeat (sep cancel dllseg).
  sep cancel Astruct.
  sep pauto.
  (*  exact H86. *)
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  go.
  eauto.
  eauto.
  eauto.
  go.
  
  (* L29 : return *)
  hoare forward.
  (*L30 : excrit*)
  hoare forward.

  pure intro.
  destruct H63.
  simpl in H63.

  assert (x16=Vnull) by (eapply xx;eauto).
  subst x16.
 
  Focus 2.
  false;eapply xx' with x16;eauto.
  assert (exists prio st,
            TcbMod.get  v'83 (v'50, Int.zero) = Some (prio, st, Vnull)).
  eapply low_stat_q_impl_high_stat_q; eauto.
  
  simpljoin1.

  assert (TcbMod.get v'75 (v'50, Int.zero) = Some (x2, x4, Vnull) ).

  eapply TcbMod.join_get_get_r; eauto.

  hoare abscsq.
  apply noabs_oslinv.
  eapply qpend_absinfer_to;eauto.
  
  unfold A_isr_is_prop. go.
  hoare forward prim.
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  unfold dllseg at 2.
  fold dllseg.
  unfold node.
  sep pauto.
  repeat (sep cancel dllseg).
  sep cancel Astruct.
  eapply tcbdllflag_hold.
  eapply tcbdllflag_hold_middle.
  instantiate (1 := (v'84
               :: v'80
                  :: x17
                     :: Vnull
                        :: Vint32 i12
                           :: Vint32 i10
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3 :: Vint32 i1 :: Vint32 i0 :: nil)).
  unfolds; eauto.
  sep cancel tcbdllflag.
  exact H83.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  simpl;splits;auto.
  eauto.
  eauto.
  eauto.
  (*go.*)
  apply isptr_zh; auto.
  apply isptr_zh; auto.
  apply isptr_zh; auto.
  clear -H76; pauto.
  clear -H77; pauto. 
  splits.
  clear -H78; pauto.
  clear -H79; pauto.
  clear -H80; pauto.
  clear -H81; pauto.
  clear -H82; pauto.
  auto.
  eauto.
  eauto.
  eauto.
  go.
  
  hoare forward.
Qed.



(*******************************************************************)
Theorem OSQPendRight: 
  forall tid vl p r,
    Some p = BuildPreA' os_api OSQPend qpendapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api OSQPend qpendapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSQPend = Some (t, d1, d2, s) /\ {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{ p }} s {{ Afalse }}.
Proof.
  init_spec.

  (* L1-L2 *)
  hoare forward; pauto.
  hoare_split_pure_all.
  hoare abscsq.
  apply noabs_oslinv.
  eapply OSQPend_high_step_null; pauto.
  hoare forward; pauto.

  (* L3 *)
  hoare forward.
  hoare_split_pure_all.
  apply val_inj_impl_Vptr in H.
  destruct H. subst x0. clear H2.
  hoare forward prim.
(*  apply GoodaOSQPend.*)

  (* L4 *)
  unfold OSInv.
  hoare normal pre.
  hoare_ex_intro.
  hoare forward.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aop.
  sep cancel AECBList.
  sep cancel tcbdllflag.
  sep cancel AOSTCBList.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBPrioTbl.
  eauto.
  pauto.
  pauto.
  apply retpost_osev.
  linv_solver.
  linv_solver.
  
  hoare_ex_intro.
  unfold OS_EventSearchPost.  
  unfold OS_EventSearchPost'.
  unfold getasrt.

  eapply backward_rule1.
  intros.
  
(*  sep lift 2%nat in H.*)
  eapply disj_star_elim; eauto.
  hoare forward.
  
(* branch 1: legal = true *)
  (* L5-L7 *)
  hoare forward.
  inverts H15.
  inverts H14.
  go.
  inverts H14.
  go.
  hoare_split_pure_all.
  inverts H14; rename H15 into H14.
  apply val_inj_impl_eq in H14.
  instantiate (1:=Afalse).
  rewrite H14 in H13; tryfalse.

  (* L8-L10 *)
  hoare forward.
  hoare_split_pure_all.
  inverts H14; rename H15 into H14.
  simpl in H8.
  inverts H8.
  hoare unfold.
  hoare forward.
  go.
  pauto.
  pauto.
  instantiate (1:=Afalse).

  hoare_split_pure_all.
  destruct H8.
  remember (Int.eq i1 ($ OS_EVENT_TYPE_Q)) as X.
  destruct X.
  unfold val_inj in H8.
  simpl in H8.
  unfold Int.notbool in H8.
  rewrite Int.eq_false in H8.
  tryfalse.
  clear.
  go.

  eapply backward_rule1.
  intros.
  sep lift 8%nat in H13.
  eapply eventtype_neq_q in H13;eauto.
  hoare_split_pure_all.
  hoare abscsq.
  apply noabs_oslinv.
  eapply qpend_absinfer_no_q;auto.
  go.
  hoare forward prim.
  
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose.
  instantiate (2:=Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'43 :: nil).
  unfold V_OSEventListPtr; simpl;  auto. 
  auto.
  auto.
  repeat (sep cancel evsllseg).
  (* AEventNode *)

  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold node.
  sep pauto.
  sep cancel 1%nat 3%nat.
  sep cancel 1%nat 1%nat.
  eauto.
  eauto.
  unfolds;simpl;auto.
  auto.
  auto.
  pauto.
  auto.
  pauto.
  hoare forward.
  
  (*if idle ------------*)
  hoare forward.
  hoare unfold.
  hoare forward.
  go.
  pauto.
  instantiate (1:=Afalse).

  

  pure intro.
  assert (Int.eq i7 ($ OS_IDLE_PRIO) =true).
  destruct (Int.eq i7 ($ OS_IDLE_PRIO));unfolds in H13;simpl in H13;tryfalse;auto.
  clear H13 H17 H30.
  unfold1 TCBList_P in H29; simpljoin1.
  unfold TCBNode_P in *.
  destruct x4.
  destruct p.
  simpljoin1.
  unfold V_OSTCBNext, V_OSTCBMsg, V_OSTCBPrio in *.
  unfold TcbJoin in *.
  assert (TcbMod.get v'38 x = Some (p, t, m)).
  lets H100 : TcbMod.get_sig_some x (p, t, m).
  eapply TcbMod.join_get_get_l; eauto.
  assert (TcbMod.get v'37 x = Some (p, t, m)).
  eapply TcbMod.join_get_get_r; eauto.
  unfolds in H43.
  inverts H43.
  lets Hx: Int.eq_spec p ($ OS_IDLE_PRIO).
  rewrite H41 in Hx.
  subst p.
  inverts H13.
  
  
  hoare abscsq.
  apply noabs_oslinv.
  eapply qpend_absinfer_idle;eauto.
  
  can_change_aop_solver.
  hoare forward prim.
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  unfold dllseg at 2.
  fold dllseg.
  unfold node.
  sep pauto.
  repeat (sep cancel dllseg).
  sep cancel Astruct.
  (* AECBList *)
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose.
  instantiate (2:=Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'43 :: nil).
  unfold V_OSEventListPtr; simpl;  auto. 
  auto.
  auto.
  repeat (sep cancel evsllseg).
  (* AEventNode *)  
  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold node.
  sep pauto.
  eauto.
  go. 
  go.
  auto.
  go.
  go.

  go.
  2:eauto.
  2:eauto.
 
  unfold1 TCBList_P.
  do 4 eexists;splits;eauto.
  unfolds.
  go.
  go.
  hoare forward.
 
  hoare forward.
  pure intro.
  assert (Int.eq i7 ($ OS_IDLE_PRIO)=false) as Hnidle.
  clear -H13.
  destruct (Int.eq i7 ($ OS_IDLE_PRIO));auto;destruct H13;simpl in H;tryfalse.
  clear H13.
  (* if no rdy-------------- *)
  hoare forward.
  go.
  destruct (Int.eq i8 ($ OS_STAT_RDY));auto.
  destruct (Int.eq i8 ($ OS_STAT_RDY));simpl;auto.
  go.
  destruct (Int.eq i9 ($ 0));auto.
  destruct (Int.eq i9 ($ 0));simpl;auto.
  destruct (Int.eq i8 ($ OS_STAT_RDY));destruct (Int.eq i9 ($ 0));simpl;auto.
  pure intro.
  instantiate (1:=Afalse).
  assert (Int.eq i8 ($ OS_STAT_RDY) = false \/ Int.eq i9 ($ 0) =false).
  clear -H13.
  destruct (Int.eq i8 ($ OS_STAT_RDY));destruct (Int.eq i9 ($ 0));simpl in H13;auto;tryfalse.
  assert (Int.ltu Int.zero (Int.notbool Int.one)
                  || Int.ltu Int.zero (Int.notbool Int.one) = false).
  unfold Int.notbool.
  clear;int auto.
  rewrite H in H13.
  unfold val_inj in H13;simpl in H13.
  tryfalse.
  clear H13 H17 H30.
  unfold1 TCBList_P in H29; simpljoin1.
  unfold TCBNode_P in *.
  destruct x4.
  destruct p.
  simpljoin1.
  unfold V_OSTCBNext, V_OSTCBMsg, V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat in *.
  unfold TcbJoin in *.
  assert (TcbMod.get v'38 x = Some (p, t, m)).
  lets H100 : TcbMod.get_sig_some x (p, t, m).
  eapply TcbMod.join_get_get_l; eauto.
  assert (TcbMod.get v'37 x = Some (p, t, m)).
  eapply TcbMod.join_get_get_r; eauto.

  lets Hnrdy: r_tcb_status_p_nrdy H45 H41.
  inverts H13.
  hoare abscsq.
  apply noabs_oslinv.
  eapply qpend_absimp_stat_err;eauto.
 
  go.
  hoare forward prim.
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  unfold dllseg at 2.
  fold dllseg.
  unfold node.
  sep pauto.
  repeat (sep cancel dllseg).
  sep cancel Astruct.
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose.
  instantiate (2:=Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'43 :: nil).
  unfold V_OSEventListPtr; simpl;  auto. 
  auto.
  auto.
  repeat (sep cancel evsllseg).
  (* AEventNode *)  

  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold node.
  sep pauto.
  eauto.
  unfolds;simpl;auto.
  
  go.
  auto.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  go.
  2:eauto.
  2:eauto.

  unfold1 TCBList_P.
  do 4 eexists;splits;eauto.
  unfolds.
  splits;eauto.
  go.
  hoare forward.
 
  hoare forward.
  pure intro.
  assert (Int.eq i8 ($ OS_STAT_RDY) = true /\ Int.eq i9 ($ 0) = true) as Hstrdy.
  clear -H13.

  
  assert (Int.ltu Int.zero (Int.notbool Int.one)
                  || Int.ltu Int.zero (Int.notbool Int.zero) = true).
  
  unfold Int.notbool.
  clear;int auto.
  destruct (Int.eq i8 ($ OS_STAT_RDY));destruct (Int.eq i9 ($ 0));simpl in H13;auto;tryfalse.
  rewrite H in H13;unfold val_inj in H13;simpl in H13;destruct H13;tryfalse.

  assert (Int.ltu Int.zero (Int.notbool Int.zero)
                  || Int.ltu Int.zero (Int.notbool Int.one) = true).
  
  unfold Int.notbool.
  clear;int auto.
  rewrite H0 in H13;
  unfold val_inj in H13;simpl in H13;destruct H13;tryfalse.

  assert (Int.ltu Int.zero (Int.notbool Int.zero)
              || Int.ltu Int.zero (Int.notbool Int.zero) = true).
  
  unfold Int.notbool.
  clear;int auto.
  rewrite H0 in H13;
  unfold val_inj in H13;simpl in H13;destruct H13;tryfalse.

  
  clear H13.
  destruct Hstrdy as (Hstrdy&Hdly0).

  destruct v'42.

  (* L11-L12 *)
  unfold AEventData.
  hoare unfold.
  hoare forward. 
  hoare forward. (* pauto *)

  go.
 
  
  (* L13-L15 *)
  hoare unfold.
  hoare forward.

   simpl;splits; try (apply isptr_zh; auto).
  clear - H50.
  pauto.
  clear - H51.
  pauto.
  auto.
  destruct (Int.ltu ($ 0) i10);simpl;auto.
  
  instantiate (1:= Afalse).
  hoare_split_pure_all.
  assert (Int.ltu ($ 0) i10 = true).
  destruct (Int.ltu ($ 0) i10).
  auto. 
  simpl in H13. 
  destruct H13.
  tryfalse.
  clear H13.
  inverts H41.
  replace (Int.zero+ᵢ($ 4+ᵢInt.zero)) with ($ 4).
  lets Hout: OSQOut_elim H43.
  unfold V_qfreeblk,V_OSQOut in Hout.
  simpl nth_val in Hout.
  destruct Hout.
  auto.
  destruct H13.
  inverts H13.
  destructs H41.
  hoare forward.
   simpl;splits; try (apply isptr_zh; auto).
  auto.
  clear - H50; pauto.
  clear - H51; pauto.
  auto.

  rewrite Int.unsigned_repr.
  auto.
  go.
  rewrite Int.unsigned_repr.
  auto.
  go.
  rewrite Int.unsigned_repr.
  auto.
  go.
  rewrite Int.unsigned_repr.
  auto.
  go.
  rewrite H45.
  unfold OS_MAX_Q_SIZE in  *.
  auto.
  
  go.
  assert (rule_type_val_match ((Void) ∗)
                          (nth_val'
                             (Z.to_nat
                                ((Int.unsigned x2 - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4))
                             v2) = true).
   eapply wellq_props;eauto.
  assert ((Int.zero+ᵢ($ 4+ᵢInt.zero)) = $ 4).
  go.
  rewrite H55 in H54;auto.
  
  hoare forward. (* pauto *)
  simpl;splits; try (apply isptr_zh; auto).
  auto.
  clear - H50; pauto.
  clear - H51; pauto.
  auto.

  hoare forward. (* pauto *)
  simpl;splits; try (apply isptr_zh; auto).
  auto.
  clear - H50; pauto.
  clear - H51; pauto.
  auto.

  (* L16-L17 *)
  lets Hend: OSQEnd_elim H43.
  unfold V_qfreeblk,V_OSQEnd,V_OSQSize in Hend.
  simpl nth_val in Hend.
  (*v'44 to v'52*)
  assert (Some x = Some (Vptr (v'52, Int.mul i11 ($ 4)+ᵢ$ 4))).
  apply Hend; auto.
  inverts H53.
  lets Hstart: OSQStart_elim H43.
  unfold V_qfreeblk, V_OSQStart, V_OSQSize in Hstart.
  simpl nth_val in Hstart.
  assert (Some x7 = Some (Vptr (v'52, $ 4))).
  apply Hstart; auto.
  inverts H53.
  hoare forward.
  simpl; splits; try (apply isptr_zh; auto); auto. 
  clear - H50; pauto.
  assert ( Int.unsigned (i10 -ᵢ $ 1) <=? Int16.max_unsigned = true).
  apply ge_0_minus_1_in_range; auto. 
  rewrite H55;auto.

  simpl; splits; try (apply isptr_zh; auto); auto.
  clear - H50; pauto.
  assert ( Int.unsigned (i10 -ᵢ $ 1) <=? Int16.max_unsigned = true).
  apply ge_0_minus_1_in_range; auto. 
  rewrite H55;auto.
 
  pauto.
  
  hoare forward. (* pauto *)

  simpl;splits;auto;  try (apply isptr_zh; auto).
  clear - H50; pauto.
  assert ( Int.unsigned (i10 -ᵢ $ 1) <=? Int16.max_unsigned = true).
  apply ge_0_minus_1_in_range; auto. 
  rewrite H56;auto.

  hoare forward. (* pauto *)
  
  (* branch 1: OSQOut == OSQEnd L18 *)
  hoare_split_pure_all.
  clear H54.
  rewrite peq_true in H53.
  assert (Int.eq (x2+ᵢInt.mul ($ 1) ($ 4)) (Int.mul i11 ($ 4)+ᵢ$ 4) = true).
  destruct (Int.eq (x2+ᵢInt.mul ($ 1) ($ 4)) (Int.mul i11 ($ 4)+ᵢ$ 4)).
  auto.
  simpl in H53.
  destruct H53; tryfalse.
  clear H53.


  hoare forward.
  
  assert (rule_type_val_match ((Void) ∗)
                          (nth_val'
                             (Z.to_nat
                                ((Int.unsigned x2 - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4))
                             v2) = true).
  eapply wellq_props;eauto.
  assert ((Int.zero+ᵢ($ 4+ᵢInt.zero)) = $ 4).
  go.
  rewrite H56 in H55;auto.
  assert (x2 =  Int.mul i11 ($ 4)).
  clear -H54.

  lets Hx:Int.eq_spec (x2+ᵢInt.mul ($ 1) ($ 4)) (Int.mul i11 ($ 4)+ᵢ$ 4).
  rewrite H54 in Hx.
  assert  (Int.mul ($ 1) ($ 4) = $ 4).
  go.
  rewrite H in Hx.

  assert (x2+ᵢ$ 4 +ᵢ Int.neg ($ 4)= Int.mul i11 ($ 4)+ᵢ$ 4 +ᵢ Int.neg ($ 4)).
  rewrite Hx;auto.
  
  rewrite Int.add_assoc in H0.
  rewrite Int.add_neg_zero in H0.
  rewrite Int.add_zero in H0.
  
  rewrite Int.add_assoc in H0.
  rewrite Int.add_neg_zero in H0.
  rewrite Int.add_zero in H0.
  auto.
  subst x2.

  (* high level step *)
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  pure intro.
  lets Hmsg : h_has_same_msg H3; eauto.
  simpl; eauto.
  simpljoin1.

  assert (EcbMod.get v'36 (v'51, Int.zero) =
      Some
        (absmsgq
          (nth_val' (Z.to_nat ((Int.unsigned (Int.mul i11 ($ 4)) - Int.unsigned ($ 4)) / 4))
            v2 :: x) x1, x2)) as Hget.
  eapply EcbMod.join_joinsig_get;eauto.
  simpljoin1.


  assert (exists prio m, TcbMod.get v'38 (v'50, Int.zero) = Some (prio, rdy, m)).
 
  eapply TCBList_P_impl_high_tcbcur_rdy with (i9:=i8) (i10:=i9) (tcbls:=v'38) (rtbl:=v'34); eauto.
  destruct H59 as [prio [m H59]].
  assert (TcbMod.get v'37 (v'50, Int.zero) = Some (prio, rdy, m)).
  eapply TcbMod.join_get_get_r; eauto.

  hoare abscsq.
  apply noabs_oslinv.
  eapply OSQPend_high_step_get_succ; eauto.
  go.

  (* L19 : excrit *)
  hoare forward prim.
  (* AOSTCBList *)
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  unfold dllseg at 2.
  fold dllseg.
  unfold node.
  sep pauto.
  repeat (sep cancel dllseg).
  sep cancel Astruct.
  (* AOSPrioTbl *)
  sep lift 2%nat.
  eapply AOSTCBPrioTbl_high_tcblist_get_msg; eauto.
  sep cancel AOSTCBPrioTbl.
  (* AECBList *)
  unfold AECBList.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep pauto.
  eapply evsllseg_compose.
  instantiate (2:=V$OS_EVENT_TYPE_Q
              :: Vint32 i0
                 :: Vint32 i2 :: Vptr (v'32, Int.zero) :: x3 :: v'43 :: nil).
  unfold V_OSEventListPtr; simpl;  auto. 
  auto.  
  auto.
  repeat (sep cancel evsllseg).
  (* AEventNode *)
  
  instantiate (2:=DMsgQ (Vptr (v'32, Int.zero))
                   (x10
              :: Vptr (v'52, $ 4)
                 :: Vptr (v'52, Int.mul i11 ($ 4)+ᵢ$ 4)
                    :: x0
                       :: Vptr (v'52, $ 4)
                          :: Vint32 i11
                             :: Vint32 (i10-ᵢ$ 1)
                                :: Vptr (v'52, Int.zero) :: nil)
                  (x11 :: x12 :: nil) v2).
  unfold AEventNode.
  unfold AEventData.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold AMsgData.
  unfold AOSQCtr, AOSQBlk.
  unfold node.
  sep pauto.
(*  sep lifts (5::6::3::7::8::nil)%nat in H61. 
  apply H61.*)
  sep cancel 3%nat 3%nat.
  sep cancel 4%nat 1%nat.
  sep cancel Astruct.
  sep cancel 4%nat 1%nat.
  sep cancel Aarray.
  eapply tcbdllflag_hold.
  eapply tcbdllflag_hold_middle.
  unfold eq_dllflag.
  instantiate (1 := (v'40
               :: v'21
                  :: x9
                     :: x8
                        :: Vint32 i9
                           :: Vint32 i8
                              :: Vint32 i7
                                 :: Vint32 i6
                                    :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: nil)).
  splits; auto.
  sep cancel tcbdllflag.
  eauto.
  eauto.
  unfold V_OSEventGrp;simpl;auto.
  auto.
  auto.
  split;auto.
  
  go.
  unfolds;simpl;auto.
  eapply get_wellformedosq_end; eauto.
  split; auto.
  simpl;splits; try(apply isptr_zh; auto); auto.
  clear -H50; pauto.
  assert ( Int.unsigned (i10 -ᵢ $ 1) <=? Int16.max_unsigned = true).
  apply ge_0_minus_1_in_range; auto. 
  rewrite H63;auto.
  auto.

  go.
(*
  simpl;splits.
  apply isptr_zh; auto.
  auto.
 *)
  
  rtmatch_solve.
  lets Hnewjoin: ecb_get_set_join_join Hget H5 H22.
  simpljoin1.

  eapply msgqlist_p_compose;eauto.
  eapply R_ECB_ETbl_P_high_tcb_get_msg_hold; eauto.
  eapply ECBList_P_high_tcb_get_msg_hold; eauto.
  eapply ECBList_P_high_tcb_get_msg_hold; eauto.
  eapply msgqnode_p_hold_end; eauto.
  simpl; auto.
  unfold V_OSTCBPrev; simpl nth_val; auto.
  unfold V_OSTCBNext; simpl nth_val; auto.

  simpl;splits;auto.
  apply isptr_zh; auto.
  apply isptr_zh; auto.
  apply isptr_zh; auto.
  
  assert (rule_type_val_match ((Void) ∗)
                          (nth_val'
                             (Z.to_nat
                                ((Int.unsigned (Int.mul i11 ($ 4)) - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4))
                             v2) = true).
  eapply wellq_props;eauto.
  assert ((Int.zero+ᵢ($ 4+ᵢInt.zero)) = $ 4).
  go.
  rewrite H64 in H63;auto.
  clear -H34; pauto.
  clear -H35; pauto.

  splits.
  clear -H36; pauto. 
  clear -H37; pauto.
  clear -H38; pauto.
  clear -H39; pauto.
  clear -H40; pauto.
  auto.

  eapply TCBList_P_tcb_get_msg_hold; eauto.
  eauto.
  eapply TcbMod.join_set_r; eauto.
  eapply TcbMod.get_indom. eexists; eauto.
  eapply RH_CurTCB_high_get_msg_hold; eauto.
  eapply RH_TCBList_ECBList_P_high_get_msg_hold; eauto.
  go.

  (* L20 *)
  hoare forward.

  (* branch 2: OSQOut != OSQEnd L18 *)
  hoare_split_pure_all.
  rewrite peq_true in H53.
  assert (Int.eq (x2+ᵢInt.mul ($ 1) ($ 4)) (Int.mul i11 ($ 4)+ᵢ$ 4) = false).
  destruct (Int.eq (x2+ᵢInt.mul ($ 1) ($ 4)) (Int.mul i11 ($ 4)+ᵢ$ 4)). 
  simpl in H53.
  destruct H53; tryfalse.
  auto.
  clear H53.
 
  hoare forward.
  assert (rule_type_val_match ((Void) ∗)
                              (nth_val'
                                 (Z.to_nat
                                    ((Int.unsigned x2 - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4))
                                 v2) = true).
  eapply wellq_props;eauto.
  assert ((Int.zero+ᵢ($ 4+ᵢInt.zero)) = $ 4).
  go.
  rewrite H56 in H55;auto.

  (* high level step *)
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  pure intro.
  lets Hmsg : h_has_same_msg H3; eauto.
  simpl; eauto.
  simpljoin1.
   
  assert (EcbMod.get v'36 (v'51, Int.zero) =
      Some
        (absmsgq
          (nth_val' (Z.to_nat ((Int.unsigned x2 - Int.unsigned ($ 4)) / 4))
            v2 :: x) x1, x4)) as Hget.
  eapply EcbMod.join_joinsig_get;eauto.
  simpljoin1.
 
  assert (exists prio  m, TcbMod.get v'38 (v'50, Int.zero) = Some (prio, rdy, m)).
  eapply TCBList_P_impl_high_tcbcur_rdy with (i9:=i8); eauto. 
  destruct H59 as [prio [m H59]].
  assert (TcbMod.get v'37 (v'50, Int.zero) = Some (prio, rdy, m)).
  eapply TcbMod.join_get_get_r; eauto.
  hoare abscsq.
  apply noabs_oslinv.
  eapply OSQPend_high_step_get_succ; eauto.
  go.
  
  (* L19 : excrit *)
  hoare forward prim.
  (* AOSTCBList *)
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  unfold dllseg at 2.
  fold dllseg.
  unfold node.
  sep pauto.
  repeat (sep cancel dllseg).
  sep cancel Astruct.
  (* AOSPrioTbl *)
  sep lift 2%nat.
  eapply AOSTCBPrioTbl_high_tcblist_get_msg; eauto.
  sep cancel AOSTCBPrioTbl.
  (* AECBList *)
  unfold AECBList.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  sep pauto.
  eapply evsllseg_compose.
  instantiate (2:=V$OS_EVENT_TYPE_Q
              :: Vint32 i0
                 :: Vint32 i2 :: Vptr (v'32, Int.zero) :: x3 :: v'43 :: nil).
  unfold V_OSEventListPtr; simpl;  auto. 
  auto.  
  auto.
  repeat (sep cancel evsllseg).
  (* AEventNode *)  
  instantiate (2:=DMsgQ (Vptr (v'32, Int.zero))
                  (x10
              :: Vptr (v'52, $ 4)
                 :: Vptr (v'52, Int.mul i11 ($ 4)+ᵢ$ 4)
                    :: x0
                       :: Vptr (v'52, x2+ᵢInt.mul ($ 1) ($ 4))
                          :: Vint32 i11
                             :: Vint32 (i10-ᵢ$ 1)
                                :: Vptr (v'52, Int.zero) :: nil)
                  (x11 :: x12 :: nil) v2).
  unfold AEventNode.
  unfold AEventData.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold AMsgData.
  unfold AOSQCtr, AOSQBlk.
  unfold node.
  sep pauto.
(*  sep lifts (5::6::3::7::8::nil)%nat in H61. 
  apply H61. *)
  sep cancel 5%nat 1%nat.
  sep cancel 3%nat 2%nat.
  sep cancel Astruct.
  sep cancel 4%nat 1%nat.
  sep cancel Aarray.
  eapply tcbdllflag_hold.
  eapply tcbdllflag_hold_middle.
  unfold eq_dllflag.
  instantiate (1 := (v'40
               :: v'21
                  :: x9
                     :: x8
                        :: Vint32 i9
                           :: Vint32 i8
                              :: Vint32 i7
                                 :: Vint32 i6
                                    :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: nil)).
  splits; auto.
  sep cancel tcbdllflag.
  eauto.
  eauto.
  unfolds;simpl;auto.
  auto.
  auto.
  
  simpl;splits;auto.
  clear -H10; pauto.
  clear -H21; pauto.
  apply isptr_zh; auto.
  
  unfolds;simpl;auto.
  eapply get_wellformedosq_end'; eauto.

  eapply Int_eq_false_Vptr_neq; eauto.
  rewrite Int.eq_sym. eauto.
  
  split; auto.
  simpl;splits;auto.
  apply isptr_zh; auto.
  apply isptr_zh; auto.
  clear -H50; pauto.
 
  assert ( Int.unsigned (i10 -ᵢ $ 1) <=? Int16.max_unsigned = true).
  apply ge_0_minus_1_in_range;auto.
  rewrite H63;auto.
  auto.
  simpl;splits;auto.
  apply isptr_zh; auto.


  rtmatch_solve.
  lets Hnewjoin: ecb_get_set_join_join Hget H5 H22.
  simpljoin1.
  
  eapply msgqlist_p_compose; eauto.
  eapply R_ECB_ETbl_P_high_tcb_get_msg_hold; eauto.
  eapply ECBList_P_high_tcb_get_msg_hold; eauto.
  eapply ECBList_P_high_tcb_get_msg_hold; eauto.
  eapply msgqnode_p_hold_no_end; eauto.
  simpl; auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
 

  simpl;splits;auto.
  apply isptr_zh; auto.
  apply isptr_zh; auto.
  apply isptr_zh; auto.

  assert (rule_type_val_match ((Void) ∗)
                              (nth_val'
                                 (Z.to_nat
                                    ((Int.unsigned x2 - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4))
                                 v2) = true).
  eapply wellq_props;eauto.
  assert ((Int.zero+ᵢ($ 4+ᵢInt.zero)) = $ 4).
  go.
  rewrite H64 in H63;auto.
  clear -H34; pauto.
  clear -H35; pauto.
  splits.
  clear -H36; pauto.
  clear -H37; pauto.
  clear -H38; pauto.
  clear -H39; pauto.
  clear -H40; pauto.
  auto.

  eapply TCBList_P_tcb_get_msg_hold; eauto.
  eauto.
  eapply TcbMod.join_set_r; eauto.
  eapply TcbMod.get_indom. eexists; eauto.
  eapply RH_CurTCB_high_get_msg_hold; eauto.
  eapply RH_TCBList_ECBList_P_high_get_msg_hold; eauto.
  go.
  
  (* L20 *)
  hoare forward.
  clear.
  int auto.
  int auto.
  hoare forward.

(***************************************)
eapply OSQPendRightPart2 with (x8:=x8); eauto.
(***************************************)
  
  (*---------ignore sem-----------*)
  clear -H8.
  remember (Int.eq i1 ($ OS_EVENT_TYPE_Q)) as X.
  destruct X;simpl in H8;destruct H8;tryfalse.
  apply backward_rule1 with Afalse.
  intros.
  sep lift 13%nat in H0.

  symmetry in HeqX.
  lets Hx: event_type_n_match H0 HeqX.
  tryfalse.
  apply pfalse_rule.

  clear -H8.
  remember (Int.eq i1 ($ OS_EVENT_TYPE_Q)) as X.
  destruct X;simpl in H8;destruct H8;tryfalse.
  apply backward_rule1 with Afalse.
  intros.
  sep lift 13%nat in H0.
  unfold AEventData in H0.
  sep normal in H0.
  sep split in H0.
  unfolds in H1;simpl in H1;inverts H1.
  symmetry in HeqX.
  rewrite Int.eq_false in HeqX.
  tryfalse.
  auto.
  apply pfalse_rule.
  
  clear -H8.
  remember (Int.eq i1 ($ OS_EVENT_TYPE_Q)) as X.
  destruct X;simpl in H8;destruct H8;tryfalse.
  apply backward_rule1 with Afalse.
  intros.
  sep lift 13%nat in H0.
  unfold AEventData in H0.
  sep normal in H0.
  sep split in H0.

  clear - H1 HeqX.
  unfolds in H1.
  simpl in H1.
  inverts H1.
  rewrite Int.eq_false in HeqX.
  inversion HeqX.
  auto.
  apply pfalse_rule.
 
  (*-------------*)
  pure intro. 
  inverts H4.
  rename H5 into H4.
  
  hoare forward.
  pure intro.
  instantiate (1:=Afalse).
  hoare abscsq.
  apply noabs_oslinv.
  eapply qpend_absinfer_no_q;eauto.
  pauto.
  intro;simpljoin1;tryfalse.
  hoare forward prim.
  exact H6.
  pauto.
  hoare forward.
  hoare forward.
  pure intro.
  assert (Int.eq ($ 0) ($ 0) =true ) by pauto.
  rewrite H3 in H2.
  destruct H2;simpl in H2;tryfalse.
Qed.
