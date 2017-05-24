Require Import sem_common.
Require Import sempend_pure.
Require Import OSMutex_common.

Require Import OSMutexPendPart5.
Require Import OSMutexPendPart1.
Require Import OSMutexPendPart2.
Require Import OSQPostPure.
Require Import mutex_pend_pure.
Open Scope code_scope.
Set Printing Depth 999.

Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.


Lemma mutex_pend_part_0: forall
  (i : int32)
  (H1 : Int.unsigned i <= 65535)
  (v' : val)
  (v'0 : val)
  (v'1 : val)
  (v'2 : val)
  (v'3 : val)
  (v'4 : val)
  (v'5 : list vallist)
  (v'6 : list vallist)
  (v'7 : list vallist)
  (v'8 : list EventData)
  (v'9 : list os_inv.EventCtr)
  (v'10 : vallist)
  (v'11 : val)
  (v'12 : val)
  (v'13 : list vallist)
  (v'14 : vallist)
  (v'15 : list vallist)
  (v'16 : vallist)
  (v'17 : val)
  (v'18 : EcbMod.map)
  (v'19 : TcbMod.map)
  (v'20 : int32)
  (v'21 : addrval)
  (v'22 : val)
  (v'23 : list vallist)
  (v'26 : list os_inv.EventCtr)
  (v'27 : list os_inv.EventCtr)
  (v'28 : list EventData)
  (v'29 : list EventData)
  (v'31 : vallist)
  (v'32 : val)
  (v'34 : list vallist)
  (v'36 : list vallist)
  (v'37 : vallist)
  (v'38 : val)
  (v'39 : EcbMod.map)
  (v'40 : TcbMod.map)
  (v'42 : val)
  (v'44 : vallist)
  (v'46 : val)
  (v'47 : EcbMod.map)
  (v'48 : EcbMod.map)
  (v'49 : EcbMod.map)
  (v'51 : addrval)
  (H5 : ECBList_P v'46 Vnull v'27 v'29 v'48 v'40)
  (H11 : EcbMod.join v'47 v'49 v'39)
  (H14 : length v'26 = length v'28)
  (v'24 : addrval)
  (v'30 : block)
  (H13 : array_type_vallist_match Int8u v'44)
  (H19 : length v'44 = ∘ OS_EVENT_TBL_SIZE)
  (H20 : isptr v'46)
  (x2 : val)
  (x3 : val)
  (i0 : int32)
  (H22 : Int.unsigned i0 <= 255)
  (i2 : int32)
  (H23 : Int.unsigned i2 <= 65535)
  (H24 : isptr x2)
  (H18 : RL_Tbl_Grp_P v'44 (Vint32 i0))
  (H25 : isptr v'46)
  (H4 : ECBList_P v'42 (Vptr (v'30, Int.zero)) v'26 v'28 v'47 v'40)
  (H2 : isptr (Vptr (v'30, Int.zero)))
  (H16 : id_addrval' (Vptr (v'30, Int.zero)) OSEventTbl OS_EVENT =
        Some v'24)
  (H21 : Int.unsigned ($ OS_EVENT_TYPE_MUTEX) <= 255)
  (H7 : R_ECB_ETbl_P (v'30, Int.zero)
         ((V$ OS_EVENT_TYPE_MUTEX
           :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'46 :: nil)%list,
         v'44) v'40)
  (x : int32)
  (x0 : owner)
  (x1 : waitset)
  (H17 : MatchMutexSem (Vint32 i2) x2 x x0)
  (H8 : EcbMod.joinsig (v'30, Int.zero) (absmutexsem x x0, x1) v'48
         v'49)
  (Hget : EcbMod.get v'39 (v'30, Int.zero) =
         Some (absmutexsem x x0, x1))
  (H26 : RH_ECB_P (absmutexsem x x0, x1))
  (H3 : ECBList_P v'42 Vnull
         (v'26 ++
          (((V$ OS_EVENT_TYPE_MUTEX
             :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'46 :: nil)%list,
           v'44) :: nil) ++ v'27)
         (v'28 ++ (DMutex (Vint32 i2) x2 :: nil) ++ v'29) v'39 v'40)
  (H6 : RLH_ECBData_P (DMutex (Vint32 i2) x2) (absmutexsem x x0, x1))
  (v'25 : val)
  (v'41 : val)
  (v'43 : TcbMod.map)
  (v'45 : TcbMod.map)
  (v'50 : val)
  (v'52 : block)
  (H29 : v'32 <> Vnull)
  (H30 : join v'43 v'45 v'40)
  (H31 : TCBList_P v'32 v'34 v'37 v'43)
  (H28 : Vptr (v'52, Int.zero) <> Vnull)
  (x11 : val)
  (x12 : val)
  (H35 : isptr x12)
  (H36 : isptr x11)
  (i6 : int32)
  (H39 : Int.unsigned i6 <= 255)
  (i5 : int32)
  (H40 : Int.unsigned i5 <= 255)
  (i4 : int32)
  (H41 : Int.unsigned i4 <= 255)
  (i3 : int32)
  (H42 : Int.unsigned i3 <= 255)
  (i1 : int32)
  (H43 : Int.unsigned i1 <= 255)
  (H34 : isptr v'25)
  (H12 : isptr v'50)
  (H : RH_TCBList_ECBList_P v'18 v'19 (v'52, Int.zero))
  (H0 : RH_CurTCB (v'52, Int.zero) v'19)
  (H9 : RH_TCBList_ECBList_P v'39 v'40 (v'52, Int.zero))
  (H10 : RH_CurTCB (v'52, Int.zero) v'40)
  (st : taskstatus)
  (Hgetcur_subr : TcbMod.get v'45 (v'52, Int.zero) =
                 Some (i6, st, x11))
  (Hgetcur : TcbMod.get v'40 (v'52, Int.zero) = Some (i6, st, x11))
  (Hneq_idle : i6 <> $ OS_IDLE_PRIO)
  (H37 : Int.unsigned ($ 0) <= 65535)
  (H38 : Int.unsigned ($ OS_STAT_RDY) <= 255)
  (H32 : TCBList_P (Vptr (v'52, Int.zero))
          ((v'50
            :: v'25
               :: x12
                  :: x11
                     :: V$ 0
                        :: V$ OS_STAT_RDY
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3
                                       :: Vint32 i1 :: nil)%list
           :: v'36) v'37 v'45)
  (Hcurnode : TCBNode_P
               (v'50
                :: v'25
                   :: x12
                      :: x11
                         :: V$ 0
                            :: V$ OS_STAT_RDY
                               :: Vint32 i6
                                  :: Vint32 i5
                                     :: Vint32 i4
                                        :: Vint32 i3
                                           :: 
                                           Vint32 i1 :: nil)%list
               v'37 (i6, st, x11))
  (H15 : x11 = Vnull)
(* ================================= *) ,
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (v'52, Int.zero) init_lg **
    ((EX v0 : val, LV timeout @ Int16u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV legal @ Int8u |-> v0) **
     (EX v0 : val, LV pip @ Int8u |-> v0) **
     (EX v0 : val, LV mprio @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.isrdy @ Int8u |-> v0) **
     (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
     (EX v0 : val, LV pevent2 @ OS_EVENT ∗ |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((timeout, Int16u)
      :: (pevent, OS_EVENT ∗)
         :: (legal, Int8u)
            :: (pip, Int8u)
               :: (mprio, Int8u)
                  :: (os_code_defs.isrdy, Int8u)
                     :: (ptcb, OS_TCB ∗)
                        :: (pevent2, OS_EVENT ∗) :: nil)%list,
   Afalse|}|- (v'52, Int.zero)
   {{Astruct (v'52, Int.zero) OS_TCB_flag
       (v'50
        :: (v'25
            :: x12
               :: x11
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 i6
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3 :: Vint32 i1 :: nil)%list) **
     dllseg v'50 (Vptr (v'52, Int.zero)) v'41 Vnull v'36
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBList @ OS_TCB ∗ |-> v'32 **
     dllseg v'32 Vnull v'25 (Vptr (v'52, Int.zero)) v'34
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'52, Int.zero) **
     AEventData
       (V$ OS_EVENT_TYPE_MUTEX
        :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'46 :: nil)%list
       (DMutex (Vint32 i2) x2) **
     Astruct (v'30, Int.zero) OS_EVENT
       (V$ OS_EVENT_TYPE_MUTEX
        :: (Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'46 :: nil)%list) **
     Aarray v'24 (Tarray Int8u ∘ OS_EVENT_TBL_SIZE) v'44 **
     Aie false **
     Ais nil **
     Acs (true :: nil)%list **
     Aisr empisr **
     GV OSEventList @ OS_EVENT ∗ |-> v'42 **
     evsllseg v'42 (Vptr (v'30, Int.zero)) v'26 v'28 **
     evsllseg v'46 Vnull v'27 v'29 **
     A_isr_is_prop **
     tcbdllflag v'32
       (v'34 ++
        (v'50
         :: v'25
            :: x12
               :: x11
                  :: V$ 0
                     :: V$ OS_STAT_RDY
                        :: Vint32 i6
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3 :: Vint32 i1 :: nil)%list
        :: v'36) **
     AOSRdyTblGrp v'37 v'38 **
     AOSTCBPrioTbl v'31 v'37 v'40 v'51 **
     HECBList v'39 **
     HTCBList v'40 **
     HCurTCB (v'52, Int.zero) **
      <|| mutexpend (Vptr (v'30, Int.zero) :: Vint32 i :: nil)%list
     ||>  **
     p_local OSLInv (v'52, Int.zero) init_lg **
     LV legal @ Int8u |-> (V$ 1) **
     AOSEventFreeList v'5 **
     AOSQFreeList v'6 **
     AOSQFreeBlk v'7 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'22 v'23 **
     AOSTime (Vint32 v'20) **
     HTime v'20 **
     AGVars **
     atoy_inv' **
     LV pevent2 @ OS_EVENT ∗ |-> v'4 **
     LV ptcb @ OS_TCB ∗ |-> v'3 **
     LV os_code_defs.isrdy @ Int8u |-> v'2 **
     LV mprio @ Int8u |-> v'1 **
     LV pip @ Int8u |-> v'0 **
     LV timeout @ Int16u |-> Vint32 i **
     LV pevent @ OS_EVENT ∗ |-> Vptr (v'30, Int.zero) **
     A_dom_lenv
       ((timeout, Int16u)
        :: (pevent, OS_EVENT ∗)
           :: (legal, Int8u)
              :: (pip, Int8u)
                 :: (mprio, Int8u)
                    :: (os_code_defs.isrdy, Int8u)
                       :: (ptcb, OS_TCB ∗)
                          :: (pevent2, OS_EVENT ∗) :: nil)%list}} 
   pip ′ =ₑ 〈 Int8u 〉 (pevent ′ → OSEventCnt ≫ ′ 8);ₛ
   If(pip ′ >ₑ OSTCBCur ′ → OSTCBPrio
      ||ₑ OSTCBCur ′ → OSTCBPrio ==ₑ pip ′)
        {EXIT_CRITICAL;ₛ
        RETURN ′ OS_ERR_MUTEX_PRIO}  ;ₛ
   mprio ′ =ₑ
   〈 Int8u 〉 (pevent ′ → OSEventCnt &ₑ ′ OS_MUTEX_KEEP_LOWER_8);ₛ
   ptcb ′ =ₑ pevent ′ → OSEventPtr;ₛ
   If(mprio ′ ==ₑ ′ OS_MUTEX_AVAILABLE)
        {pevent ′ → OSEventCnt &= ′ OS_MUTEX_KEEP_UPPER_8;ₛ
        pevent ′ → OSEventCnt =ₑ
        pevent ′ → OSEventCnt |ₑ OSTCBCur ′ → OSTCBPrio;ₛ
        pevent ′ → OSEventPtr =ₑ OSTCBCur ′;ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′ OS_NO_ERR}  ;ₛ
   If(ptcb ′ ==ₑ OSTCBCur ′)
        {EXIT_CRITICAL;ₛ
        RETURN ′ OS_ERR_MUTEX_DEADLOCK}  ;ₛ
   If(ptcb ′ → OSTCBPrio ==ₑ ′ OS_IDLE_PRIO)
        {EXIT_CRITICAL;ₛ
        RETURN ′ OS_ERR_MUTEX_IDLE}  ;ₛ
   If(ptcb ′ → OSTCBStat !=ₑ ′ OS_STAT_RDY
      ||ₑ ptcb ′ → OSTCBDly !=ₑ ′ 0)
        {EXIT_CRITICAL;ₛ
        RETURN ′ OS_ERR_NEST}  ;ₛ
   If(mprio ′ ==ₑ OSTCBCur ′ → OSTCBPrio)
        {EXIT_CRITICAL;ₛ
        RETURN ′ OS_ERR_MUTEX_DEADLOCK}  ;ₛ
   IF(ptcb ′ → OSTCBPrio !=ₑ pip ′ &&ₑ
      mprio ′ >ₑ OSTCBCur ′ → OSTCBPrio)
        {If(OSTCBPrioTbl ′ [pip ′]
            !=ₑ 〈 OS_TCB ∗ 〉 os_mutex.PlaceHolder)
              {EXIT_CRITICAL;ₛ
              RETURN ′ OS_ERR_MUTEXPR_NOT_HOLDER}  ;ₛ
        OSTCBPrioTbl ′ [ptcb ′ → OSTCBPrio] =ₑ
        〈 OS_TCB ∗ 〉 os_mutex.PlaceHolder;ₛ
        OSTCBPrioTbl ′ [pip ′] =ₑ 〈 OS_TCB ∗ 〉 ptcb ′;ₛ
        OSRdyTbl ′ [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX;ₛ
        If(OSRdyTbl ′ [ptcb ′ → OSTCBY] ==ₑ ′ 0)
             {OSRdyGrp ′ &= ∼ ptcb ′ → OSTCBBitY}  ;ₛ
        ptcb ′ → OSTCBPrio =ₑ pip ′;ₛ
        ptcb ′ → OSTCBY =ₑ ptcb ′ → OSTCBPrio ≫ ′ 3;ₛ
        ptcb ′ → OSTCBBitY =ₑ OSMapTbl ′ [ptcb ′ → OSTCBY];ₛ
        ptcb ′ → OSTCBX =ₑ ptcb ′ → OSTCBPrio &ₑ ′ 7;ₛ
        ptcb ′ → OSTCBBitX =ₑ OSMapTbl ′ [ptcb ′ → OSTCBX];ₛ
        OSRdyGrp ′ =ₑ OSRdyGrp ′ |ₑ ptcb ′ → OSTCBBitY;ₛ
        OSRdyTbl ′ [ptcb ′ → OSTCBY] =ₑ
        OSRdyTbl ′ [ptcb ′ → OSTCBY] |ₑ ptcb ′ → OSTCBBitX;ₛ
        OSTCBCur ′ → OSTCBStat =ₑ ′ OS_STAT_MUTEX;ₛ
        OSTCBCur ′ → OSTCBDly =ₑ timeout ′;ₛ
        OS_EventTaskWait (­ pevent ′­);ₛ
        EXIT_CRITICAL;ₛ
        OS_Sched (­);ₛ
        ENTER_CRITICAL;ₛ
        If(OSTCBCur ′ → OSTCBMsg !=ₑ NULL)
             {EXIT_CRITICAL;ₛ
             RETURN ′ OS_NO_ERR}  ;ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′ OS_TIMEOUT} 
       ELSE {OSTCBCur ′ → OSTCBStat =ₑ ′ OS_STAT_MUTEX;ₛ
            OSTCBCur ′ → OSTCBDly =ₑ timeout ′;ₛ
            OS_EventTaskWait (­ pevent ′­);ₛ
            EXIT_CRITICAL;ₛ
            OS_Sched (­);ₛ
            ENTER_CRITICAL;ₛ
            If(OSTCBCur ′ → OSTCBMsg !=ₑ NULL)
                 {EXIT_CRITICAL;ₛ
                 RETURN ′ OS_NO_ERR}  ;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′ OS_TIMEOUT}    {{Afalse}}
.
Proof.
  intros.
  subst.
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  pure_auto. tryfalse.
  pure_auto.
  
  assert (Feq_i2_1:(Int.shru i2 ($ 8)) = (Int.modu (Int.shru i2 ($ 8)) ($ Byte.modulus))).
  {
    clear - H23.
    apply eq_sym.
    apply le65535shr8mod255self. 
    auto.
  }

  rewrite <- Feq_i2_1 in *.
  remember (Int.shru i2 ($ 8)) as cpip.

  assert (x = cpip).
  {
    clear -Heqcpip H17. 
    unfold MatchMutexSem in H17.
    mytac_H.
    inverts H.
    auto.
  }
  subst x.

  assert (Fneq_i2_1: Int.unsigned (i2>>ᵢ$ 8) <= 255).
  {
    apply mund_int_a1; auto.
  }

  lzh_hoare_if.
  {
  apply mund_int_a2; auto.
  }
  apply mund_val_inj_a0.
  apply mund_int_a2; auto.

  apply mund_val_inj_a0.


  apply mund_val_inj_a1; auto.
  
  assert (Hlte: Int.ltu cpip i6 = false).
  {
    subst cpip.
    clear -LHift_true.
    destruct (Int.ltu i6 (i2>>ᵢ$ 8)) eqn: H.
    destruct (Int.eq i6 (i2>>ᵢ$ 8)) eqn: H1.
  
    eapply mund_int_ltu_revers; auto.
    eapply mund_int_ltu_revers; auto.
    destruct (Int.eq i6 (i2>>ᵢ$ 8)) eqn: H1.
    eapply mund_int_ltu_revers; auto.
    destruct LHift_true.
    unfold bool_or in H0.
    unfold val_inj in H0.
    rewrite mund_int_ltu_revers in H0; auto.
    simpl in H0.
    tryfalse.
  }
  clear LHift_true.

  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_cur_prio_higher; eauto.
  can_change_aop_solver.

  hoare lift 13%nat pre. 
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  (***** ex critical ****)

  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 4%nat 1%nat.
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel dllseg.
  sep cancel 2%nat 1%nat.
  sep pauto.
  unfolds; auto.
  unfolds; auto.
  split; auto.
  struct_type_match_solver.
  eauto.
  eauto.
  eauto.
  pure_auto.
  hoare forward.
(************************ CurPrio <= pip finished ************************)
(**************************** CurPiro > pip  ****************************)
  assert (Hcur_prio: Int.ltu cpip i6 = true).
  {
    subst cpip.
    clear - Hif_false.
    eapply intlemma11.
    auto.
  }
  clear Hif_false.

  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  pure_auto.
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.

  assert (Htmp:(Int.modu (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ Byte.modulus)) = (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8)).
  {
    clear -H23.
    idtac.
    apply mund_int_a3 in H23.
    remember (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
    clear Heqi.
    unfold Int.modu.


    rewrite mund_int_byte_modulus.

    repeat ur_rewriter.

    apply mund_int_mod. auto.
  }
  rewrite -> Htmp in *. 
  clear Htmp.
  remember (i2&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as cmprio.
  lets Fneq_i2_2: mund_int_a3 H23.
(************************* Mutexsem is available *************************)
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  assert (Htmp:cmprio = $ OS_MUTEX_AVAILABLE).
  {
    subst cmprio.
    subst cpip.
    clear -LHift_true.
    lzh_simpl_int_eq.
    auto.
  }
  clear LHift_true.
  inverts Htmp.

  subst.
  assert (Havai_none: x0 = None).
  {
    clear -H17 H15.
    unfold MatchMutexSem in H17.
    mytac.
    inverts H.
    apply H3.
    auto.
  }
  subst.
  assert (Htmp: x1 = nil).
  {
    clear -H26.
    unfold RH_ECB_P in H26.
    mytac.
  }
  subst.
  assert (Hprio_i6:Int.unsigned i6 < 64).
  {
    clear - Hcurnode.
    unfold TCBNode_P in Hcurnode.
    mytac.
    unfold RL_TCBblk_P in H1.
    mytac.
    inverts H1.
    auto.
  }
  
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  (* pure_auto. *)
  hoare forward.
  (* pure_auto. *)
  (* ** ac: Check acpt_int_lemma0. *)
  assert (Htmp: Int.unsigned (i2&ᵢ$ OS_MUTEX_KEEP_UPPER_8) <= 65535).
  {
    apply acpt_int_lemma0.
    auto.
  }
  struct_type_match_solver.
  struct_type_match_solver.
  pure_auto.
  hoare forward.

  
  transform_pre mutex_pend_inv_update1 ltac:(sep cancel AEventData).
  (** the unfold of transform_pre:
    eapply backward_rule1.
    intros.
    eapply mutex_pend_inv_update1; eauto.
    sep cancel AEventData.
    exact_s.
  *)

(***************** infer the high level cur_stat is rdy *****************)

  repeat match goal with
           | H: RLH_ECBData_P _ _ |- _ =>
             clear H
           | H: ECBList_P _ Vnull (_ ++ _ ++ _) (_ ++ _ ++ _) _ _ |- _=>
             clear H
         end.
  hoare_split_pure_all.

  hoare lift 23%nat pre. (** lift AOSRdyTblGrp **)
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.
  
  transform_pre AOSRdyTblGrp_fold ltac:(sep cancel GAarray;
                                        sep cancel AOSRdyGrp).
  rename v'38 into os_rdy_tbl.
  destruct H6 as (Hrtbl_type & Hrtbl_len).
  destruct H27 as (Hgrp1 & Hgrp2).

  Open Scope list_scope.
  (** put AOSRdyTblGrp in older place **)
  hoare lifts (2::3::4::5::6::7::8::9::10::11::12::13::14
                ::15::16::17::18::19::20::21::22::23::nil)%nat pre.

  assert (Htmp1: st = rdy).
  {
    clear -Hcurnode Hrtbl_type Hrtbl_len.
    eapply mutexpend_TCBNode_P_in_tcb_rdy; eauto.
  }
  subst st.

(**************************** rdy infer: end ****************************)
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_available_return; eauto.
  can_change_aop_solver.

  (* ** ac: Check lzh_ecb_join_set_one. *)
  match goal with
    | H: EcbMod.join v'47 _ v'39 |- _ =>
      lets Hnewjoin: lzh_ecb_join_set_one H; eauto
  end.
  destruct Hnewjoin as (ml1n & Ht1 & Ht2).
  
  hoare forward prim.
  (** * cancel AECBList *)
  unfold AECBList.
  sep pauto.

  eapply lzh_evsllseg_compose.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  sep pauto.
  sep cancel AEventData.
  unfold AOSEvent.
  sep pauto.
  unfold AOSEventTbl.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  (** * AOSTCBList *)
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 7%nat 1%nat.
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel dllseg.
  sep cancel 5%nat 1%nat.
  exact_s.
  unfolds; auto.
  unfolds; auto.
  split; [auto | struct_type_match_solver].
  eauto.
  eauto.
  eauto.
  eauto.
  (* ** ac: Check acpt_intlemma6. *)
  assert (Htmp: Int.unsigned (Int.or (i2&ᵢ$ OS_MUTEX_KEEP_UPPER_8) i6) <= 65535).
  {
    apply acpt_intlemma6.
    clear -Hprio_i6.
    omega.
  }
  split; [auto | struct_type_match_solver].
  eauto.
  unfolds; auto.
  auto.
  unfolds; auto.
  eauto.
  eauto.

  eapply ecblist_p_compose; eauto. 
  unfold ECBList_P.
  simpl.
  fold ECBList_P.
  eexists.
  splits; eauto.
  do 3 eexists.
  splits; eauto.
  unfolds; auto.

  eapply mutex_acpt_rh_tcblist_ecblist_p_hold; eauto.

  pure_auto.

  hoare forward.
(********************** mutex is available finished **********************)
(********************** mutex is not avalable begin **********************)
  assert (Hmutex_not_avail: cmprio <> ($ OS_MUTEX_AVAILABLE)).
  {
    subst  cmprio cpip.
    clear -Hif_false.
    lzh_simpl_int_eq.
    auto.
  }
  clear Hif_false.
  
  hoare_unfold.
  
  unfolds in H17.
  destruct H17 as (tv & top & F1 & F2 & F3 & F4 & _ & F5).
  inverts F1; inverts F3; inverts F4.
  clear H15.
  lets F6: F5 Hmutex_not_avail.
  clear F5.
  destruct F6 as (xtid & F7 & F8).
  inverts F7; inverts F8.
  clear H17.
  clear H15.

  clear H.
  rename H9 into H.
  assert (H_ptcb: exists xp xm xs, TcbMod.get v'40 xtid = Some (xp, xs, xm)).
  {
    unfolds in H.
    destruct H as (_ & _ & _ & H).
    destruct H as (_ & _ & H).
    unfolds in H.
    eapply H.
    eauto.
  }
  destruct H_ptcb as (xp & xm & xs & H_ptcb).

  (** * rename TcbList_P part *)
  Set Printing Depth 300.
  rename H31 into Htcblist_subl.
  rename H32 into Htcblist_subr.
  unfold TCBList_P in Htcblist_subr.
  fold TCBList_P in Htcblist_subr.
  mytac_H.
  inverts H9; inverts H15.
  assert (Htmp: x4 = (i6, st, Vnull)).
  {
    clear - H17 Hgetcur_subr.
    rename H17 into H.
    unfold TcbJoin in *.
    apply TcbMod.join_get_get_l with (a:=(v'52, Int.zero)) (b:=x4) in H.
    rewrite H in *.
    inverts Hgetcur_subr.
    auto.
    auto.
    apply TcbMod.get_sig_some; auto.
  }
  subst x4.
  clear H27.
  rename H31 into Htcblist_subr.

  rename H30 into Htcbjoin_whole.
  rename H17 into Htcbjoin_right.
  rename v'40 into tcbls.
  rename v'43 into tcbls_l.
  rename v'45 into tcbls_r.
  rename v'52 into cur_addr.
  rename v'30 into pevent_addr.
  rename xtid into ptcb_tid.

  rename i6 into cur_prio.
  rename xp into ptcb_prio.
  rename tv into x.
  rename x1 into wls.

(*************************** ptcb is cur: err ***************************)
  lzh_hoare_if.
  {
    destruct ptcb_tid.
    destruct (peq b cur_addr).
    apply mund_val_inj_a0.
    unfold val_inj.
    pure_auto.
  }
  {
    eapply mutex_pend_ptcb_is_cur_err; eauto.
  }

  assert (H_ptcb_not_cur: ptcb_tid <> (cur_addr, Int.zero)).
  {
    clear -Hif_false.
    destruct ptcb_tid.
    destruct (peq b cur_addr) eqn:H;
    destruct (Int.eq i Int.zero) eqn:H1.
    unfold val_inj in *; destruct Hif_false; tryfalse.
    unfold not.
    intros.
    inverts H0.
    lzh_simpl_int_eq; tryfalse.
    unfold not; intros; inverts H0.
    tryfalse.
    unfold not; intros; inverts H0.
    tryfalse.
  }    
    
  clear Hif_false.
  assert (H_where_ptcb_in: TcbMod.get tcbls_l ptcb_tid = Some (ptcb_prio, xs, xm) \/
                 TcbMod.get tcbls_r ptcb_tid = Some (ptcb_prio, xs, xm)).
  {
    clear -H_ptcb Htcbjoin_whole.
    eapply TcbMod.join_get_or; eauto.
  }
  
(************************* ptcb_tid is left to Hcur *************************)
  destruct H_where_ptcb_in as [H_ptcb_in_left | H_ptcb_in_right].
  Focus 1.

  eapply backward_rule1.
  intros.
  sep lift 8%nat in H9.
  eapply lzh_tcb_list_split.
  unfold tcbdllseg.
  sep cancel dllseg.
  exact_s.
  eapply H_ptcb_in_left.
  eauto.
  hoare_split_pure_all.
  inverts H9; inverts H30.
  rename H17 into Hget_last_tcb.
  clear H46 H9.

  rename H33 into Hptcb_node.
  rename H44 into Htcblist_sub_left.
  rename H45 into Htcblist_sub_right.

  rename H31 into Htcbjoin_sub_whole.
  rename H32 into Htcbjoin_sub_right.
  rename v'50 into tcbls_sub_l.
  rename v'53 into tcbls_sub_r.
  (** info: tcbls_sub_l ++ ptcb_node ++ tcbls_sub_r = tcbls_l **)
  
  hoare_unfold.
  rename v'34 into ptcb_addr.

  remember Hptcb_node as Hptcb_node'.
  clear HeqHptcb_node'.
  unfold TCBNode_P in Hptcb_node'.
  destruct Hptcb_node' as (Ht1 & Ht2 & Hptcb_blk & Hptcb_stat).
  inverts Ht1; inverts Ht2.
(*************************** split tcblist end ***************************)
(*************************** ptcb_prio == idle : err ***************************)
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  
  {
       eapply mutex_pend_ptcb_is_idle_err_left_to_cur; eauto. 
  }
(************************** ptcb_prio != idle : err **************************)
  assert (Hptcb_prio_not_idle:ptcb_prio <> ($ OS_IDLE_PRIO)).
  {
    clear - Hif_false.
    lzh_simpl_int_eq.
    auto.
  }
  clear Hif_false.

  assert (Hptcb_prio_scope: 0 <= Int.unsigned ptcb_prio < 64).
  {
    clear -Hptcb_blk.
    unfold RL_TCBblk_P in Hptcb_blk.
    mytac_H.
    inverts H11; inverts H1; inverts H3; inverts H2.
    inverts H0; inverts H4; inverts H.
    auto.
  }
  destruct Hptcb_prio_scope as (Hptcb_prio_scope_obv & Hptcb_prio_scope).
  rename i10 into ptcb_stat.
(*************************** ptcb not rdy: err ***************************)

  lzh_hoare_if.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  
  assert (Hif_ptcb_is_not_rdy:
            (ptcb_stat <> ($ OS_STAT_RDY)) \/
            (i11 <> ($ 0))).
  {
    clear -LHift_true.
    rename LHift_true into H.

    (* ** ac: Check mund_ltu_a1. *)
    (* ** ac: Check mund_ltu_a2. *)
    (* ** ac: Check Int.eq_true. *)
    destruct (Int.eq ptcb_stat ($ OS_STAT_RDY)) eqn: F1;
      destruct (Int.eq i11 ($ 0)) eqn: F2;
      unfold val_inj in H;
      unfold notint in H;
      unfold Int.notbool in H;
      unfold bool_or in H;
      try rewrite Int.eq_true in H;
      try rewrite mund_ltu_a1 in H;
      try rewrite mund_ltu_a2 in H;
      simpl in H.
 
    rewrite Int.eq_false in H.
    rewrite mund_ltu_a1 in H.
    simpl in H.
    destruct H; tryfalse.
    pure_auto.

    rewrite Int.eq_false in H.
    rewrite mund_ltu_a1 in H.
    simpl in H.
    destruct H; tryfalse.
    lzh_simpl_int_eq.
    right.
    auto.
    pure_auto.
    
    lzh_simpl_int_eq.
    left.
    auto.

    lzh_simpl_int_eq.
    left; auto.
  }
            
  clear LHift_true.
  {
    eapply mutex_pend_ptcb_is_not_rdy_left_to_cur; eauto.
  }

(***************************** ptcb is ready *****************************)
  assert (Hif_ptcb_is_rdy:
            (ptcb_stat = ($ OS_STAT_RDY)) /\
            (i11 = ($ 0))).
  {
    clear - Hif_false.
    rename Hif_false into H.
    
    destruct (Int.eq ptcb_stat ($ OS_STAT_RDY)) eqn: F1;
      destruct (Int.eq i11 ($ 0)) eqn: F2;
      unfold val_inj in H;
      unfold notint in H;
      unfold Int.notbool in H;
      unfold bool_or in H;
      try rewrite Int.eq_true in H;
      try rewrite mund_ltu_a1 in H;
      try rewrite mund_ltu_a2 in H;
      simpl in H;
      lzh_simpl_int_eq.

    auto.
    rewrite Int.eq_false in H.
    rewrite mund_ltu_a1 in H.
    simpl in H.
    destruct H; tryfalse.
    pure_auto.

    destruct H; tryfalse.
    destruct H; tryfalse.
  }

  clear Hif_false.
  destruct Hif_ptcb_is_rdy as (Hif_ptcb_is_rdy1 & Hif_ptcb_is_rdy2).

  hoare lift 24%nat pre.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.
  
  transform_pre AOSRdyTblGrp_fold ltac:(sep cancel GAarray;
                                        sep cancel AOSRdyGrp).

  rename v'37 into os_rdy_tbl.
  destruct H9 as (Hrtbl_type & Hrtbl_len).
  destruct H15 as (Hgrp1 & Hgrp2).

  hoare lifts (2::3::4::5::6::7::8::9::10::11::12::13::14
                ::15::16::17::18::19::20::21::22::23::24::nil)%nat pre.
  rename i7 into ptcb_tcby.
  rename i6 into ptcb_bitx.

  assert (Htmp: xs = rdy).
  {
    clear -Hptcb_node Hrtbl_type Hrtbl_len Hif_ptcb_is_rdy1 Hif_ptcb_is_rdy2.
    eapply mutexpend_TCBNode_P_in_tcb_rdy; eauto.
  }
  assert (Htmp1: st = rdy).
  {
    clear -Hcurnode Hrtbl_type Hrtbl_len Hif_ptcb_is_rdy1 Hif_ptcb_is_rdy2.
    eapply mutexpend_TCBNode_P_in_tcb_rdy; eauto.
  }
  subst xs st.
(************************* cur_prio = mprio: err *************************)

  lzh_hoare_if.
  {
    rewrite mund_int_byte_max_unsigned.
    apply mund_int_a2.
    auto.
  }
  {
    eapply mund_val_inj_a0.
  }
  rename LHift_true into Hcur_prio_eql_mprio.
  {
    eapply mutex_pend_cur_prio_eql_mprio_left_to_cur; eauto.
  }

(*************************** cur_prio <> mprio ***************************)
  assert (Hnocur: Int.eq cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = false).
  {
    clear -Hif_false.
    rewrite Int.eq_sym.
    auto.
  }
  
  assert (H_cur_prio_scope: Int.unsigned cur_prio < 64).
  {
    clear -Hcurnode.
    unfold TCBNode_P in Hcurnode.
    mytac.
    invert H0.
    eapply tcbblk_prio_range.
    eauto.
    unfolds; simpl; auto.
  }  
  assert (Hx_scope1: Int.unsigned (x>>ᵢ$ 8) < 64).
  {
    clear -H_cur_prio_scope Hcur_prio.
    apply Int.ltu_inv in Hcur_prio.
    inversion Hcur_prio.
    inversion Hcur_prio.
    omega.
  }

(************************ ptcb need lift priority ************************)
  lzh_hoare_if.
  (* pure_auto. *)
  {
    clear -Fneq_i2_1.
    unfold Byte.max_unsigned.
    rewrite mund_int_byte_modulus.
    simpl.
    apply mund_int_a2; auto.
  }
  {
    eapply mund_val_inj_a0; auto.
  }
  {
    destruct (Int.eq ptcb_prio (x>>ᵢ$ 8)).
    unfold notint; unfold Int.notbool.
    unfold val_inj.
    rewrite Int.eq_false.
    pure_auto.
    pure_auto.
    unfold notint; unfold Int.notbool; unfold val_inj.
    rewrite Int.eq_true.
    pure_auto.
  }
  {
    clear -Fneq_i2_2.
    unfold Byte.max_unsigned;
      rewrite mund_int_byte_modulus; simpl.
    apply mund_int_a2; auto.
  }
  {
    eapply mund_val_inj_a0; auto.
  }
  {
    clear.
    destruct (Int.eq ptcb_prio (x>>ᵢ$ 8));
    destruct (Int.ltu cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8));
    unfold val_inj;
    unfold bool_and;
    unfold notint;
    unfold Int.notbool;
    try rewrite Int.eq_true;
    try rewrite Int.eq_false;
    try rewrite mund_ltu_a1;
    pure_auto.
  }
  instantiate (1:=Afalse).
  
  Focus 1.
  assert (Hif_can_lift: (ptcb_prio <> (Int.shru x ($ 8))) /\
                        (Int.ltu cur_prio (x &ᵢ ($ OS_MUTEX_KEEP_LOWER_8)) = true)).
  {
    clear -LHif_true.
    rename LHif_true into H.
    destruct (Int.eq ptcb_prio (x>>ᵢ$ 8)) eqn:F1;
    destruct (Int.ltu cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) eqn:F2;
    unfold val_inj in H;
    unfold bool_and in H;
    unfold notint in H;
    unfold Int.notbool in H;
    try rewrite Int.eq_true in H;
    try rewrite Int.eq_false in H;
    try rewrite mund_ltu_a1 in H;
    try rewrite mund_ltu_a2 in H;
    simpl in H;
    lzh_simpl_int_eq;
    pure_auto.
  }

  clear LHif_true.
(************************ pip is not held in ptbl ************************)
  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  destruct Hif_can_lift as (Hif_can_lift1 & Hif_can_lift2).
  rename v'31 into ptbl.
  destruct H9 as (Hptbl_1 & Hptbl_2).

  
  eapply seq_rule.
  eapply lzh_if_then_rule.
  intros.

  (* ** ac: Locate uop_rv. *)
  Require Import symbolic_lemmas.
  eapply uop_rv.
  eapply bop_rv.
  {
    sep_get_rv.
    {
      clear -Fneq_i2_1.
      unfold Byte.max_unsigned;
        rewrite mund_int_byte_modulus; simpl.
      apply mund_int_a2; auto.
    }
    {
      clear -Hptbl_1 Hptbl_2 Hx_scope1.
      eapply array_type_vallist_match_imp_rule_type_val_match.
      rewrite Hptbl_2.
(* apply intlt2nat in Hx_scope1. *)
      apply mund_to_nat_a1.
      auto.
      auto.
    }      
  }
  {
    (* ** ac: Locate PlaceHolder. *)
    Require Import os_mutex.
    unfold PlaceHolder.
    {
      eapply cast_rv_tptr.
      {
        eapply addrof_gvar_rv.
        eapply dom_lenv_imp_notin_lenv.
        2:sep cancel A_dom_lenv.
        auto.
        sep cancel Agvarenv'.
        exact_s.
      }        
      {
        pure_auto.
      }
    }      
  }
  eauto.
  {
    clear -Hptbl_1 Hptbl_2 Hx_scope1.    
    unfold bop_eval.
  

    lets H: mund_nth_val_a1 Hx_scope1 Hptbl_1 Hptbl_2.
    destruct H.
    destruct H as (v & H).
    rewrite H.
    unfold val_eq.
    destruct v; destruct v'51.
    destruct (peq b b0); destruct (Int.eq i i0);
    try rewrite Int.eq_true; try rewrite Int.eq_false;
    unfold val_inj; simpl; pure_auto.    
    rewrite H.
    unfold val_eq.
    destruct v'51.
    unfold val_inj; simpl; pure_auto.
  }
  {
    clear.
    unfold bop_type.
    eauto.
  }
  eauto.
  {
    clear -Hptbl_1 Hptbl_2 Hx_scope1.
    lets H: mund_nth_val_a1 Hx_scope1 Hptbl_1 Hptbl_2.
    destruct H as [(v&H) | H].
    rewrite H.
    unfold bop_eval.
    unfold val_eq.
    destruct v.
    destruct v'51.
    destruct (peq b b0); destruct (Int.eq i i0);
    try rewrite Int.eq_true; try rewrite Int.eq_false;
    unfold val_inj; simpl; pure_auto.

    rewrite H.
    unfold bop_eval.
    unfold val_eq.
    destruct v'51.
    unfold val_inj; simpl; pure_auto.
  }
  {
    clear.
    simpl.
    auto.
  }
  instantiate (1:=Afalse).
  Open Scope code_scope.
  lzh_split_first Hif_true.
  {
    eapply mutex_pend_pip_is_not_hold_left_to_cur; eauto.
  }
(****************************** pip is hold in ptbl ******************************)
  idtac.
  hoare forward.
  lzh_split_first H'.
  apply pfalse_rule.
  lzh_split_first H_pip_is_hold. 
  
  eapply seq_rule;[idtac|idtac].
  eapply forward_rule2;   [ idtac | first [ intros s H; exact H | sep pauto ] ].
  Open Scope list_scope.
  let s := fresh in
  let H := fresh in
  match goal with
  | |- {|_ , _, _, _, _, _|}|- ?ct {{?P}}?x ′ [_] =ₑ _ {{_}} =>
        match find_lvararray P x with
        | some ?m => idtac 
        | none _ =>match find_dom_lenv P with
            | (none _, _) => fail 2
            | (some ?m, Some ?ls) =>
                let ret1 := constr:(var_notin_dom x ls) in
                let ret2 := eval compute in ret1 in
                match ret2 with
                | true =>
                    match find_aop P with
                    | none _ => fail 1
                    | some ?n =>
                        match find_gvararray P x with
                        | none _ => fail 3
                        | some ?o =>
                            hoare lifts (n :: m :: o :: nil) pre;
                             eapply assign_rule_array_g_aop
                        end
                    end
                | false => fail
                end
            end
        end
  end.
  intros sss; split; intro HHH; exact HHH.
  simpl; pure_auto.
  unfold PlaceHolder.
  {
    intros.
    eapply cast_rv_tptr.
    {
      eapply addrof_gvar_rv.
      eapply dom_lenv_imp_notin_lenv.
      2:sep cancel A_dom_lenv.
      auto.
      sep cancel Agvarenv'.
      exact_s.
    }        
      unfold rule_type_val_match.
      auto.
  }      
  symbolic execution.
  (* pure_auto. *)
  struct_type_match_solver.
  auto.
  {
    unfold Z.of_nat.
    simpl.
    auto.
  }
  {
    (* ** ac: Locate assign_type_match_true. *)
    Import hoare_assign.
    apply assign_type_match_true.
    auto.
  }
  {
    rewrite Hptbl_2.
    auto.
  }
  intros.
  sep auto.
  Open Scope code_scope.
  idtac.
  hoare forward.
  {
    clear -Fneq_i2_1.
    rewrite mund_int_byte_max_unsigned.
    apply mund_int_a2.
    auto.
  }
  {
    clear -Hx_scope1.
    unfold Z.of_nat.
    simpl.
    auto.
  }
  {
    rewrite update_nth_val_len_eq.
    clear -Hx_scope1 Hptbl_2.
    rewrite Hptbl_2.
    unfold Z.of_nat; simpl.
    auto.
  }
(*********************** ptcb lift actions perform ***********************)

  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  hoare_split_pure_all.
  clear H9 H51.
  rename H50 into H_os_grp_type.

  assert (Htmp: ptcb_tcby = (ptcb_prio >>ᵢ$ 3) /\
                ptcb_bitx = ($ 1) <<ᵢ (ptcb_prio &ᵢ ($ 7))).
  {
    clear -Hptcb_blk.
    unfold RL_TCBblk_P in Hptcb_blk.
    mytac_H.
    inverts H11; inverts H1; inverts H3; inverts H2.
    inverts H0; inverts H4; inverts H.
    auto.
  }
  destruct Htmp as (Hptcb_tcby & Hptcb_bitx).
  
  lets Hptcb_tcby_scope: post_intlemma3 Hptcb_prio_scope.

  eapply mutex_pend_ptcb_is_rdy_left_to_cur with
    (tcbls_l:=tcbls_l)
    (tcbls_r:=tcbls_r)
    (tcbls_sub_l:=tcbls_sub_l)
    (tcbls_sub_r:=tcbls_sub_r)
    (v'19:=v'19)
    (v'21:=(cur_addr, Int.zero))
    (v'48:=v'46)
    (v'28:=v'27)
    (v'30:=v'29)
    (v'50:=v'48)
    (v'49:=v'47)
    (v'51:=v'49)
    (wls:=wls)
    (x2:=x2)
    (st:=rdy)
    (xs:=rdy)
    (v'52:=v'52); auto.
  {
    subst.
    clear -H_pip_is_hold.
    generalize H_pip_is_hold.
    clear H_pip_is_hold.
    unfold bop_eval.
    remember (nth_val' (Z.to_nat (Int.unsigned (x>>ᵢ$ 8))) ptbl).
    destruct v; unfold val_eq; unfold val_inj; simpl;
    try (intros H; destruct H; tryfalse).
    destruct v'51;
    unfold notint in H;
    unfold Int.notbool in H;
    try rewrite Int.eq_true in H;
      try rewrite Int.eq_false in H;
      tryfalse.

    destruct v'51;
    unfold notint in H;
    unfold Int.notbool in H;
    try rewrite Int.eq_true in H;
      try rewrite Int.eq_false in H;
      tryfalse.

    destruct a;
    destruct v'51;
    destruct (Int.eq i i0) eqn: F1;
    destruct (peq b b0) eqn: F2; 
    unfold notint in H;
    unfold Int.notbool in H;
    try rewrite Int.eq_true in H;
      try rewrite Int.eq_false in H;
      tryfalse.

    lzh_simpl_int_eq.
    subst.
    
    subst; reflexivity.
    pure_auto.

    destruct a;
    destruct v'51;
    destruct (Int.eq i i0) eqn: F1;
    destruct (peq b b0) eqn: F2; 
    unfold notint in H;
    unfold Int.notbool in H;
    try rewrite Int.eq_true in H;
      try rewrite Int.eq_false in H;
      tryfalse.
  }
  {
    assert (Fptcb_is_rdy: prio_in_tbl ptcb_prio os_rdy_tbl).
    {
      clear -Hptcb_stat.
      rename Hptcb_stat into H.
      unfold R_TCB_Status_P in H.
      destruct H as (_ & H & _).
      unfold RHL_RdyI_P in H.
      lets H': H ptcb_prio xm.
      assert (Htmp: (ptcb_prio, rdy, xm) = (ptcb_prio, rdy, xm)) by auto.
      apply H' in Htmp.
      mytac.
      clear H.
      clear H'.
      inverts H1; inverts H2.
      unfold RdyTCBblk in H0.
      mytac.
    }

    assert (Htmp: exists v, (nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl)= Some (Vint32 v)).
    {
      clear -Hptcb_tcby_scope Hptcb_tcby Hrtbl_len Hrtbl_type.
      subst.
      remember (Int.unsigned (ptcb_prio>>ᵢ$ 3)).
      assert (Htmp: (0 <= (Z.to_nat z) < 8)%nat).
      {
        subst.
        apply nat_8_range_conver.
        auto.
      }
      unfold OS_RDY_TBL_SIZE in *.
      clear Heqz.
      lets H: n07_arr_len_ex Htmp Hrtbl_type Hrtbl_len.
      mytac.
    }

    clear - Hptcb_prio_scope Hptcb_prio_scope_obv Htmp Fptcb_is_rdy Hptcb_tcby Hptcb_bitx.
    rename Fptcb_is_rdy into H.
    unfold prio_in_tbl in H.
    destruct Htmp as (v & Hnth_val).
    remember (ptcb_prio &ᵢ$ 7).
    lets H': H i ptcb_tcby v. 
    clear H.
    subst.
    lets H: H' Hnth_val; auto.
    clear H'.
    apply nth_val_nth_val'_some_eq in Hnth_val.
    rewrite Hnth_val.
    remember ($ 1<<ᵢ(ptcb_prio&ᵢ$ 7)).
    assert (i <> $0).
    {
      subst.
      eapply math_prop_neq_zero2.
      omega.
    }
    clear Heqi.

    unfold and.
    rewrite H.
    unfold val_inj.
    unfold val_eq.
    destruct (Int.eq i ($ 0)) eqn:F.
    lzh_simpl_int_eq; tryfalse.
    left; auto.
  }
  Unfocus.
(************************ need not lift priority ************************)
  Focus 1.
  instantiate (1:=Afalse).

  idtac.

  eapply mutex_pend_can_not_lift_left_to_cur with
    (tcbls_l:=tcbls_l)
    (tcbls_r:=tcbls_r)
    (tcbls_sub_l:=tcbls_sub_l)
    (tcbls_sub_r:=tcbls_sub_r)
    (v'19:=v'19)
    (v'21:=(cur_addr, Int.zero))
    (v'48:=v'46)
    (v'28:=v'27)
    (v'30:=v'29)
    (v'50:=v'48)
    (v'49:=v'47)
    (v'51:=v'49)
    (wls:=wls)
    (x2:=x2)
    (v'52:=v'52); auto.
  exact rdy.

(****************** ptcb is left to cur: some tail work ******************)
  clear.
  intros.
  (* ** ac: Locate DisjPropE. *)
Theorem DisjPropE :
  forall P Q s,
    (s |= P \\// Q) -> s |= P \/ s |= Q.
Proof.
  intros.
  simpl in H.
  auto.
Qed.

  eapply DisjPropE in H.
  destruct H.
  apply astar_comm in H.
  eapply astar_l_afalse_elim; eauto.
  apply astar_comm in H.
  eapply astar_l_afalse_elim; eauto.

(********************************** *** **********************************)
(********************************** *** **********************************)
(********************************** *** **********************************)
(************************* ptcb is right to cur *************************)

  idtac.
  rename x2 into tcbls_r'.
  assert (Htmp: TcbMod.get tcbls_r' ptcb_tid = Some (ptcb_prio, xs, xm)).
  {
    clear - H_ptcb_in_right Htcbjoin_right H_ptcb_not_cur.
    unfold TcbJoin in *.
    assert (H0: TcbMod.get (TcbMod.sig (cur_addr, Int.zero) (cur_prio, st, Vnull))
                           ptcb_tid 
                  = None).
    {
      eapply TcbMod.get_sig_none.
      auto.
    }
    lets H: TcbMod.join_get_or Htcbjoin_right H_ptcb_in_right.
    destruct H.
    unfold sig in H; simpl in H.
    rewrite H0 in H.
    tryfalse.
    auto.
  }  
  clear H_ptcb_in_right.
  rename Htmp into H_ptcb_in_right.

  
  eapply backward_rule1.
  intros.
  sep lift 6%nat in H9.
  eapply lzh_tcb_list_split.
  unfold tcbdllseg.
  sep cancel dllseg.
  exact_s.
  eapply H_ptcb_in_right. 
  eauto.
  hoare_split_pure_all.
  inverts H9; inverts H30.
  rename H17 into Hget_last_tcb.
  clear H46 H9.

  rename H33 into Hptcb_node.
  rename H44 into Htcblist_sub_left.
  rename H45 into Htcblist_sub_right.

  rename H31 into Htcbjoin_sub_whole.
  rename H32 into Htcbjoin_sub_right.
  rename v'50 into tcbls_sub_l.
  rename v'53 into tcbls_sub_r.
  (** info: tcbls_sub_l ++ ptcb_node ++ tcbls_sub_r = tcbls_r' **)

  hoare_unfold.
  rename v'36 into ptcb_addr.

  remember Hptcb_node as Hptcb_node'.
  clear HeqHptcb_node'.
  unfold TCBNode_P in Hptcb_node'.
  destruct Hptcb_node' as (Ht1 & Ht2 & Hptcb_blk & Hptcb_stat).
  inverts Ht1; inverts Ht2.
(*************************** split tcblist end ***************************)
(*************************** ptcb_prio == idle : err ***************************)
  lzh_hoare_if.
  (* pure_auto. *)
  eapply mund_val_inj_a0; auto.
  {
    eapply mutex_pend_ptcb_is_idle_err_right_to_cur; eauto. 
  }
(************************** ptcb_prio != idle : err **************************)
  assert (Hptcb_prio_not_idle:ptcb_prio <> ($ OS_IDLE_PRIO)).
  {
    clear - Hif_false.
    lzh_simpl_int_eq.
    auto.
  }
  clear Hif_false.
  
  

  assert (Hptcb_prio_scope: 0 <= Int.unsigned ptcb_prio < 64).
  {
    clear -Hptcb_blk.
    unfold RL_TCBblk_P in Hptcb_blk.
    mytac_H.
    inverts H11; inverts H1; inverts H3; inverts H2.
    inverts H0; inverts H4; inverts H.
    auto.
  }
  destruct Hptcb_prio_scope as (Hptcb_prio_scope_obv & Hptcb_prio_scope).
  rename i10 into ptcb_stat.
(*************************** ptcb not rdy: err ***************************)

  lzh_hoare_if.
  (* pure_auto. *)
  {
    apply mund_val_inj_a0.
  }
  {
    clear.
    destruct (Int.eq ptcb_stat ($ OS_STAT_RDY)).
    unfold val_inj.
    unfold notint.
    unfold Int.notbool.
    rewrite Int.eq_false.
    pure_auto.
    pure_auto.
    unfold val_inj.
    unfold notint.
    unfold Int.notbool.
    rewrite Int.eq_true.
    pure_auto.
  }
  (* pure_auto. *)
  {
    apply mund_val_inj_a0.
  }
  {
    clear.
    destruct (Int.eq i11 ($ 0)).
    unfold val_inj.
    unfold notint.
    unfold Int.notbool.
    rewrite Int.eq_false.
    pure_auto.
    pure_auto.
    unfold val_inj.
    unfold notint.
    unfold Int.notbool.
    rewrite Int.eq_true.
    pure_auto.
  }
  {
    clear.
    destruct (Int.eq ptcb_stat ($ OS_STAT_RDY));
      destruct (Int.eq i11 ($ 0));
      unfold val_inj;
      unfold notint;
      unfold Int.notbool;
      try rewrite Int.eq_true;
      try rewrite Int.eq_false; pure_auto.
  }
  
  assert (Hif_ptcb_is_not_rdy:
            (ptcb_stat <> ($ OS_STAT_RDY)) \/
            (i11 <> ($ 0))).
  {
    clear -LHift_true.
    rename LHift_true into H.

    destruct (Int.eq ptcb_stat ($ OS_STAT_RDY)) eqn: F1;
      destruct (Int.eq i11 ($ 0)) eqn: F2;
      unfold val_inj in H;
      unfold notint in H;
      unfold Int.notbool in H;
      unfold bool_or in H;
      try rewrite Int.eq_true in H;
      try rewrite mund_ltu_a1 in H;
      try rewrite mund_ltu_a2 in H;
      simpl in H.
    rewrite Int.eq_false in H.
    rewrite mund_ltu_a1 in H.
    simpl in H.
    destruct H; tryfalse.
    pure_auto.

    rewrite Int.eq_false in H.
    rewrite mund_ltu_a1 in H.
    simpl in H.
    destruct H; tryfalse.
    lzh_simpl_int_eq.
    right.
    pure_auto.
    pure_auto.
    
    lzh_simpl_int_eq.
    left.
    pure_auto.

    lzh_simpl_int_eq.
    left; pure_auto.
  }
            
  clear LHift_true.

  {
    eapply mutex_pend_ptcb_is_not_rdy_right_to_cur; eauto. 
  }

(***************************** ptcb is ready *****************************)
  assert (Hif_ptcb_is_rdy:
            (ptcb_stat = ($ OS_STAT_RDY)) /\
            (i11 = ($ 0))).
  {
    clear - Hif_false.
    rename Hif_false into H.
    
    destruct (Int.eq ptcb_stat ($ OS_STAT_RDY)) eqn: F1;
      destruct (Int.eq i11 ($ 0)) eqn: F2;
      unfold val_inj in H;
      unfold notint in H;
      unfold Int.notbool in H;
      unfold bool_or in H;
      try rewrite Int.eq_true in H;
      try rewrite mund_ltu_a1 in H;
      try rewrite mund_ltu_a2 in H;
      simpl in H;
      lzh_simpl_int_eq.

    pure_auto.
    rewrite Int.eq_false in H.
    rewrite mund_ltu_a1 in H.
    simpl in H.
    destruct H; tryfalse.
    pure_auto.

    destruct H; tryfalse.
    destruct H; tryfalse.
  }

  clear Hif_false.
  destruct Hif_ptcb_is_rdy as (Hif_ptcb_is_rdy1 & Hif_ptcb_is_rdy2).
  
  hoare lift 24%nat pre.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.

  
  transform_pre AOSRdyTblGrp_fold ltac:(sep cancel GAarray;
                                        sep cancel AOSRdyGrp).
  rename v'37 into os_rdy_tbl.
  destruct H9 as (Hrtbl_type & Hrtbl_len).
  destruct H15 as (Hgrp1 & Hgrp2).

  hoare lifts (2::3::4::5::6::7::8::9::10::11::12::13::14
                ::15::16::17::18::19::20::21::22::23::24::nil)%nat pre.
  rename i7 into ptcb_tcby.
  rename i6 into ptcb_bitx.

  assert (Htmp: xs = rdy).
  {
    clear -Hptcb_node Hrtbl_type Hrtbl_len Hif_ptcb_is_rdy1 Hif_ptcb_is_rdy2.
    eapply mutexpend_TCBNode_P_in_tcb_rdy; eauto.
  }
  assert (Htmp1: st = rdy).
  {
    clear -Hcurnode Hrtbl_type Hrtbl_len Hif_ptcb_is_rdy1 Hif_ptcb_is_rdy2.
    eapply mutexpend_TCBNode_P_in_tcb_rdy; eauto.
  }
  subst xs st.
(************************* cur_prio = mprio: err *************************)

  lzh_hoare_if.
  {
    rewrite mund_int_byte_max_unsigned.
    apply mund_int_a2.
    auto.
  }
  {
    eapply mund_val_inj_a0.
  }
  rename LHift_true into Hcur_prio_eql_mprio.
  {
    apply mutex_pend_cur_prio_eql_mprio_right_to_cur with
      (v'19:=v'19)
      (v'49:=v'49)
      (v'51:=v'51)
      (v'47:=v'47)
      (v'48:=v'48)
      (wls:=wls)
      (tcbls_l:=tcbls_l)
      (tcbls_r:=tcbls_r)
      (tcbls_r':=tcbls_r')
      (tcbls_sub_l:=tcbls_sub_l)
      (v'52:=v'52)
      (tcbls_sub_r:=tcbls_sub_r); auto.
  }

(*************************** cur_prio <> mprio ***************************)
  assert (Hnocur: Int.eq cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = false).
  {
    clear -Hif_false.
    rewrite Int.eq_sym.
    auto.
  }
  
  assert (H_cur_prio_scope: Int.unsigned cur_prio < 64).
  {
    clear -Hcurnode.
    unfold TCBNode_P in Hcurnode.
    mytac.
    invert H0.
    eapply tcbblk_prio_range.
    eauto.
    unfolds; simpl; auto.
  }  
  assert (Hx_scope1: Int.unsigned (x>>ᵢ$ 8) < 64).
  {
    clear -H_cur_prio_scope Hcur_prio.
    apply Int.ltu_inv in Hcur_prio.
    inversion Hcur_prio.
    inversion Hcur_prio.
    omega.
  }

(************************ ptcb need lift priority ************************)
  lzh_hoare_if.
  (* pure_auto. *)
  {
    clear -Fneq_i2_1.
    unfold Byte.max_unsigned.
    rewrite mund_int_byte_modulus.
    simpl.
    apply mund_int_a2; auto.
  }
  {
    eapply mund_val_inj_a0; auto.
  }
  {
    destruct (Int.eq ptcb_prio (x>>ᵢ$ 8)).
    unfold notint; unfold Int.notbool.
    unfold val_inj.
    rewrite Int.eq_false.
    pure_auto.
    pure_auto.
    unfold notint; unfold Int.notbool; unfold val_inj.
    rewrite Int.eq_true.
    pure_auto.
  }
  {
    clear -Fneq_i2_2.
    unfold Byte.max_unsigned;
      rewrite mund_int_byte_modulus; simpl.
    apply mund_int_a2; pure_auto.
  }
  {
    eapply mund_val_inj_a0; auto.
  }
  {
    clear.
    destruct (Int.eq ptcb_prio (x>>ᵢ$ 8));
    destruct (Int.ltu cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8));
    unfold val_inj;
    unfold bool_and;
    unfold notint;
    unfold Int.notbool;
    try rewrite Int.eq_true;
    try rewrite Int.eq_false;
    try rewrite mund_ltu_a1;
    pure_auto.
  }
  instantiate (1:=Afalse).
  
  Focus 1.
  assert (Hif_can_lift: (ptcb_prio <> (Int.shru x ($ 8))) /\
                        (Int.ltu cur_prio (x &ᵢ ($ OS_MUTEX_KEEP_LOWER_8)) = true)).
  {
    clear -LHif_true.
    rename LHif_true into H.
    destruct (Int.eq ptcb_prio (x>>ᵢ$ 8)) eqn:F1;
    destruct (Int.ltu cur_prio (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) eqn:F2;
    unfold val_inj in H;
    unfold bool_and in H;
    unfold notint in H;
    unfold Int.notbool in H;
    try rewrite Int.eq_true in H;
    try rewrite Int.eq_false in H;
    try rewrite mund_ltu_a1 in H;
    try rewrite mund_ltu_a2 in H;
    simpl in H;
    lzh_simpl_int_eq;
    pure_auto.
  }
  clear LHif_true.
(************************ pip is not held in ptbl ************************)
  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  destruct Hif_can_lift as (Hif_can_lift1 & Hif_can_lift2).
  rename v'31 into ptbl.
  destruct H9 as (Hptbl_1 & Hptbl_2).

  
  eapply seq_rule.
  eapply lzh_if_then_rule.
  intros.

  eapply uop_rv.
  eapply bop_rv.
  {
    sep_get_rv.
    {
      clear -Fneq_i2_1.
      unfold Byte.max_unsigned;
        rewrite mund_int_byte_modulus; simpl.
      apply mund_int_a2; auto.
    }
    {
      clear -Hptbl_1 Hptbl_2 Hx_scope1.
      eapply array_type_vallist_match_imp_rule_type_val_match.
      rewrite Hptbl_2.
      apply mund_to_nat_a1.
      auto.
      auto.
    }      
  }
  {
    unfold PlaceHolder.
    {
      eapply cast_rv_tptr.
      {
        eapply addrof_gvar_rv.
        eapply dom_lenv_imp_notin_lenv.
        2:sep cancel A_dom_lenv.
        auto.
        sep cancel Agvarenv'.
        exact_s.
      }        
      {
        pure_auto.
      }
    }      
  }
  eauto.
  {
    clear -Hptbl_1 Hptbl_2 Hx_scope1.    
    unfold bop_eval.

    idtac.
    lets H: mund_nth_val_a1 Hx_scope1 Hptbl_1 Hptbl_2.
    destruct H.
    destruct H as (v & H).
    rewrite H.
    unfold val_eq.
    destruct v; destruct v'51.
    destruct (peq b b0); destruct (Int.eq i i0);
    try rewrite Int.eq_true; try rewrite Int.eq_false;
    unfold val_inj; simpl; pure_auto.    
    rewrite H.
    unfold val_eq.
    destruct v'51.
    unfold val_inj; simpl; pure_auto.
  }
  {
    clear.
    unfold bop_type.
    eauto.
  }
  eauto.
  {
    clear -Hptbl_1 Hptbl_2 Hx_scope1.
    lets H: mund_nth_val_a1 Hx_scope1 Hptbl_1 Hptbl_2.
    destruct H as [(v&H) | H].
    rewrite H.
    unfold bop_eval.
    unfold val_eq.
    destruct v.
    destruct v'51.
    destruct (peq b b0); destruct (Int.eq i i0);
    try rewrite Int.eq_true; try rewrite Int.eq_false;
    unfold val_inj; simpl; pure_auto.

    rewrite H.
    unfold bop_eval.
    unfold val_eq.
    destruct v'51.
    unfold val_inj; simpl; pure_auto.
  }
  {
    clear.
    simpl.
    auto.
  }
  instantiate (1:=Afalse).
  lzh_split_first Hif_true.
  {
    eapply mutex_pend_pip_is_not_hold_right_to_cur with
      (v'19:=v'19)
      (v'49:=v'49)
      (v'48:=v'48)
      (v'51:=v'51)
      (v'47:=v'47)
      (wls:=wls)
      (tcbls_l:=tcbls_l)
      (tcbls_r:=tcbls_r)
      (tcbls_r':=tcbls_r')
      (tcbls_sub_l:=tcbls_sub_l)
      (v'52:=v'52)
      (tcbls_sub_r:=tcbls_sub_r); auto.
  }
(****************************** pip is hold in ptbl ******************************)
  hoare forward.
  lzh_split_first H'.
  apply pfalse_rule.
  lzh_split_first H_pip_is_hold. 
  
  eapply seq_rule;[idtac|idtac].
  eapply forward_rule2;   [ idtac | first [ intros s H; exact H | sep pauto ] ].
  let s := fresh in
  let H := fresh in
  match goal with
  | |- {|_ , _, _, _, _, _|}|- ?ct {{?P}}?x ′ [_] =ₑ _ {{_}} =>
        match find_lvararray P x with
        | some ?m => idtac 
        | none _ =>match find_dom_lenv P with
            | (none _, _) => fail 2
            | (some ?m, Some ?ls) =>
                let ret1 := constr:(var_notin_dom x ls) in
                let ret2 := eval compute in ret1 in
                match ret2 with
                | true =>
                    match find_aop P with
                    | none _ => fail 1
                    | some ?n =>
                        match find_gvararray P x with
                        | none _ => fail 3
                        | some ?o =>
                            hoare lifts (n :: m :: o :: nil) pre;
                             eapply assign_rule_array_g_aop
                        end
                    end
                | false => fail
                end
            end
        end
  end.
  intros sss; split; intro HHH; exact HHH.
  simpl; auto.
  unfold PlaceHolder.
  {
    intros.
    eapply cast_rv_tptr.
    {
      eapply addrof_gvar_rv.
      eapply dom_lenv_imp_notin_lenv.
      2:sep cancel A_dom_lenv.
      auto.
      sep cancel Agvarenv'.
      exact_s.
    }        
      unfold rule_type_val_match.
      auto.
  }      
  symbolic execution.
  (* pure_auto. *)
  struct_type_match_solver.
  auto.
  {
    unfold Z.of_nat.
    simpl.
    auto.
  }
  {
    apply assign_type_match_true.
    auto.
  }
  {
    rewrite Hptbl_2.
    auto.
  }
  intros.
  sep auto.
  hoare forward.
  {
    clear -Fneq_i2_1.
    rewrite mund_int_byte_max_unsigned.
    apply mund_int_a2.
    auto.
  }
  {
    clear -Hx_scope1.
    unfold Z.of_nat.
    simpl.
    auto.
  }
  {
    rewrite update_nth_val_len_eq.
    clear -Hx_scope1 Hptbl_2.
    rewrite Hptbl_2.
    unfold Z.of_nat; simpl.
    auto.
  }
(*********************** ptcb lift actions perform ***********************)
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  hoare_split_pure_all.
  clear H9 H51.
  rename H50 into H_os_grp_type.
  
  assert (Htmp: ptcb_tcby = (ptcb_prio >>ᵢ$ 3) /\
                ptcb_bitx = ($ 1) <<ᵢ (ptcb_prio &ᵢ ($ 7))).
  {
    clear -Hptcb_blk.
    unfold RL_TCBblk_P in Hptcb_blk.
    mytac_H.
    inverts H11; inverts H1; inverts H3; inverts H2.
    inverts H0; inverts H4; inverts H.
    auto.
  }
  destruct Htmp as (Hptcb_tcby & Hptcb_bitx).
  lets Hptcb_tcby_scope: post_intlemma3 Hptcb_prio_scope.
  
  eapply mutex_pend_ptcb_is_rdy_right_to_cur with
    (tcbls_l:=tcbls_l)
    (tcbls_r:=tcbls_r)
    (tcbls_r':=tcbls_r')
    (tcbls_sub_l:=tcbls_sub_l)
    (tcbls_sub_r:=tcbls_sub_r)
    (v'19:=v'19)
    (v'21:=(cur_addr, Int.zero))
    (v'49:=v'47)
    (v'50:=v'48)
    (v'51:=v'49)
    (wls:=wls)
    (v'52:=v'52); auto.
  {
    assert (Fptcb_is_rdy: prio_in_tbl ptcb_prio os_rdy_tbl).
    {
      clear -Hptcb_stat.
      rename Hptcb_stat into H.
      unfold R_TCB_Status_P in H.
      destruct H as (_ & H & _).
      unfold RHL_RdyI_P in H.
      lets H': H ptcb_prio xm.
      assert (Htmp: (ptcb_prio, rdy, xm) = (ptcb_prio, rdy, xm)) by auto.
      apply H' in Htmp.
      mytac.
      clear H.
      clear H'.
      inverts H1; inverts H2.
      unfold RdyTCBblk in H0.
      mytac.
    }

    assert (Htmp: exists v, (nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl)= Some (Vint32 v)).
    {
      clear -Hptcb_tcby_scope Hptcb_tcby Hrtbl_len Hrtbl_type.
      subst.
      remember (Int.unsigned (ptcb_prio>>ᵢ$ 3)).
      assert (Htmp: (0 <= (Z.to_nat z) < 8)%nat).
      {
        subst.
        apply nat_8_range_conver.
        auto.
      }
      unfold OS_RDY_TBL_SIZE in *.
      clear Heqz.
      lets H: n07_arr_len_ex Htmp Hrtbl_type Hrtbl_len.
      mytac.
    }

    clear - Hptcb_prio_scope Hptcb_prio_scope_obv Htmp Fptcb_is_rdy Hptcb_tcby Hptcb_bitx.
    rename Fptcb_is_rdy into H.
    unfold prio_in_tbl in H.
    destruct Htmp as (v & Hnth_val).
    remember (ptcb_prio &ᵢ$ 7).
    lets H': H i ptcb_tcby v. 
    clear H.
    subst.
    lets H: H' Hnth_val; auto.
    clear H'.
    apply nth_val_nth_val'_some_eq in Hnth_val.
    rewrite Hnth_val.
    remember ($ 1<<ᵢ(ptcb_prio&ᵢ$ 7)).
    assert (i <> $0).
    {
      subst.
      eapply math_prop_neq_zero2.
      omega.
    }
    clear Heqi.

    unfold and.
    rewrite H.
    unfold val_inj.
    unfold val_eq.
    destruct (Int.eq i ($ 0)) eqn:F.
    lzh_simpl_int_eq; tryfalse.
    left; auto.
  }

  Unfocus.
(************************ need not lift priority ************************)
  Focus 1.
  instantiate (1:=Afalse).

  eapply mutex_pend_can_not_lift_right_to_cur with
    (tcbls_l:=tcbls_l)
    (tcbls_r:=tcbls_r)
    (tcbls_r':=tcbls_r')
    (tcbls_sub_l:=tcbls_sub_l)
    (tcbls_sub_r:=tcbls_sub_r)
    (v'19:=v'19)
    (v'21:=(cur_addr, Int.zero))
    (v'49:=v'47)
    (v'50:=v'48)
    (v'51:=v'49)
    (wls:=wls)
    (v'52:=v'52); auto.
(****************** ptcb is right to cur: some tail work ******************)
  clear.
  intros.
  eapply DisjPropE in H.
  destruct H.
  apply astar_comm in H.
  eapply astar_l_afalse_elim; eauto.
  apply astar_comm in H.
  eapply astar_l_afalse_elim; eauto.

Qed.


Theorem OSMutexPendProof: 
  forall tid vl p r,
    Some p =
    BuildPreA' os_api OSMutexPend
               mutexpendapi vl OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api OSMutexPend
               mutexpendapi  vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSMutexPend = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |- tid {{ p }} s {{ Afalse }}.
Proof.
  init_spec.

(************************ pevent == Null **************************************)
  lzh_hoare_if.
  pure_auto. pure_auto.
  assert (Hval: x0 = Vnull).
  {
    auto.
  }
  subst.
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_null_return.
  can_change_aop_solver.
  unfold tl_vl_match; unfold type_val_match; pure_auto.
  hoare forward.
(******************** pevent == Null finished ******************************)
  hoare forward prim.
  lzh_val_inj_simpl.
  hoare_unfold.
  hoare forward.

  sep cancel Aie.
  sep cancel Ais.
  sep cancel Aisr.
  sep cancel Acs.
  sep cancel tcbdllflag.
  sep cancel AECBList.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBList.
  sep cancel AOSTCBPrioTbl.
  sep pauto.
  pure_auto.
  pure_auto.
  
  apply retpost_osev.
  sep pauto.
  sep destruct H3.
  apply adisj_elim in H3.
  destruct H3.
  sep auto.
  sep auto.

  intros.
  sep auto.
  
  hoare_split_pure_all.
  unfold OS_EventSearchPost.
  unfold OS_EventSearchPost'.
  unfold getasrt. (* getasrt is meaning of notation PRE *)
  eapply backward_rule1.
  intros.
  eapply disj_star_elim; eauto.
  (** PS: 由于os_eventsearch(pevent)可能找到，也可能找不到，所以，这里就天然的要分成两种情况 *)
  hoare forward.
  
(*********************************** legal == 0 *****************************)
  
  Focus 2. (* proof legal == 0 branch first *)
  hoare_split_pure_all.
  destruct H6. inverts H6.
  inverts H5.
  lzh_inverts_logic.
  lzh_hoare_if.
  pure_auto.
  
  hoare abscsq.
  auto.
  eapply absinfer_mbox_pend_p_not_legal_return; pure_auto.

  hoare forward prim.
  sep pauto.
  pure_auto.
  hoare forward.
  
  lzh_val_inj_simpl. tryfalse.
(******************************legal = 0 finished *************************)  
(****************************** legal = 1 *********************************)
  hoare_split_pure_all.
  inverts H11; destruct H8; inverts H16; inverts H17.
  subst.
  lzh_hoare_if.
  pure_auto.
  lzh_val_inj_simpl. tryfalse.

  clear Hif_false.
  lets Hget: eventsearch_after_get_H H3 H4 H11 H8; eauto.
(**************************** type != mutex ****************************)
  hoare_unfold.
  lzh_hoare_if.
  pure_auto. pure_auto.
  pure_auto.
  
  assert (i1 <> ($ OS_EVENT_TYPE_MUTEX)).
  {
    clear -LHift_true.
    lzh_simpl_int_eq.
    auto.
  }
  clear LHift_true.

  transform_pre mutex_eventtype_neq_mutex ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  hoare abscsq.
  auto.
  
  eapply absinfer_mutex_pend_wrong_type_return; pure_auto.

  (*********  exit critical ***********)
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  sep pauto.
  pure_auto.
  hoare forward.
(************************ type != mutex finished ************************)
(***************************** type == mutex *****************************)
  lzh_val_inj_simpl.
  lzh_simpl_int_eq.
  subst.

  transform_pre mutex_triangle ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  mytac_H.

  hoare_unfold.

  lets Ftcbnode: TCBList_imp_TCBNode H32.
(*  destruct Ftcbnode as [abstcb [HCurnode [Hgetcur [st Htmp]]]]. *)
  destruct Ftcbnode as (abstcb & Hcurnode & Hgetcur_subr & st & Htmp ).
  subst.
  lets Hgetcur: TcbMod.join_get_r Hgetcur_subr; eauto.

(**************************** curtid == idle ****************************)
  lzh_hoare_if.
  pure_auto.
  

  assert (i6 = ($ OS_IDLE_PRIO)).
  {
    clear -LHift_true.
    lzh_simpl_int_eq.
    auto.
  }
  clear LHift_true.
  subst.

  hoare lift 7%nat pre. 
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.
  
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_from_idle_return.
  can_change_aop_solver.
  auto.
  do 2 eexists; eauto.

  hoare forward prim.
  
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  split; auto.
  struct_type_match_solver.

  eauto.
  eauto.
  eauto.
  pure_auto.

  hoare forward.
(************************** cur = idle finished **************************)
(****************************** cur <> idle ******************************)

(************************* OSTCBCur is not ready *************************)
  idtac.
  lzh_val_inj_simpl.
  rename Hif_false into Hneq_idle.
  lzh_hoare_if.
  pure_auto. pure_auto. pure_auto. pure_auto. pure_auto.
  assert (Heq: Int.eq i7 ($ OS_STAT_RDY) = false \/
               Int.eq i8 ($ 0) = false).
  {
    clear -LHift_true.
    destruct (Int.eq i7 ($ OS_STAT_RDY)). 
    destruct (Int.eq i8 ($ 0)). 
    mytac.
    simpl in H.
    unfold Int.notbool in H.
    rewrite Int.eq_false in H; int auto.
    simpl in H. tryfalse.
    auto. auto.
  }
  clear LHift_true.
  
  unfold TCBNode_P in Hcurnode.
  destruct Hcurnode as (_&_&_& Htemp).

  Require Import Mbox_common.
  lets Hnrdy: r_tcb_status_p_nrdy Htemp Heq.
  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_not_ready_return; eauto.
  can_change_aop_solver.

  hoare lift 12%nat pre. 
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  (***** ex critical ****)

  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  split; auto.
  struct_type_match_solver.
  eauto.
  eauto.
  eauto.
  pure_auto.
  hoare forward.
(******************** OSTCBCur is not ready finished ********************)
(************************** OSTCBCur is ready  **************************)
  idtac.
  assert (Heq: Int.eq i7 ($ OS_STAT_RDY) = true
               /\ Int.eq i8 ($ 0) = true).
  {
    clear -Hif_false.
    generalize Hif_false.
    clear Hif_false.
    destruct (Int.eq i7 ($ OS_STAT_RDY)) eqn:F1;
      destruct (Int.eq i8 ($ 0)) eqn:F2;
      unfold val_inj;
      unfold notint;
      unfold Int.notbool;
      unfold bool_or;
      try rewrite Int.eq_true;
      try rewrite Int.eq_false;
      try rewrite mund_ltu_a1;
      try rewrite mund_ltu_a2;
      simpl.
    intro H; destruct H; tryfalse; auto.
    pure_auto.
    intro H; destruct H; tryfalse; auto.
    pure_auto.
    intro H; destruct H; tryfalse; auto.
    pure_auto.
    intro H; destruct H; tryfalse; auto.
  }
  clear Hif_false.
  inverts Heq.
  lzh_simpl_int_eq.
  subst.
(****************** msg != Null: for timeout situation ******************)
  lzh_hoare_if.
  {
    clear -H36.
    unfold isptr in H36.
    destruct H36. subst.
    unfold val_eq; unfold val_inj.
    pure_auto.
    mytac.
    unfold val_eq; unfold val_inj;auto.
    destruct x.
    pure_auto.
  }
  {
    clear -H36;
    unfold isptr in H36.
    destruct H36; mytac;
    unfold val_eq; unfold val_inj; unfold notint;
    unfold Int.notbool.
    (* pure_auto. *)
    destruct x.
    rewrite Int.eq_true.
    pure_auto.
  }

  assert (x11 <> Vnull).
  {
    clear - H36 LHift_true.
    generalize LHift_true.
    clear LHift_true.
    unfold isptr in H36.
    destruct H36 as [H | (p & H)];
      [ subst
      | destruct p; subst ];
      unfold val_eq;
      unfold val_inj;
      unfold notint; unfold Int.notbool;
      try rewrite Int.eq_true in *;
      try rewrite Int.eq_false in *.
    intro H; destruct H; tryfalse.
    pure_auto.
    intro H; destruct H; tryfalse.
    pure_auto.
  }
  clear LHift_true.

  hoare abscsq.
  auto.
  eapply absinfer_mutex_pend_msg_not_null_return; eauto.
  can_change_aop_solver.
  
  hoare lift 12%nat pre. 
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare forward prim.
  (***** ex critical ****)

  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  split; auto.
  struct_type_match_solver.
  eauto.
  eauto.
  eauto.
  pure_auto.
  hoare forward.
(************************* msg != null finished *************************)
(****************************** msg == null ******************************)
  assert (x11 = Vnull).
  {
    clear -H36 Hif_false.
    generalize Hif_false.
    clear Hif_false.
    unfold isptr in H36.
    destruct H36 as [H | (p & H)];
      [ subst
      | destruct p; subst ];
      unfold val_eq;
      unfold val_inj;
      unfold notint; unfold Int.notbool;
      try rewrite Int.eq_true;
      try rewrite Int.eq_false.
    intro H; destruct H; tryfalse; auto.
    pure_auto.
    intro H; destruct H; tryfalse; auto.
  }
  clear Hif_false.

  Set Printing Depth 300.
  idtac.
  
  apply mutex_pend_part_0
  with
  (v'18 := v'18)
    (v'19 := v'19)
    (v'47 := v'47)
    (v'48 := v'48)
    (v'49 := v'49)
    (x := x)
    (x0 := x0)
    (x1 := x1)
    (v'43 := v'43)
    (v'45 := v'45)
    (st := st); eauto.
Qed.

  
















  
