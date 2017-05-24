Require Import ucos_include.
Require Import os_ucos_h.
Require Import sep_lemmas_ext.
Require Import linv_solver.
Require Import inline_definitions.
Require Import inline_bittblfunctions.
Require Import inline_tactics.
Require Import symbolic_lemmas.
Require Import new_inv.
Require Import task_pure.
Require Import protect.
Require Import OSQPostPure.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.
 

  Lemma absimp_taskdel_rdy_succ:
  forall P v3 sch t tls mqls ct ,
    can_change_aop P ->
    (* Int.lt ($ 63) v3 = false ->
     * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
     * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
     * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||> **
                       HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| sdel ((Vint32 v3):: nil);;isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||> **  HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  unfold taskdelcode.
  infer_branch 5%nat.
  unfold sdel.
  eapply absinfer_eq.
Qed.


Lemma task_delete_ready:
  forall
    (
  v' v'0 v'1 v'2 : val
                     )(
  v'3 v'4 v'5 : list vallist
)(
  v'6 : list EventData
)(
  v'7 : list os_inv.EventCtr
)(
  priotbl : vallist
)(
  v'9 : val
)(
  l1 l2 : list vallist
)(
  v'16 : EcbMod.map
)(
  tcbmap : TcbMod.map
)(
  v'18 : int32
)(
  vhold : addrval
)(
  v'20 : val
)(
  v'21 : list vallist
)(
  v'22 : val
)(
  H4 : array_type_vallist_match OS_TCB ∗ priotbl
)(
  H7 : length priotbl = 64%nat
)(
  H6 : R_PrioTbl_P priotbl tcbmap vhold
)(
  v'23 v'24 : val
)(
  v'25 v'26 : TcbMod.map
)(
  H8 : v'9 <> Vnull
)(
  H9 : join v'25 v'26 tcbmap
)(
  v'27 : val
)(
  cur_tcb_blk : block
)(
  H2 : RH_TCBList_ECBList_P v'16 tcbmap (cur_tcb_blk, Int.zero)
)(
  H3 : RH_CurTCB (cur_tcb_blk, Int.zero) tcbmap
)(
  H15 : Vptr (cur_tcb_blk, Int.zero) <> Vnull
)(
  x1 x2 x3 x4 : val
)(
  x5 : int32
)(
  x6 x7 x8 x9 : val
)(
  H12 : isptr v'27
)(
  hello : taskstatus
)(
  kitty : ProtectWrapper
            (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) = Some (x5, hello, x2))
)(
  H19 : RH_CurTCB (cur_tcb_blk, Int.zero) tcbmap
)(
  H17 : RH_TCBList_ECBList_P v'16 tcbmap (cur_tcb_blk, Int.zero)
)(
  v'10 v'12 : val
)(
  H18 : v'9 <> Vnull
)(
  x : taskstatus
)(
  x0 : msg
)(
  l1' l2' : list vallist
)(
  v'13 : val
)(
  v'17 v'19 : TcbMod.map
)(
  H28 : TcbMod.join v'17 v'19 tcbmap
)(
  x17 x18 x19 x20 : val
)(
  H16 : isptr x20
)(
  H27 : isptr x19
)(
  H31 : isptr x18
)(
  H32 : isptr x17
)(
  i6 : int32
)(
  H33 : Int.unsigned i6 <= 65535
)(
  i5 : int32
)(
  H34 : Int.unsigned i5 <= 255
)(
  i4 : int32
)(
  H35 : Int.unsigned i4 <= 255
)(
  i3 : int32
)(
  H36 : Int.unsigned i3 <= 255
)(
  i2 : int32
)(
  H37 : Int.unsigned i2 <= 255
)(
  i1 : int32
)(
  H38 : Int.unsigned i1 <= 255
)(
  i0 : int32
)(
  H39 : Int.unsigned i0 <= 255
)(
  todelblock : block
)(
  H14 : (todelblock, Int.zero) <> vhold
)(
  some_pure_hyp : ~ is_some_mutex_owner (todelblock, Int.zero) v'16
)(
  H40 : Vptr (todelblock, Int.zero) <> Vnull
)(
  i13 : int32
)(
  H45 : Int.unsigned i13 <= 65535
)(
  H42 : isptr v'13
)(
  x10 : addrval
)(
  H41 : isptr (Vptr x10)
)(
  x13 : TcbMod.map
)(
  H44 : isptr x0
)(
  x23 : val
)(
  H43 : isptr x23
)(
  v'11 : block
)(
  v'29 : int32
)(
  v'30 : vallist
)(
  v'31 : addrval
)(
  v'32 v'33 v'34 v'35 v'36 : expr
)(
  v'40 v'41 v'43 : int32
)(
  H59 : OSRdyGrp ′
        :: OSRdyTbl ′
           :: ptcb ′ → OSTCBBitX
              :: ptcb ′ → OSTCBBitY :: ptcb ′ → OSTCBY :: nil =
        v'33 :: v'32 :: v'34 :: v'35 :: v'36 :: nil
)(
  H71 : Int.unsigned v'41 <= Byte.max_unsigned
)(
  H66 : rule_type_val_match Int8u (Vint32 v'40) = true
)(
  H21 : Int.unsigned v'29 <= 255
)(
  H5 : RL_RTbl_PrioTbl_P v'30 priotbl vhold
)(
  H10 : TCBList_P v'9 l1 v'30 v'25
)(
  H29 : TCBList_P v'9 l1' v'30 v'17
)(
  H11 : TCBList_P (Vptr (cur_tcb_blk, Int.zero))
          ((x20
            :: x19
               :: x18
                  :: x17
                     :: Vint32 i6
                        :: Vint32 i5
                           :: Vint32 i4
                              :: Vint32 i3
                                 :: Vint32 i2
                                    :: Vint32 i1 :: Vint32 i0 :: nil) :: l2)
          v'30 v'26
)(
  H52 : TCBList_P (Vptr x10) l2' v'30 x13
)(
  H20 : array_type_vallist_match Int8u v'30
)(
  H56 : length v'30 = ∘ OS_RDY_TBL_SIZE
)(
  H55 : prio_in_tbl ($ OS_IDLE_PRIO) v'30
)(
  H54 : length v'30 = ∘ OS_RDY_TBL_SIZE
)(
  H30 : RL_Tbl_Grp_P v'30 (Vint32 v'29)
)(
  H57 : 0 <= Int.unsigned v'43
)(
  H65 : Int.unsigned v'43 < 64
)(
  H1 : Int.unsigned v'43 <= 255
)(
  H : Int.unsigned v'43 < 64
)(
  H0 : Int.unsigned v'43 <> 63
)(
  H13 : nth_val' (Z.to_nat (Int.unsigned v'43)) priotbl =
        Vptr (todelblock, Int.zero)
)(
  H23 : TcbMod.get tcbmap (todelblock, Int.zero) = Some (v'43, x, x0)
)(
  H47 : Int.unsigned v'43 <= 255
)(
  H22 : TcbJoin (todelblock, Int.zero) (v'43, x, x0) x13 v'19
)(
  H49 : Int.unsigned (v'43 >>ᵢ $ 3) <= 255
)(
  H50 : Int.unsigned ($ 1<<ᵢ(v'43&ᵢ$ 7)) <= 255
)(
  H48 : Int.unsigned (v'43&ᵢ$ 7) <= 255
)(
  H51 : Int.unsigned ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) <= 255
)(
  H60 : nth_val' (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30 = Vint32 v'41
)(
  H63 : length
          (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
             (val_inj
                (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7))))))) =
        ∘ OS_RDY_TBL_SIZE
)(
  H67 : RL_Tbl_Grp_P
          (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
             (val_inj
                (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7)))))))
          (Vint32 v'40)
)(
  H68 : forall x : int32,
        prio_in_tbl x v'30 ->
        Int.eq x v'43 = false ->
        prio_in_tbl x
          (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
             (val_inj
                (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7)))))))
)(
  H69 : prio_not_in_tbl v'43
          (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
             (val_inj
                (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7)))))))
)(
  H70 : array_type_vallist_match Int8u
          (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
             (val_inj
                (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7)))))))
)(
  H64 : $ OS_STAT_RDY = $ OS_STAT_RDY -> x23 = Vnull
)(
  H46 : Int.unsigned ($ OS_STAT_RDY) <= 255
)(
  H24 : ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'9
          (l1' ++
           (Vptr x10
            :: v'13
               :: x23
                  :: x0
                     :: Vint32 i13
                        :: V$ OS_STAT_RDY
                           :: Vint32 v'43
                              :: Vint32 (v'43&ᵢ$ 7)
                                 :: Vint32 (v'43 >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                                          :: nil) :: l2')
)(
  Heqtcblst : ProtectWrapper
                (l1' ++
                 (Vptr x10
                  :: v'13
                     :: x23
                        :: x0
                           :: Vint32 i13
                              :: V$ OS_STAT_RDY
                                 :: Vint32 v'43
                                    :: Vint32 (v'43&ᵢ$ 7)
                                       :: Vint32 (v'43 >>ᵢ $ 3)
                                          :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                             :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                                                :: nil) :: l2' =
                 l1 ++
                 (x20
                  :: x19
                     :: x18
                        :: x17
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3
                                       :: Vint32 i2
                                          :: Vint32 i1 :: Vint32 i0 :: nil)
                 :: l2)
)(
  H26 : ptr_in_tcbdllseg (Vptr (todelblock, Int.zero)) v'9
          (l1' ++
           (Vptr x10
            :: v'13
               :: x23
                  :: x0
                     :: Vint32 i13
                        :: V$ OS_STAT_RDY
                           :: Vint32 v'43
                              :: Vint32 (v'43&ᵢ$ 7)
                                 :: Vint32 (v'43 >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                                          :: nil) :: l2')
)(
  H25 : TCBList_P v'9
          (l1' ++
           (Vptr x10
            :: v'13
               :: x23
                  :: x0
                     :: Vint32 i13
                        :: V$ OS_STAT_RDY
                           :: Vint32 v'43
                              :: Vint32 (v'43&ᵢ$ 7)
                                 :: Vint32 (v'43 >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                                          :: nil) :: l2') v'30 tcbmap
)(
  backup : TCBList_P (Vptr (todelblock, Int.zero))
             ((Vptr x10
               :: v'13
                  :: x23
                     :: x0
                        :: Vint32 i13
                           :: V$ OS_STAT_RDY
                              :: Vint32 v'43
                                 :: Vint32 (v'43&ᵢ$ 7)
                                    :: Vint32 (v'43 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                                             :: nil) :: l2') v'30 v'19
)(
  H53 : R_TCB_Status_P
          (Vptr x10
           :: v'13
              :: x23
                 :: x0
                    :: Vint32 i13
                       :: V$ OS_STAT_RDY
                          :: Vint32 v'43
                             :: Vint32 (v'43&ᵢ$ 7)
                                :: Vint32 (v'43 >>ᵢ $ 3)
                                   :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                      :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
          v'30 (v'43, x, x0)
          ),
   {|OS_spec, GetHPrio, OSLInv, I,
   fun v : option val =>
   ( <|| END v ||>  **
    p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
    ((EX v0 : val, LV prio @ Int8u |-> v0) **
     (EX v0 : val, LV pevent @ OS_EVENT ∗ |-> v0) **
     (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
     (EX v0 : val, LV self @ Int8u |-> v0) **
     (EX v0 : val, LV os_code_defs.x @ OS_TCB ∗ |-> v0) ** Aemp) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil), Afalse|}
   |- (cur_tcb_blk, Int.zero)
   {{ <||
     (* taskdel_clear_waitls_bit (|Vint32 v'43 :: nil|);; *)
     sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
     LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
     Astruct (todelblock, Int.zero) OS_TCB_flag
       (Vptr x10
        :: v'13
           :: Vnull
              :: x0
                 :: V$ 0
                    :: V$ OS_STAT_RDY
                       :: Vint32 v'43
                          :: Vint32 (v'43&ᵢ$ 7)
                             :: Vint32 (v'43 >>ᵢ $ 3)
                                :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                   :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil) **
     HECBList v'16 **
     HTCBList tcbmap **
     HTime v'18 **
     HCurTCB (cur_tcb_blk, Int.zero) **
     LV pevent @ OS_EVENT ∗ |-> Vnull **
     GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
     GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
       (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
          (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7))))))) **
     dllseg (Vptr x10) (Vptr (todelblock, Int.zero)) v'12 Vnull l2'
       OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
       (fun vl : vallist => nth_val 0 vl) **
     dllseg v'9 Vnull v'13 (Vptr (todelblock, Int.zero)) l1' OS_TCB_flag
       (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
     GV OSTCBList @ OS_TCB ∗ |-> v'9 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aisr empisr **
     AECBList v'7 v'6 v'16 tcbmap **
     tcbdllflag v'9
       (l1' ++
        (Vptr x10
         :: v'13
            :: Vnull
               :: x0
                  :: Vint32 i13
                     :: V$ OS_STAT_RDY
                        :: Vint32 v'43
                           :: Vint32 (v'43&ᵢ$ 7)
                              :: Vint32 (v'43 >>ᵢ $ 3)
                                 :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                    :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
        :: l2') **
     AOSTCBPrioTbl priotbl v'30 tcbmap vhold **
     A_isr_is_prop **
     p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
     LV self @ Int8u |-> (V$ 0) **
     AOSEventFreeList v'3 **
     AOSQFreeList v'4 **
     AOSQFreeBlk v'5 **
     AOSMapTbl **
     AOSUnMapTbl **
     AOSIntNesting **
     AOSTCBFreeList v'20 v'21 **
     AOSTime (Vint32 v'18) **
     AGVars **
     atoy_inv' **
     LV os_code_defs.x @ OS_TCB ∗ |-> v'2 **
     LV prio @ Int8u |-> Vint32 v'43 **
     A_dom_lenv
       ((prio, Int8u)
        :: (pevent, OS_EVENT ∗)
           :: (ptcb, OS_TCB ∗)
              :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil)}} 
   OSTCBPrioTbl ′ [prio ′] =ₑ NULL;ₛ
   ptcb ′ → OSTCBEventPtr =ₑ NULL;ₛ
   IF(ptcb ′ → OSTCBPrev ==ₑ NULL)
        {os_code_defs.x ′ =ₑ ptcb ′ → OSTCBNext;ₛ
        os_code_defs.x ′ → OSTCBPrev =ₑ NULL;ₛ
        OSTCBList ′ =ₑ os_code_defs.x ′} 
       ELSE {os_code_defs.x ′ =ₑ ptcb ′ → OSTCBPrev;ₛ
            os_code_defs.x ′ → OSTCBNext =ₑ ptcb ′ → OSTCBNext;ₛ
            os_code_defs.x ′ =ₑ ptcb ′ → OSTCBNext;ₛ
            os_code_defs.x ′ → OSTCBPrev =ₑ ptcb ′ → OSTCBPrev}   ;ₛ
   ptcb ′ → OSTCBNext =ₑ OSTCBFreeList ′;ₛ
   OSTCBFreeList ′ =ₑ ptcb ′;ₛ
   os_task.STKFREE ptcb ′;ₛ
   ptcb ′ → OSTCBflag =ₑ ′ 0;ₛ
   EXIT_CRITICAL;ₛ
   OS_Sched (­);ₛ
                  RETURN ′ OS_NO_ERR {{Afalse}}.
Proof.
  intros.
  hoare unfold.
  hoare forward.
  math simpls.
  assumption.




  
  (* ... *)
    Set Printing Depth 999.
  hoare forward.

    destruct l2'.
    unfold1 dllseg.
    hoare unfold.
    inverts H73.
    unfold1 dllseg.
    unfold node.
    hoare unfold.

  
  (* hoare abscsq.
   * apply noabs_oslinv.
   * eapply absimp_taskdel_rdy_succ.
   * go.
   * exact H23.
   * go.
   * go.
   * go. *)
  
  destruct l1'.
  hoare_assert_pure (v'13 = Vnull). 
  unfold1 dllseg in H73.
  sep normal in H73.
  sep destruct H73.
  sep split in H73.
  rewrite H75; reflexivity.
  
  (* v'13 is null, deleting first tcb node *)
  {
    hoare_split_pure_all.
    subst v'13.

    hoare forward.
    (* intro; tryfalse. *)
    go.
    (* intro; tryfalse. *)

    Focus 2.
    hoare_split_pure_all; false.
    clear -H73; simpljoin.
    destruct H73; tryfalse.

    hoare unfold.
    hoare forward.
    (* intro; tryfalse. *)
    go.
    hoare forward.
    hoare forward.

    hoare forward.

    Focus 2.
    hoare_split_pure_all.
    false.
    clear -H73; destruct H73; tryfalse.


    hoare unfold.
    unfold AOSTCBFreeList.
    hoare unfold.
    hoare forward.

    eapply isptr_is_definitely_ptr.
    eapply sll_head_isptr.
    instantiate (5:=s).
    sep cancel sll.
    go.

    hoare forward.
    (* Local Open Scope list_scope. *)

    (* hoare abscsq.
     * apply noabs_oslinv.
     * eapply absimp_taskdel_succ.
     * go.
     * 2: eauto.
     * exact kitty. *)
    (*************)
    clear H73 H74 H75.
    assert (todelblock = cur_tcb_blk \/ todelblock <> cur_tcb_blk) by tauto. 
    destruct H73.
    (* delete current *)
    {
      subst todelblock.
      (* unfold get in H16; simpl in H16. *)
      rewrite H23 in kitty.
      Set Printing Depth 999.
      eapply backward_rule1.
      instantiate (1:=
                     (
 <|| sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                  HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
   GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   LV ptcb @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag
     (v'20
      :: Vnull
         :: Vnull
            :: x0
               :: V$ 0
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'43
                        :: Vint32 (v'43&ᵢ$ 7)
                           :: Vint32 (v'43 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil) **
   GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'15, Int.zero) **
   LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'15, Int.zero) **
   Astruct (v'15, Int.zero) OS_TCB_flag
     (v'14
      :: Vnull
         :: x25
            :: x24
               :: Vint32 i12
                  :: Vint32 i11
                     :: Vint32 i10
                        :: Vint32 i9
                           :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil) **
   dllseg v'14 (Vptr (v'15, Int.zero)) v'12 Vnull l2' OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
     (update_nth_val (Z.to_nat (Int.unsigned v'43)) priotbl Vnull) **
   PV vhold @ Int8u |-> v'8 **
   HECBList v'16 **
   (* HTCBList tcbmap ** *)
   HTime v'18 **
   (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
   LV pevent @ OS_EVENT ∗ |-> Vnull **
   GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
   GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
        (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7))))))) **
   dllseg v'9 Vnull Vnull (Vptr (cur_tcb_blk, Int.zero)) nil OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   (* Aie false ** *)
   (* Ais nil ** *)
   (* Acs (true :: nil) ** *)
   (* Aisr empisr ** *)
   AECBList v'7 v'6 v'16 tcbmap **
   tcbdllflag v'9
     (nil ++
      (Vptr (v'15, Int.zero)
       :: Vnull
          :: Vnull
             :: x0
                :: Vint32 i13
                   :: V$ OS_STAT_RDY
                      :: Vint32 v'43
                         :: Vint32 (v'43&ᵢ$ 7)
                            :: Vint32 (v'43 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
      :: (v'14
          :: Vptr (cur_tcb_blk, Int.zero)
             :: x25
                :: x24
                   :: Vint32 i12
                      :: Vint32 i11
                         :: Vint32 i10
                            :: Vint32 i9
                               :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
         :: l2') **
   G& OSPlaceHolder @ Int8u == vhold **
   (* A_isr_is_prop ** *)
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   LV self @ Int8u |-> (V$ 0) **
   AOSEventFreeList v'3 **
   AOSQFreeList v'4 **
   AOSQFreeBlk v'5 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSIntNesting **
   sll v'20 v'21 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
   sllfreeflag v'20 v'21 **
   AOSTime (Vint32 v'18) **
   AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'43 )).
      clear.
      intro; intros.
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.
      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (cur_tcb_blk, Int.zero) (v'43, x, x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in *; simpl in *.
      unfold get, sig, join in *; simpl in *.
      go.

      destruct H73 as (tcbmap_left & tcbmapleft_join_hyp).


      eapply seq_rule.
      eapply  derive_delself_rule.

        
      apply goodlinv.
       (* goodlinv *)
      go.
      unfold AEventData.
      (* destruct x22; go. *)
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.

      exact tcbmapleft_join_hyp.
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H73.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.

      rewrite app_nil_l.
      unfold1 tcbdllflag.
      unfold1 dllsegflag.
      hoare unfold.
      hoare lift 4%nat pre.
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      unfold1 dllseg.
      hoare unfold.
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 24)  ) in H74.
      eauto.

      hoare lift 2%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 12%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep cancel 40%nat 1%nat.
      simpl; auto.
      splits; eauto.
      unfolds; auto.
      

      eapply backward_rule1.
      intro; intros.
      sep lifts (7::9::nil)%nat in H74.
      eapply add_a_isr_is_prop in H74.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local, OSLInv.
      unfold LINV.
      sep pauto.
      sep cancel 2%nat 1%nat.
      sep cancel CurTid.
      unfold OSInv.
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      instantiate (17 := v'7).
      instantiate (16 := v'6).
      unfold AECBList.

      (* instantiate (x3 := (x11 ++ (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
       *                            (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
       *                                            (val_inj
       *                                               (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
       *                           ) :: x15)).
       * instantiate (x2 :=(x23 ++ x22 :: x24) ). *)
      unfold AECBList in H74.
      sep pauto.
      (* eapply evsllseg_merge. *)
      (* eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H80). *)
      (* eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H81). *)

      (* unfold1 evsllseg . *)
      (* sep pauto. *)
      (* unfold AEventNode. *)
      (* sep cancel evsllseg. *)
      (* sep cancel evsllseg. *)
      (* unfold AOSEvent. *)
      (* unfold node. *)
      (* unfold AOSEventTbl. *)
      (* sep pauto. *)
      (* sep cancel Aarray. *)
      (* sep lift 2%nat. *)
      (* eapply AED_changegrp. *)
      (* sep cancel AEventData. *)
      (* unfold Astruct. *)
      (* unfold OS_EVENT. *)
      (* unfold Astruct'. *)
      (* sep normal. *)
      (* sep cancel 14%nat 2%nat. *)
      (* repeat sep cancel 14%nat 1%nat. *)
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 12%nat 1%nat.
      sep cancel 16%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold AOSTCBList'.
      eapply intro_or_r.
      sep pauto.
      unfold tcblist.
      instantiate ( 5 := nil).
      instantiate ( 3 := l2').
      instantiate ( 4 := (v'38
                             :: Vnull
                             :: x25
                             :: x24
                             :: Vint32 i12
                             :: Vint32 i11
                             :: Vint32 i10
                             :: Vint32 i9
                             :: Vint32 i8
                             :: Vint32 i7 :: Vint32 i :: nil)).
      (* instantiate (x1 := (nil ++ (v'48
       *                               :: Vnull
       *                               :: x35
       *                               :: x34
       *                               :: Vint32 i15
       *                               :: Vint32 i14
       *                               :: Vint32 i12
       *                               :: Vint32 i11
       *                               :: Vint32 i10
       *                               :: Vint32 i9 :: Vint32 i :: nil) :: l2')). *)
      
(* ** ac:       Print  TCB_Not_In . *)
      unfold TCB_Not_In.
      sep pauto.
      (* unfold tcbdllseg. *)
      (* SearchAbout dllseg. *)
      eapply tcbdllseg_compose.
      unfold tcbdllseg.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 9%nat 1%nat.
      sep cancel 9%nat 1%nat.
      unfold1 tcbdllflag.
      unfold tcbdllflag in H74.
      rewrite app_nil_l.
      unfold1 dllsegflag.
      unfold1 dllsegflag in H74.
      sep normal in H74.
      sep pauto.
      (* inverts H126. *)
      sep cancel dllsegflag.
      sep cancel 2%nat 1%nat.
      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_r. 
      unfold TCBFree_Eq.
      sep pauto.
      sep cancel sll.
      sep cancel sllfreeflag.
      eauto.
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      sep cancel sll.
      go.
      unfolds.
      {
        do 6 eexists.
        splits.
        go.
        go.
        go.
        go.
        go.
        go.
        go.
        splits.
        go.
        go.
        go.
        go.
        left; auto.
        repeat tri_exists_and_solver1.
        go.
        lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
        subst.
        reflexivity.
      }
      eexists; go.
      {
        unfolds in H6.
        simpljoin.
        clear -tcbmapleft_join_hyp H93.
        unfolds.
        unfolds in tcbmapleft_join_hyp.
        intro.
        simpljoin.

        unfolds in H93.
        assert (x1 <> (cur_tcb_blk, Int.zero)).
        intro.
        subst.
(* ** ac:         SearchAbout join. *)
(* ** ac:         SearchAbout TcbMod.join. *)
        eapply TcbMod.map_join_get_some .
        
        auto.
        eauto.
        2: exact H.
        instantiate (1:=(v'43, x, x0)).
        unfold get in *; simpl in *.
        unfold sig in *; simpl in *.
        eapply TcbMod.get_a_sig_a.
        go.
        unfold join, sig, get in *; simpl in *.
        assert (TcbMod.get tcbmap x1 =Some (v'43, x2, x3) ).
        go.
        assert (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) =Some (v'43, x, x0) ).
        go.
        lets bb: H93 H0 H1 H2.
        apply bb.
        reflexivity.

      }
      
      go.
      go.
      intro; tryfalse.
      go.
      go.
      {
        split.
        rewrite ptr_in_tcblist_app.
        2: simpl; auto.
        intro.
        destruct H92.
        simpl in H92.
        exact H92.
        simpl (val_inj (get_last_tcb_ptr nil (Vptr (v'15, Int.zero)))) in H92.
        gen H92.
        eapply distinct_is_unique_second.
        3: eapply  TCBLP_imply_dictinct_list .
        2:instantiate ( 1 := (Vptr (v'15, Int.zero)
      :: Vnull
         :: x23
            :: x0
               :: Vint32 i13
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'43
                        :: Vint32 (v'43&ᵢ$ 7)
                           :: Vint32 (v'43 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)).
        2: go.
        2:instantiate (3 :=  nil).
        simpl; auto.
        rewrite app_nil_l.

         exact backup.
         simpl.
         auto.
         eauto.
      }
       (* from tcblist_p, get they are all different? *)
      {
        rewrite app_nil_l.
        rewrite app_nil_l in H25.
(* ** ac:         Print  R_PrioTbl_P . *)
        

        eapply tcblist_p_hold_for_del_a_tcb_at_head.
        omega.
        2:go.
        2:go.
        3: exact H25.
        2: exact tcbmapleft_join_hyp.
        unfolds in H6.
        simpljoin; assumption.
      }
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.

        
(* OSTimeDlyPure.update_rtbl_tcblist_hold: *)

        
        
      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        omega.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .

      }
       (* r_priotbl_p hold for deleting a tcb *)
      
{
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
  omega.
  rewrite Int.repr_unsigned.
  reflexivity.

  rewrite Int.repr_unsigned.
  reflexivity.

  2: assumption.
  unfold nat_of_Z.
  apply nv'2nv.
  
  assumption.
  intro; tryfalse.
  
      }

       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.
(* ** ac:       Check  ECBLP_hold4del_a_tcb. *)
(* ** ac:       Print ECBList_P. *)
(* ** ac:       Print isWait4Ecb. *)
      Lemma ECBLP_hold4del_a_tcb_rdy:
        forall lowl head tail highl ecbmap tcbmap v'43 x x0 tcbmap_left tcb_block,
          ECBList_P head tail lowl highl ecbmap tcbmap ->
          TcbMod.joinsig (tcb_block, Int.zero) (v'43, x, x0) tcbmap_left tcbmap ->
          (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ) ->
          ECBList_P head tail lowl highl ecbmap tcbmap_left .
      Proof.
        induction lowl.
        simpl.
        intros.
        auto.
        intros.
        unfold1 ECBList_P in *.
        simpljoin.
        destruct highl; tryfalse.
        destruct a.
        simpljoin.
        repeat tri_exists_and_solver1.
        rewrite R_ECB_ETbl_P_is_poi.
        rewrite R_ECB_ETbl_P_is_poi in H2.
        unfold poi_RLEHT in *.
        simpljoin.
        splits; auto.

        unfold poi_RHT_LE in *.
        intros.
        assert (get tcbmap tid0 = Some (prio, wait hwb n, m)).
        unfold get in *; simpl in *.
        go.
        eapply H2; eauto.
        
        unfold poi_RLE_HT in *.
        intros.

        lets bb: H6 H8.
        simpljoin.

        eapply join_get_or in H9.
        2: auto.
        2: exact H0.
        destruct H9.
        Focus 2.
        repeat tri_exists_and_solver1.
        false.
        apply (H1 x1).
        assert ( x5 = (tcb_block, Int.zero) \/ x5 <> (tcb_block, Int.zero)).
        tauto.
        destruct H12; subst;
        unfold get in *; simpl in *.
        rewrite TcbMod.get_a_sig_a in H9.
        inverts H9.
        repeat tri_exists_and_solver1.
        go.


        rewrite TcbMod.get_a_sig_a' in H9.
        inverts H9.
        go.
      Qed.

      assert (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ). 
      intros.
      intro.
      simpljoin.
      Lemma lowready_not_wait4ecb:
        forall v'15 x0 i13  v'30 v'43 x11 x12 ecbid, 
        R_TCB_Status_P
          (Vptr (v'15, Int.zero)
           :: Vnull
              :: Vnull
                 :: x0
                    :: Vint32 i13
                       :: V$ OS_STAT_RDY
                          :: Vint32 v'43
                             :: Vint32 (v'43&ᵢ$ 7)
                                :: Vint32 (v'43 >>ᵢ $ 3)
                                   :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                      :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
          v'30 (v'43, wait x11 x12, x0) ->
        ~ isWait4Ecb x11 ecbid .
      Proof.
        intros.
        unfolds in H.
        simpljoin.
        clear -H2.
        unfolds in H2.
        simpljoin.
        unfold isWait4Ecb.
        intro.
        destruct H4; subst.
        {
        clear -H0.
        unfolds in H0.
        lets bb: H0 (eq_refl  (v'43, wait (os_stat_sem ecbid) x12, x0) ).
        simpljoin;  tryfalse.
        }
       destruct H4; subst.
        {
        clear -H1.
        unfolds in H1.
        lets bb: H1 (eq_refl  (v'43, wait (os_stat_q ecbid) x12, x0) ).
        simpljoin;  tryfalse.
        }
       
        destruct H4; subst.
        {
        clear -H2.
        unfolds in H2.
        lets bb: H2 (eq_refl  (v'43, wait (os_stat_mbox ecbid) x12, x0) ).
        simpljoin;  tryfalse.
        }
       
        {
        clear -H3.
        unfolds in H3.
        lets bb: H3 (eq_refl  (v'43, wait (os_stat_mutexsem ecbid) x12, x0) ).
        simpljoin;  tryfalse.
        }
      Qed.
      gen H93.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.

      eapply ECBLP_hold4del_a_tcb_rdy; eauto.
      

      
      (* eapply poi_is_rtep in H2.
       * unfolds in H2.
       * simpljoin.
       *                           
       * clear -H92 H93 H23.
       * unfolds in H92.
       * lets bb: 
       * go.
       * go.
       * go.
       * go.
       * clear -H96 H121.
       * unfolds in H96.
       * change Byte.max_unsigned with 255%Z in * .
       * math simpl in H96.
       * omega.
       * go.
       * 
       * {
       *   eapply ECBLP_hold4del_a_tcb; eauto.
       *   3:exact tcbmapleft_join_hyp.
       *   clear -H6; unfolds in H6; tauto.
       *   clear -H6; unfolds in H6; tauto.
       * } *)
      
      (* admit. (* from H101 : RL_Tbl_Grp_P *)
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)

          
(* ** ac:       Check poi_RHTEP_hold_for_del_a_tcb. *)
      assert (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ). 
      intros.
      intro.
      simpljoin.
      gen H92.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.

      rewrite <- poi_is_rtep.
      rewrite <- poi_is_rtep in H2.
      Lemma poi_RH_T_E_P_hold_for_tcbdel_rdy:
        forall todel v'43 x x0 tcbmap_left tcbmap v'16,
          ~ is_some_mutex_owner todel v'16  ->
          TcbMod.joinsig todel (v'43, x, x0) tcbmap_left tcbmap ->
          (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ) ->
          poi_RH_T_E_P v'16 tcbmap ->
          poi_RH_T_E_P v'16 tcbmap_left.
      Proof.
        intros.
        unfold poi_RH_T_E_P in *; simpljoin.
        splits; auto.
        unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
        intros.
        lets bb: H2 H5.
        simpljoin.
        eapply join_get_or in H6.
        2:auto.
        2: eauto.
        destruct H6; eauto.
        assert (todel = tid \/ todel <> tid).
        tauto.
        unfold get in *; simpl in *.
        destruct H7; subst.
        rewrite TcbMod.get_a_sig_a in H6.
        inverts H6.
        false.
        apply H.
        unfolds.
        eauto.
        go.

        rewrite TcbMod.get_a_sig_a' in H6.
        inverts H6.
        go.

        unfold poi_R_TE in *.
        intros.
        assert (get tcbmap tid = Some (p, wait waitstat t, msg)).
        unfold get in *; simpl in *.
        go.
        lets bb: H3 H5 H7.
        auto.

        unfold poi_R_ET in *.
        intros.
        lets bb: H4 H5.
        simpljoin.
        
        eapply join_get_or in H6; eauto.
        destruct H6; eauto.
        assert (todel = tid \/ todel <> tid).
        tauto.
        unfold get in *; simpl in *.
        destruct H8; subst.
        rewrite TcbMod.get_a_sig_a in H6.
        inverts H6.
(* ** ac:         SearchAbout hle2wait. *)
        
        false.
        apply (H1 eid).
        repeat tri_exists_and_solver1.
(* ** ac:         SearchAbout hle2wait. *)
        Lemma isw4e_hle2w_same':
          forall (a : edata) (b : ecbid),
             isWait4Ecb (hle2wait a b) b .
        Proof.
          intros.
          unfold isWait4Ecb; unfold hle2wait.
          destruct a; auto.
        Qed.

        apply isw4e_hle2w_same'.
        go.

        rewrite TcbMod.get_a_sig_a' in H6.
        inverts H6.
        go.
        
      Qed.

      eapply poi_RH_T_E_P_hold_for_tcbdel_rdy; eauto.

      
        
      (* eapply poi_is_rtep.
       * 
       *  
       * 
       * {
       *   eapply poi_RHTEP_hold_for_del_a_tcb.
       *   assumption.
       *   go.
       *   eapply tcbmapleft_join_hyp.
       *   go.
       *   clear -H2 H61 H62; unfolds; splits; auto.
       * } *)
        
      
       (* change to poi, *)
(* from some_pure_hyp : forall (eid : tidspec.A) (pr : int32) 
 *                     (tid0 : tid) (opr : int32) (wls : waitset),
 *                   EcbMod.get ecbmap eid =
 *                   Some (absmutexsem pr (Some (tid0, opr)), wls) ->
 *                   tid0 <> (cur_tcb_blk, Int.zero)
 * get rh_te_p hold for deleting a tcb *)
      splits; go.
      unfolds; auto.
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      inverts H75.
      reflexivity.
    }

    (* delete some tcb other than current, at head *)
    {
      eapply backward_rule1.
      Set Printing Depth 999.
      intro; intros.
      Set Printing Depth 999.
(* ** ac:       Show. *)
      instantiate ( 1 := (
        <|| sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                              HTCBList tcbmap **
                              HCurTCB (cur_tcb_blk, Int.zero) **
                              OS [ empisr, false, nil, (true::nil)] **
 (* <|| sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  ** *)
           A_dom_lenv
             ((prio, Int8u)
              :: (pevent, OS_EVENT ∗)
                 :: (ptcb, OS_TCB ∗)
                    :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
           GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
           LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
           Astruct (todelblock, Int.zero) OS_TCB_flag
             (v'20
              :: Vnull
                 :: Vnull
                    :: x0
                       :: V$ 0
                          :: V$ OS_STAT_RDY
                             :: Vint32 v'43
                                :: Vint32 (v'43&ᵢ$ 7)
                                   :: Vint32 (v'43 >>ᵢ $ 3)
                                      :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                         :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                                            :: nil) **
           GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'15, Int.zero) **
           LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'15, Int.zero) **
           Astruct (v'15, Int.zero) OS_TCB_flag
             (v'14
              :: Vnull
                 :: x25
                    :: x24
                       :: Vint32 i12
                          :: Vint32 i11
                             :: Vint32 i10
                                :: Vint32 i9
                                   :: Vint32 i8
                                      :: Vint32 i7 :: Vint32 i :: nil) **
           dllseg v'14 (Vptr (v'15, Int.zero)) v'12 Vnull l2' OS_TCB_flag
             (fun vl : vallist => nth_val 1 vl)
             (fun vl : vallist => nth_val 0 vl) **
           GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
             (update_nth_val (Z.to_nat (Int.unsigned v'43)) priotbl Vnull) **
           PV vhold @ Int8u |-> v'8 **
           HECBList v'16 **
           (* HTCBList tcbmap ** *)
           HTime v'18 **
           (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
           LV pevent @ OS_EVENT ∗ |-> Vnull **
           GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
             (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
                (val_inj
                   (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7))))))) **
           dllseg v'9 Vnull Vnull (Vptr (todelblock, Int.zero)) nil
             OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
             (fun vl : vallist => nth_val 0 vl) **
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
           (* Aie false ** *)
           (* Ais nil ** *)
           (* Acs (true :: nil) ** *)
           (* Aisr empisr ** *)
           AECBList v'7 v'6 v'16 tcbmap **
           tcbdllflag v'9
             (nil ++
              (Vptr (v'15, Int.zero)
               :: Vnull
                  :: Vnull
                     :: x0
                        :: Vint32 i13
                           :: V$ OS_STAT_RDY
                              :: Vint32 v'43
                                 :: Vint32 (v'43&ᵢ$ 7)
                                    :: Vint32 (v'43 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                                             :: nil)
              :: (v'14
                  :: Vptr (todelblock, Int.zero)
                     :: x25
                        :: x24
                           :: Vint32 i12
                              :: Vint32 i11
                                 :: Vint32 i10
                                    :: Vint32 i9
                                       :: Vint32 i8
                                          :: Vint32 i7 :: Vint32 i :: nil)
                 :: l2') **
           G& OSPlaceHolder @ Int8u == vhold **
           (* A_isr_is_prop ** *)
           p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
           LV self @ Int8u |-> (V$ 0) **
           AOSEventFreeList v'3 **
           AOSQFreeList v'4 **
           AOSQFreeBlk v'5 **
           AOSMapTbl **
           AOSUnMapTbl **
           AOSIntNesting **
           sll v'20 v'21 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
           sllfreeflag v'20 v'21 **
           AOSTime (Vint32 v'18) **
           AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'43)).
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.
      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (todelblock, Int.zero) (v'43, x, x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in H22; simpl in H22.
      unfold get, sig, join in H22, H9; simpl in H22, H9.
      go.

      destruct H74 as (tcbmap_left & tcbmapleft_join_hyp).
      rename H73 into not_cur_hyp.


      eapply seq_rule.
      eapply  derive_delother_rule.
      apply goodlinv.
       (* goodlinv *)
      go.
      (* unfold AEventData. *)
      (* destruct x22; go. *)
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      exact tcbmapleft_join_hyp.
      clear -H3.
      unfolds in H3.
      unfolds.
      simpljoin; eauto.

      clear -not_cur_hyp.
      intro H; inverts H; apply not_cur_hyp; reflexivity.

      
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H73.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.

      rewrite app_nil_l.
      unfold1 tcbdllflag.
      unfold1 dllsegflag.
      hoare unfold.
      hoare lift 4%nat pre.
      unfold OSLInv at 3.
      unfold LINV.
      unfold1 dllseg.
      hoare unfold.
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 24)  ) in H73.
      eauto.

      (* hoare lift 2%nat pre. *)
      hoare lift 4%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 12%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      linv_solver.
      (* intro; intros.
       * unfold p_local, OSLInv.
       * sep pauto.
       * unfold LINV.
       * sep pauto.
       * sep cancel 49%nat 1%nat.
       * simpl; auto.
       * splits; eauto.
       * unfolds; auto. *)
      

      eapply backward_rule1.
      intro; intros.
      sep lifts (7::9::nil)%nat in H73.
      eapply add_a_isr_is_prop in H73.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel p_local.
      eapply poi_OSINV_imply_OSInv.

      unfold poi_OSINV.
(*       try progress snormal_3.
 *       try unfold myAconj.
 *       Ltac aaa :=
 *   let H := fresh "H" in
 *   match goal with
 *     | |- _ |= EX _ , _ =>
 *       eapply aexists_prop;
 *         [intros ? H; try progress aaa; exact H | idtac]
 *     | |- _ |= _ => idtac
 *   end.
 *       aaa.
 * Ltac aaa' :=
 *   let s := fresh in
 *   let H := fresh in
 *   match goal with
 *     | |- ?s' |= ?A => 
 *           let t := toTree A in
 *           pose (ssimplI t) as H;
 *             cbv [asrtTree_to_list asrtTree_to_list' listsimpl listsimplA listsimplB
 *                  myAppAsrtTree list_to_asrtTree unTree] in H;
 *             apply H; clear H;
 *             try unfold myAconj
 *     | _ => fail
 *   end.
 * aaa'.
 * assert (   s
 *    |= EX (y y0 y1 : list vallist) (y2 : list EventData)
 *       (y3 : list os_inv.EventCtr) (y4 : vallist) (y5 : val) 
 *       (y6 : vallist) (y7 : val) (y8 : list vallist) 
 *       (y9 : EcbMod.map) (y10 : TcbMod.map) (y11 : int32) 
 *       (y12 y13 : addrval) (y14 : val) (y15 : list vallist),
 *       (AOSEventFreeList y **
 *        AOSQFreeList y0 **
 *        AOSQFreeBlk y1 **
 *        AECBList y3 y2 y9 y10 **
 *        AOSMapTbl **
 *        AOSUnMapTbl **
 *        AOSTCBPrioTbl y4 y6 y10 y13 **
 *        AOSIntNesting **
 *        poi_AOSTCBList y5 y10 y6 y12 y8 y14 **
 *        AOSTCBFreeList' y14 y15 y12 **
 *        AOSRdyTblGrp y6 y7 **
 *        AOSTime (Vint32 y11) **
 *        HECBList y9 **
 *        HTCBList y10 **
 *        HTime y11 **
 *        HCurTCB y12 **
 *        AGVars ** [|RH_TCBList_ECBList_P y9 y10 y12|] ** A_isr_is_prop) ).
 * sep normal.
 * sep eexists.
 * 
 *       ssimpl.
 *       Print OSInv.
 *       sep semiauto.
 *       sep pauto. *)
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      instantiate (14 := v'7).
      instantiate (13 := v'6).
      unfold AECBList.
      (* instantiate (x3 := (x11 ++ (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
       *                            (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
       *                                            (val_inj
       *                                               (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
       *                           ) :: x15)).
       * instantiate (x2 :=(x23 ++ x22 :: x24) ). *)

      (* instantiate (x3 := (x5 ++ (Vint32 i8 :: Vint32 v'53 :: Vint32 i9 :: x29 :: x30 :: v'6 :: nil,
       *                            (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
       *                                            (val_inj
       *                                               (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
       *                           ) :: x15)).
       * instantiate (x2 :=(x23 ++ x22 :: x24) ). *)
      unfold AECBList in H73.
      sep pauto.
      (* eapply evsllseg_merge.
       * 
       * eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H80).
       * eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H81).
       * unfold1 evsllseg .
       * sep pauto.
       * Print AEventNode.
       * unfold AEventNode.
       * sep cancel evsllseg.
       * sep cancel evsllseg.
       * unfold AOSEvent.
       * unfold node.
       * unfold AOSEventTbl.
       * sep pauto.
       * sep cancel Aarray.
       * (* Lemma AED_changegrp:
       *  *   forall a grp grp' b c d e f g P,
       *  *     AEventData (a:: grp:: b:: c:: d:: e:: f :: nil) g **P  ==>
       *  *                AEventData (a:: grp' :: b :: c :: d ::e ::f ::nil) g ** P. 
       *  * Proof.
       *  *   intros.
       *  *   unfold AEventData in *.
       *  *   destruct g;
       *  *     sep pauto.
       *  * Qed.
       *  * 
       *  * Show. *)
       * sep lift 2%nat.
       * eapply AED_changegrp.
       * sep cancel AEventData.
       * unfold Astruct.
       * unfold OS_EVENT.
       * unfold Astruct'.
       * sep normal.
       * sep cancel 14%nat 2%nat.
       * repeat sep cancel 14%nat 1%nat. *)
      unfold AOSTCBPrioTbl.
      sep pauto.
      idtac.
      idtac.
      sep cancel 12%nat 1%nat.
      sep cancel 16%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold poi_AOSTCBList.
      
      sep pauto.
      instantiate (4 := (
                          (v'39
                             :: Vnull
                             :: x25
                             :: x24
                             :: Vint32 i12
                             :: Vint32 i11
                             :: Vint32 i10
                             :: Vint32 i9
                             :: Vint32 i8
                             :: Vint32 i7 :: Vint32 i :: nil)
                            :: l2')).
      (* unfold tcbdllflag.
       * 
       * sep cancel dllsegflag.
       * sep cancel 1%nat 1%nat.
       * SearchAbout ptr_in_tcbdllseg.
       * 
       * 
       * 
       * 
       * 
       * sep pauto.
       * unfold tcblist.
       * instantiate ( x7 := nil).
       * instantiate ( x9 := l2').
       * instantiate ( x8 := (v'50
       *                        :: Vnull
       *                        :: x35
       *                        :: x34
       *                        :: Vint32 i16
       *                        :: Vint32 i15
       *                        :: Vint32 i14
       *                        :: Vint32 i12
       *                        :: Vint32 i11
       *                        :: Vint32 i10 :: Vint32 i7 :: nil)).
       * instantiate (x1 := (nil ++ (v'50
       *                               :: Vnull
       *                               :: x35
       *                               :: x34
       *                               :: Vint32 i16
       *                               :: Vint32 i15
       *                               :: Vint32 i14
       *                               :: Vint32 i12
       *                               :: Vint32 i11
       *                               :: Vint32 i10 :: Vint32 i7 :: nil) :: l2')).
       * 
       * Print  TCB_Not_In .
       * unfold TCB_Not_In.
       * sep pauto.
       * (* unfold tcbdllseg. *)
       * (* SearchAbout dllseg. *)
       * SearchAbout tcbdllseg.
       * eapply tcbdllseg_compose. *)
      unfold tcbdllseg.
      unfold tcbdllflag.
      unfold1 dllsegflag.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 2%nat 1%nat.
      sep cancel dllsegflag.
      sep cancel dllseg.
      sep cancel 7%nat 1%nat.
      (* sep cancel 9%nat 1%nat.
       * sep cancel 9%nat 1%nat.
       * unfold tcbdllflag in H123.
       * rewrite app_nil_l.
       * unfold1 dllsegflag in H123.
       * sep normal in H123.
       * sep pauto.
       * (* inverts H126. *)
       * sep cancel dllsegflag.
       * sep cancel 2%nat 1%nat. *)
      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_l. 
      unfold TCBFree_Not_Eq.
      sep pauto.
      instantiate (2 := (
                           (v'20
                              :: Vnull
                              :: Vnull
                              :: x0
                              :: V$ 0
                              :: V$ OS_STAT_RDY
                              :: Vint32 v'43
                              :: Vint32 (v'43&ᵢ$ 7)
                              :: Vint32 (v'43 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                              :: nil) ::v'21
                                      
                         )).
      unfold sll.
      unfold sllfreeflag.
      unfold1 sllseg.
      unfold1 sllsegfreeflag.
      unfold node.
      unfold sll in H73.
      unfold sllfreeflag in H73.
      sep pauto.
      sep cancel sllseg.
      sep cancel sllsegfreeflag.
      
      sep cancel 1%nat 1%nat.
      sep cancel Astruct.
      eauto.
      go.
      go.
      apply isptr_is_definitely_ptr.
      eapply sllseg_head_isptr.
      instantiate (5:=s).
      sep cancel sllseg.
      eauto.

      go.
      intro; tryfalse.
      go.
      go.
      go.
      intro; tryfalse.
      {

        rewrite app_nil_l in H25.
        eapply tcblist_p_hold_for_del_a_tcb_at_head.
        omega.
        2:go.
        2:go.
        3: exact H25.
        2: exact tcbmapleft_join_hyp.
        unfolds in H6.
        simpljoin; assumption.
      }
       (* tcblist_p hold for deleting a tcb *)
      {

        clear -H24 not_cur_hyp .

        eapply ptr_in_tcbdllseg_change_head.
        Focus 2.
                eapply ptr_in_tcbdllseg_not_head.
        rewrite app_nil_l in H24.
        2: eauto.
        simpl; auto.
        intro; tryfalse.
        unfold V_OSTCBNext.
        reflexivity.
      }

      
       (* from tcblist_p, get they are all different? *)
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.

      {
        eapply r_priotbl_p_hold_for_del_a_tcb.
        
        omega.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .
      }
       (* r_priotbl_p hold for deleting a tcb *)
      {
        eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
        omega.
        rewrite Int.repr_unsigned.
        reflexivity.

        rewrite Int.repr_unsigned.
        reflexivity.

        2: assumption.
        unfold nat_of_Z.
        apply nv'2nv.
        
        assumption.
        intro; tryfalse.
      }
       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.

      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.

      {
      assert (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ). 
      intros.
      intro.
      simpljoin.
      
      gen H91.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.

      eapply ECBLP_hold4del_a_tcb_rdy; eauto.
      }
       (* from H101 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)
      {
        rewrite <- poi_is_rtep.
        rewrite <- poi_is_rtep in H2.

        eapply poi_RH_T_E_P_hold_for_tcbdel_rdy; eauto.
      intros.
      intro.
      simpljoin.
      
      gen H90.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.
      }
       (* change to poi,
from some_pure_hyp : forall (eid : tidspec.A) (pr : int32) 
                    (tid0 : tid) (opr : int32) (wls : waitset),
                  EcbMod.get ecbmap eid =
                  Some (absmutexsem pr (Some (tid0, opr)), wls) ->
                  tid0 <> (cur_tcb_blk, Int.zero)
get rh_te_p hold for deleting a tcb
              *)
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      inverts H74.
      reflexivity.
      
    }
    (* delete some tcb in the middle of the tcblist *)
  }
  {
    destruct H42.
    hoare_assert_pure False.
    (* hw **)
    subst v'13.

    eapply dllseg_tail_not_null.
    instantiate (10:=s0).
    sep pauto.
    sep cancel 16%nat 1%nat.
    eauto.
    hoare unfold.
    inverts H73.

    destruct H42 as (prev_tcb_ptr & eqprev); subst v'13.
    (* rename x11 into prev_tcb_ptr. *)

    eapply backward_rule1.
    intro; intros.
    sep lift 16%nat in H42.
    rewrite dllseg_split_node_tail in H42.
    
    eauto.
    unfold node.
    hoare unfold.
    rename v'38 into prev_tcb_block.
    rename v'15 into next_tcb_block.

    hoare forward.
    (* intro; tryfalse. *)
    go.
    (* intro; tryfalse. *)
    hoare unfold.
    instantiate (1:= Afalse).
    false.

    hoare unfold.
    clear H42.
    hoare forward.
    (* intro; tryfalse. *)
    go.
    hoare forward.
    (* intro; tryfalse. *)
    go.
    
    hoare forward.
    (* intro; tryfalse. *)
    go.
    
    hoare forward.
    (* intro; tryfalse. *)
    go.

    hoare forward.
    hoare unfold.
    unfold   AOSTCBFreeList.
    hoare normal pre.
    hoare forward.
    eapply isptr_match_eq_true.
    eapply sll_head_isptr.
    instantiate (5 := s).
    sep cancel sll.
    eauto.

    hoare forward.
    assert (todelblock = cur_tcb_blk \/ todelblock <> cur_tcb_blk) by tauto. 
    destruct H74.
    (* delete current *)
    {
      subst todelblock.
      (* unfold get in H16; simpl in H16. *)
      rewrite H23 in kitty.
      (* Lemma derive_delself_rule:
       *   forall pa P  prio st msg tls' tls t e tp  aop r ri sd Spec I isr ie is cs,
       *     GoodLInvAsrt pa ->
       *     GoodFrm P ->
       *     joinsig t (prio, st, msg) tls' tls  ->
       *     P ==>  Rv e @ tp == Vptr t //\\  CurLINV pa t ->
       *     InfRules Spec sd pa I r ri 
       *              (
       *                <|| spec_del  (Vint32 prio);; aop ||>  **
       *                    Aabsdata abstcblsid (abstcblist tls) **
       *                    Aabsdata curtid (oscurt t) **
       *                    OS[isr, ie, is, cs] ** P
       *              ) 
       *              (sprim (stkfree e))
       *              (
       *                <|| aop ||>  **
       *                    Aabsdata abstcblsid (abstcblist tls') ** 
       *                    Aabsdata curtid (oscurt t) **
       *                    OS[isr, ie, is, cs]  
       *                    ** P
       *              ) t.
       * Proof.
       *   intros.
       *   eapply backward_rule1.
       *   instantiate (1:= (
       *                     <|| spec_del (Vint32 prio);; aop ||> ** P**
       *                         HTCBList tls ** HCurTCB t ** OS [isr, ie, is, cs] 
       *                         
       *                   )).
       *   intro.
       *   intros.
       *   sep pauto.
       *   eapply forward_rule2.
       *   eapply delself_rule; eauto.
       *   intro.
       *   intro.
       *   sep pauto.
       * Qed. *)
      eapply backward_rule1.
      instantiate (1:=
                     (
                       <|| sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **

   (* <|| sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  ** *)
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
   GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   LV ptcb @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
   Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag
     (v'20
      :: Vptr (prev_tcb_block, Int.zero)
         :: Vnull
            :: x0
               :: V$ 0
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'43
                        :: Vint32 (v'43&ᵢ$ 7)
                           :: Vint32 (v'43 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil) **
   LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (next_tcb_block, Int.zero) **
   Astruct (next_tcb_block, Int.zero) OS_TCB_flag
     (v'14
      :: Vptr (prev_tcb_block, Int.zero)
         :: x25
            :: x24
               :: Vint32 i12
                  :: Vint32 i11
                     :: Vint32 i10
                        :: Vint32 i9
                           :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil) **
   Astruct (prev_tcb_block, Int.zero) OS_TCB_flag
     (Vptr (next_tcb_block, Int.zero)
      :: v'13
         :: x26
            :: x22
               :: Vint32 i20
                  :: Vint32 i19
                     :: Vint32 i18
                        :: Vint32 i17
                           :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil) **
   dllseg v'9 Vnull v'13 (Vptr (prev_tcb_block, Int.zero)) v'28 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   dllseg v'14 (Vptr (next_tcb_block, Int.zero)) v'12 Vnull l2' OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
     (update_nth_val (Z.to_nat (Int.unsigned v'43)) priotbl Vnull) **
   PV vhold @ Int8u |-> v'8 **
   HECBList v'16 **
   (* HTCBList tcbmap ** *)
   HTime v'18 **
   (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
   LV pevent @ OS_EVENT ∗ |-> Vnull **
   GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
   GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
        (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7))))))) **
   GV OSTCBList @ OS_TCB ∗ |-> v'9 **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   (* Aie false ** *)
   (* Ais nil ** *)
   (* Acs (true :: nil) ** *)
   (* Aisr empisr ** *)
   AECBList v'7 v'6 v'16 tcbmap **
   tcbdllflag v'9
     ((v :: l1') ++
      (Vptr (next_tcb_block, Int.zero)
       :: Vptr (prev_tcb_block, Int.zero)
          :: Vnull
             :: x0
                :: Vint32 i13
                   :: V$ OS_STAT_RDY
                      :: Vint32 v'43
                         :: Vint32 (v'43&ᵢ$ 7)
                            :: Vint32 (v'43 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
      :: (v'14
          :: Vptr (cur_tcb_blk, Int.zero)
             :: x25
                :: x24
                   :: Vint32 i12
                      :: Vint32 i11
                         :: Vint32 i10
                            :: Vint32 i9
                               :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
         :: l2') **
   G& OSPlaceHolder @ Int8u == vhold **
   (* A_isr_is_prop ** *)
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   LV self @ Int8u |-> (V$ 0) **
   AOSEventFreeList v'3 **
   AOSQFreeList v'4 **
   AOSQFreeBlk v'5 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSIntNesting **
   sll v'20 v'21 OS_TCB_flag V_OSTCBNext **
   sllfreeflag v'20 v'21 **
   AOSTime (Vint32 v'18) **
   AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'43 )).

      clear.
      intro; intros.
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.

      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (cur_tcb_blk, Int.zero) (v'43, x,  x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in *; simpl in *.
      unfold get, sig, join in *; simpl in *.
      go.

      destruct H74 as (tcbmap_left & tcbmapleft_join_hyp).


      eapply seq_rule.
      eapply derive_delself_rule.
      apply goodlinv.

       (* goodlinv *)
      go.
      (* unfold AEventData. *)
      (* destruct x22; go. *)
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      exact tcbmapleft_join_hyp.
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H74.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.
      hoare lift 27%nat pre.
      eapply backward_rule1.
      eapply dllsegflag_split.
      hoare_split_pure_all.
      unfold dllsegflag at 2.
      fold dllsegflag .
      hoare_split_pure_all.
      inverts H75.
      inverts H101.
      inverts H100.
      inverts H74.
      inverts H75.
      rewrite H73.

      (* Lemma dllsegflag_last_next_is_endstnl:
       *   forall l head endstnl endp next s P,
       *     s |= dllsegflag head endstnl (l++ (endp :: nil)) next  ** P ->
       *     next endp = Some endstnl.
       * Proof.
       *   induction l.
       *   intros.
       *   simpl (nil ++ endp :: nil) in H.
       *   unfold dllsegflag in H.
       *   sep normal in H.
       *   sep destruct H.
       *   sep split in H.
       *   subst.
       *   auto.
       * 
       *   intros.
       *   simpl ((a ::l ) ++ endp :: nil) in H.
       *   unfold1 dllsegflag in H.
       *   
       *   sep normal in H.
       *   sep destruct H.
       *   sep split in H.
       *   sep lift 2%nat in H.
       *   eapply IHl.
       *   eauto.
       * Qed. *)

      hoare_assert_pure ( (fun vl : vallist => nth_val 0 vl) (Vptr (cur_tcb_blk, Int.zero)
                                                                   :: v'13
                                                                   :: x26
                                                                   :: x22
                                                                   :: Vint32 i20
                                                                   :: Vint32 i19
                                                                   :: Vint32 i18
                                                                   :: Vint32 i17
                                                                   :: Vint32 i16
                                                                   :: Vint32 i15 :: Vint32 i14 :: nil) = Some (Vptr v'37) ).
      eapply dllsegflag_last_next_is_endstnl.
      instantiate (4 := s0).
      sep cancel 4%nat 1%nat.
      eauto.

      hoare_split_pure_all.
      inverts H74.

      
      
      (* rewrite app_nil_l. *)
      (* hoare unfold. *)
      (* hoare lift 4%nat pre. *)
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      hoare_split_pure_all.
      (* unfold1 dllseg. *)
      (* hoare unfold. *)
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 24)  ) in H100.
      eauto.

      hoare lift 5%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 13%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep cancel 43%nat 1%nat.
      simpl; auto.
      splits; eauto.
      unfolds; auto.
      

      eapply backward_rule1.
      intro; intros.
      sep lifts (8::10::nil)%nat in H100.
      eapply add_a_isr_is_prop in H100.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local, OSLInv.
      unfold LINV.
      sep pauto.
      sep cancel 2%nat 1%nat.
      sep cancel CurTid.
      unfold OSInv.
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      instantiate (17 := v'7).
      instantiate (16 := v'6).
      unfold AECBList.
(* instantiate (x3 := (x11 ++ (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
 *                                  (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
 *                                                  (val_inj
 *                                                     (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
 *                                 ) :: x15)).
 *       instantiate (x2 :=(x23 ++ x22 :: x24) ). *)


      (* instantiate (x3 := (x5 ++ (Vint32 i8 :: Vint32 v'53 :: Vint32 i9 :: x29 :: x30 :: v'6 :: nil,
       *                            (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
       *                                            (val_inj
       *                                               (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
       *                           ) :: x15)).
       * instantiate (x2 :=(x23 ++ x22 :: x24) ). *)
      unfold AECBList in H100.
      sep pauto.
      (* eapply evsllseg_merge.
       * eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H80).
       * eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H81).
       * 
       * (* admit.
       *  * admit. *)
       * unfold1 evsllseg .
       * sep pauto.
       * unfold AEventNode.
       * sep cancel evsllseg.
       * sep cancel evsllseg.
       * unfold AOSEvent.
       * unfold node.
       * unfold AOSEventTbl.
       * sep pauto.
       * sep cancel Aarray.
       * 
       * sep lift 2%nat.
       * eapply AED_changegrp.
       * sep cancel AEventData.
       * unfold Astruct.
       * unfold OS_EVENT.
       * unfold Astruct'.
       * sep normal.
       * sep cancel 16%nat 2%nat.
       * repeat sep cancel 16%nat 1%nat. *)
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 20%nat 2%nat.
      sep cancel 14%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold AOSTCBList'.
      eapply intro_or_r.
      sep pauto.
      unfold tcblist.

      instantiate ( 5 :=(v'28 ++
                               (Vptr (next_tcb_block, Int.zero)
                                     :: v'13
                                     :: x26
                                     :: x22
                                     :: Vint32 i20
                                     :: Vint32 i19
                                     :: Vint32 i18
                                     :: Vint32 i17
                                     :: Vint32 i16
                                     :: Vint32 i15 :: Vint32 i14 :: nil)
                               :: nil)  ).

      instantiate ( 3 := l2').
      instantiate ( 4 :=
                      (v'42
                         :: Vptr (prev_tcb_block, Int.zero)
                         :: x25
                         :: x24
                         :: Vint32 i12
                         :: Vint32 i11
                         :: Vint32 i10
                         :: Vint32 i9
                         :: Vint32 i8
                         :: Vint32 i7 :: Vint32 i :: nil)).
      (* (Vptr (next_tcb_block, Int.zero)
       *                :: v'13
       *                   :: x36
       *                      :: x33
       *                         :: Vint32 i23
       *                            :: Vint32 i22
       *                               :: Vint32 i21
       *                                  :: Vint32 i20
       *                                     :: Vint32 i19
       *                                        :: Vint32 i18 :: Vint32 i17 :: nil) 
       *              ). *)
      (* instantiate (x1 :=
       *                ((v'46 ++
       *                       (Vptr (cur_tcb_blk, Int.zero)
       *                             :: v'13
       *                             :: x36
       *                             :: x33
       *                             :: Vint32 i23
       *                             :: Vint32 i22
       *                             :: Vint32 i21
       *                             :: Vint32 i20
       *                             :: Vint32 i19
       *                             :: Vint32 i18 :: Vint32 i17 :: nil) :: nil)
       *                   ++
       *                   (v'52
       *                      :: Vptr (prev_tcb_block, Int.zero)
       *                      :: x35
       *                      :: x34
       *                      :: Vint32 i16
       *                      :: Vint32 i15
       *                      :: Vint32 i14
       *                      :: Vint32 i12
       *                      :: Vint32 i11
       *                      :: Vint32 i10 :: Vint32 i7 :: nil) :: l2') ). *)

      unfold TCB_Not_In.
      sep pauto.
      eapply tcbdllseg_compose.
      unfold tcbdllseg.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 10%nat 1%nat.
      sep cancel 12%nat 1%nat.
      (* Goal forall l head headprev tail tailnext x t fprev fnext,
       *        dllseg head headprev tail tailnext (l++x::nil) t fprev fnext <==>
       *               EX tail', dllseg head headprev tail' tail l t fprev fnext **
       *                                [| |] *)
       
      (* Fixpoint poidllseg (head  headprev tail tailnext: val) (l : list vallist) cond : asrt:=
       *   match l with
       *     | nil =>  [| head = tailnext /\ headprev = tail|]
       *        | vl :: l' =>
       *          EX  (vn : val),
       *          cond head headprev vl vn **
       *          (* scond head vl  ** *)
       *           poidllseg vn head tail tailnext l' cond 
       *   end.
       * 
       * Lemma poidllseg_is_poillseg :
       *   forall l head hp tail tn cond,
       *     poidllseg head hp tail tn l cond <==> poi_llseg (head, hp) (tn, tail) l
       *               (fun head vl head'=> let (h, hp) := head in let (h', hp') := head' in 
       *                                                           cond h hp vl h' ** [|hp' = h|]).
       * Proof.
       *   induction l.
       *   intros.
       *   split.
       *   unfold poidllseg, poi_llseg in *.
       *   intro.
       *   sep auto.
       *   simpljoin.
       *   
       *   unfold poidllseg, poi_llseg in *.
       *   intro.
       *   sep auto.
       *   simpljoin.
       *   tauto.
       *   intros.
       *   splits.
       *   intros.
       *   unfold1 poidllseg in H.
       *   sep destruct H.
       *   unfold poi_llseg.
       *   sep eexists.
       *   instantiate (x := (x, head)).
       *   simpl (let (h', hp') := (x, head) in cond head hp a h' ** [| hp' = head |]) .
       *   sep pauto.
       *   apply IHl.
       *   auto.
       *   intro.
       *   unfold poi_llseg in H.
       *   sep destruct H.
       *   destruct x.
       *   unfold1 poidllseg.
       *   sep eexists.
       *   sep cancel 1%nat 1%nat.
       *   sep split in H.
       *   apply IHl in H.
       *   subst.
       *   auto.
       * Qed. *)
        
      (* Lemma split_poidllseg :
       *   forall l1 l2 head headprev tail tailnext cond P,
       *     poidllseg head headprev tail tailnext (l1 ++ l2) cond ** P<==>
       *               EX mid midn,
       *               poidllseg head headprev mid midn l1 cond **
       *                         poidllseg midn mid tail tailnext l2 cond ** P.
       * Proof.
       *   induction l1.
       *   intros.
       *   splits.
       *   intros.
       *   simpl (nil ++ l2) in H.
       *   sep eexists.
       *   unfold1 poidllseg.
       *   sep pauto.
       *   intros.
       * 
       *   simpl (nil ++ l2) .
       *   sep pauto.
       *   unfold1 poidllseg in H.
       *   sep pauto.
       *   subst; auto.
       *   intro.
       * 
       *   split.
       *   intros.
       *   simpl  ( (a::l1) ++ l2) in H.
       *   unfold1 poidllseg in H.
       *   sep normal in H.
       *   sep destruct H.
       *   sep split in H.
       *   sep lift 2%nat in H.
       *   apply IHl1 in H.
       *   sep pauto.
       *   unfold1 poidllseg.
       *   sep pauto.
       *   sep cancel 3%nat 1%nat.
       *   sep pauto.
       *   intro.
       *   
       *   simpl  ( (a::l1) ++ l2) .
       *   unfold1 poidllseg.
       *   sep destruct H.
       *   unfold1 poidllseg in H.
       *   sep normal in H.
       *   sep destruct H.
       *   sep split in H.
       *   sep normal.
       *   sep eexists.
       *   sep split.
       *   sep lift 2%nat.
       *   rewrite IHl1.
       *   sep eexists.
       *   sep cancel 1%nat 3%nat.
       *   sep pauto.
       * Qed.
       * 
       * Show. *)
      eapply dllseg_is_poi.
      eapply split_poillseg.
      sep eexists.
      rewrite <- dllseg_is_poi.
      sep lift 2%nat.
      rewrite <- dllseg_is_poi.
      instantiate (3 := (Vptr (prev_tcb_block, Int.zero))).
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 10%nat 1%nat.
      sep cancel dllseg.


     (* Fixpoint poisllseg (head tailnext: val) (l : list vallist) cond : asrt:=
      *    match l with
      *      | nil =>  [| head = tailnext |]
      *         | vl :: l' =>
      *           EX  (vn : val),
      *           cond head vl vn **
      *           (* scond head vl  ** *)
      *            poisllseg vn tailnext l' cond 
      *    end.
      *  
      * 
      *  Lemma split_poisllseg :
      *    forall l1 l2 head tailnext cond P,
      *      poisllseg head tailnext (l1 ++ l2) cond ** P<==>
      *                EX midn,
      *                poisllseg head midn l1 cond **
      *                          poisllseg midn tailnext l2 cond ** P.
      *  Proof.
      *    induction l1.
      *    intros.
      *    splits.
      *    intros.
      *    simpl (nil ++ l2) in H.
      *    sep eexists.
      *    unfold1 poisllseg.
      *    sep pauto.
      *    intros.
      * 
      *    simpl (nil ++ l2) .
      *    sep pauto.
      *    unfold1 poisllseg in H.
      *    sep pauto.
      *    subst; auto.
      *    intro.
      * 
      *    split.
      *    intros.
      *    simpl  ( (a::l1) ++ l2) in H.
      *    unfold1 poisllseg in H.
      *    sep normal in H.
      *    sep destruct H.
      *    sep split in H.
      *    sep lift 2%nat in H.
      *    apply IHl1 in H.
      *    sep pauto.
      *    unfold1 poisllseg.
      *    sep pauto.
      *    sep cancel 3%nat 1%nat.
      *    sep pauto.
      *    intro.
      *    
      *    simpl  ( (a::l1) ++ l2) .
      *    unfold1 poisllseg.
      *    sep destruct H.
      *    unfold1 poisllseg in H.
      *    sep normal in H.
      *    sep destruct H.
      *    sep split in H.
      *    sep normal.
      *    sep eexists.
      *    sep split.
      *    sep lift 2%nat.
      *    rewrite IHl1.
      *    sep eexists.
      *    sep cancel 1%nat 3%nat.
      *    sep pauto.
      *  Qed.
      * 
      *  Show.
      * 
      *  Print tcbdllflag.
      *  Print tcbdllflag.
      *  Print dllsegflag.
      *  Print dllsegflag.
      *  Print dllsegflag.
      *  Print dllsegflag. *)
      unfold tcbdllflag.
      sep lift 4%nat in H100.
      rewrite dllsegflag_is_poi in H100.
      apply split_poillseg in H100.

      apply dllsegflag_is_poi.
      sep pauto.
      apply split_poillseg.
      sep eexists.
      apply split_poillseg.
      sep eexists.
      sep cancel 1%nat 1%nat.
      unfold1 @poi_llseg in *.
      sep normal.
      sep normal in H100.
      sep destruct H100.
      sep eexists.
      instantiate ( 3 := Vptr (next_tcb_block, Int.zero)).
      sep pauto.
      sep lift 2%nat.
      rewrite <- dllsegflag_is_poi.
      sep cancel dllsegflag.
      (* instantiate (x1 := x14). *)
      sep cancel 1%nat 2%nat.
      sep cancel 2%nat 1%nat.

      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_r. 
      unfold TCBFree_Eq.
      sep pauto.
      sep cancel sll.
      sep cancel sllfreeflag.
      eauto.
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      sep cancel sll.
      go.
      unfolds.
      {
        do 6 eexists.
        splits.
        go.
        go.
        go.
        go.
        go.
        go.
        go.
        splits.
        go.
        go.
        go.
        go.
        left; auto.
        repeat tri_exists_and_solver1.
        go.
        rewrite (H64 (eq_refl ($ OS_STAT_RDY))).
        reflexivity.
      }
      eexists; go.
           {
        unfolds in H6.
        simpljoin.
        clear -tcbmapleft_join_hyp H104.
        unfolds.
        unfolds in tcbmapleft_join_hyp.
        intro.
        simpljoin.

        unfolds in H104.
        assert (x1 <> (cur_tcb_blk, Int.zero)).
        intro.
        subst.
(* ** ac:         SearchAbout join. *)
(* ** ac:         SearchAbout TcbMod.join. *)
        eapply TcbMod.map_join_get_some .
        
        auto.
        eauto.
        2: exact H.
        instantiate (1:=(v'43, x, x0)).
        unfold get in *; simpl in *.
        unfold sig in *; simpl in *.
        eapply TcbMod.get_a_sig_a.
        go.
        unfold join, sig, get in *; simpl in *.
        assert (TcbMod.get tcbmap x1 =Some (v'43, x2, x3) ).
        go.
        assert (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) =Some (v'43, x, x0) ).
        go.
        lets bb: H104 H0 H1 H2.
        apply bb.
        reflexivity.

      }
  
      go.
      2: go.
      go.
      (* intro; tryfalse. *)
      go.
      go.
      (* intro; tryfalse. *)
      go.
      go.
      go.
      {
        splits
.
assert( list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None)
   (v'28 ++
    (Vptr (cur_tcb_blk, Int.zero)
     :: v'13
        :: x26
           :: x22
              :: Vint32 i20
                 :: Vint32 i19
                    :: Vint32 i18
                       :: Vint32 i17
                          :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil)
    :: nil) )as hell.

change ((fun x => list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) x)
         (v'28 ++
      (Vptr (cur_tcb_blk, Int.zero)
       :: v'13
          :: x26
             :: x22
                :: Vint32 i20
                   :: Vint32 i19
                      :: Vint32 i18
                         :: Vint32 i17
                            :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil)
      :: nil)).
 
 rewrite <- H73.

     
 eapply TCBLP_imply_nextnotnull_list.
 exact H29.
 
 rewrite H73.
 
         rewrite get_last_tcb_ptr_appsig.
         reflexivity.

        (* here *)
        rewrite ptr_in_tcblist_app.
        (* 2: simpl; auto. *)
        intro.
        destruct H102.
        eapply ptr_in_tcblist_last_ir in H102.
        gen H102.
        eapply distinct_is_unique_first.
instantiate ( 1 :=(Vptr (cur_tcb_blk, Int.zero)
             :: v'13
                :: x26
                   :: x22
                      :: Vint32 i20
                         :: Vint32 i19
                            :: Vint32 i18
                               :: Vint32 i17
                                  :: Vint32 i16
                                  :: Vint32 i15 :: Vint32 i14 :: nil)).

exact hell.

         eapply  TCBLP_imply_dictinct_list .
         rewrite <- H73.
         exact H25.

         rewrite get_last_tcb_ptr_appsig.
         reflexivity.

           
       
        (* simpl in H131. *)
        (* exact H131. *)
         rewrite get_last_tcb_ptr_appsig in H102.
         simpl (val_inj (Some (Vptr (next_tcb_block, Int.zero)))) in H102. 

        eapply ptr_in_tcblist_change_first in H102.
        gen H102.

        eapply distinct_is_unique_second.
        3: eapply  TCBLP_imply_dictinct_list .
        3: exact H25.
        2: go.
        rewrite H73.
        exact hell.
        rewrite H73.
        rewrite get_last_tcb_ptr_appsig.
        reflexivity.
        rewrite list_all_P_app.
        rewrite list_all_P_app in hell.
        simpljoin.
        splits; auto.
        simpl.
        split; auto.
         (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)
        eauto.
      }
       (* from tcblist_p, get they are all different? *)
      {


         eapply TCBList_merge_prop.
         instantiate (2 := v'17).
         instantiate (1 := x13).

         eapply some_join_lemma0; eauto.
         exact H22.
         exact tcbmapleft_join_hyp.
         rewrite app_last.
         simpl.
         go.
         Focus 2.

         eapply  tcblist_p_hold_for_del_a_tcb_at_head .
         omega.

        2:go.
        2:go.
        2: exact H22.
        2: exact backup.
        unfolds in H6.
        simpljoin.
        clear -H103 H28.
        eapply R_Prio_No_Dup_hold_for_subset.
        apply TcbMod.join_comm; eauto.
        eauto.

        
        eapply OSTimeDlyPure.update_rtbl_tcblist_hold.

        omega.
        unfold nat_of_Z; eapply nv'2nv.
        exact H60.
        intro; tryfalse.
        intros.

        unfolds in H6.
        simpljoin.
        clear -H28 H22 H104 H102.
        eapply H104.
        instantiate (2 := tid).
        instantiate (1 := (cur_tcb_blk, Int.zero)).
        intro; subst tid.
        eapply TcbMod.map_join_get_some.
        auto.
        exact H28.
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        go.
        
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        go.
        
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        unfold get; simpl.
        go.
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        unfold get; simpl.
        go.


        eapply TCBList_P_hold_for_last_change.
        rewrite H73 in H29.
        exact H29.
        
        
      }
       (* tcblist_p hold for deleting a tcb *)
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.
       
      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        omega.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .

      }

       (* r_priotbl_p hold for deleting a tcb *)
      
{
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
  omega.
  rewrite Int.repr_unsigned.
  reflexivity.

  rewrite Int.repr_unsigned.
  reflexivity.

  2: assumption.
  unfold nat_of_Z.
  apply nv'2nv.
  
  assumption.
  intro; tryfalse.
  
      }

       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.


      {
      assert (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ). 
      intros.
      intro.
      simpljoin.
      
      gen H103.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.

      eapply ECBLP_hold4del_a_tcb_rdy; eauto.
      }
       (* from H101 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)
      {
        rewrite <- poi_is_rtep.
        rewrite <- poi_is_rtep in H2.

        eapply poi_RH_T_E_P_hold_for_tcbdel_rdy; eauto.
      intros.
      intro.
      simpljoin.
      
      gen H102.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.
      }

      splits; go.
      unfolds; auto.
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      inverts H101.
      reflexivity.
    }

    (* delete not current *)
    {
      eapply backward_rule1.
      Set Printing Depth 999.
(* ** ac:       Show. *)
      instantiate (1:=
                     (
                       <|| sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **
   (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
   (* <|| sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  ** *)
   A_dom_lenv
     ((prio, Int8u)
      :: (pevent, OS_EVENT ∗)
         :: (ptcb, OS_TCB ∗)
            :: (self, Int8u) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
   GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
   LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
   Astruct (todelblock, Int.zero) OS_TCB_flag
     (v'20
      :: Vptr (prev_tcb_block, Int.zero)
         :: Vnull
            :: x0
               :: V$ 0
                  :: V$ OS_STAT_RDY
                     :: Vint32 v'43
                        :: Vint32 (v'43&ᵢ$ 7)
                           :: Vint32 (v'43 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil) **
   LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (next_tcb_block, Int.zero) **
   Astruct (next_tcb_block, Int.zero) OS_TCB_flag
     (v'14
      :: Vptr (prev_tcb_block, Int.zero)
         :: x25
            :: x24
               :: Vint32 i12
                  :: Vint32 i11
                     :: Vint32 i10
                        :: Vint32 i9
                           :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil) **
   Astruct (prev_tcb_block, Int.zero) OS_TCB_flag
     (Vptr (next_tcb_block, Int.zero)
      :: v'13
         :: x26
            :: x22
               :: Vint32 i20
                  :: Vint32 i19
                     :: Vint32 i18
                        :: Vint32 i17
                           :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil) **
   dllseg v'9 Vnull v'13 (Vptr (prev_tcb_block, Int.zero)) v'28 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   dllseg v'14 (Vptr (next_tcb_block, Int.zero)) v'12 Vnull l2' OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
     (update_nth_val (Z.to_nat (Int.unsigned v'43)) priotbl Vnull) **
   PV vhold @ Int8u |-> v'8 **
   HECBList v'16 **
   (* HTCBList tcbmap ** *)
   HTime v'18 **
   (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
   LV pevent @ OS_EVENT ∗ |-> Vnull **
   GV OSRdyGrp @ Int8u |-> Vint32 v'40 **
   GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'30
        (val_inj (and (Vint32 v'41) (Vint32 (Int.not ($ 1<<ᵢ(v'43&ᵢ$ 7))))))) **
   GV OSTCBList @ OS_TCB ∗ |-> v'9 **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
   (* Aie false ** *)
   (* Ais nil ** *)
   (* Acs (true :: nil) ** *)
   (* Aisr empisr ** *)
   AECBList v'7 v'6 v'16 tcbmap **
   tcbdllflag v'9
     ((v :: l1') ++
      (Vptr (next_tcb_block, Int.zero)
       :: Vptr (prev_tcb_block, Int.zero)
          :: Vnull
             :: x0
                :: Vint32 i13
                   :: V$ OS_STAT_RDY
                      :: Vint32 v'43
                         :: Vint32 (v'43&ᵢ$ 7)
                            :: Vint32 (v'43 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3)) :: nil)
      :: (v'14
          :: Vptr (todelblock, Int.zero)
             :: x25
                :: x24
                   :: Vint32 i12
                      :: Vint32 i11
                         :: Vint32 i10
                            :: Vint32 i9
                               :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
         :: l2') **
   G& OSPlaceHolder @ Int8u == vhold **
   (* A_isr_is_prop ** *)
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   LV self @ Int8u |-> (V$ 0) **
   AOSEventFreeList v'3 **
   AOSQFreeList v'4 **
   AOSQFreeBlk v'5 **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSIntNesting **
   sll v'20 v'21 OS_TCB_flag V_OSTCBNext **
   sllfreeflag v'20 v'21 **
   AOSTime (Vint32 v'18) **
   AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'43)).
      clear.
      intro; intros.
      sep lifts (4:: 6::nil)%nat. 
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.

      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (todelblock, Int.zero) (v'43, x , x0) mmm tcbmap).
      apply tcb_get_join.
      unfold get, sig, join in *; simpl in *.
      unfold get, sig, join in *; simpl in *.
      go.

      destruct H75 as (tcbmap_left & tcbmapleft_join_hyp).


      eapply seq_rule.
      eapply derive_delother_rule.
      apply goodlinv.

       (* goodlinv *)
      go.
      (* unfold AEventData. *)
      (* destruct x22; go. *)
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      exact tcbmapleft_join_hyp.
      clear -H3; unfolds in H3.
      unfolds.
      simpljoin.
      eauto.
      intro; tryfalse.
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H75.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.
      hoare lift 28%nat pre.
      eapply backward_rule1.
      eapply dllsegflag_split.
      hoare_split_pure_all.
      unfold dllsegflag at 2.
      fold dllsegflag .
      hoare_split_pure_all.
      inverts H102.
      inverts H100.
      inverts H101.
      inverts H103.
      rewrite H73.

      (* Lemma dllsegflag_last_next_is_endstnl:
       *   forall l head endstnl endp next s P,
       *     s |= dllsegflag head endstnl (l++ (endp :: nil)) next  ** P ->
       *     next endp = Some endstnl.
       * Proof.
       *   induction l.
       *   intros.
       *   simpl (nil ++ endp :: nil) in H.
       *   unfold dllsegflag in H.
       *   sep normal in H.
       *   sep destruct H.
       *   sep split in H.
       *   subst.
       *   auto.
       * 
       *   intros.
       *   simpl ((a ::l ) ++ endp :: nil) in H.
       *   unfold1 dllsegflag in H.
       *   
       *   sep normal in H.
       *   sep destruct H.
       *   sep split in H.
       *   sep lift 2%nat in H.
       *   eapply IHl.
       *   eauto.
       * Qed. *)

      hoare_assert_pure ( (fun vl : vallist => nth_val 0 vl) (Vptr (todelblock, Int.zero)
                                                                   :: v'13
                                                                   :: x26
                                                                   :: x22
                                                                   :: Vint32 i20
                                                                   :: Vint32 i19
                                                                   :: Vint32 i18
                                                                   :: Vint32 i17
                                                                   :: Vint32 i16
                                                                   :: Vint32 i15 :: Vint32 i14 :: nil) = Some (Vptr v'38) ).
      eapply dllsegflag_last_next_is_endstnl.
      instantiate (4 := s0).
      sep cancel 5%nat 1%nat.
      eauto.

      hoare_split_pure_all.
      inverts H100.

      
      
      (* rewrite app_nil_l. *)
      (* hoare unfold. *)
      (* hoare lift 4%nat pre. *)
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      hoare_split_pure_all.
      (* unfold1 dllseg. *)
      (* hoare unfold. *)
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 24)  ) in H102.
      eauto.

      hoare lift 5%nat pre.
      eapply seq_rule.
      eapply assign_rule'.
      Focus 2.

      intro; intros.
      split.
      eapply field_asrt_impl.
      Focus 3.
      sep cancel 13%nat 1%nat.
      eauto.
      reflexivity.
      reflexivity.
      sep get rv.
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep lift 30%nat in H102.
      unfold OSLInv in H102.
      sep normal in H102.
      sep destruct H102.
      sep split in H102.
      unfold init_lg in H100; destruct H100.
      inverts H100.
      sep cancel 1%nat 1%nat.
      eauto.

      simpl; auto.
      splits; eauto.
      unfolds; auto.
      

      eapply backward_rule1.
      intro; intros.
      sep lifts (8::10::nil)%nat in H102.
      eapply add_a_isr_is_prop in H102.
      eauto.
      hoare lift 4%nat pre.
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep cancel OSLInv.
      eapply poi_OSINV_imply_OSInv.
      unfold poi_OSINV.
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
      unfold AECBList in H102.
      unfold AECBList.
      instantiate (14 := v'7).
      instantiate (13 := v'6).
(* instantiate (x3 := (x11 ++ (Vint32 i7 :: Vint32 v'50 :: Vint32 i8 :: x29 :: x30 :: v'6 :: nil,
 *                                  (update_nth_val (Z.to_nat (Int.unsigned (v'53 >>ᵢ $ 3))) v'37
 *                                                  (val_inj
 *                                                     (and (Vint32 v'51) (Vint32 (Int.not ($ 1<<ᵢ(v'53&ᵢ$ 7)))))))
 *                                 ) :: x15)).
 *       instantiate (x2 :=(x23 ++ x22 :: x24) ). *)


      (* instantiate (x3 := (x5 ++ (Vint32 i8 :: Vint32 v'53 :: Vint32 i9 :: x29 :: x30 :: v'6 :: nil,
       *                            (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
       *                                            (val_inj
       *                                               (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
       *                           ) :: x15)).
       * instantiate (x2 :=(x23 ++ x22 :: x24) ). *)
      sep pauto.
      (* eapply evsllseg_merge.
       *       eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H80).
       * eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H81).
       * 
       * (* admit.
       *  * admit. *)
       * unfold1 evsllseg .
       * sep pauto.
       * unfold AEventNode.
       * sep cancel evsllseg.
       * sep cancel evsllseg.
       * unfold AOSEvent.
       * unfold node.
       * unfold AOSEventTbl.
       * sep pauto.
       * sep cancel Aarray.
       * 
       * sep lift 2%nat.
       * eapply AED_changegrp.
       * sep cancel AEventData.
       * unfold Astruct.
       * unfold OS_EVENT.
       * unfold Astruct'.
       * sep normal.
       * sep cancel 16%nat 2%nat.
       * repeat sep cancel 16%nat 1%nat. *)
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 20%nat 2%nat.
      sep cancel 14%nat 1%nat.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold poi_AOSTCBList.
      
      sep pauto.
      instantiate (4 := (
(v'28 ++
               (Vptr (next_tcb_block, Int.zero)
                :: v'13
                   :: x26
                      :: x22
                         :: Vint32 i20
                            :: Vint32 i19
                               :: Vint32 i18
                                  :: Vint32 i17
                                     :: Vint32 i16
                                        :: Vint32 i15 :: Vint32 i14 :: nil)
               :: nil)  ++
                         (v'44
               :: Vptr (prev_tcb_block, Int.zero)
                  :: x25
                     :: x24
                        :: Vint32 i12
                           :: Vint32 i11
                              :: Vint32 i10
                                 :: Vint32 i9
                                    :: Vint32 i8
                                       :: Vint32 i7 :: Vint32 i :: nil) 
                          
                            :: l2')).
      unfold tcbdllseg.
      unfold tcbdllflag.
      unfold1 dllsegflag.
      unfold1 dllseg.
      unfold node.
      sep pauto.

      
      (* unfold TCB_Not_In.
       * sep pauto.
       * eapply tcbdllseg_compose.
       * unfold tcbdllseg.
       * unfold1 dllseg.
       * unfold node.
       * sep pauto.
       * sep cancel 10%nat 1%nat.
       * sep cancel 12%nat 1%nat. *)
      (* Goal forall l head headprev tail tailnext x t fprev fnext,
       *        dllseg head headprev tail tailnext (l++x::nil) t fprev fnext <==>
       *               EX tail', dllseg head headprev tail' tail l t fprev fnext **
       *                                [| |] *)
      eapply dllseg_is_poi.
      eapply split_poillseg.
      sep eexists.
      eapply split_poillseg.
      sep eexists.
      rewrite <- dllseg_is_poi.
      sep lift 2%nat.
      rewrite <- dllseg_is_poi.
      sep lift 3%nat.
      rewrite <- dllseg_is_poi.
      unfold1 dllseg.
      unfold node.
      sep normal.
      sep eexists.
      instantiate (22 := prev_tcb_block).
      instantiate (4 := Vptr (prev_tcb_block, Int.zero)).
      instantiate (4 := v'13).
      instantiate (15 := Vptr (next_tcb_block, Int.zero)).
      instantiate (4 := Vptr (next_tcb_block, Int.zero)).
      instantiate (6 := Vptr (prev_tcb_block, Int.zero)).
      instantiate (7 := next_tcb_block).

      sep pauto.
      sep cancel 11%nat 1%nat.
      sep cancel 10%nat 1%nat.
      (* sep cancel 11%nat 1%nat. *)
      (* sep cancel dllseg. *)

      sep lift 4%nat in H102.
      rewrite dllsegflag_is_poi in H102.
      apply split_poillseg in H102.
      sep destruct H102.
      apply dllsegflag_is_poi.
      apply split_poillseg.
      sep eexists.
      apply split_poillseg.
      sep eexists.
      sep pauto.
      sep cancel 1%nat 1%nat.
      unfold1 @poi_llseg in *.
      sep normal in H102; sep destruct H102.
      sep normal; sep eexists.
      instantiate (5 := Vptr (next_tcb_block, Int.zero)).
      sep pauto.
      2: go.
      sep lift 2%nat.
      rewrite <- dllsegflag_is_poi.
      sep cancel dllsegflag.
      (* instantiate (x1 := x14). *)
      sep cancel 1%nat 2%nat.
      sep cancel 2%nat 1%nat.

      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_l. 
      unfold TCBFree_Not_Eq.
      sep pauto.
      instantiate ( 2 := (
(v'20
               :: Vptr (prev_tcb_block, Int.zero)
                  :: Vnull
                     :: x0
                        :: V$ 0
                           :: V$ OS_STAT_RDY
                              :: Vint32 v'43
                                 :: Vint32 (v'43&ᵢ$ 7)
                                    :: Vint32 (v'43 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'43&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'43 >>ᵢ $ 3))
                                             :: nil) :: v'21
                            
                          )).
      unfold1 sll.
      unfold1 sllfreeflag.
      unfold1 sllseg.
      unfold1 sllsegfreeflag.
      
      sep pauto.
      unfold node.
      unfold sll, sllfreeflag in H102.
      sep pauto.
      sep cancel sllsegfreeflag.
      sep cancel sllseg.
      sep cancel Astruct.
      eauto.
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      unfold sll.
      sep cancel sllseg.
      go.
      go.
      
      go.
      intro; tryfalse.
      (* intro; tryfalse. *)
      go.
      go.
      go.
      intro; tryfalse.
      (* intro; tryfalse.
       * go.
       * go.
       * go.
       * go.
       * go.
       * go.
       * intro; tryfalse. *)
      {


         eapply TCBList_merge_prop.
         instantiate (2 := v'17).
         instantiate (1 := x13).

         eapply some_join_lemma0; eauto.
         exact H22.
         exact tcbmapleft_join_hyp.
                  
  (* H22 : TcbJoin (cur_tcb_blk, Int.zero)
   *         (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0) x13 v'19
   * H28 : TcbMod.join v'17 v'19 tcbmap
   * tcbmapleft_join_hyp : TcbJoin (cur_tcb_blk, Int.zero)
   *                         (v'53, wait (hle2wait x (v'15, Int.zero)) i13, x0)
   *                         tcbmap_left tcbmap
   * 
   *         *)
         rewrite app_last.
         simpl.
         go.
         Focus 2.

         eapply  tcblist_p_hold_for_del_a_tcb_at_head .
         omega.

        2:go.
        2:go.
        2: exact H22.
        2: exact backup.
        unfolds in H6.
        simpljoin.
        clear -H105 H28.
        eapply R_Prio_No_Dup_hold_for_subset.
        apply TcbMod.join_comm; eauto.
        eauto.

        
        eapply OSTimeDlyPure.update_rtbl_tcblist_hold.

        omega.
        unfold nat_of_Z; eapply nv'2nv.
        exact H60.
        intro; tryfalse.
        intros.

        unfolds in H6.
        simpljoin.
        clear -H28 H22 H106 H104.
        eapply H106.
        instantiate (2 := tid).
        instantiate (1 := (todelblock, Int.zero)).
        intro; subst tid.
        eapply TcbMod.map_join_get_some.
        auto.
        exact H28.
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        go.
        
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        go.
        
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        unfold get; simpl.
        go.
        unfold TcbJoin in H22.
        unfold join,sig,get in H22; simpl in H22.
        unfold get; simpl.
        go.
        eapply TCBList_P_hold_for_last_change.
        rewrite H73 in H29.
        exact H29.
        
      }
       (* tcblist_p hold for deleting a tcb *)

      {
        assert (list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) (v'28 ++
         (Vptr (todelblock, Int.zero)
          :: v'13
             :: x26
                :: x22
                   :: Vint32 i20
                      :: Vint32 i19
                         :: Vint32 i18
                            :: Vint32 i17
                               :: Vint32 i16
                                  :: Vint32 i15 :: Vint32 i14 :: nil) :: nil
                                                                         )).

 eapply TCBLP_imply_nextnotnull_list.
 rewrite H73 in H29.
 exact H29.
 rewrite  get_last_tcb_ptr_appsig.
 eauto.


 
        eapply  ptr_in_tcblist_app in H24.
        destruct H24.
        apply  ptr_in_tcblist_app.

        2: left; eapply ptr_in_tcblist_last_ir.
        apply  list_all_P_app.
        apply  list_all_P_app in H104.
        simpljoin.
        splits; auto.
        simpl; go.
        (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)
        rewrite H73 in H24; exact H24.

        
        apply  ptr_in_tcblist_app.

        apply  list_all_P_app.
        apply  list_all_P_app in H104.
        simpljoin.
        splits; auto.
        simpl; go.
        (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)

        right.
        
        rewrite          get_last_tcb_ptr_appsig.
        rewrite H73 in H24.
        rewrite          get_last_tcb_ptr_appsig in H24.
        eapply  ptr_in_tcbdllseg_change_head.
        Focus 2.
        eapply ptr_in_tcbdllseg_not_head. 
        2: exact H24.
        reflexivity.
        simpl; intro; tryfalse.
        reflexivity.
        rewrite H73.
        exact H104.
        
      }
       (* from tcblist_p, get they are all different? *)
      split.
      assumption.
      eapply (H68 _ H55).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.
        
      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        omega.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .

      }

       (* r_priotbl_p hold for deleting a tcb *)
      
{
  eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
  omega.
  rewrite Int.repr_unsigned.
  reflexivity.

  rewrite Int.repr_unsigned.
  reflexivity.

  2: assumption.
  unfold nat_of_Z.
  apply nv'2nv.
  
  assumption.
  intro; tryfalse.
  
      }

       (* rl_rtbl_ptbl_p hold for deleting a tcb *)

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.



      {
      assert (forall ecbid, ~ exists bb cc, x = wait bb cc /\ isWait4Ecb bb ecbid ). 
      intros.
      intro.
      simpljoin.
      
      gen H105.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.

      eapply ECBLP_hold4del_a_tcb_rdy; eauto.
      }
       (* from H101 : RL_Tbl_Grp_P
           (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
              (val_inj
                 (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
           (Vint32 v'53), ECBList_P holds for deleting a tcb *)
      {
        rewrite <- poi_is_rtep.
        rewrite <- poi_is_rtep in H2.

        eapply poi_RH_T_E_P_hold_for_tcbdel_rdy; eauto.
      intros.
      intro.
      simpljoin.
      
      gen H104.
      eapply lowready_not_wait4ecb.
      lets bb: H64 (eq_refl ($ OS_STAT_RDY)).
      subst x23.
      exact H53.
      }
      go.
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      inverts H103.
      reflexivity.
    }
  }


    Unshelve.
    exact (Afalse).
    exact   cur_tcb_blk .
    exact   cur_tcb_blk .
    exact   cur_tcb_blk .
    exact   cur_tcb_blk .

Qed.
