(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(********** Proof of Internal Fucntion: void OSTimeTick() ************)
(**************************** Code:***********************************)
(*
 Void ·OSTimeTick·(⌞ ⌟)··{
        ⌞ptcb @ OS_TCB∗;
         pevent @ OS_EVENT∗;
         ptbl @ Tptr Int8u⌟;
         
1        ++OSTime′;ₛ
2        ptcb′ =ₑ OSTCBList′;ₛ
3        WHILE (ptcb′ !=ₑ NULL)
         {
4          If (ptcb′→ OSTCBDly !=ₑ ′0)
           {
5               ptcb′→OSTCBDly =ₑ (ptcb′→OSTCBDly) − ′1;ₛ
6               If (ptcb′→OSTCBDly ==ₑ ′0)
                {
7                 OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ ptcb′→OSTCBBitY;ₛ
8                OSRdyTbl′[ptcb′→OSTCBY] =ₑ OSRdyTbl′[ptcb′→OSTCBY] |ₑ ptcb′→OSTCBBitX;ₛ
9                 ptcb′→OSTCBStat =ₑ ′OS_STAT_RDY;ₛ
10                pevent′ =ₑ ptcb′→OSTCBEventPtr;ₛ
11                If (pevent′ !=ₑ NULL)
                 {
12                 ptbl′ =ₑ pevent′→OSEventTbl;ₛ
13                 ptbl′[ptcb′→OSTCBY] =ₑ 
                           ptbl′[ptcb′→OSTCBY] &ₑ (∼ptcb′→OSTCBBitX);ₛ
14                 If (ptbl′[ptcb′→OSTCBY] ==ₑ ′0)
                   {
15                    pevent′→OSEventGrp &=  ∼ptcb′→OSTCBBitY
                   };ₛ
16                 ptcb′→OSTCBEventPtr =ₑ NULL
                 }
               }
           };ₛ
17          ptcb′ =ₑ ptcb′→OSTCBNext
        };ₛ
18      RETURN
 }·.
*)
Require Import ucos_include.
Require Import OSTimeTickPure.
Require Import OSTimeDlyPure.
Require Import ucos_common.
Require Import oscore_common.
Require Import os_ucos_h.
Open Scope code_scope.

Lemma OSTimeTick_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSTimeTick
                  vl logicl OSTimeTickPre ct ->
      Some r =
      BuildRetI os_internal OSTimeTick vl logicl OSTimeTickPost ct ->
      exists t d1 d2 s,
        os_internal OSTimeTick = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  unfold OSTimeTickPre'.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AECBList.
  pure_intro'.
  rename v'20 into vcode.
  rename v'23 into v'20.
  rename H10 into Hidle.
  rename H11 into H10.
  hoare forward.
  (* intro;tryfalse. *)
  hoare forward.
  eapply backward_rule1.
  intros.
  sep lifts (12::14::nil)%nat in H.

  eapply tcbdllseg_compose' in H.
  exact H.
  pure_intro'.
  remember (v'5 ++ v'6 :: v'7) as tcbl.
  apply backward_rule1 with (p:=
  EX tail1 tcbl1 tcbl2 x tcbl1' rtbl' rgrp' ectrl' v'0 v'1,
     [| tcbl = tcbl1 ++ tcbl2|] **
     tcbdllseg (Vptr v'4) Vnull tail1 x tcbl1' **
     tcbdllseg x tail1 v'12 Vnull tcbl2 **
     evsllseg v'20 Vnull ectrl' v'17 **
     [| tcbls_rtbl_timetci_update tcbl1 v'8 (Vint32 i) v'20 v'16= Some (tcbl1',rtbl',Vint32 rgrp',ectrl')|] **
     <|| vcode ||>  **
     LV ptcb @ OS_TCB ∗ |-> x **
     LV pevent @ OS_EVENT ∗ |-> v'0 **
     LV ptbl @ (Int8u) ∗ |-> v'1 **
     A_dom_lenv ((ptcb, OS_TCB ∗) :: (pevent, OS_EVENT ∗) ::  (ptbl, (Int8u) ∗) :: nil)  **
     GV OSEventList @ OS_EVENT ∗ |-> v'20 **
     GV OSTime @ Int32u |-> Vint32 (Int.add v'10 Int.one) **
     Aisr (isrupd v'2 0%nat false) **
     Aie false **
     Ais (0%nat :: v'3) **
     Acs nil **
     GV OSTCBList @ OS_TCB ∗ |-> Vptr v'4 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
     GAarray OSRdyTbl (Tarray Int8u ∘OS_RDY_TBL_SIZE) rtbl' **
     GV OSRdyGrp @ Int8u |-> Vint32 rgrp' ** p_local OSLInv ct (logic_val v'22 :: nil)).
  intros.
  exists Vnull (nil:list vallist) tcbl (Vptr v'4) (nil:list vallist).
  exists v'8 i v'16 v'0 v'1.

  sep semiauto.
  unfold tcbdllseg at 1.
  unfold dllseg.
  sep auto.
  
  eapply seq_rule.
  eapply while_rule.
  intros.

  sep normal in H11.
  sep destruct H11.
  sep lift 3%nat in H11.
  unfold tcbdllseg in H11.
  lets Hisptr: dllseg_head_isptr H11.

  symbolic execution;pauto.
  Focus 2.
  pure_intro'.
  eapply backward_rule1.
  intros.
  destruct H11.

  sep lift 6%nat in H11.
  lets Hx:neq_null_false_elim H11 H12.
  subst v'25.

  instantiate (1:= LV ptcb @ OS_TCB ∗ |-> Vnull **
           tcbdllseg (Vptr v'4) Vnull v'9 Vnull v'26 **
           tcbdllseg Vnull v'9 v'12 Vnull v'24 **
           evsllseg v'20 Vnull v'29 v'17 **
           [|tcbls_rtbl_timetci_update v'23 v'8 (Vint32 i) v'20 v'16 =
             Some (v'26, v'27, Vint32 v'28, v'29)|] **
            <|| vcode ||>  **
           LV pevent @ OS_EVENT ∗ |-> v'30 **
           LV ptbl @ (Int8u) ∗ |-> v'31 **
           A_dom_lenv
             ((ptcb, OS_TCB ∗)
              :: (pevent, OS_EVENT ∗) :: (ptbl, (Int8u) ∗) :: nil) **
           GV OSEventList @ OS_EVENT ∗ |-> v'20 **
           GV OSTime @ Int32u |-> Vint32 (v'10 +ᵢ  Int.one) **
           Aisr (isrupd v'2 0%nat false) **
           Aie false **
           Ais (0%nat :: v'3) **
           Acs nil **
           GV OSTCBList @ OS_TCB ∗ |-> Vptr v'4 **
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) v'27 **
           GV OSRdyGrp @ Int8u |-> Vint32 v'28 **
           p_local OSLInv ct (logic_val v'22 :: nil) **
           [|v'5 ++ v'6 :: v'7 = v'23 ++ v'24|]).
  auto.
  unfold OSTimeTickPost'.
  unfold tcbdllseg at 3.

  eapply backward_rule1.
  intros.
  sep lift 3%nat in H11.
  lets Hx:dllseg_head_null_elim H11.
  destruct Hx;subst.
  instantiate (1:=
       LV ptcb @ OS_TCB ∗ |-> Vnull **
           tcbdllseg (Vptr v'4) Vnull v'12 Vnull v'26 **
           evsllseg v'20 Vnull v'29 v'17 **
           [|tcbls_rtbl_timetci_update v'23 v'8 (Vint32 i) v'20 v'16 =
             Some (v'26, v'27, Vint32 v'28, v'29)|] **
            <|| vcode ||>  **
           LV pevent @ OS_EVENT ∗ |-> v'30 **
           LV ptbl @ (Int8u) ∗ |-> v'31 **
           A_dom_lenv
             ((ptcb, OS_TCB ∗)
              :: (pevent, OS_EVENT ∗) :: (ptbl, (Int8u) ∗) :: nil) **
           GV OSEventList @ OS_EVENT ∗ |-> v'20 **
           GV OSTime @ Int32u |-> Vint32 (v'10+ᵢInt.one) **
           Aisr (isrupd v'2 0%nat false) **
           Aie false **
           Ais (0%nat :: v'3) **
           Acs nil **
           GV OSTCBList @ OS_TCB ∗ |-> Vptr v'4 **
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
           GAarray OSRdyTbl (Tarray Int8u ∘OS_RDY_TBL_SIZE) v'27 **
           GV OSRdyGrp @ Int8u |-> Vint32 v'28 **
           p_local OSLInv ct (logic_val v'22 :: nil) **
           [|v'5 ++ v'6 :: v'7 = v'23 ++ nil|]).
  simpl dllseg in H11.
  sep semiauto.
  pure_intro'.
  rewrite List.app_nil_r in H12;subst.
  apply ret_rule'.
  intros.
  sep normal.
  sep eexists.
  sep normal in H12.
  sep split in H12.
  sep split.
  Focus 21.
  auto.
  sep semiauto.
  sep lift 2%nat;eauto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  eapply timetick_idle_in_rtbl;eauto.
  eapply TCBList_P_imp_RL;eauto.
  eapply OSQPostPure.TCBList_P_Combine;eauto.
  clear -H.
  destruct H.
  Import DeprecatedTactic.
  mytac;subst;simpl;auto.
  inverts H0.
  auto.
  mytac.
  unfolds.
  destruct v'5;tryfalse;simpl;auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  eauto.
  auto.
  auto.
  auto.
  (* while body *)
  remember (
    logic_isr v'2
      :: logic_is v'3
         :: logic_val (Vint32 v'10)
            :: logic_val (Vptr v'4)
               :: logic_val (Vptr v'4)
                  :: logic_llv v'5
                     :: logic_lv v'6
                        :: logic_llv v'7
                           :: logic_lv v'8
                              :: logic_val (Vint32 i)
                                 :: logic_val v'11
                                    :: logic_val v'12
                                       :: logic_abstcb v'13
                                          :: logic_abstcb v'14
                                             :: logic_abstcb v'15
                                                :: 
                                                logic_leventc v'16
                                                :: 
                                                logic_leventd v'17
                                                :: 
                                                logic_absecb v'18
                                                :: 
                                                logic_code vcode
                                                :: 
                                                logic_val (Vptr v'21)
                                                :: 
                                                logic_val v'22 :: nil) as ll.
  clear Heqll.
  
  pure_intro'.

  eapply backward_rule1.
  intros.
  destruct H11.
  sep lift 6%nat in H11.
  lets Hx:neq_null_true_elim H11 H12.
  instantiate (1:=LV ptcb @ OS_TCB ∗ |-> v'25 **
           tcbdllseg (Vptr v'4) Vnull v'9 v'25 v'26 **
           tcbdllseg v'25 v'9 v'12 Vnull v'24 **
           evsllseg v'20 Vnull v'29 v'17 **
           [|tcbls_rtbl_timetci_update v'23 v'8 (Vint32 i) v'20 v'16 =
             Some (v'26, v'27, Vint32 v'28, v'29)|] **
            <|| vcode ||>  **
           LV pevent @ OS_EVENT ∗ |-> v'30 **
           LV ptbl @ (Int8u) ∗ |-> v'31 **
           A_dom_lenv
             ((ptcb, OS_TCB ∗)
              :: (pevent, OS_EVENT ∗) :: (ptbl, (Int8u) ∗) :: nil) **
           GV OSEventList @ OS_EVENT ∗ |-> v'20 **
           GV OSTime @ Int32u |-> Vint32 (v'10 +ᵢ  Int.one) **
           Aisr (isrupd v'2 0%nat false) **
           Aie false **
           Ais (0%nat :: v'3) **
           Acs nil **
           GV OSTCBList @ OS_TCB ∗ |-> Vptr v'4 **
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) v'27 **
           GV OSRdyGrp @ Int8u |-> Vint32 v'28 **
           p_local OSLInv ct (logic_val v'22 :: nil) **
           [|v'5 ++ v'6 :: v'7 = v'23 ++ v'24|] ** [| v'25 <> Vnull |]).
  clear H12.
  sep semiauto.
  pure_intro'.
  destruct v'24.
  unfold tcbdllseg at 3.
  unfold dllseg.
  pure_intro'.
  tryfalse.
  hoare lift 3%nat pre.
  unfold tcbdllseg at 2.
  unfold dllseg;fold dllseg.
  unfold node.

  pure_intro'.
  
  hoare forward.
  (* intro;tryfalse. *)
  go.
  destruct (Int.eq i6 ($ 0));simpl;intro;tryfalse.
  destruct (Int.eq i6 ($ 0));simpl;intro;tryfalse.

  hoare forward.
  (* intro;tryfalse. *)
  go.
  (* intro;tryfalse. *)
  hoare forward.
  (* intro;tryfalse. *)
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  destruct H16.
  destruct (Int.eq i6  ($ 0)).
  
  simpl in H16.
  unfold Int.notbool in H16.
  rewrite eq_one_zero in H16.
  tryfalse.
  auto.
  pauto.
  rtmatch_solve.
  splits;pauto.
  pauto.
  (* destruct (Int.eq (i6 -ᵢ $ 1) ($ 0));simpl;intro;tryfalse. *)
  lets Hx: tcblist_p_recombine H0 H1 H2 H12;auto.
  mytac.
  lets Hx:timetick_update_prop H6 H10 H7 H8 H11.
  exact H15.

  
  mytac.
  hoare forward.
  rtmatch_solve.
  (* intro;tryfalse. *)
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  destruct H32.
  destruct (Int.eq i6  ($ 0)).
  
  simpl in H32.
  unfold Int.notbool in H32.
  rewrite eq_one_zero in H32.
  tryfalse.
  auto.
  pauto.
  rtmatch_solve.
  splits;pauto.
  (* intro;tryfalse. *)

  lets Hrltcbblk: tcbnode_rl_prop H0 H1 H2 H12.
  lets Hi2:rl_tcbblk_tcby_range Hrltcbblk.
  hoare forward.
  (* intro;tryfalse. *)
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  destruct H32.
  destruct (Int.eq i6  ($ 0)).
  
  simpl in H32.
  unfold Int.notbool in H32.
  rewrite eq_one_zero in H32.
  tryfalse.
  auto.
  pauto.
  rtmatch_solve.
  splits;pauto.
   

  rewrite H28;simpl.
  auto.
(* ** ac:   Locate array_type_vallist_match_imp_rule_type_val_match. *)
  Require Import symbolic_lemmas.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H28.
  unfold OS_RDY_TBL_SIZE.
  simpl.
  unfold Pos.to_nat.
  unfold  Pos.iter_op.
  simpl.
  apply ge0_z_nat_le.
  lets Hx: Int.unsigned_range i2.
  omega.
  simpl.
  auto.
  (* intro;tryfalse. *)
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  destruct H32.
  destruct (Int.eq i6  ($ 0)).
  
  simpl in H32.
  unfold Int.notbool in H32.
  rewrite eq_one_zero in H32.
  tryfalse.
  auto.
  rtmatch_solve.
  rtmatch_solve.
  splits;try solve [rtmatch_solve].
  auto.

  assert (rule_type_val_match Int8u (nth_val' (Z.to_nat (Int.unsigned i2)) v'27) =true).
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H28.
  unfold OS_RDY_TBL_SIZE.
  simpl.
  unfold Pos.to_nat.
  unfold  Pos.iter_op.
  simpl.
  apply ge0_z_nat_le.
  lets Hx: Int.unsigned_range i2.
  omega.
  simpl.
  auto.
  simpl in H32.
  destruct (nth_val' (Z.to_nat (Int.unsigned i2)) v'27);tryfalse.
  simpl;auto.
  (* intro;tryfalse. *)
  (* intro;tryfalse. *)

  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  destruct H32.
  destruct (Int.eq i6  ($ 0)).
  
  simpl in H32.
  unfold Int.notbool in H32.
  rewrite eq_one_zero in H32.
  tryfalse.
  auto.
  pauto.
  rtmatch_solve.
  splits;pauto.
  
  simpl.
  auto.
  rewrite H28;simpl;auto.
  pure_intro'.
  assert (Int.eq i6 ($ 0) = false).
  clear -H31.
  destruct (Int.eq i6 ($ 0));simpl in H31;auto.
  unfold Int.notbool in H31.
  assert (Int.eq Int.one Int.zero = false).
  int auto.
  rewrite H in H31.
  tryfalse.
  clear H31 H36 H35.
  assert (Int.eq (i6-ᵢ$ 1) ($ 0) =true).
  clear -H32.
  destruct (Int.eq (i6-ᵢ$ 1) ($ 0));simpl in H32;tryfalse;auto.
  clear H34 H32 H33.
  hoare forward.
  
  hoare forward.
  (* intro;tryfalse. *)
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  pauto.
  pauto.
  splits;pauto.
  Require Import List.
  instantiate
    (1:= EX ectrl' vx,
     <|| vcode ||>  **
     LV pevent @ OS_EVENT ∗ |-> x7 **
     LV ptcb @ OS_TCB ∗ |-> Vptr (v'33, Int.zero) **
     Astruct (v'33, Int.zero) OS_TCB_flag
       (v'32
        :: (v'9
            :: Vnull
               :: x6
                  :: Vint32 (i6 -ᵢ $ 1)
                     :: V$ OS_STAT_RDY
                        :: Vint32 i4
                           :: Vint32 i3
                              :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)) **
       [| RL_TCBblk_P   (v'32
        :: (v'9
            :: Vnull
               :: x6
                  :: Vint32 (i6 -ᵢ $ 1)
                     :: V$ OS_STAT_RDY
                        :: Vint32 i4
                           :: Vint32 i3
                              :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil))|] **
     A_dom_lenv
       ((ptcb, OS_TCB ∗) :: (pevent, OS_EVENT ∗) :: (ptbl, (Int8u) ∗) :: nil) **
     GAarray OSRdyTbl (Tarray Int8u ∘OS_RDY_TBL_SIZE)
       (update_nth_val (Z.to_nat (Int.unsigned i2)) v'27
          (val_inj
             (or (nth_val' (Z.to_nat (Int.unsigned i2)) v'27) (Vint32 i1)))) **
     GV OSRdyGrp @ Int8u |-> Vint32 (Int.or v'28 i0) **
     dllseg v'32 (Vptr (v'33, Int.zero)) v'12 Vnull v'24 OS_TCB_flag
       (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
       tcbdllseg (Vptr v'4) Vnull v'9 (Vptr (v'33, Int.zero)) v'26 **
     [|tick_rdy_ectr   (v'32
        :: (v'9
            :: x7
               :: x6
                  :: Vint32 (i6 -ᵢ $ 1)
                     :: V$ OS_STAT_RDY
                        :: Vint32 i4
                           :: Vint32 i3
                              :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)) v'20 v'29 = Some ectrl'|] **
     evsllseg v'20 Vnull ectrl' v'17 **
     LV ptbl @ (Int8u) ∗ |-> vx **
     GV OSEventList @ OS_EVENT ∗ |-> v'20 **
     GV OSTime @ Int32u |-> Vint32 (v'10+ᵢInt.one) **
     Aisr (isrupd v'2 0%nat false) **
     Aie false **
     Ais (0%nat :: v'3) **
     Acs nil **
     GV OSTCBList @ OS_TCB ∗ |-> Vptr v'4 ** GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
     p_local OSLInv ct (logic_val v'22 :: nil) ).

  hoare_assert_pure (vl_elem_neq (get_eid_list v'20 v'29)).
  sep lift 10%nat in H32.
  eapply evsllseg_eid_neq;eauto.
  pure_intro'.
  rename H32 into Heidneq.
  eapply forward_rule2.
  hoare forward.
  pauto.
  pauto.
  pauto.
  instantiate
    (1:= EX ectrl' vx,
         <|| vcode ||>  **
             LV pevent @ OS_EVENT ∗ |-> x7 **
             LV ptcb @ OS_TCB ∗ |-> Vptr (v'33, Int.zero) **
             Astruct (v'33, Int.zero) OS_TCB_flag
             (v'32
         :: v'9
            :: Vnull
               :: x6
                  :: Vint32 (i6 -ᵢ $ 1)
                     :: V$ OS_STAT_RDY
                        :: Vint32 i4
                           :: Vint32 i3
                              :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) **
             A_dom_lenv
             ((ptcb, OS_TCB ∗) :: (pevent, OS_EVENT ∗) :: (ptbl, (Int8u) ∗) :: nil) **
             GAarray OSRdyTbl (Tarray Int8u ∘OS_RDY_TBL_SIZE)
             (update_nth_val (Z.to_nat (Int.unsigned i2)) v'27
                             (val_inj
                                (or (nth_val' (Z.to_nat (Int.unsigned i2)) v'27) (Vint32 i1)))) **
             GV OSRdyGrp @ Int8u |-> Vint32 (Int.or v'28 i0) **
             dllseg v'32 (Vptr (v'33, Int.zero)) v'12 Vnull v'24 OS_TCB_flag
             (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
             tcbdllseg (Vptr v'4) Vnull v'9 (Vptr (v'33, Int.zero)) v'26 **
             [|tick_rdy_ectr  (v'32
         :: v'9
            :: x7
               :: x6
                  :: Vint32 (i6 -ᵢ $ 1)
                     :: V$ OS_STAT_RDY
                        :: Vint32 i4
                           :: Vint32 i3
                              :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) v'20 v'29 = Some ectrl'|] **
             evsllseg v'20 Vnull ectrl' v'17 **
             LV ptbl @ (Int8u) ∗ |-> vx **
             GV OSEventList @ OS_EVENT ∗ |-> v'20 **
             GV OSTime @ Int32u |-> Vint32 (v'10+ᵢInt.one) **
             Aisr (isrupd v'2 0%nat false) **
             Aie false **
             Ais (0%nat :: v'3) **
             Acs nil **
             GV OSTCBList @ OS_TCB ∗ |-> Vptr v'4 ** GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
      p_local OSLInv ct (logic_val v'22 :: nil)).
  pure_intro'.
  unfolds in H19.
  destruct H19;subst.
  unfold notint in H32.
  simpl in H32.

  unfold Int.notbool in H32.
  assert (Int.eq Int.one Int.zero=false).
  pauto.
  rewrite H19 in H32.
  tryfalse.
  destruct H19.
  destruct x1.
  subst x7.
  clear H34 H32 H33.

  lets Hx': tcb_eptr_get_ectr H0 H1 H2 H12 H5.
  lets Hx: Hx' H3 H10;eauto.
  clear -Hrltcbblk.
  unfolds in Hrltcbblk.
  mytac.
  unfolds in H;simpl in H;inverts H.
  auto.
  unfolds in H;simpl in H;inverts H.
  auto.
  clear Hx'.
  mytac.
  (*H31 placeholder*)
  Open Scope Z_scope.
  assert (Int.unsigned i5 <= 255) by auto.

  eapply backward_rule1.
  intros.

  sep lift 10%nat in H33.
  lets Hx: get_ectr_decompose H33 H19.
  clear H33.
  exact Hx.
  pure_intro'.
  rename H38 into Hgetl1none.
  rename H39 into Hgetl2last.
  rename H40 into Hpnovnull.
  rename H41 into Hinvptr.
  unfold AEventNode.

  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  pure_intro'.
  
  assert (exists i, nth_val' (Z.to_nat (Int.unsigned i2)) x2 = Vint32 i /\ Int.unsigned i <= 255).
  eapply array_int8u_nth_lt_len;eauto.
  rewrite H41;simpl.
  unfold Pos.to_nat.
  unfold Pos.iter_op.
  simpl.
  apply z_le_7_imp_n;auto.
  omega.
  mytac.

  hoare forward.
  simpl in H38;eauto.
 
  hoare forward.
  (* intro;tryfalse. *)
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  pauto.
  pauto.
  splits;pauto.
   
  rewrite H41.
  unfold OS_EVENT_TBL_SIZE.
  simpl.
  auto.
  rewrite H33.
  rtmatch_solve.
  (* intro;tryfalse. *)
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  pauto.
  pauto.
  splits;pauto.
  (* intro;tryfalse. *)
  rewrite H33.
  pauto.
  (* intro;tryfalse. *)
  (* intro;tryfalse. *)
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  pauto.
  pauto.
  splits;pauto.
  
  eapply assign_type_match_true;simpl;auto.
  rewrite H41.
  unfold OS_EVENT_TBL_SIZE.
  simpl.
  auto.
  
  hoare forward.
  (* intro;tryfalse. *)
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  pauto.
  pauto.
  splits;pauto.
   
  rewrite H33.
  rewrite update_nth_val_len_eq.
  rewrite H41.
  unfold OS_EVENT_TBL_SIZE.
  simpl.
  auto.
  rewrite H33.
  rewrite len_lt_update_get_eq.
  rtmatch_solve.
  eapply int_lemma1;eauto.
  rewrite H41.
  unfold OS_EVENT_TBL_SIZE.
  simpl;auto.
  rewrite H33.
  rewrite len_lt_update_get_eq.
  unfold val_inj.
  unfold and.
  unfold val_eq.
  destruct (Int.eq (x1&ᵢInt.not i1) ($ 0));auto.
  (* intro;tryfalse. *)
  (* intro;tryfalse. *)
  rewrite H41.
  unfold OS_EVENT_TBL_SIZE.
  simpl.
  auto.
  hoare forward.
  (* intro;tryfalse. *)
  simpl;splits;pauto.
  (* intro;tryfalse. *)
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  pauto.
  pauto.
  splits;pauto.
  (* intro;tryfalse. *)
  (* intro;tryfalse. *)
  eapply disj_rule.
  pure_intro'.
  rewrite len_lt_update_get_eq in H39.
  rewrite H33 in H39.
  unfold and in H39.
  unfold val_eq, val_inj in H39.
  remember (Int.eq (x1&ᵢInt.not i1) ($ 0)) as X.
  destruct X;simpl in H39;tryfalse.
  clear H39 H51 H52 H47 H49 H50.
  hoare forward.
  sep lift 3%nat.
  instantiate (1:=v'34++ (((Vint32 i9
              :: Vint32 (i8&ᵢInt.not i0)
                 :: Vint32 i10 :: x7 :: x8 :: v'25 :: nil), (update_nth_val (Z.to_nat (Int.unsigned i2)) x2
                (val_inj
                   (and (nth_val' (Z.to_nat (Int.unsigned i2)) x2)
                        (Vint32 (Int.not i1))))))::nil) ++ v'35).
  eapply evsllseg_compose;eauto.
  unfolds;simpl;auto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold node.
  
          
  sep semiauto;eauto.
  2:unfolds;simpl;auto.
  rewrite H33.
  unfold and.
  simpl val_inj.
  eapply event_wait_rl_tbl_grp';eauto.
  unfolds;simpl;auto.
  rewrite H33.
  unfold and,val_inj.

  eapply array_type_vallist_match_int8u_update_hold_255;eauto.
  omega.
  simpl;splits;auto.
  rtmatch_solve.
  rtmatch_solve.
  apply int_lemma1;auto.
  pauto.
  pauto.
  pauto.
  simpl.
  rewrite H33.
  unfold and,val_inj.
  eapply tick_rdy_ectr_imp;eauto.

  rewrite H41;unfold OS_EVENT_TBL_SIZE;simpl;auto.

  pure_intro'.
  rewrite len_lt_update_get_eq in H39.
  rewrite H33 in H39.
  unfold and in H39.
  unfold val_eq, val_inj in H39.
  remember (Int.eq (x1&ᵢInt.not i1) ($ 0)) as X.
  destruct H39;destruct X;simpl in H39;tryfalse.
  clear H39.
  hoare forward.
  sep lift 3%nat.
  instantiate (1:=v'34++ (((Vint32 i9
              :: Vint32 i8
                 :: Vint32 i10 :: x7 :: x8 :: v'25 :: nil), (update_nth_val (Z.to_nat (Int.unsigned i2)) x2
                (val_inj
                   (and (nth_val' (Z.to_nat (Int.unsigned i2)) x2)
                        (Vint32 (Int.not i1))))))::nil) ++ v'35).
  eapply evsllseg_compose;eauto.
  unfolds;simpl;auto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold node.
  sep semiauto;eauto.
  instantiate (1:=v'39).
  sep auto.
  instantiate (1:=Vint32 i8).
  rewrite H33.
  eapply event_wait_rl_tbl_grp'';eauto.
  unfolds;simpl;auto.
  rewrite H33.
  unfold and,val_inj.

  eapply array_type_vallist_match_int8u_update_hold_255;eauto.
  omega.
  simpl;splits;auto.
  rtmatch_solve.
  pauto.
  pauto.
  pauto.
  pauto.


  simpl.
  rewrite H33.
  unfold and,val_inj.
  eapply tick_rdy_ectr_imp';eauto.
 
  rewrite H41;unfold OS_EVENT_TBL_SIZE;simpl;auto.
  intros.
  destruct H32.
  sep auto.
  clear -Hrltcbblk.
  unfold RL_TCBblk_P in *.
  mytac;auto.
  do 5 eexists;exists ($ OS_STAT_RDY);splits;eauto.
  splits;eauto.
  exists Vnull;split;auto.
  
  
  exists v'29 v'31.
  sep split in H32.
  assert (x7 = Vnull).
  clear -H33 H19.
  unfolds in H19.
  destruct H19;auto.
  mytac.
  destruct H33;destruct x;unfold val_eq, val_inj,notint in H;tryfalse.
  subst x7.
  sep auto.
  clear -Hrltcbblk.
  unfold RL_TCBblk_P in *.
  mytac;auto.
  do 5 eexists;exists ($ OS_STAT_RDY);splits;eauto.
  splits;eauto.
  exists Vnull;split;auto.
  
  apply disj_rule.
  pure_intro'.
  apply disj_rule.
  pure_intro'.
  assert (Int.eq i6 ($ 0) = false).
  clear -H15.
  destruct (Int.eq i6 ($ 0));simpl in H15;auto.
  unfold Int.notbool in H15.
  assert (Int.eq Int.one Int.zero = false).
  int auto.
  rewrite H in H15.
  tryfalse.
  assert (Int.eq (i6-ᵢ$ 1) ($ 0) =true).
  clear -H31.
  destruct (Int.eq (i6-ᵢ$ 1) ($ 0));simpl in H31;tryfalse;auto.
  clear H16 H15 H28 H32 H33 H31.
  eapply forward_rule2.
  hoare forward.
  (* intro;tryfalse. *)
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  pauto.
  pauto.
  splits;pauto.
   
  intros.
  exists (Vptr (v'33, Int.zero))
         ( v'23 ++
                (v'32
                   :: v'9
                   :: x7
                   :: x6
                   :: Vint32 i6
                   :: Vint32 i5
                   :: Vint32 i4
                   :: Vint32 i3
                   :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)::nil)
         v'24
         v'32
         (v'26 ++( (v'32
              :: v'9
                 :: Vnull
                    :: x6
                       :: Vint32 (i6-ᵢ$ 1)
                          :: V$OS_STAT_RDY
                             :: Vint32 i4
                                :: Vint32 i3
                                   :: Vint32 i2
                                      :: Vint32 i1 :: Vint32 i0 :: nil)::nil)).
  sep semiauto.
  sep cancel evsllseg.
  unfold tcbdllseg at 2.
  sep cancel dllseg.

  apply tcbdllseg_compose_tail;auto.
 
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  pauto.
  pauto.
  splits;pauto.
   
  lets Hx: tcblist_p_recombine H0 H1 H2 H12;auto.
  mytac.
 
  eapply tcbls_rtbl_timetci_update_hold;eauto.

  rewrite List.app_assoc_reverse.
  simpl.
  auto.

  pure_intro'.
  assert (Int.eq i6 ($ 0) = false).
  clear -H15.
  destruct (Int.eq i6 ($ 0));simpl in H15;auto.
  unfold Int.notbool in H15.
  assert (Int.eq Int.one Int.zero = false).
  int auto.
  rewrite H in H15.
  tryfalse.
  assert (Int.eq (i6-ᵢ$ 1) ($ 0) = false).
  clear -H30.
  destruct (Int.eq (i6-ᵢ$ 1) ($ 0));simpl in H30;destruct H30;tryfalse;auto.
  clear H16 H15 H32 H28 H30 H31 H29.
  eapply forward_rule2.
  hoare forward.
  (* intro;tryfalse. *)
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  pauto.
  pauto.
  splits;pauto.
   
  intros.
  exists (Vptr (v'33, Int.zero))
         ( v'23 ++
                (v'32
                   :: v'9
                   :: x7
                   :: x6
                   :: Vint32 i6
                   :: Vint32 i5
                   :: Vint32 i4
                   :: Vint32 i3
                   :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)::nil)
         v'24
         v'32
         (v'26 ++( (v'32
                      :: v'9
                      :: x7
                      :: x6
                      :: Vint32 (i6-ᵢ$ 1)
                      :: Vint32 i5
                      :: Vint32 i4
                      :: Vint32 i3
                      :: Vint32 i2
                      :: Vint32 i1 :: Vint32 i0 :: nil)::nil)).
  sep semiauto.
  sep cancel evsllseg.
  unfold tcbdllseg at 2.
  sep cancel dllseg.
  apply tcbdllseg_compose_tail;auto.
  
  simpl;splits.
  pauto.
  pauto.
  pauto.
  pauto.
  rtmatch_solve.
  eapply ne_0_minus_1_in_range;eauto.
  pauto.
  pauto.
  splits;pauto.
   


  eapply tcbls_rtbl_timetci_update_hold';eauto.
  rewrite List.app_assoc_reverse.
  simpl.
  auto.

  pure_intro'.
  assert (Int.eq i6 ($ 0) = true).
  clear -H15.
  destruct (Int.eq i6 ($ 0));simpl in H15;destruct H15;tryfalse;auto.
  eapply forward_rule2.
  hoare forward.
  (* intro;tryfalse. *)
  simpl;splits;pauto.
  intros.
  exists (Vptr (v'33, Int.zero))
         ( v'23 ++
                (v'32
                   :: v'9
                   :: x7
                   :: x6
                   :: Vint32 i6
                   :: Vint32 i5
                   :: Vint32 i4
                   :: Vint32 i3
                   :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)::nil)
         v'24
         v'32
         (v'26 ++( (v'32
                      :: v'9
                      :: x7
                      :: x6
                      :: Vint32 i6
                      :: Vint32 i5
                      :: Vint32 i4
                      :: Vint32 i3
                      :: Vint32 i2
                      :: Vint32 i1 :: Vint32 i0 :: nil)::nil)).
  sep semiauto.
  sep cancel evsllseg.
  unfold tcbdllseg at 2.
  sep cancel dllseg.
  apply tcbdllseg_compose_tail;auto.
  simpl;split;pauto.
  eapply tcbls_rtbl_timetci_update_hold'';eauto.
  rewrite List.app_assoc_reverse.
  simpl.
  auto.
Qed.
