(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(***** Proof for Internal Function: Int8u OS_TCBInit (Int8u prio) ****)
(************************C Source Code:*******************************)
(***
 Int8u ·OS_TCBInit·(⌞prio @ Int8u (*; task @ Int32 ;  pdata @ Void∗ *)⌟)··{
        ⌞ptcb @ OS_TCB∗⌟;

(*      ENTER_CRITICAL;ₛ *)
1:        ptcb′ =ₑ OSTCBFreeList′;ₛ
2:        If (ptcb′ !=ₑ NULL)
          {
3:            OSTCBFreeList′ =ₑ ptcb′→OSTCBNext;ₛ
(*          EXIT_CRITICAL;ₛ *)
4:            ptcb′→OSTCBPrio =ₑ (*〈Int8u〉*) prio′;ₛ
5:            ptcb′→OSTCBStat =ₑ ′OS_STAT_RDY;ₛ
6:            ptcb′→OSTCBDly =ₑ ′0;ₛ
7:            ptcb′→OSTCBY =ₑ prio′ ≫ ′3;ₛ
8:            ptcb′→OSTCBBitY =ₑ OSMapTbl′[ptcb′→OSTCBY];ₛ
9:            ptcb′→OSTCBX =ₑ prio′ &ₑ ′7;ₛ
10:           ptcb′→OSTCBBitX =ₑ OSMapTbl′[ptcb′→OSTCBX];ₛ
11:           ptcb′→OSTCBEventPtr =ₑ NULL;ₛ
12:           ptcb′→OSTCBMsg =ₑ NULL;ₛ
(*            ENTER_CRITICAL;ₛ *)
13:           OSTCBPrioTbl′[prio′] =ₑ ptcb′;ₛ
14:           ptcb′→OSTCBNext =ₑ OSTCBList′;ₛ
15:           ptcb′→OSTCBPrev =ₑ NULL;ₛ

16:           OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ ptcb′→OSTCBBitY;ₛ
17:           OSRdyTbl′[ptcb′→OSTCBY] =ₑ 
                    OSRdyTbl′[ptcb′→OSTCBY] |ₑ ptcb′→OSTCBBitX;ₛ


18:           If(OSTCBList′ !=ₑ NULL)
              {
19:               OSTCBList′→OSTCBPrev =ₑ ptcb′
              };ₛ
20:           OSTCBList′ =ₑ ptcb′;ₛ
21:           ptcb ′ → OSTCBflag =ₑ ′ 1;ₛ
(*            EXIT_CRITICAL;ₛ *)
22:           RETURN (OS_TCBInit) ′OS_NO_ERR 
          };ₛ
(*        EXIT_CRITICAL;ₛ *)           
23:       RETURN (OS_TCBInit) ′OS_NO_MORE_TCB

}·.

***
the order of the statements of the code is different from the original,
the nested if clause has been moved towards the end of the outter if block.
***)

Require Import ucos_include. 
Require Import oscore_common.
Require Import OSQPostPure. 
Require Import inv_prop.
Require Import OSTCBInitPure.
Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope list_scope.

Lemma OSTCBInit_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal OS_TCBInit
              vl logicl OS_TCBInitPre ct->
    Some r =
    BuildRetI os_internal OS_TCBInit vl logicl OS_TCBInitPost ct->
    exists t d1 d2 s,
      os_internal OS_TCBInit = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv,  I, r, Afalse|} |-ct {{p}} s {{Afalse}}. 
Proof.
  (*init spec*)
  init spec.
  unfold AOSTCBFreeList.
  hoare normal pre; hoare_split_pure_all.
  
  apply hoare_pure_gen' with (p:=isptr v'0).
  intros.
  sep lift 7%nat in H5.
  unfold sll in H5.
  eapply sllseg_head_isptr; eauto.
  hoare_split_pure_all.

  apply hoare_pure_gen' with (p:=exists x, v'5 = Vptr x).
  intros.
  sep lift 15%nat in H6.
  unfold tcbdllseg at 1 in H6.
  simpljoin.
  eapply dllseg_vptr; eauto.
  hoare_split_pure_all.
  
  assert(Int.unsigned v'10 < 64) as Hx1.
  simpljoin.
  clear - H7.
  unfold OS_LOWEST_PRIO in H7.
  int auto.

  assert (Int.unsigned (Int.shru v'10 ($ 3)) < 8) as Hx2.
  clear - Hx1.
  mauto.

  assert (Int.unsigned (v'10&ᵢ$ 7) < 8) as Hx3.
  clear - Hx1.
  mauto.

  simpljoin.
  assert (Z.to_nat (Int.unsigned (Int.shru v'10 ($3))) < 8)%nat as Hx11.
  clear - Hx2.
  apply z_le_7_imp_n.
  apply Zlt_succ_le.
  simpl; auto.

  assert (Z.to_nat (Int.unsigned (v'10&ᵢ$ 7)) < 8)%nat as Hx12.
  clear - Hx3.
  apply z_le_7_imp_n.
  apply Zlt_succ_le.
  simpl; auto.


(*L1: ptcb′ =ₑ OSTCBFreeList′;ₛ *)
  simpl in H.
  inverts H; inverts H8.
  hoare forward.
  pauto.

(*L2: If (ptcb′ !=ₑ NULL)*)
  hoare forward; pauto.
  instantiate (1:=Afalse).

(*L3-L7*)
  hoare_split_pure_all; simpljoin.
  assert(exists x, v'0 = Vptr x).
  clear - H5 H.
  destruct v'0; unfolds in H5; destruct H5; simpljoin; tryfalse.
  simpl in H.
  unfold Int.notbool in H; rewrite Int.eq_false in H; auto.
  tryfalse.
  eauto.
  simpljoin.

  unfold sll at 3.
  destruct v'1.
  unfold sllseg; hoare_split_pure_all; tryfalse.
  unfold sllseg; fold sllseg.

  unfold node.
  hoare_split_pure_all; simpljoin.
  inverts H9.
  assert(exists x0 x1 x2 x3 x4 x5 x6 x7 x8 x9, (exists x10, v = x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::nil)).
  struct_type_vallist_match_elim.
  do 11 eexists; eauto.
  simpljoin.
  simpl in H10; inverts H10.
  unfold AOSMapTbl at 3.
  unfold OSMapVallist.

  do 4 (hoare forward; pure_auto).

  hoare forward.
  pure_auto.
(*  assert (Int.ltu ($ 3) Int.iwordsize = true).
  clear - H9; clear H9.
  mauto.
  rewrite H10.
  simpl.
  intro; tryfalse.
*)
(*L8: ptcb ′ → OSTCBBitY =ₑ OSMapTbl ′ [ptcb ′ → OSTCBY];ₛ *) 
  assert(Int.ltu ($ 3) Int.iwordsize = true).
  pauto.
  rewrite H9.
  unfold val_inj.

  assert(rule_type_val_match Int8u (Vint32 v'10) = true) as Hx4.
  simpl in H12; simpljoin.
  simpl.
  erewrite Zle_bool_trans; auto.
  instantiate (1:=63).
  replace 63 with (64 - 1).
  apply Zlt_is_le_bool; auto.
  simpl; auto.
  pauto.

  assert(rule_type_val_match Int8u (Vint32 (Int.shru v'10 ($ 3))) = true) as Hx5.
  simpl in H12; simpljoin.
  simpl.
  erewrite Zle_bool_trans; auto.
  instantiate (1:=7).
  replace 7 with (8 - 1).
  apply Zlt_is_le_bool; auto.
  simpl; auto.
  pauto.
 
  assert( rule_type_val_match Int8u (nth_val' (Z.to_nat (Int.unsigned (Int.shru v'10 ($ 3)))) (V$1 :: V$2 :: V$4 :: V$8 :: V$16 :: V$32 :: V$64 :: V$128 :: nil)) =
          true) as Hx6.
 
  lets Hxx: OSMapVallist_bound Hx11.
  auto.
  simpljoin.
  unfold OSMapVallist in H10.
  rewrite H10.
  assert(Int.unsigned x0 <= 255).
  clear - H13.
  mauto.
  apply rule_type_val_match_int8_intro; auto.
  
  hoare forward.
  (*pure_auto.*)
  simpl in H12; simpl; simpljoin; splits; auto.
  pure_auto.

(*L9: ptcb ′ → OSTCBX =ₑ prio ′ &ₑ ′7;ₛ *)
  hoare forward; pauto.
  (*intro; tryfalse.*)

(*L10: ptcb ′ → OSTCBBitX =ₑ OSMapTbl ′ [ptcb ′ → OSTCBX];ₛ*)
  assert(rule_type_val_match Int8u (Vint32 (v'10&ᵢ$ 7)) = true) as Hx7.
  simpl in H12; simpljoin.
  simpl.
  erewrite Zle_bool_trans; auto.
  instantiate (1:=7).
  replace 7 with (8 - 1).
  apply Zlt_is_le_bool; auto.
  simpl; auto.
  pauto.

  assert(rule_type_val_match Int8u
     (nth_val' (Z.to_nat (Int.unsigned (v'10&ᵢ$ 7)))
        (V$1 :: V$2 :: V$4 :: V$8 :: V$16 :: V$32 :: V$64 :: V$128 :: nil)) =
         true) as Hx8.
  lets Hxx: OSMapVallist_bound Hx12.
  auto.
  simpljoin.
  unfold OSMapVallist in H10.
  rewrite H10.
  assert(Int.unsigned x0 <= 255).
  clear - H13.
  mauto.
  apply rule_type_val_match_int8_intro; auto.

  hoare forward.
  (*pure_auto.*)
  simpl in H12; simpl; simpljoin; splits; auto.
  pauto.

(*L11-12*)
  do 2 hoare forward; pauto.
  
(*L13*)
  hoare forward; pauto.

(*L14-15*)
  hoare forward; pauto.
  hoare forward.

(*L16: OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ ptcb′→OSTCBBitY;ₛ*)
  unfold AOSRdyTblGrp at 3.
  unfold AOSRdyGrp.
  hoare forward.
  (*pure_auto.*)
  simpl in H12; simpl; simpljoin; splits; auto.

  clear - H13 Hx11.
  simpl in H13; destruct v'4; tryfalse.
  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn : eq1; tryfalse.
  apply Z.leb_le in eq1.
  lets Hxx: OSMapVallist_bound Hx11; auto; simpljoin.
  unfold OSMapVallist in H.
  rewrite H.
  simpl; auto.
  (*intro; tryfalse.*)
  
(*L17: OSRdyTbl′[ptcb′→OSTCBY] =ₑ 
    OSRdyTbl′[ptcb′→OSTCBY] |ₑ ptcb′→OSTCBBitX;ₛ *)
  unfold AOSRdyTbl.
  hoare_split_pure_all.
  hoare forward.
  (*intro; tryfalse.*)
  simpl in H12; simpl; simpljoin; splits; auto.
  clear - H10 Hx2; simpljoin.
  rewrite H0.
  pauto.

  clear - H10 Hx11.
  simpljoin.
  lets Hxx: symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match H.
  unfold OS_RDY_TBL_SIZE in H0.
  simpl in H0.
  unfold Pos.to_nat in H0.
  simpl in H0.
  rewrite <- H0 in Hx11.
  eauto.
  auto.
  (*pure_auto.*)

  simpl in H12; simpl; simpljoin; splits; auto.
  clear - H10 Hx11 Hx12.
  lets Hxx: OSMapVallist_bound Hx12; auto.
  simpljoin.
  unfold OSMapVallist in H.
  rewrite H.
  lets Hxx: symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match H1.
  unfold OS_RDY_TBL_SIZE in H2.
  simpl in H2.
  unfold Pos.to_nat in H2.
  simpl in H2.
  rewrite <- H2 in Hx11.
  eauto.
  apply rule_type_val_match_int8u_elim in Hxx; simpljoin.
  rewrite H3.
  simpl; intro; tryfalse.
  (*pure_auto.*)
  
  simpl in H12; simpl; simpljoin; splits;  auto.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  clear - H10 Hx2; simpljoin.
  rewrite H0.
  unfold OS_RDY_TBL_SIZE.
  simpl.
  auto.

(* the tcb list has two doubly-linked segments,
   the first segment may or may not be nil,
   so there are two cases to consider.
*)
  destruct v'8.
(* the first segment is nil,
   so the node we are changing the prev ptr is
   the head of the second segment *)
  unfold tcbdllseg at 5.
  unfold dllseg; hoare_split_pure_all.
  inverts H15; substs.
  destruct v'9.
  unfold tcbdllseg at 5.
  unfold dllseg; hoare_split_pure_all; tryfalse.
  unfold tcbdllseg at 5.
  unfold dllseg; fold dllseg.
  unfold node.
  hoare_split_pure_all; simpljoin.
  inverts H15.
  assert(exists x0 x1 x2 x3 x4 x5 x6 x7 x8 x9, (exists x10, v = x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::nil)).
  struct_type_vallist_match_elim.
  do 11 eexists; eauto.
  simpljoin.
  unfolds in H16; unfolds in H17.
  simpl in H16; simpl in H17.
  inverts H16; inverts H17.

  (*L18: If(OSTCBList′ !=ₑ NULL) *)
  hoare forward.
  (*intro; tryfalse.*)
   
  (*L19: OSTCBList′→OSTCBPrev =ₑ ptcb′ *)
  hoare forward.

(*disjunction*)
  hoare forward.
(*1: true*)
(*L20: OSTCBList ′ =ₑ ptcb ′;ₛ *)  
  hoare forward.

(*L21: ptcb ′ → OSTCBflag =ₑ ′ 1;ₛ*)
  unfold sllfreeflag.
  unfold sllsegfreeflag; fold sllsegfreeflag.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  unfolds in H16; simpl in H16.
  inverts H15; inverts H16.

  hoare lifts (3::1::nil)%nat pre.
  eapply seq_rule.
  eapply assign_rule'.
  instantiate (1:=Int32u).
  eapply eq_int; auto.

  intros.
  split.
  sep remember (1::9::nil)%nat in H15.
  remember (get_off_addr (v'5, Int.zero) ($ 24)) as l.
  clear HeqH16.
  destruct_s s.
  simpl in H15; simpljoin1.

  simpl.
  rewrite H36.
  unfold os_ucos_h.OS_TCB at 2.
  unfold OSTCBflag.
  split; [ |simpl; auto].
  unfold getoff.
  unfold evaltype.
  rewrite H36.
  unfold os_ucos_h.OS_TCB at 2.

  lets Hx:symbolic_lemmas.mapstoval_load H37.
  simpl; auto.

  lets Hxx: symbolic_lemmas.load_mono H28 Hx.
  rewrite Hx in Hxx.
  apply join_comm in H23.
  lets Hxxx: symbolic_lemmas.load_mono H23 Hxx.
  rewrite Hxx in Hxxx.
  rewrite Int.unsigned_zero in Hxxx.
  rewrite Hxxx.
  simpl.
  unfold get_off_addr.
  simpl.
  change ($ Int.unsigned Int.zero +ᵢ($ 1 +ᵢ ($ 1 +ᵢ ($ 1 +ᵢ ($ 1 +ᵢ($ 1 +ᵢ ($ 1 +ᵢ ($ 2 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  Int.zero))))))))))))
  with
  (Int.zero +ᵢ $ 24).
  auto.
  symbolic execution.
  intro.
  sep auto.

(*L21 RETURN  (OS_TCBInit)′OS_NO_ERR *)
  eapply backward_rule2.
  hoare_forward_stmts'.
  intros. 

  assert (exists bitx, nth_val' (Z.to_nat (Int.unsigned (v'10&ᵢ$ 7))) OSMapVallist = Vint32 bitx /\ Int.unsigned bitx <= 128).
  eapply OSMapVallist_bound; auto.
  destruct H16 as (bitx & nth_val_bitx & bitx_le128).

  assert (exists bity, (nth_val' (Z.to_nat (Int.unsigned (v'10 >>ᵢ $ 3)))
              (V$ 1
               :: V$ 2
               :: V$ 4 :: V$ 8 :: V$ 16 :: V$ 32 :: V$ 64 :: V$ 128 :: nil)) = Vint32 bity /\ Int.unsigned bity <= 128).
  eapply OSMapVallist_bound; auto.
  destruct H16 as (bity & nth_val_bity & bity_le128).

  assert (exists row, (nth_val' (Z.to_nat (Int.unsigned (v'10 >>ᵢ $ 3))) v'2 = Vint32 row /\ Int.unsigned row <= 255)).
  eapply array_int8u_nth_lt_len; auto.
  rewrite H21.
  clear - Hx2.
  apply z_le_7_imp_n.
  remember (Int.unsigned (v'10 >>ᵢ $ 3)) as x.
  int auto.
  destruct H16 as (row & nth_val_row & row_le255).
  
  sep pauto.
  do 4 (sep cancel 14%nat 1%nat).
  sep cancel 4%nat 2%nat.
  right.
  sep auto.
  unfold AOSRdyTblGrp; unfold AOSRdyTbl; unfold AOSRdyGrp; unfold AOSMapTbl.
  sep auto.
  unfold sll.

  sep cancel 5%nat 2%nat.
  sep cancel 4%nat 1%nat.
  sep cancel 1%nat 1%nat.
  
(*  instantiate (2:=(Vptr (v'5, Int.zero))). *)
  instantiate (3:=nil).
  instantiate (1:= (v'6::Vptr (v'5, Int.zero)::x11::x12::x13
                         :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: nil) :: v'9). 
  unfold tcbdllseg at 1.
  unfold dllseg.
  sep auto.
  unfold tcbdllseg.
  unfold dllseg; fold dllseg.
  unfold node.
  
  sep auto.

  left.
  splits; eauto.

  clear - H13 Hx11.
  apply rule_type_val_match_int8u_elim in H13; simpljoin.
  lets Hxx: OSMapVallist_bound Hx11; auto.
  simpljoin.
  unfold OSMapVallist in H; rewrite H.
  simpl; auto.

  unfold val_inj; auto.
  fold OSMapVallist.

  split.
  eapply RL_Tbl_Grp_P_update_nth_val_or; eauto.
  clear - Hx1.
  mauto.

  remember (nth_val' (Z.to_nat (Int.unsigned (v'10&ᵢ$ 7))) OSMapVallist) as bitx'.
  rewrite nth_val_bitx in Heqbitx'.
  substs.
  eapply idle_in_rtbl_hold'; eauto.
  clear - Hx1; mauto.

  destruct v'4; simpl in H13; tryfalse.
  assert (Int.unsigned i <= 255).
  apply int_true_le255 in H13; auto.
  rewrite nth_val_bity.
  lets Hxxx : int_unsigned_or_prop H26 bity_le128.
  pure_auto.

  fold OSMapVallist.
  rewrite nth_val_bitx.
  rewrite nth_val_row.
  simpl val_inj.

  split.
  eapply array_type_vallist_match_hold; auto.
  rewrite H21.
  clear - H21 Hx2.
  eapply z_le_7_imp_n.
  int auto.

  clear - row_le255 bitx_le128.
  lets Hx: int_unsigned_or_prop row_le255 bitx_le128.
  pure_auto.

  rewrite hoare_assign.update_nth_val_len_eq.
  auto.
 
  unfold new_tcb_node_p.
  go.

  fold OSMapVallist.
  rewrite nth_val_bitx.
  rewrite nth_val_row.
  
  eapply RL_RTbl_PrioTbl_P_update_nth_val; eauto.
  clear - Hx1.
  mauto.

  sep remember (8::14::nil)%nat in H15.
  clear HeqH26.
  fold OSMapVallist in *.
  intro; substs.

  eapply Astruct_PV_dup_false; eauto.

  clear - H0 H4 Hx1.
  split.
  eapply array_type_vallist_match_vptr_update_nth_val; eauto.
  rewrite H4.
  mauto.

  rewrite update_nth_val_len_eq; auto.
 
  simpljoin; split; auto.
  go.

(*2: false*)
  hoare_split_pure_all.
  unfold Int.notbool in H15.
  rewrite Int.eq_true in H15.
  destruct H15; tryfalse.


(* the first segment is not nil,
   so the node we are changing the prev ptr is
   the head of the first segment *)
  unfold tcbdllseg at 5.
  unfold dllseg; fold dllseg.
  unfold node.


(*L18: If(OSTCBList ′ !=ₑ NULL) *)
  hoare_split_pure_all.
  assert(exists x0 x1 x2 x3 x4 x5 x6 x7 x8 x9, (exists x10, v = x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::nil)).
  simpljoin.
  struct_type_vallist_match_elim.
  do 11 eexists; eauto.
  simpljoin.
  unfolds in H16; unfolds in H17.
  simpl in H16; simpl in H17.
  inverts H16; inverts H17.
  
  hoare forward.
  destruct x; pauto.
  destruct x; pauto.
  (*simpl; intro; tryfalse.*)
  (*simpl; intro; tryfalse.*)
  (*simpl; intro; tryfalse.*)
  (*destruct x; simpl; intro; tryfalse.*)

(*L19 OSTCBList ′ → OSTCBPrev =ₑ ptcb ′ *)
  inverts H15.
  hoare forward.

(*disjunction in pre*)
  hoare forward.
(*left: true*)
(*L20: OSTCBList ′ =ₑ ptcb ′;ₛ *)  
  hoare forward.
  destruct x.

(*L21: ptcb ′ → OSTCBflag =ₑ ′ 1;ₛ*)
  unfold sllfreeflag.
  unfold sllsegfreeflag; fold sllsegfreeflag.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  unfolds in H17; simpl in H17.
  inverts H16; inverts H17.

  hoare lifts (3::1::nil)%nat pre.
  eapply seq_rule.
  eapply assign_rule'.
  instantiate (1:=Int32u).
  eapply eq_int; auto.

  intros.
  split.
  sep remember (1::9::nil)%nat in H16.
  remember (get_off_addr (v'5, Int.zero) ($ 24)) as l.
  clear HeqH17.
  destruct_s s.
  simpl in H16; simpljoin1.

  simpl.
  rewrite H37.
  unfold os_ucos_h.OS_TCB at 2.
  unfold OSTCBflag.
  split; [ |simpl; auto].
  unfold getoff.
  unfold evaltype.
  rewrite H37.
  unfold os_ucos_h.OS_TCB at 2.

  lets Hx:symbolic_lemmas.mapstoval_load H38.
  simpl; auto.

  lets Hxx: symbolic_lemmas.load_mono H29 Hx.
  rewrite Hx in Hxx.
  apply join_comm in H24.
  lets Hxxx: symbolic_lemmas.load_mono H24 Hxx.
  rewrite Hxx in Hxxx.
  rewrite Int.unsigned_zero in Hxxx.
  rewrite Hxxx.
  simpl.
  unfold get_off_addr.
  simpl.
  change ($ Int.unsigned Int.zero +ᵢ($ 1 +ᵢ ($ 1 +ᵢ ($ 1 +ᵢ ($ 1 +ᵢ($ 1 +ᵢ ($ 1 +ᵢ ($ 2 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 4 +ᵢ  Int.zero))))))))))))
  with
  (Int.zero +ᵢ $ 24).
  auto.
  symbolic execution.
  intro.
  sep auto.

  
(*L22: RETURN  (OS_TCBInit)′OS_NO_ERR *)
  eapply backward_rule2.
  hoare_forward_stmts'.

  assert (exists bitx, nth_val' (Z.to_nat (Int.unsigned (v'10&ᵢ$ 7))) OSMapVallist = Vint32 bitx /\ Int.unsigned bitx <= 128).
  eapply OSMapVallist_bound; auto.
  destruct H16 as (bitx & nth_val_bitx & bitx_le128).

  assert (exists bity, (nth_val' (Z.to_nat (Int.unsigned (v'10 >>ᵢ $ 3)))
              (V$ 1
               :: V$ 2
               :: V$ 4 :: V$ 8 :: V$ 16 :: V$ 32 :: V$ 64 :: V$ 128 :: nil)) = Vint32 bity /\ Int.unsigned bity <= 128).
  eapply OSMapVallist_bound; auto.
  destruct H16 as (bity & nth_val_bity & bity_le128).

  assert (exists row, (nth_val' (Z.to_nat (Int.unsigned (v'10 >>ᵢ $ 3))) v'2 = Vint32 row /\ Int.unsigned row <= 255)).
  eapply array_int8u_nth_lt_len; auto.
  rewrite H22.
  clear - Hx2.
  apply z_le_7_imp_n.
  remember (Int.unsigned (v'10 >>ᵢ $ 3)) as x.
  int auto.
  destruct H16 as (row & nth_val_row & row_le255).

  intros.
  sep pauto.
  do 4 (sep cancel 14%nat 1%nat).
  sep cancel 4%nat 2%nat.
  right.
 
  sep pauto.
  sep cancel 1%nat 7%nat.
  unfold AOSRdyTblGrp; unfold AOSRdyTbl; unfold AOSRdyGrp; unfold AOSMapTbl. 
  sep pauto.
  8:eauto.
  unfold sll.
  sep cancel 5%nat 2%nat.
  sep cancel 4%nat 1%nat.
  sep cancel 4%nat 2%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 3%nat 1%nat.
  sep cancel 3%nat 2%nat.

  instantiate (1:= (v'14
              :: Vptr (v'5, Int.zero)
                 :: x12
                    :: x13
                       :: x14
                          :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: nil) :: v'8). 
  unfold tcbdllseg.
  unfold dllseg; fold dllseg.
  unfold node.
  inverts H15.
  sep pauto.

  split.
  eapply RL_Tbl_Grp_P_update_nth_val_or; eauto.
  clear - Hx1.
  mauto.

  fold OSMapVallist.
  remember (nth_val' (Z.to_nat (Int.unsigned (v'10&ᵢ$ 7))) OSMapVallist) as bitx'.
  rewrite nth_val_bitx in Heqbitx'.
  substs.
  eapply idle_in_rtbl_hold'; eauto.
  clear - Hx1; mauto.

  destruct v'4; simpl in H13; tryfalse.
  assert (Int.unsigned i0 <= 255).
  apply int_true_le255 in H13; auto.
  rewrite nth_val_bity.
  lets Hxxx : int_unsigned_or_prop H27 bity_le128.
  pure_auto.

  fold OSMapVallist.
  rewrite nth_val_bitx.
  rewrite nth_val_row.
  simpl val_inj.

  split.
  eapply array_type_vallist_match_hold; auto.
  rewrite H22.
  clear - H22 Hx2.
  eapply z_le_7_imp_n.
  int auto.

  clear - row_le255 bitx_le128.
  lets Hx: int_unsigned_or_prop row_le255 bitx_le128.
  pure_auto.

  rewrite hoare_assign.update_nth_val_len_eq.
  auto.

  right.
  split.
  intro; tryfalse.
  simpl.
  splits; auto.
  rewrite nth_val_bity.
  destruct v'4; simpl in H13; tryfalse.
  simpl; auto.

  unfold val_inj.
  auto.

  fold OSMapVallist.
  rewrite nth_val_bitx.
  unfold new_tcb_node_p.
  go.
  rewrite nth_val_bitx; auto.
  
  fold OSMapVallist.
  rewrite nth_val_bitx.
  rewrite nth_val_row.

  eapply RL_RTbl_PrioTbl_P_update_nth_val; eauto.
  clear - Hx1.
  mauto.

  sep remember (8::14::nil)%nat in H16.
  intro; substs.
  eapply Astruct_PV_dup_false; eauto.

  clear - H0 H4 Hx1.
  split.
  eapply array_type_vallist_match_vptr_update_nth_val; eauto.
  rewrite H4.
  mauto.

  rewrite update_nth_val_len_eq; auto.
 
  simpljoin; split; auto.
  go.

(*2: false*)
  hoare_split_pure_all.
  destruct x.
  simpl in H16.
  unfold Int.notbool in H16.
  rewrite Int.eq_true in H16.
  destruct H16; tryfalse.

(*23:  RETURN  (OS_TCBInit)′OS_NO_MORE_TCB *)
(*disjunction in pre*)
  hoare forward.

(*return*)
  eapply backward_rule2.
  hoare forward.
  intros.
  sep pauto.
  do 4 (sep cancel 2%nat 1%nat).
  sep cancel 15%nat 2%nat.
  left.
  sep auto.

  clear - H6 H5.
  unfold isptr in H5.
 
  destruct v'0; simpl in H5; destruct H5; simpljoin; tryfalse.
  inverts H. 
  simpl in H6; destruct x; simpl in H6.
  unfold Int.notbool in H6.
  rewrite Int.eq_true in H6.
  destruct H6; tryfalse.
Qed.
