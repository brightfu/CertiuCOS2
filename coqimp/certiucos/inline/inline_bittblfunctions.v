Require Import include_frm.
Require Import inline_definitions.
(* Require Import OSTimeDlyPure. *)
Require Import os_code_defs.
Require Import inline_tactics.
Require Import symbolic_lemmas.
Require Import sep_auto.
Require Import math_auto.
Require Import os_inv. (* RL_Tbl_Grp_P *)
Require Import hoare_forward.
Require Import pure_lib.
Require Import abs_step. (* tri_exists_and_solver *)
Require Import pure.
Require Import ucos_bitsmap. (**)
Local Open Scope list_scope.
Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

Definition  bittbl_setbit_inline_code :inline_function_code :=
  (fun (le : list expr) =>
     match le with
       |    (grp::tbl::bitx::bity::y::nil) =>
            grp                    =ₑ grp |ₑ bity;ₛ
            tbl[y] =ₑ tbl[y] |ₑ bitx
       (* no meaning statement here *)
       | _ =>Skip
     end
  ). 

Lemma nth_val'2nth_val:
  forall n rtbl x,
    nth_val' n rtbl = Vint32 x ->
    nth_val n rtbl = Some (Vint32 x).
Proof.
  intros.
  inductions n;
    simpl in *;  destruct rtbl; simpl in *;tryfalse; try subst; auto.
Qed.


Lemma xchange_asrt_ex:
  forall {T:Type} p q,
    EX (x:T),  q ** p x <==> q ** EX (x:T), p x.
  intros.
  splits.
  intros.
  sep auto.
  intros.
  sep auto.
Qed.

Lemma mutexpost_intlemma1:
  forall x,
    Int.unsigned x < 64 ->
    (Int.modu x ($ Byte.modulus)) = x.
Proof.
  intros.
  unfold Int.modu.
  unfold Byte.max_unsigned.
  unfold Byte.modulus.
  unfold Byte.wordsize.
  unfold Wordsize_8.wordsize.
  unfold two_power_nat.
  unfold shift_nat.
  simpl.
  repeat ur_rewriter.
  mauto.
Qed.

Lemma ob1 :
  forall x x1,
    Int.unsigned x <=7 ->
    Int.unsigned x1 <=7 ->
    (((x<<ᵢ$ 3)+ᵢx1)>>ᵢ$ 3) = x.
Proof.
  intros.
  mauto.
Qed.

Lemma ob2 :
  forall x x1,
    Int.unsigned x <=7 ->
    Int.unsigned x1 <=7 ->
    (((x<<ᵢ$ 3)+ᵢx1)&ᵢ $ 7) = x1.
Proof.
  intros.
  mauto.
Qed.

Lemma sep_or2or:
  forall s p q,
    s|= p \\// q ->
    s |= p \/ s |= q.
Proof.
  intro.
  intros.
  simpl in H.
  auto.
Qed.


Lemma z2n_int_eq:
  forall x y,
    Z.to_nat (Int.unsigned x) = Z.to_nat (Int.unsigned y) ->
    x = y.
Proof.
  intros.
  apply Z2Nat.inj in H.
  math simpl in H.
  auto.
  int auto.
  int auto.
Qed.



Lemma twopow_sub_1_testbit_true:
  forall i n,
    0 <= i ->
    i<n ->
    Z.testbit (2^n-1) i = true.
Proof.
  intros.
  assert ((if zlt i n then true else false) = true).
  apply zlt_true.
  auto.
  rewrite <- H1.
  assert (2 ^ n = two_p n).
  rewrite two_p_equiv. 
  auto.
  rewrite H2.
  apply Int16.Ztestbit_two_p_m1.
  omega.
  omega.
Qed.



Lemma lpart_eq_rpart_eq_eq:
  forall n x y,
    0 <= n < 32 ->
    x >>ᵢ $ n = y>>ᵢ $ n ->
    x &ᵢ $ (2 ^ n -1) = y &ᵢ $ (2 ^ n -1) ->
    x = y.
Proof.
  intros.
  apply unsigned_inj.

  apply Int.eqm_small_eq.
  Focus 2.
  clear.
  int auto.
  bsimplr.
  tauto.
  Focus 2.

  clear.
  int auto.
  bsimplr.
  tauto.
  apply Int.eqm_same_bits.
  intros.
  change Int.zwordsize with 32 in H2.

  assert ( i < n \/ i >= n).
  omega.
  destruct H3; intros.

  Focus 2.
  assert (i = (i-n) + (n)).
  omega.
  rewrite H4.
  erewrite <- Z.shiftr_spec_aux ; try omega.
  erewrite <- Z.shiftr_spec_aux ; try omega.
  rewrite <- Int.testbit_repr.
  rewrite <- Int.testbit_repr.
  unfold Int.shru in H0.
  ur_rewriter_in H0.
  rewrite H0.
  auto.
  csimpl Int.max_unsigned.
  omega.
  csimpl Int.zwordsize.
  omega.
  csimpl Int.zwordsize.
  omega.
 
  assert ( forall k, Int.testbit ( x&ᵢ$ (2 ^ n - 1) ) k = Int.testbit (y&ᵢ$ (2 ^ n - 1) ) k).
  intro.
  rewrite H1.
  auto.
  lets fff: H4 i.


  assert (0<=i< Int.zwordsize).
  exact H2.
  
  rewrite Int.bits_and in fff; auto.
  rewrite Int.bits_and in fff; auto.

  rewrite Int.testbit_repr in fff; auto.
  rewrite <- (Int.repr_unsigned x) in fff.
  rewrite <- (Int.repr_unsigned y) in fff.
  rewrite Int.testbit_repr in fff; auto.
  rewrite Int.testbit_repr in fff; auto.

  rewrite  twopow_sub_1_testbit_true in fff; try omega.
  rewrite andb_true_r in fff.
  rewrite andb_true_r in fff.
  auto.
Qed.
  


Lemma not_eq_at_least_one_part_not_eq:
  forall x y,
    x <> y ->
    x >>ᵢ $ 3 = y>>ᵢ $ 3 ->
    x &ᵢ $ 7 <> y &ᵢ $ 7.
Proof.
  intros.
  change 7 with (2^3 -1).
  intro.
  apply H.
  eapply lpart_eq_rpart_eq_eq.
  2:eauto.
  omega.
  auto.
Qed.



Definition bittbl_setbit_inline_pre :inline_function_asrt :=
  (fun (p:asrt)(ll: list logicvar) (le: list expr) => 
     (EX sc prgrp vrgrp vrtbl prtbl nrtbl nrgrp nbitx nbity ny vbitx vbity vy vx prio,
      <|| sc ||> **
          [|ll = (logic_val (Vint32 vrgrp) :: logic_lv vrtbl :: logic_val (Vptr prgrp) :: logic_val (Vptr prtbl) :: logic_val (Vint32 vbity) :: logic_val (Vint32 vbitx) :: logic_val (Vint32 vy) :: logic_code sc :: nil) |] **
          [|le = nrgrp :: nrtbl :: nbitx :: nbity ::ny::nil|]**
          PV prgrp @ Int8u |-> Vint32 vrgrp **
          Aarray prtbl (Tarray Int8u ∘OS_RDY_TBL_SIZE) vrtbl **
          [| RL_Tbl_Grp_P vrtbl (Vint32 vrgrp) |] **
          [| p ==> Rv nrtbl @ Tarray Int8u  ∘OS_RDY_TBL_SIZE == Vptr prtbl //\\
             Lv nrgrp @ Int8u == prgrp //\\  
             Rv nbity @ Int8u == Vint32 vbity //\\ 
             Rv nbitx @ Int8u == Vint32 vbitx //\\ 
             Rv ny @ Int8u == Vint32 vy |] **
          [| (Z.to_nat (Int.unsigned vy) <  ∘OS_RDY_TBL_SIZE)%nat |] **
          [| array_type_vallist_match Int8u vrtbl |] **
          [| length vrtbl = ∘OS_RDY_TBL_SIZE |] **
          [| rule_type_val_match Int8u (Vint32 vrgrp) = true |] **
          [| prio >>ᵢ  ($ 3) = vy |] **
          [| prio &ᵢ ($ 7) = vx |] **
          [| vbitx = ($ 1) <<ᵢ vx |] **
          [| vbity = ($ 1) <<ᵢ vy |] **
          [| Int.unsigned prio < 64 |] 
     )). 

Definition bittbl_setbit_inline_post : inline_function_asrt :=
  (fun (p:asrt)(ll: list logicvar) (le: list expr) =>
     EX sc prgrp vrgrp vrtbl prtbl nrtbl nrgrp nbitx nbity ny vbitx vy vrtbl' vrgrp' prevalue vbity, 
           <||sc||> ** 
          [|ll = (logic_val (Vint32 vrgrp) :: logic_lv vrtbl :: logic_val (Vptr prgrp) :: logic_val (Vptr prtbl) :: logic_val (Vint32 vbity) :: logic_val (Vint32 vbitx) :: logic_val (Vint32 vy) :: logic_code sc :: nil) |] **
              [|le = nrgrp :: nrtbl :: nbitx :: nbity ::ny::nil|]**
              Aarray prtbl (Tarray Int8u ∘OS_RDY_TBL_SIZE) vrtbl' **
              PV prgrp @ Int8u |-> Vint32 vrgrp' **

              [|(nth_val' (Z.to_nat (Int.unsigned vy)) vrtbl) = Vint32 prevalue /\
                       Int.unsigned prevalue <= Byte.max_unsigned |] **
              [| vrtbl' = update_nth_val (Z.to_nat (Int.unsigned vy)) vrtbl 
                                         (val_inj (or (Vint32 prevalue) (Vint32 vbitx)))|] ** 
              [| length vrtbl' =  ∘OS_RDY_TBL_SIZE |] **
              [| rule_type_val_match Int8u (Vint32 vrgrp) = true |] **
              [| RL_Tbl_Grp_P vrtbl' (Vint32 vrgrp') |] **
              [| forall x, prio_in_tbl x vrtbl -> prio_in_tbl x vrtbl' |] 
  ).

Goal make_inl_proof bittbl_setbit_inline_code bittbl_setbit_inline_pre bittbl_setbit_inline_post.
Proof.
  unfolds.
  intros.
  rename H into LocalInv_H.
  unfold bittbl_setbit_inline_pre.
  unfold bittbl_setbit_inline_code.
  unfold bittbl_setbit_inline_post.
  hoare_split_pure_all.
  subst .
  rename v'4 into nrtbl.
  rename v'5 into nrgrp.
  rename v'7 into nbity.
  rename v'6 into nbitx.
  rename v'8 into ny.
  rename v'13 into prio.
  rename v'3 into prtbl.
  rename v'2 into vrtbl.
  sep_conj_handlerH H2.
  assert ( (Z.to_nat (Int.unsigned  (prio>>ᵢ$ 3) )) <  length vrtbl )%nat.
  rewrite H5.
  clear -H11.
  mauto.
  

  lets fff: array_int8u_nth_lt_len H4 H8.
  simpljoin.

  eapply seq_rule.
  
  eapply assign_rule_general' .
  Focus 2.
  intro.
  intros.
  eapply monoasrt_imp_mono.
  apply Lv_mono.
  2:eauto.
  sep auto.

  Focus 2.
  sep auto.
  split.
  intros; sep auto.
  auto.

  Focus 2.
  intros.
  eapply bop_rv.

  {
	eapply lv_mapsto_to_rv.
	Focus 2.
	eapply monoasrt_imp_mono.
	apply Lv_mono.
	2:eauto.
	sep auto.

	Focus 2.
	sep auto.
	auto.
  }
  eapply monoasrt_imp_mono.
  apply Rv_mono.
  2:eauto.
  sep auto.
  simpl.
  eauto.
  intro; tryfalse.
  simpl.
  eauto.
 
  apply eq_int.
  tauto.
  
  intro.
  intros.
  sep lift 2%nat.
  eapply xchange_asrt_ex.
  sep lift 2%nat.
  eapply monoasrt_imp_mono.
  apply startrue_mono.
  Focus 2.
  intro.
  intros.
  sep normal.
  apply LocalInv_H.
  eauto.
  sep auto.
  

  (*destruct prtbl.*)
  (*lets ffasdf: ht.nthval'_has_value Hf He Hd.*)
  
  eapply forward_rule2.
  eapply assign_rule_ptr_array_aop.
  {
	intro.
	intros.
	eapply monoasrt_imp_mono.
	apply Rv_mono.
	2:eauto.
	sep auto.
  }

  intro.
  split.
  intros.
  sep auto.
  intros.
  sep auto.
  Focus 2.
  intro.
  intros.
  eapply monoasrt_imp_mono.
  apply Rv_mono.
  2:eauto.
  sep auto.
  {
	intro.
	intros.
	eapply bop_rv.
	{
	  eapply expr_array_member_rv.
	  eapply monoasrt_imp_mono.
	  apply Rv_mono.
	  2:eauto.
	  sep auto.
	  sep auto.
	  
	  eapply monoasrt_imp_mono.
	  apply Rv_mono.
	  2:eauto.
	  sep auto.
	  tauto.
	  tauto.
	  compute.
	  auto.
	  clear -H11; unfold OS_RDY_TBL_SIZE; mauto.
	  rewrite H5.
	  clear -H11; unfold OS_RDY_TBL_SIZE; mauto.
	  2: auto.
	  rewrite H10.
	  unfolds.
      math simpls.
	}
	eapply monoasrt_imp_mono.
	apply Rv_mono.
	2:eauto.
	sep auto.
	rewrite H10.
	simpl.
	eauto.
    intro; tryfalse.
	simpl.
	eauto.
  }
  tauto.
  tauto.
  clear -H11; unfold OS_RDY_TBL_SIZE; mauto.
  apply eq_int.
  tauto.
  rewrite H5.
  clear -H11; unfold OS_RDY_TBL_SIZE; mauto.
  intro.
  intros.

  sep lift 2%nat.
  eapply xchange_asrt_ex.
  sep lift 2%nat.
  eapply monoasrt_imp_mono.
  apply startrue_mono.
  Focus 2.
  intro.
  intros.
  sep normal.
  apply LocalInv_H.
  eauto.
  sep auto.

  sep pauto.


  
  {  
    intros.
    unfold prio_in_tbl in *.
    intros.
    lets fff: H14 H15 H16.
    unfold nat_of_Z in *.
    assert ( (Z.to_nat (Int.unsigned y)) <> (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3)))  \/ (Z.to_nat (Int.unsigned y)) = (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3))) ). 
    tauto.
    elim H18; intros.
    apply nth_upd_neq in H17.
    apply fff.
    exact H17.
    auto.
    rewrite <- H19 in *.

    lets fffb: H14 H15 H16 (nth_val'2nth_val _ _ _ H10). 
    apply nth_upd_eq in H17.
    simpl in H17.
    inverts H17.
    rewrite Int.and_or_distrib_l.
    rewrite fffb.
    assert ( 0<= Int.unsigned (($ 1<<ᵢ(prio&ᵢ $ 7))) < 256)%Z.
    clear -H11; mauto.
    assert (0<=Int.unsigned x1 < 8).
    rewrite H15.
    rewrite Int.and_commut.
    clear.
    split.
    remember ($ 7&ᵢx0).
    int auto.
    change 8 with (Int.unsigned ($ 8)).
    assert ( Int.unsigned ($ 7&ᵢx0) <= Int.unsigned ($ 7)).
    apply Int.and_le.
    ur_rewriter.
    ur_rewriter_in H.
    omega.
    lets bbba: prio_int_disj H17 H20.
    clear -bbba H20.
    destruct bbba; intros; rewrite H.
    clear -H20; mauto.
    clear -H20; mauto.
  }

  (* Require Import OSQPendPure. *)
  (* eapply event_wait_rl_tbl_grp;eauto. *)

Lemma event_wait_rl_tbl_grp:
  forall x10 x9 x8 x7 i10 i6 i5 i4 i3 i2 v'5 x0 i i1,
    RL_TCBblk_P
      (x10
         :: x9
         :: x8
         :: x7
         :: Vint32 i10
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: nil) ->
    array_type_vallist_match Int8u v'5 ->
    nth_val' (Z.to_nat (Int.unsigned i3)) v'5 = Vint32 x0 ->
    RL_Tbl_Grp_P v'5 (Vint32 i) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned i3)) v'5 (Vint32 (Int.or x0 i2)))
      (Vint32 (Int.or i i1)).
Proof.
  introv Hrl Harr Hnth Hrt.
  funfold Hrl.
  funfold Hrt.
  assert ( 0 <= Int.unsigned x < 64) as Hran by omega.
  clear H5 H13.
  unfolds.
  introv Hn Hnv Hvi.
  inverts Hvi.
  assert (n <> (Z.to_nat (Int.unsigned (Int.shru x ($ 3)))) \/
          n = (Z.to_nat (Int.unsigned (Int.shru x ($ 3))))) by tauto.
  destruct H.
  lets Hex : nth_upd_neq H Hnv.
  assert (Vint32 i = Vint32 i) by auto.
  lets Hexz : Hrt Hn Hex H0.
  destruct Hexz as (He1 & He2).
  split.
  split.
  intros.
  apply He1.
  rewrite Int.and_commut in H1.
  rewrite Int.and_or_distrib in H1.
  
  lets Hc : math_and_zero Hran Hn H.
  rewrite Hc in H1.
  rewrite Int.or_zero in H1.
  rewrite Int.and_commut.
  auto.
  intros.
  lets Hc : math_and_zero Hran Hn H.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  rewrite Hc.
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  apply He1; auto.
  lets Hc : math_and_zero Hran Hn H.
  split.
  intros.
  apply He2.
  rewrite Int.and_commut in H1.
  rewrite Int.and_or_distrib in H1.
  rewrite Hc in H1.
  rewrite Int.or_zero in H1.
  rewrite Int.and_commut.
  auto.
  intros.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  rewrite Hc.
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  apply He2; auto.
  subst n.
  lets Hins : nth_upd_eq  Hnv.
  inverts Hins.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  split.
  split.
  intros.
  apply int_or_zero_split in H.
  destruct H.
  lets Hf : math_prop_neq_zero Hran.
  tryfalse.
  intros.
  apply int_or_zero_split in H.
  destruct H.
  apply math_prop_neq_zero2 in H0.
  tryfalse.
  auto.
  split.
  intros.
  apply int_ltu_true; auto.
  intros.
  rewrite math_prop_eq; auto.
  rewrite Int.and_idem.
  rewrite Int.or_commut.
  rewrite Int.or_and_absorb.
  auto.
Qed.


  eapply event_wait_rl_tbl_grp;eauto.
  unfolds. 
  repeat tri_exists_and_solver1.
  go.
  go.

  go.
  go.
  go.
  go.
  2: go.
  clear.
  int auto.
  auto.
  rewrite update_nth_val_len_eq.
  auto.
  simpl.
  auto.
  split.
  auto.
  auto.
  Unshelve.
  exact (Vint32 (Int.repr 0)).
  exact (Vint32 (Int.repr 0)).
  exact (Vint32 (Int.repr 0)).
  exact ((Int.repr 0)).
Qed.

Definition inline_bittbl_setbit :=
  Inline_record_cons bittbl_setbit_inline_code bittbl_setbit_inline_pre bittbl_setbit_inline_post Unnamed_thm.


(* get highest prio *)


Definition  bittbl_gethighestprio_inline_code :inline_function_code :=
  (fun (le : list expr) =>
     match le with
       |    (grp::tbl::x::y::prio::nil) =>
            y =ₑ OSUnMapTbl′[ grp ];ₛ
            x =ₑ OSUnMapTbl′[ tbl[y] ];ₛ
            prio =ₑ 〈Int8u〉 ((y ≪ ′3) +ₑ x)
       | _ =>Skip
     end
  ). 


Definition bittbl_gethighestprio_inline_pre :inline_function_asrt :=
  (fun (p:asrt)(ll: list logicvar) (le: list expr) => 
     (EX sc vrgrp vrtbl prtbl nrtbl nrgrp py ny vy px nx vx pprio nprio vprio l,
      <|| sc ||> **
          [|ll = (logic_val (Vint32 vrgrp) :: logic_lv vrtbl ::  logic_val (Vptr prtbl) :: logic_val (Vptr l) :: logic_code sc :: nil) |] **
          [|le = nrgrp :: nrtbl :: nx :: ny :: nprio::nil|]**
          PV px @ Int8u |-> Vint32 vx **
          PV py @ Int8u |-> Vint32 vy **
          PV pprio @ Int8u |-> Vint32 vprio **
          Aarray prtbl (Tarray Int8u ∘OS_RDY_TBL_SIZE) vrtbl **
          Aarray l (Tarray Int8u 256) OSUnMapVallist **
          [| RL_Tbl_Grp_P vrtbl (Vint32 vrgrp) |] **
          [| p ==> Rv nrtbl @ Tarray Int8u  ∘OS_RDY_TBL_SIZE == Vptr prtbl //\\
             Rv nrgrp @ Int8u == Vint32 vrgrp //\\  
             Lv ny @ Int8u == py //\\ 
             Lv nx @ Int8u == px //\\ 
             Lv nprio @ Int8u == pprio //\\
             Rv OSUnMapTbl ′ @ (Tarray Int8u 256) == Vptr l
           |] **
          [| array_type_vallist_match Int8u vrtbl |] **
          [| length vrtbl = ∘OS_RDY_TBL_SIZE |] **
          [| rule_type_val_match Int8u (Vint32 vrgrp) = true |] **
          [| Int.eq vrgrp ($ 0) = false|]
     )). 

Definition x_min_under_P {T:Type} (x:T) (P: T ->Prop) (ltProp: T -> T ->Prop) := P x /\ (forall other, P other -> other <> x -> ltProp x other).

Definition highest_in_prio_tbl x rtbl := x_min_under_P x (fun t => prio_in_tbl t rtbl) (fun x y => Int.ltu x y = true).


Definition bittbl_gethighestprio_inline_post : inline_function_asrt :=
  (fun (p:asrt)(ll: list logicvar) (le: list expr) =>
     EX sc vrgrp vrtbl prtbl nrtbl nrgrp ny px py vx' vy' pprio vprio' nx nprio l,  
           <||sc||> ** 
          [|ll = (logic_val (Vint32 vrgrp) :: logic_lv vrtbl ::  logic_val (Vptr prtbl) :: logic_val (Vptr l) :: logic_code sc :: nil) |] **
              [|le = nrgrp :: nrtbl :: nx :: ny ::nprio::nil|]**
              Aarray prtbl (Tarray Int8u ∘OS_RDY_TBL_SIZE) vrtbl **
              Aarray l (Tarray Int8u 256) OSUnMapVallist **
              PV px @ Int8u |-> Vint32 vx' **
              PV py @ Int8u |-> Vint32 vy' **
              PV pprio @ Int8u |-> Vint32 vprio' **
              [| Int.eq vx' (vprio' >>ᵢ ($ 3)) = true|] **
              [| Int.eq vy' (vprio' &ᵢ  ($ 7)) = true|] **
              [| highest_in_prio_tbl vprio' vrtbl |] 
  ).

Goal make_inl_proof bittbl_gethighestprio_inline_code bittbl_gethighestprio_inline_pre bittbl_gethighestprio_inline_post.
Proof.
  unfolds.
  intros.
  rename H into LocalInv_H.
  unfold bittbl_gethighestprio_inline_pre.
  unfold bittbl_gethighestprio_inline_code.
  unfold bittbl_gethighestprio_inline_post.
  hoare_split_pure_all.
  subst.
  rename H6 into anotherH.

  rename v'4 into nrgrp.
  rename v'6 into nx.
  rename v'9 into ny.
  rename v'12 into nprio.
  rename v'3 into nrtbl.

  rename v'2 into prtbl.
  rename v'0 into vrgrp.
  rename v'5 into px.
  rename v'8 into py.
  rename v'11 into pprio.
  
  sep_conj_handlerH H2.

  assert (Int.unsigned vrgrp <= 255).
  unfolds in H5.

  math simpl in H5.
  change Byte.max_unsigned with 255 in H5.
  auto.
  lets aa: osunmapvallist_prop H8.
  simpljoin.

  eapply seq_rule.
  eapply assign_rule_general' .
  Focus 2.
  intro.
  intros.
  eapply monoasrt_imp_mono.
  apply Lv_mono.
  2:eauto.
  sep auto.

  Focus 2.
  sep auto.
  split.
  intros; sep auto.
  intros; sep auto.

  Focus 2.
  intro.
  intros.
  eapply expr_array_member_rv.
  eapply monoasrt_imp_mono.
  eapply Rv_mono.
  2:eauto.
  sep auto.
  sep auto.
  eapply monoasrt_imp_mono.
  eapply Rv_mono.
  2:eauto.
  sep auto.
  auto.
  auto.
  simpl.
  omega.
  clear -H8.
  bsimplr.
  omega.
  bsimplr.
  clear -H8.
  omega.
  Focus 2.
  eauto.
  unfolds.
  math simpls.
  bsimplr.
  math simpl in H11.
  clear -H11; omega.
  apply eq_int.
  tauto.

  intro.
  intros.
  sep lift 2%nat.
  apply xchange_asrt_ex.
  sep lift 2%nat.
  eapply monoasrt_imp_mono.
  apply startrue_mono.
  Focus 2.
  intro; intros.
  sep normal.
  apply LocalInv_H.
  eauto.
  sep auto.
  

  assert (Z.to_nat (Int.unsigned x) < length v'1)%nat as lt_len.
  rewrite H4.
  math simpl in H11.
  clear -H11.
  mauto.

  lets bb: array_int8u_nth_lt_len H3 lt_len.
  simpljoin.
  lets cc: osunmapvallist_prop H13.
  simpljoin.
  
  
  eapply seq_rule.
  eapply assign_rule_general' .
  Focus 2.

  intro.
  intros.
  eapply monoasrt_imp_mono.
  apply Lv_mono.
  2:eauto.
  sep auto.
 
  Focus 2.
  split.
  intros.
  sep auto.
  intros; sep auto.

  Focus 2.
  intro.
  intros.
  eapply expr_array_member_rv.
 
  eapply monoasrt_imp_mono.
  eapply Rv_mono.
  2:eauto.
  sep auto.
  sep auto.


  eapply expr_array_member_rv.
 
  eapply monoasrt_imp_mono.
  eapply Rv_mono.
  2:eauto.
  
  sep auto.
  sep auto.

  eapply lv_mapsto_to_rv.
  Focus 2.
  eapply monoasrt_imp_mono.
  eapply Lv_mono.
  2:eauto.
  sep auto.
  Focus 2.
  sep auto.
  unfolds.
  math simpls.
  math simpl in H11.
  bsimplr.
  omega.

  tauto.
  tauto.
  unfold OS_RDY_TBL_SIZE.
  simpl.
  omega.
  bsimplr.
  math simpl in H11; omega.
  rewrite H4.
  bsimplr.
  math simpl in H11; omega.
  Focus 2.
  eauto.
  unfolds.
  math simpls.

  tauto.
  tauto.
  simpl; omega.
  simpl.
  omega.
  bsimplr.
  omega.
  2:eauto.
  unfolds.
  math simpls.
  bsimplr.
  math simpl in H15.
  omega.
  apply eq_int.
  tauto.

  intro.
  intros.
  sep lift 2%nat.
  apply xchange_asrt_ex.
  sep lift 2%nat.
  eapply monoasrt_imp_mono.
  apply startrue_mono.
  Focus 2.
  intro; intros.
  sep normal.
  apply LocalInv_H.
  eauto.
  sep auto.
 


  eapply forward_rule2.
  eapply assign_rule_general' .
  Focus 2.
  intro; intros.
  
  eapply monoasrt_imp_mono.
  eapply Lv_mono.

  2:eauto.
  sep auto.

  Focus 2.
  split; intro; intros; sep auto.
  Focus 2.
  intros.

  eapply cast_rv_tint32_tint8.
  eapply bop_rv.

  eapply bop_rv.
  eapply lv_mapsto_to_rv.
  Focus 2.
  eapply monoasrt_imp_mono.
  eapply Lv_mono.
  2:eauto.
  sep auto.
  2:sep auto.
  unfolds.
  math simpls.
  bsimplr.
  math simpl in H11.
  omega.
  sep get rv.
  simpl.
  change (Int.ltu ($ 3) Int.iwordsize) with true.
  simpl.
  eauto.
  intro; tryfalse.
  auto.
  simpl.
  eauto.

  eapply lv_mapsto_to_rv.
  Focus 2.

  eapply monoasrt_imp_mono.
  eapply Lv_mono.
  2:eauto.
  sep auto.

  Focus 2.
  sep auto.
  unfolds.
  math simpl in H15.
  math simpls.
  simpl.
  eauto.
  intro; tryfalse.
  simpl; auto.
  simpl.
  eauto.
  apply eq_int.
  tauto.

  intro.
  intros.
  sep lift 2%nat.
  apply xchange_asrt_ex.
  sep lift 2%nat.
  eapply monoasrt_imp_mono.
  apply startrue_mono.
  Focus 2.
  intro; intros.
  sep normal.
  apply LocalInv_H.
  eauto.
  sep auto.
 

  assert (Int.unsigned x <= 7).
  math simpl in H11; omega.

  assert (Int.unsigned x1 <= 7).
  math simpl in H15; omega.

  assert ( Int.unsigned ((x<<ᵢ$ 3)+ᵢx1) < 64).
  clear -H16 H17.
  mauto.
  rewrite (mutexpost_intlemma1 _ H18).

  intros.
  sep normal.
  sep eexists.
  sep cancel 1%nat 1%nat.
  sep cancel 4%nat 3%nat.
  sep cancel 4%nat 3%nat.
  sep cancel 1%nat 5%nat.
  sep cancel 1%nat 4%nat.
  sep cancel 1%nat 3%nat.
  sep auto.
 
  Focus 2.

  clear -H16 H17; mauto.
  Focus 2.
  clear -H16 H17; mauto.

  assert (x0 <> $ 0) as anotherH2.

  lets backup: H1.
  unfolds in H1.

  assert (0<= (Z.to_nat (Int.unsigned x)) < 8)%nat.
  clear -H16.
  mauto.
  lets bbb: nth_val'_imply_nth_val H12.
  rewrite H4.
  clear -H16.
  mauto.
  lets adf: H1 H20 bbb (eq_refl (Vint32 vrgrp)).
  simpljoin.
  assert (vrgrp <> $0).
  clear -anotherH.
  math simpl in anotherH.
  auto.

  lets dasf: math_8_255_eq H8 H10 H24.
  rewrite Z2Nat.id in H22.
  rewrite Int.repr_unsigned in H22.
  apply H22 in dasf.
  clear -dasf.
  intro.
  rewrite H in dasf.
  int auto.
  clear.
  int auto.

  unfolds.
  unfolds.

  split.
  unfolds.
  intros.
(*  repeat tri_exists_and_solver1.
  clear .
  remember  ((x<<$ 3)+ᵢx1).
  clear Heqi.
  int auto.
  rewrite Int.repr_unsigned.
*)

  rewrite ob1 in H21; auto.
(*  apply nth_val'_imp_nth_val_int.
  eauto.
  rewrite Int.repr_unsigned.
*)
  rewrite ob2 in H20; auto.
(*  apply math_8_255_eq.
  auto.
  auto.*)
  subst y.
  subst x2.
  unfold nat_of_Z in H22.
  rewrite (nth_val'2nth_val _ _ _ H12) in H22.
  inverts H22.
  apply math_8_255_eq.
  auto.
  auto.
  auto.


  intros.
  lets backup: H1.
  unfolds in H1.

  assert (0<= (Z.to_nat (Int.unsigned x)) < 8)%nat.
  clear -H16.
  mauto.
  lets bbb: nth_val'_imply_nth_val H12.
  rewrite H4.
  clear -H16.
  mauto.


  lets adf: H1 H22 bbb (eq_refl (Vint32 vrgrp)).
  simpljoin.
  lets dasf: math_8_255_eq H8 H10.
  assert (vrgrp <> $0).
  clear -anotherH.
  intro.
  rewrite H in anotherH.
  int auto.
  apply dasf in H26.
  unfolds in H20.

  

  rename x into y.
  rename x1 into x.
  rename other into t.
  assert (Int.unsigned t < 64 \/ Int.unsigned t >= 64).
  tauto.
  destruct H27.

  assert (Int.unsigned (t &ᵢ $7) < 8).
  clear -H27.
  mauto.
  assert (Int.unsigned (t>>ᵢ$ 3) < 8).
  clear -H27.
  mauto.
  assert (Int.unsigned x < 8).
  omega.
  assert (Int.unsigned y < 8).
  omega.


  assert ( (nat_of_Z (Int.unsigned  ( t>>ᵢ$ 3))) <  nat_of_Z OS_RDY_TBL_SIZE)%nat.
  clear -H29.
  remember ( t>>ᵢ$ 3) as y'.
  remember (t &ᵢ ($ 7)) as x'.  
  mauto.

  lets asdf: nthval'_has_value H3 H4  H32.
  destruct asdf.
  destruct H33.
  lets bbbasfd: H20 (eq_refl (t &ᵢ ($ 7))) (eq_refl  ( t>>ᵢ$ 3)) (nth_val'2nth_val _ _ _ H33).

  lets fasf: math_highest_prio_select H31 H30 H28 H27 H29.
  cut (  Int.unsigned ((y<<ᵢ$ 3)+ᵢx) <= Int.unsigned t).
  intro.
  remember ((y<<ᵢ$ 3)+ᵢx).
  clear -H35 H21.
  int auto.
  false.
  apply H21.
  assert (Int.unsigned i = Int.unsigned t).
  omega.
  apply unsigned_inj.
  auto.

  rewrite Z2Nat.id in H24.

  rewrite Int.repr_unsigned in H24.
  remember ( t>>ᵢ$ 3) as y'.
  remember (t &ᵢ ($ 7)) as x'.
  apply fasf.
  3:eauto.
  3:eauto.
  3:eauto.
  Focus 3.
  apply nth_val'2nth_val.
  exact H33.

  auto.
  auto.
  auto.
  clear -anotherH.
  intro.
  rewrite H in anotherH.
  int auto.
  auto.
  
  2: auto.
  
(*  assert (y' <> $ 0).

  Focus 2.*)
  assert (0<=  (nat_of_Z (Int.unsigned (t>>ᵢ$ 3))) <8)%nat.
  rewrite <- Heqy'.
  clear -H29.
  mauto.
  rewrite <- Heqy' in *.

  apply nth_val'2nth_val in H33.

  lets fdasf: H1 H35 H33 (eq_refl (Vint32 vrgrp)).
  rewrite Z2Nat.id in fdasf.
  rewrite Int.repr_unsigned in fdasf.
  destruct fdasf.


  apply H37.
  cut (x1 <> $0).
  intros.
  clear -H38.


  int auto.
  false.
  apply H38.
  assert (0<=Int.unsigned x1) by int auto.
  assert (0=Int.unsigned x1) by omega.
  rewrite H0.
  
  int auto.
(*  clear.
  remember (t>>ᵢ$ 3); clear.
  int auto.
  remember (t& $ 7).
*)
  intro.
  subst x1.
  assert ( $ 0&ᵢ(Int.one<<ᵢx') <> Int.one<<ᵢx').
  clear -H28.
  mauto.
  apply H38.
  auto.
  clear.
  int auto.
  clear.
  int auto.
  clear -H18 H27.
  remember  ((y<<ᵢ$ 3)+ᵢx).
  clear Heqi.
  int auto.
Qed.

Definition inline_gethighestprio_setbit :=
  Inline_record_cons bittbl_gethighestprio_inline_code bittbl_gethighestprio_inline_pre bittbl_gethighestprio_inline_post Unnamed_thm0.

Definition bittbl_clearbit_inline_code :inline_function_code :=
  (fun (le: list expr) =>
     match le with
       | (grp :: tbl :: bitx :: bity :: y ::nil) =>
            tbl[y] =ₑ tbl[y] &ₑ (∼ bitx);ₛ
            If ( tbl[y] ==ₑ ′0) {
              grp =ₑ grp &ₑ ∼bity
            }
      | _ => Skip
    end
  ).

Definition bittbl_clearbit_inline_pre :inline_function_asrt:=
  (fun (p:asrt) (ll: list logicvar) (le: list expr) =>
(EX sc prgrp vrgrp vrtbl prtbl nrtbl nrgrp nbitx nbity ny vbitx vbity vy vx prio,
      <|| sc ||> **
          [|ll = (logic_val (Vint32 vrgrp) :: logic_lv vrtbl :: logic_val (Vptr prgrp) :: logic_val (Vptr prtbl) :: logic_val (Vint32 vbity) :: logic_val (Vint32 vbitx) :: logic_val (Vint32 vy) :: logic_val (Vint32 prio) :: logic_code sc :: nil) |] **
          [|le = nrgrp :: nrtbl :: nbitx :: nbity ::ny::nil|]**
          PV prgrp @ Int8u |-> Vint32 vrgrp **
          Aarray prtbl (Tarray Int8u ∘OS_RDY_TBL_SIZE) vrtbl **
          [| RL_Tbl_Grp_P vrtbl (Vint32 vrgrp) |] **
          [| p ==> Rv nrtbl @ Tarray Int8u  ∘OS_RDY_TBL_SIZE == Vptr prtbl //\\
             Lv nrgrp @ Int8u == prgrp //\\  
             Rv nbity @ Int8u == Vint32 vbity //\\ 
             Rv nbitx @ Int8u == Vint32 vbitx //\\ 
             Rv ny @ Int8u == Vint32 vy |] **
          [| (Z.to_nat (Int.unsigned vy) <  ∘OS_RDY_TBL_SIZE)%nat |] **
          [| array_type_vallist_match Int8u vrtbl |] **
          [| length vrtbl = ∘OS_RDY_TBL_SIZE |] **
          [| rule_type_val_match Int8u (Vint32 vrgrp) = true |] **
          [| prio >>ᵢ  ($ 3) = vy |] **
          [| prio &ᵢ ($ 7) = vx |] **
          [| vbitx = ($ 1) <<ᵢ vx |] **
          [| vbity = ($ 1) <<ᵢ vy |] **
          [| Int.unsigned prio < 64 |] 
)).

Definition bittbl_clearbit_inline_post : inline_function_asrt :=
(fun (p:asrt)(ll: list logicvar) (le: list expr) =>
     EX sc prgrp vrgrp vrtbl prtbl nrtbl nrgrp nbitx nbity ny vbitx vy vrtbl' vrgrp' prevalue vbity prio, 
           <||sc||> ** 
          [|ll = (logic_val (Vint32 vrgrp) :: logic_lv vrtbl :: logic_val (Vptr prgrp) :: logic_val (Vptr prtbl) :: logic_val (Vint32 vbity) :: logic_val (Vint32 vbitx) :: logic_val (Vint32 vy) :: logic_val (Vint32 prio) :: logic_code sc :: nil) |] **
              [|le = nrgrp :: nrtbl :: nbitx :: nbity ::ny::nil|]**
              Aarray prtbl (Tarray Int8u ∘OS_RDY_TBL_SIZE) vrtbl' **
              PV prgrp @ Int8u |-> Vint32 vrgrp' **

              [|(nth_val' (Z.to_nat (Int.unsigned vy)) vrtbl) = Vint32 prevalue /\
                       Int.unsigned prevalue <= Byte.max_unsigned |] **
              [| vrtbl' = update_nth_val (Z.to_nat (Int.unsigned vy)) vrtbl 
                                         (val_inj (and (Vint32 prevalue) (Vint32 (Int.not  vbitx))))|] ** 
              [| length vrtbl' =  ∘OS_RDY_TBL_SIZE |] **
              [| rule_type_val_match Int8u (Vint32 vrgrp') = true |] **
              [| RL_Tbl_Grp_P vrtbl' (Vint32 vrgrp') |] **
              [| forall x, prio_in_tbl x vrtbl -> Int.eq x prio = false -> prio_in_tbl x vrtbl' |] **
              [| prio_not_in_tbl prio vrtbl' |]  **
              [| array_type_vallist_match Int8u vrtbl' |] 
).


Goal make_inl_proof bittbl_clearbit_inline_code bittbl_clearbit_inline_pre bittbl_clearbit_inline_post.
Proof.
  unfolds.
  intros.
  rename H into LocalInv_H.
  unfold bittbl_clearbit_inline_pre.
  unfold bittbl_clearbit_inline_code.
  unfold bittbl_clearbit_inline_post.
  hoare_split_pure_all; subst.
  rename v'4 into nrtbl.
  rename v'5 into nrgrp.
  rename v'7 into nbity.
  rename v'6 into nbitx.
  rename v'8 into ny.
  rename v'13 into prio.
  rename v'3 into prtbl.
  rename v'2 into vrtbl.

  sep_conj_handlerH H2.

  assert ( (Z.to_nat (Int.unsigned  (prio>>ᵢ$ 3) )) <  length vrtbl )%nat.

  rewrite H5.
  clear -H11.
  mauto.
  lets fff: array_int8u_nth_lt_len H4 H8.
  simpljoin.

  eapply seq_rule.

  eapply assign_rule_ptr_array_aop.
  Focus 2.
  intro.
  split.
  intros.
  sep auto.
  intro.
  sep auto.
  intro; intros.

  eapply monoasrt_imp_mono.
  apply Rv_mono.
  2:eauto.
  sep auto.

  intro; intros.
  eapply bop_rv.

  {
    eapply expr_array_member_rv.

	eapply monoasrt_imp_mono.
	apply Rv_mono.
	2:eauto.
	sep auto.
    sep auto.

	eapply monoasrt_imp_mono.
	apply Rv_mono.
	2:eauto.
	sep auto.
    tauto.
    tauto.
    unfold OS_RDY_TBL_SIZE.
    simpl.
    clear;
    omega.
    unfold OS_RDY_TBL_SIZE.
    simpl.
    clear -H11.
    mauto.
    rewrite H5.
    unfold OS_RDY_TBL_SIZE.
    simpl.
    clear -H11.
    mauto.
	Focus 2.
    eauto.
    unfolds.
    math simpls.
  }
  eapply uop_rv.
  eapply monoasrt_imp_mono.
  apply Rv_mono.
  2:eauto.
  sep auto.
  simpl.
  eauto.
  intro; tryfalse.
  simpl.
  eauto.
  simpl.
  eauto.
  intro; tryfalse.
  simpl.
  eauto.

  intro.
  intros.
  eapply monoasrt_imp_mono.
  apply Rv_mono.
  2:eauto.
  sep auto.
  tauto.
  tauto.
  unfold OS_RDY_TBL_SIZE.
  simpl.
  clear -H11.
  mauto.
  apply eq_int.
  tauto.
  rewrite H5.
  unfold OS_RDY_TBL_SIZE.
  simpl.
  clear -H11.
  mauto.


  intro.
  intros.
  sep lift 2%nat.
  apply xchange_asrt_ex.
  sep lift 2%nat.
  eapply monoasrt_imp_mono.
  apply startrue_mono.
  Focus 2.
  intro; intros.
  sep normal.
  apply LocalInv_H.
  eauto.
  sep auto.
 


  
  remember (Int.eq (x&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))) ($ 0)).
  (* destruct b0. *)

  eapply forward_rule2.
  eapply ift_rule''.
  intro; intros.
  eapply bop_rv.
  eapply expr_array_member_rv.
  eapply monoasrt_imp_mono.
  apply Rv_mono.
  2:eauto.
  sep auto.
  sep auto.

  eapply monoasrt_imp_mono.
  apply Rv_mono.
  2:eauto.
  sep auto.
  tauto.
  tauto.

  unfold OS_RDY_TBL_SIZE.
  simpl; omega.

  unfold OS_RDY_TBL_SIZE.
  simpl; clear -H11; mauto.


  rewrite update_nth_val_len_eq.
  rewrite H5.
  unfold OS_RDY_TBL_SIZE.
  simpl.
  simpl; clear -H11; mauto.

  Focus 2.
  apply len_lt_update_get_eq.
  rewrite H5.
  unfold OS_RDY_TBL_SIZE.
  simpl.
  simpl; clear -H11; mauto.
  unfolds.
  math simpls.
  bsimplr.

  apply le255_and_le255.
  auto.

  sep get rv.
  simpl.
  rewrite <- Heqb0.
  eauto.
  intro; destruct b0; tryfalse.
  simpl; eauto.
  
  (* Locate "&=".   *)

(* "L '&=' R" := sassign L (ebinop obitand L R) *)
(* "L '=ₑ' R" := sassign L R      : code_scope *)
  hoare normal pre.
  hoare_split_pure_all.
  eapply assign_rule_general' .
  Focus 2.
  intro.
  intros.

  eapply monoasrt_imp_mono.
  apply Lv_mono.
  2:eauto.
  sep auto.

  Focus 2.
  split.
  
  intro; intros; eauto.
  sep auto.
  intro.
  sep auto.

  Focus 2.
  intro; intros.


  eapply bop_rv.

  {
	eapply lv_mapsto_to_rv.
	Focus 2.
	eapply monoasrt_imp_mono.
	apply Lv_mono.
	2:eauto.
	sep auto.

	Focus 2.
	sep auto.
	auto.
  }
  eapply uop_rv.
  eapply monoasrt_imp_mono.
  apply Rv_mono.
  2:eauto.
  sep auto.
  simpl.
  eauto.
  intro; tryfalse.
  simpl.
  eauto.
  simpl.
  eauto.
  intro; tryfalse.
  simpl.
  eauto.
  apply eq_int.
  tauto.
 

  intro.
  intros.
  sep lift 2%nat.
  apply xchange_asrt_ex.
  sep lift 2%nat.
  eapply monoasrt_imp_mono.
  apply startrue_mono.
  Focus 2.
  intro; intros.
  sep normal.
  apply LocalInv_H.
  eauto.
  sep auto.


  intro.
  intros.
  apply sep_or2or in H13.
  destruct H13.
  sep normal in H13.
  sep auto.

  {
    apply array_type_vallist_match_hold.
    auto.
    assumption.
    unfolds.
    math simpls.
    change Byte.max_unsigned with 255.
    eapply pure_lib.le255_and_le255.
    auto.
    
  }

  {
    unfold prio_not_in_tbl.
    intros.
    unfold nat_of_Z in H17.
    subst y.
    erewrite hoare_assign.update_nth in H17.
    inverts H17.
    subst x0.
    rewrite Int.and_assoc.
    Lemma and_not_zero:
      forall x,
        Int.unsigned x <= 128 ->
        Int.and (Int.not x) x = $ 0.
    Proof.
      intros.
      mauto.
    Qed.

    rewrite and_not_zero.
    apply Int.and_zero.
    clear -H11.
    mauto.
    lets bb: nth_val'_imp_nth_val_int H10.
    unfold nat_of_Z in bb.
    eauto.

  }



  {  
    intros.
    unfold prio_in_tbl in *.
    intros.
    lets fff: H15 H17 H18.
    unfold nat_of_Z in *.
    assert ( (Z.to_nat (Int.unsigned y)) <> (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3)))  \/ (Z.to_nat (Int.unsigned y)) = (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3))) ). 
    tauto.
    elim H20; intros.
    apply nth_upd_neq in H19.
    apply fff.
    exact H19.
    auto.
    rewrite <- H21 in *.

    lets fffb: H15 H17 H18 (nth_val'2nth_val _ _ _ H10). 
    apply nth_upd_eq in H19.
    simpl in H19.
    inverts H19.
    assert ( y = prio >>ᵢ $ 3).
    clear -H21.
    apply z2n_int_eq.
    auto.
    
    cut ( x1 <> (prio&ᵢ$ 7)).
    intro.
    rewrite Int.and_assoc.
    rewrite int_not_shrl_and.
    auto.
    rewrite Int.and_commut.
    set(Int.and_le ($7) prio).
    clear -l.
    ur_rewriter_in l.
    omega.

    subst x1.
    rewrite Int.and_commut.
    set(Int.and_le ($7) x0).
    clear -l.
    ur_rewriter_in l.
    omega.
    auto.

    math simpl in H16.
    subst.
    apply not_eq_at_least_one_part_not_eq.
    auto.
    auto.
   
  }
  {

Lemma event_wait_rl_tbl_grp':
  forall x10 x9 x8 x7 i10 i6 i5 i4 i3 i2 i1 i0 v'1 x,
    RL_TCBblk_P
      (x10
         :: x9
         :: x8
         :: x7
         :: Vint32 i10
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: nil) ->
    array_type_vallist_match Int8u v'1 ->
    Int.eq (x&ᵢInt.not i2) ($ 0) = true ->
    RL_Tbl_Grp_P v'1 (Vint32 i0) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned i3)) v'1 (Vint32 (x&ᵢInt.not i2)))
      (Vint32 (i0&ᵢInt.not i1)).
Proof.
  introv Hrl Harr  Hint Hrll.
  assert (if Int.eq (x&ᵢInt.not i2) ($ 0) then
            (x&ᵢInt.not i2)  = $ 0 else   (x&ᵢInt.not i2)  <> $ 0  ) by (apply Int.eq_spec).
  rewrite Hint in H.
  rewrite H.
  unfolds in Hrl.
  funfold Hrl.
  funfold Hrll.
  unfolds.
  introv Hn Hnth Hvin.
  assert (n <> (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3)))) \/
          n = (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3))))) by tauto.
  destruct H0.
  lets Hex : nth_upd_neq H0 Hnth.
  assert (Vint32 i0 = Vint32 i0) by auto.
  lets Hes : Hrll Hn Hex H1.
  destruct Hes.
  inverts Hvin.
  lets Hzx : math_prop_and H0; try omega; auto.
  splits.
  destruct H2.
  split.
  intros.
  apply H2.
  rewrite Int.and_assoc in H5. 
  rewrite Hzx in H5.
  auto.
  intros.
  apply H4 in H5.
  rewrite Int.and_assoc.
  rewrite Hzx ; auto.
  split.
  intros.
  destruct H3.
  rewrite Int.and_assoc in H4.
  rewrite Hzx in H4.
  apply H3; auto.  
  intros.
  rewrite Int.and_assoc.
  rewrite Hzx.
  apply H3; auto.
  subst n.
  lets Hdx : nth_upd_eq Hnth.
  inverts Hdx.
  inverts Hvin.
  assert ( 0 <= Int.unsigned x0 < 64) by omega.
  lets Hdd : math_prop_eq0 H0.
  split.
  split; auto.
  intros.
  rewrite Int.and_assoc.
  rewrite Hdd.
  rewrite Int.and_zero.
  auto.
  rewrite Int.and_assoc.
  rewrite Hdd.
  rewrite Int.and_zero.
  split.
  intros.
  apply math_lshift_neq_zero in H0.
  tryfalse.
  intros.
  clear -H1.
  false.
Qed.


    eapply event_wait_rl_tbl_grp'.
    unfolds.
    repeat tri_exists_and_solver1.
    go.
    go.
    go.
    go.
    go.
    go.
    clear; int auto.
    go.
    auto.
    2: auto.
    simpljoin.
    remember ( Int.eq (x&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))) ($ 0)).
    destruct b0.

    auto.
    false.
    apply H14.
    auto.
  }
  {
    unfolds.
    math simpls.
    eapply pure_lib.le255_and_le255. 
    unfolds in H6.
    math simpl in H6.
    exact H6.
  }
  

  rewrite <- update_nth_val_length_eq.
  auto.

  simpl.
  eauto.
  splits; auto.


  sep auto.

  {
    apply array_type_vallist_match_hold.
    auto.
    assumption.
    unfolds.
    math simpls.
    change Byte.max_unsigned with 255.
    eapply pure_lib.le255_and_le255.
    auto.
    
  }


  {
    unfold prio_not_in_tbl.
    intros.
    unfold nat_of_Z in H17.
    subst y.
    erewrite hoare_assign.update_nth in H17.
    inverts H17.
    subst x0.
    rewrite Int.and_assoc.
    rewrite and_not_zero.
    apply Int.and_zero.
    clear -H11.
    mauto.
    lets bb: nth_val'_imp_nth_val_int H10.
    unfold nat_of_Z in bb.
    eauto.
  }


  intros.
  {  
    intros.
    unfold prio_in_tbl in *.
    intros.
    lets fff: H15 H17 H18.
    unfold nat_of_Z in *.
    assert ( (Z.to_nat (Int.unsigned y)) <> (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3)))  \/ (Z.to_nat (Int.unsigned y)) = (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3))) ). 
    tauto.
    elim H20; intros.
    apply nth_upd_neq in H19.
    apply fff.
    exact H19.
    auto.
    rewrite <- H21 in *.

    lets fffb: H15 H17 H18 (nth_val'2nth_val _ _ _ H10). 
    apply nth_upd_eq in H19.
    simpl in H19.
    inverts H19.
    assert ( y = prio >>ᵢ $ 3).
    clear -H21.
    apply z2n_int_eq.
    auto.
    
    cut ( x1 <> (prio&ᵢ$ 7)).
    intro.
    rewrite Int.and_assoc.
    rewrite int_not_shrl_and.
    auto.
    rewrite Int.and_commut.
    set(Int.and_le ($7) prio).
    clear -l.
    ur_rewriter_in l.
    omega.

    subst x1.
    rewrite Int.and_commut.
    set(Int.and_le ($7) x0).
    clear -l.
    ur_rewriter_in l.
    omega.
    auto.

    math simpl in H16.
    subst.
    apply not_eq_at_least_one_part_not_eq.
    auto.
    auto.
   
  }
  {

Lemma event_wait_rl_tbl_grp'':
  forall x10 x9 x8 x7 i10 i6 i5 i4 i3 i2 i1 i0 v'1 x,
    RL_TCBblk_P
      (x10
         :: x9
         :: x8
         :: x7
         :: Vint32 i10
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: nil) ->
    array_type_vallist_match Int8u v'1 ->
    nth_val' (Z.to_nat (Int.unsigned i3)) v'1 = Vint32 x ->
    Int.eq (x&ᵢInt.not i2) ($ 0) = false ->
    RL_Tbl_Grp_P v'1 (Vint32 i0) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned i3)) v'1 (Vint32 (x&ᵢInt.not i2)))
      (Vint32 i0).
Proof.
  introv Hrl Harr Htt Hnth Hrt.
  funfold Hrl.
  funfold Hrt.
  assert ( 0 <= Int.unsigned x0 < 64) as Hran by omega.
  clear H5 H13.
  unfolds.
  introv Hn Hnv Hvi.
  inverts Hvi.
  assert (n <> (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3)))) \/
          n = (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3))))) by tauto.
  destruct H.
  lets Hex : nth_upd_neq H Hnv.
  assert (Vint32 v' = Vint32 v') by auto.
  lets Hexz : Hrt Hn Hex H0.
  destruct Hexz as (He1 & He2).
  auto.
  subst n.
  lets Hins : nth_upd_eq  Hnv.
   apply nth_val'_imp_nth_val_int in Htt.
   assert (Vint32 v' = Vint32 v') by auto.
  lets Hdx : Hrt Hn Htt H.
  inverts Hins.
  split.
  split.
  destruct Hdx.
  intros.
  apply H0 in H2.
  subst.
  rewrite Int.and_commut.
  rewrite Int.and_zero.
  auto.
  intros.
  rewrite H0 in Hnth.
  rewrite Int.eq_true in Hnth.
  tryfalse.
  split.
  intros.
  destruct Hdx.
  apply H2 in H0.
  apply int_eq_false_ltu; eauto.
  intros.
  destruct Hdx.
  apply H2.
  apply int_eq_false_ltu; eauto.
  apply Int.eq_false.
  assert (   x <> $ 0  \/  x = $ 0) by tauto.
  destruct H3; auto.
  subst x.
  rewrite Int.and_commut in Hnth.
  rewrite Int.and_zero in Hnth.
  unfold Int.zero in Hnth.
  rewrite Int.eq_true in Hnth.
  tryfalse.
Qed.



    eapply event_wait_rl_tbl_grp''.
    unfolds.
    repeat tri_exists_and_solver1.
    go.
    go.
    go.
    go.
    go.
    go.
    clear; int auto.
    go.
    auto.
    auto.
    2: auto.
    simpljoin.
    remember ( Int.eq (x&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))) ($ 0)).
    destruct b0.

    false.
    destruct H14; intros.
    inverts H14.
    inverts H14.
    auto.
  }

  rewrite <- update_nth_val_length_eq.
  auto.

  simpl.
  eauto.
  splits; auto.

  Unshelve.
  exact (V$ 0).
  exact (V$ 0).
  exact (V$ 0).
  exact ($ 0).
  exact (V$ 0).
  exact (V$ 0).
  exact (V$ 0).
  exact ($ 0).
Qed.


Definition inline_bittbl_clearbit :=
  Inline_record_cons bittbl_clearbit_inline_code bittbl_clearbit_inline_pre bittbl_clearbit_inline_post Unnamed_thm1.

