Require Import Integers.
Require Import ZArith.
Require Import Coqlib.
Require Import LibTactics.

Local Close Scope nat_scope.
Local Open Scope Z_scope.

(* these tactics may not be here *)

Ltac csimpl a := let val:= eval compute in a in change a with val.
Ltac icsimpl a := let val:= eval compute -[Int.unsigned] in a in change a with val.

Ltac csimplH a H := let val:= eval compute in a in change a with val in H. 
Ltac icsimplH a H := let val:= eval compute -[Int.unsigned] in a in change a with val in H.

Ltac desif H :=
  let ifexpr := fresh in
  match goal with
    | |- context[(if ?e then _ else _) = _] => remember (e) as ifexpr eqn:H ;apply EqdepFacts.internal_eq_sym_internal in H; destruct ifexpr; auto
  end.

Ltac simplifH H :=
  let ifexpr := fresh in
  let H' := fresh in 
  match type of H with
    | context[(if ?e then _ else _ ) = _] => rename H into H'; remember (e) as ifexpr eqn:H; apply EqdepFacts.internal_eq_sym_internal in H;  destruct ifexpr; tryfalse ;clear H'
  end.

Tactic Notation "ifsimpl" := let H := fresh in desif H.
Tactic Notation "ifsimpl" "in" constr(H) := simplifH H.

(* really math rewriter *)

Lemma Intlt_true_is_Zlt :
  forall a b,
    Int.ltu a b = true <-> Int.unsigned a < Int.unsigned b.
Proof.
  intros.
  split; intros.
  unfold Int.ltu in H.
  destruct (zlt (Int.unsigned a) (Int.unsigned b)).
  auto.
  inversion H.
  
  unfold Int.ltu .
  destruct (zlt (Int.unsigned a) (Int.unsigned b)).
  auto.
  omega.
Qed.  

Lemma Intlt_false_is_Zge :
  forall a b,
    Int.ltu a b = false <-> Int.unsigned a >= Int.unsigned b.
Proof.
  intros.
  split; intros; unfold Int.ltu in *; destruct (zlt (Int.unsigned a) (Int.unsigned b)); auto.
  inversion H.
  omega.
Qed.

Lemma Inteq_true_is_Zeq :
  forall a b,
    Int.eq a b = true <-> Int.unsigned a = Int.unsigned b.
Proof.
  intros.
  split; intros; unfold Int.eq in *; destruct (zeq (Int.unsigned a) (Int.unsigned b)); auto.
  inversion H.
Qed.

Lemma Inteq_false_is_Zneq :
  forall a b,
    Int.eq a b = false <-> Int.unsigned a <> Int.unsigned b.
Proof.
  intros.
  split; intros; unfold Int.eq in *; destruct (zeq (Int.unsigned a) (Int.unsigned b)); auto; try intro.
  inversion H.
  omega.
Qed.

Lemma ZInteq_imp_Zeq:
  forall a b,
    Int.unsigned a = Int.unsigned b <->
    a = b.
Proof.
  intros.
  split; intro.
  rewrite <- Inteq_true_is_Zeq in H.
  change (if true then a=b else a <> b).
  rewrite <- H.
  apply Int.eq_spec.
  subst; auto.
Qed.

Lemma ZIntneq_is_Zneq:
  forall a b,
    Int.unsigned a <> Int.unsigned b <->
    a <> b.
Proof.
  intros.
  unfold not.
  rewrite ZInteq_imp_Zeq.
  tauto.
Qed. 


Lemma Zleb_le: forall n m : Z,   (n <=? m) = true <-> n <= m.
Proof.
  symmetry.
  apply Zle_is_le_bool.
Qed.

Hint Rewrite Intlt_true_is_Zlt Intlt_false_is_Zge Inteq_true_is_Zeq Inteq_false_is_Zneq ZInteq_imp_Zeq ZIntneq_is_Zneq
     Z.leb_gt Zleb_le Z.geb_leb Z.ltb_antisym Z.gtb_ltb Z.eqb_eq Z.eqb_neq:
 math_rewrite_base.

Ltac bsimplH H:=
  match type of H with
    | _ ?a ?b => try timeout 2 icsimplH a H; try timeout 2 icsimplH b H
  end.

Ltac bsimpl :=
  match goal with
    | |- _ ?a ?b => try timeout 2 icsimpl a; try timeout 2 icsimpl b 
  end.

Ltac bsimplHl H:=
  match type of H with
    | _ ?a ?b => try timeout 2 icsimplH a H
  end.

Ltac bsimpll :=
  match goal with
    | |- _ ?a ?b => try timeout 2 icsimpl a
  end.

Ltac bsimplHr H:=
  match type of H with
    | _ ?a ?b => try timeout 2 icsimplH b H
  end.

Ltac bsimplr :=
  match goal with
    | |- _ ?a ?b => try timeout 2 icsimpl b
  end.


Ltac math_simplH H :=  repeat first[ ifsimpl in H | autorewrite with math_rewrite_base in H] .

Tactic Notation "math" "simpl" "in" constr(H) :=math_simplH H.

Ltac math_simpl H :=repeat first[ desif H; math simpl in H| autorewrite with math_rewrite_base ].

Tactic Notation "math" "simpl" := let H:= fresh in math_simpl H.

Ltac math_add_negH H :=
  match type of H with
    | ~ _ => idtac
    | _ => first [rewrite Z.le_ngt in H| rewrite Z.lt_nge in H| rewrite Z.ge_le_iff in H| rewrite Z.gt_lt_iff in H];math_add_negH H
  end.

Ltac math_prove_neg H :=
  false; math_add_negH H; apply H; clear H.

Tactic Notation "math" "prove" "neg" constr(H) := math_prove_neg H.

Tactic Notation "math" "simpls" := let H := fresh in math_simpl H; math prove neg H; try solve [bsimpl; omega].


(* examples *)

Goal forall a b, (if Int.ltu a b then true else false) = true -> Int.unsigned a < Int.unsigned b.
Proof.
  intros.
  math simpl in H.
  auto.
Abort.

Goal forall x, Int.unsigned x <= 255 ->   (if Int.unsigned x <=? Int16.max_unsigned then true else false) = true .
Proof.
  intros.
  math simpl.
  bsimplH H0.
  math prove neg H0.
  bsimplr.
  auto.
Abort.

Ltac revs := 
  match goal with 
    |  |- ?a < ?b => cut (b > a); [intro; omega| idtac]
    |  |- ?a > ?b => cut (b < a); [intro; omega| idtac]
    |  |- ?a >= ?b => cut (b <= a); [intro; omega| idtac]
    |  |- ?a <= ?b => cut (b >= a); [intro; omega| idtac]
  end.

Ltac revs' H := 
  match type of H with 
    |  ?a < ?b => assert (b > a) by omega
    |  ?a > ?b => assert (b < a) by omega
    |  ?a >= ?b => assert (b <= a) by omega
    |  ?a <= ?b => assert (b >= a) by omega
  end.


Lemma a_mult_b_ge_b : forall a b, 0<a -> 0<=b -> a*b >= b.
Proof.  
  intros.
  apply Zle_lt_or_eq in H0.
  elim H0; intros.
  apply Zlt_le_succ in H.
  simpl in H.
  assert (a = Z.succ (Z.pred a)) by omega.
  rewrite H2 at 1.
  rewrite <- Zmult_succ_l_reverse.
  assert (Z.pred a * b >=0).
  revs.
  apply Zmult_gt_0_le_0_compat.
  omega.
  omega.
  omega.
  rewrite <- H1.
  rewrite <- Zmult_0_r_reverse.
  omega.
Qed.

Lemma div_in_intrange: 
  forall x a mx, 0<=x <=mx -> a>0 -> 0<=x/a<=mx.
Proof.
  intros.
  split.
  revs.
  apply Z_div_ge0.
  omega.
  omega.
  apply Z.div_le_upper_bound.
  omega.
  elim H; intros.
  eapply Zle_trans.
  exact H2.
  revs.
  apply a_mult_b_ge_b; omega.
Qed.

Ltac clear_useless_int32 :=
  match goal with
    | a : int32 |- _ => clear dependent a
  end.

Ltac clear_all_useless_int32 := repeat clear_useless_int32.

Ltac solve_int_range' := 
  match goal with 
    | i : int32 |- _ =>
      let xval := fresh in 
      let xrange := fresh in destruct i as [xval xrange]; 
        unfold Int.modulus, two_power_nat, shift_nat in xrange; 
        simpl in xrange; simpl in *;  
        solve_int_range'
    | _ => subst; 
        try csimpl Int.max_unsigned; solve [ omega | apply div_in_intrange; omega ]
  end.

Ltac rangesolver :=
  clear_all_useless_int32; 
  try solve_int_range';
  repeat (rewrite Int.unsigned_repr; try solve_int_range').

Ltac ur_rewriter := 
  rewrite Int.unsigned_repr; [idtac| try solve[rangesolver] ].

Ltac ur_rewriter_in H := 
  rewrite Int.unsigned_repr in H; [idtac|clear H; try solve[rangesolver] ].

Ltac trivial_ur_rewriterH H :=
  repeat (rewrite Int.unsigned_repr in H; [idtac |solve [split;[omega| try csimpl Int.max_unsigned; omega]]]).

