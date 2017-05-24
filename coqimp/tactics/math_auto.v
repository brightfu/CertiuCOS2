Require Export int_auto.
Require Export math_sol.
Require Export math_rewrite.
(*
Require Import Coqlib.
Require Import Integers.
Require Import ZArith.
Require Import LibTactics.

Open Scope Z_scope.

(** * Frequently used lemmas in tactics. *)

Lemma min_signed_lt0 : Int.min_signed < 0.
Proof.
  unfold Int.min_signed, Int.half_modulus, Int.modulus.
  simpl; omega.
Qed.

Lemma max_signed_gt0 : Int.max_signed > 0.
Proof.
  unfold Int.max_signed, Int.half_modulus, Int.modulus.
  simpl; omega.
Qed.

Lemma zdiv_equiv: forall x y : Z, x >= 0 -> y > 0 -> x ÷ y = x / y.
Proof.
  intros.
  rewrite Int.Zquot_Zdiv.
  destruct (zlt x 0).
  omega.
  trivial.
  assumption.
Qed.

Lemma zadd_rm_head: forall n p q, p = q -> n + p = n + q.
Proof.
  intros.
  rewrite H.
  trivial.
Qed.

Lemma zadd_rm_tail: forall n p q, p = q -> p + n = q + n.
Proof.
  intros.
  rewrite H.
  trivial.
Qed.

Lemma zdiv_range_le_lt : forall a b c x: Z, a <= 0 -> b > 0 -> c > 0 -> a <= x < b -> a <= x/ c < b.
Proof.
  intros.
  destruct H2.
  split.
  apply Zdiv_le_lower_bound.
  omega.
  assert(a * c <= a).
  assert(- a * c >= - a).
  rewrite <- Zmult_1_r.
  assert(c >= 1) by omega.
  apply Zmult_ge_compat_l.
  omega.
  omega.
  rewrite Zopp_mult_distr_l_reverse in H4.
  omega.
  omega.
  apply Zdiv_lt_upper_bound.
  omega.
  assert(b <= b * c).
  rewrite <- Zmult_1_r at 1.
  assert(1 <= c) by omega.
  apply Zmult_le_compat_l.
  omega.
  omega.
  omega.
Qed.

Lemma zdiv_range_le_le : forall a b c x: Z, a <= 0 -> b > 0 -> c > 0 -> a <= x <= b -> a <= x/ c <= b.
Proof.
  intros.
  destruct H2.
  split.
  apply Zdiv_le_lower_bound.
  omega.
  assert(a * c <= a).
  assert(- a * c >= - a).
  rewrite <- Zmult_1_r.
  assert(c >= 1) by omega.
  apply Zmult_ge_compat_l.
  omega.
  omega.
  rewrite Zopp_mult_distr_l_reverse in H4.
  omega.
  omega.
  apply Zdiv_le_upper_bound.
  omega.
  assert(b <= b * c).
  rewrite <- Zmult_1_r at 1.
  assert(1 <= c) by omega.
  apply Zmult_le_compat_l.
  omega.
  omega.
  omega.
Qed.

Lemma max_unsigned_gt0: Int.max_unsigned > 0.
Proof.
  unfold Int.max_unsigned, Int.modulus.
  simpl; omega.
Qed.

Lemma max_unsigned_val: Int.max_unsigned  = 4294967295.
Proof.
  unfold Int.max_unsigned, Int.modulus.
  simpl; omega.
Qed.

Lemma max_signed_val : Int.max_signed = 2147483647.
Proof.
  unfold Int.max_signed, Int.half_modulus, Int.modulus.
  simpl; omega.
Qed.

Lemma min_signed_val : Int.min_signed = -2147483648.
Proof.
  unfold Int.min_signed, Int.half_modulus, Int.modulus.
  simpl; omega.
Qed.

Lemma unsigned_mone_val : Int.unsigned Int.mone = 4294967295.
Proof.
  rewrite Int.unsigned_mone.
  simpl; auto.
Qed.

Lemma modulus_val : Int.modulus = 4294967296.
Proof.
  unfold Int.modulus.
  simpl; auto.
Qed.

Lemma unsigned_inj : forall a b, Int.unsigned a = Int.unsigned b -> a = b.
Proof.
  intros. rewrite <- (Int.repr_unsigned a).
  rewrite <- (Int.repr_unsigned b).
  f_equal.
  trivial.
Qed.

Lemma minus1lt: forall i:Z, i - 1 < i.
Proof.
  intro.
  omega.
Qed.

Lemma Z_land_range_lo: forall x y, 0 <= x -> 0 <= Z.land x y.
Proof.
  intros.
  rewrite Z.land_nonneg.
  left.
  assumption.
Qed. 

Lemma Z_land_range_lo_r: forall x y, 0 <= y -> 0 <= Z.land x y.
Proof.
  intros.
  rewrite Z.land_nonneg.
  right.
  assumption.
Qed.

Lemma Z_land_range_hi: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned -> Z.land x y <= Int.max_unsigned.
Proof.
  rewrite max_unsigned_val.
  intros.
  assert(Z.land x y < 4294967296).
  apply Z.log2_lt_cancel.
  assert(Z.log2 (Z.land x y) <= Z.min (Z.log2 x) (Z.log2 y)).
  apply Z.log2_land.
  omega.
  omega.
  rewrite Zmin_spec in H1.
  destruct (zlt (Z.log2 x) (Z.log2 y)).
  assert(Z.log2 x <= Z.log2 4294967295).
  apply Z.log2_le_mono.
  omega.
  simpl in *.
  omega.
  assert(Z.log2 y <= Z.log2 4294967295).
  apply Z.log2_le_mono.
  omega.
  simpl in *.
  omega.
  omega.
Qed.   

Lemma Z_land_range: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned -> 0 <= Z.land x y <= Int.max_unsigned.
Proof.
  split.
  apply Z_land_range_lo; omega.
  apply Z_land_range_hi; omega.
Qed.

Lemma Z_lor_range_lo: forall x y, 0 <= x -> 0 <= y -> 0 <= Z.lor x y.
Proof.
  intros.
  apply Z.lor_nonneg; auto.
Qed.

Lemma Z_lor_range_hi: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned -> Z.lor x y <= Int.max_unsigned.
Proof.
  rewrite max_unsigned_val; simpl.
  intros.
  assert(Z.lor x y < 4294967296).
  apply Z.log2_lt_cancel.
  assert(Z.log2 (Z.lor x y) = Z.max (Z.log2 x) (Z.log2 y)).
  apply Z.log2_lor.
  omega.
  omega.
  rewrite H1.
  rewrite Zmax_spec in *.
  destruct (zlt (Z.log2 y) (Z.log2 x)).
  assert(Z.log2 x <= Z.log2 4294967295).
  apply Z.log2_le_mono.
  omega.
  simpl in *.
  omega.
  assert(Z.log2 y <= Z.log2 4294967295).
  apply Z.log2_le_mono.
  omega.
  simpl in *.
  omega.
  omega.
Qed.

Lemma Z_lor_range: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned -> 0 <= Z.lor x y <= Int.max_unsigned.
Proof.
  intros.
  split.
  apply Z_lor_range_lo; omega.
  apply Z_lor_range_hi; omega.
Qed.

Lemma Z_lxor_range :
  forall x y,
    0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
    0 <= Z.lxor x y <= Int.max_unsigned.
Proof.
  rewrite max_unsigned_val; simpl.
  intros.
  split.
  rewrite Z.lxor_nonneg.
  split; omega.
  assert(Z.lxor x y < 4294967296).
  apply Z.log2_lt_cancel.
  assert(Z.log2 (Z.lxor x y) <= Z.max (Z.log2 x) (Z.log2 y)).
  apply Z.log2_lxor.
  omega.
  omega.
  apply Z.le_lt_trans with (m := Z.max (Z.log2 x) (Z.log2 y)); auto.
  rewrite Zmax_spec in *.
  destruct (zlt (Z.log2 y) (Z.log2 x)).
  assert(Z.log2 x <= Z.log2 4294967295).
  apply Z.log2_le_mono.
  omega.
  simpl in *.
  omega.
  assert(Z.log2 y <= Z.log2 4294967295).
  apply Z.log2_le_mono.
  omega.
  simpl in *.
  omega.
  omega.
Qed.

Lemma Z_shiftl_16_range :
  forall x,
    0 <= x < 65536 -> 0 <= Z.shiftl x 16 <= Int.max_unsigned.
Proof.
  unfold Int.max_unsigned. simpl (Int.modulus - 1).
  intros.
  split.
  rewrite Z.shiftl_nonneg. omega.

  assert (Z.shiftl x 16 < 4294967296).
  case_eq (zeq x 0); intros; subst.

  (* x = 0 *)
  simpl. omega.

  (* x <> 0 *)
  apply Z.log2_lt_cancel.
  rewrite Z.log2_shiftl; try omega.

  assert (Z.log2 x <= Z.log2 65535).
  apply Z.log2_le_mono. omega.
  simpl in *. omega.

  omega.
Qed.

(** * Hints for autorewrite *)

Lemma unsigned_zero: Int.unsigned Int.zero = 0.
Proof. reflexivity. Qed.

Lemma unsigned_one: Int.unsigned Int.one = 1.
Proof. reflexivity. Qed.

Lemma eq_one_zero: Int.eq Int.one Int.zero = false.
Proof. reflexivity. Qed.

Lemma eq_zero_zero: Int.eq Int.zero Int.zero = true.
Proof. reflexivity. Qed.

Lemma negb_true: negb true = false.
Proof. reflexivity. Qed.

Lemma negb_false: negb false = true.
Proof. reflexivity. Qed.

Lemma repr_zero: Int.repr 0 = Int.zero.
Proof. reflexivity. Qed.

Lemma repr_one: Int.repr 1 = Int.one.
Proof. reflexivity. Qed.

Lemma and_zero_zero: Z.land 0 0 = 0.
Proof. reflexivity. Qed.

Lemma and_one_zero: Z.land 1 0 = 0.
Proof. reflexivity. Qed.

Lemma and_zero_one: Z.land 0 1 = 0.
Proof. reflexivity. Qed.

Lemma and_one_one: Z.land 1 1 = 1.
Proof. reflexivity. Qed.

Lemma or_zero_zero: Z.lor 0 0 = 0.
Proof. reflexivity. Qed.

Lemma or_one_zero: Z.lor 1 0 = 1.
Proof. reflexivity. Qed.

Lemma or_zero_one: Z.lor 0 1 = 1.
Proof. reflexivity. Qed.

Lemma or_one_one: Z.lor 1 1 = 1.
Proof. reflexivity. Qed.

Hint Rewrite unsigned_zero unsigned_one eq_one_zero eq_zero_zero negb_true negb_false repr_zero repr_one: arith.
Hint Rewrite and_zero_zero and_zero_one and_one_zero and_one_one or_zero_zero or_zero_one or_one_zero or_one_one : arith.


(** * Auxiliary tactics used by other main tactics below. *)
(* Check svn version before 1408 *)

Ltac simpleproof := match goal with
                      | [|- _ <= _] => tryfalse || assumption || omega || trivial || eassumption || auto || idtac
                      | _ => tryfalse || assumption || omega || trivial || reflexivity || eassumption || auto || idtac
                    end.

Ltac autorewritearith := autorewrite with arith using simpleproof.

Ltac solve_signed_range c x:= 
  assert(cge0: c > 0) by omega; 
  generalize(zdiv_range_le_le Int.min_signed Int.max_signed c (Int.signed x) min_signed_lt0 max_signed_gt0 cge0 (Int.signed_range x));
  omega; clear cge0.

Ltac solve_unsigned_range c x :=
  assert(cge0: c > 0) by omega;
  assert(zlez: 0 <= 0) by omega; 
  generalize(zdiv_range_le_le 0 Int.max_unsigned c (Int.unsigned x) zlez max_unsigned_gt0 cge0 (Int.unsigned_range_2 x));
  omega; clear cge0 zlez.

Ltac solve_unsigned_range_lt c x := 
  assert(cge0: c > 0) by omega; 
  assert(zlez: 0 <= 0) by omega;
  assert(xpre: 0 <= x < Int.max_unsigned) by omega;
  generalize(zdiv_range_le_lt 0 Int.max_unsigned c x zlez max_unsigned_gt0 cge0 xpre);
  omega; clear cge0 zlez xpre.

Ltac computedivmul := 
  match goal with
    | [|- context [?x / ?y]] => let val := eval compute in (x / y) in change (x / y) with val
    | [|- context [?x * ?y]] => let val := eval compute in (x * y) in change (x * y) with val
  end.


(** * The tactic to prove the integers fit in signed range or unsigned range. *)

Ltac gen_signed_unsigned_range e :=
  let H := fresh in
  match e with
    | ?e1 + ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2
    | ?e1 - ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2
    | ?e1 * ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2
    | ?e1 / ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2
    | context [ Int.signed ?i ] => 
      generalize (Int.signed_range i);
        intros H; rewrite max_signed_val in H; rewrite min_signed_val in H
    | context [ Int.unsigned ?i ] =>
      generalize (Int.unsigned_range i);
        intros H; rewrite modulus_val in H    
    | _ => idtac
  end.

Ltac solve_int_unequal :=
  match goal with
    | H: _ /\ _ |- _=> destruct H; solve_int_unequal
    | |- _ /\ _ => split; solve_int_unequal
    | |- ?e1 <= ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2; try omega
    | |- ?e1 < ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2; try omega
    | |- ?e1 >= ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2; try omega
    | |- ?e1 > ?e2 => gen_signed_unsigned_range e1; gen_signed_unsigned_range e2; try omega
    | |- Int.min_signed <= Int.signed ?x / ?c =>
      solve_signed_range c x
    | |- Int.min_signed <= ?x / ?c => 
      rewrite <- Int.signed_repr with (z:= x); solve_signed_range c (Int.repr x)
    | |- Int.signed ?x / ?c <= Int.max_signed =>
      solve_signed_range c x
    | |- ?x / ?c <= Int.max_signed => 
      rewrite <- Int.signed_repr with (z:= x); solve_signed_range c (Int.repr x)
    | |- 0 <= Int.unsigned ?x / ?c => solve_unsigned_range c x
    | |- 0 <= ?x / ?c => rewrite <- Int.unsigned_repr with (z:= x); solve_unsigned_range c (Int.repr x)
    | |- 0 <= ?x / ?c + 1 => rewrite <- Int.unsigned_repr with (z:= x); solve_unsigned_range c (Int.repr x)
    | |- Int.unsigned ?x / ?c <= Int.max_unsigned => solve_unsigned_range c x
    | |- ?x / ?c <= Int.max_unsigned => rewrite <- Int.unsigned_repr with (z:= x); solve_unsigned_range c (Int.repr x)
    | |- ?x / ?c + 1 <= Int.max_unsigned => solve_unsigned_range_lt c x
    | |- ?x / ?y * ?c => try (computedivmul; omega)
    | _ => idtac
  end.

 
   

Ltac unsigned_range := 
  match goal with
   | [|- 0 <= ?af] =>
      match af with
        | Z.shiftl _ _ => simpl; try omega
        | Z.shiftr _ _ => simpl; try omega
        | Z.land ?x ?y => apply Z_land_range_lo; try (simpl; omega)
        | Z.lor ?x ?y => apply Z_lor_range_lo; try (simpl; omega)
        | _ => try omega
      end
    | [|- ?af <= Int.max_unsigned] => 
      match af with
        | Z.shiftl _ _ => simpl; try omega
        | Z.shiftr _ _ => simpl; try omega
        | Z.land ?x ?y => apply Z_land_range_hi; try (simpl; omega)
        | Z.lor ?x ?y => apply Z_lor_range_hi; try (simpl; omega)
        | _ => repeat rewrite max_unsigned_val; try omega
      end
  end.

Ltac int_auto_simpl :=
  match goal with
    | H: _ /\ _ |- _ => destruct H; int_auto_simpl

    | H: context [Int.signed Int.zero] |- _ => change (Int.signed Int.zero) with 0 in H; int_auto_simpl
    | |- context [Int.signed Int.zero] => change (Int.signed Int.zero) with 0; int_auto_simpl
    | H: context [Int.signed Int.one] |- _ => change (Int.signed Int.one) with 1 in H; int_auto_simpl
    | |- context [Int.signed Int.one] => change (Int.signed Int.one) with 1; int_auto_simpl

    | H: context [Int.unsigned Int.zero] |- _ => change (Int.unsigned Int.zero) with 0 in H; int_auto_simpl
    | |- context [Int.unsigned Int.zero] => change (Int.unsigned Int.zero) with 0; int_auto_simpl
    | H: context [Int.unsigned Int.one] |- _ => change (Int.unsigned Int.one) with 1 in H; int_auto_simpl
    | |- context [Int.unsigned Int.one] => change (Int.unsigned Int.one) with 1; int_auto_simpl
    | H: context [Int.unsigned Int.mone] |- _ => rewrite unsigned_mone_val in H; int_auto_simpl
    | |- context [Int.unsigned Int.mone] => rewrite unsigned_mone_val; int_auto_simpl

    | H: context [Int.eq ?x ?x] |- _ => rewrite Int.eq_true in H; int_auto_simpl
    | |- context [Int.eq ?x ?x] => rewrite Int.eq_true; int_auto_simpl
    | H: context [Int.eq Int.one Int.zero] |- _ => change (Int.eq Int.one Int.zero) with false in H; int_auto_simpl
    | |- context [Int.eq Int.one Int.zero] => change (Int.eq Int.one Int.zero) with false; int_auto_simpl

    | H: context [Int.and Int.zero _] |- _ => rewrite Int.and_zero_l in H; int_auto_simpl
    | |- context [Int.and Int.zero _] => rewrite Int.and_zero_l; int_auto_simpl
    | H: context [Int.and _ Int.zero] |- _ => rewrite Int.and_zero in H; int_auto_simpl
    | |- context [Int.and _ Int.zero] => rewrite Int.and_zero; int_auto_simpl
                                                                 
    | H: context [negb true] |- _ => change (negb true) with false in H; int_auto_simpl
    | |- context [negb true] => change (negb true) with false; int_auto_simpl
    | H: context [negb false] |- _ => change (negb false) with true in H; int_auto_simpl
    | |- context [negb false] => change (negb false) with true; int_auto_simpl

    | H: context [Int.repr (Int.signed _)] |- _ => rewrite Int.repr_signed in H; int_auto_simpl
    | |- context [Int.repr (Int.signed _)] => rewrite Int.repr_signed; int_auto_simpl
    | H: context [Int.repr (Int.unsigned _)] |- _ => rewrite Int.repr_unsigned in H; int_auto_simpl
    | |- context [Int.repr (Int.unsigned _)] => rewrite Int.repr_unsigned; int_auto_simpl

    | H: context [Int.signed (Int.repr _)] |- _ => rewrite Int.signed_repr in H; [ int_auto_simpl | rewrite min_signed_val, max_signed_val; try omega ]
    | H: context [Int.unsigned (Int.repr _)] |- _ => rewrite Int.unsigned_repr in H; [ int_auto_simpl | rewrite max_unsigned_val; try omega ]
    | |- context [Int.signed (Int.repr _)] => rewrite Int.signed_repr; [ int_auto_simpl | rewrite min_signed_val, max_signed_val; try omega ]
    | |- context [Int.unsigned (Int.repr _)] => rewrite Int.unsigned_repr; [ int_auto_simpl | rewrite max_unsigned_val; try omega ]

    | H: context [Int.min_signed] |- _ => rewrite min_signed_val in H; int_auto_simpl
    | |- context [Int.min_signed] => rewrite min_signed_val; int_auto_simpl
    | H: context [Int.max_signed] |- _ => rewrite max_signed_val in H; int_auto_simpl
    | |- context [Int.max_signed] => rewrite max_signed_val; int_auto_simpl
    | H: context [Int.max_unsigned] |- _ => rewrite max_unsigned_val in H; int_auto_simpl
    | |- context [Int.max_unsigned] => rewrite max_unsigned_val; int_auto_simpl

    | H: context [Int.cmpu] |- _ => unfold Int.cmpu in H; int_auto_simpl
    | H: context [Int.eq] |- _ => unfold Int.eq in H; int_auto_simpl
    | H: context [Int.ltu] |- _ => unfold Int.ltu in H; int_auto_simpl
    | H: context [Int.add] |- _ => unfold Int.add in H; int_auto_simpl
    | H: context [Int.sub] |- _ => unfold Int.sub in H; int_auto_simpl
    | H: context [Int.mul] |- _ => unfold Int.mul in H; int_auto_simpl
    | H: context [Int.divu] |- _ => unfold Int.divu in H; int_auto_simpl
    | H: context [Int.divs] |- _ => unfold Int.divs in H; int_auto_simpl
    | H: context [Int.and] |- _ => unfold Int.and in H; int_auto_simpl
    | H: context [Int.or] |- _ => unfold Int.or in H; int_auto_simpl
    | H: context [Int.xor] |- _ => unfold Int.xor in H; int_auto_simpl
    | H: context [Int.shl] |- _ => unfold Int.shl in H; int_auto_simpl
    | H: context [Int.shr] |- _ => unfold Int.shr in H; int_auto_simpl
    | H: context [Int.lt] |- _ => unfold Int.lt in H; int_auto_simpl
    | H: context [Int.modu] |- _ => unfold Int.modu in H; int_auto_simpl
  
    | |- context [Int.cmpu] => unfold Int.cmpu; int_auto_simpl
    | |- context [Int.eq] => unfold Int.eq; int_auto_simpl
    | |- context [Int.ltu] => unfold Int.ltu; int_auto_simpl
    | |- context [Int.add] => unfold Int.add; int_auto_simpl
    | |- context [Int.sub] => unfold Int.sub; int_auto_simpl
    | |- context [Int.mul] => unfold Int.mul; int_auto_simpl
    | |- context [Int.divu] => unfold Int.divu; int_auto_simpl
    | |- context [Int.divs] => unfold Int.divs; int_auto_simpl
    | |- context [Int.and] => unfold Int.and; int_auto_simpl
    | |- context [Int.or] => unfold Int.or; int_auto_simpl
    | |- context [Int.xor] => unfold Int.xor; int_auto_simpl
    | |- context [Int.shl] => unfold Int.shl; int_auto_simpl
    | |- context [Int.shr] => unfold Int.shr; int_auto_simpl
    | |- context [Int.lt] => unfold Int.lt; int_auto_simpl
    | |- context [Int.modu] => unfold Int.modu; int_auto_simpl

    | _ => repeat progress autorewritearith
  end.

Ltac int_auto_H :=
  int_auto_simpl;
  match goal with    
    | H: context[Int.add] |- _ => rewrite Int.add_signed in H; int_auto_H
    | H: context[Int.sub] |- _ => rewrite Int.sub_signed in H; int_auto_H
    | H: context [Int.mul] |- _ => rewrite Int.mul_signed in H; int_auto_H
    | H: context [_ ÷ _] |- _ => rewrite zdiv_equiv in H; int_auto_H
    
   
    | H: context [zle ?z1 ?z2] |- _ => destruct (zle z1 z2); int_auto_H
    | H: context [zlt ?z1 ?z2] |- _ => destruct (zlt z1 z2); int_auto_H
    | H: context [zeq ?z1 ?z2] |- _ => destruct (zeq z1 z2); int_auto_H
    
    | _ => idtac
  end.

Ltac int_auto' :=
  match goal with
    | |- _ /\ _ => split; int_auto'
    | |- Int.repr _ = Int.repr _ => apply Int.eqm_samerepr; apply Int.eqm_refl2; int_auto'
    | |- Int.repr _ = _ => rewrite <- Int.repr_signed; apply Int.eqm_samerepr; apply Int.eqm_refl2; int_auto'
    | |- _ = Int.repr _ => rewrite <- Int.repr_signed; apply Int.eqm_samerepr; apply Int.eqm_refl2; int_auto'
 
    | |- context[Int.add] => rewrite Int.add_signed; int_auto'
    | |- context[Int.sub] => rewrite Int.sub_signed; int_auto'
    | |- context[Int.mul] => rewrite Int.mul_signed; int_auto'
    | |- context [_ ÷ _] => rewrite zdiv_equiv; int_auto'    
  
    | |- context [zle ?z1 ?z2] => destruct (zle z1 z2); int_auto'
    | |- context [zlt ?z1 ?z2] => destruct (zlt z1 z2); int_auto'
    | |- context [zeq ?z1 ?z2] => destruct (zeq z1 z2); int_auto'
    
    | _ => solve_int_unequal || simpleproof
  end.

Ltac int_auto :=
  intros;
  int_auto_H;
  int_auto'.

Ltac int_auto ::=
     intros;
     int_auto_simpl;
  [ try solve [ simpleproof ];
    match goal with
      | |- _ /\ _ => split; int_auto
      | |- Int.repr _ = Int.repr _ => apply Int.eqm_samerepr; apply Int.eqm_refl2; int_auto
      | |- Int.repr _ = _ => try solve [ rewrite <- Int.repr_signed; apply Int.eqm_samerepr; apply Int.eqm_refl2; int_auto
                                       | rewrite <- Int.repr_unsigned; apply Int.eqm_samerepr; apply Int.eqm_refl2; int_auto ]
      | |- _ = Int.repr _ => try solve [ rewrite <- Int.repr_signed; apply Int.eqm_samerepr; apply Int.eqm_refl2; int_auto
                                       | rewrite <- Int.repr_unsigned; apply Int.eqm_samerepr; apply Int.eqm_refl2; int_auto ]                                                                                                        
      | H: context [zle ?z1 ?z2] |- _ => destruct (zle z1 z2); int_auto
      | H: context [zlt ?z1 ?z2] |- _ => destruct (zlt z1 z2); int_auto
      | H: context [zeq ?z1 ?z2] |- _ => destruct (zeq z1 z2); int_auto
      | |- context [zle ?z1 ?z2] => destruct (zle z1 z2); int_auto
      | |- context [zlt ?z1 ?z2] => destruct (zlt z1 z2); int_auto
      | |- context [zeq ?z1 ?z2] => destruct (zeq z1 z2); int_auto
      | _ => solve_int_unequal
    end
  | idtac.. ].

Tactic Notation "int" "auto" := int_auto.



Goal
  forall z1 z2,
    0 < z1 < Int.max_signed ->
    0 < z2 < Int.max_signed ->
    z1 < z2 ->
    Int.sub (Int.add (Int.repr z1) (Int.sub (Int.repr z2) (Int.repr z1))) (Int.sub (Int.repr z2) (Int.repr z1)) = Int.repr z1.
Proof.
  int auto.
  int auto.
  int auto.
  int auto.
Qed.

Goal
  forall x y,
    Int.signed (Int.repr 1) < x < Int.signed (Int.repr 100) ->
    Int.signed (Int.repr 1) < y < Int.signed (Int.repr 100) ->
    Int.add (Int.repr x) (Int.repr y) = Int.repr (y + x).
Proof.
  int auto.
Qed.
  

Goal forall x y, 1 < x < Int.signed (Int.repr 100) -> 1 < y < 100 
           -> Int.min_signed <= x + y <= Int.max_signed.
Proof.
  int auto.
Qed.

Goal forall x y,  0 < y < x -> x <= 1073741823 -> 
                   Int.signed (Int.add (Int.repr x) (Int.repr y))  =  x + y.
 Proof.
   int auto.
   int auto.
 Qed.

Goal forall x, Int.ltu x (Int.repr 100) =true -> 
               Int.ltu (Int.add x (Int.repr 10))(Int.repr 120) = true.
Proof.
  int auto.
  int auto.
Qed.

Goal forall x,
       Int.signed x < 100 ->
       Int.min_signed <= Int.signed x + 10 <= Int.max_signed.
Proof.
  int auto.
Qed.

Goal
  forall i1 i2,
    Int.ltu (Int.repr 0) i1 = true ->
    Int.ltu i2 (Int.repr Int.max_signed) = true ->
    Int.ltu i1 i2 = true ->
    Int.unsigned (Int.sub i1 i2) < 1  .
Proof.
  int auto.
  int auto.
Abort.

Goal
  forall i1 i2,
    Int.ltu Int.zero i1 = true ->
    Int.ltu i1 i2 = true ->
    Int.sub (Int.add i1 (Int.sub i2 i1)) (Int.sub i2 i1) = i1.
Proof.
  int auto.
  int auto.
  int auto.
  int auto.
Qed.


Set Implicit Arguments.
Unset Strict Implicit.

Require Import Integers.
Require Import Coq.Setoids.Setoid.
Require Import ZArith.
Require Import Arith.
Require Import LibTactics.

Module _mathsolver.

Fixpoint _iter {T:Type} (f:T->T) (base : T) (n: nat) : T :=
  match n with 
      | O => base
      | S n' => _iter f (f base) n'
 end.
Module Type has_le.
  Parameter A: Type.
  Parameter le : A->A->Prop.

  Axiom le_refl : forall x:A, le x x.
  Axiom le_antisymm : forall a b:A, le a b -> le b a -> a=b.
  Axiom le_trans : forall a b c:A, le a b -> le b c -> le a c. 
End has_le.

Module Type has_next (LE: has_le).
  Import LE.
  Parameter next : A->A.
  Axiom next_is_smallest : forall (x n:A), le x n <-> n =  x \/ le (next x) n.
End has_next.

Module Type has_dist (Import LE: has_le) (Import HN:has_next LE).
  Parameter dist : A->A->nat.
  Axiom dist_a : forall a b,le a b-> _iter next a (dist a b) = b.
End has_dist.

Module Range (Import LE: has_le) (Import HN : has_next LE) (Import HD: has_dist LE HN).
  Definition range (b:A)(l:nat)(x:A) := le b x /\ le x (_iter next b l).

  Lemma x_le_next: forall x :A , le x (next x).
    intros.
    rewrite next_is_smallest.
    right.
    apply le_refl.
  Qed.

  Lemma x_le_iter_next : forall (x :A) (n:nat), le x (_iter next x n).
    intros.
    generalize x; clear x.
    induction n.
    simpl.
    apply le_refl.
    simpl.
    intros.
    eapply (@le_trans _  (next x)).
    apply x_le_next.
    apply IHn.
  Qed.

  Lemma range_l_r: forall (l r x:A) , le l r -> (le l x /\ le x r <-> range l (dist l r) x).
    intros.
    split;
    intro;
    unfold range in *;
    rewrite dist_a in *;auto.
  Qed.

  Lemma range_split_first' : forall (b:A) (l:nat) (x:A), x=b \/ range (next b) l x -> range b (S l) x.
    intros b l.
    generalize b; clear b.
    induction l.
    intros.
    elim H; intros.
    unfold range.
    simpl.
    rewrite H0.
    split.
    apply le_refl.
    
    apply x_le_next.

    unfold range.
    unfold range in H0.
    unfold _iter in H0.
    unfold _iter.
    elim H0; intros.
    set (@le_antisymm x (next b) H2 H1 ).
    rewrite e.
    split.
    apply x_le_next.
    apply le_refl.

    intros.

    elim H; intros.
    rewrite H0; split; intros.
    apply le_refl.
    simpl.

    eapply (@le_trans _  (next (next b))).
    eapply (@le_trans _ (next b)).
    apply (x_le_next).
    apply x_le_next.
    apply x_le_iter_next.

    unfold range in *.
    elim H0; intros.
    split.
    eapply le_trans.
    Focus 2.
    exact H1.
    apply x_le_next.
    simpl.
    simpl in H2.
    exact H2.
  Qed.

  Lemma range_split_first'' : forall (b:A) (l:nat) (x:A), range b (S l) x -> x=b \/ range (next b) l x.
    intros.
    set (next_is_smallest b x).
    elim i; intros o o'.
    unfold range in H.
    inversion H.
    set (o H0).
    elim o0; intros.
    left; auto.
    right; unfold range.
    split; auto.
  Qed.

  Lemma range_split_first : forall (b:A) (l:nat) (x:A), range b (S l) x <-> x=b \/ range (next b) l x.
    split.
    apply range_split_first''.
    apply range_split_first'.
  Qed.

  Lemma range_eq : forall (l x:A), range l O x <-> x=l.
    split;intros.
    unfold range in H.
    elim H; intros.
    apply le_antisymm; auto.
    unfold range; rewrite H; split;apply le_refl.
  Qed.

  (* good *)
  Fixpoint gen_prop (b:A) (len:nat) (x:A) {struct len} := 
    match len with
      | O => x=b
      | S n => x = b \/ gen_prop (next b) n x
    end.

  (* bad *)
  Fixpoint gen_prop' (b:A) (len:nat) (x:A) {struct len} :=
    match len with 
      | O => x=b
      | S n => gen_prop' b n x \/ x= _iter next b len
    end.

  Lemma range_fin_elem: forall b l x, range b l x <-> gen_prop b l x.
    intros b l.
    generalize b; clear b.
    induction l.
    intros; split; simpl;
    apply range_eq.

    intros; split; simpl; intros.
    apply range_split_first in H.
    elim H; intros.
    left; auto.
    right.
    apply IHl.
    auto.
    
    apply range_split_first.
    elim H; intros.
    left; auto.
    right; apply IHl.
    auto.
  Qed.
  Lemma range_l_r_fin_elem: forall (l r x:A) , le l r -> (le l x /\ le x r <-> gen_prop l (dist l r) x).
    intros.
    split.
    intro.
    rewrite range_l_r in H0.
    rewrite range_fin_elem in H0.
    auto.
    auto.
    intro.
    rewrite range_l_r; auto.
    rewrite range_fin_elem; auto.
  Qed.

  Lemma range_split_last'' : forall (b:A) (l:nat) (x:A), range b (S l) x -> range b l x \/ x= _iter next b (S l).
    intros b l.
    generalize b; clear b.
    induction l.
    intros.
    simpl.
    rewrite range_fin_elem in *.
    simpl in *.  
    auto.
    intros.

    apply range_split_first in H.
    elim H; intros.
    left; rewrite H0.
    unfold range.
    split; auto.
    apply le_refl.
    apply x_le_iter_next.
    apply IHl in H0.
    elim H0; intros.
    left.


    unfold range.
    unfold range in H1.
    elim H1; intros.
    split.
    eapply le_trans.
    Focus 2.
    exact H2.
    apply x_le_next.
    simpl.
    exact H3.

    right.
    auto.
  Qed.

  Lemma range_split_last' : forall (b:A) (l:nat) (x:A), range b l x \/ x = _iter next b (S l) -> range b (S l) x.
    intros b l.
    generalize b; clear b.
    induction l.
    intros.
    rewrite range_fin_elem in *.
    simpl in *.
    auto.

    intros.
    elim H; intros.
    unfold range in H0.
    unfold range.
    elim H0; intros; split; auto.
    eapply le_trans.
    exact H2.
    Lemma iter_n_lt_lt: forall n b, le (_iter next b n) (_iter next b (S n)).
      intro.
      induction n.
      intros.
      simpl.
      apply x_le_next.

      intros.
      assert (forall k, _iter next b (S k) = _iter next (next b) k).
      auto.
      rewrite H.
      rewrite H.
      apply IHn.
    Qed.
    apply iter_n_lt_lt.
    unfold range.
    split.
    rewrite H0.
    apply x_le_iter_next.
    rewrite H0.
    apply le_refl.
  Qed.

  Lemma range_split_last : forall (b:A) (l:nat) (x:A), range b l x \/ x = _iter next b (S l) <-> range b (S l) x.
    intros.
    split.
    apply range_split_last'.
    apply range_split_last''.
  Qed.

  Lemma range_fin_elem2' : forall b len x, range b len x -> gen_prop' b len x.
    intros b l.
    generalize b; clear b.
    induction l.
    intros.
    simpl in *.
    apply range_eq.
    auto.

    intros.
    simpl.
    rewrite <- range_split_last in H.
    elim H; intros.
    left.
    apply IHl.
    auto.
    right.
    simpl in H0; auto.
  Qed.

  Lemma range_fin_elem2'': forall b len x, gen_prop' b len x -> range b len x.
    intros b l.
    generalize b; clear b.
    induction l;intros.
    simpl in H; apply range_eq.
    auto.

    rewrite<- range_split_last. 
    simpl in H.
    elim H; intros.
    left; apply IHl; auto.
    right; simpl; auto.
  Qed.

  Lemma range_fin_elem2 : forall b len x, gen_prop' b len x <-> range b len x.
    intros.
    split.
    apply range_fin_elem2''.
    apply range_fin_elem2'.
  Qed.
End Range.

(* Z has le next and dist *)
Module Z_has_le <: has_le.
  Definition A := Z.
  Definition le := Zle.

  Definition le_refl:=Z.le_refl.
  Definition le_antisymm :=Z.le_antisymm.
  Definition le_trans := Z.le_trans.
End Z_has_le.

Module Z_has_next <: has_next Z_has_le.
  Definition next := fun x:Z => (1+ x)%Z.
  Lemma next_is_smallest: forall (x a:Z), Zle x a <-> a = x \/ Zle (next x) a.
    intros.
    split; intros.
    apply Z.le_lteq in H.
    elim H; intros.
    right.
    unfold next.
    omega.
    left ; auto.
    
    rewrite Z.le_lteq.
    elim H; intros.
    right; auto.
    left; unfold next in H0; omega.
  Qed.
End Z_has_next.

Module Z_has_dist <: has_dist Z_has_le Z_has_next.
  Import Z_has_le.
  Import Z_has_next.
  Definition dist := fun a b:Z => Z.to_nat (b-a).
    Lemma dist_a': forall n a, _iter next a n = (a+ Z.of_nat n)%Z.
       intro.
       induction n.
       intros.
       simpl.
       omega.
       
       intros.
       rewrite Nat2Z.inj_succ.
       simpl.
       rewrite IHn.
       unfold next.
       omega.
    Qed.

  Lemma dist_a : forall a b, le a b -> _iter next a (dist a b)  =b.
    intros a b.
    intro.
    assert (b = a + Z.of_nat (dist a b))%Z.
    unfold dist.
    rewrite Z2Nat.id.
    omega.
    unfold le in H; omega.
    rewrite H0 at 2.
    apply dist_a'.
  Qed.
End Z_has_dist.

(* nat has le next and dist *)

Module nat_has_le <: has_le.
  Definition A := nat.
  Definition le := le.

  Definition le_refl:=le_refl.
  Definition le_antisymm :=le_antisym.
  Definition le_trans := le_trans.
End nat_has_le.

Module nat_has_next <: has_next nat_has_le.
  Definition next := fun x => (S x).
  Lemma next_is_smallest: forall (x a:nat), le x a <-> a = x \/ le (next x) a.
    intros.
    split; intros.
    apply le_lt_or_eq_iff in H.
    elim H; intros.
    right.
    unfold next.
    omega.
    left ; auto.
    rewrite le_lt_or_eq_iff.
    elim H; intros.
    right; auto.
    left; unfold next in H0; omega.
  Qed.
End nat_has_next.

Module nat_has_dist <: has_dist nat_has_le nat_has_next.
  Import nat_has_le.
  Import nat_has_next.
  Definition dist := fun a b: nat => (b-a)%nat.
    Lemma dist_a': forall n a, _iter next a n = (a+n)%nat.
       intro.
       induction n.
       intros.
       simpl.
       omega.
       
       intros.
       simpl.
       rewrite IHn.
       unfold next.
       omega.
    Qed.

  Lemma dist_a : forall a b, le a b -> _iter next a (dist a b)  =b.
    intros a b.
    intro.
    assert (b = a + (dist a b))%nat.
    unfold dist.
    unfold le in H.
    omega.
    rewrite H0 at 2.
    apply dist_a'.
  Qed.
End nat_has_dist.

Module Z_range := Range Z_has_le Z_has_next Z_has_dist.

Module nat_range := Range nat_has_le nat_has_next nat_has_dist.

Ltac nat_range_unfold_all H:=try unfold nat_range.gen_prop in H;try unfold nat_has_next.next in H;try unfold nat_has_dist.dist in H;try unfold nat_has_le.A in H.

Ltac Z_range_unfold_all H:=try unfold Z_range.gen_prop in H;try unfold Z_has_next.next in H;try unfold Z_has_dist.dist in H;try unfold Z_has_le.A in H.

Ltac stdrange_fin_elem :=
  repeat progress
  match goal with 
      | H : ( _ <= ?a (?b _) <= _)%nat |- _ => apply nat_range.range_l_r_fin_elem in H;[cbv beta delta -[a b] iota in H| unfold nat_has_le.le; omega]
      | H : ( _ <= ?a _ _ <= _)%nat |- _ => apply nat_range.range_l_r_fin_elem in H;[cbv beta delta -[a] iota in H| unfold nat_has_le.le; omega]
      | H : ( _ <= ?a _ <= _)%nat |- _ => apply nat_range.range_l_r_fin_elem in H;[cbv beta delta -[a] iota in H| unfold nat_has_le.le; omega]
      | H : ( _ <= _ <= _)%nat |- _ => apply nat_range.range_l_r_fin_elem in H;[cbv beta delta iota in H| unfold nat_has_le.le; omega]
      | H : ( _ <= ?a (?b _) <= _)%Z |- _ => apply Z_range.range_l_r_fin_elem in H;[cbv beta delta -[a b] iota in H| unfold Z_has_le.le; omega]
      | H : ( _ <= ?a _ _ <= _)%Z |- _ => apply Z_range.range_l_r_fin_elem in H;[cbv beta delta -[a] iota in H| unfold Z_has_le.le; omega]
      | H : ( _ <= ?a _ <= _)%Z |- _ => apply Z_range.range_l_r_fin_elem in H;[cbv beta delta -[a] iota in H| unfold Z_has_le.le; omega]
      | H : ( _ <= _ <= _ )%Z   |- _ => apply Z_range.range_l_r_fin_elem  in H;[cbv beta delta iota in H| unfold Z_has_le.le; omega]
      | _ => fail
  end.

(* range split part end *)

Open Scope nat_scope.
  Lemma nat_lt2stdrange : forall x b:nat, x<b -> 0<=x<=(pred b).
    intros;set (le_0_n x); split; auto.
    omega.
  Qed.

  Lemma nat_le2stdrange : forall x b:nat,  x<=b -> 0<=x<=b.
    intros; set (le_0_n x);split; auto.
  Qed.

  Lemma nat_gt2stdrange : forall x b:nat, b>x -> 0<=x<=(pred b).
    intros; set (le_0_n x); split; auto.
    omega.
  Qed.
  Lemma nat_ge2stdrange: forall x b, b>=x -> 0<=x<=b.
    intros; set (le_0_n x); split; auto.
  Qed.
Close Scope nat_scope.

(*******************************)

Open Scope Z_scope.
  Lemma unsigned_lt2stdrange : forall x b, Int.unsigned x< b -> 0<=Int.unsigned x <= (Z.pred b).
    intros;split;[set (Int.unsigned_range x); tauto| omega].
  Qed.
  
  Lemma unsigned_le2stdrange : forall x b, Int.unsigned x<=b -> 0<=Int.unsigned x<=b.
    intros;split;[set (Int.unsigned_range x); tauto| omega].
  Qed.

  Lemma unsigned_gt2stdrange : forall x b,  b > Int.unsigned x -> 0<=Int.unsigned x <= (Z.pred b).
    intros;split;[set (Int.unsigned_range x); tauto| omega].
  Qed.
  
  Lemma unsigned_ge2stdrange : forall x b, b >= Int.unsigned x -> 0<=Int.unsigned x<=b.
    intros;split;[set (Int.unsigned_range x); tauto| omega].
  Qed.

  Lemma repr_unsigned : forall x n, Int.unsigned x = n -> x= Int.repr n.
    intros.
    rewrite <- H.
    rewrite Int.repr_unsigned.
    reflexivity.
  Qed.

  (* TODO: change this function *)
  Ltac pre' :=
    match goal with 
       | H : (?x <  ?b)%nat |- _                => apply nat_lt2stdrange in H
       | H : (?x <= ?b)%nat |- _                => apply nat_le2stdrange in H
       | H : (?b >  ?x)%nat |- _                => apply nat_gt2stdrange in H
       | H : (?b >= ?x)%nat |- _                => apply nat_ge2stdrange in H
       | H : (Int.unsigned ?x <  ?b)     |- _   => apply unsigned_lt2stdrange in H
       | H : (Int.unsigned ?x <= ?b)     |- _   => apply unsigned_le2stdrange in H
       | H : (?b >  Int.unsigned ?x )    |- _   => apply unsigned_gt2stdrange in H
       | H : (?b >= Int.unsigned ?x)     |- _   => apply unsigned_ge2stdrange in H
       | H : (?a < ?x < ?b)%nat |- _            => let H' := fresh in rename H into H'; assert ( (S a) <= x <= (pred b))%nat as H by omega; clear H'
       | H : (?a <= ?x < ?b)%nat |- _           => let H' := fresh in rename H into H'; assert ( (a) <= x <= (pred b))%nat as H by omega; clear H'
       | H : (?a < ?x <= ?b)%nat |- _           => let H' := fresh in rename H into H'; assert ( (S a) <= x <= ( b))%nat as H by omega; clear H'
       | H : (?a < ?x < ?b) |- _                => let H' := fresh in rename H into H'; assert ( (1+ a) <= x <= (Z.pred b)) as H by omega; clear H'
       | H : (?a <= ?x < ?b) |- _               => let H' := fresh in rename H into H'; assert ( (a) <= x <= (Z.pred b)) as H by omega; clear H'
       | H : (?a < ?x <= ?b) |- _               => let H' := fresh in rename H into H'; assert ( (1+ a) <= x <= ( b)) as H by omega; clear H'
    end.
  
  Ltac pre := repeat pre';repeat ((* handle even not a real range, 1<=x<=0 for example*)try omega; timeout 8 stdrange_fin_elem).
  Ltac pre_noto := repeat pre';repeat ((* handle even not a real range, 1<=x<=0 for example*)try omega; stdrange_fin_elem).


  (* do NOT use this *)
  (* use a tactic as a param in another tactic is VERY slow*)
  Ltac brute_force tac:=
    match goal with 
        | H : _ \/ _ |- _ => destruct H; brute_force tac
        | _               => tac
    end.

  Lemma sample'' : forall n , (0< n<63)%nat ->True.
    intros.
    pre.
    auto.
  Qed.

  Lemma sample0: forall n m :int32,  Int.unsigned m < 64 -> 64 > Int.unsigned n ->  True.
    intros.
    pre.
    auto.
  Qed.

  Lemma sample1: forall n:nat, (n<25)%nat-> True.
    intros.
    pre.
    auto.
  Qed.

  Lemma sample2: forall n:nat, (25>n)%nat-> True.
    intros.
    pre.
    auto.
  Qed.

  Ltac math_solver_pre :=
    match goal with 
        | H : Int.unsigned _ = _ |- _ => apply repr_unsigned in H
        | _  => idtac
    end.

  (* can use compute -[Int.unsigned Int.mone] instead *)
  Ltac munfold :=try unfold Int.shru; try unfold Int.shl; try unfold Int.not; try unfold Z.shiftr; try unfold Int.xor; try unfold Int.and; try unfold Z.to_nat; try unfold Pos.to_nat; try unfold Int.or; try unfold Z.lor; try unfold Int.divu; try unfold Int.add; try unfold Int.mul; try unfold Int.sub; try unfold Int.ltu; try unfold Int.zero; try unfold Int.one; try unfold Int.eq.

  Ltac mycompute := compute -[Int.unsigned].


(*
Lemma div_in_intrange: forall x a mx:Z, (0<=x <=mx -> a>0 -> 0<= Z.div x a <=mx)%Z.
  intros.
  split.
  ht.revs.
  apply Z_div_ge0.
  omega.
  omega.
  apply Z.div_le_upper_bound.
  omega.
  elim H; intros.
  eapply Zle_trans.
  exact H2.
  ht.revs.
  apply a_mult_b_ge_b; omega.
Qed.
  Ltac solve_int_range := 
match goal with 
    | i : int32 |- _ => let xval := fresh in let xrange := fresh in destruct i as [xval xrange]; unfold Int.modulus, two_power_nat, shift_nat in xrange; simpl in xrange; simpl in *;  solve_int_range
    | _ => subst; try rewrite max_unsigned_val; solve [ omega | apply div_in_intrange; omega ]
end.
  Ltac rangesolver :=try solve_int_range; repeat (rewrite Int.unsigned_repr; try solve_int_range).
  Ltac ur_rewriter := rewrite Int.unsigned_repr; [idtac| rangesolver].
  Ltac ur_rewriter_in H := rewrite Int.unsigned_repr in H; [idtac| rangesolver].
 *)
  Ltac trivial_ur_rewriter := rewrite Int.unsigned_repr;[idtac| rewrite max_unsigned_val; omega].

  Ltac subst_all := subst.



(* not so basic *)
  Ltac basic_solver := match goal with 
| H : Int.unsigned ?a = ?b |- _  => rewrite H in *; apply repr_unsigned in H; basic_solver
| _  => subst_all; simpl; repeat trivial_ur_rewriter; simpl; solve [auto| omega |  timeout 2 mycompute; intros; try split; tryfalse; try omega; auto]
end.
  Ltac basic_solver_noto := match goal with 
| H : Int.unsigned ?a = ?b |- _  => rewrite H in *; apply repr_unsigned in H; basic_solver
| _  => subst_all; simpl; repeat trivial_ur_rewriter; simpl; solve [auto| omega |  mycompute; intros; try split; tryfalse; try omega; auto]
end.
  

  Ltac bf_basic_solver :=
    repeat progress
           match goal with
             | H : _ \/ _ |- _  => destruct H;
                                  [match goal with
                                     |  H' : _\/_ |- _ => destruct H';
                                                         [match goal with
                                                            |  H'' : _\/_ |- _ => destruct H''; [basic_solver | idtac]
                                                            |  _ => basic_solver
                                                          end | idtac ]
                                     |  _ => basic_solver
                                   end | idtac ]
             | _ => basic_solver
           end.

  Ltac bf_basic_solver_noto :=
    repeat progress
           match goal with
             | H : _ \/ _ |- _  => destruct H;
                                  [match goal with
                                     |  H' : _\/_ |- _ => destruct H';
                                                         [match goal with
                                                            |  H'' : _\/_ |- _ => destruct H''; [basic_solver_noto | idtac]
                                                            |  _ => basic_solver_noto
                                                          end | idtac ]
                                     |  _ => basic_solver_noto
                                   end | idtac ]
             | _ => basic_solver_noto
           end.


  Ltac basic_solver_safe := match goal with 
| H : Int.unsigned ?a = ?b |- _  => rewrite H; apply repr_unsigned in H; basic_solver_safe
| _  => subst_all; simpl;  split; try omega
end.

Ltac bf1_basic_solver :=
   match goal with
     | H : _ \/ _ |- _  => solve[clear -H; repeat (destruct H as [H | H] ;[basic_solver_safe| idtac] ) ; basic_solver_safe]
   end.

Ltac clear_useless_or :=
  match goal with
      | H : _ ?a = _ \/ _ |- _ => clear dependent a
      | H : ?a = _ \/ _   |- _ => clear dependent a
end.

Ltac clear_all_useless_or := repeat clear_useless_or.

Ltac mrewrite := repeat rewrite unsigned_mone_val; repeat rewrite Int.unsigned_repr; try rewrite max_unsigned_val; [idtac|solve [clear; omega |  clear_all_useless_or;  bf_basic_solver] .. ].
Ltac mrewrite_noto := repeat rewrite unsigned_mone_val; repeat rewrite Int.unsigned_repr; try rewrite max_unsigned_val; [idtac|solve [clear; omega |  clear_all_useless_or;  bf_basic_solver_noto] .. ].

  Ltac new_mathsolver:= munfold; pre; mrewrite; bf_basic_solver.
  Ltac new_mathsolver_noto := munfold; pre_noto; mrewrite_noto; bf_basic_solver_noto.
  (* old version *)
  Ltac math_rewrite :=
    repeat progress (
             try rewrite Int.unsigned_repr in *;
             try rewrite max_unsigned_val in *;
             try omega ;
             try rewrite unsigned_mone_val in *;
             try omega; auto).


  Ltac math_solver:=
    math_solver_pre;
    subst;
    try simpl in *;
    try unfold Int.shru in *;
    try unfold Int.shl in *;
    try unfold Int.not in *;
    try unfold Z.shiftr in *;
    try unfold Int.xor in *;
    try unfold Int.and in *;
    try unfold Z.to_nat in *;
    try unfold Pos.to_nat in *;
    try unfold Int.or in *;
    try unfold Z.lor in *;
    try unfold Int.divu in *;
    try unfold Int.add in *;
    try unfold Int.mul in *;
    try unfold Int.sub in *;
    try unfold Int.ltu in *;
    try unfold Int.zero in *;
    try unfold Int.one in *;
    try unfold Int.eq in *;
    match goal with
      | H : ?f  _  =  _ |- _ => simpl f in H;  inverts H
      | _ => idtac
    end;
    math_rewrite;
    try simpl in *;
    math_rewrite;
    intuition tryfalse;
    try (simpl; omega).

  Ltac mathsolver' :=
    repeat progress
           match goal with
             | H : False |- _ => inversion H
             | H : _ \/ _ |- _  => destruct H;
                                  [match goal with
                                     |  H' : _\/_ |- _ => destruct H';
                                                         [match goal with
                                                            |  H'' : _\/_ |- _ => destruct H''; [math_solver | idtac]
                                                            |  _ => math_solver
                                                          end | idtac ]
                                     |  _ => math_solver
                                   end | idtac ]
             | _ => math_solver
           end.
  
  Ltac mathsolver:= pre; mathsolver'.

End _mathsolver.
(*
Require Import memory. (* for Vint32 *)
Require Import OSTCBInvDef. (* for OSUnMapVallist *)
Require Import BaseAsrtDef. (* for nth_val' *)

Module _mathsolver_ext.
  Close Scope nat_scope.
  Open Scope Z_scope.
  Definition deref_Vint32_unsafe (x:val): int32 :=
    match x with
        | Vint32 x => x
        | _ => (Int.repr 0)
    end.

  Lemma OSUnMapVallist_safe_deVint32 : forall z y, 0<=z<=255 -> nth_val' (Z.to_nat z) OSUnMapVallist = Vint32 y -> y = deref_Vint32_unsafe ( nth_val' (Z.to_nat z) OSUnMapVallist).
Proof.
  intros.
  _mathsolver.pre.
  repeat (destruct H; [rewrite H in *; simpl in H0; inversion H0; auto| idtac]).
  rewrite H in *; simpl in H0; inversion H0; auto.
Qed.
 
  Lemma OSMapVallist_safe_deVint32 : forall z y, 0<=z<=7 -> nth_val' (Z.to_nat z) OSMapVallist = Vint32 y -> y = deref_Vint32_unsafe ( nth_val' (Z.to_nat z) OSMapVallist).
    intros.
    _mathsolver.pre.
    repeat (destruct H; [rewrite H in *; simpl in H0; inversion H0; auto| idtac]).
    rewrite H in *; simpl in H0; inversion H0; auto.
  Qed.
  
  Ltac deref_vint32_for_array := match goal with 
                                 | H : nth_val' (Z.to_nat (Int.unsigned ?a) ) OSUnMapVallist = Vint32 _ |- _=> apply OSUnMapVallist_safe_deVint32 in H;[unfold deref_Vint32_unsafe in H; try rewrite H in *; clear H |set (@Int.unsigned_range_2 a); try omega]
                                 | H : nth_val' (Z.to_nat (Int.unsigned ?a) ) OSMapVallist = Vint32 _ |- _ => apply OSMapVallist_safe_deVint32 in H; [unfold deref_Vint32_unsafe in H; try rewrite H in *; clear H | set (@Int.unsigned_range_2 a);  try omega]
                                 | H : nth_val' (Z.to_nat _ ) OSUnMapVallist = Vint32 _ |- _=> apply OSUnMapVallist_safe_deVint32 in H;[unfold deref_Vint32_unsafe in H; try rewrite H in *; clear H | try omega]
                                 | H : nth_val' (Z.to_nat _ ) OSMapVallist = Vint32 _ |- _ => apply OSMapVallist_safe_deVint32 in H; [unfold deref_Vint32_unsafe in H; try rewrite H in *; clear H | try omega]
                                 end.
End _mathsolver_ext.
*)

Ltac mauto := (*repeat _mathsolver_ext.deref_vint32_for_array; *)_mathsolver.new_mathsolver.
Ltac mauto_noto := (*repeat _mathsolver_ext.deref_vint32_for_array;*) _mathsolver.new_mathsolver_noto.
Ltac mauto_old := _mathsolver.mathsolver.
Ltac mauto_dbg := _mathsolver.pre.
*)
