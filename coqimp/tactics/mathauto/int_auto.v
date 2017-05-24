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
