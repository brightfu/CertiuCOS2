(***************************************************************)
(* Coq code for OCAP                                           *)
(*                                                             *)
(* Utilities for manipulating natural numbers                  *)
(*                                                             *)
(*                                                             *)
(***************************************************************)

(* $Id: IntBool.v 21 2012-08-16 14:14:35Z guoyu $ *)

Require Import ZArith.
Require Export Bool.

(* *********************************************************** *)

Definition int := Z.

Open Scope Z_scope.

Theorem int_eq_dec : forall a b : int, {a = b} + {a <> b}.
Proof.
  apply Z_eq_dec.
Qed.

(* *********************************************************** *)

Fixpoint blt_pos (p q : positive) {struct p} : bool :=
  match (Pcompare p q Eq) with
    | Lt => true 
    | _  => false
  end.

Fixpoint blt_int (n m : int) {struct n} : bool :=
  match n, m with
    | Z0, Zpos p => true
    | Zneg p, Z0 => true
    | Zneg p, Zpos q => true
    | Zneg p, Zneg q => blt_pos q p
    | Zpos p, Zpos q => blt_pos p q
    | _, _ => false
  end.

Lemma blt_pos_irrefl : 
  forall p : positive, blt_pos p p = false.
Proof.
  induction p; simpl; auto with arith.
  rewrite Pcompare_refl; trivial.
  rewrite Pcompare_refl; trivial.
Qed.

Lemma blt_irrefl :
  forall a : int, blt_int a a = false.
Proof.
  destruct a; simpl; auto with arith.
  apply blt_pos_irrefl; trivial.
  apply blt_pos_irrefl; trivial.
Qed.

Lemma blt_irrefl_Prop :
  forall a : int, ~ (blt_int a a = true).
Proof.
  induction a; simpl; auto with arith.
  intro H. rewrite blt_pos_irrefl in H.
  discriminate.
  intro H; rewrite blt_pos_irrefl in H; discriminate.
Qed.

(* *********************************************************** *)

Fixpoint beq_pos (p p' : positive) {struct p} : bool :=
  match p, p' with
    | x~0, x'~0 => andb true (beq_pos x x')
    | p~1, p'~1 => andb true (beq_pos p p')
    | 1, 1 => true 
    | _, _ => false
  end %positive.

Fixpoint beq_int (z z' : int) {struct z} : bool :=
  match z, z' with
    | Z0, Z0 => true
    | Zpos p, Zpos p' => beq_pos p p'
    | Zneg p, Zneg p' => beq_pos p p'
    | _, _ => false
  end.

Lemma beq_int_true_eq : forall z z' : int, 
  beq_int z z' = true -> z = z'.
Proof.
  intros.
  induction z;destruct z';try inversion H;trivial.
  clear -H1.
  generalize dependent p0.
  induction p.
  intros.
  destruct p0.
  simpl in H1.
  apply IHp in H1.
  rewrite Zpos_xI.
  rewrite Zpos_xI.
  rewrite H1.
  trivial.
  inversion H1.
  inversion H1.
  intros.
  destruct p0.
  inversion H1.
  simpl in H1.
  apply IHp in H1.
  rewrite Zpos_xO.
  symmetry.
  rewrite Zpos_xO.
  rewrite H1.
  trivial.
  inversion H1.
  intros.
  destruct p0;try inversion H1;trivial.
  generalize dependent p0.
  induction p.
  intros.
  destruct p0.
  simpl in H1.
  apply IHp in H1.
  rewrite Zneg_xI.
  rewrite Zneg_xI.
  rewrite H1;trivial.
  simpl in H.
  simpl.
  assumption.
  inversion H1.
  inversion H1.
  intros.
  destruct p0.
  inversion H1.
  simpl in H1.
  apply IHp in H1.
  rewrite Zneg_xO.
  rewrite Zneg_xO.
  rewrite H1.
  trivial.
  simpl in H.
  simpl.
  assumption.
  inversion H1.
  intros.
  destruct p0;inversion H1;trivial.
Qed.

Lemma beq_int_false_neq : forall z z' : int,
  beq_int z z' = false -> z <> z'.
Proof.
  intros z z' Hbeq Hz.
  subst z'.
  induction z;try inversion Hbeq;induction p;try apply IHp;try assumption;try inversion Hbeq.
Qed.

Lemma eq_beq_int_true : forall z z' : int, 
  z = z' -> beq_int z z' = true.
Proof.
  intros.
  subst z'.
  induction z;trivial;induction p;try assumption;trivial.
Qed.

Lemma neq_beq_int_false : forall z z' : int, 
  z <> z' -> beq_int z z' = false.
Proof.
  intros.
  induction z.
  destruct z'.
  case H.
  trivial.
  trivial.
  trivial.
  destruct z'.
  trivial.
  simpl.
  generalize dependent p0.
  induction p.
  intros.
  destruct p0.
  simpl.
  apply IHp.
  rewrite Zpos_xI in H.
  rewrite Zpos_xI in H.
  intro.
  rewrite H0 in H.
  case H;trivial.
  trivial.
  trivial.
  intros.
  destruct p0.
  trivial.
  trivial.
  apply IHp.
  intro.
  apply H.
  rewrite Zpos_xO.
  symmetry.
  rewrite Zpos_xO.
  rewrite H0.
  trivial.
  trivial.
  intros.
  destruct p0;trivial;try case H;trivial.
  trivial.
  destruct z'.
  trivial.
  trivial.
  simpl.
  generalize dependent p0.
  induction p.
  intros.
  destruct p0.
  simpl.
  apply IHp.
  intro.
  rewrite Zneg_xI in H.
  rewrite Zneg_xI in H.
  rewrite H0 in H.
  case H;trivial.
  trivial.
  trivial.
  intros.
  destruct p0.
  trivial.
  simpl.
  apply IHp.
  intro.
  rewrite Zneg_xO in H.
  rewrite Zneg_xO in H.
  rewrite H0 in H.
  case H;trivial.
  trivial.
  intros.
  destruct p0;trivial;try case H;trivial.
Qed.

Lemma beq_int_dec : forall a b,
  {beq_int a b = true} + {beq_int a b = false}.
Proof.
  intros; destruct (beq_int a b); [left |  right];  trivial.
Qed.

(* *********************************************************** *)

(* *********************************************************** *)

(* *********************************************************** *)

(* for beq int *)

Ltac beq_case_tac x y :=
  let Hb := fresh "Hb" in
    (destruct (beq_int_dec x y) as [Hb | Hb]; trivial).

Tactic Notation "bint" "case" constr(i) constr (i') := beq_case_tac i i'.
(*
Ltac simpl_int_tac := 
  match goal with

    (* beq rewrite directly *)
    | [H : beq_int ?x ?y = ?f 
      |- context [(beq_int ?x ?y)]] =>
       rewrite H; simpl_int_tac
    | [H : beq_int ?x ?y = ?f,
       H0 : context [(beq_int ?x ?y)] |- _ ] =>
       rewrite H in H0; simpl_int_tac

    (* beq_refl *)
    | [ |- context [(beq_int ?x ?x)] ] =>
      rewrite (beq_int_refl x); simpl_int_tac
    | [H : context [(beq_int ?x ?x)] |- _ ] => 
      rewrite (beq_int_refl x) in H; simpl_int_tac

    (* beq_sym *)
    | [ H : beq_int ?x ?y = ?b 
        |- context [(beq_int ?y ?x)] ] =>
      rewrite (beq_int_sym x y b H); simpl_int_tac
    | [H : beq_int ?x ?y = ?b,
       H0 : context [(beq_int ?y ?x)] |- _ ] => 
      rewrite (beq_int_sym x y b H) in H0; simpl_int_tac

    (* (* neq -> beq *) *)
    (* | [ H : ?x <> ?y |- context [(beq_int ?x ?y)] ] =>  *)
    (*   rewrite (neq_beq_int_false x y H); simpl_int_tac *)
    (* | [ H : ?x <> ?y,  *)
    (*     H0 : context [(beq_int ?x ?y)] |- _ ] =>  *)
    (*   rewrite (neq_beq_false x y H) in H0; simplbnat *)

    (* | [ H : ?y <> ?x |- context [(beq_int ?x ?y)] ] =>  *)
    (*   rewrite (neq_beq_false x y (sym_not_eq H)); simplbnat *)
    (* | [ H : ?y <> ?x,  *)
    (*     H0 : context [(beq_int ?x ?y)] |- _ ] =>  *)
    (*   rewrite (neq_beq_false x y (sym_not_eq H)) in H0; simplbnat *)
        
    | [H : ?x = ?x |- _ ] => clear H; simpl_int_tac
    | [H : true = false |- _ ] => discriminate H
    | [H : false = true |- _ ] => discriminate H
    | _ => idtac
  end.

Tactic Notation "bint" "simpl" := simpl_int_tac.

Ltac rew_beq_tac H :=
  match type of H with
    | beq_int ?a ?b = true => 
      match goal with 
        | [ |- context [(?a)]] => 
          rewrite (beq_int_true_eq a b H)
        | [ |- context [(?b)]] => 
          rewrite <- (beq_int_true_eq a b H)
      end
    | _ => fail
  end.

Tactic Notation "bint" "rewrite" constr(t) := rew_beq_tac t.

Ltac rewH_beq_tac H H' :=
  match type of H with
    | beq_int ?a ?b = true => 
      match goal with 
        | [ H' : context [(?a)] |- _ ] => 
          rewrite (beq_int_true_eq a b H) in H'
        | [ H' : context [(?b)] |- _ ] => 
          rewrite <- (beq_int_true_eq a b H) in H'
      end
    | _ => fail
  end.

Tactic Notation "bint" "rewrite" constr(t) "in" hyp(H) := rewH_beq_tac t H.

*)
