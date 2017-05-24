(* ************************************************************************ *)
(*                                                                          *)
(*  Verifying Thread Management                                             *)
(*                                                                          *)
(*      Author:  Yu Guo (guoyu@mail.ustc.edu.cn)                            *)
(*                                                                          *)
(* ************************************************************************ *)

(* $Id: MapLib.v 192 2014-01-30 02:19:36Z guoyu $ *)

Require Import extac.
Require Import IntBool.
Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.

Module Type MAP_DOMAIN.

  Parameter A : Set.

  Axiom beq : A -> A -> bool.

  Axiom blt : A -> A -> bool.

  Axiom beq_true_eq : forall a a' : A, 
    beq a a' = true -> a = a'.
 
  Axiom beq_false_neq : forall a a' : A,
    beq a a' = false -> a <> a'.
  
  Axiom eq_beq_true : forall a a' : A, 
    a = a' -> beq a a' = true.

  Axiom neq_beq_false : forall a a' : A, 
    a <> a' -> beq a a' = false.

  Axiom blt_trans : forall a a' a'' : A,
    blt a a' = true -> blt a' a'' = true -> blt a a'' = true.

  Axiom blt_irrefl : forall a : A,
    blt a a = false.

  Axiom blt_asym :  forall a b : A, 
    blt a b = true -> blt b a = false.

  Axiom blt_beq_dec : forall a b : A,
    {blt a b = true} + {beq a b = true} + {blt b a = true}.

End MAP_DOMAIN.

Module Type MAP_RANGE.

  Parameter B : Type.

  Parameter holder : B. (** used to define del **)
End MAP_RANGE.

Module MapFun (Domain : MAP_DOMAIN) (Range : MAP_RANGE).

Import Domain.

Import Range.

(*   Parameter A : Set. *)

(* Definition A := int. *)

(* Definition beq : A -> A -> bool := beq_int. *)

(* Lemma beq_true_eq : forall a a' : A,  *)
(*   beq a a' = true -> a = a'. *)
(* Proof beq_int_true_eq. *)
 
(* Lemma beq_false_neq : forall a a' : A, *)
(*   beq a a' = false -> a <> a'. *)
(* Proof beq_int_false_neq. *)
  
(* Lemma eq_beq_true : forall a a' : A,  *)
(*   a = a' -> beq a a' = true. *)
(* Proof eq_beq_int_true. *)

(* Lemma neq_beq_false : forall a a' : A,  *)
(*   a <> a' -> beq a a' = false. *)
(* Proof neq_beq_int_false. *)

Lemma beq_dec : forall a a' : A, {beq a a' = true} + {beq a a' = false}.
Proof.
  intros; destruct (beq a a'); [left | right]; trivial.
Qed.

Lemma eq_dec : forall a a' : A, {a = a'} + {a <> a'}.
Proof.
  intros; destruct (beq_dec a a'); [left | right]. 
  apply beq_true_eq; trivial.
  apply beq_false_neq; trivial.
Qed.

Ltac beq_case_tac x y :=
  let Hb := fresh "Hb" in
    (destruct (beq_dec x y) as [Hb | Hb]; trivial).

Lemma beq_sym : forall a a' b, 
  beq a a' = b -> beq a' a = b.
Proof.
  intros m n b H.
  destruct b.  
    apply eq_beq_true.
    apply sym_eq.
    apply beq_true_eq; trivial.
  apply neq_beq_false.
  apply sym_not_eq.
  apply beq_false_neq; trivial.
Qed.

Lemma beq_refl : forall a, beq a a = true.
Proof.
  intro m.
  apply eq_beq_true; trivial.
Qed.

Lemma beq_trans : forall a a' a'' b, beq a a' = true
  -> beq a' a'' = b
  -> beq a a'' = b.
Proof.
  intros m n k b H1 H2.
  assert (m = n).
    apply beq_true_eq; trivial.
  subst m.
  destruct b.
    apply eq_beq_true.
    apply beq_true_eq; trivial.
  apply neq_beq_false.
  apply beq_false_neq; trivial.
Qed.

Ltac beq_simpl_tac := 
  match goal with

    (* beq rewrite directly *)
    | [H : beq ?x ?y = ?f 
      |- context [(beq ?x ?y)]] =>
       rewrite H; beq_simpl_tac
    | [H : beq ?x ?y = ?f,
       H0 : context [(beq ?x ?y)] |- _ ] =>
       rewrite H in H0; beq_simpl_tac

    (* beq_refl *)
    | [ |- context [(beq ?x ?x)] ] =>
      rewrite (@beq_refl x); beq_simpl_tac
    | [H : context [(beq ?x ?x)] |- _ ] => 
      rewrite (@beq_refl x) in H; beq_simpl_tac

    (* beq_sym *)
    | [ H : beq ?x ?y = ?b 
        |- context [(beq ?y ?x)] ] =>
      rewrite (@beq_sym x y b H); beq_simpl_tac
    | [H : beq ?x ?y = ?b,
       H0 : context [(beq ?y ?x)] |- _ ] => 
      rewrite (@beq_sym x y b H) in H0; beq_simpl_tac

    (* neq -> beq *)
    | [ H : ?x <> ?y |- context [(beq ?x ?y)] ] =>
      rewrite (neq_beq_false H); beq_simpl_tac
    | [ H : ?x <> ?y,
        H0 : context [(beq ?x ?y)] |- _ ] =>
      rewrite (neq_beq_false H) in H0; beq_simpl_tac
    | [ H : ?x <> ?y |- context [(beq ?y ?x)] ] =>
      rewrite (beq_sym (neq_beq_false H)); beq_simpl_tac
    | [ H : ?x <> ?y,
        H0 : context [(beq ?y ?x)] |- _ ] =>
      rewrite (beq_sym (neq_beq_false H)) in H0; beq_simpl_tac

    (* beq -> neq *)
    | [ H : (beq ?x ?y = false) |- ?x <> ?y ] =>
      apply (beq_false_neq H); beq_simpl_tac
    | [ H : (beq ?x ?y = false) |- ?y <> ?x ] =>
      apply (beq_false_neq (beq_sym H)); beq_simpl_tac

    (* | [ H : ?y <> ?x |- context [(beq_int ?x ?y)] ] =>  *)
    (*   rewrite (neq_beq_false x y (sym_not_eq H)); simplbnat *)
    (* | [ H : ?y <> ?x,  *)
    (*     H0 : context [(beq_int ?x ?y)] |- _ ] =>  *)
    (*   rewrite (neq_beq_false x y (sym_not_eq H)) in H0; simplbnat *)
        
    | [H : ?x = ?x |- _ ] => clear H; beq_simpl_tac
    | [H : true = false |- _ ] => discriminate H
    | [H : false = true |- _ ] => discriminate H

    | [|- true = true ] => trivial
    | [|- false = false ] => trivial

    | [|- context [beq ?x ?y] ] => simpl; trivial
    | [ H: context [beq ?x ?y] |- _ ] => simpl in H

    | _ => idtac
  end.

(* Section Test. *)
(*   Variables a b : A. *)
(*   Goal beq a b = false -> b <> a. *)
(*     intro H. *)
(*     beq_simpl_tac. *)
(*   Abort. *)
(* End Test. *)

Tactic Notation "beq" "simpl" := beq_simpl_tac.

Ltac beq_rewrite_tac H :=
  match type of H with
    | beq ?a ?b = true => 
      match goal with 
        | [ |- context [(?a)]] => 
          rewrite (@beq_true_eq a b H)
        | [ |- context [(?b)]] => 
          rewrite <- (@beq_true_eq a b H)
      end
    | _ => fail
  end.

Tactic Notation "beq" "rewrite" constr(t) := beq_rewrite_tac t.

Ltac beq_rewriteH_tac H H' :=
  match type of H with
    | beq ?a ?b = true => 
      match type of H' with 
        | context [(?a)] => 
          rewrite (@beq_true_eq a b H) in H'
        | context [(?b)] => 
          rewrite <- (@beq_true_eq a b H) in H'
      end
    | _ => fail
  end.

Tactic Notation "beq" "rewrite" constr(t) "in" hyp(H) := beq_rewriteH_tac t H.

Section Test.
  Variables a b a' : A.
  Goal beq a b = true -> beq a a' = true -> False.
    intros.
    beq_rewriteH_tac H0 H.
  Abort.
End Test.

Lemma blt_dec : forall a b,
  {blt a b = true} + {blt a b = false}.
Proof.
  intros a b.
  destruct (blt a b); [left | right]; trivial.
Qed.

(* *********************************************************** *)

Lemma blt_t_beq_f : 
  forall m n, blt m n = true 
    -> beq m n = false.
Proof.
  intros m n H.
  beq_case_tac m n.
  rewrite (beq_true_eq Hb) in H.
  rewrite (blt_irrefl) in H.
  discriminate.
Qed.

Lemma bgt_t_beq_f :
  forall m n, blt n m = true
    -> beq m n = false.
Proof.
  intros m n H.
  apply beq_sym.
  apply blt_t_beq_f.
  trivial.
Qed.

Lemma beq_t_blt_f : 
  forall m n, beq m n = true
    -> blt m n = false. 
Proof.
  intros m n H.
  rewrite (beq_true_eq H).
  apply blt_irrefl.
Qed.

Lemma beq_t_bgt_f :
  forall m n, beq m n = true
    -> blt n m = false.
Proof.
  intros m n H.
  rewrite (beq_true_eq H).
  apply blt_irrefl.
Qed.

Lemma blt_beq_blt : forall a a',
  blt a a' = false -> beq a a' = false -> blt a' a = true.
Proof.
  intros a a' H1 H2.
  destruct (blt_beq_dec a a') as [[H3 | H4] | H5].
      rewrite H3 in H1.
      discriminate.
    rewrite H2 in H4.
    discriminate.
  trivial.
Qed.

Ltac blt_simpl_tac := 
  match goal with
    (* blt rewrite directly *)
    | [H : blt ?x ?y = ?f
      |- context [(blt ?x ?y)]] =>
       rewrite H; blt_simpl_tac
    | [H : blt ?x ?y = ?f,
       H0 : context [(blt ?x ?y)] 
      |- _ ] =>
       rewrite H in H0; blt_simpl_tac
         
    (* blt -> beq *)
    | [H : blt ?x ?y = true 
      |- context[(beq ?x ?y)]] =>
      rewrite (blt_t_beq_f H); blt_simpl_tac
    | [H : blt ?x ?y = true,
       H0 : context[(beq ?x ?y)] |- _ ] =>
      rewrite (blt_t_beq_f H) in H0; blt_simpl_tac
     
    (* bgt -> beq *)
    | [H : blt ?y ?x = true 
      |- context[(beq ?x ?y)]] =>
      rewrite (bgt_t_beq_f H); blt_simpl_tac
    | [H : blt ?y ?x = true, 
       H0 : context[(beq ?x ?y)] |- _ ] =>
      rewrite (bgt_t_beq_f H) in H0; blt_simpl_tac
         
    (* beq -> blt *)
    | [H : beq ?y ?x = true 
      |- context[(blt ?x ?y)]] =>
      rewrite (beq_t_blt_f H); blt_simpl_tac
    | [H : beq ?y ?x = true, 
       H0 : context[(blt ?x ?y)] |- _ ] =>
      rewrite (beq_t_blt_f H) in H0; blt_simpl_tac
         
    (* beq -> bgt *)
    | [H : beq ?y ?x = true 
      |- context[(blt ?y ?x)]] =>
      rewrite (beq_t_bgt_f H); blt_simpl_tac
    | [H : beq ?y ?x = true, 
       H0 : context[(blt ?y ?x)] |- _ ] =>
      rewrite (beq_t_bgt_f H) in H0; blt_simpl_tac

    (* blt_irrefl *)
    | [ |- context [blt ?x ?x]] =>
      rewrite (@blt_irrefl x); blt_simpl_tac
    | [H : context [blt ?x ?x] |- _ ] =>
      rewrite (@blt_irrefl x) in H; blt_simpl_tac

    (* blt_asym *)
    | [H : blt ?x ?y = true 
      |- context [blt ?y ?x]] =>
      rewrite (blt_asym x y H); blt_simpl_tac
    | [H : blt ?x ?y = true,
       H0 : context [blt ?y ?x] |- _ ] =>
      rewrite (blt_asym x y H) in H0; blt_simpl_tac

    (* blt_beq_blt *)
    | [H : blt ?x ?y = false,
       H1 : beq ?x ?y = false
      |- context [blt ?y ?x]] =>
      apply (blt_beq_blt H H1); blt_simpl_tac
    | [H : blt ?x ?y = false,
       H1 : beq ?y ?x = false
      |- context [blt ?y ?x]] =>
      apply (blt_beq_blt H (beq_sym H1)); blt_simpl_tac

    | [H : ?x = ?x |- _ ] => clear H; blt_simpl_tac
    | [H : true = false |- _ ] => discriminate H
    | [H : false = true |- _ ] => discriminate H
    | _ => idtac
  end.

Ltac blt_dec_tac x y :=
  let Hb := fresh "Hb" in
    (destruct (blt_dec x y) as [Hb | Hb]; blt_simpl_tac).


(*****************************************************************************)
(** Definition of map                                                        *)
(*****************************************************************************)

(* raw_list *)
Definition rlist := list (prod A B).

(* lb a rl: forall a', (a' _) in rlist, then a < a' *)
Fixpoint lb (a : A) (rl : rlist) {struct rl} : Prop :=
  match rl with 
    | nil => True
    | (a', b') :: rl' => (blt a a' = true) /\ (lb a rl')
  end.

Lemma lb_trans : 
  forall rl a1 a2, lb a2 rl -> blt a1 a2 = true -> lb a1 rl.
Proof.
  unfold lb.
  induction rl as [ | (a, b) rl' IHrl' ]; fold lb in *; trivial.
  intros a1 a2 [H1 H2] H.
  split.
  apply blt_trans with a2; trivial.
  apply (IHrl' a1 a2); trivial.
Qed.

(* rl is ordered by a in (a, _) *)
Fixpoint is_orderset (rl : rlist) : Prop :=
  match rl with 
    | nil => True
    | (a', b') :: rl' => (lb a' rl') /\ (is_orderset rl')
  end.

(***********************)
(** map                *)
(***********************)

(* forall (listset_con lst prove-of-order) : listset, is_orderset lst *)
Inductive listset  := 
  | listset_con : forall lst : rlist, 
                 is_orderset lst -> listset.

(*   Parameter map : Type. *)
Definition map := listset.

Definition lst (m : listset) := let (lst, _) := m in lst.

Definition prf (m : listset) := 
  let (lst, prf) as m return (is_orderset (lst m)) 
    := m in prf.

(* Parameter get : map -> A -> option B. *)
(* get' rl a: according a, get b, which (a,b) in rl *)
Fixpoint get' (rl : rlist) (a : A) {struct rl} : option B :=
  match rl with 
    | nil => None
    | (a', b') :: rl' =>
        match (beq a a') with
          | true => Some b'
          | false => get' rl' a
        end
  end.

Lemma lb_notin : 
  forall rl a, lb a rl -> get' rl a = None.
Proof.
  unfold get', lb.
  induction rl as [|(a', b') rl' IHrl']; trivial.
  intros a [H1 H2].
  destruct (eq_dec a a') as [Heq | Hneq].
    subst a'.
    rewrite (@blt_irrefl a) in H1.
    discriminate.
  beq_simpl_tac.
  apply IHrl'.
  apply H2.
Qed.

Lemma in_notlb :
  forall rl a b, get' rl a = Some b -> ~ lb a rl.
Proof.
  unfold not;intros.
  rewrite (lb_notin H0) in H.
  discriminate.
Qed.

Definition get (m : map) (a : A) := get' (lst m) a.

Lemma get_dec :
  forall (m : map) (a : A),
    {exists b, get m a = Some b} + {get m a = None}.
Proof.
  intros m a.
  destruct (get m a).
  left.
  exists b.
  trivial.
  right; trivial.
Qed.

(*   Parameter emp_map : map. *)

Definition emp' : rlist := nil.

Lemma is_orderset_emp' : is_orderset emp'.
Proof.
  red; apply I.
Qed.

Definition emp : map := listset_con is_orderset_emp'.

Lemma emp_sem : 
  forall a : A, get emp a = None.
Proof.
  intros; unfold get, emp; trivial.
Qed.
  
(*   Parameter sig : A -> B -> map. *)

Definition sig' (a : A) (b : B) := (a, b) :: nil.

Lemma is_orderset_sig' : forall a b, is_orderset (sig' a b).
Proof.
  unfold is_orderset, lb; intros; split; apply I.
Qed.

Definition sig (a : A) (b : B) := 
  @listset_con (sig' a b) (is_orderset_sig' a b).

Lemma sig_sem : forall (a a' : A) (b : B),
  get (sig a b) a' = 
  match (beq a a') with
    | true => Some b
    | false => None
  end.
Proof.
  unfold get, sig, get', sig', lst. intros a a' b.
  destruct (eq_dec a a').
  rewrite e; trivial.
  rewrite (@neq_beq_false a a').
  rewrite (@neq_beq_false a' a).
  trivial.
  apply sym_not_eq; trivial.
  trivial.
Qed.

Require Import Coq.Logic.Classical_Prop.

(* insert (a, b) to rl, sortedly *)
Fixpoint set' (a : A) (b : B) (rl : rlist) 
  {struct rl}: rlist :=
  match rl with
    | nil => (a, b) :: nil
    | (a', b') :: rl' =>
      match blt a a' with
        | true  => (a, b) :: rl
        | false =>           
          match beq a a' with 
            | true => (a', b) :: rl'
            | false => (a', b') :: (set' a b rl')
          end

      end
  end.

Lemma get'_set' : forall rl a b,
  get' (set' a b rl) a = Some b.
Proof.
  intros rl a b.
  induction rl as [|(a', b') rl' IHrl'].
    simpl. 
    beq_simpl_tac; trivial.
  simpl.
  destruct (blt_dec a a') as [Hblt | Hnblt].
    blt_simpl_tac.
    simpl.
    beq_simpl_tac.
    trivial.
  blt_simpl_tac.
  beq_case_tac a a'; beq_simpl_tac; simpl.
    rewrite Hb.
    trivial.
  beq_simpl_tac.
  trivial.
Qed.

Lemma get'_set'_neq : forall rl a a0 b,
  a <> a0 -> get' (set' a b rl) a0 = get' rl a0.
Proof.
  intros rl a a0 b Hneq.
  induction rl as [|(a', b') rl' IHrl'].
    simpl.
    beq_simpl_tac.
    trivial.
  simpl.
  destruct (blt_dec a a') as [Hblt | Hnblt].
    rewrite Hblt.
    simpl.
    beq_simpl_tac.
    trivial.
  rewrite Hnblt.
  destruct (beq_dec a a') as [Hbeq | Hnbeq].
    rewrite Hbeq.
    simpl.
    beq_rewrite_tac Hbeq.
    beq_simpl_tac.
    trivial.
  rewrite Hnbeq.
  simpl.
  rewrite IHrl'.
  trivial.
Qed.

Lemma lb_set'_lt : forall rl a a0 b,
  lb a rl -> blt a0 a = true -> lb a0 (set' a b rl).
Proof.
  intros rl a a0 b Ha Hlta0.
  induction rl as [|(a', b') rl' IHrl'].
    simpl in *.
    split; trivial.
  simpl in *.
  destruct Ha as [Hlta Hlb].
  destruct (blt_dec a a') as [Hblt | Hnblt].
    rewrite Hblt.
    simpl.
    split; trivial.
    split. 
      eapply blt_trans; eauto.
    eapply lb_trans; eauto.
  rewrite Hlta in Hnblt.
  discriminate.
Qed.

Lemma lb_set'_gt : forall rl a a0 b,
  lb a0 rl -> blt a0 a = true -> lb a0 (set' a b rl).
Proof.
  intros rl a a0 b Ha0 Hlta.
  induction rl as [|(a', b') rl' IHrl'].
    simpl in *.
    split; trivial.
  simpl in *.
  destruct Ha0 as [Hlta0 Hlb].
  destruct (blt_dec a a') as [Hblt | Hnblt]. 
    rewrite Hblt.
    simpl.
    split; trivial.
    split; trivial.
  rewrite Hnblt.
  destruct (beq_dec a a') as [Hbeq | Hnbeq].
    rewrite Hbeq.
    simpl.
    beq_rewrite_tac Hbeq.
    split; trivial.
  rewrite Hnbeq.
  simpl.
  split; trivial.
  apply (IHrl' Hlb).
Qed.

Lemma is_orderset_set' : forall rl : rlist, 
  is_orderset rl -> forall a b, is_orderset (set' a b rl).
Proof.
  intros rl Hrl a b.
  induction rl as [|(a', b') rl' IHrl'].
  split; trivial.
  simpl in *.
  destruct Hrl as [Hlb Hrl'].
  destruct (blt_dec a a') as [Hblt | Hnblt].
    rewrite Hblt.
    simpl.
    split; split; trivial.
  eapply lb_trans; eauto.
  rewrite Hnblt.
  destruct (beq_dec a a') as [Hbeq | Hnbeq].
    rewrite Hbeq.
    simpl.
    split; trivial.
  rewrite Hnbeq.
  simpl.
  split.
    eapply lb_set'_gt; eauto.
    blt_simpl_tac.
  apply (IHrl' Hrl').
Qed.

Definition set (m : map) (a : A) (b : B) : map :=
  @listset_con (set' a b (lst m)) 
         (@is_orderset_set' (lst m) (prf m) a b).

Lemma set_sem_old : forall m a a' b, 
  match (beq a a') with
    | true => get (set m a b) a = Some b
    | false => get (set m a b) a' = get m a'
  end.
Proof.
  intros m a a' b.
  unfold get, set.
  destruct m as [m prf0].
  destruct (beq_dec a a') as [Heq | Hneq].
    rewrite Heq.
    simpl.
    eapply get'_set'; eauto.
  rewrite Hneq.
  simpl.
  eapply get'_set'_neq; eauto.
  beq_simpl_tac.
Qed.

Lemma set_sem : forall m a a' b,
  get (set m a b) a' =
  match (beq a a') with
    | true => Some b
    | false => get m a'
  end.
  intros.
  assert (H := set_sem_old). substH H with (H m a a' b).
  assert (H1 := beq_true_eq). substH H1 with (H1 a a').
  assert (H2 := beq_false_neq). substH H2 with (H2 a a').
  destruct (beq a a').
  substH H1 with (H1 (refl_equal _)).
  rewrite H1 in H; rewrite H1; trivial.
  trivial.
Qed.


(***********************)
(** extensionality     *)
(***********************)

Lemma equal_ext: forall m1 m2, (lst m1) = (lst m2) -> m1 = m2.
Proof.
  destruct m1 as [m1  prf1].
  destruct m2 as [m2  prf2].
  simpl.
  intros.
  subst m1.
  rewrite (proof_irrelevance _ prf1 prf2).
  auto.
Qed.

Lemma extensionality: forall (m1 m2 : map), 
  (forall a, get m1 a = get m2 a) -> m1 = m2.
Proof.
  intros m1 m2 H.
  apply equal_ext.
  destruct m1 as [m1 prf1].
  destruct m2 as [m2 prf2].
  gen_clear m1 m2 prf1 prf2 H.
  induction m1 as [|(a1, b1) m1' IHm1'];
    unfold get, get', lst; 
      cbv beta in *; fold get' in *; 
        intros.

  induction m2 as [|(a2, b2) m2' IHm2'];
    unfold get, get', lst; 
      cbv beta in *; fold get' in *.
  reflexivity.
  simpl in H.
  assert (H2 := H a2). 
    beq_simpl_tac. 
    discriminate.
  destruct m2 as [|(a2,b2) m2']; simpl in * .
  assert (H1 := H a1). 
    beq_simpl_tac. 
    discriminate.
  assert (He : 
    forall a : A, get' m1' a = get' m2' a).
(* subgoals := a1 < a2 , a1 = a2, a1 > a2 *)
  destruct (blt_beq_dec a1 a2) as [ [Hb | Hb ] | Hb].
  (* a1 < a2 *)
  substH H with (H a1).
  blt_simpl_tac.
  beq_simpl_tac.
  assert (Hf := @in_notlb m2' a1 b1).
  rewrite <- H in Hf; clear H.
  assert (Hlb := @lb_trans m2' a1 a2 (proj1 prf2) Hb).
  destruct (Hf (refl_equal _) Hlb).
  (* a1 = a2 *)
  intro a; substH H with (H a).
  assert (H0 := @beq_true_eq a1 a2 Hb).
  subst a1.
  destruct (eq_dec a a2) as [Heq | Hneq].
  subst a2.
  blt_simpl_tac; beq_simpl_tac.
  rewrite (@lb_notin m1' a (proj1 prf1)).
  rewrite (@lb_notin m2' a (proj1 prf2)).
  trivial.
  beq_simpl_tac.
  trivial.
  (* a1 > a2 *)
  substH H with (H a2).
  beq_simpl_tac.
  blt_simpl_tac.
  assert (Hf := @in_notlb m1' a2 b2).
  rewrite <- H in Hf; clear H.
  assert (Hlb := @lb_trans m1' a2 a1 (proj1 prf1) Hb).
  destruct (Hf (refl_equal _) Hlb).
(* solved *)
  substH IHm1' with
    (IHm1' m2' (proj2 prf1) (proj2 prf2) He).
  subst m2'.
  assert (H1 := H a1).
  assert (H2 := H a2).
  beq_simpl_tac.
  beq_case_tac a1 a2; beq_simpl_tac.
    rewrite (@beq_true_eq a1 a2 Hb).
    injection H1; intro; subst; trivial.
  rewrite (@lb_notin m1' a1 (proj1 prf1)) in H1.
  discriminate.
Qed.

Lemma get_set_same : forall m a b, get m a = Some b -> set m a b = m.
Proof.
  intros.
  apply extensionality; intros.
  rewrite set_sem.
  destruct (beq_dec a a0) as [ Heq | Hneq ].
  rewrite Heq.
  apply beq_true_eq in Heq; subst; auto.
  rewrite Hneq.
  auto.
Qed.


(***********************************************************)
(**                                                        *)
(**    Lemmas                                              *)
(**                                                        *)
(**    Tactics                                             *)
(**                                                        *)
(***********************************************************)

(***********************)
(** indom              *)
(** lookup             *)
(***********************)

Definition indom (m : map) (a : A) := 
  exists b : B, get m a = Some b.

Definition lookup (m : map) (a : A) (b : B) := 
  get m a = Some b.
  
(***********************)
(** sub                *)
(** meq                *)
(** compat             *)
(***********************)

Definition sub (m1 m2 : map) :=
  forall (a : A) (b : B), 
    lookup m1 a b -> lookup m2 a b.
  
Definition meq (m1 m2 : map) :=
  sub m1 m2 /\ sub m2 m1.

Definition compat (m1 m2 : map) : Prop :=
  forall a : A,
    match get m1 a, get m2 a with
      | Some b1, Some b2 => b1 = b2
      | _, _ => True
    end.

(************************)
(** disj                *)
(************************)

  Definition disj (m1 m2 : map) : Prop :=
    forall a : A, 
      match get m1 a, get m2 a with
        | Some b, None => True
        | None, Some b => True
        | None, None => True
        | _ , _ => False
      end.

(************************)
(** merge               *)
(************************)

Fixpoint app' (rl1 rl2 : rlist) {struct rl1} : rlist :=
  match rl1 with 
    | nil => rl2
    | (a,b) :: rl1' =>
      (set' a b (app' rl1' rl2))
  end.

Lemma is_set_app' : forall (rl1 rl2 : rlist), 
  is_orderset rl1 -> is_orderset rl2 -> is_orderset (app' rl1 rl2).
Proof.
  intros rl1 rl2 Hrl1 Hrl2.
  induction rl1 as [|(a', b') rl1' IHrl1'].
  simpl; trivial.
  simpl in *.
  apply is_orderset_set'.
  apply (IHrl1' (proj2 Hrl1)).
Qed.

Definition merge (m1 : map) (m2 : map) : map :=
  @listset_con (app' (lst m1) (lst m2)) 
    (@is_set_app' _ _ (prf m1) (prf m2)).

Lemma merge_sem : forall (m1 m2 : map) (a : A),
    get (merge m1 m2) a 
    = match (get m1 a, get m2 a) with
        | (Some b1, Some b2) => Some b1
        | (Some b1, None) => Some b1
        | (None, Some b2) => Some b2
        | (None, None) => None
      end.
Proof.
  intros m1 m2 a.
  unfold merge, get.
  destruct m1 as [rl1 prf1].
  destruct m2 as [rl2 prf2].
  simpl.
  induction rl1 as [|(a', b') rl1' IHrl1'].
  simpl.
  destruct (get' rl2 a); trivial.
  simpl in *.
  destruct (eq_dec a a') as [Heq | Hneq].
    subst a'; simpl.
    rewrite (get'_set' (app' rl1' rl2) a b').
    beq_simpl_tac.
    destruct (get' rl2 a); trivial.
    assert (Hneq' : a' <> a).
      intro H; apply Hneq; auto.
  beq_simpl_tac.
  rewrite (@get'_set'_neq (app' rl1' rl2) 
    a' a b' Hneq').
  apply IHrl1'.
  apply (proj2 prf1).
Qed.

(* subtract m/m1 *)

Fixpoint minus' (rl1 rl2 : rlist) {struct rl1} : rlist :=
  match rl1 with 
    | nil => nil
    | (a,b) :: rl1' => 
      match (get' rl2 a) with
        | Some b' => (minus' rl1' rl2)
        | None => set' a b (minus' rl1' rl2)
      end 
  end.

Lemma is_orderset_minus' : forall (rl1 rl2 : rlist), 
  is_orderset rl1 -> is_orderset (minus' rl1 rl2).
Proof.
  intros rl1 rl2 Hrl1.
  induction rl1 as [|(a', b') rl1' IHrl1'].
  simpl; trivial.
  simpl in *.
  destruct (get' rl2 a').
  apply (IHrl1' (proj2 Hrl1)).
  apply is_orderset_set'.
  apply (IHrl1' (proj2 Hrl1)).
Qed.

Definition minus (m : map) (m1 : map) : map :=
  @listset_con (minus' (lst m) (lst m1)) 
    (@is_orderset_minus' _ _ (prf m)).

Lemma lb_minus' : forall (rl1 rl2 : rlist) (a : A), 
  lb a rl1 -> lb a (minus' rl1 rl2).
Proof.
  intros rl1 rl2. 
  induction rl1 as [|(a', b') rl1' IHrl1'].
    intros a H.
    simpl; trivial.
  simpl in *.
  intros a [Heq Hlb].
  destruct (get' rl2 a').
  apply (IHrl1' _ Hlb).
  apply lb_set'_gt; trivial.
  apply IHrl1'; trivial. 
Qed.

Lemma minus_sem : forall (m m1 : map) (a : A),
    get (minus m m1) a 
    = match (get m a, get m1 a) with
        | (Some b, Some b1) => None
        | (Some b1, None) => Some b1
        | (None, Some b2) => None
        | (None, None) => None
      end.
Proof.
  intros m1 m2 a.
  unfold minus, get.
  destruct m1 as [rl1 prf1].
  destruct m2 as [rl2 prf2].
  simpl.
  induction rl1 as [|(a', b') rl1' IHrl1'].
    simpl.
    destruct (get' rl2 a); trivial.
  simpl in *.
  destruct (eq_dec a a') as [Heq | Hneq].
    subst a'; simpl.
    (* rewrite (get'_set' (app' rl1' rl2) a b'). *)
    beq_simpl_tac.
    destruct (get' rl2 a); trivial.
      destruct prf1.
      apply lb_notin; trivial.
    apply lb_minus'; trivial.
    apply get'_set'; trivial.
  assert (Hneq' : a' <> a).
    intro H; apply Hneq; auto.
  beq_simpl_tac.
  destruct (get' rl2 a').
    apply IHrl1'.
    destruct prf1.
    trivial.
  rewrite (@get'_set'_neq (minus' rl1' rl2) 
    a' a b' Hneq').
  apply IHrl1'.
  apply (proj2 prf1).
Qed.

(************************)
(** join                *)
(************************)

(* join and merge are not same  *)
(* join need the intersection of m1 and m2 to be zero *)  
Definition join (m1 m2 m: map) :=
  forall a : A,
    match get m1 a, get m2 a, get m a with
      | None, Some b1, Some b2 => b1 = b2
      | Some b1, None, Some b2 => b1 = b2
      | None, None, None => True
      | _, _, _ => False
    end.

Definition join3 (m1 m2 m3 m: map) :=
  forall a : A,
    match get m1 a, get m2 a, get m3 a, get m a with
      | Some b1, None, None, Some b2 => b1 = b2
      | None, Some b1, None, Some b2 => b1 = b2
      | None, None, Some b1, Some b2 => b1 = b2
      | None, None, None, None => True
      | _, _, _, _ => False
    end.

(***********************************************************)
(**                                                        *)
(**    Lemmas                                              *)
(**                                                        *)
(**    Tactics                                             *)
(**                                                        *)
(***********************************************************)

(***********************)
(** get set            *)
(***********************)

Ltac destruct_get :=
  match goal with
  
    | H: context [ get ?m ?a ] |- _ =>
        destruct (get m a);
          destruct_get

    | |- context [ get ?m ?a ] =>
        destruct (get m a);
          destruct_get

    | _ => idtac

end.

Ltac rewrite_get :=
  match goal with

    | H: context [ get (merge ?m1 ?m2) ?a ] |- _ =>
        rewrite (merge_sem m1 m2 a) in H;
        rewrite_get

    | H: context [ get (set ?m ?a ?b) ?a' ] |- _ =>
        rewrite (set_sem m a a' b) in H;
        beq simpl;
        rewrite_get

    | H: context [ get (sig ?a ?b) ?a' ] |- _ =>
        rewrite (sig_sem a a' b) in H;
        beq simpl;
        rewrite_get

    | H: context [ get emp ?a ] |- _ =>
        rewrite (emp_sem a) in H;
        rewrite_get

    | |- context [ get (merge ?m1 ?m2) ?a ] =>
        rewrite (merge_sem m1 m2 a);
        rewrite_get

    | |- context [ get (set ?m ?a ?b) ?a' ] =>
        rewrite (set_sem m a a' b);
        beq simpl;
        rewrite_get

    | |- context [ get (sig ?a ?b) ?a' ] =>
        rewrite (sig_sem a a' b);
        beq simpl;
        rewrite_get

    | |- context [ get emp ?a ] =>
        rewrite (emp_sem a);
        rewrite_get

    | _ => idtac

end.

Ltac solve_sn :=
  match goal with

    | H: context [ Some ?x = Some ?y ] |-
         context [ ?x = ?y ] =>
        injection H;
        solve_sn

    | H: context [ Some ?y = Some ?x ] |-
         context [ ?x = ?y ] =>
        injection H;
        solve_sn

    | H: context [ Some ?x = None ] |- _=>
        apply False_ind;
        discriminate;
        solve_sn

    | H: context [ None = Some ?x ] |- _ =>
        apply False_ind;
        discriminate;
        solve_sn

    | H: context [ ?x = ?y ] |-
         context [ Some ?x = Some ?z ] =>
        subst;
        solve_sn

    | H: context [ ?y = ?x ] |-
         context [ Some ?x = Some ?z ] =>
        subst;
        solve_sn

    | H: context [ _ -> Some ?x = Some ?y] |-
         context [ Some ?x = Some ?y ] =>
        apply H;
        solve_sn

    | H: context [ _ -> Some ?x = None ] |-
         context [ Some ?x = None ] =>
        apply H;
        solve_sn

    | H: context [ _ -> None = Some ?x] |-
         context [ None = Some ?x] =>
        apply H;
        solve_sn

    | |- context [_ -> _] =>
        intros;
        solve_sn

    | _ => try tauto || auto

end.      

Lemma get_sig : forall (a a' : A) (b : B),
  get (sig a b) a' = match (eq_dec a a') with
                      | left _ => Some b
                       | right _ => None
                     end.
Proof.
  intros.
  rewrite_get; trivial.
  destruct (eq_dec a a').
  beq_case_tac a a'; beq_simpl_tac; trivial.
  subst a.
  beq_simpl_tac.
  beq_case_tac a a'; beq_simpl_tac; trivial.
Qed.

Lemma get_sig_some : forall (a : A) (b : B),
    get (sig a b) a = Some b.
Proof.
  intros.
  rewrite_get.
  trivial.
Qed.

Lemma get_sig_none : forall (a a' : A) (b : B),
  a <> a'
  -> get (sig a b) a' = None.
Proof.
  intros.
  rewrite_get.
  beq_case_tac a a'; beq_simpl_tac; trivial.
Qed.

Lemma get_a_sig_a : forall (a a' : A) (b : B),
  beq a a' = true -> get (sig a b) a' = Some b.
Proof.
  intros.
  rewrite_get.
  trivial.
Qed.

Lemma get_a_sig_a' : forall (a a' : A) (b : B),
  beq a a' = false -> get (sig a b) a' = None.
Proof.
  intros.
  rewrite_get.
  trivial.
Qed.

Lemma get_sig_some_eq : forall (a a' : A) (b : B),
  get (sig a b) a' = Some b -> a = a'.
Proof.
  intros.
  beq_case_tac a a'.
    beq_rewrite_tac Hb.
    trivial.
  rewrite get_a_sig_a' in H; trivial.
  discriminate H.
Qed.

Lemma get_sig_some_eq' : forall (a a' : A) (b b' : B),
  get (sig a b) a' = Some b' -> a = a' /\ b = b'.
Proof.
  intros.
  beq_case_tac a a'.
    assert (a = a').
      beq_rewrite_tac Hb; trivial.
    split; trivial.
    subst a'.
    rewrite get_sig_some in H.
    inversion H; trivial.
  rewrite get_a_sig_a' in H; trivial.
  discriminate H.
Qed.
  
Lemma set_a_get_a : forall (m : map) (a a' : A) (b : B),
  beq a a' = true -> get (set m a b) a' = Some b.
Proof.
  intros.
  rewrite_get.
  trivial.
Qed.

Lemma set_a_get_a' : forall (m : map) (a a' : A) (b : B),
  beq a a' = false -> get (set m a b) a' = get m a'.
Proof.
  intros.
  rewrite_get.
  trivial.
Qed.

Lemma set_sig : forall a b b',
  set (sig a b) a b' = sig a b'.
Proof.
  intros a b b'.
  apply extensionality.
  intro a0.
  beq_case_tac a a0.
    rewrite set_sem.
    rewrite Hb.
    rewrite sig_sem.
    rewrite Hb.
    trivial.
  rewrite set_sem.
  rewrite Hb.
  rewrite sig_sem.
  rewrite Hb.
  rewrite sig_sem.
  rewrite Hb.
  trivial.
Qed.

Lemma set_emp_sig : forall a b,
  set emp a b = sig a b.
Proof.
  intros.
  apply extensionality.
  intros.
  beq_case_tac a a0.
Qed.

(***********************)
(** lookup             *)
(***********************)

Lemma lookup_emp : forall (a : A) (b : B),
  lookup emp a b -> False.
Proof.
  intros a b; unfold lookup.
  intros H; rewrite_get.
  discriminate.
Qed.

Lemma lookup_get : forall (m : map) (a : A) (b : B),
  lookup m a b
  -> get m a = Some b.
Proof.
  intros m a b. unfold lookup. trivial.
Qed.

Lemma get_lookup : forall (m : map) (a : A) (b : B),
  get m a = Some b
    -> lookup m a b.
Proof.
  intros; unfold lookup; trivial.
Qed.

Lemma lookup_unique : forall (m : map) (a : A) (b b' :B),
  lookup m a b -> lookup m a b' -> b = b'.
Proof.
  intros m a b b'; unfold lookup.
  intros H1 H2; rewrite H1 in H2; injection H2.
  trivial.
Qed.

(**********************)
(** indom <--> lookup *)
(**********************)

Lemma lookup_indom : forall (m : map) (a : A) (b : B),
    lookup m a b -> indom m a.
Proof.
  intros m a b; unfold lookup, indom. 
  intros H; exists b; trivial.
Qed.

Lemma indom_lookup : forall (m : map) (a : A), 
  indom m a 
  -> exists b : B, 
    lookup m a b.
Proof.
  intros m a; unfold indom, lookup; trivial.
Qed.

(***********************)
(** indom <---> get    *)
(***********************)
 
Lemma indom_get : forall (m : map) (a : A),
  indom m a 
  -> exists b : B, 
    get m a = Some b.
Proof.
  intros m a; unfold indom; trivial.
Qed.

Lemma get_indom : forall (m : map) (a : A),
  (exists b : B, get m a = Some b)
  -> indom m a.
Proof.
  intros m a; unfold indom; trivial.
Qed.

Lemma nindom_get :
  forall (m : map) (a : A),
    ~ indom m a -> get m a = None.
Proof.
  intros m a; unfold indom, not; trivial.
  destruct (get m a).
  intros H; elimtype False; apply H; exists b; trivial.
  trivial.
Qed.

(***********************)
(** sub                *)
(** meq                *)
(** compat             *)
(***********************)

Lemma sub_refl : forall (m : map),
  sub m m.
Proof.
  intros m a; destruct (get m a); trivial.
Qed.

(* prevent the funtion expanding from coq-type-checker *)
Implicit Arguments sub_refl[].

Lemma sub_asym : forall (m1 m2 : map),
  sub m1 m2 
  -> sub m2 m1
  -> meq m1 m2.
Proof.
  unfold meq.
  auto.
Qed.

Lemma sub_trans : forall (m1 m2 m3 : map),
  sub m1 m2 
  -> sub m2 m3
  -> sub m1 m3.
Proof.
  intros m1 m2 m3; unfold sub.
  intros H1 H2 a b.
    substH H1 with (H1 a b); 
    substH H2 with (H2 a b);
    auto.
Qed.
(* prevent the funtion expanding from coq-type-checker *)
Implicit Arguments sub_trans[m1 m2 m3].

Lemma sub_sig : forall m a b,
  get m a = Some b
  -> sub (sig a b) m.
Proof.
  unfold sub, lookup.
  intros.
  rewrite_get.
  beq_case_tac a a0.
    beq_simpl_tac.
    inversion H0.
    subst b0.
    beq_rewrite_tac Hb.
    trivial.
  beq_simpl_tac.
  discriminate.
Qed.

Lemma meq_refl : forall (m : map), 
  meq m m.
Proof.
  intros m; unfold meq; split; apply sub_refl.
Qed.

Lemma meq_sym : forall (m1 m2 : map),
  meq m1 m2 -> meq m2 m1.
Proof.
  intros m1 m2; unfold meq.
  intros [H1 H2]; split; assumption.
Qed.

Lemma meq_trans : forall (m1 m2 m3 : map),
  meq m1 m2
  -> meq m2 m3
  -> meq m1 m3.
Proof.
  intros m1 m2 m3; unfold meq, sub.
  intros [H1 H2] [H3 H4];
    split; intros a b;
    substH H1 with (H1 a b);
    substH H2 with (H2 a b);
    substH H3 with (H3 a b);
    substH H4 with (H4 a b);
    tauto.
Qed.

Lemma meq_sem : forall (m1 m2 : map),
  meq m1 m2 -> 
  forall (a : A),
    match get m1 a, get m2 a with
      | Some b1, Some b2 => b1 = b2
      | None, None => True
      | _, _ => False
    end.
Proof.
  unfold meq, sub, lookup.
  intros m1 m2 [H1 H2] a.
  substH H1 with (H1 a).
  substH H2 with (H2 a).
  destruct_get; auto.
  substH H2 with (H2 b (refl_equal _)).
  injection H2.
  trivial.
  substH H2 with (H2 b (refl_equal _)).
  discriminate.
  substH H1 with (H1 b (refl_equal _)).
  discriminate.
Qed.

(* The lemma below is another form of extensionality *)
Lemma meq_eq : forall m1 m2 : map,
  meq m1 m2 -> m1 = m2.
Proof.
  intros m1 m2 H.
  assert (H' := @meq_sem m1 m2 H).
  apply extensionality.
  intro a.
  substH H' with (H' a).
  destruct (get m1 a); destruct (get m2 a); simpl; subst; trivial. 
  destruct H'.
  destruct H'.
Qed.

Lemma compat_refl : forall m : map,
  compat m m.
Proof.
  unfold compat.
  intros.
  destruct_get; trivial.
Qed.

Lemma compat_sym : forall (m1 m2 : map),
  compat m1 m2 -> compat m2 m1.
Proof.
  unfold compat; intros m1 m2 H a.
  substH H with (H a).
  destruct_get;
    auto.
Qed.

(***********************)
(** get    <--> sub    *)
(** lookup <--> sub    *)
(***********************)

Lemma get_sub_get : forall (m1 m2 : map) (a : A) (b : B),
  get m1 a = Some b -> sub m1 m2 -> get m2 a = Some b.
Proof.
  unfold sub.
  intros m1 m2 a b H H1.
  substH H1 with (H1 a b).
  apply (H1 H).
Qed.

Lemma lookup_sub_lookup : forall (m1 m2 : map) (a : A) (b : B),
  lookup m1 a b -> sub m1 m2 -> lookup m2 a b.
Proof.
  unfold sub.
  intros m1 m2 a b H H1.
  substH H1 with (H1 a b).
  apply (H1 H).
Qed.

Lemma indom_sub_indom : forall m1 m2 a, 
    indom m1 a -> sub m1 m2 -> indom m2 a.
Proof.
  unfold meq, sub. 
  intros m1 m2 a H H1. 
  substH H with (indom_lookup H).
  destruct H as [b H].
  substH H1 with (H1 a b).
  apply (lookup_indom (H1 H)).
Qed.

(***********************)
(** lookup <--> meq    *)
(***********************)

Lemma lookup_meq_lookup : forall (m1 m2 : map) (a : A) (b : B),
  lookup m1 a b -> meq m1 m2 -> lookup m2 a b.
Proof.
  unfold meq, sub.
  intros m1 m2 a b H0 [H1 H2].
  substH H1 with (H1 a b);
  substH H2 with (H2 a b).
  apply (H1 H0).
Qed.

Lemma indom_meq_indom : forall m1 m2 a, 
    indom m1 a -> meq m1 m2 -> indom m2 a.
Proof.
  unfold meq, sub. 
  intros m1 m2 a H [H1 H2]. 
  substH H with (indom_lookup H).
  destruct H as [b H].
  substH H1 with (H1 a b);
  substH H2 with (H2 a b).
  apply (lookup_indom (H1 H)).
Qed.

(************************)
(** disj                *)
(************************)

Lemma disj_emp_l : forall (m : map),
  disj (emp) m.
Proof.
  intros m a; rewrite_get;
  destruct_get; trivial.
Qed.

Lemma disj_emp_r : forall (m : map),
  disj m (emp).
Proof.
  intros m a;rewrite_get;
  destruct_get; trivial.
Qed.

Lemma disj_sym : forall (m1 m2 : map),
  disj m1 m2
  -> disj m2 m1.
Proof.
  intros m1 m2 H a;
  substH H with (H a);
  destruct_get; trivial.
Qed.

Lemma disj_sig : forall (a a' : A) (b b' : B),
  beq a a' = false
  -> disj (sig a b) (sig a' b').
Proof.
  intros.
  unfold disj.
  intros a0.
  beq_case_tac a a0; beq_case_tac a' a0.
  destruct_get; trivial.
  beq_rewriteH_tac Hb H.
  beq_rewriteH_tac Hb0 H.
  beq_simpl_tac.
  rewrite (@get_a_sig_a' a' a0); trivial.
  destruct_get; trivial.
  rewrite (@get_a_sig_a' a a0); trivial.
  destruct_get; trivial.
  rewrite (@get_a_sig_a' a a0); trivial.
  rewrite (@get_a_sig_a' a' a0); trivial.
Qed.

(***********************)
(** indom <---> disj   *)
(***********************)

Lemma disj_indom : 
  forall (m1 m2 : map),
    disj m1 m2 
    -> (forall a : A, 
      (indom m1 a -> ~ indom m2 a)
      /\ (indom m2 a -> ~ indom m1 a)).
Proof.
  intros m1 m2 H a; unfold indom, not;
    substH H with (H a);split; 
      intros H1 H2; 
        destruct H1 as [b1 H1];
          destruct H2 as [b2 H2];
            destruct_get; solve_sn.
Qed.

Lemma indom_disj : forall (m1 m2 : map),
  (forall a : A, 
    (indom m1 a -> ~ indom m2 a)
    /\ (indom m2 a -> ~ indom m1 a))
  -> disj m1 m2.
Proof.
  unfold indom, disj, not.
  intros m1 m2 H a.
    substH H with (H a).
  destruct H as [H1 H2]. 
    destruct_get; solve_sn.
  apply H1.
  exists b0; trivial.
  exists b; trivial.
Qed.

(* (***********************) *)
(* (** disj --> lookup    *) *)
(* (***********************) *)
(* Lemma lookup_disj : forall (m1 m2 : map), *)
(*   (forall (a : A) (b : B), *)
(*     (lookup m1 a b -> ~ lookup m2 a b) *)
(*     /\ (lookup m1 a b -> ~ lookup m2 a b)) *)
(*   -> disj m1 m2. *)
(* Proof. *)
(*   intros m1 m2 H. *)
(*   unfold disj. *)
(*   intro a. *)
(* Qed. *)

(* Lemma disj_lookup forall (m1 m2 : map) (a : A) (b : B), *)
(*   disj m1 m2 *)
(*   ->   *)
(*   (forall (a : A) (b : B), *)
(*     (lookup m1 a b -> ~ lookup m2 a b) *)
(*     /\ (lookup m1 a b -> ~ lookup m2 a b)) *)
(* Proof. *)

(* Qed. *)

(***********************)
(** disj <--> meq       *)
(***********************)


Lemma disj_meq_disj_r : forall (m1 m2 m3 : map),
  disj m1 m2 
  -> meq m2 m3 
  -> disj m1 m3.
Proof.
  unfold disj, meq, sub, lookup.
  intros m1 m2 m3 Hj [H1 H2] a.
  substH Hj with (Hj a).
  substH H1 with (H1 a).
  substH H2 with (H2 a).
  destruct_get; solve_sn.
  substH H2 with (H2 b (refl_equal _)); discriminate.  
Qed.

Lemma disj_meq_disj_l : forall (m1 m2 m3 : map),
  disj m1 m2 
  -> meq m1 m3 
  -> disj m3 m2.
Proof.
  unfold disj, meq, sub, lookup.
  intros m1 m2 m3 Hj [H1 H2] a.
  substH Hj with (Hj a).
  substH H1 with (H1 a).
  substH H2 with (H2 a).
  destruct_get; solve_sn.
  substH H2 with (H2 b (refl_equal _)); discriminate.
Qed.

(***********************)
(** disj --> compat    *)
(***********************)

Lemma disj_compat : forall m1 m2 : map,
  disj m1 m2 -> compat m1 m2.
Proof.
  unfold disj, compat.
  intros.
  substH H with (H a).
  destruct_get; solve_sn.
Qed.

(***********************)
(** sub <--> compat    *)
(***********************)

Lemma compat_sub_l : forall (m1 m2 : map),
  compat m1 m2 -> sub m1 (merge m1 m2).
Proof.
  intros m1 m2.
  unfold compat, sub, lookup.
  intros H a b.
  substH H with (H a).
  rewrite_get;
    destruct_get; solve_sn.
Qed.

Lemma compat_sub_r : forall (m1 m2 : map),
    compat m1 m2 -> sub m2 (merge m1 m2).
Proof.
  intros m1 m2.
  unfold compat, sub, lookup.
  intros H a b.
  substH H with (H a).
  rewrite_get;
    destruct_get; solve_sn.
Qed.

Lemma sub_compat :
  forall (m1 m2 : map),
    sub m1 m2 -> compat m1 m2.
Proof.
  unfold sub, compat, lookup.
  intros.
  substH H with (H a).
  destruct_get; auto.
  substH H with (H b (refl_equal _)).
  injection H; auto.
Qed.

(*************************************************)
(**                                              *)
(** *  merge (union)                             *)
(**                                              *)
(*************************************************)

(* 
  sub <--> merge
*)

Lemma sub_merge_l :
  forall (m1 m2 : map),
    compat m1 m2
    -> sub m1 (merge m1 m2).
Proof.
  unfold compat, sub, lookup.
  intros.
  substH H with (H a).
  rewrite_get;
    destruct_get;
      solve_sn.
Qed.

Lemma sub_merge_r :
  forall (m1 m2 : map),
    compat m1 m2
    -> sub m2 (merge m1 m2).
Proof.
  unfold compat, sub, lookup.
  intros.
  substH H with (H a).
  rewrite_get;
    destruct_get;
      solve_sn.
Qed.

Lemma sub_merge_elim_l :
  forall (m1 m2 m3: map),
    compat m1 m2
    -> sub (merge m1 m2) m3
    -> sub m1 m3.
Proof.
  intros.
  substH H with (sub_merge_l H).
  eapply sub_trans.
  eauto. assumption.
Qed.
Implicit Arguments sub_merge_elim_l [m1 m2 m3].

Lemma sub_merge_elim_r :
  forall (m1 m2 m3: map),
    compat m1 m2
    -> sub (merge m1 m2) m3
    -> sub m2 m3.
Proof.
  intros.
  substH H with (sub_merge_r H).
  eapply sub_trans.
  eauto. assumption.
Qed.
Implicit Arguments sub_merge_elim_r [m1 m2 m3].

Lemma sub_merge_intro_l :
  forall (m1 m2 m3: map),
    compat m1 m2
    -> sub m3 m1
    -> sub m3 (merge m1 m2).
Proof.
  intros.
  substH H with (sub_merge_l H).
  eapply sub_trans.
  eauto. assumption.
Qed.
Implicit Arguments sub_merge_intro_l [m1 m2 m3].

Lemma sub_merge_intro_r :
  forall (m1 m2 m3: map),
    compat m1 m2
    -> sub m3 m2
    -> sub m3 (merge m1 m2).
Proof.
  intros.
  substH H with (sub_merge_r H).
  eapply sub_trans.
  eauto. assumption.
Qed.
Implicit Arguments sub_merge_intro_r [m1 m2 m3].


Lemma merge_sub_intro : forall (m m1 m2 : map),
  sub m1 m 
  -> sub m2 m
  -> sub (merge m1 m2) m.
Proof.
  unfold sub, lookup.
  intros.
  substH H with (H a b).
  substH H0 with (H0 a b).
  rewrite_get;
    destruct_get; auto.
Qed.
Implicit Arguments merge_sub_intro [m m1 m2].

(*
  meq <--> merge
*)

Lemma meq_merge_sym : forall (m1 m2 : map),
  compat m1 m2
  -> meq (merge m1 m2) (merge m2 m1).
Proof.
  unfold compat, meq, sub, lookup.
  split; intros; substH H with (H a);
  rewrite_get;
  destruct_get;
    solve_sn.
Qed.

Lemma meq_merge_assoc_l : forall (m1 m2 m3 : map),
  meq 
  (merge (merge m1 m2) m3)
  (merge m1 (merge m2 m3)).
Proof.
  unfold meq, sub, lookup.
  intros; split; intros;
  rewrite_get;
  destruct_get;
    solve_sn.
Qed.

Lemma meq_merge_assoc_r : forall (m1 m2 m3 : map),
  meq 
  (merge m1 (merge m2 m3))
  (merge (merge m1 m2) m3).
Proof.
  unfold meq, sub, lookup.
  intros m1 m2 m3; split; intros a b;
  rewrite_get;
  destruct_get;
    trivial.
Qed.

Lemma meq_merge_emp_l : forall (m : map),
  meq (merge emp m) m.
Proof.
  unfold meq, sub, lookup.
  intros m; split; intros a b;
  rewrite_get;
  destruct_get;
    trivial.
Qed.

Lemma meq_merge_emp_r : forall (m : map),
  meq (merge m emp) m.
Proof.
  unfold meq, sub, lookup.
  intros m; split; intros a b;
  rewrite_get;
  destruct_get;
    trivial.
Qed.

Lemma meq_merge_meq : 
  forall m1 m2 m3 m4,
    meq m1 m3 -> meq m2 m4
    -> meq (merge m1 m2) (merge m3 m4).
Proof.
  unfold meq, sub, lookup.
  intros m1 m2 m3 m4 [H1 H2] [H3 H4].
  split; intros a b;
    substH H1 with (H1 a);
    substH H2 with (H2 a);
    substH H3 with (H3 a);
    substH H4 with (H4 a);
  rewrite_get;
  intros H;
    destruct (get m1 a) as [b1 |];
    destruct (get m2 a) as [b2 |];
    destruct (get m3 a) as [b3 |];
    destruct (get m4 a) as [b4 |];
      auto.
  assert (Hf := H1 b H); discriminate.
  assert (Hf := H2 b3 (refl_equal _)); discriminate.
  assert (Hf := H1 b1 (refl_equal _)); discriminate.
  assert (Hf := H2 b H); discriminate.
Qed.

(************************)
(** lookup <--> merge   *)
(************************)

Lemma lookup_merge_elim : 
  forall (m1 m2 : map) (a : A) (b : B),
    lookup (merge m1 m2) a b 
    -> lookup m1 a b \/ lookup m2 a b.
Proof.
  intros m1 m2 a b.
  unfold lookup; rewrite_get.
  destruct_get; auto.
Qed.

Lemma lookup_merge_intro :
  forall (m1 m2 : map) (a : A) (b : B), 
    lookup m1 a b \/ lookup m2 a b
    -> compat m1 m2
    -> lookup (merge m1 m2) a b.
Proof.
  intros m1 m2 a b.
  unfold lookup, compat; rewrite_get.
  intros [H1 | H2]; intros H; 
    substH H with (H a);   
    destruct_get;
      solve_sn.
Qed.

(********************************)
(** indom <--> merge            *)
(********************************)

Lemma indom_merge_intro :
  forall (m1 m2 : map) (a : A),
    indom m1 a \/ indom m2 a
    -> indom (merge m1 m2) a.
Proof. 
  (* < *)
  unfold indom.
  intros m1 m2 a [[b H]|[b H]];
  rewrite_get;
    destruct_get; solve_sn.
  exists b0; trivial.
  exists b0; trivial.
  exists b1; trivial.
  exists b; trivial.
  (* > *)
Qed.

Lemma indom_merge_elim : 
  forall (m1 m2 : map) (a : A),
  indom (merge m1 m2) a
  -> indom m1 a \/ indom m2 a.
Proof.
  (* < *)
  unfold indom.
  intros m1 m2 a [b H].
  rewrite_get;
    destruct_get; solve_sn.
  left; exists b; assumption.
  left; exists b; assumption.
  right; exists b; assumption.
  (* > *)
Qed.

(********************************)
(** disj <--> disj merge        *)
(********************************)

Lemma disj_merge_intro_l :
  forall (m1 m2 m3 : map),
    disj m1 m3 /\ disj m2 m3
    -> disj (merge m1 m2) m3.
Proof.
  unfold disj.
  intros m1 m2 m3 [H1 H2] a.
  substH H1 with (H1 a).
  substH H2 with (H2 a).
  rewrite_get;
    destruct_get; trivial.
Qed.

Lemma disj_merge_elim_l :
  forall (m1 m2 m3 : map),
    disj (merge m1 m2) m3    
    -> disj m1 m3 /\ disj m2 m3.
Proof.
  unfold disj.
  intros m1 m2 m3 H.
  split; intro a; substH H with (H a);
    rewrite_get;
      destruct_get; solve_sn.
Qed.

Lemma disj_merge_intro_r :
  forall (m1 m2 m3 : map),
    disj m1 m2 /\ disj m1 m3
    -> disj m1 (merge m2 m3).
Proof.
  intros.
  apply disj_sym.
  apply disj_merge_intro_l.
  elim H; intros; split; apply disj_sym; trivial.
Qed.

Lemma disj_merge_elim_r :
  forall (m1 m2 m3 : map),
    disj m1 (merge m2 m3)
    -> disj m1 m2 /\ disj m1 m3.
Proof.
  intros.
  substH H with (disj_merge_elim_l (disj_sym H)).
  elim H; split; intros;
  apply disj_sym; assumption.
Qed.

Lemma disj_merge_intro_lr :
  forall (m1 m2 m1' m2' : map),
    disj m1 m1'
    -> disj m1 m2'
    -> disj m2 m1'
    -> disj m2 m2'
    -> disj (merge m1 m2) (merge m1' m2').
Proof.
  unfold disj.
  intros m1 m2 m1' m2' H1 H2 H3 H4 a.
  substH H1 with (H1 a);
  substH H2 with (H2 a);
  substH H3 with (H3 a);
  substH H4 with (H4 a).
  rewrite_get;
    destruct_get; solve_sn.
Qed.

Lemma disj_merge_elim_lr :
  forall (m1 m2 m1' m2' : map),
    disj (merge m1' m2') (merge m1 m2)
    -> (disj m1 m1' /\ disj m1 m2')
    /\ (disj m2 m1' /\ disj m2 m2').
Proof.
  unfold disj.
  intros m1 m2 m1' m2' H.
  split; split; intro a;
  substH H with (H a);
  rewrite_get;
    destruct_get; solve_sn.
Qed.

(*************************************************)
(**                                              *)
(** * join lemmas                                *)
(**                                              *)
(*************************************************)

Lemma join_comm :
  forall ma mb mab : map,
    join ma mb mab -> join mb ma mab.
Proof.
  intros ma mb mab.
  unfold join.
  intros H a.
  substH H with (H a).
  destruct_get; auto.
Qed.

Lemma join_assoc_l :
  forall ma mb mc mab mabc,
    join ma mb mab->
    join mab mc mabc ->
    exists mbc, join mb mc mbc /\
      join ma mbc mabc.
Proof.
  intros ma mb mc mab mabc. 
  unfold join.
  intros H1 H2.
  exists (merge mb mc).
  split; intros a; 
    rewrite_get; 
    substH H1 with (H1 a);
    substH H2 with (H2 a);
    destruct_get; solve_sn.
  rewrite H1; trivial.
  rewrite H1; trivial.
Qed.

Lemma join_assoc_r :
  forall ma mb mc mbc mabc,
    join mb mc mbc->
    join ma mbc mabc ->
    exists mab, join ma mb mab /\
      join mab mc mabc.
Proof.
  intros ma mb mc mbc mabc. 
  unfold join.
  intros H1 H2.
  exists (merge ma mb).
  split; intros a;
    rewrite_get;
    substH H1 with (H1 a);
    substH H2 with (H2 a);
    destruct_get; solve_sn.
  rewrite H1; trivial.
  rewrite H1; trivial.
Qed.

Lemma join_disj_meq :
  forall (m1 m2 m : map),
    join m1 m2 m
    -> disj m1 m2 /\ meq (merge m1 m2) m.
Proof.
  unfold join, disj, meq,sub, lookup.
  split; intros; try split; intros; substH H with (H a);
  rewrite_get;
    destruct_get; solve_sn.
Qed.

Lemma disj_meq_join :
  forall (m1 m2 m: map),
    disj m1 m2 /\ meq (merge m1 m2) m
    -> join m1 m2 m.
Proof.
  unfold disj, meq,sub, lookup.
  intros m1 m2 m [H0 [H1 H2]] a.
  substH H0 with (H0 a);
  substH H1 with (H1 a);
  substH H2 with (H2 a).
  rewrite_get;
  destruct_get;
    (try substH H2 
      with (H2 b (refl_equal _)); 
      (injection H2 || discriminate || trivial; 
        trivial))
|| (try substH H2 
      with (H1 b (refl_equal _)); 
      (injection H1 || discriminate || trivial; 
        trivial));
    trivial.
Qed.

Lemma join_sub_l :
  forall m1 m2 m,
    join m1 m2 m
    -> sub m1 m.
Proof.
  intros m1 m2 m.
  unfold join, sub, lookup; intros H.
  intro a.
  substH H with (H a).
  destruct_get;
    solve_sn.
Qed.

Lemma join_sub_r :
  forall m1 m2 m,
    join m1 m2 m
    -> sub m2 m.
Proof.
  intros m1 m2 m.
  unfold join, sub, lookup; intros H.
  intro a.
  substH H with (H a).
  destruct_get; solve_sn.
Qed.
Implicit Arguments join_sub_r [m1 m2 m].

Lemma join_unique :
  forall m1 m2 m m',
  join m1 m2 m ->
  join m1 m2 m' ->
  m = m'.
Proof.
  intros.
  apply join_disj_meq in H.
  apply join_disj_meq in H0.
  destruct H.
  destruct H0.
  apply meq_eq in H1.
  apply meq_eq in H2.
  rewrite H1 in H2.
  assumption.
Qed.

Lemma join_lookup_lookup_l :
  forall m1 m2 m a b,
    join m1 m2 m
    -> lookup m1 a b
    -> lookup m a b.
Proof.
  intros m1 m2 m a b Hj H1.
  assert (H:= join_sub_l Hj).
  unfold sub in H.
  apply (H a b H1).
Qed.

Lemma join_lookup_lookup_r :
  forall m1 m2 m a b,
    join m1 m2 m
    -> lookup m2 a b
    -> lookup m a b.
Proof.
  intros m1 m2 m a b Hj H2.
  assert (H:= join_sub_r Hj).
  unfold sub in H.
  apply (H a b H2).
Qed.

Lemma join_get_get_l :
  forall m1 m2 m a b,
    join m1 m2 m
    -> get m1 a = Some b
    -> get m a = Some b.
Proof.
  intros m1 m2 m a b Hj H1.
  assert (H:= join_sub_l Hj).
  unfold sub, lookup in H.
  apply (H a b H1).
Qed.

Lemma join_get_get_r :
  forall m1 m2 m a b,
    join m1 m2 m
    -> get m2 a = Some b
    -> get m a = Some b.
Proof.
  intros m1 m2 m a b Hj H2.
  assert (H:= join_sub_r Hj).
  unfold sub, lookup in H.
  apply (H a b H2).
Qed.

Lemma join_merge_disj :
  forall m1 m2,
    disj m1 m2 ->
    join m1 m2 (merge m1 m2).
Proof.
  intros.
  unfold disj in *.
  unfold join.
  intros.
  assert (match get m1 a with
      | Some _ => match get m2 a with
                  | Some _ => False
                  | None => True
                  end
      | None => match get m2 a with
                | Some _ => True
                | None => True
                end
      end).
  apply H.
  clear H.
  rewrite merge_sem.
  destruct (get m1 a);destruct (get m2 a);trivial;assumption.
Qed.

Lemma join_lookup_or :
  forall m1 m2 m a b,
    join m1 m2 m ->
    lookup m a b ->
    (lookup m1 a b) \/ (lookup m2 a b).
Proof.
  intros.
  unfold lookup in *.
  unfold join in H.
  assert (match get m1 a with
      | Some b1 =>
          match get m2 a with
          | Some _ => False
          | None =>
              match get m a with
              | Some b2 => b1 = b2
              | None => False
              end
          end
      | None =>
          match get m2 a with
          | Some b1 =>
              match get m a with
              | Some b2 => b1 = b2
              | None => False
              end
          | None => match get m a with
                    | Some _ => False
                    | None => True
                    end
          end
      end).
  apply H.
  clear H.
  rewrite H0 in H1.
  destruct (get m1 a);destruct (get m2 a);destruct H1;try (left;reflexivity);try (right;reflexivity).
Qed.

Lemma join_get_or :
  forall m1 m2 m a b,
    join m1 m2 m ->
    get m a = Some b ->
    (get m1 a = Some b) \/ (get m2 a = Some b).
Proof.
  intros.
  apply get_lookup in H0.
  destruct (join_lookup_or H H0).
  left; apply get_lookup; trivial.
  right; apply get_lookup; trivial.
Qed.

Lemma join_set_l :
  forall m1 m2 m a b,
    join m1 m2 m
    -> indom m1 a
    -> join (set m1 a b) m2 (set m a b).
Proof.
  unfold indom, join.
  intros m1 m2 m a b H H1.
  intro a0.
  substH H with (H a0).
  destruct H1.
  rewrite_get.
  beq_case_tac a a0; beq simpl; trivial.
  assert (a = a0).
    beq rewrite Hb; trivial.
  subst a0.
  rewrite_get;
    destruct_get; solve_sn.
Qed.

Lemma join_set_r :
  forall m1 m2 m a b,
    join m1 m2 m
    -> indom m2 a
    -> join m1 (set m2 a b) (set m a b).
Proof.
  unfold indom, join.
  intros m1 m2 m a b H H1.
  intro a0.
  substH H with (H a0).
  rewrite_get.
  beq_case_tac a a0; beq simpl; trivial.
  rewrite_get.
  assert (a = a0).
    beq rewrite Hb; trivial.
  subst a0.
  destruct_get; trivial.
  destruct H1; discriminate.
Qed.

Lemma join_set_l_rev :
  forall m1 m2 m a b,
    join (set m1 a b) m2 m
    -> exists m', join m1 m2 m'
                  /\ m = (set m' a b).
Proof.
  unfold join.
  intros m1 m2 m a b H.
  exists (merge m1 m2).
  split.
    intro a0.
    substH H with (H a0).
    rewrite_get.
    beq_case_tac a a0; beq simpl; trivial.
    beq rewrite Hb; trivial.
    beq rewrite Hb in H; trivial.
    destruct (get m1 a); destruct (get m2 a); trivial; try contradiction.
    destruct (get m1 a0); destruct (get m2 a0); trivial; try contradiction.
  apply extensionality.
  intro a0. 
  substH H with (H a0).
  rewrite_get.  
  beq_case_tac a a0; beq simpl; trivial.
    beq rewrite Hb; trivial.
    beq rewrite Hb in H; trivial.
    destruct (get m2 a); destruct (get m a); trivial; try contradiction.
    subst; trivial.
  destruct (get m1 a0); destruct (get m2 a0); 
    destruct (get m a0); trivial; try contradiction.
    subst; trivial.
  subst; trivial.
Qed.

Lemma join_set_nindom_l :
  forall m1 m2 m m1' m' l v, join m1 m2 m ->
    m1' = set m1 l v ->
    m' = set m l v ->
    ~indom m l ->
    join m1' m2 m'.
Proof.
  intros.
  unfold join.
  intro.
  rewrite H0,H1.
  rewrite_get.
  beq_case_tac l a.
  rewrite Hb;simpl.
  rewrite nindom_get;auto.
  unfold join in H.
  generalize (H a);intros.
  red;intros. generalize (indom_get H4).
  intros. destruct H5.
  rewrite H5 in H3.
  generalize (nindom_get H2).
  intros. generalize (beq_true_eq Hb).
  intros. rewrite H7 in H6.
  rewrite H6 in H3. 
  destruct (get m1 a).
  inversion H3.
  inversion H3.
  rewrite Hb;simpl.
  apply H.
Qed.

Lemma join_set_nindom_r :
  forall m1 m2 m m2' m' l v, join m1 m2 m ->
    m2' = set m2 l v ->
    m' = set m l v ->
    ~indom m l ->
    join m1 m2' m'.
Proof.
  intros.
  apply join_comm.
  apply join_comm in H.
  eapply join_set_nindom_l;eauto.
Qed.

Lemma join_emp :
  forall m m',
    m = m' ->
    join emp m m'.
Proof.
  intros.
  subst m'.
  unfold join.
  unfold emp.
  simpl.  
  intros.
  destruct (get m a);trivial.
Qed.

Lemma join_sig_set : 
  forall m a b,
    ~indom m a ->
    join m (sig a b) (set m a b).
Proof.
  intros.
  rewrite<-set_emp_sig.
  eapply join_set_nindom_r;eauto.
  apply join_comm.
  apply join_emp.
  auto.
Qed.  

Lemma join_unique_r :
  forall m1 m2 m2' m,
  join m1 m2 m ->
  join m1 m2' m ->
  m2 = m2'.
Proof.
  intros m1 m2 m2' m H1 H2.
  apply extensionality.
  unfold join in * .
  intro a.
  assert (H3 := H1 a).
  assert (H4 := H2 a).
  clear H1 H2.
  destruct (get m1 a); destruct (get m2' a);
    destruct (get m a); destruct (get m1 a); 
      destruct (get m2 a); trivial; try contradiction.
    subst b2 b; trivial.
  subst b1 b; trivial.
Qed.

Lemma join_meq :
  forall m m',
  join emp m m' -> meq m m'.
Proof.
  intros.
  unfold emp in H.
  unfold meq.
  unfold sub.
  unfold lookup.
  intros.
  unfold join in H.
  simpl in H.
  split.
    intros.
    assert (match get m a with
      | Some b1 =>
          match get m' a with
          | Some b2 => b1 = b2
          | None => False
          end
      | None => match get m' a with
              | Some _ => False
              | None => True
              end
      end).
      apply H.
    clear H.
    rewrite H0 in H1.
    destruct (get m' a).
      subst.
      trivial.
    destruct H1.
  intros.
  assert (match get m a with
      | Some b1 =>
          match get m' a with
          | Some b2 => b1 = b2
          | None => False
          end
      | None => match get m' a with
              | Some _ => False
              | None => True
              end
      end).
    apply H.
  rewrite H0 in H1.
  destruct (get m a).
    subst;trivial.
  destruct H1.
Qed.

Lemma join_emp_eq :
  forall m m',
  join emp m m' -> m = m'.
Proof.
  intros.
  apply extensionality.
  intros.
  unfold join in H.
  simpl in H.
  assert (H' := H a).
  clear H.
  destruct_get; subst; trivial. 
  contradiction.
  contradiction.
Qed.

(* a strange lemma *)
Lemma sub_exists_join :
  forall m1 m,
    sub m1 m ->
    exists m2, join m1 m2 m.
Proof.
  unfold sub, lookup, join.
  intros m1 m H.
  exists (minus m m1).
  intro a.
  rewrite minus_sem.
  substH H with (H a).
  destruct (get m1 a); destruct (get m a). 
    substH H with (H b).
    injection H; trivial.
    intros; subst; trivial.
    substH H with (H b).
    discriminate H; trivial.
    trivial.
  trivial.
Qed.

Lemma join_sub_minus : forall m m1,
    sub m1 m
    -> join m1 (minus m m1) m.
Proof.
  unfold sub, lookup.
  intros.
  unfold join.
  intro.
  rewrite minus_sem.
  assert (H0 := H a).
  destruct_get; trivial.
  assert (H1 := H0 b). 
  injection H1; trivial.
  intro; subst; trivial.
  assert (H1 := H0 b).
  discriminate H1; trivial.
Qed.

Lemma join_sub_sub : forall m1 m2 m m',
  join m1 m2 m
  -> sub m1 m'
  -> sub m2 m'
  -> sub m m'.
Proof.
  intros.
  unfold sub, lookup in * .
  intros.
  substH H0 with (H0 a b).
  substH H1 with (H1 a b).
  substH H with (H a).
  destruct_get; (try contradiction); trivial.
  apply H0; trivial.
  inversion H2; subst; trivial.
  inversion H2; subst; auto.
  inversion H2; subst; auto.
  inversion H2; subst; auto.
  inversion H2.
Qed.

(*************************************************)
(**                                              *)
(** * join3 lemmas                               *)
(**                                              *)
(*************************************************)

Lemma join_join_join3 : forall m1 m2 m3 m12 m,
  join m1 m2 m12
  -> join m12 m3 m
  -> join3 m1 m2 m3 m.
Proof.
  unfold join3; intros.
  substH H with (H a).
  substH H0 with (H0 a).
  destruct_get; (try discriminate); (try contradiction); trivial.
  subst; trivial.
  subst; trivial.
Qed.

Lemma join3_join_join : forall m1 m2 m3 m23 m,
  join3 m1 m2 m3 m
  -> join m1 m23 m
  -> join m2 m3 m23.
Proof.
  intros.
  intro.
  substH H with (H a).
  substH H0 with (H0 a).
  destruct_get; (try discriminate); (try contradiction); trivial.
  subst; trivial.
  subst; trivial.
Qed.

Lemma join3_comm_213 : forall m1 m2 m3 m,
  join3 m1 m2 m3 m
  -> join3 m2 m1 m3 m.
Proof.
  intros.
  intro.
  substH H with (H a).
  destruct_get; (try discriminate); (try contradiction); trivial.
Qed.

Lemma join3_comm_312 : forall m1 m2 m3 m,
  join3 m1 m2 m3 m
  -> join3 m3 m1 m2 m.
Proof.
  intros.
  intro.
  substH H with (H a).
  destruct_get; (try discriminate); (try contradiction); trivial.
Qed.

Lemma join3_comm_231 : forall m1 m2 m3 m,
  join3 m1 m2 m3 m
  -> join3 m2 m3 m1 m.
Proof.
  intros.
  intro.
  substH H with (H a).
  destruct_get; (try discriminate); (try contradiction); trivial.
Qed.

Lemma join3_comm_132 : forall m1 m2 m3 m,
  join3 m1 m2 m3 m
  -> join3 m1 m3 m2 m.
Proof.
  intros.
  intro.
  substH H with (H a).
  destruct_get; (try discriminate); (try contradiction); trivial.
Qed.

Lemma join3_2join : forall m1 m2 m3 m,
  join3 m1 m2 m3 m
  -> exists m12,
      join m1 m2 m12
      /\ join m12 m3 m.
Proof.
  intros.
  exists (merge m1 m2).
  split.
    apply join_merge_disj.
    intro.
    substH H with (H a).
    destruct_get; (try discriminate); (try contradiction); trivial.
  intro.
  substH H with (H a).
  rewrite_get.
  destruct_get; (try discriminate); (try contradiction); trivial.
Qed.

(***********************************************************)
(**                                                        *)
(**    Tactics                                             *)
(**                                                        *)
(***********************************************************)

(* Ltac simplgs :=  *)
(*   match goal with *)
(*     | [ |- context [(get (sig ?a ?b) ?a)] ] => *)
(*       rewrite (get_sig a b); simplgs *)

(*     | [ H : context [(get (sig ?a ?b) ?a)] |- _ ] => *)
(*       rewrite (get_sig a b) in H; simplgs *)

(*     | [ |- context [(get (set ?m ?a ?b) ?a)] ] => *)
(*       rewrite (set_a_get_a m a b); simplgs *)

(*     | [ H : context [(get (set ?m ?a ?b) ?a)] |- _ ] => *)
(*       rewrite (set_a_get_a m a b) in H; simplgs *)

(*     | [ H : ?a <> ?a' *)
(*       |- context [(get (set ?m ?a ?b) ?a')] ] => *)
(*       rewrite (@set_a_get_a' m a a' b H); simplgs *)

(*     | [ H : ?a <> ?a', *)
(*       H0 : context [(get (set ?m ?a ?b) ?a')] |- _ ] => *)
(*       rewrite (@set_a_get_a' m a a' b H) in H0; simplgs *)

(*     | [ H : ?a' <> ?a *)
(*       |- context [(get (set ?m ?a ?b) ?a')] ] => *)
(*       rewrite (@set_a_get_a' m a a' b (sym_not_eq H)); simplgs *)

(*     | [ H : ?a' <> ?a, *)
(*       H0 : context [(get (set ?m ?a ?b) ?a')] |- _] => *)
(*       rewrite (@set_a_get_a' m a a' b (sym_not_eq H)) in H0; simplgs *)

(*     | [ |- context [(get (set ?m ?a ?b) ?a')] ] => *)
(*       rewrite (@set_a_get_a' m a a' b); simplgs *)

(* (*     | [ |- context [(lookup (set ?m ?a ?b) ?a' ?b')] ] => *) *)
(* (*       apply get_lookup;  *) *)
(* (*         rewrite (@set_a_get_a' m a a' b); simplgs *) *)

(*     | _ => idtac *)
(*   end. *)

Ltac unfoldlookup H :=
  unfold lookup in H.

(* Fixpoint upd (m : map) (a : A) (b : B) {struct m} : option map := *)
(*   match m return option map with *)
(*       | nil => None *)
(*       | (a', b') :: m' => *)
(*         match beq a a' with *)
(*           | true => Some ((a, b) :: m') *)
(*           | false =>  *)
(*               let m'' := (upd m' a b) in *)
(*                 match m'' with  *)
(*                   | None => None *)
(*                   | Some m' => Some ((a', b') :: m') *)
(*                 end *)
(*         end *)
(*   end. *)

(* Lemma upd_sem : forall m a b, *)
(*   upd m a b = *)
(*   match get m a with  *)
(*     | Some _ => Some (set m a b) *)
(*     | None => None *)
(*   end. *)
(* Proof. *)
(*   intros m a b. *)
(*   induction m as [ | [a' b'] m]; simpl; trivial. *)
(*   rewrite IHm. *)
(*   beq_case_tac a a'; beq simpl; trivial. *)
(*   destruct (get m a); trivial. *)
(* Qed. *)

(* Lemma get_a_upd_a : forall (m : map) (a : A) (b b' : B), *)
(*   get m a = Some b *)
(*   -> upd m a b' = Some (set m a b'). *)
(* Proof. *)
(*   intros. *)
(*   assert (H0 := upd_sem m a b'). *)
(*   destruct (get_dec m a). *)
(*   assumption. *)
(*   rewrite e in H. *)
(*   discriminate. *)
(* Qed. *)

(* Lemma upd_a_get_a' : forall (m m' : map) (a a' : A) (b : B), *)
(*   a <> a' *)
(*   -> upd m a b = Some m' *)
(*   -> get m' a' = get m a'. *)
(* Proof. *)
(*   intros m m' a a' b H H0. *)
(*   assert (H1 := upd_sem m a b). *)
(*   destruct (get_dec m a). *)
(*   rewrite H0 in H1. *)
(*   injection H1; intro He; subst m'. *)
(*   rewrite_get; trivial. *)
(*   rewrite H0 in H1; discriminate. *)
(* Qed. *)

(* Lemma upd_lookup : forall (m m' : map) (a : A) (b : B), *)
(*   upd m a b = Some m' *)
(*   -> lookup m' a b. *)
(* Proof. *)
(*   unfold lookup. *)
(*   intros. *)
(*   rewrite upd_sem in H. *)
(*   destruct get_dec. *)
(*   injection H. *)
(*   intros; subst. *)
(*   rewrite_get. *)
(*   trivial. *)
(*   discriminate. *)
(* Qed. *)


(*------------------added by zhanghui ---------------------*)
Lemma join_index_beq_false : forall m1 m2 m3 a b x y,
  join m1 m2 m3 -> get m1 a = Some x -> get m2 b = Some y -> beq a b = false.
Proof.
  intros.
  destruct (beq a b) eqn : eq1.
  apply beq_true_eq in eq1; subst.
  unfold join in H; pose proof H b; clear H.
  rewrite H1 in H2; rewrite H0 in H2.
  inversion H2.
  auto.
Qed.

Lemma join_sig_get : forall a x m1 m2,
  join (sig a x) m1 m2 -> get m2 a = Some x.
Proof.
  intros.
  unfold join in H; pose proof H a; clear H.
  rewrite get_sig_some in H0.
  destruct (get m1 a); try inversion H0.
  destruct (get m2 a); try inversion H0.
  auto.
Qed.


Definition joinsig x v m1 m2 := join (sig x v) m1 m2.

Lemma  join_joinsig_get : forall v'24 v'25 v'16 x8 x13 x12 ,
              join v'24 v'25 v'16 -> joinsig x8 x13 x12 v'25 -> 
             get v'16 x8 = Some x13.
Proof.
  intros.
  unfold joinsig in H0.
  unfold join in *.
  pose proof H x8; clear H.
  pose proof H0 x8; clear H0.
  rewrite get_sig_some in H.
  destruct (get v'24 x8);
  destruct (get v'25 x8);
  destruct (get v'16 x8);
  destruct (get x12 x8);
  try (inversion H1);
  try (inversion H).
  subst; auto.
Qed.


Lemma joinsig_set : 
    forall x8 x13 x12 v'25 v,
      joinsig x8 x13 x12 v'25 ->  
      joinsig x8 v x12 (set v'25 x8 v).
Proof.
  intros.
  unfold joinsig in *.
  unfold join in *.
  intro.
  pose proof H a; clear H.
  destruct (beq x8 a) eqn : eq1.
  apply beq_true_eq in eq1; subst.
  rewrite get_sig_some.
  rewrite set_a_get_a.
  rewrite get_sig_some in H0.
  destruct (get x12 a);
  destruct (get v'25 a); auto.
  apply eq_beq_true; auto.

  rewrite get_sig_none; auto.
  rewrite set_a_get_a'; auto.
  rewrite get_sig_none in H0.
  auto.
  apply beq_false_neq in eq1; auto.
  apply beq_false_neq in eq1; auto.
Qed.

Lemma  joinsig_set_set : forall x8 x13 x12  v'24 v'25 v'16 v,
 joinsig x8 x13 x12 v'25 ->
   join v'24 v'25 v'16 -> 
   join v'24 (set v'25 x8 v) (set v'16 x8 v).
Proof.
  intros.
  unfold joinsig in *.
  unfold join in *.
  intro.
  pose proof H a; clear H.
  pose proof H0 a; clear H0.
  destruct (beq x8 a) eqn : eq1. 
  pose proof beq_true_eq eq1; subst.
  rewrite set_a_get_a; auto.
  rewrite set_a_get_a; auto.
  rewrite get_sig_some in H1; auto.
  destruct (get v'24 a);
  destruct (get v'25 a);
  destruct (get x12 a); auto.

  rewrite set_a_get_a'; auto.
  rewrite set_a_get_a'; auto.
Qed.


(*------some other extension of MapLib lemmas, added by zhanghui------*)
Lemma disj_set_disj_1 : forall M1 M2 x v v',
  disj M1 M2 -> get M1 x = Some v -> disj (set M1 x v') M2.
Proof.
  intros.
  unfold disj in *.
  intro.
  pose proof H a; clear H.
  destruct (beq x a) eqn : eq1.
  pose proof beq_true_eq eq1.
  rewrite H; rewrite H in eq1; rewrite H in H0.
  rewrite set_a_get_a; auto.
  rewrite H0 in H1; auto.
  rewrite set_a_get_a'; auto.
Qed.

Lemma disj_set_disj_2 : forall M1 M2 x v v',
  disj M1 M2 -> get M2 x = Some v -> disj M1 (set M2 x v').
Proof.
  intros.
  apply disj_sym in H.
  apply disj_sym.
  eapply disj_set_disj_1; eauto.
Qed.

Lemma index_beq_false_1 : forall M a b v,
  get M a = Some v -> get M b = None -> beq a b = false.
Proof.
  intros.
  destruct (beq a b) eqn : eq1.
  apply beq_true_eq in eq1; rewrite eq1 in H.
  rewrite H in H0.
  inversion H0.
  auto.
Qed.

Lemma merge_set_eq_1 : forall M1 M2 x v,
  merge (set M1 x v) M2 = set (merge M1 M2) x v.
Proof.
  intros.
  apply extensionality.
  intros.
  rewrite merge_sem.
  destruct (beq x a) eqn : eq1.
  pose proof beq_true_eq eq1; rewrite H; rewrite H in eq1.
  rewrite set_a_get_a; auto.
  rewrite set_a_get_a; auto.
  destruct (get M2 a); auto.
  rewrite set_a_get_a'; auto.
  rewrite set_a_get_a'; auto.
  rewrite merge_sem; auto.
Qed.

Lemma merge_set_eq_2 : forall M1 M2 x v v', 
  disj M1 M2 -> get M2 x = Some v ->
  merge M1 (set M2 x v') = set (merge M1 M2) x v'.
Proof.
  intros.
  apply extensionality.
  intros.
  rewrite merge_sem.
  unfold disj in H. pose proof H a; clear H.
  destruct (beq x a) eqn : eq1.
  pose proof beq_true_eq eq1; rewrite H; rewrite H in eq1; rewrite H in H0.
  rewrite set_a_get_a; auto.
  rewrite set_a_get_a; auto.
  rewrite H0 in H1.
  destruct (get M1 a) eqn : eq2; auto.
  inversion H1.
  rewrite set_a_get_a'; auto.
  rewrite set_a_get_a'; auto.
  rewrite merge_sem; auto.
Qed.

Lemma join_shift_l : forall m1 m2 m3 mx a v,
  join m1 m2 m3 -> joinsig a v mx m2 -> join (merge m1 (sig a v)) mx m3.
Proof.
  intros.
  unfold join; intros.
  destruct (beq a a0) eqn : eqx.
  rewrite merge_sem.
  unfold join in H; pose proof H a0; clear H.
  unfold joinsig in H0; unfold join in H0; pose proof H0 a; clear H0.
  rewrite get_sig_some in H.
  pose proof beq_true_eq eqx; subst.
  rewrite get_sig_some.
  destruct (get m1 a0);
  destruct (get m2 a0);
  destruct (get m3 a0);  
  destruct (get mx a0); try inversion H1; try inversion H; subst; auto.
  rewrite merge_sem.
  rewrite get_sig_none.
  pose proof H a0.
  pose proof H0 a0.
  rewrite get_sig_none in H2.
  
  destruct (get m1 a0) eqn: eq1;
  destruct (get m2 a0) eqn: eq2;
  destruct (get m3 a0) eqn: eq3;   
  destruct (get m2 a)  eqn: eq4;
  destruct (get mx a0) eqn: eq5;
  destruct (get mx a)  eqn: eq6;
  try inversion H1; try inversion H; subst; auto; subst.
  apply beq_false_neq in eqx; auto.
  apply beq_false_neq in eqx; auto.
Qed.

Lemma joinsig_merge_sig : forall a1 v1 m1 m2 a2 v2,
  joinsig a1 v1 m1 m2 -> a1 <> a2 ->
  joinsig a1 v1 (merge m1 (sig a2 v2)) (merge m2 (sig a2 v2)).
Proof.
  intros.
  unfold joinsig.
  unfold join.
  intros.
  destruct (beq a1 a) eqn: eq1.
  pose proof beq_true_eq eq1; subst.
  rewrite get_sig_some.
  rewrite merge_sem.
  rewrite get_sig_none; auto.
  rewrite merge_sem.
  rewrite get_sig_none; auto.
  pose proof H a.
  rewrite get_sig_some in H1.
  destruct (get m1 a); try inversion H1.
  destruct (get m2 a); try inversion H1.
  auto.
  pose proof beq_false_neq eq1.
  rewrite get_sig_none; auto.
  rewrite merge_sem.
  rewrite merge_sem.
  pose proof H a.
  rewrite get_sig_none in H2; auto.
  destruct (get m1 a) eqn: eq2;
  destruct (get m2 a) eqn: eq3; try inversion H2.
  destruct (get (sig a2 v2) a); auto.
  destruct (get (sig a2 v2) a); auto.
Qed.
  
(*--------------added the definition eqdom, by zhanghui--------------------*)
Definition eqdom M1 M2 := forall x, indom M1 x <-> indom M2 x.

Lemma eqdom_merge_set : forall O Of x v v',
  get O x = Some v -> eqdom (merge O Of) (merge (set O x v') Of).
Proof.
  intros.
  unfold eqdom.
  unfold indom in *.
  intro; split; intros.
  destruct H0.
  rewrite merge_sem.
  destruct (beq x x0) eqn :eq1.
  pose proof beq_true_eq eq1; subst.
  rewrite set_a_get_a; auto.
  exists v'; destruct (get Of x0); auto.
  rewrite set_a_get_a'; auto.
  rewrite merge_sem in H0.
  exists x1; auto.
  destruct (beq x x0) eqn :eq1.
  pose proof beq_true_eq eq1; subst.
  destruct H0.
  rewrite merge_sem in H0.
  rewrite set_a_get_a in H0; auto.
  rewrite merge_sem.
  rewrite H.
  exists v; destruct (get Of x0); auto.
  rewrite merge_sem in H0.
  rewrite set_a_get_a' in H0; auto.
  rewrite merge_sem.
  destruct H0.
  eauto.
Qed.

(*--------------added some lemma of join, disj, memq, sub by lzh ----------*)

Lemma option2val:
  forall T (x y: T),
    Some x = Some y -> x = y.
Proof.
  intros T x y.
  intros F1.
  inversion F1.
  trivial.
Qed.

Lemma option2false:
  forall T (x : T),
    None = Some x -> False.
Proof.
  intros T x.
  intros F1.
  inversion F1.
Qed.

Lemma disj_comm:
  forall ma mb,
    disj ma mb ->
    disj mb ma.
Proof.
  apply disj_sym.
Qed.

Ltac find_join_eql :=
  match goal with
    | H: join ?ma _ _ |-
         join ?ma ?mb ?mab =>
        eapply H

    | H: join _ ?ma _ |-
         join ?ma ?mb ?mab =>
        apply join_comm; eapply H

    | H: join ?mb _ _ |-
         join ?ma ?mb ?mab =>
        apply join_comm; eapply H

    | H: join _ ?mb _ |-
         join ?ma ?mb ?mab =>
        eapply H
    
    | H: join _ _ ?mab |-
         join ?ma ?mb ?mab =>
        eapply H
  end.

Lemma join_meq_sub_1st:
  forall m1 m2 m3 m12,
    join m1 m2 m12 ->
    meq m1 m3 ->
    join m3 m2 m12.
Proof.
  intros m1 m2 m3 m12.
  unfold join, meq, sub, lookup.
  intros H1 H2.
  inversion H2 as [H21 H22].
  intros a.
  rewrite_get;
    substH H1 with (H1 a);
    substH H21 with (H21 a);
    substH H22 with (H22 a);
    destruct_get; solve_sn; subst.
  apply option2val.
  apply H21.
  trivial.
  apply option2false with (x:=b); apply H22; trivial.
  apply option2false with (x:=b); apply H22; trivial.
  apply option2false with (x:=b0); apply H21; trivial.
Qed.  

Lemma disj_trans_sub:
  forall m1 m2 m3,
    sub m1 m2 ->
    disj m3 m2 ->
    disj m3 m1.
Proof.
  intros m1 m2 m3.
  unfold sub, disj, lookup.
  intros.
  substH H0 with (H0 a).
  substH H with (H a).
  rewrite_get; destruct_get; solve_sn.
  assert (None = Some b).
    apply H.
    reflexivity.
  inversion H1.
Qed.

Lemma join_assoc:
  forall ma mb mc mab mbc mabc,
    join ma mb mab ->
    join mab mc mabc ->
    join mb mc mbc ->
    join ma mbc mabc.
Proof.
  intros ma mb mc mab mbc mabc.
  unfold join.
  intros H1 H2 H3.
  intros a; 
    rewrite_get;
    substH H1 with (H1 a);
    substH H2 with (H2 a);
    substH H3 with (H3 a);
    destruct_get; solve_sn.
  rewrite <- H3; trivial.
  subst; trivial.
  subst; trivial.
  subst; trivial.
  subst; trivial.
Qed.


Lemma join_assoc_spec_1:
  forall ma mb mc mab mabc,
    join ma mb mab ->
    join mc mab mabc ->
    exists mac, join mc ma mac /\
                join mac mb mabc.
Proof.
  intros ma mb mc mab mabc.
  unfold join.
  intros H1 H2.
  exists (merge mc ma).
  split; intros a;
    rewrite_get;
    substH H1 with (H1 a);
    substH H2 with (H2 a);
    destruct_get; solve_sn; 
    subst; trivial.
Qed.

Lemma my_joinsig_join_set:
  forall x1 v1 v2 ma mb mb' mab,
    joinsig x1 v1 mb' mb ->
    join ma mb mab ->
    join ma (set mb x1 v2) (set mab x1 v2).
Proof.
  intros x1 v1 v2 ma mb mb' mab.
  intros F1 F2.
  apply joinsig_set_set with (x13:=v1)(x12:=mb').
  unfold joinsig; trivial.
  trivial.
Qed.

Lemma join_join_disj_r:
  forall ma mb mab mc mabc,
    join ma mb mab ->
    join mab mc mabc ->
    disj mb mc.
Proof.
  intros ma mb mab mc mabc.
  intros F1 F2.
  apply join_sub_r in F1.
  apply join_disj_meq in F2.
  inversion F2.
  apply disj_sym.
  apply disj_trans_sub with (m2:=mab).
  trivial.
  apply disj_sym. trivial.
Qed.


Lemma join_join_disj_l:
  forall ma mb mab mc mabc,
    join ma mb mab ->
    join mab mc mabc ->
    disj ma mc.
Proof.
  intros ma mb mab mc mabc.
  intros F1 F2.
  eapply join_join_disj_r; find_join_eql. 
Qed.
  
Lemma join_whole2part:
  forall ma mb mab mc mabc,
    join ma mb mab ->
    join mab mc mabc ->
    join mb mc (merge mb mc).
Proof.
  intros ma mb mab mc mabc.
  intros F1 F2.
  apply join_merge_disj.
  eapply join_join_disj_r.
  eapply F1.
  eapply F2.
Qed.


Lemma my_join_sig_abc:
  forall ma mb mc mc' x1 v1 v2 mbc mabc,
    join mb mc mbc ->
    join ma mbc mabc ->
    joinsig x1 v1 mc' mc ->
    join ma (set mbc x1 v2)
            (set mabc x1 v2).
Proof.
  intros ma mb mc mc' x1 v1 v2 mbc mabc.
  intros F1 F2 F3.
  apply my_joinsig_join_set with (v1:=v1)(mb':=merge mc' mb).
  unfold joinsig in *.
  apply join_assoc with (mb:=mc')(mc:=mb)(mab:=mc).
  trivial.
  apply join_comm; trivial.
  eapply join_whole2part.
  eapply F3.
  apply join_comm; eapply F1.
  trivial.
Qed.

Lemma my_joinsig_set:
  forall x1 v1 v2 m' m,
    joinsig x1 v1 m' m ->
    joinsig x1 v2 m' (set m x1 v2).
Proof.
  intros.
  eapply joinsig_set.
  eapply H.
Qed.
Lemma join_get_r:
  forall ma mb mab x1 v1,
    join ma mb mab ->
    get mb x1 = Some v1 ->
    get mab x1 = Some v1.
Proof.
  intros ma mb mab x1 v1 F1 F2.
  eapply get_sub_get.
  eapply F2.
  eapply join_sub_r.
  eapply F1.
Qed.

Lemma join_get_l:
  forall ma mb mab x1 v1,
    join ma mb mab ->
    get ma x1 = Some v1 ->
    get mab x1 = Some v1.
Proof.
  intros ma mb mab x1 v1.
  intros F1 F2.
  eapply join_get_r.
  eapply join_comm; eapply F1.
  apply F2.
Qed.

Lemma disj_get_neq:
  forall ma mb x1 v1 x2 v2,
    disj ma mb ->
    get ma x1 = Some v1 ->
    get mb x2 = Some v2 ->
    x1 <> x2.
Proof.
  intros ma mb x1 v1 x2 v2.
  unfold disj.
  intros F1 F2 F3.
  substH F1 with (F1 x1).
  rewrite F2 in F1.
  destruct (get mb x1) eqn:H1.
  inversion F1.
  unfold not.
  intros F4.
  subst.
  rewrite H1 in F3.
  inversion F3.
Qed.

Lemma my_join_disj:
  forall ma mb mab,
    join ma mb mab ->
    disj ma mb.
Proof.
  intros ma mb mab F1.
  apply join_disj_meq in F1.
  intuition.
Qed.

Lemma join_meq_eql:
  forall ma mb mab,
    join ma mb mab ->
    mab = merge ma mb.
Proof.
  intros ma mb mab F1.
  apply join_disj_meq in F1.
  apply meq_eq.
  apply meq_sym.
  intuition.
Qed.


(**** lzh-begin: join tactics *)
Ltac solve_get :=
  match goal with
    | H: get ?m ?x = _ |-
         get ?m ?x = _ =>
       eapply H
    | H: join (sig ?x _) _ ?m |-
         get ?m ?x = Some _ =>
        eapply join_sig_get;
        eapply H
    | |- get (sig ?x _) ?x = Some _ =>
        eapply get_sig_some 
    | H: join ?ma ?mb ?mab |-
         get ?mab ?x = Some ?v =>
         match goal with
           | H': get ?ma ?x = Some ?v |- _ =>
               eapply join_get_l; [eapply H | eapply H']
           | H': get ?mb ?x = Some ?v |- _ =>
               eapply join_get_r; [eapply H | eapply H']
         end
  end.

Ltac solve_sub :=
  match goal with
    | H: join ?ma ?mb ?mab |-
         sub ?ma ?mab =>
        eapply join_sub_l; eapply H
    | H: join ?ma ?mb ?mab |-
         sub ?mb ?mab =>
        eapply join_sub_r; eapply H
  end.

Ltac solve_disj :=
  match goal with
    | H: disj ?ma ?mb |-
         disj ?ma ?mb =>
        apply H
    | H: disj ?ma ?mb |-
         disj ?mb ?ma =>
        apply disj_sym; apply H
    | H: join ?ma ?mb ?mab |-
         disj ?ma ?mb =>
        eapply my_join_disj; eapply H
    | H: join ?ma ?mb ?mab |-
         disj ?mb ?ma =>
        eapply disj_sym; eapply my_join_disj; eapply H
  end.

Ltac solve_join :=
  match goal with
    | H: join _ _ ?mab |-
         join _ _ ?mab =>
        first [eapply H | apply join_comm; eapply H | idtac]
  end.

Ltac solve_map :=
  match goal with
    | |- get _ _ = _ =>
        try solve_get
    | |- sub _ _ =>
        try solve_sub
    | |- disj _ _ =>
        try solve_disj
    | |- join _ _ _ =>
        try solve_join
    | _ => idtac
  end.

(**** lzh-end: join tactics *)

Lemma join_get_get_neq:
  forall ma mb mab x1 v1 x2 v2,
    join ma mb mab ->
    get ma x1 = Some v1 ->
    get mb x2 = Some v2 ->
    x1 <> x2.
Proof.
  intros ma mb mab x1 v1 x2 v2.
  intros F1.
  apply disj_get_neq.
  eapply my_join_disj.
  find_join_eql.
Qed.

(******************************************************************************)
(** using to instant MapClass **)
Definition usePerm := false.
Definition isRw := fun (v:B) => true.
Definition flip := fun (v:B) => v.
Definition sameV := fun (v1 v2:B) => v1 = v2.

Lemma map_dec_a:
  forall (t1 t2: A), {t1 = t2} + {t1 <> t2}.
  exact eq_dec.
Qed.  

(** * join **)
Lemma map_join_emp:
  forall x, join x emp x.
  intros.
  eapply join_emp; auto.
Qed.

Require Import LibTactics.
Lemma map_join_pos:
  forall x y,
    join x y emp ->
    x = emp /\ y = emp.
  intros.
  generalize (join_sub_l H); intro Ha.
  generalize (join_sub_r H); intro Hb.
  split.
  eapply extensionality.
  intros.
  rewrite emp_sem.
  assert  ({(exists b, get x a = Some b)} + {get x a = None}).
  apply get_dec.
  destruct H0; auto.
  destruct e.
  generalize (get_sub_get H0 Ha); intro Hx.
  rewrite emp_sem in Hx.
  tryfalse.
  eapply extensionality.
  intros.
  rewrite  emp_sem.
  assert  ({(exists b, get y a = Some b)} + {get y a = None}).
  apply get_dec.
  destruct H0; auto.
  destruct e.
  lets Hx : get_sub_get  H0 Hb.
  rewrite emp_sem in Hx.
  tryfalse.
Qed.

Lemma map_join_comm:
  forall x y z,
    join x y z ->
    join y x z.
Proof.
  intros.
  eapply join_comm; eauto.
Qed.

Lemma map_join_assoc:
  forall a b mab c mabc,
    join a b mab ->
    join mab c mabc ->
        exists mbc,
          join a mbc mabc /\
          join b c mbc.
Proof.
  intros.
  lets Hx: join_assoc_l H H0.
  destruct Hx.
  destruct H1.
  eexists x.
  split; auto.
Qed.


Lemma map_join_cancel:
  forall a b b' c,
    join a b c ->
    join a b' c ->
    b = b'.
  eapply join_unique_r.
Qed.

Lemma map_join_deter:
  forall a b c c',
    join a b c ->
    join a b c' ->
    c = c'.
  eapply join_unique.
Qed.

(** * saveV and flip: Permission specific, in this file, trivially true **)
Lemma map_sv_ref:
  forall v, usePerm = true -> sameV v v.
  intros; tryfalse.
Qed.  
       
Lemma map_sv_comm:
  forall v v',
    usePerm = true ->
    sameV v v' ->
    sameV v' v.
  intros; tryfalse.
Qed.

Lemma map_sv_assoc:
  forall v1 v2 v3,
    usePerm = true ->
    sameV v1 v2 ->
    sameV v2 v3 ->
    sameV v1 v3.
  intros; tryfalse.
Qed.

Lemma map_perm_eql:
  forall v1 v2,
    usePerm = true ->
    sameV v1 v2 ->
    isRw v1 = isRw v2 ->
    v1 = v2.
  intros; tryfalse.
Qed.
 
Lemma map_flip_isRw:
  forall v,
    usePerm = true ->
    isRw (flip v) = negb (isRw v).
  intros; tryfalse.
Qed.

Lemma map_flip_sv:
  forall v,
    usePerm = true ->
    sameV v (flip v).
  intros; tryfalse.
Qed.

(** * get **)
(** ** general **)
Lemma map_emp_get:
  forall t, get emp t = None.
Proof.
  intros.
  apply emp_sem.
Qed.  
  
Lemma map_eql:
  forall x y,
    (forall t, get x t = get y t) ->
    x = y.
Proof.
  intros.
  apply extensionality.
  auto.
Qed.

Lemma map_disjoint':
  forall x y,
    (forall t, get x t = None \/
          get y t = None \/
          (exists v,
              usePerm = true /\
              get x t = Some v /\
              get y t = Some v /\
              isRw v = false)) ->
    disj x y.
Proof.
  intros.
  apply indom_disj.
  intros t.
  unfold indom.
  split.
  lets H': H t.
  clear H.
  destruct H'.
  intros.
  destruct H0.
  tryfalse.
  destruct H.
  intros.
  unfold not.
  intros.
  destruct H1.
  tryfalse.
  destruct H.
  destruct H.
  unfold usePerm in *.
  tryfalse.
  intros.
  lets H': H t.
  clear H.
  destruct H'.
  unfold not.
  intros.
  destruct H1.
  tryfalse.
  destruct H.
  destruct H0.
  tryfalse.
  destruct H.
  destruct H.
  unfold usePerm in *.
  tryfalse.
Qed.  
  
Lemma map_disjoint:
  forall x y,
    (forall t, get x t = None \/
          get y t = None \/
          (exists v,
              usePerm = true /\
              get x t = Some v /\
              get y t = Some v /\
              isRw v = false)) ->
    exists z, join x y z.
Proof.
  intros.
  exists (merge x y).
  apply join_merge_disj.
  eapply map_disjoint'.
  auto.
Qed.  

Lemma map_get_unique:
  forall x t v v',
    get x t = Some v ->
    get x t = Some v' ->
    v = v'.
Proof.
  intros.
  rewrite H in H0.
  inverts H0.
  auto.
Qed.

Lemma map_get_sig:
  forall t v,
    get (sig t v) t = Some v.
Proof.
  intros. 
  rewrite get_sig.
  induction (eq_dec t t ) ; tryfalse; auto.
Qed.

Lemma map_get_sig':
  forall t t' v,
    t <> t' ->
    get (sig t v) t' = None.
Proof.
  intros.
  rewrite get_sig.
  induction (eq_dec t t' ) ; tryfalse; split; inverts H; auto.
Qed.

Lemma map_get_set:
  forall x t v,
    get (set x t v) t = Some v.
Proof.
  intros.
  apply set_a_get_a.
  apply beq_refl.
Qed.

Lemma map_get_set':
  forall x t t' v,
    t <> t' ->
    get (set x t v) t' = get x t'. 
Proof.
  intros.
  apply set_a_get_a'.
  apply neq_beq_false.
  auto.
Qed.

Lemma map_join_get_none:
  forall x y z t,
    join x y z ->
    get x t = None ->
    get z t = get y t.
Proof.
  intros.
  destruct (get y t) eqn: F.
  eapply join_get_get_r; eauto.
  unfold join in *.
  generalize (H t); clear H; intro H.
  rewrite H0 in *.
  rewrite F in *.
  destruct (get z t).
  inversion H.
  auto.
Qed.

(** ** no permission **)
Lemma map_join_get_some:
  forall x y z t v1 v2,
    usePerm = false ->
    join x y z ->
    get x t = Some v1 ->
    get y t = Some v2 ->
    False.
Proof.
  intros.
  unfold join in *.
  clear H. rename H0 into H.
  generalize (H t); clear H; intro H.
  rewrite H1 in *.
  rewrite H2 in *.
  tryfalse.
Qed.

(** ** use permission **)
Lemma map_join_getp_some:
  forall x y z t v1 v2 v',
    usePerm = true ->
    join x y z ->
    get x t = Some v1 ->
    get y t = Some v2 ->
    v' = flip v1 ->
    v1 = v2 /\ isRw v1 = false /\ get z t = Some v'.
  intros; tryfalse.
Qed.

(** * set **)
(** ** general **)
Lemma map_set_emp:
  forall t v,
    set emp t v = sig t v. 
  exact set_emp_sig.
Qed.

Lemma map_set_sig:
  forall t v v',
    set (sig t v) t v' = sig t v'.
  exact set_sig.
Qed.

Lemma map_join_set_none:
  forall x y z t v',
    join x y z ->
    get y t = None ->
    join (set x t v') y (set z t v').
Proof.
  intros.
  destruct (get x t) eqn:F.
  eapply join_set_l.
  auto.
  unfold indom.
  exists b. auto.
  assert (get z t = None).
    unfold join in *.
    generalize (H t); clear H; intro H.
    rewrite H0 in *.
    rewrite F in *.
    destruct (get z t); tryfalse.
    auto.
  eapply join_set_nindom_l; eauto.
  unfold not.
  intro.
  apply indom_get in H2.
  destruct H2.
  rewrite H2 in H1.
  tryfalse.
Qed.

(** ** use permission **)
Lemma map_join_set_perm:
  forall x y z t v v',
    usePerm = true ->
    join x y z ->
    get x t = None ->
    get y t = Some v ->
    isRw v = false ->
    v' = flip v ->
    join (set x t v) y (set z t v').
  intros; tryfalse.
Qed.

(** * sig **)
(** ** general **)
Lemma map_join_get_sig:
  forall x t v,
    get x t = Some v ->
    exists x', join (sig t v) x' x.
Proof.
  intros.
  exists (minus x  (sig t v)).
  eapply join_sub_minus; eauto.
  eapply sub_sig; eauto.
Qed.

(** ** use permission **)
Lemma map_join_get_sig_perm:
  forall x t v v',
    usePerm = true ->
    get x t = Some v ->
    isRw v = true ->
    v' = flip v ->
    exists x1 x2, join (sig t v') x1 x /\ join (sig t v') x2 x1.
  intros; tryfalse.
Qed.
  
(** * merge **)
(* ** ac: Check map_dec_a. *)

Lemma map_merge_sem:
  (** def1 **)
  forall m1 m2 a,
    usePerm = false ->
    get (merge m1 m2) a 
    = match (get m1 a, get m2 a) with
        | (Some b1, Some b2) => Some b1
        | (Some b1, None) => Some b1
        | (None, Some b2) => Some b2
        | (None, None) => None
      end.
  intros.
  apply merge_sem; auto.
Qed.


Lemma map_join_merge:
  (** the scope of exists is very large, using parenthesis **)
  forall x y,
    (exists z, join x y z) ->
    join x y (merge x y).
Proof.
  intros.
  destruct H.
  assert (join x y x0) as Hxx by auto.
  apply join_disj_meq in H.
  destruct H.
  apply meq_eq in H0. 
  subst.
  auto.
Qed. 

  
Lemma map_merge_comm:
  forall x y,
    (exists z, join x y z) ->
    merge x y = merge y x.
Proof.
  intros.
  destruct H.
  apply join_disj_meq in H.
  destruct H.
  apply disj_compat in H.
  apply meq_merge_sym in H.
  apply meq_eq in H.
  auto.
Qed.

(** * minus **)
Lemma map_minus_sem:
  (** def1 **)
  forall m m1 a,
    usePerm = false ->
    get (minus m m1) a 
    = match (get m a, get m1 a) with
        | (Some b, Some b1) => None
        | (Some b1, None) => Some b1
        | (None, Some b2) => None
        | (None, None) => None
      end.
  intros.
  apply minus_sem; auto.
Qed.

Lemma map_join_minus:
  forall z x,
    (exists y, join x y z) ->
    join x (minus z x) z.
Proof.
  intros. 
  destruct H.
  eapply join_sub_minus.
  eapply join_sub_l.
  eauto.
Qed.

Definition del m a := minus m (sig a holder).

Lemma map_del_sem:
  forall m a t,
    get (del m a) t
    = match (map_dec_a a t) with
        | left _ => None
        | right _ => get m t
      end.
  intros.
  unfold del.
  rewrite minus_sem.
  destruct (map_dec_a a t); subst; tryfalse.
  rewrite map_get_sig.
  destruct (get m t); auto.
  rewrite map_get_sig'; auto.  
  destruct (get m t); auto.
Qed.

Definition same (v1 v2 :B) : bool := true. 

End MapFun.

Unset Implicit Arguments.
