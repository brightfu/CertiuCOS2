Require Import Coqlib.


Hint Extern 4 (~( _ = _ )) => discriminate.

Hint Extern 5 ({?X1 = ?X2} + {?X1 <> ?X2}) =>
                  generalize X1 X2; decide equality.


Module Type MapSpec.

Parameter domain : Set.
Parameter image : Type.
Parameter beq_Domain : forall (x y : domain), {x = y} + {x <> y}.

End MapSpec.

(* Partial Map *)

Module MapFun(Spec : MapSpec).

Set Implicit Arguments.
Definition A : Set := Spec.domain.
Definition B  := Spec.image.
Definition beq_A := Spec.beq_Domain.

(* partial map *)
Definition Map := A -> option B.

(* empty map *)
Definition emp : Map :=
  fun a : A => None.


(* map extension *)
Definition put : Map -> A -> B -> Map :=
  fun M a b =>
    fun x => if (beq_A x a) then (Some b) else M x.


Definition remove : Map -> A -> Map :=
  fun M a =>
    fun x => if (beq_A x a) then None else M x.


Definition maps_to : Map -> A -> B -> Prop :=
  fun M a b => M a = Some b.


Definition in_dom : A -> Map -> Prop :=
  fun a M => exists b : B, M a = Some b.


Definition not_in_dom : A -> Map -> Prop :=
  fun a M => M a = None.


(* map that has only one element in the domain *)
Definition sgltonM : Map -> A -> B -> Prop :=
  fun M a b => 
    maps_to M a b /\ (forall (x : A), x <> a -> not_in_dom x M).

Definition sig : A -> B -> Map :=
  fun a b => put emp a b.

Definition sub_dom : Map -> Map -> Prop :=
  fun M M' => forall (x : A), in_dom x M -> in_dom x M'.


Definition eqDom : Map -> Map -> Prop :=
  fun M M' => sub_dom M M' /\ sub_dom M' M.


Definition merge : Map -> Map -> Map :=
  fun M1 M2 =>
    fun x =>
      match M1 x with
        None => M2 x
      | _ => M1 x
      end.


Definition disjoint : Map -> Map -> Prop :=
  fun M1 M2 =>
    forall (x : A), not_in_dom x M1 \/ not_in_dom x M2.



Definition disjUnion : Map -> Map -> Map -> Prop :=
  fun M' M'' M => disjoint M' M'' /\ (M = merge M' M'').

Definition disjUnion3 : Map -> Map -> Map -> Map -> Prop :=
  fun M1 M2 M3 M => exists M12, disjUnion M1 M2 M12 /\ disjUnion M12 M3 M.

Definition subseteq : Map -> Map -> Prop :=
  fun M1 M2 =>
    forall (x : A), in_dom x M1 -> M1 x = M2 x.


Definition compat : Map -> Map -> Prop :=
  fun M1 M2 =>
    forall (x : A) (y : B), maps_to M1 x y -> not_in_dom x M2 \/ maps_to M2 x y.


(* extensional equality about Maps *)
Axiom extensionality : forall (A : Set) (B : Type) (f g : A -> B), (forall x : A, f x = g x) -> f = g.
(*
Definition extensional_eqMap := extensionality A (option B).
*)
Lemma eq_get : forall (M M' : Map) (x : A), M = M' -> M x = M' x.
Proof.
  intros; subst; trivial.
Qed.

(* ****************************** *)
(* properties about map extension *)
(* ****************************** *)

Lemma put_get_eq :
  forall (M : Map) (x: A) (y : B), (put M x y) x = Some y.
Proof.
intros.
unfold put.
case (beq_A x x).
auto.
intro.
assert (x=x). auto. contradiction.
Qed.

Lemma put_noninterfere:
  forall (M : Map) (x x' : A) (y : B), x <> x' -> (put M x y) x' = M x'.
Proof.
intros M x x' y x_neq.
unfold put.
case (beq_A x' x).
intro. assert (x = x'). symmetry. auto. contradiction.
auto.
Qed.

Hint Resolve put_get_eq put_noninterfere: PMap.

Lemma put_unique : 
  forall (M : Map) (x : A) (y y' : B),
    put M x y = put M x y'
    -> y = y'.
Proof.
  intros.
  assert (H': put M x y x = put M x y' x).
    rewrite H; trivial.
  rewrite put_get_eq in H'.
  rewrite put_get_eq in H'.
  injection H'; trivial.
Qed.
    
(* ****************************** *)
(*    properties about remove     *)
(* ****************************** *)
Lemma remove_shrinks_dom:
  forall (M : Map) (x : A),
    forall (y : A), not_in_dom y M -> not_in_dom y (remove M x).
Proof.
  intros.
  unfold not_in_dom.
  unfold remove.
  induction (beq_A y x).
  auto.
  unfold not_in_dom in H. auto.
Qed.

Lemma nid_remove:
  forall (M : Map) (x : A), not_in_dom x (remove M x).
Proof.
  intros M x.
  unfold remove.
  unfold not_in_dom.
  induction (beq_A x x). auto.
  assert (x = x); auto. contradiction.
Qed.

Hint Resolve remove_shrinks_dom nid_remove : PMap.

Lemma remove_nothing:
  forall (M : Map) (x : A), not_in_dom x M -> M = (remove M x).
Proof.
  intros.
  apply extensionality.
  intros.
  unfold remove.
  induction (beq_A x0 x).
  unfold not_in_dom in H.
  rewrite <- a in H. auto.
  auto.
Qed.

Lemma remove_cancel_put:
  forall (M : Map) (x : A) (y : B), remove (put M x y) x = remove M x.
Proof.
  intros.
  apply extensionality.
  intros.
  unfold remove.
  induction (beq_A x0 x).
  auto.
  unfold put.
  induction (beq_A x0 x).
  contradiction.
  auto.
Qed.

Lemma put_cancel_remove:
  forall (M : Map) (x : A) (y : B), put (remove M x) x y = put M x y.
Proof.
  intros M x y. 
  apply extensionality.
  intro x0.
  unfold put.
  unfold remove.
  induction (beq_A x0 x); auto.
Qed.

Lemma remove_ext_ext_remove:
  forall (M : Map) (x x' : A) (y : B), x <> x' -> remove (put M x y) x' = put (remove M x') x y.
Proof.
  intros.
  apply extensionality.
  intros.
  unfold put.
  unfold remove.
  induction (beq_A x0 x).
  induction (beq_A x0 x').
  rewrite a in a0. contradiction. auto.
  induction (beq_A x0 x'). auto. auto.
Qed.

Hint Resolve remove_nothing remove_cancel_put put_cancel_remove remove_ext_ext_remove : PMap.
  

(******************************************)
(* properties about in_dom and not_in_dom *)
(******************************************)

Lemma in_not_notin :
  forall (x : A) (M : Map), in_dom x M -> ~ (not_in_dom x M).
Proof.
  intros.
  intro.
  unfold in_dom in H. unfold not_in_dom in H0.
  inversion_clear H.
  rewrite H0 in H1. inversion_clear H1.
Qed.


Lemma notin_not_in:
  forall (x : A) (M : Map), not_in_dom x M -> ~ (in_dom x M).
Proof.
  intros.
  intro.
  unfold in_dom in H0. unfold not_in_dom in H.
  inversion_clear H0.
  rewrite H in H1. inversion_clear H1.
Qed.


Lemma not_in_notin:
  forall (x : A) (M : Map), ~ in_dom x M -> not_in_dom x M.
Proof.
  intros.
  unfold not_in_dom.
  unfold in_dom in H.
  induction (M x).
  assert (exists b : B, Some a = Some b). exists a; auto.
  contradiction.
  auto.
Qed.


Lemma not_notin_in:
  forall (x : A) (M : Map), ~ not_in_dom x M -> in_dom x M.
Proof.
  intros.
  unfold in_dom. unfold not_in_dom in H.
  induction (M x). exists a. auto. elim H. auto.
Qed.


Lemma in_or_notin:
  forall x M, in_dom x M \/ not_in_dom x M.
Proof.
  intros x M.
  unfold in_dom.
  unfold not_in_dom.
  elim (M x).
  left. exists a. auto.
  right. auto.
Qed.

Hint Resolve in_not_notin notin_not_in not_in_notin not_notin_in in_or_notin : PMap.

(* properties about disjoint *)
Lemma disjoint_commut: forall M1 M2, disjoint M1 M2 -> disjoint M2 M1.
Proof.
  intros M1 M2.
  unfold disjoint.
  intros.
  assert (not_in_dom x M1 \/ not_in_dom x M2); auto.
  inversion_clear H0.
  right; auto.
  left; auto.
Qed.

Hint Resolve disjoint_commut : PMap.

Lemma putA_presv_nidB :
  forall M x x' y,
    not_in_dom x M -> x<>x' -> not_in_dom x (put M x' y).
Proof.
  intros.
  unfold not_in_dom.
  unfold put.
  induction (beq_A  x x'); auto.
  contradiction.
Qed.

Lemma extend_presv_disj_left:
  forall (M1 M2 : Map) (x : A) (y : B),
    disjoint M1 M2 -> not_in_dom x M2 -> disjoint (put M1 x y) M2.
Proof.
  intros.
  unfold disjoint.
  unfold not_in_dom in H0.
  unfold disjoint in H.
  intro.
  assert (not_in_dom x0 M1 \/ not_in_dom x0 M2).
  apply H.
  inversion_clear H1.
  unfold put.
  unfold not_in_dom.
  induction (beq_A x0 x).
  right. rewrite a. auto.
  left. unfold not_in_dom in H2. auto.
  right. auto.
Qed.

Hint Resolve extend_presv_disj_left putA_presv_nidB : PMap.

Lemma extend_presv_disj_right:
  forall (M1 M2 : Map) (x : A) (y : B),
    disjoint M1 M2 -> not_in_dom x M1 -> disjoint M1 (put M2 x y).
Proof.
  intros.
  apply disjoint_commut.
  assert (disjoint M2 M1). auto with PMap.
  auto with PMap.
Qed.

Hint Resolve extend_presv_disj_right : PMap.

(* ******************************** *)
(* Disjoint and in_dom / not_in_dom *)
(* ******************************** *)
Lemma disj_exclusive_left :
  forall (x : A) (M M' : Map), 
    disjoint M M' -> in_dom x M -> not_in_dom x M'.
Proof.
  intros.
  unfold disjoint in H.
  assert (not_in_dom x M \/ not_in_dom x M'). auto.
  inversion_clear H1.
  assert (~ in_dom x M); auto with PMap.
  auto.
Qed.

Hint Resolve disj_exclusive_left : PMap.

Lemma disj_exclusive_right :
  forall (x : A) (M M' : Map), 
    disjoint M M' -> in_dom x M' -> not_in_dom x M.
Proof.
  intros.
  assert (disjoint M' M); auto with PMap.
  apply disj_exclusive_left with M'; auto.
Qed.
Hint Resolve disj_exclusive_right : PMap.

Lemma update_presv_disj_left:
  forall (M1 M2 : Map) (x : A) (y : B),
    disjoint M1 M2 -> in_dom x M1 -> disjoint (put M1 x y) M2.
Proof.
  intros.
  assert (not_in_dom x M2).
  apply disj_exclusive_left with M1; auto.
  auto with PMap.
Qed.

Hint Resolve update_presv_disj_left : PMap.

Lemma update_presv_disj_right:
  forall (M1 M2 : Map) (x : A) (y : B),
    disjoint M1 M2 -> in_dom x M2 -> disjoint M1 (put M2 x y).
Proof.
  intros.
  apply disjoint_commut.
  assert (disjoint M2 M1); auto with PMap.
Qed.

Hint Resolve update_presv_disj_right : PMap.

Lemma remove_presv_disj_left:
  forall (M1 M2 : Map) (x : A),
    disjoint M1 M2 -> disjoint (remove M1 x) M2.
Proof.
  intros.
  unfold disjoint.
  unfold disjoint in H.
  intro.
  assert (not_in_dom x0 M1 \/ not_in_dom x0 M2).
  apply H.
  inversion_clear H0.
  left.
  auto with PMap.
  right. auto.
Qed.

Hint Resolve remove_presv_disj_left : PMap.

Lemma remove_presv_disj_right:
  forall (M1 M2 : Map) (x : A),
    disjoint M1 M2 -> disjoint (remove M1 x) M2.
Proof.
  intros.
  apply disjoint_commut.
  assert (disjoint M2 M1); auto with PMap.
Qed.

Hint Resolve remove_presv_disj_right : PMap.



(* ******************************** *)
(*  Merge and in_dom / not_in_dom   *)
(* ******************************** *)
Lemma notin_merge_distr_left : 
  forall (M1 M2 : Map) (x : A), 
    not_in_dom x (merge M1 M2) -> not_in_dom x M1.
Proof.
intros M1 M2 x.
unfold not_in_dom.
unfold merge.
elim (M1 x); auto.
Qed.

Hint Resolve notin_merge_distr_left: PMap.

Lemma notin_merge_distr_right : 
  forall (M1 M2 : Map) (x : A), 
    not_in_dom x (merge M1 M2) -> not_in_dom x M2.
Proof.
intros M1 M2 x.
unfold not_in_dom.
unfold merge.
elim (M1 x). 
intros.
inversion_clear H.
auto.
Qed.
Hint Resolve notin_merge_distr_right: PMap.

  
Lemma merge_presv_indom_left:
  forall (M1 M2: Map) (x: A), in_dom x M1 -> in_dom x (merge M1 M2).
Proof.
  intros M1 M2 x.
  unfold in_dom.
  unfold merge.
  intro.
  inversion_clear H.
  exists x0.
  rewrite H0.
  auto.
Qed.


Lemma merge_presv_indom_right:
  forall (M1 M2: Map) (x: A), in_dom x M2 -> in_dom x (merge M1 M2).
Proof.
  intros.
  unfold in_dom. unfold in_dom in H.
  unfold merge.
  assert ((exists y, M1 x = Some y) \/ (M1 x = None)).
  induction (M1 x).
  left. exists a. auto. right. auto.
  inversion_clear H0.
  inversion_clear H1.
  exists x0. rewrite H0. auto.
  inversion_clear H.
  exists x0. rewrite H1. auto.
Qed.

Hint Resolve merge_presv_indom_left merge_presv_indom_right : PMap.

Lemma in_merge_left_or_right:
  forall (M1 M2: Map) (x: A), in_dom x (merge M1 M2) -> in_dom x M1 \/ in_dom x M2.
Proof.
  intros.
  unfold in_dom in H.
  unfold merge in H.
  unfold in_dom.
  induction (M1 x).
  left. auto.
  right. auto.
Qed.

Hint Resolve in_merge_left_or_right : PMap.

Lemma in_merge_not_left_in_right:
  forall (M1 M2: Map) (x: A), in_dom x (merge M1 M2) -> not_in_dom x M1 -> in_dom x M2.
Proof.
  intros.
  assert (in_dom x M1 \/ in_dom x M2); auto with PMap.
  inversion_clear H1.
  assert (~ in_dom x M1). auto with PMap.
  contradiction. auto.
Qed.
Hint Resolve in_merge_not_left_in_right: PMap.


Lemma in_merge_not_right_in_left:
  forall (M1 M2: Map) (x: A), in_dom x (merge M1 M2) -> not_in_dom x M2 -> in_dom x M1.
Proof.
  intros.
  assert (in_dom x M1 \/ in_dom x M2); auto with PMap.
  inversion_clear H1; auto.
  assert (~ in_dom x M2). auto with PMap.
  contradiction.
Qed.
Hint Resolve in_merge_not_right_in_left: PMap.


Lemma in_merge_commut:
  forall (M1 M2: Map) (x: A), in_dom x (merge M1 M2) -> in_dom x (merge M2 M1).
Proof.
  intros.
  assert (in_dom x M1 \/ in_dom x M2); auto with PMap.
  inversion_clear H0; auto with PMap.
Qed.

Hint Resolve in_merge_commut : PMap.

Lemma not_in_merge_commut:
  forall (M1 M2: Map) (x: A), not_in_dom x (merge M1 M2) -> not_in_dom x (merge M2 M1).
Proof.
  intros.
  assert (in_dom x (merge M2 M1) \/ not_in_dom x (merge M2 M1)); auto with PMap.
  inversion_clear H0; auto.
  assert (in_dom x (merge M1 M2)); auto with PMap.
  assert (~ (in_dom x (merge M1 M2))); auto with PMap.
Qed.

Hint Resolve not_in_merge_commut : PMap.

Lemma notin_left_notin_right_notin_merge:
  forall (M1 M2 : Map) (x : A), not_in_dom x M1 -> not_in_dom x M2 -> not_in_dom x (merge M1 M2).
Proof.
  intros.
  assert (in_dom x (merge M1 M2) \/ not_in_dom x (merge M1 M2)); auto with PMap.
  inversion_clear H1; auto.
  assert (in_dom x M1 \/ in_dom x M2); auto with PMap.
  inversion_clear H1.
  assert (~ (in_dom x M1)); auto with PMap.
  assert (~ (in_dom x M2)); auto with PMap.
Qed.

Hint Resolve notin_left_notin_right_notin_merge : PMap.
(* *************************************** *)
(*              merge and subseteq         *)
(* *************************************** *)
Lemma merge_extends_map:
  forall (M1 M2 : Map), subseteq M1 (merge M1 M2).
Proof.
  intros.
  unfold subseteq.
  unfold merge.
  intros.
  unfold in_dom in H.
  inversion H.
  rewrite H0.
  auto.
Qed.

Hint Resolve merge_extends_map : PMap.

(* ********************* *)
(* Propeties about merge *)
(* ********************* *)
Lemma merge_assoc: 
  forall M1 M2 M3, merge (merge M1 M2) M3 = merge M1 (merge M2 M3).
Proof.
intros M1 M2 M3.
apply extensionality.
intro.
unfold merge.
elim (M1 x).
auto.
elim (M2 x); auto.
Qed.

Hint Resolve merge_assoc : PMap.

Lemma in_left_in_merge:
  forall M1 M2 x y,
    maps_to M1 x y -> maps_to (merge M1 M2) x y.
Proof.
  unfold maps_to.
  intros.
  unfold merge.
  rewrite H. auto.
Qed.

Hint Resolve in_left_in_merge.

Lemma in_right_in_merge :
  forall M1 M2 x y,
    not_in_dom x M1 -> maps_to M2 x y -> maps_to (merge M1 M2) x y.
Proof.
  unfold maps_to.
  unfold merge.
  unfold not_in_dom.
  intros.
  rewrite H. auto.
Qed.

Hint Resolve in_right_in_merge.

Lemma put_merge_merge_put:
  forall (M1 M2 : Map) (x : A) (y : B),
    put (merge M1 M2) x y = merge (put M1 x y) M2.
Proof.
  intros M1 M2 x y.
  apply extensionality.
  intro.
  unfold put. unfold merge.
  induction (beq_A x0 x). auto. induction (M1 x0); auto.
Qed.

Hint Resolve put_merge_merge_put : PMap.

Lemma remove_merge_merge_remove_right: 
  forall (M1 M2 : Map) (x : A),
    not_in_dom x M1 -> remove (merge M1 M2) x = merge M1 (remove M2 x).
Proof.
  intros.
  apply extensionality.
  intro.
  unfold remove.
  unfold merge.
  induction (beq_A x0 x).
  rewrite <- a in H. unfold not_in_dom in H.
  rewrite H. auto.
  induction (M1 x0); auto.
Qed.


Lemma disj_remove_merge_merge_remove :
  forall (M1 M2 : Map) (x : A),
    disjoint M1 M2 -> in_dom x M1 -> remove (merge M1 M2) x = merge (remove M1 x) M2.
Proof.
  intros.
  assert (not_in_dom x M2).
  apply disj_exclusive_left with M1; auto.
  apply extensionality.
  intro.
  unfold remove. unfold merge.
  induction (beq_A x0 x).
  rewrite a. unfold not_in_dom in H1. auto. 
  auto.
Qed.

Hint Resolve remove_merge_merge_remove_right disj_remove_merge_merge_remove : PMap.


(* *************************************** *)
(*  Properties about disjoint and  merge   *)
(* *************************************** *)
Lemma disj_merge_disj_left: 
  forall M1 M2 M' : Map, disjoint (merge M1 M2) M' -> disjoint M1 M'.
Proof.
intros M1 M2 M'.
unfold disjoint.
intros.
assert (not_in_dom x (merge M1 M2) \/ not_in_dom x M'); auto.
inversion_clear H0.
left.
apply notin_merge_distr_left with M2; auto.
right. auto.
Qed.
Hint Resolve disj_merge_disj_left: PMap.

Lemma disj_merge_disj_right: 
  forall M1 M2 M' : Map, disjoint (merge M1 M2) M' -> disjoint M2 M'.
Proof.
intros M1 M2 M'.
unfold disjoint.
intros.
assert (not_in_dom x (merge M1 M2) \/ not_in_dom x M'); auto.
inversion_clear H0.
left.
apply notin_merge_distr_right with M1; auto.
right. auto.
Qed.
Hint Resolve disj_merge_disj_right: PMap.


Lemma disj_x_merge_disj_left: 
  forall M1 M2 M' : Map, disjoint M' (merge M1 M2) -> disjoint M' M1.
Proof.
  intros.
  assert (disjoint (merge M1 M2) M'). auto with PMap.
  assert (disjoint M1 M'); auto with PMap.
  apply disj_merge_disj_left with M2. auto.
Qed.


Lemma disj_x_merge_disj_right: 
  forall M1 M2 M' : Map, disjoint M' (merge M1 M2) -> disjoint M' M2.
Proof.
  intros.
  assert (disjoint (merge M1 M2) M'). auto with PMap.
  assert (disjoint M2 M'); auto with PMap.
  apply disj_merge_disj_right with M1. auto.
Qed.

Hint Resolve disj_x_merge_disj_left  disj_x_merge_disj_right: PMap.


Lemma disj_merge_commut : forall M1 M2 : Map, disjoint M1 M2 -> (merge M1 M2) = (merge M2 M1).
Proof.
intros M1 M2 disj.
apply extensionality.
intro.
unfold merge.
unfold disjoint in disj.
unfold not_in_dom in disj.
assert (M1 x = None \/ M2 x = None); auto.
inversion H.
rewrite H0.
elim (M2 x); auto.
rewrite H0.
elim (M1 x); auto.
Qed.

Hint Resolve disj_merge_commut : PMap.

Lemma disj_merge_disjUnion: forall M1 M2 : Map, disjoint M1 M2 -> disjUnion M1 M2 (merge M1 M2).
Proof.
intros M1 M2 disj.
unfold disjUnion.
split; auto.
Qed.

Hint Resolve disj_merge_disjUnion : PMap.
Lemma disj_merge_A:
  forall M1 M2 M3, disjoint M1 M2 -> disjoint M1 M3 -> disjoint M1 (merge M2 M3).
Proof.
  intros M1 M2 M3. 
  unfold disjoint.
  intros disj1 disj2.
  intro.
  assert (not_in_dom x M1 \/ not_in_dom x M2); auto.
  assert (not_in_dom x M1 \/ not_in_dom x M3); auto.
  inversion_clear H.
  left; auto.
  inversion_clear H0.
  left; auto.
  right.
  unfold not_in_dom in * |- * .
  unfold merge.
  rewrite H1.
  auto.
Qed.
Hint Resolve disj_merge_A : PMap.

Lemma disj_merge_B:
  forall M1 M2 M3, disjoint M2 M1 -> disjoint M3 M1 -> disjoint (merge M2 M3) M1.
Proof.
  intros.
  assert (disjoint M1 (merge M2 M3)); auto with PMap.
Qed.

Hint Resolve disj_merge_B : PMap.

Lemma disj_merge_assoc_left_right:
  forall M1 M2 M3, disjoint M1 M2 -> disjoint (merge M1 M2) M3 -> disjoint M1 (merge M2 M3).
Proof.
  intros M1 M2 M3 disj1 disj2.
  assert (disjoint M1 M3).
  apply disj_merge_disj_left with M2.
  auto.
  apply disj_merge_A; auto.
Qed.

Lemma disj_merge_assoc_right_left:
  forall M1 M2 M3, disjoint M2 M3 -> disjoint M1 (merge M2 M3) -> disjoint (merge M1 M2) M3.
Proof.
  intros M1 M2 M3 disj1 disj2.
  assert (disjoint M1 M3).
  apply disj_x_merge_disj_right with M2.
  auto.
  assert (disjoint M3 (merge M1 M2)); auto with PMap.
Qed.

Lemma disj_merge_ABC_BAC:
  forall M1 M2 M3, disjoint M1 M2 -> merge (merge M1 M2) M3 = merge M2 (merge M1 M3).
Proof.
intros M1 M2 M3 disj.
assert (merge M1 M2 = merge M2 M1).
apply disj_merge_commut. auto.
rewrite H.
apply merge_assoc.
Qed.

Hint Resolve disj_merge_assoc_left_right disj_merge_assoc_right_left disj_merge_ABC_BAC : PMap.


Lemma disj_merge_ABC_CAB:
  forall (M_1 M_2 M_3 : Map), 
    disjoint M_1 M_2 -> disjoint M_3 M_1 -> disjoint M_3 M_2 ->
    (merge (merge M_1 M_2) M_3) = (merge (merge M_3 M_1) M_2).
Proof.
  intros.
  assert (merge M_1 M_2 = merge M_2 M_1). auto with PMap.
  rewrite H2.
  assert (merge M_3 M_1 = merge M_1 M_3). auto with PMap.
  rewrite H3.
  assert ((merge (merge M_1 M_3) M_2) = (merge M_2 (merge M_1 M_3)));  auto with PMap.
  rewrite H4. auto with PMap.
Qed.

Hint Resolve disj_merge_ABC_CAB : PMap.

(* Properties about disjUnion and merge *)
Lemma disj_emp : forall M, disjoint M emp.
Proof.
  unfold disjoint.
  intros.
  right.
  unfold not_in_dom.
  unfold emp.
  auto.
Qed.

Lemma disj_emp_B : forall M, disjoint emp M.
Proof.
  intro.
  assert (disjoint M emp). apply disj_emp.
  auto with PMap.
Qed.

Lemma unit_emp_merge: forall M, merge M emp = M.
Proof.
  intro M.
  apply extensionality.
  intros.
  unfold merge.
  induction (M x).
  auto.
  unfold emp.
  auto.
Qed.

Hint Resolve disj_emp disj_emp_B unit_emp_merge : PMap.

Lemma unit_emp_merge_B : forall M, merge emp M = M.
Proof.
  intros.
  assert (merge emp M = merge M emp).
  auto with PMap.
  rewrite H. auto with PMap.
Qed.

Hint Resolve unit_emp_merge_B : PMap.

Lemma unit_emp_disjUnion: forall M, disjUnion M emp M.
Proof.
  intro.
  unfold disjUnion.
  split; auto with PMap.
Qed.

Hint Resolve unit_emp_disjUnion : PMap.

Lemma emp_disjUnion_unique:
  forall M M', disjUnion M emp M' -> M = M'.
Proof.
  intros.
  unfold disjUnion in H.
  inversion_clear H.
  assert (merge M emp = M); auto with PMap.
  rewrite H in H1. auto.
Qed.

Hint Resolve  emp_disjUnion_unique : PMap.

Lemma disjUnion_commut : 
  forall M1 M2 M, disjUnion M1 M2 M -> disjUnion M2 M1 M.
Proof.
  unfold disjUnion. intros.
  inversion_clear H.
  split. 
  apply disjoint_commut.
  auto.
  assert (merge M1 M2 = merge M2 M1).
  apply disj_merge_commut. auto. rewrite <- H; auto.
Qed.

Hint Resolve disjUnion_commut : PMap.

Lemma disjUnion_in_left:
  forall (M1 M2 M : Map) (x : A) (y : B),
    disjUnion M1 M2 M -> in_dom x M1 -> maps_to M x y -> maps_to M1 x y.
Proof.
  intros.
  unfold disjUnion in H.
  inversion_clear H.
  assert (not_in_dom x M2).
  apply disj_exclusive_left with M1; auto.
  rewrite H3 in H1. unfold not_in_dom in H.
  unfold maps_to. unfold maps_to in H1.
  unfold merge in H1. rewrite H in H1.
  induction (M1 x). auto. inversion_clear H1.
Qed.

Lemma disjUnion_in_right:
  forall (M1 M2 M : Map) (x : A) (y : B),
    disjUnion M1 M2 M -> in_dom x M2 -> maps_to M x y -> maps_to M2 x y.
Proof.
  intros.
  apply disjUnion_in_left with M1 M; auto with PMap.
Qed.

Hint Resolve disjUnion_in_left  disjUnion_in_right: PMap.


Lemma disjUnion_assoc_left_right:
  forall M1 M2 M3 M, disjoint M1 M2 -> disjUnion (merge M1 M2) M3 M -> disjUnion M1 (merge M2 M3) M.
Proof.
  unfold disjUnion. intros.
  inversion_clear H0.
  split.
  auto with PMap.
  rewrite H2. auto with PMap.
Qed.

Hint Resolve disjUnion_assoc_left_right: PMap.

Lemma disjUnion_assoc_right_left:
  forall M1 M2 M3 M, disjoint M2 M3 -> disjUnion M1 (merge M2 M3) M -> disjUnion (merge M1 M2) M3 M.
Proof.
  unfold disjUnion.
  intros.
  inversion_clear H0.
  split; auto with PMap.
  rewrite H2. auto with PMap.
Qed.

Hint Resolve disjUnion_assoc_right_left: PMap.

Lemma disj_merge_unique : 
  forall M1 M2 M3 M4, disjoint M1 M2 -> disjoint M3 M4 -> merge M1 M2 = merge M3 M4 -> M1 = M3 -> M2 = M4.
Proof.
  intros M1 M2 M3 M4 disj1 disj2.
  intro eqMerge. intro eq13.
  rewrite eq13 in eqMerge.
  apply extensionality.
  intro.
  assert (merge M3 M2 x = merge M3 M4 x).
  rewrite <- eqMerge. auto.
  unfold merge in H.
  assert (in_dom x M3 \/ not_in_dom x M3).
  apply in_or_notin.
  inversion_clear H0.
  rewrite eq13 in disj1.
  unfold disjoint in disj1.
  unfold disjoint in disj2.
  assert (not_in_dom x M3 \/ not_in_dom x M4); auto.
  assert (not_in_dom x M3 \/ not_in_dom x M2); auto.
  inversion_clear H0.
  unfold not_in_dom in H3.
  unfold in_dom in H1.
  inversion_clear H1.
  rewrite H3 in H0. inversion_clear H0.
  inversion_clear H2.
  unfold not_in_dom in H0.
  unfold in_dom in H1.
  inversion_clear H1.  
  rewrite H0 in H2. inversion_clear H2.
  unfold not_in_dom in H3.
  unfold not_in_dom in H0.
  rewrite <- H3 in H0. auto.
  unfold not_in_dom in H1.
  rewrite H1 in H. auto.
Qed.

Hint Resolve  disj_merge_unique : PMap.

Lemma disj_merge_unique_right : 
  forall M1 M2 M3 M4, disjoint M1 M2 -> disjoint M3 M4 -> merge M1 M2 = merge M3 M4 -> M2 = M4 -> M1 = M3.
Proof.
  intros.
  assert (disjoint M2 M1).
  auto with PMap.
  assert (disjoint M4 M3).
  auto with PMap.
  assert (merge M1 M2 = merge M2 M1); auto with PMap.
  assert (merge M3 M4 = merge M4 M3); auto with PMap.
  rewrite H5 in H1. rewrite H6 in H1.
  apply disj_merge_unique with M2 M4; auto.
Qed.

Lemma disjUnion_unique:
  forall M1 M2 M3 M4 M5,
    disjUnion M1 M2 M5 -> disjUnion M3 M4 M5 -> M1 = M3 -> M2 = M4.
Proof.
  intros.
  unfold disjUnion in H.
  unfold disjUnion in H0.
  inversion_clear H.
  inversion_clear H0.
  rewrite H3 in H4.
  apply disj_merge_unique with M1 M3; auto.
Qed.

Lemma disjUnion_equ:
   forall M1 M2 M3 M4 M5,
     disjUnion M1 M3 M4 -> disjUnion M2 M3 M5 -> M1 = M2 -> M4 = M5.
Proof.
   intros.
   unfold disjUnion in H.
   unfold disjUnion in H0.
   inversion_clear H.
   inversion_clear H0.
   rewrite H1 in H3.
   rewrite H3.
   rewrite H4.
   auto.
Qed.

Hint Resolve disj_merge_unique_right disjUnion_unique disjUnion_equ: PMap.

Lemma disjUnion_reshuffle:
  forall M M1 M2 M1' M2' M11,
      disjUnion M1 M2 M -> disjUnion M1' M2' M -> disjUnion M11 M2' M1
      -> disjUnion M11 M2 M1'.
Proof.
  intros.
  unfold disjUnion in H. unfold disjUnion in H0. unfold disjUnion in H1.
  InvertAll.
  assert (disjoint M11 M2).
  rewrite H3 in H0.
  apply disj_merge_disj_left with M2'; auto.
  assert (disjoint M2' M2).
  rewrite H3 in H0.
  apply disj_merge_disj_right with M11; auto.
  unfold disjUnion. split; auto.
  rewrite H3 in H5.
  assert (merge (merge M11 M2') M2 = merge (merge M2 M11) M2').
  auto with PMap.
  rewrite H7 in H5.
  rewrite H5 in H4.
  assert (merge M11 M2 = merge M2 M11). auto with PMap.
  rewrite H8.
  cut (merge M2 M11 = M1'). auto.
  apply disj_merge_unique_right with M2' M2'; auto.
  assert (disjoint M2' M2). auto with PMap.
  auto with PMap.
Qed.

(* properties about subDom and eqDom *)
Lemma eqDom_refl: forall M, eqDom M M.
Proof.
  intro.
  unfold eqDom.
  unfold sub_dom. auto.
Qed.

Lemma eqDom_sym: forall M1 M2, eqDom M1 M2 -> eqDom M2 M1.
Proof.
  intros M1 M2.
  unfold eqDom.
  tauto.
Qed.

Lemma subDom_trans: forall M1 M2 M3, sub_dom M1 M2 -> sub_dom M2 M3 -> sub_dom M1 M3.
Proof.
  intros M1 M2 M3.
  unfold sub_dom.
  intros. auto.
Qed.

Lemma eqDom_trans : forall M1 M2 M3, eqDom M1 M2 -> eqDom M2 M3 -> eqDom M1 M3.
Proof.
  intros M1 M2 M3.
  unfold eqDom.
  intros. inversion_clear H. inversion_clear H0.
  split. apply subDom_trans with M2; auto. apply subDom_trans with M2; auto.
Qed.

Hint Resolve eqDom_refl eqDom_sym subDom_trans eqDom_trans: PMap.

Lemma subDom_update: forall (M : Map) (x : A) (y : B), sub_dom M (put M x y).
Proof.
  intros M x y.
  unfold sub_dom.
  intros x0 INDOM.
  unfold in_dom.
  unfold in_dom in INDOM.
  inversion_clear INDOM.
  unfold put.
  induction (beq_A x0 x). exists y. auto.
  rewrite H. exists x1. auto.
Qed.

Lemma subDom_inDom_update :
  forall (M : Map) (x : A) (y : B), in_dom x M -> sub_dom (put M x y) M.
Proof.
  intros.
  unfold sub_dom.
  unfold in_dom.
  intros.
  inversion_clear H0.
  unfold put in H1.
  induction (beq_A x0 x). unfold in_dom in H. 
  inversion_clear H. rewrite a. exists x2. auto. 
  exists x1. auto.
Qed.

Lemma eqDom_indom_update_eq : 
  forall (M : Map) (x : A) (y : B), in_dom x M -> eqDom M (put M x y).
Proof.
  intros M x y indom.
  unfold eqDom.
  split.
  apply subDom_update.
  apply subDom_inDom_update; auto.
Qed.

Hint Resolve subDom_update subDom_inDom_update eqDom_indom_update_eq : PMap.

(* eqDom and merge / disjUnion *)
Lemma eqDom_merge: 
  forall M1 M2 M3 M4, merge M1 M2 = merge M3 M4 -> eqDom M1 M3 -> M1 = M3.
Proof.
  intros M1 M2 M3 M4 MG ED.
  apply extensionality.
  intro.
  unfold eqDom in ED.
  unfold sub_dom in ED.
  inversion_clear ED.
  assert (in_dom x M1 \/ not_in_dom x M1).
  apply in_or_notin.
  inversion_clear H1.
  assert (in_dom x M3). apply H. auto.
  unfold in_dom in H2. inversion_clear H2.
  unfold in_dom in H1. inversion_clear H1.
  assert (merge M1 M2 x = merge M3 M4 x). rewrite MG. auto.
  unfold merge in H1.
  rewrite H3 in H1. rewrite H2 in H1.
  rewrite H2. rewrite H3. auto.
  assert (in_dom x M3 \/ not_in_dom x M3).
  apply in_or_notin.
  inversion_clear H1.
  assert (in_dom x M1). apply H0. auto.
  unfold in_dom in H1. unfold not_in_dom in H2.
  rewrite H2 in H1. inversion_clear H1. inversion_clear H4.
  unfold not_in_dom in H2. unfold not_in_dom in H3.
  rewrite <- H3 in H2. auto.
Qed.

Lemma eqDom_disjUnion_left:  
  forall (M1 M2 M3 M4 M : Map), 
    disjUnion M1 M2 M -> disjUnion M3 M4 M -> eqDom M1 M3 -> M1 = M3.
Proof.
  intros M1 M2 M3 M4 M. unfold disjUnion.
  intros DU1 DU2 ED.
  inversion_clear DU1. inversion_clear DU2.
  rewrite H0 in H2.
  apply eqDom_merge with M2 M4; auto.
Qed.


Lemma eqDom_disjUnion_right:  
  forall M1 M2 M3 M4 M, 
    disjUnion M1 M2 M -> disjUnion M3 M4 M -> eqDom M1 M3 -> M2 = M4.
Proof.
  intros M1 M2 M3 M4 M DU1 DU2 ED.
  assert (M1 = M3). apply eqDom_disjUnion_left with M2 M4 M; auto.
  unfold disjUnion in DU1. unfold disjUnion in DU2.
  inversion_clear DU1. inversion_clear DU2.
  rewrite H1 in H3.
  apply disj_merge_unique with M1 M3; auto.
Qed.
Hint Resolve  eqDom_merge eqDom_disjUnion_left eqDom_disjUnion_right: PMap.



Lemma eqDom_notin_presv:
  forall (M1 M2 : Map) (x : A), eqDom M1 M2 -> not_in_dom x M1 -> not_in_dom x M2.
Proof.
  intros M1 M2 x ED.
  unfold not_in_dom.
  unfold eqDom in ED.
  unfold sub_dom in ED. 
  unfold in_dom in ED.
  inversion_clear ED.
  intro.
  assert ((exists b : B, M1 x = Some b) -> exists b : B, M2 x = Some b). auto.
  assert ((exists b : B, M2 x = Some b) -> exists b : B, M1 x = Some b). auto.
  induction (M2 x).
  assert (exists b : B, M1 x = Some b). apply H3. exists a. auto.
  inversion_clear H4. rewrite H1 in H5. inversion_clear H5. 
  auto.
Qed.

Lemma eqDom_disj_presv:
  forall (M1 M2 M : Map), eqDom M1 M2 -> disjoint M1 M -> disjoint M2 M.
Proof.
  intros M1 M2 M ED.
  unfold disjoint.
  intros.
  assert (not_in_dom x M1 \/ not_in_dom x M). auto.
  inversion_clear H0. left.
  unfold eqDom in ED.
  apply eqDom_notin_presv with M1; auto.
  right. auto.
Qed.
Hint Resolve  eqDom_notin_presv eqDom_disj_presv: PMap.


Lemma disjUnion_presv_in_dom:
  forall (M1 M2 M : Map) (x : A), in_dom x M1 -> disjUnion M1 M2 M -> in_dom x M.
Proof.
  intros.
  unfold disjUnion in H0.
  inversion_clear H0.
  rewrite H2.
  auto with PMap.
Qed.

Lemma disjUnion_presv_eqDom:
  forall (M1 M2 M3 M4 M M' : Map), 
    disjUnion M1 M2 M -> disjUnion M3 M4 M' -> eqDom M1 M3 -> eqDom M2 M4 -> eqDom M M'.
Proof.
  unfold eqDom.
  unfold sub_dom.
  unfold disjUnion.
  intros.
  inversion_clear H1.
  inversion_clear H2.
  inversion_clear H.
  inversion_clear H0.
  unfold in_dom.
  split.
  intros.
  inversion_clear H0.
  rewrite H6 in H8.
  unfold merge in H8.
  assert ((exists b : B, M1 x = Some b) \/ (M1 x = None)).
  induction (M1 x).
  left. exists a. auto. right. auto.
  inversion_clear H0.
  assert (in_dom x M3). apply H3. unfold in_dom. auto.
  unfold in_dom in H0. inversion_clear H0. rewrite H7. unfold merge.
  exists x1. rewrite H10. auto.
  assert (not_in_dom x M3).
  apply not_in_notin. intro. assert (in_dom x M1). apply H4; auto.
  unfold in_dom in H10. inversion_clear H10. rewrite H9 in H11. inversion_clear H11.
  rewrite H9 in H8. assert (in_dom x M4). apply H1. unfold in_dom. exists x0. auto.
  unfold in_dom in H10. inversion_clear H10. exists x1.
  rewrite H7. unfold merge. unfold not_in_dom in H0. rewrite H0. auto.
  
  intros.
  inversion_clear H0.
  rewrite H7 in H8.
  unfold merge in H8.
  assert ((exists b : B, M3 x = Some b) \/ (M3 x = None)).
  induction (M3 x).
  left. exists a. auto. right. auto.
  inversion_clear H0.
  assert (in_dom x M1). apply H4. unfold in_dom. auto.
  unfold in_dom in H0. inversion_clear H0. rewrite H6. unfold merge.
  exists x1. rewrite H10. auto.
  assert (not_in_dom x M1).
  apply not_in_notin. intro. assert (in_dom x M3). apply H3; auto.
  unfold in_dom in H10. inversion_clear H10. rewrite H9 in H11. inversion_clear H11.
  rewrite H9 in H8. assert (in_dom x M2). apply H5. unfold in_dom. exists x0. auto.
  unfold in_dom in H10. inversion_clear H10. exists x1.
  rewrite H6. unfold merge. unfold not_in_dom in H0. rewrite H0. auto.
Qed.
Hint Resolve disjUnion_presv_in_dom disjUnion_presv_eqDom: PMap.


Lemma remove_left_presv_disjUnion_left:
  forall (M1 M2 M : Map) (x : A),
    disjUnion M1 M2 M -> in_dom x M1 -> disjUnion (remove M1 x) M2 (remove M x).
Proof.
  intros M1 M2 M x.
  unfold disjUnion. intros.
  inversion_clear H.
  split.
  auto with PMap.
  rewrite H2.
  apply disj_remove_merge_merge_remove; auto.
Qed.

Hint Resolve remove_left_presv_disjUnion_left : PMap.

Lemma remove_left_presv_disjUnion_right:
  forall (M1 M2 M : Map) (x : A),
    disjUnion M1 M2 M -> in_dom x M2 -> disjUnion M1 (remove M2 x) (remove M x).
Proof.
  intros.
  cut (disjUnion (remove M2 x) M1 (remove M x)); auto with PMap.
Qed.

Hint Resolve remove_left_presv_disjUnion_right : PMap.

Lemma extend_presv_disjUnion_left:
  forall (M1 M2 M : Map) (x : A) (y : B),
    disjUnion M1 M2 M -> not_in_dom x M2 -> disjUnion (put M1 x y) M2 (put M x y).
Proof.
  intros M1 M2 M x y.
  unfold disjUnion.
  intros.
  inversion_clear H.
  split.
  auto with PMap.
  rewrite H2.
  apply put_merge_merge_put.
Qed.

Hint Resolve extend_presv_disjUnion_left : PMap.

Lemma extend_presv_disjUnion_right:
  forall (M1 M2 M : Map) (x : A) (y : B),
    disjUnion M1 M2 M -> not_in_dom x M1 -> disjUnion M1 (put M2 x y) (put M x y).
Proof.
  intros.
  cut (disjUnion (put M2 x y) M1 (put M x y)); auto with PMap.
Qed.

Hint Resolve extend_presv_disjUnion_right : PMap.

Lemma update_presv_disjUnion_left:
  forall (M1 M2 M : Map) (x : A) (y : B),
    disjUnion M1 M2 M -> in_dom x M1 -> disjUnion (put M1 x y) M2 (put M x y).
Proof.
  intros.
  assert (not_in_dom x M2).
  apply disj_exclusive_left with M1; auto.
  unfold disjUnion in H. inversion_clear H. auto.
  auto with PMap.
Qed.

Hint Resolve update_presv_disjUnion_left : PMap.

Lemma update_presv_disjUnion_right:
  forall (M1 M2 M : Map) (x : A) (y : B),
    disjUnion M1 M2 M -> in_dom x M2 -> disjUnion M1 (put M2 x y) (put M x y).
Proof.
  intros.
  cut (disjUnion (put M2 x y) M1 (put M x y)); auto with PMap.
Qed.

Hint Resolve update_presv_disjUnion_right : PMap.

(* disjunion and subseteq *)
Lemma disjoint_merge_subseteq:
  forall M_1 M_2 M, disjoint M_1 M_2 -> subseteq M_1 M -> subseteq M_2 M -> subseteq (merge M_1 M_2) M.
Proof.
  intros.
  unfold subseteq.
  intros.
  unfold merge in H2.
  unfold in_dom in H2.
  unfold merge.
  unfold subseteq in H0.
  unfold in_dom in H0.
  assert (M_1 x = None \/ exists y, M_1 x = Some y).
  induction (M_1 x).
  right.
  exists a. auto.
  left. auto.
  inversion_clear H3.
  rewrite H4. rewrite H4 in H2.
  unfold subseteq in H1.
  apply H1. unfold in_dom. auto.
  inversion_clear H4.
  rewrite H3.
  rewrite <- H3.
  apply H0. exists x0. auto.
Qed.
Hint Resolve disjoint_merge_subseteq : PMap.

Lemma disjUnion_subseteq_left:
  forall M_1 M_2 M, disjUnion M_1 M_2 M -> subseteq M_1 M.
Proof.
  intros.
  unfold disjUnion in H.
  inversion_clear H.
  rewrite H1.
  apply merge_extends_map.
Qed.


Lemma disjUnion_subseteq_right:
  forall M_1 M_2 M, disjUnion M_1 M_2 M -> subseteq M_2 M.
Proof.
  intros.
  apply disjUnion_subseteq_left with M_1.
  apply disjUnion_commut; auto.
Qed.

Lemma split_sglton_free:
  forall M x y, maps_to M x y -> disjUnion (put emp x y) (remove M x) M.
Proof.
  intros.
  unfold disjUnion.
  unfold put.
  unfold remove.
  split.
  unfold disjoint.
  intro.
  unfold not_in_dom.
  induction (beq_A x0 x).
  right. auto.
  left. unfold emp. auto.
  unfold merge.
  apply extensionality.
  intro.
  induction (beq_A x0 x).
  unfold maps_to in H.
  rewrite <- a in H. auto.
  unfold emp. auto.
Qed.
Hint Resolve disjUnion_subseteq_left disjUnion_subseteq_right split_sglton_free : PMap.


Lemma ext_emp_sglton:
  forall x y, sgltonM (put emp x y) x y.
Proof.
  unfold sgltonM.
  unfold emp.
  unfold put.
  unfold maps_to.
  unfold not_in_dom.
  intros.
  split.
  induction (beq_A x x). auto.
  assert (x = x). auto.
  contradiction.
  intros.
  induction (beq_A x0 x).
  contradiction. auto.
Qed.

Hint Resolve ext_emp_sglton.

(* properties about subseteq *)

Lemma subseteq_transitivity:
  forall M M' M'', subseteq M M' -> subseteq M' M'' -> subseteq M M''.
Proof.
  intros.
  unfold subseteq.
  intros.
  assert (M x = M' x).
  unfold subseteq in H.
  apply H; auto.
  rewrite H2. 
  unfold subseteq in H0.
  apply H0.
  unfold in_dom.
  unfold in_dom in H1.
  inversion H1.
  rewrite H3 in H2.
  exists x0.
  rewrite <- H2. auto.
Qed.

Hint Resolve subseteq_transitivity: PMap.

Lemma subset_unique_map:
  forall M M' x y, subseteq M M' -> maps_to M x y -> maps_to M' x y.
Proof.
  unfold subseteq.
  unfold maps_to.
  unfold in_dom.
  intros.
  assert (M x = M' x).
  apply H. exists y. auto.
  rewrite <- H1. auto.
Qed.
Hint Resolve subset_unique_map: PMap.

Definition minus (M M' : Map) : Map :=
  fun x =>
    match M' x with
      None => M x
    | Some _ => None
    end.

Lemma minus_disjoint:
  forall M M', disjoint M' (minus M M').
Proof.
  intros.
  unfold disjoint.
  unfold not_in_dom.
  intro x.
  assert (M' x = None \/ exists y, M' x = Some y).
  induction (M' x).
  right.
  exists a. auto. left. auto.
  inversion_clear H.
  left. auto.
  right.
  unfold minus.
  inversion_clear H0.
  rewrite H. auto.
Qed.
Hint Resolve minus_disjoint : PMap.

Lemma minus_disjUnion:
  forall M M', subseteq M' M -> disjUnion M' (minus M M') M.
Proof.
  intros.
  unfold disjUnion. split; auto with PMap.
  apply extensionality.
  intro.
  unfold merge. unfold minus.
  assert (M' x = None \/ exists y, M' x = Some y).
  induction (M' x). right. eauto. left. auto.
  inversion_clear H0.
  rewrite H1. auto.
  inversion_clear H1.
  rewrite H0.
  unfold subseteq in H.
  rewrite <- H0.
  assert (M' x = M x).
  apply H. unfold in_dom. exists x0. auto. auto.
Qed.
Hint Resolve minus_disjUnion: PMap.


Lemma subseteq_split:
  forall M' M, subseteq M' M -> exists M'', disjUnion M' M'' M.
Proof.
  intros.
  exists (minus M M').
  auto with PMap.
Qed.
Hint Resolve subseteq_split : PMap.


Lemma ext_in_dom:
  forall x y M, in_dom x (put M x y).
Proof.
  intros.
  unfold put.
  unfold in_dom.
  induction (beq_A x x).
  exists y. auto.
  assert (x = x). auto.
  contradiction.
Qed.

Hint Resolve ext_in_dom : PMap.

Lemma ext_mapsto:
  forall x y M, maps_to (put M x y) x y.
Proof.
  unfold maps_to.
  intros.
  auto with PMap.
Qed.

Hint Resolve ext_mapsto.

Lemma mapsto_indom:
  forall x y M, maps_to M x y -> in_dom x M.
Proof.
  unfold in_dom.
  unfold maps_to.
  intros.
  exists y. auto.
Qed.

Lemma ext_presv_mapsto:
  forall M x x' y y',
    x <> x' -> maps_to (put M x y) x' y' -> maps_to M x' y'.
Proof.
  intros.
  unfold maps_to.
  unfold maps_to in H0.
  unfold put in H0.
  induction (beq_A x' x).
  assert (x = x'). auto. contradiction.
  auto.
Qed.
Hint Resolve mapsto_indom ext_presv_mapsto: PMap.


Lemma put_xy_commut:
  forall M x x' y y',
    x <> x' -> put (put M x y) x' y' = put (put M x' y') x y.
Proof.
  intros.
  apply extensionality.
  unfold put.
  intro.
  induction (beq_A x0 x').
  induction (beq_A x0 x).
  rewrite a0 in a. contradiction. auto.
  induction (beq_A x0 x). auto.
  auto.
Qed.

Lemma put_xx_update:
  forall M x y y',
    put (put M x y) x y' = put M x y'.
Proof.
  intros.
  apply extensionality.
  unfold put.
  intro.
  induction (beq_A x0 x); auto.
Qed.

Hint Resolve put_xy_commut put_xx_update: PMap.

Lemma removeX_presv_Y:
  forall M x x' y,
    x <> x' -> maps_to M x' y -> maps_to (remove M x) x' y.
Proof.
  intros.
  unfold maps_to.
  unfold remove.
  induction (beq_A x' x).
  assert (x = x'). auto. contradiction.
  unfold maps_to in H0. auto.
Qed.
Hint Resolve removeX_presv_Y : PMap.

(* add by guoyu *)

Lemma mapsto_put : forall m a b,
  maps_to (put m a b) a b.
Proof.
  intros m a b.
  unfold maps_to, put.
  induction (beq_A a a); trivial.
  destruct (b0 (refl_equal _)).
Qed.
Implicit Arguments mapsto_put [].

Lemma mapsto_put_eq : forall m a b b',
  maps_to (put m a b) a b'
  -> b = b'.
Proof.
  intros.
  unfold maps_to, put in H.
  induction (beq_A a a); inversion H; trivial.
  destruct (b0 (refl_equal _)).
Qed.
Implicit Arguments mapsto_put_eq [m a b b'].

Lemma mapsto_put_neq : forall m a a' b b',
  maps_to (put m a b) a' b'
  -> a <> a'
  -> maps_to m a' b'.
Proof.
intros.
unfold maps_to, put in *.
destruct (beq_A a' a); auto.
subst a'.
destruct (H0 (refl_equal _)).
Qed.
Implicit Arguments mapsto_put_neq [m a a' b b'].

Lemma mapsto_mapsto_put : forall m a b a' b',
  maps_to m a b
  -> a <> a'
  -> maps_to (put m a' b') a b.
Proof.
intros.
unfold maps_to, put in *.
destruct (beq_A a a'); auto.
subst a'.
destruct (H0 (refl_equal _)).
Qed.
Implicit Arguments mapsto_mapsto_put [m a b a'].

Lemma mapsto_subseteq_mapsto : forall m m' a b,
  maps_to m a b
  -> subseteq m m'
  -> maps_to m' a b.
Proof.
  intros.
  unfold maps_to in *.
  unfold subseteq in H0.
  assert (in_dom a m).
  exists b; auto.
  rewrite <- (H0 a H1); auto.
Qed.
Implicit Arguments mapsto_subseteq_mapsto [m m' a b].

Ltac map_solve :=
  match goal with

    | H : maps_to ?m ?a ?b,
      H0 : ?a <> ?a'
      |- maps_to (put ?m ?a' ?b') ?a ?b =>
        apply (mapsto_mapsto_put b' H H0)

    | H : maps_to ?m ?a ?b,
      H0 : ?a' <> ?a
      |- maps_to (put ?m ?a' ?b') ?a ?b =>
        let Hn := fresh "H" in
          (assert (Hn : a <> a'); 
          [auto | apply (mapsto_mapsto_put b' H Hn)])

    | H : maps_to ?m ?a ?b,
      H0 : ?a' <> ?a
      |- maps_to (put (remove ?m ?a')?a' ?b') ?a ?b =>
        let Hn := fresh "H" in
          (assert (Hn : a <> a'); 
          [auto | 
            rewrite put_cancel_remove;
            apply (mapsto_mapsto_put b' H Hn)])

    | H : maps_to ?m ?a ?b,
      H0 : ?a <> ?a'
      |- maps_to (put (remove ?m ?a')?a' ?b') ?a ?b =>
          rewrite put_cancel_remove;
            apply (mapsto_mapsto_put b' H H0)

    | H : maps_to ?m ?a ?b,
      H0 : subseteq ?m ?m'
      |- maps_to ?m' ?a ?b =>
        apply (mapsto_subseteq_mapsto H H0)

    | H : maps_to (put ?m ?a ?b) ?a' ?b', 
      H0 : ?a <> ?a'
      |- maps_to ?m ?a' ?b' => 
        apply (mapsto_put_neq H H0)

    | H : maps_to (put ?m ?a ?b) ?a' ?b', 
      H0 : ?a' <> ?a
      |-  maps_to ?m ?a' ?b' =>
        let Hn := fresh "H" in
          (assert (Hn : a <> a'); 
          [auto | apply (mapsto_put_neq H Hn)])

    | H : maps_to (put ?m ?a ?b) ?a ?b' 
      |-  ?b = ?b' => apply (mapsto_put_eq H)
        
    | H : maps_to (put ?m ?a ?b) ?a ?b' 
      |-  ?b' = ?b => 
        pose (mapsto_put_eq H); subst b'; trivial
          
    | |- maps_to (put ?m ?a ?b) ?a ?b =>
      apply (@mapsto_put m a b)

  end.

End MapFun.
