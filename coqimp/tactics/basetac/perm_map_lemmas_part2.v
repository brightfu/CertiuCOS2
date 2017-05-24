Require Import memory.
Require Import language.
Require Import join_lib.
Require Import join_tactics.

Import veg.

Lemma mem_join_disjoint_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 m3 ->
    disjoint m3 m4 ->
    join (merge m1 m4) m2 (merge m3 m4).
  hy.
Qed.  

Lemma mem_join_disjoint_merge :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 m3 ->
    disjoint m3 m4 ->
    join (merge m1 m4) m2 (merge m3 m4).
Proof.
  intros.
  eapply mem_join_disjoint_merge'; ica.
Qed.  

Lemma mem_sub_disjoint_sub_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3,
    Maps.sub m1 m2 ->
    disjoint m2 m3 ->
    Maps.sub m1 (merge m2 m3).
  hy.
Qed.
  
Lemma mem_sub_disjoint_sub_merge :
  forall (m1:mem) m2 m3,
    Maps.sub m1 m2 ->
    disjoint m2 m3 ->
    Maps.sub m1 (merge m2 m3).
Proof.
  intros.
  eapply mem_sub_disjoint_sub_merge'; ica.
Qed.  

Lemma osabst_join_disjoint_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = false ->
    join m1 m2 m3 ->
    disjoint m3 m4 ->
    join (merge m1 m4) m2 (merge m3 m4).
  hy.
Qed.

Lemma osabst_join_disjoint_merge :
  forall (m1:osabst) m2 m3 m4,
    join m1 m2 m3 ->
    disjoint m3 m4 ->
    join (merge m1 m4) m2 (merge m3 m4).
Proof.
  intros.
  eapply osabst_join_disjoint_merge'; ica.
Qed.

Lemma osabst_join_disjoint_disjoint' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3,
    join m1 m2 m12 ->
    disjoint m12 m3 ->
    disjoint m1 m3.
  hy.
Qed.

Lemma osabst_join_disjoint_disjoint :
  forall (m1:osabst) m2 m12 m3,
    join m1 m2 m12 ->
    disjoint m12 m3 ->
    disjoint m1 m3.
Proof.
  intros.
  eapply osabst_join_disjoint_disjoint'; eauto.
Qed.

Lemma mem_join_join_merge_eq' :
  forall (A B T : Type) (MC : PermMap A B T) M1 M2 M3 M4 M,
    join M1 M2 M ->
    join M3 M4 M2 ->
    M = merge M3 (merge M1 M4).
  hy.
Qed.
  
Lemma mem_join_join_merge_eq :
  forall (M1:mem) M2 M3 M4 M,
    join M1 M2 M ->
    join M3 M4 M2 ->
    M = merge M3 (merge M1 M4).
Proof.
  intros.
  eapply mem_join_join_merge_eq'; eauto.
Qed.

Lemma mem_disj_join_disjmerge':
  forall (A B T : Type) (MC : PermMap A B T) M M' M1 M2,
    disjoint M M' ->
    join M1 M2 M' ->
    disjoint (merge M2 M) M1.
  hy.
Qed.

Lemma mem_disj_join_disjmerge:
  forall (M:mem) M' M1 M2,
    disjoint M M' ->
    join M1 M2 M' ->
    disjoint (merge M2 M) M1.
Proof.
  intros.
  eapply mem_disj_join_disjmerge'; eauto.
Qed.

Lemma osabst_sub_merge_minus_eq' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2,
    usePerm = false ->
    Maps.sub o1 o2 ->
    merge o1 (minus o2 o1) = o2.
  hy.
Qed.

Lemma osabst_sub_merge_minus_eq :
  forall (o1:osabst) o2,
    Maps.sub o1 o2 ->
    merge o1 (minus o2 o1) = o2.
Proof.
  intros.
  eapply osabst_sub_merge_minus_eq'; eauto.
Qed.

Lemma osabst_join_eq_merge' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3,
    usePerm = false ->
    join m1 m2 m3 ->
    m3 = merge m1 m2.
  hy.
Qed.

Lemma osabst_join_eq_merge :
  forall (m1:osabst) m2 m3,
    join m1 m2 m3 ->
    m3 = merge m1 m2.
Proof.
  intros.
  eapply osabst_join_eq_merge'; ica.
Qed.

Lemma osabst_join_minus_eq' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3,
    usePerm = false ->
    join o1 o2 o3 ->
    minus o3 o1 = o2.
Proof.
  hy.
Qed.

Lemma osabst_join_minus_eq :
  forall (o1:osabst) o2 o3,
    join o1 o2 o3 ->
    minus o3 o1 = o2.
Proof.
  intros.
  eapply osabst_join_minus_eq'; ica.
Qed.

Lemma osabst_join_disjoint_minus_disjoint_minus' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4 o5,
    usePerm = false ->
    join o1 o2 o3 ->
    disjoint o4 (minus o3 o5) ->
    disjoint o4 (minus o2 o5).
  hy.
Qed.
  
Lemma osabst_join_disjoint_minus_disjoint_minus :
  forall (o1:osabst) o2 o3 o4 o5,
    join o1 o2 o3 ->
    disjoint o4 (minus o3 o5) ->
    disjoint o4 (minus o2 o5).
Proof.
  intros.
  eapply osabst_join_disjoint_minus_disjoint_minus'; ica.
Qed.

Lemma osabst_join_disjoint_minus_join' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4,
    usePerm = false ->
    join o1 o2 o3 ->
    disjoint o1 o4 ->
    join o1 (minus o2 o4) (minus o3 o4).
  hy.
Qed.

Lemma osabst_join_disjoint_minus_join :
  forall (o1:osabst) o2 o3 o4,
    join o1 o2 o3 ->
    disjoint o1 o4 ->
    join o1 (minus o2 o4) (minus o3 o4).
Proof.
  intros.
  eapply osabst_join_disjoint_minus_join'; ica.
Qed.

Lemma osabst_disjoint_minus_join_disjoint_disjoint' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4 o5,
    usePerm = false ->
    disjoint o1 (minus o2 o3) ->
    join o4 o5 o2 ->
    disjoint o4 o3 ->
    disjoint o1 o4.
  hy.
Qed.
  
Lemma osabst_disjoint_minus_join_disjoint_disjoint :
  forall (o1:osabst) o2 o3 o4 o5,
    disjoint o1 (minus o2 o3) ->
    join o4 o5 o2 ->
    disjoint o4 o3 ->
    disjoint o1 o4.
Proof.
  intros.
  eapply osabst_disjoint_minus_join_disjoint_disjoint'; ica.
Qed.

Lemma osabst_join_disjoint_merge1' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4,
    usePerm = false ->
    join o1 o2 o3 ->
    disjoint o4 o1 ->
    join o1 (merge o4 o2) (merge o4 o3).
  hy.
Qed.
  
Lemma osabst_join_disjoint_merge1 :
  forall (o1:osabst) o2 o3 o4,
    join o1 o2 o3 ->
    disjoint o4 o1 ->
    join o1 (merge o4 o2) (merge o4 o3).
Proof.
  intros.
  eapply osabst_join_disjoint_merge1'; ica.
Qed.

(* Lemma mem_join_disjoint_minus' : *)
(*   forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4, *)
(*     usePerm = true -> *)
(*     join m1 m2 m3 -> *)
(*     disjoint m1 m4 -> *)
(*     join m1 (minus m2 m4) (minus m3 m4). *)
(*   hy. *)
(* Qed. *)

(** error! **)
(* Lemma mem_join_disjoint_minus : *)
(*   forall (m1:mem) m2 m3 m4, *)
(*     join m1 m2 m3 -> *)
(*     disjoint m1 m4 -> *)
(*     join m1 (minus m2 m4) (minus m3 m4). *)
(* Proof. *)
(*   intros. *)
(*   eapply mem_join_disjoint_minus'; ica. *)
(* Qed. *)

Lemma mem_sub_join_minus_join' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 m3 ->
    Maps.sub m4 m1 ->
    join (minus m1 m4) m2 (minus m3 m4).
  hy.
Qed.  
  
Lemma mem_sub_join_minus_join :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 m3 ->
    Maps.sub m4 m1 ->
    join (minus m1 m4) m2 (minus m3 m4).
Proof.
  intros.
  eapply mem_sub_join_minus_join'; ica.
Qed.

Lemma mem_disjoint_sub_disjoint' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3,
    usePerm = true ->
    Maps.sub m1 m2 ->
    disjoint m2 m3 ->
    disjoint m1 m3.
  hy.
Qed.

Lemma mem_disjoint_sub_disjoint :
  forall (m1:mem) m2 m3,
    Maps.sub m1 m2 ->
    disjoint m2 m3 ->
    disjoint m1 m3.
Proof.
  intros.
  eapply mem_disjoint_sub_disjoint'; ica.
Qed.

Lemma osabst_join_sub_disjoint' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4,
    usePerm = false ->
    join o1 o2 o3 ->
    Maps.sub o4 o2 ->
    disjoint o1 o4.
  hy.
Qed.

Lemma osabst_join_sub_disjoint :
  forall (o1:osabst) o2 o3 o4,
    join o1 o2 o3 ->
    Maps.sub o4 o2 ->
    disjoint o1 o4.
Proof.
  intros.
  eapply osabst_join_sub_disjoint'; ica.
Qed.

Lemma osabst_join_sub_join_minus' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4,
    usePerm = false ->
    join o1 o2 o3 ->
    Maps.sub o4 o2 ->
    join o1 (minus o2 o4) (minus o3 o4).
  hy.
Qed.
  
Lemma osabst_join_sub_join_minus :
  forall (o1:osabst) o2 o3 o4,
    join o1 o2 o3 ->
    Maps.sub o4 o2 ->
    join o1 (minus o2 o4) (minus o3 o4).
Proof.
  intros.
  eapply osabst_join_sub_join_minus'; ica.
Qed.

Lemma osabst_join_minus1' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3,
    usePerm = false ->
    join o1 o2 o3 ->
    minus o3 o1 = o2.
  hy.
Qed.
  
Lemma osabst_join_minus1 :
  forall (o1:osabst) o2 o3,
    join o1 o2 o3 ->
    minus o3 o1 = o2.
Proof.
  intros.
  eapply osabst_join_minus1'; ica.
Qed.
  
Lemma mem_join_sub_join_minus' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    join m1 (minus m2 m4) (minus m3 m4).
  hy.
Qed.

Lemma mem_join_sub_join_minus :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    join m1 (minus m2 m4) (minus m3 m4).
Proof.
  intros.
  eapply mem_join_sub_join_minus'; ica.
Qed.

Lemma mem_join_minus1' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3,
    usePerm = true ->
    join m1 m2 m3 ->
    minus m3 m1 = m2.
  hy.
Qed.

Lemma mem_join_minus1 :
  forall (m1:mem) m2 m3,
    join m1 m2 m3 ->
    minus m3 m1 = m2.
Proof.
  intros.
  eapply mem_join_minus1'; ica.
Qed.

Lemma osabst_sub_disjoint_sub_minus' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3,
    usePerm = false ->
    Maps.sub o1 o2 ->
    disjoint o1 o3 ->
    Maps.sub o1 (minus o2 o3).
  hy.
Qed.

Lemma osabst_sub_disjoint_sub_minus :
  forall (o1:osabst) o2 o3,
    Maps.sub o1 o2 ->
    disjoint o1 o3 ->
    Maps.sub o1 (minus o2 o3).
Proof.
  intros.
  eapply osabst_sub_disjoint_sub_minus'; ica.
Qed.

Lemma osabst_disjoint_minus_minus_disjoint' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4,
    usePerm = false ->
    disjoint o1 (minus o2 o3) ->
    disjoint o1 (minus (minus o2 o4) o3).
  hy.
Qed.

Lemma osabst_disjoint_minus_minus_disjoint :
  forall (o1:osabst) o2 o3 o4,
    disjoint o1 (minus o2 o3) ->
    disjoint o1 (minus (minus o2 o4) o3).
Proof.
  intros.
  eapply osabst_disjoint_minus_minus_disjoint'; ica.
Qed.

Lemma osabst_disjoint_merge_disjoint2' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3,
    usePerm = false ->
    disjoint (merge o1 o2) o3 ->
    disjoint o2 o3.
  hy.
Qed.

Lemma osabst_disjoint_merge_disjoint2 :
  forall (o1:osabst) o2 o3,
    disjoint (merge o1 o2) o3 ->
    disjoint o2 o3.
Proof.
  intros.
  eapply osabst_disjoint_merge_disjoint2'; ica.
Qed.


Lemma osabst_disjoint_minus_disjoint' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3,
    usePerm = false ->
    disjoint o1 o2 ->
    disjoint o1 (minus o2 o3).
  hy.
Qed.
  
Lemma osabst_disjoint_minus_disjoint :
  forall (o1:osabst) o2 o3,
    disjoint o1 o2 ->
    disjoint o1 (minus o2 o3).
Proof.
  intros.
  eapply osabst_disjoint_minus_disjoint'; ica.
Qed.


Lemma osabst_disjoint_disjoint_merge_distribute' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4,
    usePerm = false ->
    disjoint o1 o2 ->
    disjoint (merge o1 o2) o3 ->
    Maps.sub o4 o3 ->
    join (merge o4 o1) (merge o2 (minus o3 o4)) (merge (merge o1 o2) o3).
  hy.
Qed.

Lemma osabst_disjoint_disjoint_merge_distribute :
  forall (o1:osabst) o2 o3 o4,
    disjoint o1 o2 ->
    disjoint (merge o1 o2) o3 ->
    Maps.sub o4 o3 ->
    join (merge o4 o1) (merge o2 (minus o3 o4)) (merge (merge o1 o2) o3).
Proof.
  intros.
  eapply osabst_disjoint_disjoint_merge_distribute'; ica.
Qed.


Lemma osabst_disjoint_minus_comm' :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3,
    usePerm = false ->
    disjoint o2 o3 ->
    minus (minus o1 o2) o3 = minus (minus o1 o3) o2.
  hy.
Qed.

Lemma osabst_disjoint_minus_comm :
  forall (o1:osabst) o2 o3,
    disjoint o2 o3 ->
    minus (minus o1 o2) o3 = minus (minus o1 o3) o2.
Proof.
  intros.
  eapply osabst_disjoint_minus_comm'; ica.
Qed.

Lemma sub_join_sub :
  forall
    {A B T:Type} {MC:PermMap A B T}
    m1 m2 m3 m4,
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    Maps.sub m4 m3.
Proof.
  hy.
Qed.


Lemma mem_sub_join_sub' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    Maps.sub m4 m3.
  hy.
Qed.

Lemma mem_sub_join_sub :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    Maps.sub m4 m3.
Proof.
  intros.
  eapply mem_sub_join_sub'; ica.
Qed.


Lemma mem_join_sub_disjoint' :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    disjoint m1 m4.
  hy.
Qed.

Lemma mem_join_sub_disjoint :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    disjoint m1 m4.
Proof.
  intros.
  eapply mem_join_sub_disjoint'; ica.
Qed.

Lemma mem_join_sub_sub_merge_a :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    Maps.sub (merge m1 m4) m3.
  hy.
Qed.

Lemma mem_join_sub_sub_merge :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    Maps.sub (merge m1 m4) m3.
Proof.
  intros; eapply mem_join_sub_sub_merge_a; ica.
Qed.

Lemma mem_join_sub_sub_merge'_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    Maps.sub (merge m4 m1) m3.
  hy.
Qed.

Lemma mem_join_sub_sub_merge' :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    Maps.sub (merge m4 m1) m3.
Proof.
  intros; eapply mem_join_sub_sub_merge'_auto; ica.
Qed.


Lemma join_sub_sub_merge :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2 m3 m4,
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    Maps.sub (merge m1 m4) m3.
Proof.
  hy.
Qed.

Lemma join_sub_sub_merge' :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2 m3 m4,
    join m1 m2 m3 ->
    Maps.sub m4 m2 ->
    Maps.sub (merge m4 m1) m3.
Proof.
  hy.
Qed.


Lemma mem_join_minus_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3,
    usePerm = true ->
    join m1 m2 m3 ->
    m1 = minus m3 m2.
  hy.
Qed.

Lemma mem_join_minus :
  forall (m1:mem) m2 m3,
    join m1 m2 m3 ->
    m1 = minus m3 m2.
Proof.
  intros; eapply mem_join_minus_auto; ica.
Qed.
