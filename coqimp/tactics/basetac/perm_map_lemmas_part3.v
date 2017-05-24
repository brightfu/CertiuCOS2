Require Import memory.
Require Import language.
Require Import join_lib.
Require Import join_tactics.

Import veg.
(* Lemma mem_minus_disjoint_join_auto : *)
(*   forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3, *)
(*     usePerm = true -> *)
(*     disjoint m1 m2 -> *)
(*     m1 = minus m3 m2 -> *)
(*     join m1 m2 m3. *)
(*   intros. *)
(*   subst. *)
(*   hy. *)
(* Qed. *)

(** error **)
(* Lemma mem_minus_disjoint_join : *)
(*   forall (m1:mem) m2 m3, *)
(*     disjoint m1 m2 -> *)
(*     m1 = minus m3 m2 -> *)
(*     join m1 m2 m3. *)
(* (* Proof. *) *)
(* (*   intros; eapply mem_minus_disjoint_join_auto; ica. *) *)
(* (* Qed. *) *)
(* Admitted. *)


Lemma mem_disjoint_sub_merge_sub_merge_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    Maps.sub (merge m1 m2) m3 ->
    disjoint m1 m2 ->
    Maps.sub m4 m1 ->
    Maps.sub (merge m4 m2) m3.
  hy.
Qed.

Lemma mem_disjoint_sub_merge_sub_merge :
  forall (m1:mem) m2 m3 m4,
    Maps.sub (merge m1 m2) m3 ->
    disjoint m1 m2 ->
    Maps.sub m4 m1 ->
    Maps.sub (merge m4 m2) m3.
Proof.
  intros; eapply mem_disjoint_sub_merge_sub_merge_auto; ica.
Qed.


Lemma mem_sub_merge_disjoint_merge_disjont_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    Maps.sub (merge m1 m2) m3 ->
    disjoint m1 m2 ->
    disjoint m4 m3 ->
    disjoint (merge m1 m4) m2.
  hy.
Qed.

Lemma mem_sub_merge_disjoint_merge_disjont :
  forall (m1:mem) m2 m3 m4,
    Maps.sub (merge m1 m2) m3 ->
    disjoint m1 m2 ->
    disjoint m4 m3 ->
    disjoint (merge m1 m4) m2.
Proof.
  intros; eapply mem_sub_merge_disjoint_merge_disjont_auto; ica.
Qed.


Lemma mem_disjoint_merge_disjoint1_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3,
    usePerm = true ->
    disjoint (merge m1 m2) m3 ->
    disjoint m1 m3.
  hy.
Qed.

Lemma mem_disjoint_merge_disjoint1 :
  forall (m1:mem) m2 m3,
    disjoint (merge m1 m2) m3 ->
    disjoint m1 m3.
Proof.
  intros; eapply mem_disjoint_merge_disjoint1_auto; ica.
Qed.

Lemma osabst_disjoint_minus_sub_disjoint_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4,
    usePerm = false ->
    disjoint o1 (minus o2 o3) ->
    Maps.sub o4 o2 ->
    disjoint o4 o3 ->
    disjoint o1 o4.
  hy.
Qed.

Lemma osabst_disjoint_minus_sub_disjoint :
  forall (o1:osabst) o2 o3 o4,
    disjoint o1 (minus o2 o3) ->
    Maps.sub o4 o2 ->
    disjoint o4 o3 ->
    disjoint o1 o4.
Proof.
  intros; eapply osabst_disjoint_minus_sub_disjoint_auto; ica.
Qed.

Lemma osabst_join_join_disjoint_merge_disjoint_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o12 o3 o123 ox,
    usePerm = false ->
    join o1 o2 o12 ->
    join o12 o3 o123 ->
    disjoint o123 ox ->
    disjoint (merge o2 o3) ox.
  hy.
Qed.

Lemma osabst_join_join_disjoint_merge_disjoint :
  forall (o1:osabst) o2 o12 o3 o123 ox,
    join o1 o2 o12 ->
    join o12 o3 o123 ->
    disjoint o123 ox ->
    disjoint (merge o2 o3) ox.
Proof.
  intros; eapply osabst_join_join_disjoint_merge_disjoint_auto; ica.
Qed.


Lemma osabst_get_merge_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 a x,
    usePerm = false ->
    get o1 a = Some x ->
    get (merge o1 o2) a = Some x.
  hy.
Qed.

Lemma osabst_get_merge :
  forall (o1:osabst) o2 a x,
    get o1 a = Some x ->
    get (merge o1 o2) a = Some x.
Proof.
  intros; eapply osabst_get_merge_auto; ica.
Qed.

Lemma osabst_get_set_disjoint_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 a x x',
    usePerm = false ->
    disjoint o1 o2 ->
    get o1 a = Some x ->
    disjoint (set o1 a x') o2.
  hy.
Qed.

Lemma osabst_get_set_disjoint :
  forall (o1:osabst) o2 a x x',
    disjoint o1 o2 ->
    get o1 a = Some x ->
    disjoint (set o1 a x') o2.
Proof.
  intros; eapply osabst_get_set_disjoint_auto; ica.
Qed.


Lemma osabst_disjoint_join_disjoint_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4,
    usePerm = false ->
    disjoint o3 o4 ->
    join o1 o2 o3 ->
    disjoint o1 o4.
  hy.
Qed.

Lemma osabst_disjoint_join_disjoint :
  forall (o1:osabst) o2 o3 o4,
    disjoint o3 o4 ->
    join o1 o2 o3 ->
    disjoint o1 o4.
Proof.
  intros; eapply osabst_disjoint_join_disjoint_auto; ica.
Qed.

Lemma mem_join_minus_disjoint_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 (minus m3 m4) ->
    disjoint m2 m4.
  hy.
Qed.

Lemma mem_join_minus_disjoint :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 (minus m3 m4) ->
    disjoint m2 m4.
Proof.
  intros; eapply mem_join_minus_disjoint_auto; ica.
Qed.

Lemma mem_disjoint_minus_merge_eq_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2,
    usePerm = true ->
    disjoint m1 m2 ->
    m1 = minus (merge m1 m2) m2.
  hy.
Qed.

Lemma mem_disjoint_minus_merge_eq :
  forall (m1:mem) m2,
    disjoint m1 m2 ->
    m1 = minus (merge m1 m2) m2.
Proof.
  intros; eapply mem_disjoint_minus_merge_eq_auto; ica.
Qed.

(* Lemma mem_minus_merge_eq_auto : *)
(*   forall (A B T : Type) (MC : PermMap A B T) m1 m2, *)
(*     usePerm = true -> *)
(*     m1 = merge (minus m1 m2) m2. *)
(*   hy. *)
(* Qed. *)
(** error **)
(* Lemma mem_minus_merge_eq : *)
(*   forall (m1:mem) m2, *)
(*     m1 = merge (minus m1 m2) m2. *)
(* Proof. *)
(* (*   intros; eapply mem_minus_merge_eq_auto; ica. *) *)
(*   (* Qed. *) *)
(* Admitted. *)

Lemma mem_disjoint_minus_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2,
    usePerm = true ->
    disjoint (minus m1 m2) m2.
  hy.
Qed.

Lemma mem_disjoint_minus :
  forall (m1:mem) m2,
    disjoint (minus m1 m2) m2.
Proof.
  intros; eapply mem_disjoint_minus_auto; ica.
Qed.

Lemma mem_join_disjoint_join_merge_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 m3 ->
    disjoint m3 m4 ->
    join m1 (merge m2 m4) (merge m3 m4).
  hy.
Qed.

Lemma mem_join_disjoint_join_merge :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 m3 ->
    disjoint m3 m4 ->
    join m1 (merge m2 m4) (merge m3 m4).
Proof.
  intros; eapply mem_join_disjoint_join_merge_auto; ica.
Qed.

Lemma osabst_join_minus_disjoint_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4,
    usePerm = false ->
    join o1 o2 (minus o3 o4) ->
    disjoint o2 o4.
  hy.
Qed.

Lemma osabst_join_minus_disjoint :
  forall (o1:osabst) o2 o3 o4,
    join o1 o2 (minus o3 o4) ->
    disjoint o2 o4.
Proof.
  intros; eapply osabst_join_minus_disjoint_auto; ica.
Qed.


Lemma osabst_disjoint_minus_merge_eq_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2,
    usePerm = false ->
    disjoint o1 o2 ->
    o1 = minus (merge o1 o2) o2.
  hy.
Qed.

Lemma osabst_disjoint_minus_merge_eq :
  forall (o1:osabst) o2,
    disjoint o1 o2 ->
    o1 = minus (merge o1 o2) o2.
Proof.
  intros; eapply osabst_disjoint_minus_merge_eq_auto; ica.
Qed.

(* Lemma osabst_minus_merge_eq_auto : *)
(*   forall (A B T : Type) (MC : PermMap A B T) o1 o2, *)
(*     usePerm = false -> *)
(*     o1 = merge (minus o1 o2) o2. *)
(*   hy. *)
(* Qed. *)
(** error **)
(* Lemma osabst_minus_merge_eq : *)
(*   forall (o1:osabst) o2, *)
(*     o1 = merge (minus o1 o2) o2. *)
(* Proof. *)
(* (*   intros; eapply osabst_minus_merge_eq_auto; ica. *) *)
(* (* Qed. *) *)
(* Admitted. *)
  
Lemma osabst_disjoint_minus_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2,
    usePerm = false ->
    disjoint (minus o1 o2) o2.
  hy.
Qed.

Lemma osabst_disjoint_minus :
  forall (o1:osabst) o2,
    disjoint (minus o1 o2) o2.
Proof.
  intros; eapply osabst_disjoint_minus_auto; ica.
Qed.

Lemma osabst_join_disjoint_join_merge_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4,
    usePerm = false ->
    join o1 o2 o3 ->
    disjoint o3 o4 ->
    join o1 (merge o2 o4) (merge o3 o4).
  hy.
Qed.

Lemma osabst_join_disjoint_join_merge :
  forall (o1:osabst) o2 o3 o4,
    join o1 o2 o3 ->
    disjoint o3 o4 ->
    join o1 (merge o2 o4) (merge o3 o4).
Proof.
  intros; eapply osabst_join_disjoint_join_merge_auto; ica.
Qed.

Lemma mem_join_sub_join_minus_minus_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 m3 ->
    Maps.sub m3 m4 ->
    join m1 (minus m4 m3) (minus m4 m2).
  hy. (** 1.(new) 86s 2. (old) 172s **)
Qed.

Lemma mem_join_sub_join_minus_minus :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 m3 ->
    Maps.sub m3 m4 ->
    join m1 (minus m4 m3) (minus m4 m2).
Proof.
  intros; eapply mem_join_sub_join_minus_minus_auto; ica.
Qed.

Lemma mem_sub_sub_disjoint_join_minus_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 M,
    usePerm = true ->
    Maps.sub m1 M ->
    Maps.sub m2 M ->
    Maps.sub (merge m1 m2) M ->
    disjoint m1 m2 ->
    join m3 m4 m1 ->
    join m3 (minus (minus (minus M m4) m3) m2) (minus (minus M m4) m2).
  hy. (** 192 seconds, new: 85 seconds **)
Qed.
  
Lemma mem_sub_sub_disjoint_join_minus :
  forall (m1:mem) m2 m3 m4 M,
    Maps.sub m1 M ->
    Maps.sub m2 M ->
    Maps.sub (merge m1 m2) M ->
    disjoint m1 m2 ->
    join m3 m4 m1 ->
    join m3 (minus (minus (minus M m4) m3) m2) (minus (minus M m4) m2).
Proof.
  intros.
  eapply mem_sub_sub_disjoint_join_minus_auto; auto.
  exact H.
  exact H1.
  exact H2.
  auto.
Qed.


Lemma mem_sub_sub_disjoint_join_minus1_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 M,
    usePerm = true ->
    Maps.sub m1 M ->
    Maps.sub m2 M ->
    Maps.sub (merge m1 m2) M ->
    disjoint m1 m2 ->
    join m3 m4 m1 ->
    join m4 (minus (minus M m4) m2) (minus M m2).
  hy. (** first: 820s, after clear memory 409s **)
Qed.

(** too low **)
Lemma mem_sub_sub_disjoint_join_minus1 :
  forall (m1:mem) m2 m3 m4 M,
    Maps.sub m1 M ->
    Maps.sub m2 M ->
    Maps.sub (merge m1 m2) M ->
    disjoint m1 m2 ->
    join m3 m4 m1 ->
    join m4 (minus (minus M m4) m2) (minus M m2).
Proof.
  intros; eapply mem_sub_sub_disjoint_join_minus1_auto.
  auto.
  exact H.
  auto.
  auto.
  auto.
  eauto.
Qed.

Lemma mem_sub_join_minus_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2,
    usePerm = true ->
    Maps.sub m2 m1 ->
    join m2 (minus m1 m2) m1.
  hy.
Qed.

Lemma mem_sub_join_minus :
  forall (m1:mem) m2,
    Maps.sub m2 m1 ->
    join m2 (minus m1 m2) m1.
Proof.
  intros; eapply mem_sub_join_minus_auto; ica.
Qed.

Lemma osabst_disjoint_join_join_merge_merge_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4,
    usePerm = false ->
    disjoint o1 o2 ->
    join o3 o4 o1 ->
    join o3 (merge o4 o2) (merge o1 o2).
  hy.
Qed.

Lemma osabst_disjoint_join_join_merge_merge :
  forall (o1:osabst) o2 o3 o4,
    disjoint o1 o2 ->
    join o3 o4 o1 ->
    join o3 (merge o4 o2) (merge o1 o2).
Proof.
  intros; eapply osabst_disjoint_join_join_merge_merge_auto; ica.
Qed.

Lemma osabst_disjoint_minus_merge_comm_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3,
    usePerm = false ->
    disjoint o1 o2 ->
    merge o1 (minus o3 o2) = minus (merge o1 o3) o2.
  hy.
Qed.

Lemma osabst_disjoint_minus_merge_comm :
  forall (o1:osabst) o2 o3,
    disjoint o1 o2 ->
    merge o1 (minus o3 o2) = minus (merge o1 o3) o2.
Proof.
  intros; eapply osabst_disjoint_minus_merge_comm_auto; ica.
Qed.

Lemma mem_join_disjoint_sub_disjoint_merge_minus_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 m5,
    usePerm = true ->
    disjoint m1 m2 ->
    Maps.sub (merge m1 m2) m3 ->
    join m4 m5 m2 ->
    disjoint (merge m1 m4) (minus (minus m3 m1) m2).
  hy. (** 21 seconds **)
Qed.

Lemma mem_join_disjoint_sub_disjoint_merge_minus :
  forall (m1:mem) m2 m3 m4 m5,
    disjoint m1 m2 ->
    Maps.sub (merge m1 m2) m3 ->
    join m4 m5 m2 ->
    disjoint (merge m1 m4) (minus (minus m3 m1) m2).
Proof.
  intros; eapply mem_join_disjoint_sub_disjoint_merge_minus_auto; ica.
Qed.

Lemma mem_join_disjoint_sub_merge_join_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 m5,
    usePerm = true ->
    Maps.sub (merge m1 m2) m3 ->
    disjoint m1 m2 ->
    join m4 m5 m2 ->
    join m5 (merge (merge m1 m4) (minus (minus m3 m1) m2)) m3.
  hy. (** 52 s **)
Qed.

Lemma mem_join_disjoint_sub_merge_join :
  forall (m1:mem) m2 m3 m4 m5,
    Maps.sub (merge m1 m2) m3 ->
    disjoint m1 m2 ->
    join m4 m5 m2 ->
    join m5 (merge (merge m1 m4) (minus (minus m3 m1) m2)) m3.
Proof.
  intros; eapply mem_join_disjoint_sub_merge_join_auto; ica.
Qed.

Lemma osabst_join_disjoint_sub_disjoint_merge_minus_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4 o5,
    usePerm = false ->
    disjoint o1 o2 ->
    Maps.sub (merge o1 o2) o3 ->
    join o4 o5 o2 ->
    disjoint (merge o1 o4) (minus (minus o3 o1) o2).
  hy.
Qed.

Lemma osabst_join_disjoint_sub_disjoint_merge_minus :
  forall (o1:osabst) o2 o3 o4 o5,
    disjoint o1 o2 ->
    Maps.sub (merge o1 o2) o3 ->
    join o4 o5 o2 ->
    disjoint (merge o1 o4) (minus (minus o3 o1) o2).
Proof.
  intros; eapply osabst_join_disjoint_sub_disjoint_merge_minus_auto; ica.
Qed.

Lemma osabst_join_disjoint_sub_merge_join_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4 o5,
    usePerm = false ->
    Maps.sub (merge o1 o2) o3 ->
    disjoint o1 o2 ->
    join o4 o5 o2 ->
    join o5 (merge (merge o1 o4) (minus (minus o3 o1) o2)) o3.
  hy.
Qed.

Lemma osabst_join_disjoint_sub_merge_join :
  forall (o1:osabst) o2 o3 o4 o5,
    Maps.sub (merge o1 o2) o3 ->
    disjoint o1 o2 ->
    join o4 o5 o2 ->
    join o5 (merge (merge o1 o4) (minus (minus o3 o1) o2)) o3.
Proof.
  intros; eapply osabst_join_disjoint_sub_merge_join_auto; ica.
Qed.

Lemma disjoint_merge_comm :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2,
    disjoint m1 m2 ->
    merge m1 m2 = merge m2 m1.
Proof.
  hy.
Qed.

Lemma mem_join_eq_trans_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m1' m2 m3 m3' m4,
    usePerm = true ->
    join m1 m2 m3 ->
    join m1' m2 m3' ->
    join m3' m4 m3 ->
    join m1' m4 m1.
  hy.
Qed.


Lemma mem_join_eq_trans :
  forall (m1:mem) m1' m2 m3 m3' m4,
    join m1 m2 m3 ->
    join m1' m2 m3' ->
    join m3' m4 m3 ->
    join m1' m4 m1.
Proof.
  intros; eapply mem_join_eq_trans_auto; ica.
Qed.

(*newly added lemmas*)

Lemma mem_join_merge3_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 m5 m6 m7,
    usePerm = true ->
    join m1 m2 m3 ->
    join m3 m4 m5 ->
    join m5 m6 m7 ->
    join m1 (merge m6 (merge m2 m4)) m7.
  hy.
Qed.

Lemma mem_join_merge3 :
  forall (m1:mem) m2 m3 m4 m5 m6 m7,
    join m1 m2 m3 ->
    join m3 m4 m5 ->
    join m5 m6 m7 ->
    join m1 (merge m6 (merge m2 m4)) m7.
Proof.
  intros; eapply mem_join_merge3_auto; ica.
Qed.
