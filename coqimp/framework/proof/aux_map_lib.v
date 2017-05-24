Require Import include_frm.
Require Import join_lib.

Lemma memory_prop_map1 :
  forall (A B T : Type) (MC : PermMap A B T) Ml Ms Ms' Mc'0 Mcc,
    usePerm = true ->
    disjoint Mc'0 Ms' ->
    merge Mc'0 Ms' = merge Mcc Ms ->
    disjoint Ml Ms ->
    Maps.sub Mcc Ml ->
    disjoint (merge (minus Ml Mcc) Mc'0) Ms'.
  intros.
  apply disjoint_semp; auto.
  intro t.
  infer' (pnil, Mc'0, Ms', disjoint Mc'0 Ms',
          merge Mc'0 Ms',
          Mcc, Ms, merge Mcc Ms,
          Ml, disjoint Ml Ms, Maps.sub Mcc Ml) t;
  rewrite H1 in *; crush; tryfalse;
  infer' (pnil, minus Ml Mcc, merge (minus Ml Mcc) Mc'0) t;
  crush.
Qed.

Lemma memory_prop_get_sub_get :
  forall (A B T : Type) (MC : PermMap A B T) Ml Mc' a c,
    usePerm = true ->
    isRw c = true ->
    get Mc' a = Some c ->
    Maps.sub Mc' Ml ->
    get Ml a = Some c.
  hy.
Qed.


Lemma memory_prop_map3 :
  forall (A B T : Type) (MC : PermMap A B T) m Ms a c,
    usePerm = true ->
    isRw c = true ->
    get m a = Some c ->
    get (merge m Ms) a = Some c.
  hy.
Qed.


Lemma join_sig_set' :
  forall (A B T : Type) (MC : PermMap A B T) a id O,
    get O id = None ->
    join O (sig id a) (set O id a).
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.



