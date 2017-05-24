Require Import include_frm.
Require Export perm_map_lemmas.


(*newly added 2016.06.12*)
Require Import join_lib.


Lemma mem_disjoint_sub_merge_part_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 m5,
    usePerm = true ->
    disjoint m1 m2 ->
    Maps.sub (merge m1 m2) m3 ->
    join m4 m5 m1 ->
    Maps.sub (merge m5 m2) m3.
  hy.
Qed.

Lemma mem_disjoint_sub_merge_part :
  forall (m1:mem) m2 m3 m4 m5,
    disjoint m1 m2 ->
    Maps.sub (merge m1 m2) m3 ->
    join m4 m5 m1 ->
    Maps.sub (merge m5 m2) m3.
Proof.
  intros; eapply mem_disjoint_sub_merge_part_auto; ica.
Qed.


Definition mem_eq_dom_true (m1:mem) (m2:mem) :=
  forall a,
    ((exists x, m1 a = Some (true, x)) <-> (exists x, m2 a = Some (true, x))) /\
    (forall x, m1 a = Some (false, x) <-> m2 a = Some (false, x)).

Definition eq_dom_truep {A B T : Type} {MC : PermMap A B T} (m1 : T) (m2 : T) :=
  usePerm = true /\
  forall a,
    ((exists x, get m1 a = Some x /\ isRw x = true) <-> (exists x, get m2 a = Some x /\ isRw x = true)) /\
    (forall x, (get m1 a = Some x /\ isRw x = false) <-> (get m2 a = Some x /\ isRw x = false)). 

Lemma mem_eq_dom_true_general :
  forall m1 m2,
    mem_eq_dom_true m1 m2 <->
    eq_dom_truep m1 m2.
  unfold mem_eq_dom_true.
  unfold eq_dom_truep.
  unfold isRw.
  unfold get.
  unfold usePerm.
  simpl.
  unfold HalfPermMap.get.
  unfold HalfPermMap.isRw.
  unfold fst.

  split.
  intros.
  split. auto.
  split.
  split.
  intros.
  heat.
  instant H a.
  heat.
  destruct x.
  subst.
  assert (exists m, m1 a = Some (true, m)).
  {
    exists m; auto.
  }
  apply H in H1.
  heat.
  exists (true, x).
  auto.

  intros.
  instant H a.
  heat.
  destruct x.
  subst.
  assert (exists m, m2 a = Some (true, m)) by (exists m; auto).
  apply H in H2.
  heat.
  exists (true, x).
  auto.

  intros.
  split.
  intros.
  instant H a.
  heat.
  destruct x.
  subst.
  instant H1 m.
  apply H1 in H0.
  auto.

  intros.
  destruct x.
  heat.
  instant H a.
  heat.
  instant H1 m.
  apply H1 in H0.
  auto.

  (** <- **)
  intros.
  destruct H as (Hn & H).
  instant H a.
  split.
  split.
  intros.
  heat.
  assert (exists x, m1 a = Some x /\ (let (x0, _) := x in x0) = true).
  {
    exists (true, x).
    auto.
  }
  apply H in H2.
  heat.
  destruct x0.
  exists m.
  subst.
  auto.

  intros.
  heat.
  assert (exists x, m2 a = Some x /\ (let (x0, _) := x in x0) = true).
  {
    exists (true, x).
    auto.
  }
  apply H in H2.
  heat.
  destruct x0.
  exists m.
  subst.
  auto.

  intros.
  heat.
  instant H0 (false,x).
  split.
  intros.
  assert (m1 a = Some (false, x) /\ false = false) by auto.
  apply H0 in H2.
  heat; auto.

  intros.
  assert (m2 a = Some (false, x) /\ false = false) by auto.
  apply H0 in H2.
  heat; auto.
Qed.

Lemma eq_dom_true_semp :
  forall (A B T : Type) (MC : PermMap A B T) (m1 m2 :T),
    usePerm = true ->
    (forall a,
        match (get m1 a, get m2 a) with
          | (Some b1, Some b2) =>
            match (isRw b1, isRw b2) with
              | (true, true) => True
              | (false, false) => b1 = b2
              | _ => False
            end
          | (None, None) => True
          | _ => False
        end) <-> eq_dom_truep m1 m2.
  unfold eq_dom_truep.
  intros.
  split.
  intros.
  split; auto.
  intro a.
  instant H0 a.
  infer' (pnil, m1, m2) a; crush.
  destruct (isRw b) eqn:R1;
  destruct (isRw b0) eqn:R2; tryfalse.
  split.
  split.
  intros.
  eexists; eauto.
  intros.
  eexists; eauto.
  intros; split; intros; heat; crush.

  split.
  split; intros; heat; crush.
  intros.
  split; intros; heat; crush.

  (** <- **)
  intros.
  heat.
  clear H0.
  instant H1 a.
  heat.
  infer' (pnil, m1, m2) a; crush.
  assert (Hx: exists x, Some b = Some x /\ isRw x = true) by (exists b; eauto).
  apply H0 in Hx.
  heat; crush.
  assert (Hx: exists x, Some b0 = Some x /\ isRw x = true) by (exists b0; eauto).
  apply H0 in Hx.
  heat; crush.

  instant H1 b.
  assert (Hx: Some b = Some b /\ isRw b = false) by auto.
  apply H1 in Hx;
  heat; crush.

  destruct (isRw b) eqn:F1.
  assert (Hx: exists x, Some b = Some x /\ isRw x = true) by (exists b; eauto);
  apply H0 in Hx;
  heat; crush.

  instant H1 b;
  assert (Hx: Some b = Some b /\ isRw b = false) by auto;
  apply H1 in Hx;
  heat; crush.
  
  destruct (isRw b) eqn:F1.
  assert (Hx: exists x, Some b = Some x /\ isRw x = true) by (exists b; eauto);
  apply H0 in Hx;
  heat; crush.

  instant H1 b;
  assert (Hx: Some b = Some b /\ isRw b = false) by auto;
  apply H1 in Hx;
  heat; crush.
Qed.

Lemma mem_sub_merge_mem_eq_dom_true_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m1' m2 m3,
    usePerm = true ->
    disjoint m1 m2 ->
    Maps.sub (merge m1 m2) m3 ->
    eq_dom_truep m1 m1' ->
    exists m3', Maps.sub (merge m1' m2) m3' /\ eq_dom_truep m3 m3'.
  intros.
  (* ** ac: SearchAbout Maps.sub. *)
  exists (merge (merge m1' m2) (minus m3 (merge m1 m2))).
  split.
  apply sub_semp; auto.
  intro t.
  eapply eq_dom_true_semp with (a:=t) in H2.
  (* SearchAbout Maps.sub. *)
  (* assert (join (merge m1 m2) (minus m3 (merge m1 m2)) m3). *)
  (* { *)
  (*   eapply sub_sem'. *)
  (*   auto. *)
  (*   auto. *)
  (* } *)
  (* clear H1. *)
  infer' (pnil, m1, m2, disjoint m1 m2,
          merge m1 m2, m3, Maps.sub (merge m1 m2) m3,
          m1') t;
  crush.
  match goal with
    | H: get m1' t = Some ?b |- _ =>
      destruct (isRw b) eqn:R1;
      tryfalse
  end;
  infer' (pnil, (merge m1' m2), minus m3 (merge m1 m2),
          merge (merge m1' m2) (minus m3 (merge m1 m2))) t;
  crush.

  destruct (isRw b0) eqn:R1;
  destruct (isRw b1) eqn:R2;
  tryfalse;
  infer' (pnil, (merge m1' m2), minus m3 (merge m1 m2),
          merge (merge m1' m2) (minus m3 (merge m1 m2))) t;
  crush.

  destruct (isRw b) eqn:R1;
  destruct (isRw b1) eqn:R2;
  tryfalse;
  infer' (pnil, (merge m1' m2), minus m3 (merge m1 m2),
          merge (merge m1' m2) (minus m3 (merge m1 m2))) t;
  crush.

  infer' (pnil, (merge m1' m2), minus m3 (merge m1 m2),
          merge (merge m1' m2) (minus m3 (merge m1 m2))) t;
  crush.
  
  infer' (pnil, (merge m1' m2), minus m3 (merge m1 m2),
          merge (merge m1' m2) (minus m3 (merge m1 m2))) t;
  crush.

  infer' (pnil, (merge m1' m2), minus m3 (merge m1 m2),
          merge (merge m1' m2) (minus m3 (merge m1 m2))) t;
  crush.

  infer' (pnil, (merge m1' m2), minus m3 (merge m1 m2),
          merge (merge m1' m2) (minus m3 (merge m1 m2))) t;
  crush.

  auto.

  (** part2 **)
  eapply eq_dom_true_semp.
  auto.
  intro t.
  eapply eq_dom_true_semp with (a:=t) in H2.
  infer' (pnil, m1, m2, disjoint m1 m2,
          merge m1 m2, m3, Maps.sub (merge m1 m2) m3,
          m1') t;
  crush;
  infer' (pnil, (merge m1' m2), minus m3 (merge m1 m2),
          merge (merge m1' m2) (minus m3 (merge m1 m2))) t;
  crush.
  destruct (isRw b) eqn:F; crush.
  auto.
Qed.

Lemma mem_sub_merge_mem_eq_dom_true :
  forall m1 m1' m2 m3,
    disjoint m1 m2 ->
    Maps.sub (merge m1 m2) m3 ->
    mem_eq_dom_true m1 m1' ->
    exists m3', Maps.sub (merge m1' m2) m3' /\ mem_eq_dom_true m3 m3'.
Proof.
  intros.
  eapply mem_eq_dom_true_general in H1.
  (* ** ac: Check @mem_sub_merge_mem_eq_dom_true_auto. *)
  assert (exists m3',Maps.sub (merge m1' m2) m3' /\ eq_dom_truep m3 m3').
  {
    eapply mem_sub_merge_mem_eq_dom_true_auto; auto.
    eauto.
    eauto.
    eauto.
  }
  heat.
  exists x.
  eapply mem_eq_dom_true_general in H3.
  eauto.
Qed.  

Lemma disjoint_mem_eq_dom_true_disjoint_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m1' m2,
    usePerm = true ->
    disjoint m1 m2 ->
    eq_dom_truep m1 m1' ->
    disjoint m1' m2.
  intros.
  eapply disjoint_semp; auto.
  intro t.
  eapply eq_dom_true_semp with (a:=t) in H1.
  infer' (pnil, m1, m2, disjoint m1 m2,
          m1') t;
  crush.
  destruct (isRw b0) eqn:F1; crush.
  destruct (isRw b0) eqn:F1; crush.
  auto.
Qed. 
  
Lemma disjoint_mem_eq_dom_true_disjoint :
  forall m1 m1' m2,
    disjoint m1 m2 ->
    mem_eq_dom_true m1 m1' ->
    disjoint m1' m2.
Proof.
  intros.
  eapply disjoint_mem_eq_dom_true_disjoint_auto; eauto.
  eapply mem_eq_dom_true_general in H0.
  auto.
Qed.


