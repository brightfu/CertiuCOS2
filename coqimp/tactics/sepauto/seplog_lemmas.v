Require Import include_frm.
Require Import base_tac.

Set Implicit Arguments.
Unset Strict Implicit.

Theorem list_reverse_prop1 :
  forall (t:Type) (a:t) l1 l2,
    (List.rev (a::l1) ++ l2)%list = (List.rev l1 ++ a::l2)%list.
Proof.
  intros.
  simpl.
  apply List.app_assoc_reverse.
Qed.

Theorem list_reverse_prop2 :
  forall (t:Type) (l1 l2:list t),
    List.rev l1 = l2 -> l1 = List.rev l2.
Proof.
  induction l1; simpl; intros.
  subst l2; simpl; auto.
  assert (l1 = List.rev (List.rev l1)) as H100 by (apply IHl1; auto).
  rewrite H100; clear H100.
  rewrite <- H; clear H.
  rewrite List.rev_app_distr.
  auto.
Qed.

Theorem pair_prop :
  forall {A B:Type} (x:A * B),
    (fst x, snd x) = x.
Proof.
  intros.
  destruct x; simpl fst; simpl snd; auto.
Qed.

Hint Rewrite (@pair_prop block int) (@pair_prop int (list val)) List.app_nil_r List.rev_involutive List.rev_app_distr list_reverse_prop1 List.app_assoc_reverse : listprop.


Ltac join_emp_eq_sub :=
  match goal with
    | H: join _ empabst _ |- _ =>
      apply map_join_emp'  in H; subst; join_emp_eq_sub
    | H: join empabst _ _ |- _ =>
      apply map_join_emp'' in H; subst; join_emp_eq_sub
    | _ => auto
  end.

Ltac simplempty :=
  match goal with
    | H : emposabst ?a |- _ => unfolds in H; subst
  end.

Ltac simpl_and_sub := repeat simplempty; join_emp_eq_sub.

Ltac trysimplall :=
  repeat progress
         (
           simpl substmo in *;
           simpl substaskst in *;
           simpl getmem in *;
           simpl getabst in *;
           simpl substmo in *;
           simpl getisr in *;
           simpl getis in *;
           simpl getie in *;
           simpl gettopis in *;
           simpl getcs in *;
           simpl get_smem in *;
           simpl get_mem in *;
           simpl gettopis in *;
           simpl starinv_isr in *;
           simpl empst in *
         ).

Ltac destruct_s s := destruct s as [[[[[[]]][[]]]]].

Ltac rjeat :=
  simp join;
  simpl_and_sub;
  cook;
  repeat progress jeat;
  simp join;
  simpl_and_sub;
  try solve [unfolds; auto];
  tryfalse.

Tactic Notation "join" "auto" := try solve [simpljoin;eauto];rjeat.


Ltac ajeat :=
  intros;
  match goal with
    | H: ?s |= _ |- _ =>
      destruct_s s; simpl in *; rjeat
  end.
(** *)


Theorem astar_comm :
  forall P Q,
    P ** Q ==> Q ** P.
Proof.
  intros.
  simpl in *.
  join auto.
Qed.


Theorem atrue_intro :
  forall s, s |= Atrue.
Proof.
  intros.
  simpl; auto.
Qed.


Theorem astar_mono :
  forall P Q P' Q',
    P ==> P' ->
    Q ==> Q' ->
    P ** Q ==> P' ** Q'.
Proof.
  intros.
  simpl  in *.
  join auto.
Qed.


Theorem aconj_mono :
  forall P Q P' Q',
    P ==> P' ->
    Q ==> Q' ->
    (P //\\ Q ==> P' //\\ Q').
Proof.
  intros.
  destruct H1.
  split; eauto.
Qed.

Theorem adisj_mono :
  forall P Q P' Q',
    P ==> P' ->
    Q ==> Q' ->
    (P \\// Q ==> P' \\// Q').
Proof.
  intros.
  destruct H1.
  left; auto.
  right; auto.
Qed.

Theorem astar_l_aemp_intro :
  forall P, P ==> Aemp ** P.
Proof.
  intros.
  destruct_s s.
  simpl in *.
  join auto.
Qed.

Theorem astar_r_aemp_intro :
  forall P, P ==> P ** Aemp.
Proof.
  intros.
  destruct_s s.
  simpl in *.
  join auto.
Qed.

Theorem astar_l_aemp_elim :
  forall P, Aemp ** P ==> P.
Proof.
  intros.
  destruct_s s.
  simpl in *.
  join auto.
Qed.

Theorem astar_r_aemp_elim :
  forall P, P ** Aemp ==> P.
Proof.
  intros.
  destruct_s s.
  simpl in *.
  join auto.
Qed.

Theorem astar_assoc_intro :
  forall P Q R, P ** Q ** R ==> (P ** Q) ** R.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem astar_assoc_elim :
  forall P Q R, (P ** Q) ** R ==> P ** Q ** R.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem apure_intro :
  forall s (P:Prop),
    s |= Aemp -> P -> s |= [| P |].
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem apure_elim :
  forall s P,
    s |= [| P |] -> P /\ s |= Aemp.
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem astar_2atrue_intro :
  Atrue ==> Atrue ** Atrue.
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem astar_2atrue_elim :
  Atrue ** Atrue ==> Atrue.
Proof.
  intro.
  simpl in *.
  join auto.
Qed.


Theorem astar_l_afalse_elim :
  forall s P,
    s |= Afalse ** P -> s |= Afalse.
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem astar_l_afalse_intro :
  forall s P,
    s |= Afalse -> s |= Afalse ** P.
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem astar_l_apure_elim :
  forall s (P:Prop) (Q:asrt),
    s |= [| P |] ** Q -> P /\ s |= Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem astar_l_apure_intro :
  forall s (P:Prop) Q,
    s |= Q -> P -> s |= [| P |] ** Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem aexists_elim :
  forall s {t:Type} (P:t->asrt),
    (s |= (EX x, P x)) -> (exists x, s |= (P x)).
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem aexists_intro :
  forall s {t:Type} (P:t->asrt),
    (exists x, s |= (P x)) -> (s |= (EX x, P x)).
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem astar_r_aexists_intro :
  forall {t:Type} P (Q:t->asrt),
    EX x, (P ** Q x) ==> P ** EX x, Q x.
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem astar_l_aexists_intro :
  forall {t:Type} (P:t->asrt) Q,
    EX x, (P x ** Q) ==> (EX x, P x) ** Q.
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem astar_r_aexists_elim :
  forall {t:Type} P (Q:t->asrt),
    P ** (EX x, Q x) ==> EX x, (P ** Q x).
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem astar_l_aexists_elim :
  forall {t:Type} (P:t->asrt) Q,
    (EX x, P x) ** Q ==> EX x, (P x ** Q).
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem aconj_r_aexists_intro :
  forall {t:Type} P (Q:t->asrt),
    EX x, (P //\\ Q x) ==> P //\\ EX x, Q x.
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem aconj_l_aexists_intro :
  forall {t:Type} (P:t->asrt) Q,
    EX x, (P x //\\ Q) ==> (EX x, P x) //\\ Q.
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem aconj_r_aexists_elim :
  forall {t:Type} P (Q:t->asrt),
    P //\\ (EX x, Q x) ==> EX x, (P //\\ Q x).
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem aconj_l_aexists_elim :
  forall {t:Type} (P:t->asrt) Q,
    (EX x, P x) //\\ Q ==> EX x, (P x //\\ Q).
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem adisj_r_aexists_intro :
  forall {t:Type} P (Q:t->asrt),
    EX x, (P \\// Q x) ==> P \\// EX x, Q x.
Proof.
  intros.
  simpl in *.
  join auto.
  destruct H.
  left; auto.
  right; eauto.
Qed.

Theorem adisj_l_aexists_intro :
  forall {t:Type} (P:t->asrt) Q,
    EX x, (P x \\// Q) ==> (EX x, P x) \\// Q.
Proof.
  intros.
  simpl in *.
  join auto.
  destruct H.
  left; eauto.
  right; auto.
Qed.

Theorem adisj_r_aexists_elim :
  forall {t:Type} P (Q:t->asrt),
    (exists (x:t), x = x) ->
    P \\// (EX x, Q x) ==> EX x, (P \\// Q x).
Proof.
  intros.
  simpl in *.
  destruct H0.
  destruct H.
  exists x.
  left ; auto.
  destruct H0.
  exists x.
  right; eauto.
Qed.

Theorem adisj_l_aexists_elim :
  forall {t:Type} (P:t->asrt) Q,
    (exists (x:t), x = x) ->
    (EX x, P x) \\// Q ==> EX x, (P x \\// Q).
Proof.
  intros.
  simpl in *.
  destruct H0.
  join auto; intuition eauto.
  destruct H.
  exists x; intuition.
Qed.


Theorem aexists_prop :
  forall {t:Type} (P Q:t->asrt) s,
    (forall x, s |= P x -> s |= Q x) ->
    (s |= EX y, P y -> s |= EX z, Q z).
Proof.
  intros.
  destruct H0.
  eexists; eauto.
Qed.

Theorem aconj_elim :
  forall P Q s,
    (s |= P //\\ Q) -> s |= P /\ s |= Q.
Proof.
  intros.
  simpl in H.
  join auto.
Qed.

Theorem aconj_intro :
  forall P Q s,
    s |= P -> s |= Q -> s |= P //\\ Q.
Proof.
  intros.
  simpl.
  split; auto.
Qed.

Theorem adisj_elim :
  forall P Q s,
    (s |= P \\// Q) -> s |= P \/ s |= Q.
Proof.
  intros.
  simpl in H.
  auto.
Qed.

Theorem adisj_intro :
  forall P Q s,
    s |= P \/ s |= Q -> s |= P \\// Q.
Proof.
  intros.
  simpl.
  intuition auto.
Qed.

Theorem astar_r_aconj_elim :
  forall P Q Q',
    P ** (Q //\\ Q') ==> P ** Q //\\ P ** Q'.
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Theorem astar_l_aconj_elim :
  forall P P' Q,
    (P //\\ P') ** Q ==> P ** Q //\\ P' ** Q.
Proof.
  intros.
  simpl in *.
  join auto.
Qed.

Lemma aconj_l_astar_l_apure_elim :
  forall P Q R,
    ([| P |] ** Q) //\\ R ==> [| P |] ** (Q //\\ R).
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Lemma aconj_l_apure_elim :
  forall P Q,
    [| P |] //\\ Q ==> [| P |] ** (Aemp //\\ Q).
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Lemma aconj_r_astar_l_apure_elim :
  forall P Q R,
    P //\\ ([| Q |] ** R) ==> [| Q |] ** (P //\\ R).
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Lemma aconj_r_apure_elim :
  forall P Q,
    P //\\ [| Q |] ==> [| Q |] ** (P //\\ Aemp).
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Lemma aconj_l_astar_l_apure_intro :
  forall P Q R,
    [| P |] ** (Q //\\ R) ==> ([| P |] ** Q) //\\ R.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Lemma aconj_l_apure_intro :
  forall P Q,
    [| P |] ** (Aemp //\\ Q) ==> [| P |] //\\ Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Lemma aconj_r_astar_l_apure_intro :
  forall P Q R,
    [| Q |] ** (P //\\ R) ==> P //\\ ([| Q |] ** R).
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Lemma aconj_r_apure_intro :
  forall P Q,
    [| Q |] ** (P //\\ Aemp) ==> P //\\ [| Q |].
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem aconj_2aemp_elim :
  Aemp //\\ Aemp ==> Aemp.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem aconj_2aemp_intro :
  Aemp ==> Aemp //\\ Aemp.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem astar_prop :
  forall s P Q,
    s |= P ** Q ->
    exists s1 s2, (s1 |= P /\ s2 |= Q).
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem astar_l_aie_intro :
  forall s i Q,
    s |= Q -> getie (gettaskst s) = i -> s |= Aie i ** Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem astar_l_aie_elim :
  forall s i Q,
    s |= Aie i ** Q ->
    getie (gettaskst s) = i /\ s |= Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem aie_intro :
  forall s i,
    s |= Aemp -> getie (gettaskst s) = i -> s |= Aie i.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem aie_elim :
  forall s i,
    s |= Aie i -> getie (gettaskst s) = i /\ s |= Aemp.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem astar_l_ais_intro :
  forall s i Q,
    s |= Q -> getis (gettaskst s) = i -> s |= Ais i ** Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem astar_l_ais_elim :
  forall s i Q,
    s |= Ais i ** Q ->
    getis (gettaskst s) = i /\ s |= Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem ais_intro :
  forall s i,
    s |= Aemp -> getis (gettaskst s) = i -> s |= Ais i.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem ais_elim :
  forall s i,
    s |= Ais i -> getis (gettaskst s) = i /\ s |= Aemp.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem astar_l_aisr_intro :
  forall s i Q,
    s |= Q -> getisr (gettaskst s) = i -> s |= Aisr i ** Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem astar_l_aisr_elim :
  forall s i Q,
    s |= Aisr i ** Q ->
    getisr (gettaskst s) = i /\ s |= Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem aisr_intro :
  forall s i,
    s |= Aemp -> getisr (gettaskst s) = i -> s |= Aisr i.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem aisr_elim :
  forall s i,
    s |= Aisr i -> getisr (gettaskst s) = i /\ s |= Aemp.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem astar_l_acs_intro :
  forall s i Q,
    s |= Q -> getcs (gettaskst s) = i -> s |= Acs i ** Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem astar_l_acs_elim :
  forall s i Q,
    s |= Acs i ** Q ->
    getcs (gettaskst s) = i /\ s |= Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem acs_intro :
  forall s i,
    s |= Aemp -> getcs (gettaskst s) = i -> s |= Acs i.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem acs_elim :
  forall s i,
    s |= Acs i -> getcs (gettaskst s) = i /\ s |= Aemp.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem astar_l_atopis_intro :
  forall s i Q,
    s |= Q -> gettopis (getis (gettaskst s)) = i -> s |= ATopis i ** Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem astar_l_atopis_elim :
  forall s i Q,
    s |= ATopis i ** Q ->
    gettopis (getis (gettaskst s)) = i /\ s |= Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem atopis_intro :
  forall s i,
    s |= Aemp -> gettopis (getis (gettaskst s)) = i -> s |= ATopis i.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem atopis_elim :
  forall s i,
    s |= ATopis i -> gettopis (getis (gettaskst s)) = i /\ s |= Aemp.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem astar_l_adomlenv_intro :
  forall s d Q,
    s |= Q -> eq_dom_env (getlenv s) d -> s |= A_dom_lenv d ** Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem astar_l_adomlenv_elim :
  forall s d Q,
    s |= A_dom_lenv d ** Q ->
    eq_dom_env (getlenv s) d /\ s |= Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem adomlenv_intro :
  forall s d,
    s |= Aemp -> eq_dom_env (getlenv s) d -> s |= A_dom_lenv d.
Proof.
  ajeat.
Qed.

Theorem adomlenv_elim :
  forall s d,
    s |= A_dom_lenv d -> eq_dom_env (getlenv s) d /\ s |= Aemp.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem astar_l_anotinlenv_intro :
  forall s x Q,
    s |= Q -> ~ EnvMod.indom (getlenv s) x -> s |= A_notin_lenv x ** Q.
Proof.
  ajeat.
Qed.

Theorem astar_l_anotinlenv_elim :
  forall s x Q,
    s |= A_notin_lenv x ** Q ->
    ~ EnvMod.indom (getlenv s) x /\ s |= Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem anotinlenv_intro :
  forall s x,
    s |= Aemp -> ~ EnvMod.indom (getlenv s) x -> s |= A_notin_lenv x.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem anotinlenv_elim :
  forall s x,
    s |= A_notin_lenv x -> ~ EnvMod.indom (getlenv s) x /\ s |= Aemp.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.



Theorem astar_l_alvarenv_intro :
  forall s x t l Q,
    s |= Q -> (snd l = 0%Z /\ EnvMod.get (getlenv s) x = Some (fst l,t)) -> s |= Alvarenv x t l ** Q.
Proof.
  intros.
  destruct l.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem astar_l_alvarenv_elim :
  forall s x t l Q,
    s |= Alvarenv x t l ** Q ->
    (snd l = 0%Z /\ EnvMod.get (getlenv s) x = Some (fst l,t)) /\ s |= Q.
Proof.
  intros.
  destruct l.
  destruct_s s; simpl in *.
  join auto.
Qed.



Theorem alvarenv_intro :
  forall s x t l,
    s |= Aemp -> (snd l = 0%Z /\ EnvMod.get (getlenv s) x = Some (fst l,t)) -> s |= Alvarenv x t l.
Proof.
  intros.
  destruct l.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem alvarenv_elim :
  forall s x t l,
    s |= Alvarenv x t l -> (snd l = 0%Z /\ EnvMod.get (getlenv s) x = Some (fst l,t)) /\ s |= Aemp.
Proof.
  intros.
  destruct l.
  destruct_s s; simpl in *.
  simpljoin.
  splits;auto.
Qed.


Theorem astar_l_agvarenv_intro :
  forall s x t l Q,
    s |= Q -> (snd l = 0%Z /\ EnvMod.get (getgenv s) x = Some (fst l, t)) -> s |= Agvarenv x t l ** Q.
Proof.
  intros.
  destruct l.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem astar_l_agvarenv_elim :
  forall s x t l Q,
    s |= Agvarenv x t l ** Q ->
    (snd l = 0%Z /\ EnvMod.get (getgenv s) x = Some (fst l, t)) /\ s |= Q.
Proof.
  intros.
  destruct l.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem agvarenv_intro :
  forall s x t l,
    s |= Aemp -> (snd l = 0%Z /\ EnvMod.get (getgenv s) x = Some (fst l,t)) -> s |= Agvarenv x t l.
Proof.
  intros.
  destruct l.
  destruct_s s; simpl in *.
  join auto.
Qed.


Theorem agvarenv_elim :
  forall s x t l,
    s |= Agvarenv x t l -> (snd l = 0%Z /\ EnvMod.get (getgenv s) x = Some (fst l,t)) /\ s |= Aemp.
Proof.
  intros.
  destruct l.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem astar_l_aop'_intro :
  forall s aop Q,
    s |= Q -> getabsop s = aop -> s |= <|| aop ||> ** Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem astar_l_aop'_elim :
  forall s aop Q,
    s |= <|| aop ||> ** Q ->
    getabsop s = aop /\ s |= Q.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem aop'_intro :
  forall s aop,
    s |= Aemp -> getabsop s = aop -> s |= <|| aop ||>.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Theorem aop'_elim :
  forall s aop,
    s |= <|| aop ||> -> getabsop s = aop /\ s |= Aemp.
Proof.
  intros.
  destruct_s s; simpl in *.
  join auto.
Qed.

Lemma disj_star_elim: 
  forall p q r, ( p \\// q )** r ==> (p ** r) \\// (q ** r).
Proof.
  intros.
  simpl in *;simp join.
  destruct H3; simp join.
  left.
  do 6 eexists;splits;eauto.
  right.
  do 6 eexists;splits;eauto.
Qed.

Lemma disj_split_star :
  forall P Q R,  
    (P \\// Q) ** R ==> (P ** R) \\// (Q ** R). 
Proof.
  intros.
  simpl in *.
  simp join.
  destruct H3.
  left.
  do 6 eexists;splits; simp join ;eauto.
  right.    
  do 6 eexists;splits;simp join;eauto.
Qed.


(*
Fixpoint can_change_aop (p:asrt) :=
  match p with
    | Astar p1 p2 => (can_change_aop p1) /\ (can_change_aop p2)
    | p1 //\\ p2 =>  (can_change_aop p1)  /\ (can_change_aop p2)
    | p1 \\// p2 =>  (can_change_aop p1) /\ (can_change_aop p2)
    | Aop aop => False
    | Anot p' => False
    | Aexists t p' => forall x : t, can_change_aop (p' x)
    | _ => True
  end.
*)
Theorem change_aop_rule:
  forall o O aop aop' P,
    (o,O,aop) |= P -> can_change_aop P -> (o,O,aop') |= P.
Proof.
  intros.
  generalize dependent O.
  generalize dependent o.
  induction P;intros;simpl in *; join auto.
  destruct H.
  left.
  apply IHP1;auto.
  right.
  eauto.
Qed.


Fixpoint can_be_cancelled (p : asrt) : bool :=
  match p with
    | Astar p1 p2 => andb (can_be_cancelled p1) (can_be_cancelled p2)
    | Aemp => true
    | Amapsto l t b v => true
   (* | Amapstolsval l t vl => true *)
    | Aabsdata id data => true
    | _ => false
  end.


Theorem cancellation_rule :
  forall A B C G E isr aux aop G' E' isr' aux' aop',
    (forall m O, (G,E,m,isr,aux,O,aop) |= B ->
                 (G',E',m,isr',aux',O,aop') |= C) ->
    can_be_cancelled A = true ->
    (forall m O, (G,E,m,isr,aux,O,aop) |= A ** B ->
                 (G',E',m,isr',aux',O,aop') |= A ** C).
Proof.
  intros.
  gen B C G E isr aux aop.
  gen G' E' isr' aux' aop' m O.
  induction A; intros; simpl in H; tryfalse.

  simpl in *; join auto.
  2: simpl in *; join auto.
  2: simpl in *; join auto.
  apply andb_true_iff in H0; destruct H0.
  apply astar_assoc_intro.
  apply astar_comm.
  apply astar_assoc_intro.
  apply astar_assoc_elim in H1.
  apply astar_comm in H1.
  apply astar_assoc_elim in H1.
  gen H1.
  apply IHA2.
  auto.
  intros.
  apply astar_comm.
  apply astar_comm in H1.
  gen H1.
  apply IHA1.
  auto.
  eauto.
Qed.

