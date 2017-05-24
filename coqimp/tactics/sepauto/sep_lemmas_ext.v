Require Import include_frm.
Require Import base_tac.

Ltac destruct_s s :=
  destruct s as [ [ [ [ [ [ ] ] ] ] ] ];
  simpl in *.

(** *)
Theorem StarComm : 
  forall P Q,
    P ** Q ==> Q ** P.
Proof.
  intros.
  simpl in *.
  simpljoin.
  do 6 eexists; splits.
  5 : eauto.
  5 : eauto.
  auto.
  2 : auto.
  jeat.
  jeat.
Qed.  

Theorem TrueI : forall s, s |= Atrue.
Proof.
  intros.
  simpl; auto.
Qed.

Theorem StarMono : 
  forall P Q P' Q',
    P ==> P' -> Q ==> Q' -> P ** Q ==> P' ** Q'.
Proof.
  intros.
  simpl in *.
  simpljoin.
  do 6 eexists; splits; eauto.
Qed.

Theorem ConjMono :
  forall P Q P' Q',
    P ==> P' -> Q ==> Q' -> (P //\\ Q ==> P' //\\ Q').
Proof.
  intros.
  destruct H1.
  split; eauto.
Qed.

Theorem DisjMono :
  forall P Q P' Q',
    P ==> P' -> Q ==> Q' -> (P \\// Q ==> P' \\// Q').
Proof.
  intros.
  destruct H1.
  left; auto.
  right; auto.
Qed.

Theorem StarEmpIL :
  forall P, P ==> Aemp ** P.
Proof.
  intros.
  simpl in *.
  destruct_s s.
  do 6 eexists; splits.
  5 : eauto.
  auto.
  4:splits; eauto.
  4:unfolds; eauto.
  jeat.
  auto.
  jeat.
  auto.
Qed.

Theorem StarEmpIR : 
  forall P, P ==> P ** Aemp.
Proof.
  intros.
  apply StarComm.
  apply StarEmpIL; auto.
Qed.


Theorem StarAssocI : 
  forall P Q R, P ** Q ** R ==> (P ** Q) ** R.
Proof.
  intros.
  destruct_s s.
  simpljoin.
  assert (exists mab, join x x5 mab /\ join mab x6 m).
  eapply join_assoc_r; eauto.
  clear H5 H0.
  assert (exists oab, join x2 x8 oab /\ join oab x9 o).
  eapply join_assoc_r; eauto.
  clear H2 H7.
  simpljoin.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
Qed.



Theorem StarEmpEL : 
  forall P, Aemp ** P ==> P.
Proof.
  intros.
  destruct_s s.
  simpljoin; auto.
  apply join_emp_eq in H0.
  subst; auto.
  unfolds in H5.
  subst x2.
  apply join_emp_eq in H2.
  subst; auto.
Qed.

Theorem StarEmpER : 
  forall P, P ** Aemp ==> P.
Proof.
  intros.
  apply StarComm in H.
  apply StarEmpEL in H; auto.
Qed.

(*
Theorem StarAssocI : 
  forall P Q R, P ** Q ** R ==> (P ** Q) ** R.
Proof.
  intros.
  destruct_s s.
  mytac.
  pose (MemMod.join_assoc_r H5 H0) as H100;
    destruct H100 as [? H100]; destruct H100 as [H100 H101];
    clear H5 H0.
  pose (OSAbstMod.join_assoc_r H7 H2) as H200;
    destruct H200 as [? H200]; destruct H200 as [H200 H201];
    clear H7 H2.
  do 6 eexists; mytac.
  5 : do 6 eexists; mytac.
  9 : eauto.
  9 : eauto.
  9 : eauto.
  6 : eauto.
  7 : eauto.
  auto.
  2 : auto.
  3 : auto.
  3 : auto.
  auto.
  auto.
Qed.

Theorem StarAssocE : 
  forall P Q R, (P ** Q) ** R ==> P ** Q ** R.
Proof.
  intros.
  destruct_s s.
  mytac.
  pose (MemMod.join_assoc_l H5 H0) as H200;
    destruct H200 as [? H200]; destruct H200 as [H200 H201];
    clear H5; clear H0.
  pose (OSAbstMod.join_assoc_l H7 H2) as H300;
    destruct H300 as [? H300]; destruct H300 as [H300 H301];
    clear H7; clear H2.
  do 6 eexists; mytac.
  6 : do 6 eexists; mytac.
  5 : eauto.
  9 : eauto.
  9 : eauto.
  6 : eauto.
  7 : eauto.
  auto.
  2 : auto.
  3 : auto.
  3 : auto.
  auto.
  auto.
Qed.

Theorem EmpPureI : 
  forall s (P:Prop),
    s |= Aemp -> P -> s |= [| P |].
Proof.
  intros.
  simpl in *.
  mytac; auto.
Qed.

Theorem EmpPureE : 
  forall s P,
    s |= [| P |] -> P /\ s |= Aemp.
Proof.
  intros.
  simpl in *.
  mytac; auto.
Qed.

Theorem Star2TrueI :
  Atrue ==> Atrue ** Atrue.
Proof.
  intros.
  simpl in *.
  do 6 eexists; mytac.
  auto.
  apply MemMod.join_emp; auto.
  auto.
  apply OSAbstMod.join_emp; auto.
Qed.

Theorem Star2TrueE : 
  Atrue ** Atrue ==> Atrue.
Proof.
  intros.
  simpl in *.
  auto.
Qed.

Theorem Star2PureI : 
  forall P Q:Prop, 
    [| P /\ Q |] ==> [| P |] ** [| Q |].
Proof.
  intros.
  destruct_s s.
  do 6 eexists; mytac; auto.
Qed.

Theorem Star2PureE : 
  forall P Q:Prop, 
    [| P |] ** [| Q |] ==> [| P /\ Q |].
Proof.
  intros.
  destruct_s s.
  mytac; auto.
Qed.

Theorem StarPureE : 
  forall s (P:Prop) (Q:asrt),
    s |= [| P |] ** Q -> P /\ s |= Q.
Proof.
  intros.
  destruct_s s.
  mytac; auto.
Qed.

Theorem StarPureI : 
  forall s (P:Prop) Q, 
    s |= Q -> P -> s |= [| P |] ** Q. 
Proof.
  intros.
  destruct_s s.
  do 6 eexists; mytac; auto.
Qed.

Theorem StarTrueI :
  forall P, P ==> P ** Atrue.
Proof.
  intros.
  destruct_s s.
  do 6 eexists; mytac; eauto.
  apply MemMod.join_comm; apply MemMod.join_emp; auto.
  apply OSAbstMod.join_comm; apply OSAbstMod.join_emp; auto.
Qed.  

Theorem Ex2exists : 
  forall s {t:Type} (P:t->asrt), 
    (s |= (EX x, P x)) -> (exists x, s |= (P x)).
Proof.
  intros.
  simpl in *.
  auto.
Qed.

Theorem exists2Ex : 
  forall s {t:Type} (P:t->asrt),
    (exists x, s |= (P x)) -> (s |= (EX x, P x)).
Proof.
  intros.
  simpl in *.
  auto.
Qed.

Theorem StarExIR : 
  forall {t:Type} P (Q:t->asrt), 
    EX x, (P ** Q x) ==> P ** EX x, Q x.
Proof.
  intros.
  destruct_s s.
  mytac.
  do 6 eexists; mytac; eauto.
Qed.

Theorem StarExIL :
  forall {t:Type} (P:t->asrt) Q,
    EX x, (P x ** Q) ==> (EX x, P x) ** Q.
Proof.
  intros.
  destruct_s s.
  mytac.
  do 6 eexists; mytac; eauto.
Qed.

Theorem StarExER : 
  forall {t:Type} P (Q:t->asrt), 
    P ** (EX x, Q x) ==> EX x, (P ** Q x).
Proof.
  intros.
  destruct_s s.
  mytac.
  do 7 eexists; mytac; eauto.
Qed.

Theorem StarExEL :
  forall {t:Type} (P:t->asrt) Q, 
    (EX x, P x) ** Q ==> EX x, (P x ** Q).
Proof.
  intros.
  destruct_s s.
  mytac.
  do 7 eexists; mytac; eauto.
Qed.

Theorem Star2PureLE : 
  forall P Q R,
    [| P |] ** [| Q |] ** R ==> [| P /\ Q |] ** R.
Proof.
  intros.
  eapply StarMono with (Q := R).
  apply Star2PureE.
  eauto.
  apply StarAssocI.  
  eauto.
Qed.

Theorem Star2PureRE : forall P Q R,
  P ** [| Q |] ** [| R |] ==> P ** [| Q /\ R |].
Proof.
  intros.
  eapply StarMono with (P:=P).
  eauto.
  apply Star2PureE.
  eauto.
Qed.

Theorem Star2PureLI : 
  forall P Q R,
    [| P /\ Q |] ** R ==> [| P |] ** [| Q |] ** R.
Proof.
  intros.
  eapply StarMono with (Q:=R) in H.
  apply StarAssocE.
  eauto.
  apply Star2PureI.
  eauto.
Qed.

Theorem Star2PureRI : 
  forall P Q R,
    P ** [| Q /\ R |] ==> P ** [| Q |] ** [| R |].
Proof.
  intros.
  eapply StarMono with (P:=P) in H.
  eauto.
  eauto.
  apply Star2PureI.
Qed.

Theorem ConjExIR : 
  forall {t:Type} P (Q:t->asrt), 
    EX x, (P //\\ Q x) ==> P //\\ EX x, Q x.
Proof.
  intros.
  simpl in *.
  mytac; eauto.
Qed.

Theorem ConjExIL : 
  forall {t:Type} (P:t->asrt) Q, 
    EX x, (P x //\\ Q) ==> (EX x, P x) //\\ Q.
Proof.
  intros.
  simpl in *.
  mytac; eauto.
Qed.

Theorem ConjExER : 
  forall {t:Type} P (Q:t->asrt), 
    P //\\ (EX x, Q x) ==> EX x, (P //\\ Q x).
Proof.
  intros.
  simpl in *.
  mytac; eauto.
Qed.

Theorem ConjExEL : 
  forall {t:Type} (P:t->asrt) Q, 
    (EX x, P x) //\\ Q ==> EX x, (P x //\\ Q).
Proof.
  intros.
  simpl in *.
  mytac; eauto.
Qed.

Theorem DisjExIR : 
  forall {t:Type} P (Q:t->asrt), 
    EX x, (P \\// Q x) ==> P \\// EX x, Q x.
Proof.
  intros.
  simpl in *.
  mytac.
  destruct H.
  left; auto.
  right; eauto.
Qed.

Theorem DisjExIL : 
  forall {t:Type} (P:t->asrt) Q, 
    EX x, (P x \\// Q) ==> (EX x, P x) \\// Q.
Proof.
  intros.
  simpl in *.
  mytac.
  destruct H.
  left; eauto.
  right; auto.
Qed.

Theorem DisjExER : 
  forall {t:Type} P (Q:t->asrt),
    (exists (x:t), x = x) ->
    P \\// (EX x, Q x) ==> EX x, (P \\// Q x).
Proof.
  intros.
  simpl in *.
  destruct H0.
  destruct H.
  exists x; intuition.
  mytac; intuition eauto.
Qed.

Theorem DisjExEL : 
  forall {t:Type} (P:t->asrt) Q,
    (exists (x:t), x = x) ->
    (EX x, P x) \\// Q ==> EX x, (P x \\// Q).
Proof.
  intros.
  simpl in *.
  destruct H0.
  mytac; intuition eauto.
  destruct H.
  exists x; intuition.
Qed.

(*
Theorem IdnotinleEmp : 
  forall var, idnotinle var ==> Aemp.
Proof.
  intros.
  simpl in *.
  conjSplit.
Qed.

Theorem IdposgEmp : 
  forall var v t, var =g= {v,t} ==> Aemp.
Proof.
  intros.
  simpl in *.
  conjSplit.
Qed.

Theorem IdposEmp : 
  forall var v t, var =l= {v,t} ==> Aemp.
Proof.
  intros.
  simpl in *.
  conjSplit.
Qed.
*)

Theorem ExProp : 
  forall {t:Type} (P Q:t->asrt) s, 
    (forall x, s |= P x -> s |= Q x) -> 
    (s |= EX x, P x -> s |= EX x, Q x).
Proof.
  intros.
  destruct H0.
  eexists; eauto.
Qed.

Theorem ConjPropE :
  forall P Q s,
    (s |= P //\\ Q) -> s |= P /\ s |= Q.
Proof.
  intros.
  simpl in H.
  auto.
Qed.

Theorem ConjPropI :
  forall P Q s,
    s |= P -> s |= Q -> s |= P //\\ Q.
Proof.
  intros.
  simpl.
  split; auto.
Qed.
*)

Theorem DisjPropE :
  forall P Q s,
    (s |= P \\// Q) -> s |= P \/ s |= Q.
Proof.
  intros.
  simpl in H.
  auto.
Qed.

(*
Theorem DisjPropI :
  forall P Q s,
    s |= P \/ s |= Q -> s |= P \\// Q.
Proof.
  intros.
  simpl.
  intuition auto.
Qed.

Theorem ConjStarIR :
  forall P Q Q',
    P ** (Q //\\ Q') ==> P ** Q //\\ P ** Q'.
Proof.
  intros.
  simpl in *.
  mytac.
  do 6 eexists; mytac; eauto.
  do 6 eexists; mytac; eauto.
Qed.

Theorem ConjStarIL :
  forall P P' Q,
    (P //\\ P') ** Q ==> P ** Q //\\ P' ** Q.
Proof.
  intros.
  simpl in *.
  mytac.
  do 6 eexists; mytac; eauto.
  do 6 eexists; mytac; eauto.
Qed.

Lemma ConjStarPureEL :
  forall P Q R,
    ([| P |] ** Q) //\\ R ==> [| P |] ** (Q //\\ R).
Proof.
  intros.
  destruct_s s.
  mytac.
  do 6 eexists; mytac; eauto.
Qed.

Lemma ConjPureEL :
  forall P Q,
    [| P |] //\\ Q ==> [| P |] ** (Aemp //\\ Q).
Proof.
  intros.
  destruct_s s.
  mytac.
  do 6 eexists; mytac; eauto.
Qed.

Lemma ConjStarPureER :
  forall P Q R,
    P //\\ ([| Q |] ** R) ==> [| Q |] ** (P //\\ R).
Proof.
  intros.
  destruct_s s.
  mytac.
  do 6 eexists; mytac; eauto.
Qed.

Lemma ConjPureER :
  forall P Q,
    P //\\ [| Q |] ==> [| Q |] ** (P //\\ Aemp).
Proof.
  intros.
  destruct_s s.
  do 6 eexists; mytac; eauto.
Qed.

Lemma ConjStarPureIL :
  forall P Q R,
    [| P |] ** (Q //\\ R) ==> ([| P |] ** Q) //\\ R.
Proof.
  intros.
  destruct_s s.
  mytac; auto.
  do 6 eexists; mytac; eauto.
Qed.

Lemma ConjPureIL :
  forall P Q,
    [| P |] ** (Aemp //\\ Q) ==> [| P |] //\\ Q.
Proof.
  intros.
  destruct_s s.
  mytac; auto.
Qed.

Lemma ConjStarPureIR :
  forall P Q R,
    [| Q |] ** (P //\\ R) ==> P //\\ ([| Q |] ** R).
Proof.
  intros.
  destruct_s s.
  mytac; auto.
  do 6 eexists; mytac; eauto.
Qed.

Lemma ConjPureIR :
  forall P Q,
    [| Q |] ** (P //\\ Aemp) ==> P //\\ [| Q |].
Proof.
  intros.
  destruct_s s.
  mytac; auto.
Qed.

Theorem Conj2AempE :
  Aemp //\\ Aemp ==> Aemp.
Proof.
  intros.
  simpl in *.
  mytac; auto.
Qed.

Theorem Conj2AempI :
  Aemp ==> Aemp //\\ Aemp.
Proof.
  intros.
  simpl in *.
  mytac; auto.
Qed.

*)
