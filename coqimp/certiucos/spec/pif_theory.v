Require Import ucos_include.
Import DeprecatedTactic.

Definition priority := int32.

Parameter taskid: Type. 

Parameter State : Type.

Parameter WaitRel: taskid -> taskid -> State -> Prop.

Parameter IsWt: taskid -> State -> Prop.

Parameter IsRdy: taskid -> State -> Prop.

Parameter CurPr: taskid -> State -> option priority.

Parameter OldPr: taskid  -> State -> option priority.

Parameter IsOwner: taskid -> State -> Prop.

Definition PrioLt a b := Int.ltu a b = true.
Definition PrioLe a b := (Int.ltu a b = true \/ Int.eq a b = true).

Parameter IsCur: taskid -> State -> Prop.

Parameter TaskEx: taskid -> State -> Prop.

Inductive WaitChain: taskid -> taskid -> State -> Prop :=
| waitO : forall t t' S, WaitRel t t' S -> t <> t' -> WaitChain t t' S
| waitS : forall t t' t'' S,
            WaitRel t t' S ->
            t <> t' ->
            WaitChain t' t'' S ->
            WaitChain t t'' S.

Definition PI S := exists t t' p p', WaitChain t t' S /\ CurPr t S = Some p /\ CurPr t' S = Some p' /\ PrioLt p' p.

Definition PIF S := ~ PI S.

Definition Preemptive S :=
  forall t p,
    IsCur t S ->
    CurPr t S = Some p ->
    IsRdy t S /\
    forall t' p', t' <> t -> CurPr t' S = Some p' -> IsRdy t' S -> PrioLe p' p.  

Definition NoDeadLock S := forall t, IsWt t S -> exists t', WaitChain t t' S /\ IsRdy t' S.

Definition PrioLift S:= (forall t po p, OldPr t S = Some po -> CurPr t S = Some p -> PrioLe po p /\ ((~ IsOwner t S) -> po = p)).

Definition StatProp S:= forall t, TaskEx t S -> IsRdy t S \/ IsWt t S.

(*
Axiom taskex_imp_ex_p_po:
  forall t S, TaskEx t S -> exists p po, CurPr t S = Some p /\ OldPr t S = Some po.
Axiom curpr_imp_taskex:
  forall t p S, CurPr t S = Some p -> TaskEx t S.
Axiom oldpr_imp_taskex:
  forall t p S, OldPr t S = Some p -> TaskEx t S.
Axiom isrdy_imp_taskex:
  forall t S, IsRdy t S -> TaskEx t S.
*)
Definition AuxProps S:=
  (forall t, TaskEx t S -> exists p po, CurPr t S = Some p /\ OldPr t S = Some po) /\
  (forall t p, CurPr t S = Some p -> TaskEx t S) /\
  (forall t p, OldPr t S = Some p -> TaskEx t S) /\
  (forall t, IsRdy t S -> TaskEx t S).

Definition UPIF S:=
  forall t tc p pc,
    t <> tc ->
    IsCur tc S ->
    OldPr t S = Some p ->
    ~ IsOwner tc S ->
    IsWt t S ->
    OldPr tc S = Some pc ->
    PrioLe p pc.

Theorem rel_pif_upif:
  forall S,
    AuxProps S ->
    NoDeadLock S ->
    PrioLift S ->
    Preemptive S ->
    StatProp S ->
    PIF S ->
    UPIF S.
Proof.
  introv Haux.
  destruct Haux as (taskex_imp_ex_p_po & curpr_imp_taskex & oldpr_imp_taskex & isrdy_imp_taskex).
  intros.
  unfolds.
  intros.
  unfolds in H.
  unfolds in H0.
  unfolds in H1.
  unfolds in H2.
  rename H8 into Hwt.
  rename H9 into H8.
  lets H100: oldpr_imp_taskex H8.
  lets H101: taskex_imp_ex_p_po H100.
  mytac.
  clear H100.
  clear H10.
  rename x into opc.
  lets Hx:H1 H5 H9.
  destruct Hx.
  lets Hx:H2 t.
  destruct Hx.
  eapply oldpr_imp_taskex;eauto.
  lets Hx: oldpr_imp_taskex H6.
  lets Hy:taskex_imp_ex_p_po Hx.
  mytac.
  rewrite H14 in H6;inverts H6.
  lets Hz: H11 H4 H13 H12.
  lets Hw: H0 H14 H13.
  unfold PrioLe in *.
  lets H100:H0 H8 H9.
  destruct H100 as (H100&H101).
  apply H101 in H7.
  subst opc.
  clear -Hz Hw.
  destruct Hw as (Hw&Hx).
  destruct Hz;destruct Hw;int auto.

  unfolds in H3.
  unfold PI in H3.
  assert (PrioLe p pc \/ ~ (PrioLe p pc)) by tauto.
  destruct H13.
  auto.
  lets Hx: H H12.
  mytac.
  destruct H3.
  lets Hx: isrdy_imp_taskex H15.
  lets Hy:taskex_imp_ex_p_po Hx.
  mytac.
  lets Hm: oldpr_imp_taskex H6.
  lets Hn:taskex_imp_ex_p_po Hm.
  mytac.
  do 4 eexists;splits;eauto.
  assert (x=tc \/ x <> tc) by tauto.
  destruct H19.
  subst.
  rewrite H3 in H9;inverts H9.
  rewrite H16 in H8;inverts H8.
  rewrite H18 in H6;inverts H6.
  lets Hl1:H0 H18 H17.
  lets H100: H0 H16 H3.
  destruct H100.
  apply H8 in H7;subst opc.
  destruct Hl1 as (Hl1 & Hxx).
  clear -H13 Hl1.
  unfold PrioLt in *.
  unfold PrioLe in *.
  destruct Hl1;int auto.

  lets Hl: H11 H19 H3 H15.
  rewrite H18 in H6;inverts H6.
  lets Hl1:H0 H18 H17.
  lets H100: H0 H8 H9.
  destruct H100.
  apply H20 in H7.
  subst opc.
  destruct Hl1 as (Hl1 & Hxx).
  clear -Hl1 Hl H13.
  unfold PrioLt in *.
  unfold PrioLe in *.
  destruct Hl;destruct Hl1;int auto.
Qed.

