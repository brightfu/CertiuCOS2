Require Import ucos_include.
Require Import seplog_tactics.

(**Lemmas for OSQGetMsg*)
Lemma R_PrioTbl_P_msg : forall v'6 v'15 x p t m m' av,
  TcbMod.get v'15 x = Some (p, t, m) ->
  R_PrioTbl_P v'6 v'15 av ->  R_PrioTbl_P v'6 (TcbMod.set v'15 x (p, t, m')) av.
Proof.
  intros.
  unfold R_PrioTbl_P in *.
  split.
  destruct H0; clear H1.
  intros.
  apply H0 in H2; auto.
  do 2 destruct H2.
  destruct (tidspec.beq x tcbid) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  rewrite TcbMod.set_a_get_a.
  unfolds in H2; simpl in H2.
  rewrite H2 in H; inverts H.
  eauto.
  apply tidspec.eq_beq_true; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  eauto.
  split.

  destruct H0; clear H0.
  intros.
  destruct (tidspec.beq x tcbid) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  rewrite TcbMod.set_a_get_a in H0.
  inverts H0.
  eapply H1; eauto.
  apply tidspec.eq_beq_true; auto.

  rewrite TcbMod.set_a_get_a' in H0; auto.
  eapply H1; eauto.
  simpljoin1.
  eapply R_Prio_NoChange_Prio_hold; eauto.
Qed.

Lemma TCBNode_P_msg : forall x0 v'19 x7 m m' i5 i4 i3 i2 i1 i0 i p t v'12,
 TCBNode_P
         (x0
          :: v'19
             :: x7
                :: m
                   :: Vint32 i5
                      :: Vint32 i4
                         :: Vint32 i3
                            :: Vint32 i2
                               :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
         v'12 (p, t, m) ->
 TCBNode_P
         (x0
          :: v'19
             :: x7
                :: m'
                   :: Vint32 i5
                      :: Vint32 i4
                         :: Vint32 i3
                            :: Vint32 i2
                               :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
         v'12 (p, t, m').
Proof.
  intros.
  unfold TCBNode_P in *; simpljoin1; splits.
  unfolds; simpl; auto.
  unfolds in H; simpl in H; inverts H.
  unfolds in H0; simpl in H0; inverts H0.
  eexists.
  auto.
  unfolds in H; simpl in H; inverts H.
  unfolds in H0; simpl in H0; inverts H0.
  unfolds in H2.
  simpljoin1.
  unfolds.
  splits; auto.
  unfolds in H.
  unfolds.
  intros.
  lets Hre : H H4.
  destruct Hre.
  destruct H6.
  splits; eauto.
  destruct H7.
  inverts H7.
  eexists; eauto.
  unfolds in H0.
  unfolds .
  intros.
  eapply H0; eauto.
  inverts H4.
  eauto.
  unfolds in H2.
  unfolds.
  simpljoin1; splits.
  unfolds in H2.
  unfolds.
  intros.
  lets Hrs : H2 H8 H9; auto.
  destruct Hrs.
  splits; eauto.
  simpljoin1.
  eexists; eauto.
  unfolds in H4.
  unfolds.
  intros.
  lets Hrs : H4 H8 H10; auto.
  simpljoin1.
  eexists; eauto.
  unfolds in H5.
  unfolds.
  intros.
  lets Hrs : H5 H8 H10; auto.
  simpljoin1.
  eexists; eauto.
  unfolds.
  intros.
  lets Hrs : H6 H8 H10; auto.
  simpljoin1.
  eexists; eauto.
  unfolds.
  intros.
  lets Hrs : H7 H8 H10; auto.
  simpljoin1.
  eexists; eauto.
  unfolds.
  splits;
  unfolds;introv Hf; inverts Hf; eapply H3; eauto.
Qed.
  

Lemma RH_TCBList_ECBList_P_msg :
  forall v'14 v'15 x p t m m',
    TcbMod.get v'15 x = Some (p, t, m) ->
    RH_TCBList_ECBList_P v'14 v'15 x ->
    RH_TCBList_ECBList_P v'14 (TcbMod.set v'15 x (p, t, m')) x.
Proof.
  intros.
  unfolds in H0.
  destruct H0 as (Hr1 & Hr2 & Hr3 & Hr4).
  unfolds in Hr1.
  splits.
  unfolds.
  splits.
  intros.
  apply Hr1 in H0; auto.
  simpljoin1.
  destruct (tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  unfolds in H0; simpl in H0.
  rewrite H in H0; inverts H0.
  do 3 eexists; eauto.
  rewrite TcbMod.set_a_get_a'; auto.
  eauto.
  intros.
  destruct (tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  rewrite TcbMod.set_a_get_a in H0; auto; inverts H0.
  eapply Hr1; eauto.
  rewrite TcbMod.set_a_get_a' in H0; auto.
  eapply Hr1; eauto.
   unfolds.
  splits.
  intros.
  apply Hr2 in H0; auto.
  simpljoin1.
  destruct (tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  unfolds in H0; simpl in H0.
  rewrite H in H0; inverts H0.
  do 3 eexists; eauto.
  rewrite TcbMod.set_a_get_a'; auto.
  eauto.
  intros.
  destruct (tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  rewrite TcbMod.set_a_get_a in H0; auto; inverts H0.
  eapply Hr2; eauto.
  rewrite TcbMod.set_a_get_a' in H0; auto.
  eapply Hr2; eauto.
  unfolds.
  splits.
  intros.
  apply Hr3 in H0; auto.
  simpljoin1.
  destruct (tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  unfolds in H0; simpl in H0.
  rewrite H in H0; inverts H0.
  do 3 eexists; eauto.
  rewrite TcbMod.set_a_get_a'; auto.
  eauto.
  intros.
  destruct (tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  rewrite TcbMod.set_a_get_a in H0; auto; inverts H0.
  eapply Hr3; eauto.
  rewrite TcbMod.set_a_get_a' in H0; auto.
  eapply Hr3; eauto.
   unfolds.
  splits.
  intros.
  apply Hr4 in H0; auto.
  simpljoin1.
  destruct (tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  unfolds in H0; simpl in H0.
  rewrite H in H0; inverts H0.
  do 3 eexists; eauto.
  rewrite TcbMod.set_a_get_a'; auto.
  eauto.
  intros.
  destruct (tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  rewrite TcbMod.set_a_get_a in H0; auto; inverts H0.
  eapply Hr4; eauto.
  rewrite TcbMod.set_a_get_a' in H0; auto.
  eapply Hr4; eauto.

  unfolds in Hr4.
  destruct Hr4; destruct H1.
  clear - H2 H.
  unfolds; intros. 
  unfolds in H2.
  destruct(tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  eauto.
  rewrite TcbMod.set_a_get_a'; auto.
  eapply H2; eauto.
Qed.


Lemma RHL_ECB_ETbl_P_msg : forall x0 x v v'14 p t m m',
  RHL_ECB_ETbl_P x0 v v'14 ->
  TcbMod.get v'14 x = Some (p, t, m) ->
  RHL_ECB_ETbl_P x0 v (TcbMod.set v'14 x (p, t, m')).
Proof.
  intros.
  unfolds in H.
  destruct H as (Hr1 & Hr2 & Hr3 & Hr4).
  destruct v.
  unfolds.
  splits.
  unfolds.
  intros.
  destruct (tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  apply (Hr1 prio m n tid).
  rewrite TcbMod.set_a_get_a in H; inverts H; auto.
  rewrite TcbMod.set_a_get_a' in H; auto.
  eapply Hr1; eauto.
   unfolds.
  intros.
  destruct (tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  apply (Hr2 prio m n tid).
  rewrite TcbMod.set_a_get_a in H; inverts H; auto.
  rewrite TcbMod.set_a_get_a' in H; auto.
  eapply Hr2; eauto.
 unfolds.
  intros.
  destruct (tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  apply (Hr3 prio m n tid).
  rewrite TcbMod.set_a_get_a in H; inverts H; auto.
  rewrite TcbMod.set_a_get_a' in H; auto.
  eapply Hr3; eauto.
   unfolds.
  intros.
  destruct (tidspec.beq x tid) eqn : eq1.
  pose proof tidspec.beq_true_eq x tid eq1; substs.
  apply (Hr4 prio m n tid).
  rewrite TcbMod.set_a_get_a in H; inverts H; auto.
  rewrite TcbMod.set_a_get_a' in H; auto.
  eapply Hr4; eauto.
Qed.

Lemma RLH_ECB_ETbl_P_msg : forall x0 v v'14 x p t m m',
  RLH_ECB_ETbl_P x0 v v'14 -> 
  TcbMod.get v'14 x = Some (p, t, m) ->
  RLH_ECB_ETbl_P x0 v (TcbMod.set v'14 x (p, t, m')).
Proof.
  intros.
  unfolds in H.
  destruct H as (Hr1 & Hr2 & Hr3 & Hr4).
  destruct v.
  unfolds.
  splits.
  unfolds.
  intros.
  eapply Hr1 in H1; eauto. 
  simpljoin1.
  destruct (tidspec.beq x x1) eqn : eq1.
  pose proof tidspec.beq_true_eq x x1 eq1; substs.
  exists x1 x2 m'.
  rewrite TcbMod.set_a_get_a; auto.
  unfolds in H1; simpl in H1.
  rewrite H0 in H1.
  inverts H1;auto.
  exists x1 x2 x3.
  rewrite TcbMod.set_a_get_a'; auto.
   unfolds.
  intros.
  eapply Hr2 in H1; eauto. 
  simpljoin1.
  destruct (tidspec.beq x x1) eqn : eq1.
  pose proof tidspec.beq_true_eq x x1 eq1; substs.
  exists x1 x2 m'.
  rewrite TcbMod.set_a_get_a; auto.
  unfolds in H1; simpl in H1.
  rewrite H0 in H1.
  inverts H1;auto.
  exists x1 x2 x3.
  rewrite TcbMod.set_a_get_a'; auto.
   unfolds.
  intros.
  eapply Hr3 in H1; eauto. 
  simpljoin1.
  destruct (tidspec.beq x x1) eqn : eq1.
  pose proof tidspec.beq_true_eq x x1 eq1; substs.
  exists x1 x2 m'.
  rewrite TcbMod.set_a_get_a; auto.
  unfolds in H1; simpl in H1.
  rewrite H0 in H1.
  inverts H1;auto.
  exists x1 x2 x3.
  rewrite TcbMod.set_a_get_a'; auto.
   unfolds.
  intros.
  eapply Hr4 in H1; eauto. 
  simpljoin1.
  destruct (tidspec.beq x x1) eqn : eq1.
  pose proof tidspec.beq_true_eq x x1 eq1; substs.
  exists x1 x2 m'.
  rewrite TcbMod.set_a_get_a; auto.
  unfolds in H1; simpl in H1.
  rewrite H0 in H1.
  inverts H1;auto.
  exists x1 x2 x3.
  rewrite TcbMod.set_a_get_a'; auto.
Qed.



Lemma R_ECB_ETbl_P_msg : forall x0 v v'14 x p t m m',
  R_ECB_ETbl_P x0 v v'14 ->
  TcbMod.get v'14 x = Some (p, t, m) ->
R_ECB_ETbl_P x0 v (TcbMod.set v'14 x (p, t, m')).
Proof.
  intros.
  unfold R_ECB_ETbl_P in *; simpljoin1; splits.
  eapply RLH_ECB_ETbl_P_msg; eauto.
  eapply RHL_ECB_ETbl_P_msg; eauto.
  auto.
Qed.


Lemma ECBList_P_msg : forall v'4 v x6 x t m m' v'3 v'13 v'14 p,  
  ECBList_P x6 v v'4 v'3 v'13 v'14 ->
  TcbMod.get v'14 x = Some (p, t, m) ->
  ECBList_P x6 v v'4 v'3 v'13 (TcbMod.set v'14 x (p, t, m')).
Proof.
  intro.
  inductions v'4; intros.
  simpl ECBList_P in *; auto.
  destruct v'3.
  simpl in H; do 3 destruct H; destruct H1; tryfalse.
  unfold ECBList_P in H; destruct a; simpljoin1.
  unfold ECBList_P.
  eexists; split; eauto.
  split.
  clear H5 IHv'4.
  eapply R_ECB_ETbl_P_msg; eauto.
  fold ECBList_P in *.
  do 3 eexists; eauto.
Qed.


Lemma RH_CurTCB_Prop : forall x y  p t m m',
                         TcbMod.get y x  = Some (p, t, m) -> 
                         RH_CurTCB x y ->
                         RH_CurTCB x
                                   (TcbMod.set y x (p,t,m')).
Proof.
  intros.
  unfold RH_CurTCB in *.
  simpljoin1.
  do 3 eexists.
  unfolds in H0; simpl in H0.
  rewrite H in H0.
  inverts H0.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true .
  eauto.
  auto.
Qed.
