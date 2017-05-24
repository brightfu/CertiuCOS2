Require Import sem_common.

Open Scope code_scope.

Lemma semacc_new_fundation:
  forall s P a msgq mq a' msgq' mq' n wls i x2 x3 x4 qid b tcbls,
    s |= AEventData a msgq ** P ->
    RLH_ECBData_P msgq mq ->
    R_ECB_ETbl_P qid (a,b) tcbls ->
    a = (V$OS_EVENT_TYPE_SEM :: Vint32 i :: Vint32 n :: x2 :: x3 :: x4 :: nil) ->
    msgq = DSem n ->
    mq = (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    a' = (V$OS_EVENT_TYPE_SEM :: Vint32 i :: Vint32 (n-ᵢ$ 1)  :: x2 :: x3 :: x4 :: nil) ->
    msgq' = DSem (n-ᵢ$ 1) ->
    mq' = (abssem (n-ᵢ$ 1), wls) ->
    s |= AEventData a' msgq' **
         [| RLH_ECBData_P msgq' mq' |] ** 
         [| R_ECB_ETbl_P qid (a',b) tcbls |] ** P. 
  intros.
  sep pauto.
  unfold AEventData in *.
  sep pauto.
  

  apply semacc_ltu_trans; auto.
  unfold RLH_ECBData_P in *.
  destruct H0.
  split.
  auto.  
  unfold RH_ECB_P in *.
  destruct H2.
  split.
  intros.
  apply H2; auto.
  intros.
  apply H2 in H5.
  tryfalse.
Qed.


Lemma semacc_RH_TCBList_ECBList_P_hold:
  forall mqls tcbls ct a n wl,
    RH_TCBList_ECBList_P mqls tcbls ct ->
    get mqls a = Some (abssem n, wl) ->
    Int.ltu Int.zero n = true ->
    RH_TCBList_ECBList_P 
      (set mqls a (abssem (Int.sub n Int.one), wl)) tcbls ct.
  intros.
  unfold RH_TCBList_ECBList_P in *.
  destruct H as [Hq [Hsem [Hmbox Hmutex]]] .
  intuition.


(***************** Q begin ************)

  unfold RH_TCBList_ECBList_Q_P in *.
  destruct Hq as [F1 F2].
  intuition.
  destruct (dec a eid) eqn:Feq.
  subst.
  match goal with
    | H: get (set _ _ _) _ = _ |- _ =>
        rewrite set_a_get_a in H; tryfalse; auto
  end.

  eapply F1.
  split; 
    [ rewrite set_a_get_a' in H2; eauto
    | eauto].

  destruct (dec a eid) eqn:Feq.
  subst.
  match goal with
    | H: get _ _ = _ |- _ =>
        apply F2 in H; mytac; tryfalse'
  end.
      
  rewrite set_a_get_a'; 
    [ eapply F2; eauto
    | auto].
(**************** Q end ************)  

  unfold RH_TCBList_ECBList_SEM_P in *.
  destruct Hsem as [F1 F2].
  intuition.
  destruct (dec a eid) eqn:Feq.
  subst.
  rewrite set_a_get_a in H2; eauto.
  inverts H2.
  eapply F1.
  split; eauto.

  eapply F1.
  split;
    [ rewrite set_a_get_a' in H2; eauto
    | eauto].

  destruct (dec a eid) eqn:Feq.
  subst.
  apply F2 in H; mytac.
  Ltac gel H :=
    match type of H with
      | ?A = ?B =>
        change ((fun y => y = B) A) in H
    end.
  gel H0.
  rewrite H in H0.
  inverts H0.
  rewrite set_a_get_a.
  do 2 eexists.
  eauto.

  rewrite set_a_get_a'.
  apply F2 in H; mytac.
  do 2 eexists.
  eauto.
  auto.
  
  unfold RH_TCBList_ECBList_MBOX_P in *.
  destruct Hmbox as [F1 F2].
  intuition.
  destruct (dec a eid) eqn:Feq.
  subst.
  match goal with
    | H: get (set _ _ _) _ = _ |- _ =>
        rewrite set_a_get_a in H; tryfalse; auto
  end.

  eapply F1.
  split; 
    [ rewrite set_a_get_a' in H2; eauto
    | eauto].

  destruct (dec a eid) eqn:Feq.
  subst.
  match goal with
    | H: get _ _ = _ |- _ =>
        apply F2 in H; mytac; tryfalse'
  end.
      
  rewrite set_a_get_a'; 
    [ eapply F2; eauto
    | auto].


  unfold RH_TCBList_ECBList_MUTEX_P in *.
  destruct Hmutex as [F1 F2].
  swallow; intros.
  
  destruct (dec a eid) eqn:Feq.
  destruct H.
  subst.
  match goal with
    | H: get (set _ _ _) _ = _ |- _ =>
        rewrite set_a_get_a in H; tryfalse; auto
  end.

  eapply F1.
  destruct H.
  split; 
    [ rewrite set_a_get_a' in e; eauto
    | eauto].

  destruct (dec a eid) eqn:Feq.
  subst.
  match goal with
    | H: get _ _ = _ |- _ =>
        apply F2 in H; mytac; tryfalse'
  end.
      
  rewrite set_a_get_a'; 
    [ eapply F2; eauto
    | auto].

  eapply Mutex_owner_set; eauto.
  intro; mytac.
  tryfalse.
  mytac.
Qed.
