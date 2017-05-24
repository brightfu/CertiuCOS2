Require Import ucos_include.
Open Scope int_scope.
Open Scope Z_scope.
(*Require Export mathlib.*)
(**Lemmas for OSEventSearch*****)

(*
Lemma Event_Type_P_struct_type_vallist_match_OS_EVENT :
  forall i0 i i1 v1 x3 x2,
    Event_Type_P (Vint32 i0 :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil) ->
    Int.unsigned i <= 255 -> Int.unsigned i1 <= 65535 ->
    isptr v1 ->
    isptr x2 ->
    struct_type_vallist_match OS_EVENT (Vint32 i0 :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil).
Proof.
  intros.
  unfolds in H.
  destruct H.
  unfolds in H; simpl in H; inverts H.
  pauto.
  destruct H.
  unfolds in H; simpl in H; inverts H.
  pauto.
  destruct H.
  unfolds in H; simpl in H; inverts H.
  pauto.
  unfolds in H; simpl in H; inverts H.
  pauto.
Qed.
*)


Lemma evsllseg_append : forall v'19 v'16 v0 v'21 v1 v'2 v'26 x3 i0 i i1 x2 H5 d,
  H5 |= evsllseg v'16 (Vptr (v'26, Int.zero)) v'19 v'21 **
        Astruct (v'26, Int.zero) os_ucos_h.OS_EVENT (Vint32 i0 :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil) ** AOSEventTbl v'2 v0 ** AEventData (Vint32 i0 :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil) d ->
  RL_Tbl_Grp_P v0 (Vint32 i) ->
  id_addrval' (Vptr (v'26, Int.zero)) OSEventTbl os_ucos_h.OS_EVENT = Some v'2 ->
  Int.unsigned i <= 255 -> Int.unsigned i1 <= 65535 ->
  isptr v1 ->
  isptr x2 ->
  struct_type_vallist_match os_ucos_h.OS_EVENT (Vint32 i0 :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil) ->
  H5 |= evsllseg v'16 x2 (v'19 ++
           (Vint32 i0 :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil,
            v0) :: nil) (v'21 ++ d :: nil).
Proof.
  intro.
  inductions v'19; intros.
  destruct_s H5.
  destruct v'21.
(*v'21 is nil*)
  simpl evsllseg in H.
  sep split in H; simpljoin1.
  simpl evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  sep normal.
  sep pauto; eauto.
 
(*v'21 is not nil*)
  simpl evsllseg in H.
  sep split in H.
  simpljoin1; inversion H8.
  destruct v'21.
  simpl evsllseg in H.
  destruct_s H5; simpl in H; simpljoin1; tryfalse.

(*ind case*) 
  rewrite <- app_comm_cons.
  rewrite <- app_comm_cons.
  simpl evsllseg in H.
  destruct a.
  sep normal in H.
  destruct H.
  sep split in H.
  sep remember (1::nil)%nat in H.
  destruct_s H5.
  simpl evsllseg.
  exists x.
  sep split; auto.
  sep pauto.
  eapply IHv'19; eauto.
Qed.

(*
Lemma evsllseg_append_q : forall v'19 v'16 v0 v'21 v1 v2 v3 v4 v'2 v'26 x3 i i1 x2 H5,
  H5 |= evsllseg v'16 (Vptr (v'26, Int.zero)) v'19 v'21 **
        Astruct (v'26, Int.zero) OS_EVENT (V$OS_EVENT_TYPE_Q :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil) ** AOSEventTbl v'2 v0 ** AMsgData v1 v2 v3 v4 ->
  RL_Tbl_Grp_P v0 (Vint32 i) ->
  id_addrval' (Vptr (v'26, Int.zero)) OSEventTbl OS_EVENT = Some v'2 ->
  Int.unsigned i <= 255 -> Int.unsigned i1 <= 65535 ->
  isptr v1 ->
  isptr x2 ->
  H5 |= evsllseg v'16 x2 (v'19 ++
           (V$OS_EVENT_TYPE_Q :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil,
            v0) :: nil) (v'21 ++ DMsgQ v1 v2 v3 v4 :: nil).
Proof.
  intro.
  inductions v'19; intros.
  destruct_s H5.
  destruct v'21.
(*v'21 is nil*)
  simpl evsllseg in H.
  sep split in H; mytac.
  simpl evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AEventData.
  sep normal.
  sep pauto; eauto.
  split; auto.
  pauto.

(*v'21 is not nil*)
  simpl evsllseg in H.
  sep split in H.
  mytac; inversion H7.
  destruct v'21.
  simpl evsllseg in H.
  destruct_s H5; simpl in H; mytac; tryfalse.

(*ind case*) 
  rewrite <- app_comm_cons.
  rewrite <- app_comm_cons.
  simpl evsllseg in H.
  destruct a.
  sep normal in H.
  destruct H.
  sep split in H.
  sep remember (1::nil)%nat in H.
  destruct_s H5.
  simpl evsllseg.
  exists x.
  sep split; auto.
  sep pauto.
  eapply IHv'19; eauto.
Qed.
*)

Lemma ECBList_P_nil : forall l1 l2 m1 m2,
  ECBList_P Vnull Vnull l1 l2 m1 m2 -> l1 = nil /\ l2 = nil /\ m1 = EcbMod.emp.
Proof.
  intros.
  unfolds in H.
  destruct l1.
  simpljoin1.
  auto.
  fold ECBList_P  in H.
  destruct l2;
  simpljoin1; tryfalse.
Qed.


Lemma ECBList_P_append : forall v'13 v'16 v'19 v0 v'21 v1 v'23 v'24 v'26 x3 i i1 x0 x1 x2 s H5 i0 d,
  ECBList_P v'16 (Vptr (v'26, Int.zero)) v'19 v'21 v'23 v'13 ->
  RLH_ECBData_P d x0 ->
  s |= Astruct (v'26, Int.zero) os_ucos_h.OS_EVENT
        (Vint32 i0 :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil) **
        evsllseg v'16 (Vptr (v'26, Int.zero)) v'19 v'21 ** H5 ->
  EcbMod.join (EcbMod.sig (v'26, Int.zero) x0) x1 v'24 ->
  R_ECB_ETbl_P (v'26, Int.zero)
               (Vint32 i0 :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil, v0) v'13 ->
  ECBList_P v'16 x2
     (v'19 ++ (Vint32 i0 :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil, v0) :: nil) (v'21 ++ d :: nil)
     (EcbMod.merge v'23 (EcbMod.sig (v'26, Int.zero) x0)) v'13.
Proof.
  intros.
  gen v'13 v'16 v0 v'21 v1 v'23 v'24.
  gen x2 x1 x0 i i1 x3 v'26 s H5 d.
  gen i0.
  inductions v'19; intros.
  destruct v'21.
  simpl in H; simpljoin1.
  simpl.
  eexists; split; eauto.
  split; auto.
  do 3 eexists.
  split.
  unfolds; simpl; eauto.
  split.
  instantiate (1:=EcbMod.emp).
  instantiate (1:= x0).
  pose proof EcbMod.meq_merge_emp_l (EcbMod.sig (v'26, Int.zero) x0).
  apply EcbMod.meq_eq in H.
  unfold empenv; simpl.
  rewrite H.
  unfolds.
  apply EcbMod.join_comm.
  apply EcbMod.join_emp; auto.
  unfold RLH_ECBData_P in H0.
  auto.
  simpl in H; simpljoin1; tryfalse.
  destruct v'21.
  simpl in H; simpljoin1; tryfalse.
  rewrite <- app_comm_cons.
  rewrite <- app_comm_cons.
  simpl.
  simpl in H; simpljoin1.
  eexists.
  split; eauto.
  split; auto.
  destruct a; simpljoin1.
  do 3 eexists; eauto.
  split; eauto.
  split.
  instantiate (2:=x4).
  instantiate (1:=(EcbMod.merge x5 (EcbMod.sig (v'26, Int.zero) x0))).

  assert(x <> (v'26, Int.zero)).
  simpl evsllseg in H1.
  unfold AEventNode in H1.
  unfold AOSEvent in H1.
  unfold node in H1.
  sep pure.
  destruct H9; destruct x; inverts H9.
  sep lift 5%nat in H1.
  sep remember (1::2::nil)%nat in H1.
  clear -H1. 

  sep lift 2%nat in H1.
  eapply sep_ptr_neq_OS_EVENT; eauto.

  clear - H6 H9.
  apply EcbMod.joinsig_merge_sig; auto.
  split; auto.

  unfold evsllseg in H1; fold evsllseg in H1.
  sep normal in H1.
  destruct H1.
  sep pure.
  sep remember (1::nil)%nat in H1.
  destruct_s s.
  simpl in H1; simpljoin1.
  sep lifts (2::1::nil)%nat in H15.
  eapply IHv'19; eauto.
  rewrite H in H9.
  inverts H9.
  eauto.
Qed.



(*
Lemma ECBList_P_append : forall v'13 v'16 v'19 v0 v'21 v1 v2 v3 v4 v'23 v'24 v'26 x3 i i1 x0 x1 x2 s H5,
  ECBList_P v'16 (Vptr (v'26, Int.zero)) v'19 v'21 v'23 v'13 ->
  RLH_ECBData_P (DMsgQ v1 v2 v3 v4) x0 ->
  s |= Astruct (v'26, Int.zero) OS_EVENT
        (V$OS_EVENT_TYPE_Q :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil) **
        evsllseg v'16 (Vptr (v'26, Int.zero)) v'19 v'21 ** H5 ->
  EcbMod.join (EcbMod.sig (v'26, Int.zero) x0) x1 v'24 ->
  R_ECB_ETbl_P (v'26, Int.zero)
               (V$OS_EVENT_TYPE_Q :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil, v0) v'13 ->
  ECBList_P v'16 x2
     (v'19 ++ (V$OS_EVENT_TYPE_Q :: Vint32 i :: Vint32 i1 :: v1 :: x3 :: x2 :: nil, v0) :: nil) (v'21 ++ DMsgQ v1 v2 v3 v4 :: nil)
     (EcbMod.merge v'23 (EcbMod.sig (v'26, Int.zero) x0)) v'13.
Proof.
  intros.
  gen v'13 v'16 v0 v'21 v1 v2 v3 v4 v'23 v'24.
  gen x2 x1 x0 i i1 x3 v'26 s H5.
  inductions v'19; intros.
  destruct v'21.
  simpl in H; mytac.
  simpl.
  eexists; split; eauto.
  split; auto.
  do 3 eexists.
  split.
  unfolds; simpl; eauto.
  split.
  instantiate (1:=EcbMod.emp).
  instantiate (1:= x0).
  pose proof EcbMod.meq_merge_emp_l (EcbMod.sig (v'26, Int.zero) x0).
  apply EcbMod.meq_eq in H.
  rewrite H.
  unfolds.
  apply EcbMod.join_comm.
  apply EcbMod.join_emp; auto.
  unfold RLH_ECBData_P in H0.
  auto.
  simpl in H; mytac; tryfalse.
  destruct v'21.
  simpl in H; mytac; tryfalse.
  rewrite <- app_comm_cons.
  rewrite <- app_comm_cons.
  simpl.
  simpl in H; mytac.
  eexists.
  split; eauto.
  split; auto.
  destruct a; mytac.
  do 3 eexists; eauto.
  split; eauto.
  split.
  instantiate (2:=x4).
  instantiate (1:=(EcbMod.merge x5 (EcbMod.sig (v'26, Int.zero) x0))).

  assert(x <> (v'26, Int.zero)).
  simpl evsllseg in H1.
  unfold AEventNode in H1.
  unfold AOSEvent in H1.
  unfold node in H1.
  sep pure.
  destruct H9; destruct x; inverts H9.
  sep lift 5%nat in H1.
  sep remember (1::2::nil)%nat in H1.
  clear -H1. 

  sep lift 2%nat in H1.
  eapply sep_ptr_neq_OS_EVENT; eauto.

  clear - H6 H9.
  apply EcbMod.joinsig_merge_sig; auto.
  split; auto.
  unfold evsllseg in H1; fold evsllseg in H1.
  sep normal in H1.
  destruct H1.
  sep pure.
  sep remember (1::nil)%nat in H1.
  destruct_s s.
  simpl in H1; mytac.
  sep lifts (2::1::nil)%nat in H15.
  eapply IHv'19; eauto.
  rewrite H in H9.
  inverts H9.
  eauto.
Qed.
*)
