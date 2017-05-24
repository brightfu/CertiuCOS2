Require Import lemmasfortoptheo. 
Require Import ucos_include.
Require Import oscorrectness. 

Import DeprecatedTactic.

Lemma join_get_set_eq:
  forall (A B T:Type) (X:PermMap A B T) O1 O2 O O' a b b',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    join (set O1 a b') O2 O' ->
    O' = set O a b'.
  intros.
  assert (join (set O1 a b') O2 (set O a b')).
  {
    clear H2.
    geat.
  }
  eapply map_join_deter; eauto.
Qed.

Lemma join_get_set_eq_2:
  forall (A B T:Type) (X:PermMap A B T) O1 O2 O O' a b b' a' c c',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c -> 
    join (set (set O1 a b') a' c') O2 O' ->
    O' = set (set O a b') a' c'.
  intros.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.

Lemma join_get_set_eq_3
: forall (A B T : Type) (X : PermMap A B T) (O1 O2 O O' : T) 
         (a : A) (b b' : B) (a' : A) (c c' : B) a'' d d',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c ->
    get O1 a'' = Some d ->
    join (set ((set (set O1 a b') a' c')) a'' d') O2 O' -> O' = set (set (set O a b') a' c') a'' d'.
  intros.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed. 

Definition WAIT_OWNER t t_owner tls els:=
  exists qid p v m p_owner wl p_q,
    TcbMod.get tls t = Some (p,wait (os_stat_mutexsem qid) v,m) /\
    EcbMod.get els qid = Some (absmutexsem p_q (Some (t_owner,p_owner)),wl).

Inductive WAIT_CHAIN: tid -> tid -> TcbMod.map ->  EcbMod.map -> Prop :=
| wait_O: forall t t_owner tls els, WAIT_OWNER t t_owner tls els /\ t <> t_owner  ->
                     WAIT_CHAIN t t_owner tls els
| wait_S: forall t t_owner tls els t', WAIT_OWNER t t' tls els -> WAIT_CHAIN t' t_owner tls els ->
                     WAIT_CHAIN t t_owner tls els.

Definition IS_OWNER t_owner qid els :=
  exists p_q p_owner wl, EcbMod.get els qid =  Some (absmutexsem p_q (Some (t_owner,p_owner)),wl).

Definition IS_OWNER_P t_owner qid els p_owner:=
  exists p_q wl, EcbMod.get els qid =  Some (absmutexsem p_q (Some (t_owner,p_owner)),wl).

Definition IS_WAITING t els:=
  exists qid p_q owner wl, EcbMod.get els qid =  Some (absmutexsem p_q owner,wl) /\ In t wl.

Definition IS_WAITING_E t eid els:=
  exists p_q owner wl, EcbMod.get els eid =  Some (absmutexsem p_q owner,wl) /\ In t wl.

Definition NO_NEST_PENDING tls els:=
  forall t qid,
    TcbMod.get tls t <> None ->
    IS_OWNER t qid els ->
    (~ IS_WAITING t els /\ ~ exists qid', qid <> qid' /\ IS_OWNER t qid' els).


Definition NO_NEST_PENDING_O O:=
  forall els tls,
    OSAbstMod.get O absecblsid = Some (absecblist els) ->
    OSAbstMod.get O abtcblsid = Some (abstcblist tls) ->
    NO_NEST_PENDING tls els.

Definition GET_OP t tls els p :=
  TcbMod.get tls t <> None ->
  (exists qid, IS_OWNER_P t qid els p) \/
  ((~ exists qid, IS_OWNER t qid els) /\ exists st msg, TcbMod.get tls t = Some (p,st,msg)).


Definition HighestRdy tls t :=
  exists prio msg0,
    TcbMod.get tls t = Some (prio, rdy, msg0) /\
    (forall (i : tid) (prio' : priority) (msg' : msg),
       i <> t ->
       TcbMod.get tls i = Some (prio', rdy, msg') ->
       Int.ltu prio prio' = true).


Definition WEAK_PIF (O:osabst) :=
  forall els tls ct p_ct,
    OSAbstMod.get O absecblsid = Some (absecblist els) ->
    OSAbstMod.get O abtcblsid = Some (abstcblist tls) ->
    OSAbstMod.get O curtid = Some (oscurt ct) ->
    GET_OP ct tls els p_ct ->
    NO_NEST_PENDING tls els ->
    HighestRdy tls ct ->
    ~ (exists eid, IS_OWNER ct eid els) ->
    forall t p_t,
      t <> ct ->
      TcbMod.get tls t <> None ->
      GET_OP t tls els p_t ->
      IS_WAITING t els ->
      Int.ltu p_ct p_t = true.

Definition O_PI tls els :=
  exists t t_owner p p_owner st st_owner msg msg_owner,
    WAIT_OWNER t t_owner tls els /\
    TcbMod.get tls t = Some (p,st,msg) /\
    TcbMod.get tls t_owner = Some (p_owner,st_owner,msg_owner) /\
    Int.ltu p p_owner = true.

Definition O_PIF tls els := ~ O_PI tls els.

Definition OLD_PIF O:=
  forall els tls,
    OSAbstMod.get O absecblsid = Some (absecblist els) ->
    OSAbstMod.get O abtcblsid = Some (abstcblist tls) ->
    O_PIF tls els.


Definition PIF (O:osabst) :=
  forall els tls ct p_ct,
    OSAbstMod.get O absecblsid = Some (absecblist els) ->
    OSAbstMod.get O abtcblsid = Some (abstcblist tls) ->
    OSAbstMod.get O curtid = Some (oscurt ct) ->
    GET_OP ct tls els p_ct ->
    HighestRdy tls ct ->
    ~ (exists eid, IS_OWNER ct eid els) -> 
    forall t p_t,
      t <> ct ->
      TcbMod.get tls t <> None ->
      GET_OP t tls els p_t ->
      IS_WAITING t els ->
      Int.ltu p_ct p_t = true.



Definition PREEMP O :=
  forall ct tls ,
    OSAbstMod.get O abtcblsid = Some (abstcblist tls) ->
    OSAbstMod.get O curtid = Some (oscurt ct) ->
    HighestRdy tls ct.


Definition api_spec_list' := 
  (OSMutexAccept, mutexaccapi)
    :: (OSMutexCreate, mutexcreapi)
    :: (OSMutexDel, mutexdelapi)
    :: (OSMutexPend, mutexpendapi)
    :: (OSMutexPost, mutexpostapi)
    :: nil.

Definition api_spec':= convert_api_spec api_spec_list'.

Definition os_spec' := (api_spec',int_spec,GetHPrio).


Definition GOOD_API_CODE O T :=
  exists C t,
    OSAbstMod.get O curtid = Some (oscurt t) /\
    TasksMod.get T t = Some C /\
    (
      (exists ke ks vl, C = (curs (hapi_code (spec_prim vl mutexacc_succ)), (ke,ks))) \/
      (exists ke ks vl, C = (curs (hapi_code (spec_prim vl mutexcre_succ)), (ke,ks))) \/
      (exists ke ks vl, C = (curs (hapi_code (spec_prim vl mutexdel_succ)), (ke,ks))) \/
      (exists ke ks vl, C = (curs (hapi_code (spec_prim vl mutexpend_get_succ)), (ke,ks))) \/
      (exists ke ks vl s, C = (curs (hapi_code (mutexpend_block_no_lift (|vl|);;s)), (ke,ks))) \/
      (exists ke ks vl s, C = (curs (hapi_code (mutexpend_block_lift (|vl|);;s)), (ke,ks))) \/
      (exists ke ks vl, C = (curs (hapi_code (mutexpost_nowt_return_prio_succ (|vl|))), (ke,ks))) \/
      (exists ke ks vl, C = (curs (hapi_code (mutexpost_nowt_no_return_prio_succ (|vl|))), (ke,ks))) \/
      (exists ke ks vl s, C = (curs (hapi_code (mutexpost_exwt_return_prio_succ (|vl|);;s)), (ke,ks))) \/
      (exists ke ks vl s, C = (curs (hapi_code (mutexpost_exwt_no_return_prio_succ (|vl|);;s)), (ke,ks)))\/
      (exists ke ks s, C = (curs (hapi_code (timetick_spec (|nil|);;s)), (ke,ks)))\/
      (exists ke ks s, C = (curs (hapi_code (sched;;s)), (ke,ks)))
    ).

Definition rdy_notin_wl tls els :=
  (forall t p m, TcbMod.get tls t = Some (p,rdy,m) -> ~ IS_WAITING t els) /\
  (forall t p m eid tm,TcbMod.get tls t = Some (p,wait (os_stat_mutexsem eid) tm,m) -> IS_WAITING_E t eid els)/\
  (forall t eid,  IS_WAITING_E t eid els -> exists p tm m, TcbMod.get tls t = Some (p,wait (os_stat_mutexsem eid) tm,m)) .

Definition not_in_two_wl els:= forall t,
                                 ~ exists eid eid', eid <> eid' /\ IS_WAITING_E t eid els /\ IS_WAITING_E t eid' els.

Definition owner_prio_prop tls els:=
  forall t p st m eid pe po l,
    TcbMod.get tls t = Some (p,st,m) ->
    EcbMod.get els eid = Some (absmutexsem pe (Some (t,po)), l) ->
    (p = pe \/ p = po) /\ Int.ltu pe po =true.

Definition task_stat_prop tls:=
  forall t p st m,
    TcbMod.get tls t = Some (p,st,m) ->
    st = rdy \/ (exists eid tm, st = wait (os_stat_mutexsem eid) tm).

Definition op_p_prop tls els :=
  forall t st p m op,
    TcbMod.get tls t = Some (p,st,m) ->
    GET_OP t tls els op ->
    Int.ltu p op = true \/ Int.eq p op = true.

Definition wait_prop tls els:=
  forall t p m eid tm,
    TcbMod.get tls t = Some (p,wait (os_stat_mutexsem eid) tm,m) ->
    exists t' po m, IS_OWNER t' eid els /\ TcbMod.get tls t' = Some (po,rdy,m) /\ Int.ltu po p = true /\
                    (forall op, GET_OP t tls els op -> op = p).

Definition no_owner_prio_prop tls els:=
  forall t p st m  op,
    TcbMod.get tls t = Some (p,st,m) ->
    (~exists eid, IS_OWNER t eid els) ->
    GET_OP t tls els op ->
    op = p.

    
Definition GOOD_ST O :=
  forall tls els,
    OSAbstMod.get O absecblsid = Some (absecblist els) ->
    OSAbstMod.get O abtcblsid = Some (abstcblist tls) ->
    rdy_notin_wl tls els /\
    owner_prio_prop tls els /\
    task_stat_prop tls/\
    op_p_prop tls els/\
    wait_prop tls els/\
    no_owner_prio_prop tls els.

Lemma joinsig_joinsig_eq:
  forall tls tls' a b x y,
    TcbMod.join tls (TcbMod.sig a b ) tls' ->
    TcbMod.join tls (TcbMod.sig x y) tls' ->
    a = x /\ b = y.
Proof.
  intros.
  pose proof H a.
  pose proof H0 a.
  rewrite TcbMod.get_sig_some in H1.
  destruct (TcbMod.get tls a);
    destruct (TcbMod.get (TcbMod.sig x y) a) eqn : eq1;
    destruct (TcbMod.get tls' a); tryfalse; substs.
  rewrite TcbMod.sig_sem in eq1.
  destruct (tidspec.beq x a) eqn : eq2; tryfalse.
  inverts eq1.
  apply tidspec.beq_true_eq in eq2; substs.
  auto.
Qed.

Lemma osabst_get_get_disj_eq : 
  forall O x y Of z,
    OSAbstMod.get O x = Some y ->
    OSAbstMod.get (OSAbstMod.merge O Of) x =
    Some z ->
    OSAbstMod.disj O Of -> y = z.
Proof.
  intros.
  rewrite OSAbstMod.merge_sem in H0.
  rewrite H in H0.
  destruct (OSAbstMod.get Of x); inverts H0; auto.
Qed.

Lemma osabst_get_get_disj_get : 
  forall O x y Of ,
    OSAbstMod.get O x = Some y ->
    
    OSAbstMod.disj O Of ->
    OSAbstMod.get (OSAbstMod.merge O Of) x =
    Some y.
Proof.
  intros.
  rewrite OSAbstMod.merge_sem.
  rewrite H.
  destruct(OSAbstMod.get Of x); auto.
Qed.


(*
Lemma abst_disj_merge_eq_eq:
  forall O Of O',OSAbstMod.disj O Of -> OSAbstMod.merge O Of = OSAbstMod.merge O' Of -> eqdomO O O' -> O = O'.
Proof.
  intros.
  apply OSAbstMod.extensionality; intros.
  assert(OSAbstMod.get (OSAbstMod.merge O Of) a = OSAbstMod.get (OSAbstMod.merge O' Of) a).
  rewrite H0; auto.
  do 2 rewrite OSAbstMod.merge_sem in H2.
  destruct H1 as (H1&Hx).
  pose proof H1 a; unfold OSAbstMod.indom in H3; destruct H3.
  pose proof H a.
  destruct (OSAbstMod.get O a);
  destruct (OSAbstMod.get O' a);
  destruct (OSAbstMod.get Of a);
  tryfalse; auto.
  assert (exists b1, Some b = Some b1) by eauto.
  apply H1 in H6.
  mytac; tryfalse.
Qed.
*)
Lemma spec_ext : forall f1 f2 : vallist -> osabst -> option val * osabst -> Prop,
                   f1 = f2 -> (forall vl O1 rst, f1 vl O1 rst = f2 vl O1 rst).
Proof.
  intros.
  substs.
  auto.
Qed.

Lemma prop_eq_impl : forall P Q : Prop, P = Q -> (P -> Q).
Proof.
  intros.
  substs.
  auto.
Qed.

Definition addrval_a := (xI xH, Int.one).
Definition tid_a := (xH, Int.zero).

Lemma no_nest_pending_set_none:
  forall tls p_ct st msg els eid ct p_e wl x6 x7,
    TcbMod.get tls ct = Some (p_ct, st, msg) ->
    EcbMod.get els eid = Some (absmutexsem x6 None, x7) ->
    NO_NEST_PENDING tls (EcbMod.set els eid (absmutexsem p_e (Some (ct, p_ct)), wl)) ->
    ~ (exists qid, IS_OWNER ct qid els).
Proof.
  intros.
  unfolds in H1.
  assert (TcbMod.get tls ct <> None).
  intro; rewrite H in H2; tryfalse.
  assert (IS_OWNER ct eid
         (EcbMod.set els eid (absmutexsem p_e (Some (ct, p_ct)), wl))).
  unfolds.
  rewrite EcbMod.set_a_get_a; eauto.
  apply tidspec.eq_beq_true; auto.
  lets Hx: H1 H2 H3; clear H1 H2 H3; mytac.
  intro; apply H2; mytac.
  destruct (tidspec.beq eid x) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H3; mytac.
  rewrite H0 in H3; tryfalse.
  exists x; mytac.
  apply tidspec.beq_false_neq; auto.
  unfolds.
  rewrite EcbMod.set_a_get_a'; auto.
Qed.

Lemma no_nest_pending_set_prio_eq:
  forall tls x4 x3 x6 ct x8 x7 x9 x10 p_ct,
    NO_NEST_PENDING tls (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, x8)), x7)) ->
    GET_OP ct tls (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, x8)), x7)) p_ct ->
    TcbMod.get tls ct = Some (x8, x9, x10) ->
    p_ct = x8.
Proof.
  intros.
  unfolds in H.
  unfolds in H0.
  assert(TcbMod.get tls ct <> None).
  intro; rewrite H1 in H2; tryfalse.
  assert(IS_OWNER ct x3 (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, x8)), x7))).
  unfolds; do 3 eexists.
  rewrite EcbMod.set_a_get_a; eauto.
  apply tidspec.eq_beq_true; auto.
  lets Hx1: H H2 H3.
  lets Hx2: H0 H2.
  clear H H0 H2 H3.
  destruct Hx2; mytac.
  unfolds in H; mytac.
  destruct (tidspec.beq x3 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H; inverts H; auto.
  false; apply H2.
  exists x; unfold IS_OWNER.
  rewrite EcbMod.set_a_get_a'; auto.
  rewrite EcbMod.set_a_get_a' in H; auto.
  apply tidspec.beq_false_neq in eq1.
  eauto.

  false; apply H.
  unfold IS_OWNER.
  do 4 eexists.
  rewrite EcbMod.set_a_get_a; eauto.
  apply tidspec.eq_beq_true; auto.
Qed.


Lemma no_nest_pending_set_hold:
  forall tls x4 x3 x6 ct x8 x7,
    NO_NEST_PENDING tls
                    (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, x8)), x7)) ->
    EcbMod.get x4 x3 = Some (absmutexsem x6 None, x7) ->
    NO_NEST_PENDING tls x4.
Proof.
  intros.
  unfolds; intros.
  destruct(tidspec.beq x3 qid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfolds in H2; do 3 destruct H2.
  rewrite H0 in H2; tryfalse.

  assert(IS_OWNER t qid (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, x8)), x7))).
  unfolds; rewrite EcbMod.set_a_get_a'; auto.
  lets Hx: H H1 H3; mytac.
  intro; apply H4.
  unfolds in H6; mytac.
  destruct (tidspec.beq x3 x) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  unfolds; do 4 eexists.
  rewrite EcbMod.set_a_get_a; eauto.
  rewrite H0 in H6; inverts H6; eauto.
  unfolds; do 4 eexists.
  rewrite EcbMod.set_a_get_a'; eauto.

  intro; apply H5; mytac.
  exists x; mytac; auto.
  unfolds in H7; mytac.
  destruct (tidspec.beq x3 x) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  unfolds; do 3 eexists.
  rewrite EcbMod.set_a_get_a; eauto.
  rewrite H7 in H0; inverts H0.
  unfolds; do 3 eexists.
  rewrite EcbMod.set_a_get_a'; eauto.
  Grab Existential Variables.
  auto.
  apply Int.zero.
  apply Int.zero.
Qed.

Lemma set_neq_getop_eq:
  forall t ct tls x4 x3 x6 x7 x8 p_t,
    t <> ct ->
    TcbMod.get tls t <> None ->
    EcbMod.get x4 x3 = Some (absmutexsem x6 None, x7) ->
    GET_OP t tls (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, x8)), x7)) p_t ->
    GET_OP t tls x4 p_t.
Proof.
  intros.
  lets Hx: H2 H0.
  unfolds; intros.
  destruct Hx; mytac.
  left.
  unfolds in H4; mytac.
  destruct (tidspec.beq x3 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; inverts H4; tryfalse.
  auto.
  rewrite EcbMod.set_a_get_a' in H4; auto.
  exists x; unfolds; eauto.

  right.
  split.
  intro; apply H4; mytac.
  destruct (tidspec.beq x3 x1) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfolds in H6; mytac.
  rewrite H1 in H6; tryfalse.
  exists x1.
  unfolds; rewrite EcbMod.set_a_get_a'; auto.
  eauto.
Qed.


Lemma iswaiting_set_ct_neq_hold:
  forall t ct tls x4 x3 x6 x7 xx yy,
    t <> ct ->
    TcbMod.get tls t <> None ->
    EcbMod.get x4 x3 = Some (absmutexsem x6 xx, x7) ->
    IS_WAITING t (EcbMod.set x4 x3 (absmutexsem x6 yy, x7)) ->
    IS_WAITING t x4.
Proof.
  intros.
  unfolds in H2; mytac.
  unfolds.
  destruct (tidspec.beq x3 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H2; auto.
  inverts H2.
  do 4 eexists; eauto.

  rewrite EcbMod.set_a_get_a' in H2; auto.
  do 4 eexists; eauto.
Qed.

Lemma ecb_joinsig_get_eq:
  forall x6 x3 x4 els x8 a0 x9 x,
    EcbMod.joinsig x6 (absmutexsem x3 None, nil) x4 els ->
    EcbMod.get x4 x = Some (absmutexsem x9 a0, x8) ->
    EcbMod.get els x = Some (absmutexsem x9 a0, x8).
Proof.
  intros.
  unfolds in H; pose proof H x.
  rewrite H0 in H1.
  destruct(EcbMod.get (EcbMod.sig x6 (absmutexsem x3 None, nil)) x); tryfalse.
  destruct(EcbMod.get els x); tryfalse.
  rewrite H1; auto.
Qed.

Lemma getop_cre_hold:
  forall x6 x3 x4 els tls ct p_ct,
    GET_OP ct tls els p_ct ->
    EcbMod.joinsig x6 (absmutexsem x3 None, nil) x4 els ->
    GET_OP ct tls x4 p_ct.
Proof.
  intros.
  unfolds; intros.
  lets Hx: H H1.
  destruct Hx; mytac.
  left.
  destruct (tidspec.beq x6 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfolds in H2; mytac.
  pose proof H0 x.
  rewrite H2 in H3.
  rewrite EcbMod.get_sig_some in H3.
  destruct (EcbMod.get x4 x); tryfalse.
  pose proof H0 x.
  rewrite EcbMod.get_sig_none in H3.
  destruct (EcbMod.get x4 x) eqn : eq2;
    destruct (EcbMod.get els x) eqn : eq3;
    tryfalse; substs.
  unfolds in H2; mytac.
  rewrite H2 in eq3; inverts eq3.
  exists x; unfolds; eauto.
  unfolds in H2; mytac.
  rewrite H2 in eq3; tryfalse.
  apply tidspec.beq_false_neq; auto.

  right. 
  split.
  intro; apply H2; mytac.
  unfolds in H4; mytac.
  pose proof H0 x1.
  rewrite H4 in H5.
  destruct (tidspec.beq x6 x1) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H5; tryfalse.
  rewrite EcbMod.get_sig_none in H5.
  destruct (EcbMod.get els x1) eqn : eq2; tryfalse.
  exists x1; unfolds; do 3 eexists.
  inverts H5.
  eauto.
  apply tidspec.beq_false_neq; auto.

  eauto.
Qed.


Lemma no_nest_pending_cre_hold:
  forall tls els x6 x3 x4,
    NO_NEST_PENDING tls els ->
    EcbMod.joinsig x6 (absmutexsem x3 None, nil) x4 els ->
    NO_NEST_PENDING tls x4.
Proof.
  intros.
  unfolds; intros.
  assert(IS_OWNER t qid els).
  unfolds in H2; mytac.
  pose proof H0 qid.
  destruct (tidspec.beq x6 qid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H3.
  rewrite H2 in H3; tryfalse.
  rewrite EcbMod.get_sig_none in H3.
  rewrite H2 in H3.
  destruct (EcbMod.get els qid) eqn : eq2; tryfalse; inverts H3.
  unfolds; do 3 eexists; eauto.
  apply tidspec.beq_false_neq; auto.

  lets Hx: H H1 H3; mytac.
  intro; apply H4.
  unfolds in H6; mytac.
  pose proof H0 x.
  rewrite H6 in H8.
  destruct (tidspec.beq x6 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H8; tryfalse.
  rewrite EcbMod.get_sig_none in H8.
  destruct (EcbMod.get els x) eqn : eq2; tryfalse.
  inverts H8.
  unfolds; do 3 eexists; eauto.
  apply tidspec.beq_false_neq; auto.

  intro; apply H5; mytac.
  exists x; split; auto.
  unfolds in H7; mytac.
  pose proof H0 x.
  rewrite H7 in H8.
  destruct (tidspec.beq x6 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H8; tryfalse.
  rewrite EcbMod.get_sig_none in H8.
  destruct (EcbMod.get els x) eqn : eq2; tryfalse.
  inverts H8.
  unfolds; do 3 eexists; eauto.
  apply tidspec.beq_false_neq; auto.
Qed.

Lemma iswaiting_cre_hold:
  forall t x4 x3 x6 els,
    EcbMod.joinsig x6 (absmutexsem x3 None, nil) x4 els ->
    IS_WAITING t els ->
    IS_WAITING t x4.
Proof.
  intros.
  unfolds in H0; mytac.
  pose proof H x.
  rewrite H0 in H2.
  destruct (tidspec.beq x6 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H2; tryfalse.
  destruct (EcbMod.get x4 x) eqn: eq2; tryfalse.
  inverts H2.
  unfolds in H1; tryfalse.
  rewrite EcbMod.get_sig_none in H2.
  destruct (EcbMod.get x4 x) eqn: eq2; tryfalse.
  inverts H2.
  unfolds; do 3 eexists; eauto.
  apply tidspec.beq_false_neq; auto.
Qed.  


Lemma ecb_join_get_eq':
  forall x6 x3 x4 els x7 x8 a0 x9 x,
    EcbMod.join els (EcbMod.sig x3 (absmutexsem x6 None, nil)) x4 ->
    EcbMod.get x4 x = Some (absmutexsem x9 (Some (a0, x7)), x8) ->
    EcbMod.get els x = Some (absmutexsem x9 (Some (a0, x7)), x8).
Proof.
  intros.
  pose proof H x.
  rewrite H0 in H1.
  destruct (EcbMod.get (EcbMod.sig x3 (absmutexsem x6 None, nil)) x) eqn : eq1;
    destruct (EcbMod.get els x) eqn : eq2; tryfalse; substs; auto.
  rewrite EcbMod.sig_sem in eq1.
  destruct (tidspec.beq x3 x); tryfalse.
Qed.

Lemma getop_del_hold:
  forall ct tls els p_ct x3 x6 x4,
    GET_OP ct tls els p_ct ->
    EcbMod.join els (EcbMod.sig x3 (absmutexsem x6 None, nil)) x4 ->
    GET_OP ct tls x4 p_ct.
Proof.
  intros.
  unfolds; intros.
  lets Hx: H H1.
  destruct Hx; mytac.
  left.
  destruct (tidspec.beq x3 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfolds in H2; mytac.
  pose proof H0 x.
  rewrite H2 in H3.
  rewrite EcbMod.get_sig_some in H3; tryfalse.
  pose proof H0 x.
  rewrite EcbMod.get_sig_none in H3.
  destruct (EcbMod.get x4 x) eqn : eq2;
    destruct (EcbMod.get els x) eqn : eq3;
    tryfalse; substs.
  unfolds in H2; mytac.
  rewrite H2 in eq3; inverts eq3.
  exists x; unfolds; eauto.
  unfolds in H2; mytac.
  rewrite H2 in eq3; tryfalse.
  apply tidspec.beq_false_neq; auto.

  right. 
  split.
  intro; apply H2; mytac.
  unfolds in H4; mytac.
  pose proof H0 x1.
  rewrite H4 in H5.
  destruct (tidspec.beq x3 x1) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H5.
  destruct (EcbMod.get els x1) eqn : eq2; tryfalse.
  rewrite EcbMod.get_sig_none in H5.
  destruct (EcbMod.get els x1) eqn : eq2; tryfalse.
  substs.
  exists x1; unfolds; do 3 eexists.
  eauto.
  apply tidspec.beq_false_neq; auto.

  eauto.
Qed.


Lemma no_nest_pending_del:
  forall tls els x3 x6 x4,
    NO_NEST_PENDING tls els ->
    EcbMod.join els (EcbMod.sig x3 (absmutexsem x6 None, nil)) x4 ->
    NO_NEST_PENDING tls x4.
Proof.
  intros.
  unfolds; intros.
  assert(IS_OWNER t qid els).
  unfolds in H2; mytac.
  pose proof H0 qid.
  destruct (tidspec.beq x3 qid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H3.
  rewrite H2 in H3.
  destruct (EcbMod.get els qid) eqn : eq2; tryfalse.
  rewrite EcbMod.get_sig_none in H3.
  rewrite H2 in H3.
  destruct (EcbMod.get els qid) eqn : eq2; tryfalse; inverts H3.
  unfolds; do 3 eexists; eauto.
  apply tidspec.beq_false_neq; auto.

  lets Hx: H H1 H3; mytac.
  intro; apply H4.
  unfolds in H6; mytac.
  pose proof H0 x.
  rewrite H6 in H8.
  destruct (tidspec.beq x3 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H8.
  destruct (EcbMod.get els x) eqn : eq2; tryfalse.
  inverts H8.
  simpl in H7; tryfalse.
  rewrite EcbMod.get_sig_none in H8.
  destruct (EcbMod.get els x) eqn : eq2; tryfalse.
  inverts H8.
  unfolds; do 3 eexists; eauto.
  apply tidspec.beq_false_neq; auto.

  intro; apply H5; mytac.
  exists x; split; auto.
  unfolds in H7; mytac.
  pose proof H0 x.
  rewrite H7 in H8.
  destruct (tidspec.beq x3 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H8.
  destruct (EcbMod.get els x) eqn : eq2; tryfalse.
  rewrite EcbMod.get_sig_none in H8.
  destruct (EcbMod.get els x) eqn : eq2; tryfalse.
  inverts H8.
  unfolds; do 3 eexists; eauto.
  apply tidspec.beq_false_neq; auto.
Qed.

Lemma iswaiting_del_hold:
  forall t x4 x3 x6 els,
    EcbMod.join els (EcbMod.sig x3 (absmutexsem x6 None, nil)) x4 ->
    IS_WAITING t els ->
    IS_WAITING t x4.
Proof.
  intros.
  unfolds in H0; mytac.
  pose proof H x.
  rewrite H0 in H2.
  destruct (tidspec.beq x3 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H2; tryfalse.
  rewrite EcbMod.get_sig_none in H2.
  destruct (EcbMod.get x4 x) eqn: eq2; tryfalse.
  inverts H2.
  unfolds; do 4 eexists; eauto.
  apply tidspec.beq_false_neq; auto.
Qed.


Lemma pend_no_lift_getop:
  forall tls ct x12 x2 els x x8 x9 x10 x7 x0 t p_t,
    TcbMod.get tls ct = Some (x12, rdy, x2) ->
    EcbMod.get els x = Some (absmutexsem x8 (Some (x9, x10)), x7) -> 
    GET_OP t (TcbMod.set tls ct (x12, wait (os_stat_mutexsem x) x0, Vnull))
           (EcbMod.set els x (absmutexsem x8 (Some (x9, x10)), ct :: x7)) p_t ->
    GET_OP t tls els p_t.
Proof.
  intros.
  unfolds; intros.
  assert(TcbMod.get (TcbMod.set tls ct (x12, wait (os_stat_mutexsem x) x0, Vnull)) t <> None).
  destruct (tidspec.beq ct t) eqn : eq1.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  apply H1 in H3.
  destruct H3; mytac.
  left.
  unfolds in H3; mytac.
  destruct (tidspec.beq x x1) eqn : eq1.
  rewrite EcbMod.set_a_get_a in H3; auto; inverts H3.
  exists x; unfolds; do 2 eexists; eauto.

  rewrite EcbMod.set_a_get_a' in H3; auto.
  exists x1; unfolds; do 2 eexists; eauto.

  right.
  split.
  intro; apply H3; mytac.
  unfolds in H5; mytac.
  destruct (tidspec.beq x x4) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  rewrite H0 in H5; inverts H5.
  eexists; unfolds; do 3 eexists.
  rewrite EcbMod.set_a_get_a; eauto.
  eexists; unfolds.
  do 3 eexists; rewrite EcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq ct t) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H4; auto.
  inverts H4; eauto.

  rewrite TcbMod.set_a_get_a' in H4; eauto.
Qed.


Lemma pend_no_lift_nnp:
  forall tls ct x12 x2 els x x8 x9 x10 x7 x0,
    TcbMod.get tls ct = Some (x12, rdy, x2) ->
    EcbMod.get els x = Some (absmutexsem x8 (Some (x9, x10)), x7) -> 
    NO_NEST_PENDING (TcbMod.set tls ct (x12, wait (os_stat_mutexsem x) x0, Vnull))
                    (EcbMod.set els x (absmutexsem x8 (Some (x9, x10)), ct :: x7)) ->
    NO_NEST_PENDING tls els.
Proof.
  intros.
  unfolds; intros.
  assert(TcbMod.get (TcbMod.set tls ct (x12, wait (os_stat_mutexsem x) x0, Vnull)) t <> None).
  destruct (tidspec.beq ct t) eqn : eq1.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  assert(IS_OWNER t qid (EcbMod.set els x (absmutexsem x8 (Some (x9, x10)), ct :: x7))).
  unfolds in H3; mytac.
  destruct (tidspec.beq x qid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H0 in H3; inverts H3.
  unfolds.
  rewrite EcbMod.set_a_get_a; auto.
  eauto.
  unfolds.
  rewrite EcbMod.set_a_get_a'; eauto.

  lets Hx: H1 H4 H5; mytac.
  intro; apply H6; mytac.
  unfolds in H8; mytac.
  unfolds.
  destruct (tidspec.beq x x1) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  do 4 eexists; rewrite EcbMod.set_a_get_a.
  rewrite H0 in H8; inverts H8.
  split; eauto.
  destruct (tidspec.beq t ct) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  simpl; auto.
  simpl; right; auto.
  eauto.
  do 4 eexists; rewrite EcbMod.set_a_get_a'; eauto.

  intro; apply H7; mytac.
  exists x1.
  split; auto.
  unfolds in H9; mytac.
  destruct (tidspec.beq x x1) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfolds; do 3 eexists; rewrite EcbMod.set_a_get_a; auto.
  rewrite H9 in H0; inverts H0; eauto.

  unfolds; do 3 eexists; rewrite EcbMod.set_a_get_a'; eauto.
Qed.


Lemma pend_no_lift_iswating:
  forall t ct els x x8 x9 x10 x7,
    t <> ct ->
    EcbMod.get els x = Some (absmutexsem x8 (Some (x9, x10)), x7) ->
    IS_WAITING t (EcbMod.set els x (absmutexsem x8 (Some (x9, x10)), ct :: x7)) ->
    IS_WAITING t els.
Proof.
  intros.
  unfolds in H1; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto.
  inverts H1.
  unfolds; do 4 eexists.
  split; eauto.
  simpl in H2; destruct H2; tryfalse; auto.

  rewrite EcbMod.set_a_get_a' in H1; auto.
  unfolds; do 4 eexists.
  split; eauto.
Qed.

Lemma tcb_get_set_neq_none:
  forall t ct x tls,
    t <> ct ->
    TcbMod.get (TcbMod.set tls ct x) t <> None ->
    TcbMod.get tls t <> None.
Proof.
  intros.
  rewrite TcbMod.set_a_get_a' in H0; auto.
  apply tidspec.neq_beq_false; auto.
Qed.

Lemma pend_lift_nnp:
  forall tls ct x11 x12 x2 els x x8 x9 x10 x0 x13 x14 x15,
    TcbMod.get tls ct = Some (x13, rdy, x2) ->
    TcbMod.get tls x10 = Some (x12, x14, x15) ->
    EcbMod.get els x = Some (absmutexsem x9 (Some (x10, x11)), x8) -> 
    NO_NEST_PENDING (TcbMod.set
                       (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2)) x10
                       (x9, x14, x15))
                    (EcbMod.set els x (absmutexsem x9 (Some (x10, x11)), ct :: x8)) ->
    NO_NEST_PENDING tls els.
Proof.
  intros.
  unfolds; intros.
  assert(TcbMod.get
           (TcbMod.set
              (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2))
            x10 (x9, x14, x15))
         t <> None).
  destruct (tidspec.beq x10 t) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  destruct (tidspec.beq ct t) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.set_a_get_a'; auto.

  assert (IS_OWNER t qid (EcbMod.set els x (absmutexsem x9 (Some (x10, x11)), ct :: x8))).
  unfolds in H4; mytac.
  destruct (tidspec.beq x qid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfolds; do 3 eexists; rewrite EcbMod.set_a_get_a; auto.
  rewrite H4 in H1; inverts H1; eauto.

  unfolds; do 3 eexists; rewrite EcbMod.set_a_get_a'; auto.
  eauto.

  lets Hx: H2 H5 H6; mytac.
  intro; apply H7.
  unfolds in H9; mytac; unfolds.
  exists x1.
  destruct (tidspec.beq x x1) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a; auto.
  rewrite H9 in H1; inverts H1.
  do 3 eexists; mytac; eauto.
  simpl; auto.

  rewrite EcbMod.set_a_get_a'; auto.
  do 3 eexists; eauto.

  intro; apply H8; mytac.
  exists x1; mytac; auto.
  unfolds in H10; mytac; unfolds.
  destruct (tidspec.beq x x1) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a; auto.
  rewrite H10 in H1; inverts H1.
  do 3 eexists; mytac; eauto.

  rewrite EcbMod.set_a_get_a'; auto.
  do 3 eexists; eauto.
Qed.


Lemma pend_lift_getop_t:
  forall tls ct x10 x13 x2 x12 x14 x15 x11 x x8 x9 t p_t els x0 st,
    t<> ct ->
    t<> x10 ->
    TcbMod.get tls ct = Some (x13, st, x2) ->
    TcbMod.get tls x10 = Some (x12, x14, x15) ->
    EcbMod.get els x = Some (absmutexsem x9 (Some (x10, x11)), x8) ->
    GET_OP t
           (TcbMod.set
              (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2)) x10
              (x9, x14, x15))
           (EcbMod.set els x (absmutexsem x9 (Some (x10, x11)), ct :: x8)) p_t ->
    GET_OP t tls els p_t.
Proof.
  intros.
  unfolds; intros.
  assert(TcbMod.get
           (TcbMod.set
              (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2))
            x10 (x9, x14, x15))
         t <> None).
  rewrite TcbMod.set_a_get_a'; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  apply tidspec.neq_beq_false; auto.
  apply tidspec.neq_beq_false; auto.
  
  lets Hx: H4 H6; destruct Hx; mytac.
  left.
  unfolds in H7; mytac.
  destruct (tidspec.beq x x1) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H7; auto.
  inverts H7; exists x1; unfolds; do 2 eexists; eauto.
  rewrite EcbMod.set_a_get_a' in H7; auto.
  exists x1; unfolds; do 2 eexists; eauto.

  right.
  split.
  intro; apply H7; mytac.
  exists x4.
  unfolds in H9; mytac.
  destruct (tidspec.beq x x4) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H9 in H3; inverts H3.
  unfolds; do 3 eexists; rewrite EcbMod.set_a_get_a; auto.
  unfolds; do 3 eexists; rewrite EcbMod.set_a_get_a'; eauto.

  rewrite TcbMod.set_a_get_a' in H8.
  rewrite TcbMod.set_a_get_a' in H8.
  eauto.
  apply tidspec.neq_beq_false; auto.
  apply tidspec.neq_beq_false; auto.
Qed.



Lemma pend_lift_iswait:
  forall t ct els x x9 x10 x11 x8 ,
    t <> ct ->
    EcbMod.get els x = Some (absmutexsem x9 (Some (x10, x11)), x8) ->
    IS_WAITING t
               (EcbMod.set els x (absmutexsem x9 (Some (x10, x11)), ct :: x8)) ->
    IS_WAITING t els.
Proof.
  intros.
  unfolds; unfolds in H1; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto.
  inverts H1; do 4 eexists; mytac; eauto.
  simpl in H2; destruct H2; tryfalse; auto.

  rewrite EcbMod.set_a_get_a' in H1; auto.
  do 4 eexists; eauto.
Qed.


Lemma post_nowt_return_getop_ct:
  forall tls els x x5 ct x6 x7 x8 p_ct,
    NO_NEST_PENDING tls els ->
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, x6)), nil) ->
    TcbMod.get tls ct = Some (x5, x7, x8) ->
    GET_OP ct (TcbMod.set tls ct (x6, x7, x8))
           (EcbMod.set els x (absmutexsem x5 None, nil)) p_ct ->
    GET_OP ct tls els x6 /\ p_ct = x6.
Proof.
    intros.
  
  assert(p_ct = x6).
  unfolds in H2.
  assert(TcbMod.get (TcbMod.set tls ct (x6, x7, x8)) ct <> None).
  rewrite TcbMod.set_a_get_a; auto.
  apply tidspec.eq_beq_true; auto.
  apply H2 in H3; clear H2.
  destruct H3; mytac.
  assert(TcbMod.get tls ct <> None).
  rewrite H1; auto.
  lets Hx: H H3.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  apply Hx in H4; clear Hx; mytac.
  unfolds in H2; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H2; auto; inversion H2.
  rewrite EcbMod.set_a_get_a' in H2; auto.
  false; apply H5.
  exists x0.
  split.
  apply tidspec.beq_false_neq; auto.
  unfolds; eauto.

  rewrite TcbMod.set_a_get_a in H3; inversion H3; auto.
  apply tidspec.eq_beq_true; auto.
  substs.

  split; auto.
  unfolds; intros.
  assert(TcbMod.get (TcbMod.set tls ct (x6, x7, x8)) ct <> None).
  rewrite TcbMod.set_a_get_a; auto.
  apply tidspec.eq_beq_true; auto.

  lets Hx: H2 H4.
  destruct Hx; mytac.
  left.
  
  unfolds in H5; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1;substs.
  rewrite EcbMod.set_a_get_a in H5; auto.
  inverts H5.
  rewrite EcbMod.set_a_get_a' in H5; auto. 
  exists x; unfolds; do 2 eexists; eauto.

  left.
  exists x; unfolds; do 2 eexists; eauto.
Qed.

Lemma post_nowt_return_getop_t:
  forall tls els x x5 t ct x6 x7 x8 p_t,
    t <> ct -> 
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, x6)), nil) ->
    TcbMod.get tls ct = Some (x5, x7, x8) ->
    GET_OP t (TcbMod.set tls ct (x6, x7, x8))
           (EcbMod.set els x (absmutexsem x5 None, nil)) p_t ->
    GET_OP t tls els p_t.
Proof.
  intros.
  unfolds; intros.  
  assert (TcbMod.get (TcbMod.set tls ct (x6, x7, x8)) t <> None).
  rewrite TcbMod.set_a_get_a'; auto.
  apply tidspec.neq_beq_false; auto.
  apply H2 in H4.
  destruct H4; mytac.
  left.
  exists x0.
  unfolds in H4; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto; inverts H4.
  rewrite EcbMod.set_a_get_a' in H4; auto.
  unfolds; eauto.

  right.
  split.
  intro; apply H4; mytac.
  exists x2.
  unfolds in H6; mytac.
  unfolds.
  destruct (tidspec.beq x x2) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H6 in H0; inverts H0; tryfalse.
  rewrite EcbMod.set_a_get_a'; auto.
  eauto.

  rewrite TcbMod.set_a_get_a' in H5.
  eauto.
  apply tidspec.neq_beq_false; auto.
Qed.


Lemma no_owner_cre:
  forall ct els x6 x3 x4,
    ~ (exists eid, IS_OWNER ct eid els) ->
    EcbMod.joinsig x6 (absmutexsem x3 None, nil) x4 els ->
    ~ (exists eid, IS_OWNER ct eid x4).
Proof.
  intros.
  intro; apply H; mytac.
  exists x.
  unfolds in H1; mytac.
  unfolds.
  pose proof H0 x.
  rewrite H1 in H2.
  destruct (tidspec.beq x6 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H2; tryfalse.
  rewrite EcbMod.get_sig_none in H2.
  destruct (EcbMod.get els x); tryfalse.
  substs; eauto.
  apply tidspec.beq_false_neq; auto.
Qed.

Lemma no_owner_del:
  forall ct els x6 x3 x4,
    ~ (exists eid, IS_OWNER ct eid els) ->
    EcbMod.join els (EcbMod.sig x3 (absmutexsem x6 None, nil)) x4 ->
    ~ (exists eid, IS_OWNER ct eid x4).
Proof.
  intros.
  intro; apply H; mytac.
  unfolds in H1; mytac.
  exists x; unfolds.
  pose proof H0 x; rewrite H1 in H2.
  destruct (tidspec.beq x3 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H2.
  destruct (EcbMod.get els x); tryfalse.
  rewrite EcbMod.get_sig_none in H2.
  destruct (EcbMod.get els x); tryfalse.
  substs; eauto.
  apply tidspec.beq_false_neq; auto.
Qed.

Lemma post_lift_get_op_ct:
  forall Ox els tls x x5 ct x0 x1 p_ct,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, x0)), nil) ->
    TcbMod.get tls ct = Some (x5, rdy, x1) ->
    GET_OP ct (TcbMod.set tls ct (x0, rdy, x1))
           (EcbMod.set els x (absmutexsem x5 None, nil)) p_ct ->
    p_ct = x0.
Proof.
  intros.
  unfolds in H4.
  assert(TcbMod.get (TcbMod.set tls ct (x0, rdy, x1)) ct <> None).
  rewrite TcbMod.set_a_get_a; auto; apply tidspec.eq_beq_true; auto.
  apply H4 in H5; clear H4.
  destruct H5; mytac.
  unfolds in H.
  lets Hx: H H0 H1.
  unfolds in Hx.
  assert(TcbMod.get tls ct <> None).
  rewrite H3; auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H5 H6; mytac.
  unfolds in H4; mytac.
  destruct (tidspec.beq x x2) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto.
  inversion H4.
  rewrite EcbMod.set_a_get_a' in H4; auto.
  false; apply H8.
  exists x2; mytac.
  apply tidspec.beq_false_neq; auto.
  unfolds.
  eauto.

  rewrite TcbMod.set_a_get_a in H5; inverts H5; auto.
  apply tidspec.eq_beq_true; auto.
Qed.


Lemma post_lift_ct_nowner:
  forall Ox els tls x x5 ct x0 x1 p_ct x3,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, p_ct)), nil) ->
    TcbMod.get tls ct = Some (x5, rdy, x1) ->
    IS_OWNER x3 x0 (EcbMod.set els x (absmutexsem x5 None, nil)) ->
    x3 <> ct.
Proof.
  intros.
  lets Hx: H H0 H1.
  unfolds in Hx.
  assert(TcbMod.get tls ct <> None).
  rewrite H3; auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H5 H6; mytac.
  unfolds in H4; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto.

  rewrite EcbMod.set_a_get_a' in H4; auto.
  intro; substs; apply H8.
  exists x0; mytac.
  apply tidspec.beq_false_neq; auto.
  unfolds; eauto.
Qed.


Lemma post_nolift_get_op_ct:
  forall Ox els tls x x5 x0 ct x1 p_ct,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, x0)), nil) ->
    TcbMod.get tls ct = Some (x0, rdy, x1) ->
    GET_OP ct tls
           (EcbMod.set els x (absmutexsem x5 None, nil)) p_ct ->
    p_ct = x0.
Proof.
  intros.
  lets Hx: H H0 H1.
  unfolds in H4.
  assert(TcbMod.get tls ct <> None).
  rewrite H3; auto.
  unfolds in Hx.
  assert (IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H5 H6.
  apply H4 in H5; clear H4.
  unfolds in H6; mytac.
  destruct H5; mytac.
  unfolds in H5; mytac.
  destruct (tidspec.beq x x6) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H5; auto; inversion H5.
  false; apply H7.
  exists x6; mytac.
  apply tidspec.beq_false_neq; auto.
  unfolds.
  rewrite EcbMod.set_a_get_a' in H5; eauto.

  rewrite H3 in H8; inverts H8.
  auto.
Qed.


Lemma post_no_lift_ct_nowner:
  forall Ox els tls x x5 ct x0 x1 p_ct x3,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, p_ct)), nil) ->
    TcbMod.get tls ct = Some (p_ct, rdy, x1) ->
    IS_OWNER x3 x0 (EcbMod.set els x (absmutexsem x5 None, nil)) ->
    x3 <> ct.
Proof.
  intros.
  lets Hx: H H0 H1.
  unfolds in H4.
  unfolds in Hx.
  assert (TcbMod.get tls ct <> None).
  rewrite H3; auto.
  assert (IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H5 H6; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto; inversion H4.
  intro; substs.
  apply H8.
  exists x0; mytac.
  apply tidspec.beq_false_neq; auto.
  rewrite EcbMod.set_a_get_a' in H4; auto.
  unfolds; eauto.
Qed.


Lemma post_ex_wait_ct_neq:
  forall Ox els tls x x6 ct x8 x11 x12,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x6 (Some (ct, x8)), x11) ->
    GetHWait tls x11 x12 ->
    x12 <> ct.
Proof.
  intros.
  lets Hx: H H0 H1.
  unfolds in H3.
  unfolds in Hx.
  mytac; intro; substs.
  assert(get tls ct <> None).
  unfolddef.
  unfold get.
  simpl.
  unfold get in H4.
  simpl in H4.
  rewrite H4;auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H6 H7.
  mytac.
  apply H8.
  unfolds.
  do 4 eexists.
  mytac; eauto.
Qed.

Lemma post_lift_exwt_get_op_ct:
  forall (Ox : OSAbstMod.map) (els : EcbMod.map) 
         (tls : TcbMod.map) (x : tidspec.A) (x6 : int32) 
         (ct : tid) (x0 : int32) (x1 : msg) (p_ct : int32) x12 x7 x11 x5,
    x12 <> ct ->
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x6 (Some (ct, x0)), x11) ->
    TcbMod.get tls ct = Some (x5, rdy, x1) ->
    GET_OP ct
           (TcbMod.set (TcbMod.set tls ct (x0, rdy, x1)) x12 (x7, rdy, Vptr x))
           (EcbMod.set els x
                       (absmutexsem x6 (Some (x12, x7)), remove_tid x12 x11)) p_ct -> 
    p_ct = x0.
Proof.
  intros.
  lets Hx:H0 H1 H2.
  unfolds in H5.
  unfolds in Hx.
  assert (TcbMod.get
         (TcbMod.set (TcbMod.set tls ct (x0, rdy, x1)) x12 (x7, rdy, Vptr x))
         ct <> None ).
  rewrite TcbMod.set_a_get_a'.
  rewrite TcbMod.set_a_get_a; auto.
  apply tidspec.eq_beq_true; auto.
  apply tidspec.neq_beq_false; auto.
  apply H5 in H6; clear H5.
  assert(TcbMod.get tls ct <> None).
  rewrite H4; auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H5 H7.
  destruct H6; mytac.
  unfolds in H6; mytac.
  destruct (tidspec.beq x x2) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H6; auto.
  inverts H6; tryfalse.

  rewrite EcbMod.set_a_get_a' in H6; auto.
  false; apply H9; exists x2; mytac.
  apply tidspec.beq_false_neq; auto.
  unfolds; eauto.

  rewrite TcbMod.set_a_get_a' in H10.
  rewrite TcbMod.set_a_get_a in H10.
  inverts H10; auto.
  apply tidspec.eq_beq_true; auto.
  apply tidspec.neq_beq_false; auto.
Qed.

Lemma post_lift_exwt_ct_nowner:
  forall Ox els tls x x5 ct x0 x1 p_ct x3 x12 x7 x11,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, p_ct)), x11) ->
    TcbMod.get tls ct = Some (x5, rdy, x1) ->
    IS_OWNER x3 x0 (EcbMod.set els x (absmutexsem x5 (Some (x12, x7)), remove_tid x12 x11)) -> x12 <> ct ->
    x3 <> ct.
Proof.
  intros.
  unfolds in H4; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto.
  inverts H4; auto.

  rewrite EcbMod.set_a_get_a' in H4; auto.
  lets Hx: H H0 H1.
  unfolds in Hx.
  assert(TcbMod.get tls ct <> None).
  rewrite H3; auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H6 H7; mytac.
  intro; substs.
  apply H9.
  exists x0; mytac.
  apply tidspec.beq_false_neq; auto.
  unfolds; eauto.
Qed.

Lemma post_nolift_exwt_get_op_ct:
  forall Ox els tls x ct p_ct x11 x12 x13 x6 x7 x8 x9,
    x13 <> ct ->
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x6 (Some (ct, x9)), x12) ->
    TcbMod.get tls ct =  Some (x8, rdy, x11) ->
    GET_OP ct (TcbMod.set tls x13 (x7, rdy, Vptr x))
           (EcbMod.set els x
                       (absmutexsem x6 (Some (x13, x7)), remove_tid x13 x12)) p_ct ->
    p_ct = x8.
Proof.
  intros.
  lets Hx: H0 H1 H2.
  unfolds in H5.
  assert(TcbMod.get (TcbMod.set tls x13 (x7, rdy, Vptr x)) ct <> None).
  rewrite TcbMod.set_a_get_a'.
  rewrite H4; auto.
  apply tidspec.neq_beq_false; auto.
  apply H5 in H6; clear H5.
  unfolds in Hx.
  assert(TcbMod.get tls ct <> None).
  rewrite H4; auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H5 H7.
  destruct H6; mytac.
  unfolds in H6; mytac.
  destruct(tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H6; auto.
  inverts H6; tryfalse.

  rewrite EcbMod.set_a_get_a' in H6; auto.
  false; apply H9; exists x0; mytac.
  apply tidspec.beq_false_neq; auto.
  unfolds; eauto.

  rewrite TcbMod.set_a_get_a' in H10.
  rewrite H4 in H10; inverts H10; auto.
  apply tidspec.neq_beq_false; auto.
Qed.

Lemma post_nolift_exwt_ct_nowner:
  forall Ox els tls x x3 ct x0 p_ct x13 x6 x7 x12 x11,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x6 (Some (ct, p_ct)), x12) ->
    TcbMod.get tls ct = Some (p_ct, rdy, x11) ->
    IS_OWNER x3 x0  (EcbMod.set els x
                                (absmutexsem x6 (Some (x13, x7)), remove_tid x13 x12))->  x13 <> ct ->
    x3 <> ct.
Proof.
  intros.
  unfolds in H4; mytac.
  destruct (tidspec.beq x x0) eqn :eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto.
  inverts H4; auto.

  rewrite EcbMod.set_a_get_a' in H4; auto.
  lets Hx: H H0 H1.
  unfolds in Hx.
  assert(TcbMod.get tls ct <> None).
  rewrite H3; auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H6 H7; mytac.
  intro; substs.
  apply H9.
  exists x0; mytac.
  apply tidspec.beq_false_neq; auto.
  unfolds; eauto.
Qed.



Lemma tickchange_els :
  forall t st st' els els',
    tickchange t st els st' els' ->
    (els = els' \/
     (exists eid m wl, EcbMod.get els eid = Some (m, wl) /\
        els' = EcbMod.set els eid (m, remove_tid t wl))
    ).
Proof.
  intros.
  inverts H;
    try solve [left; auto].
  right.
  do 3 eexists; split; eauto.
Qed.

Lemma GET_OP_st_irrel :
  forall tls els t ct p st st' msg p_ct,
    TcbMod.get tls t = Some (p, st, msg) ->
    GET_OP ct (TcbMod.set tls t (p, st', msg)) els p_ct ->
    GET_OP ct tls els p_ct.
Proof.
  intros.
  unfolds in H0; unfolds; intros.
  assert(TcbMod.get (TcbMod.set tls t (p, st', msg)) ct <> None).
  destruct(tidspec.beq t ct) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  apply H0 in H2.
  destruct H2; mytac.
  left; eauto.
  right; split; eauto.
  destruct(tidspec.beq t ct) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H3; auto; inverts H3; eauto.
  rewrite TcbMod.set_a_get_a' in H3; auto; eauto.
Qed.

Lemma IS_OWNER_remove_tid_irrel :
    forall els m wl x x0 t ct,
      EcbMod.get els x = Some (m, wl) ->
      IS_OWNER ct x0 (EcbMod.set els x (m, remove_tid t wl)) ->
      IS_OWNER ct x0 els.
Proof.
  intros.
  unfolds in H0; mytac.
  unfolds.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H0; inverts H0; eauto.
  rewrite EcbMod.set_a_get_a' in H0; eauto.
Qed.

Lemma IS_OWNER_remove_tid_irrel' :
    forall els m wl x x0 t ct,
      EcbMod.get els x = Some (m, wl) ->
      IS_OWNER ct x0 els ->
      IS_OWNER ct x0 (EcbMod.set els x (m, remove_tid t wl)).
Proof.
  intros.
  unfolds in H0; mytac.
  unfolds.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H0 in H; inverts H.
  rewrite EcbMod.set_a_get_a; eauto.
  rewrite EcbMod.set_a_get_a'; eauto.
Qed.

Lemma IS_OWNER_P_remove_tid_irrel :
  forall els m wl x x0 t ct p_ct,
    EcbMod.get els x = Some (m, wl) ->
    IS_OWNER_P ct x0 (EcbMod.set els x (m, remove_tid t wl)) p_ct ->
    IS_OWNER_P ct x0 els p_ct.
Proof.
  intros.
  unfolds in H0; mytac.
  unfolds.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H0; auto; inverts H0; eauto.
  rewrite EcbMod.set_a_get_a' in H0; eauto.
Qed.

Lemma GET_OP_remove_tid_irrel :
  forall tls els ct t x m wl p_ct,
    EcbMod.get els x = Some (m, wl) ->
    GET_OP ct tls (EcbMod.set els x (m, remove_tid t wl)) p_ct ->
    GET_OP ct tls els p_ct.
Proof.
  intros.
  unfolds in H0; unfolds; intros.
  apply H0 in H1; clear H0.
  destruct H1; mytac.
  left.
  apply IS_OWNER_P_remove_tid_irrel in H0; eauto.  
  right; split.
  intro; apply H0; mytac; eexists.
  apply IS_OWNER_remove_tid_irrel'; eauto.
  eauto.
Qed.

  
Lemma tickchange_getop_eq:
  forall ct tls tls' t0 p st msg0 st' els els' p_ct',
    TcbMod.get tls t0 = Some (p, st, msg0) ->
    TcbMod.set tls t0 (p, st', msg0) = tls' ->
    tickchange t0 st els st' els' ->
    GET_OP ct tls' els' p_ct' ->
    GET_OP ct tls els p_ct'.
Proof.
  intros.
  apply tickchange_els in H1.
  destruct H1.
  substs.
  eapply GET_OP_st_irrel; eauto.
  mytac.
  assert(GET_OP ct tls (EcbMod.set els x (x0, remove_tid t0 x1)) p_ct').
  eapply GET_OP_st_irrel; eauto.
  eapply GET_OP_remove_tid_irrel; eauto.
Qed.
  
Lemma tickchange_highestrdy_rdy:
  forall ct tls tls' t0 p st msg0 st' els els',
    TcbMod.get tls t0 = Some (p, st, msg0) ->
    TcbMod.set tls t0 (p, st', msg0) = tls' ->
    tickchange t0 st els st' els' ->
    HighestRdy tls' ct ->
    (exists p msg, TcbMod.get tls ct = Some (p,rdy,msg)) -> 
    HighestRdy tls ct.
Proof.

  intros.
  assert ( t0 = ct \/ t0 <> ct ) by tauto.
  destruct H4.
  subst.
  mytac.
  rewrite H0 in H;inverts H.
  inverts H1;tryfalse;auto.
  destruct H;tryfalse.
  rewrite TcbMod.get_set_same in H2;auto.
  destruct H;tryfalse.
  destruct H;tryfalse.
  destruct H;tryfalse.
  clear H3.
  rename H4 into H3.
  
  unfolds in H2; unfolds; mytac.
  rewrite TcbMod.set_a_get_a' in H2.
  do 2 eexists; mytac; eauto.
  intros.
  eapply H4; eauto.
  destruct (tidspec.beq t0 i) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H5 in H; inverts H.
  rewrite TcbMod.set_a_get_a; eauto.
  inverts H1; substs; eauto; tryfalse.
  rewrite TcbMod.set_a_get_a'; eauto.
  apply tidspec.neq_beq_false; auto.
Qed.



Lemma tickchange_no_owner:
  forall ct tls tls' t0 p st msg0 st' els els',
    TcbMod.get tls t0 = Some (p, st, msg0) ->
    TcbMod.set tls t0 (p, st', msg0) = tls' ->
    tickchange t0 st els st' els' ->
    ~ (exists eid, IS_OWNER ct eid els') ->
    ~ (exists eid, IS_OWNER ct eid els).
Proof.
  intros.
  apply tickchange_els in H1; destruct H1.
  substs; eauto.
  mytac; intro; apply H2; mytac.
  eexists; eapply IS_OWNER_remove_tid_irrel'; eauto.
Qed.

Lemma tickchange_nonone:
  forall ct tls tls' t0 p st msg0 st' els els',
    TcbMod.get tls t0 = Some (p, st, msg0) ->
    TcbMod.set tls t0 (p, st', msg0) = tls' ->
    tickchange t0 st els st' els' ->
    TcbMod.get tls' ct <> None ->
    TcbMod.get tls ct <> None.
Proof.
  intros.
  intro; apply H2.
  destruct (tidspec.beq t0 ct) eqn:eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H3 in H; tryfalse.
  substs; rewrite TcbMod.set_a_get_a'; auto.
Qed.

Lemma tickchange_iswait:
  forall ct tls tls' t0 p st msg0 st' els els',
    TcbMod.get tls t0 = Some (p, st, msg0) ->
    TcbMod.set tls t0 (p, st', msg0) = tls' ->
    tickchange t0 st els st' els' ->
    IS_WAITING ct els' ->
    IS_WAITING ct els.
Proof.
  intros.
  apply tickchange_els in H1; destruct H1.
  substs; auto.
  mytac.
  unfolds; unfolds in H2; mytac.
  destruct(tidspec.beq x x2) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H0; auto; inverts H0.
  do 4 eexists; split; eauto.
  Lemma In_remove_tid : forall wl t ct, In ct (remove_tid t wl) -> In ct wl.
  Proof.
    inductions wl; intros.
    simpl in H; tryfalse.
    simpl in H.
    destruct (beq_tid t a) eqn : eq1.
    simpl.
    right; eapply IHwl; eauto.
    simpl in H; destruct H; substs.
    simpl; left; auto.
    simpl; right; eapply IHwl; eauto.
  Qed.
  eapply In_remove_tid; eauto.

  rewrite EcbMod.set_a_get_a' in H0; eauto.
  do 4 eexists; split; eauto.
Qed.

Lemma tickchange_nonestpend:
  forall tls tls' t0 p st msg0 st' els els',
    TcbMod.get tls t0 = Some (p, st, msg0) ->
    TcbMod.set tls t0 (p, st', msg0) = tls' ->
    tickchange t0 st els st' els' ->
    NO_NEST_PENDING tls els ->
    NO_NEST_PENDING tls' els'.
Proof.
  intros.
  apply tickchange_els in H1; destruct H1.
  substs. 
  unfolds; intros; unfolds in H2.
  assert(TcbMod.get tls t <> None).
  intro; apply H0.
  destruct(tidspec.beq t0 t) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H3 in H; tryfalse.
  rewrite TcbMod.set_a_get_a'; auto.
  eapply H2; eauto.

  mytac.
  unfolds; intros; unfolds in H2.
  assert(TcbMod.get tls t <> None).
  destruct(tidspec.beq t0 t) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H; auto.
  rewrite TcbMod.set_a_get_a' in H0; auto.
  assert(IS_OWNER t qid els).
  eapply IS_OWNER_remove_tid_irrel; eauto.
  lets Hx: H2 H4 H5; clear H2 H4 H5.
  mytac.
  intro; apply H2.
  unfolds in H5; unfolds; mytac.
  destruct(tidspec.beq x x2) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H5; auto; inverts H5.
  do 4 eexists; mytac; eauto.
  eapply In_remove_tid; eauto.
  rewrite EcbMod.set_a_get_a' in H5; eauto.
  do 4 eexists; mytac; eauto.
  intro; apply H4; mytac.
  exists x2; split; eauto.
  eapply IS_OWNER_remove_tid_irrel; eauto.
Qed.

Lemma tickchange_exct:
  forall tls els els' tls' t0 ct p st st' msg0,
    tickchange t0 st els st' els' ->
    TcbMod.set tls t0 (p, st', msg0) = tls' ->
    TcbMod.get tls t0 = Some (p, st, msg0) ->
    HighestRdy tls' ct ->
    exists  pct stct mct,TcbMod.get tls ct = Some (pct,stct,mct).
Proof.
  intros.
  destruct(tidspec.beq t0 ct) eqn :eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  inverts H; eauto.
  substs.
  unfolds in H2; mytac.
  rewrite TcbMod.set_a_get_a' in H0; eauto.
Qed.

Lemma tickchange_eq_prio:
  forall tls els els' tls' t0 ct p msg0 pct pct' st st' stx stx' m m',
    tickchange t0 st els st' els' ->
    TcbMod.set tls t0 (p, st', msg0) = tls' ->
    TcbMod.get tls t0 = Some (p, st, msg0) ->
    TcbMod.get tls ct = Some (pct,stx,m) ->
    TcbMod.get tls' ct = Some (pct',stx',m') ->
    pct = pct'.
Proof.
  intros.
  substs.
  destruct(tidspec.beq t0 ct) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H3; auto.
  inverts H3; rewrite H2 in H1; inverts H1; auto.

  rewrite TcbMod.set_a_get_a' in H3; auto.
  rewrite H2 in H3; inverts H3; auto.
Qed.

Lemma tickchange_nonest_ct:
  forall tls els els' tls' t0 ct p msg0 pct' st st' tm m eid x2,
    rdy_notin_wl tls els ->
    tickchange t0 st els st' els' ->
    TcbMod.set tls t0 (p, st', msg0) = tls' ->
    TcbMod.get tls t0 = Some (p, st, msg0) ->
    IS_OWNER ct x2 els' -> 
    TcbMod.get tls ct = Some (pct', wait (os_stat_mutexsem eid) tm, m) ->
    NO_NEST_PENDING tls els ->
    False.
Proof.
  intros.
  inverts H0.

  unfolds in H; mytac.
  lets Hx: H0 H4; unfolds in Hx; mytac.
  unfolds in H5.
  assert(TcbMod.get tls ct <> None).
  rewrite H4; auto.
  lets Hx: H5 H9 H3.
  mytac.
  apply H10.
  unfolds.
  exists eid x x0 x1.
  split; auto.

  unfolds in H; mytac.
  lets Hx: H0 H4; unfolds in Hx; mytac.
  unfolds in H5.
  assert(TcbMod.get tls ct <> None).
  rewrite H4; auto.
  lets Hx: H5 H9 H3.
  mytac.
  apply H10.
  unfolds.
  exists eid x x0 x1.
  split; auto.

  unfolds in H; mytac.
  lets Hx: H0 H4; unfolds in Hx; mytac.
  unfolds in H5.
  assert(TcbMod.get tls ct <> None).
  rewrite H4; auto.
  lets Hx: H5 H8 H3.
  mytac.
  apply H9.
  unfolds.
  exists eid x x0 x1.
  split; auto.

  unfolds in H; mytac.
  lets Hx: H0 H4; unfolds in Hx; mytac.
  unfolds in H5.
  assert(TcbMod.get tls ct <> None).
  rewrite H4; auto.
  lets Hx: H5 H11 H3.
  mytac.
  apply H12.
  unfolds.
  exists eid x0 x1 x3.
  split; auto.

  clear H6.
  assert(IS_OWNER ct x2 els).
  eapply IS_OWNER_remove_tid_irrel; eauto.
  unfolds in H; mytac.
  lets Hx: H6 H4; unfolds in Hx; mytac.
  unfolds in H5.
  assert(TcbMod.get tls ct <> None).
  rewrite H4; auto.
  lets Hx: H5 H10 H0.
  mytac.
  apply H11.
  unfolds.
  exists eid x0 x1 x3.
  split; auto.
Qed.



Lemma joinsig_neq_get:
  forall x y els els0 s eid,
    eid <> x ->
    EcbMod.get els0 eid = s ->
    EcbMod.joinsig x y els els0 ->
    EcbMod.get els eid = s.
Proof.
  intros.
  pose proof H1 eid.
  rewrite EcbMod.get_sig_none in H2; auto.
  destruct (EcbMod.get els eid);
  destruct (EcbMod.get els0 eid); tryfalse; substs; auto.
Qed.

Lemma ecb_joinsig_get_eq'
: forall (x6 : tidspec.A) (x3 : int32) (x4 els : EcbMod.map)
         (x8 : waitset) a0 (x9 : int32) (x : tidspec.A),
    EcbMod.joinsig x6 (absmutexsem x3 None, nil) els x4->
    EcbMod.get x4 x = Some (absmutexsem x9 (Some a0), x8) ->
    EcbMod.get els x = Some (absmutexsem x9 (Some a0), x8).
Proof.
  intros.
  pose proof H x.
  rewrite H0 in H1.
  destruct (tidspec.beq x6 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H1.
  destruct (EcbMod.get els x); tryfalse.
  rewrite EcbMod.get_sig_none in H1.
  destruct(EcbMod.get els x); tryfalse.
  substs; auto.
  apply tidspec.beq_false_neq; auto.
Qed.

Lemma is_owner_set_other:
  forall t eid els x x3 x4 x5 ct,
    t <> ct ->
    IS_OWNER t eid els ->
    EcbMod.get els x = Some (absmutexsem x3 None, x4) ->
    IS_OWNER t eid
             (EcbMod.set els x (absmutexsem x3 (Some (ct, x5)), x4)).
Proof.
  intros.
  unfolds; unfolds in H0; mytac.
  destruct(tidspec.beq x eid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a; auto.
  rewrite H0 in H1; inverts H1.
  rewrite EcbMod.set_a_get_a'; auto.
  eauto.
Qed.


Lemma pend_lift_getop_ct:
  forall (tls : TcbMod.map) (ct x10 : tidspec.A) 
         (x13 : priority) (x2 : msg) (x12 : priority) 
         (x14 : taskstatus) (x15 : msg) (x11 : int32) 
         (x : tidspec.A) (x8 : waitset) (x9 : int32) 
         (p_t : int32) (els : EcbMod.map) 
         (x0 : int32) (st : taskstatus),
    x10 <> ct ->
    TcbMod.get tls ct = Some (x13, st, x2) ->
    TcbMod.get tls x10 = Some (x12, x14, x15) ->
    EcbMod.get els x = Some (absmutexsem x9 (Some (x10, x11)), x8) ->
    GET_OP ct
           (TcbMod.set
              (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2)) x10
              (x9, x14, x15))
           (EcbMod.set els x (absmutexsem x9 (Some (x10, x11)), ct :: x8)) p_t ->
    GET_OP ct tls els p_t.
Proof.
  intros.
  unfolds; intros.
  assert(TcbMod.get (TcbMod.set
            (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2)) x10
            (x9, x14, x15)) ct <> None).
  rewrite TcbMod.set_a_get_a'.
  rewrite TcbMod.set_a_get_a; auto.
  apply tidspec.eq_beq_true; auto.
  apply tidspec.neq_beq_false; auto.
  apply H3 in H5; clear H3; destruct H5; mytac.
  left.
  unfolds in H3; mytac.
  destruct (tidspec.beq x x1) eqn: eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H3; auto; inverts H3; tryfalse.
  rewrite EcbMod.set_a_get_a' in H3; auto.
  exists x1; unfolds; eauto.

  right.
  split.
  intro; apply H3.
  destruct H6; unfolds in H6; mytac.
  destruct(tidspec.beq x x4) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H6 in H2; inverts H2; tryfalse.
  exists x4; unfolds; rewrite EcbMod.set_a_get_a'; eauto.
  rewrite TcbMod.set_a_get_a' in H5.
  rewrite TcbMod.set_a_get_a in H5.
  inverts H5; eauto.
  apply tidspec.eq_beq_true; auto.
  apply tidspec.neq_beq_false; auto.
Qed.

Lemma post_iswait:
  forall t x11 x12 x x6 els owner owner',
    t <> x12 ->
    EcbMod.get els x = Some (absmutexsem x6 owner, x11) ->
    (IS_WAITING t
               (EcbMod.set els x
                           (absmutexsem x6 owner', remove_tid x12 x11)) <->
    IS_WAITING t els).
Proof.
  intros.
  split; intros.
  unfolds in H1; mytac.
  unfolds.
  destruct(tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto.
  inverts H1.
  do 4 eexists.
  split; eauto.
  eapply In_remove_tid; eauto.
  rewrite EcbMod.set_a_get_a' in H1; auto.
  do 4 eexists; split; eauto.

  unfolds in H1; mytac.
  unfolds.
  destruct(tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H1 in H0; inverts H0.
  exists x0.
  rewrite EcbMod.set_a_get_a; auto.
  do 3 eexists; split; eauto.
  Lemma In_remove_tid' : forall wl t t', t <> t' -> In t wl -> In t (remove_tid t' wl).
  Proof.
    intro; inductions wl; intros.
    simpl in ; tryfalse.
    simpl in H0; destruct H0; substs.
    simpl.
    destruct(beq_tid t' t) eqn : eq1.
    false; apply H.
    Lemma beq_tid_true_eq: forall t1 t2, beq_tid t1 t2 = true -> t1 = t2.
    Proof.
      intros.
      unfolds in H; destruct t1; destruct t2.
      apply andb_true_iff in H; destruct H.
      rewrite beq_pos_Pos_eqb_eq in H.
      apply Pos.eqb_eq in H.
      pose proof Int.eq_spec i i0.
      rewrite H0 in H1.
      substs; auto.
    Qed.
    apply beq_tid_true_eq in eq1; auto.
    simpl; auto.
    simpl.
    destruct(beq_tid t' a) eqn : eq1.
    eapply IHwl; eauto.
    simpl.
    right.
    eapply IHwl; eauto.
  Qed.
  eapply In_remove_tid'; eauto.

  exists x0.
  rewrite EcbMod.set_a_get_a'; auto.
  eauto.
Qed.

Lemma post_iswait':
  forall t x11 x12 x x6 eid els owner owner',
    t <> x12 ->
    EcbMod.get els x = Some (absmutexsem x6 owner, x11) ->
    (IS_WAITING_E t eid
                 (EcbMod.set els x
                             (absmutexsem x6 owner', remove_tid x12 x11)) <->
    IS_WAITING_E t eid els).
Proof.
  intros.
  split; intros.
  unfolds in H1; mytac.
  unfolds.
  destruct(tidspec.beq x eid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto; inverts H1.
  do 3 eexists; split; eauto.
  eapply In_remove_tid; eauto.
  rewrite EcbMod.set_a_get_a' in H1; auto.
  do 3 eexists; split; eauto.

  unfolds in H1; mytac.
  unfolds.
  destruct(tidspec.beq x eid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H1 in H0; inverts H0.
  rewrite EcbMod.set_a_get_a; auto.
  do 3 eexists; split; eauto.
  eapply In_remove_tid'; eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  do 3 eexists; split; eauto.
Qed.

Lemma In_remove_tid_false : forall wl t, In t (remove_tid t wl) -> False.
Proof.
  intro; inductions wl; intros.
  simpl in H; auto.
  simpl in H.
  destruct (beq_tid t a) eqn : eq1.
  eapply IHwl; eauto.
  simpl in H.
  destruct H.
  substs.
  Lemma beq_tid_true : forall t, beq_tid t t = true.
  Proof.
    intros.
    unfolds; destruct t.
    rewrite beq_pos_Pos_eqb_eq.
    rewrite Pos.eqb_refl.
    rewrite Int.eq_true.
    simpl; auto.
  Qed.
  rewrite beq_tid_true in eq1; tryfalse.
  eapply IHwl; eauto.
Qed.
  
Lemma nnp_remove_nwait:
  forall tls els x11 t x x6 ct x8 p x13 x14,
    NO_NEST_PENDING tls els ->
    rdy_notin_wl tls els ->
    GetHWait tls x11 t ->
    EcbMod.get els x = Some (absmutexsem x6 (Some (ct, x8)), x11) ->
    TcbMod.get tls t = Some (p, x13, x14) ->
    ~
      IS_WAITING t
      (EcbMod.set els x (absmutexsem x6 (Some (t, p)), remove_tid t x11)).
Proof.
  intros.
  intro.
  unfolds in H4; mytac.
  destruct(tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto.
  inverts H4.
  eapply In_remove_tid_false; eauto.

  rewrite EcbMod.set_a_get_a' in H4; auto.
  unfolds in H1; mytac.
  unfolds in H0; mytac.
  assert(IS_WAITING_E t x els).
  unfolds; do 3 eexists; split; eauto.
  assert(IS_WAITING_E t x0 els).
  unfolds; do 3 eexists; split; eauto.
  lets Hx1 : H9 H10.
  lets Hx2 : H9 H11.
  mytac.
  rewrite H13 in H12; inverts H12.
  assert(tidspec.beq x0 x0 = true).
  apply tidspec.eq_beq_true; auto.
  rewrite eq1 in H12; tryfalse.
Qed.

Lemma remove_is_wait_neq:
  forall x12 t x x6 x7 x11 els ct x8,
    t <> x12 ->
    EcbMod.get els x = Some (absmutexsem x6 (Some (ct, x8)), x11) ->
    IS_WAITING t
               (EcbMod.set els x
                           (absmutexsem x6 (Some (x12, x7)), remove_tid x12 x11)) ->
    IS_WAITING t els.
Proof.
  intros.
  unfolds in H1; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto; inverts H1.
  unfolds; exists x0 x1 (Some (ct, x8)) x11.
  split; auto.
  eapply In_remove_tid; eauto.

  rewrite EcbMod.set_a_get_a' in H1; auto.
  unfolds.
  exists x0 x1 x2 x3; split; eauto.
Qed.

Lemma tickchange_not_waiting:
  forall tls t p0 eid m0 m wl els,
    EcbMod.get els eid = Some (m, wl) ->
    TcbMod.get tls t = Some (p0, wait (os_stat_mutexsem eid) Int.one, m0)->
    rdy_notin_wl tls els ->
    NO_NEST_PENDING tls els ->
    ~ IS_WAITING t (EcbMod.set els eid (m, remove_tid t wl)).
Proof.
  intros.
  unfolds in H1; mytac.
  lets Hx: H3 H0.
  unfolds in Hx; mytac.
  intro; unfolds in H7; mytac.
  destruct (tidspec.beq eid x2) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H7; auto; inverts H7.
  
  eapply In_remove_tid_false; eauto.

  rewrite EcbMod.set_a_get_a' in H7; auto.
  assert(IS_WAITING_E t eid els).
  unfolds; do 3 eexists; split; eauto.
  assert(IS_WAITING_E t x2 els).
  unfolds; do 3 eexists; split; eauto.
  lets Hx1: H4 H9.
  lets Hx2: H4 H10.
  mytac.
  rewrite H12 in H11.
  inverts H11.
  assert(tidspec.beq x2 x2 = true).
  apply tidspec.eq_beq_true; auto.
  rewrite eq1 in H11; tryfalse.
Qed.


Lemma remove_tid_in_false:
  forall t wl,
    In t (remove_tid t wl) -> False.
Proof.
  intros; gen t.
  inductions wl; intros.
  simpl in H; auto.
  simpl in H.
  destruct(beq_tid t a) eqn : eq1.
  eapply IHwl; eauto.
  
  simpl in H; destruct H.
  substs; unfolds in eq1; destruct t.
  apply andb_false_iff in eq1; destruct eq1.
  rewrite beq_pos_Pos_eqb_eq in H.
  assert(b = b) by auto.
  apply Pos.eqb_eq in H0.
  rewrite H in H0; tryfalse.
  rewrite Int.eq_true in H; tryfalse.
  eapply IHwl; eauto.
Qed.
(*-----------------------*)

Fixpoint GoodStmt_h (s : stmts) {struct s} : Prop :=
  match s with
    | sskip _ => True
    | sassign _ _ => True
    | sif _ s1 s2 => GoodStmt_h s1 /\ GoodStmt_h s2
    | sifthen _ _ => False
    | swhile _ s' => GoodStmt_h s'
    | sret => True
    | srete  _ => True
    | scall f _ => True
    | scalle _ f _ => True
    | sseq s1 s2 => GoodStmt_h s1 /\ GoodStmt_h s2
    | sprint _ => True
    | sfexec _ _ _ => False
    | sfree _ _ => False
    | salloc _ _ => False
    | sprim _ => False
    | hapi_code _ => False
  end.

Definition GoodAcc (s:spec_code) vl:=
  (s = mutexacc_null (|vl|)
                     ?? mutexacc_no_mutex_err (|vl|)
                     ?? mutexacc_no_available (|vl|)
                     ?? mutexacc_prio_err (|vl|) ?? mutexacc_succ (|vl|)) \/
  s = mutexacc_null (|vl|) \/
  (s = mutexacc_no_mutex_err (|vl|)
                             ?? mutexacc_no_available (|vl|)
                             ?? mutexacc_prio_err (|vl|) ?? mutexacc_succ (|vl|)) \/
  s = mutexacc_no_mutex_err (|vl|) \/
  (s = mutexacc_no_available (|vl|)
                             ?? mutexacc_prio_err (|vl|) ?? mutexacc_succ (|vl|))\/
  s = mutexacc_no_available (|vl|)\/
  (s = mutexacc_prio_err (|vl|) ?? mutexacc_succ (|vl|) ) \/
  s = mutexacc_prio_err (|vl|) \/
  s = mutexacc_succ (|vl|) \/
  exists v, s = spec_done v.

Definition GoodCre (s:spec_code) vl:=
  (s = mutexcre_error (|vl|) ?? mutexcre_succ (|vl|)) \/
  s = mutexcre_error (|vl|) \/
  s = mutexcre_succ (|vl|) \/
  exists v, s = spec_done v.

Definition GoodDel (s:spec_code) vl:=
  (s = mutexdel_null (|vl|)
                     ?? mutexdel_no_mutex_err (|vl|)
                     ?? mutexdel_type_err (|vl|)
                     ?? mutexdel_ex_wt_err (|vl|) ?? mutexdel_succ (|vl|) ?? mutexdel_pr_not_holder_err (|vl|)) \/
  (s = mutexdel_null (|vl|)) \/
  (s = mutexdel_no_mutex_err (|vl|)
                     ?? mutexdel_type_err (|vl|)
                     ?? mutexdel_ex_wt_err (|vl|) ?? mutexdel_succ (|vl|) ?? mutexdel_pr_not_holder_err (|vl|) ) \/
  (s = mutexdel_no_mutex_err (|vl|)) \/
  (s = mutexdel_type_err (|vl|)
                         ?? mutexdel_ex_wt_err (|vl|) ?? mutexdel_succ (|vl|)?? mutexdel_pr_not_holder_err (|vl|)) \/
  (s = mutexdel_type_err (|vl|)) \/
  (s = mutexdel_ex_wt_err (|vl|) ?? mutexdel_succ (|vl|)?? mutexdel_pr_not_holder_err (|vl|)) \/
  (s = mutexdel_ex_wt_err (|vl|)) \/
  (s = mutexdel_succ (|vl|)?? mutexdel_pr_not_holder_err (|vl|)) \/
  s = mutexdel_succ (|vl|) \/
  s = mutexdel_pr_not_holder_err (|vl|) \/
  exists v, s = spec_done v.


Definition GoodPend (s:spec_code) vl :=
  s = mutexpend_null (|vl|)
                     ?? mutexpend_no_mutex_err (|vl|)
                     ?? mutexpend_type_err (|vl|)
                     ?? mutexpend_idle_err (|vl|)
                     ?? mutexpend_stat_err (|vl|)
                     ?? mutexpend_prio_err (|vl|)
                     ?? mutexpend_get_succ (|vl|)
                     ?? (mutexpend_block_lift (|vl|)
                                              ?? mutexpend_block_no_lift (|vl|));;
                     isched;;
                     (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|))  ?? mutexpend_pr_not_holder_err (|vl|) ??
                     mutexpend_nest_err (|vl|) ?? mutexpend_deadlock_err (|vl|)
                     ?? mutexpend_msg_not_null_err (|vl|) ?? mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                          (|vl|)
  \/
  s = mutexpend_null (|vl|) \/
  s = mutexpend_no_mutex_err (|vl|)
                             ?? mutexpend_type_err (|vl|)
                             ?? mutexpend_idle_err (|vl|)
                             ?? mutexpend_stat_err (|vl|)
                             ?? mutexpend_prio_err (|vl|)
                             ?? mutexpend_get_succ (|vl|)
                             ?? (mutexpend_block_lift (|vl|)
                                                      ?? mutexpend_block_no_lift (|vl|));;
                                                      isched;;
                                                      (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|))  ?? mutexpend_pr_not_holder_err (|vl|) ??
  mutexpend_nest_err (|vl|) ?? mutexpend_deadlock_err (|vl|)
                              ?? mutexpend_msg_not_null_err (|vl|) ?? mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                          (|vl|) \/
  s = mutexpend_no_mutex_err (|vl|) \/
  s = mutexpend_type_err (|vl|)
                         ?? mutexpend_idle_err (|vl|)
                         ?? mutexpend_stat_err (|vl|)
                         ?? mutexpend_prio_err (|vl|)
                         ?? mutexpend_get_succ (|vl|)
                         ?? (mutexpend_block_lift (|vl|)
                                                  ?? mutexpend_block_no_lift (|vl|));;
                                                  isched;;
                                                  (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|))  ?? mutexpend_pr_not_holder_err (|vl|)??
  mutexpend_nest_err (|vl|) ?? mutexpend_deadlock_err (|vl|)
                              ?? mutexpend_msg_not_null_err (|vl|) ?? mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                          (|vl|) \/
  s = mutexpend_type_err (|vl|) \/
  s = mutexpend_idle_err (|vl|)
                         ?? mutexpend_stat_err (|vl|)
                         ?? mutexpend_prio_err (|vl|)
                         ?? mutexpend_get_succ (|vl|)
                         ?? (mutexpend_block_lift (|vl|)
                                                  ?? mutexpend_block_no_lift (|vl|));;
                                                  isched;;
                                                  (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|))  ?? mutexpend_pr_not_holder_err (|vl|)??
  mutexpend_nest_err (|vl|) ?? mutexpend_deadlock_err (|vl|)
                              ?? mutexpend_msg_not_null_err (|vl|) ?? mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                          (|vl|) \/
  s = mutexpend_idle_err (|vl|) \/
  s = mutexpend_stat_err (|vl|)
                         ?? mutexpend_prio_err (|vl|)
                         ?? mutexpend_get_succ (|vl|)
                         ?? (mutexpend_block_lift (|vl|)
                                                  ?? mutexpend_block_no_lift (|vl|));;
                                                  isched;;
                                                  (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|))  ?? mutexpend_pr_not_holder_err (|vl|)??
  mutexpend_nest_err (|vl|) ?? mutexpend_deadlock_err (|vl|)
                              ?? mutexpend_msg_not_null_err (|vl|) ?? mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                          (|vl|)\/
  s = mutexpend_stat_err (|vl|) \/
  s = mutexpend_prio_err (|vl|)
                         ?? mutexpend_get_succ (|vl|)
                         ?? (mutexpend_block_lift (|vl|)
                                                  ?? mutexpend_block_no_lift (|vl|));;
                                                  isched;;
                                                  (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|))  ?? mutexpend_pr_not_holder_err (|vl|)??
  mutexpend_nest_err (|vl|) ?? mutexpend_deadlock_err (|vl|)
                              ?? mutexpend_msg_not_null_err (|vl|) ?? mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                          (|vl|) \/
  s = mutexpend_prio_err (|vl|)\/
  s = mutexpend_get_succ (|vl|)
                         ?? (mutexpend_block_lift (|vl|)
                                                  ?? mutexpend_block_no_lift (|vl|));;
                                                  isched;;
                                                  (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|)) ?? mutexpend_pr_not_holder_err (|vl|)??
  mutexpend_nest_err (|vl|) ?? mutexpend_deadlock_err (|vl|)
                              ?? mutexpend_msg_not_null_err (|vl|) ?? mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                          (|vl|) \/
  s = mutexpend_get_succ (|vl|) \/
  s = (mutexpend_block_lift (|vl|)
                            ?? mutexpend_block_no_lift (|vl|));;
                            isched;;
                            (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|))  ?? mutexpend_pr_not_holder_err (|vl|) ??
  mutexpend_nest_err (|vl|) ?? mutexpend_deadlock_err (|vl|)
                              ?? mutexpend_msg_not_null_err (|vl|) ?? mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                          (|vl|)\/

  s = (mutexpend_block_lift (|vl|)
                            ?? mutexpend_block_no_lift (|vl|));;
                                                              isched;;
                                                              (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|)) \/
  s = mutexpend_pr_not_holder_err (|vl|) ??
                                  mutexpend_nest_err (|vl|) ?? mutexpend_deadlock_err (|vl|)
                              ?? mutexpend_msg_not_null_err (|vl|) ?? mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                          (|vl|) \/
  s = mutexpend_pr_not_holder_err (|vl|) \/
  s = mutexpend_nest_err (|vl|) ?? mutexpend_deadlock_err (|vl|)
                         ?? mutexpend_msg_not_null_err (|vl|) ?? mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                          (|vl|) \/
  s = mutexpend_nest_err (|vl|) \/
  s = mutexpend_deadlock_err (|vl|)
                             ?? mutexpend_msg_not_null_err (|vl|) ?? mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                          (|vl|) \/
  s = mutexpend_deadlock_err (|vl|) \/
  s = mutexpend_msg_not_null_err (|vl|) ?? mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                       (|vl|) \/
  s = mutexpend_msg_not_null_err (|vl|) \/
  s = mutexpend_cur_prio_eql_mprio_err
                                       (|vl|)
                                       ?? mutexpend_ptcb_prio_eql_idle_err
                                       (|vl|) \/
  s = mutexpend_cur_prio_eql_mprio_err
        (|vl|) \/
  s = mutexpend_ptcb_prio_eql_idle_err
        (|vl|) \/
  s = mutexpend_block_lift (|vl|)
                            ;;
                            isched;;
                            (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|)) \/

  s = mutexpend_block_no_lift (|vl|)
                            ;;
                            isched;;
                            (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|)) \/
  s = spec_done None ;; isched ;;
                            (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|)) \/
  s = isched ;; (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|)) \/
  s = (ASSUME sc;; sched) ;;(mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|)) \/
  s = (spec_done None;;sched) ;; (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|)) \/
  s = sched;;(mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|)) \/
  s = ASSUME nsc;;(mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|)) \/
  s = spec_done None;;(mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|)) \/
  s = mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|) \/
  s = mutexpend_to (|vl|)  \/
  s = mutexpend_block_get (|vl|) \/
  exists v, s = spec_done v.

Open Scope int_scope.
Definition GoodPost (s:spec_code) vl:=
  s = mutexpost_null (|vl|)
                     ?? mutexpost_no_mutex_err (|vl|)
                     ?? mutexpost_type_err (|vl|)
                     ?? mutexpost_no_owner_err (|vl|)
                     ?? mutexpost_nowt_return_prio_succ (|vl|)
                                                         ?? mutexpost_nowt_no_return_prio_succ (|vl|)

                                                           ?? (mutexpost_exwt_return_prio_succ (|vl|)
                                                              ?? mutexpost_exwt_no_return_prio_succ (|vl|))
                                                         ;;isched;; END Some (V$NO_ERR)??
                     mutexpost_original_not_holder_err (|vl|) ??
                     mutexpost_prio_err (|vl|)  ?? mutexpost_wl_highest_prio_err (|vl|) \/
  s = mutexpost_null (|vl|) \/
  s = mutexpost_no_mutex_err (|vl|)
                             ?? mutexpost_type_err (|vl|)
                             ?? mutexpost_no_owner_err (|vl|)
                             ?? mutexpost_nowt_return_prio_succ (|vl|)
                                                                  ?? mutexpost_nowt_no_return_prio_succ (|vl|)
                                                                  ?? (mutexpost_exwt_return_prio_succ (|vl|)
                                                                  ?? mutexpost_exwt_no_return_prio_succ (|vl|))
                                   ;;isched;; END Some (V$NO_ERR)??
                     mutexpost_original_not_holder_err (|vl|) ??
                     mutexpost_prio_err (|vl|)  ?? mutexpost_wl_highest_prio_err (|vl|) \/
  s = mutexpost_no_mutex_err (|vl|) \/
  s = mutexpost_type_err (|vl|)
                         ?? mutexpost_no_owner_err (|vl|)
                         ?? mutexpost_nowt_return_prio_succ (|vl|)
                                                              ?? mutexpost_nowt_no_return_prio_succ (|vl|)
                                                              ?? (mutexpost_exwt_return_prio_succ (|vl|)
                                                              ?? mutexpost_exwt_no_return_prio_succ (|vl|))
                               ;;isched;; END Some (V$NO_ERR)??
                     mutexpost_original_not_holder_err (|vl|) ??
                     mutexpost_prio_err (|vl|)  ?? mutexpost_wl_highest_prio_err (|vl|)\/
  s = mutexpost_type_err (|vl|) \/
  s = mutexpost_no_owner_err (|vl|)
                             ?? mutexpost_nowt_return_prio_succ (|vl|)
                                                                  ?? mutexpost_nowt_no_return_prio_succ (|vl|)
                                                                  ?? (mutexpost_exwt_return_prio_succ (|vl|)
                                                                  ?? mutexpost_exwt_no_return_prio_succ (|vl|))
                                   ;;isched;; END Some (V$NO_ERR)??
                     mutexpost_original_not_holder_err (|vl|) ??
                     mutexpost_prio_err (|vl|)  ?? mutexpost_wl_highest_prio_err (|vl|) \/
  s = mutexpost_no_owner_err (|vl|) \/
  s = mutexpost_nowt_return_prio_succ (|vl|)
                                        ?? mutexpost_nowt_no_return_prio_succ (|vl|)
                                        ?? (mutexpost_exwt_return_prio_succ (|vl|)
                                        ?? mutexpost_exwt_no_return_prio_succ (|vl|))
         ;;isched;; END Some (V$NO_ERR)??
                     mutexpost_original_not_holder_err (|vl|) ??
                     mutexpost_prio_err (|vl|) ?? mutexpost_wl_highest_prio_err (|vl|) \/
  s = mutexpost_nowt_return_prio_succ (|vl|) \/
  s = mutexpost_nowt_no_return_prio_succ (|vl|)
                                        ?? (mutexpost_exwt_return_prio_succ (|vl|)
                                        ?? mutexpost_exwt_no_return_prio_succ (|vl|))
         ;;isched;; END Some (V$NO_ERR) ?? mutexpost_original_not_holder_err (|vl|) ??
                     mutexpost_prio_err (|vl|) ?? mutexpost_wl_highest_prio_err (|vl|) \/
  s = mutexpost_nowt_no_return_prio_succ (|vl|) \/
  s = (mutexpost_exwt_return_prio_succ (|vl|)
                                        ?? mutexpost_exwt_no_return_prio_succ (|vl|))
         ;;isched;; END Some (V$NO_ERR) ?? mutexpost_original_not_holder_err (|vl|) ??
                     mutexpost_prio_err (|vl|)  ?? mutexpost_wl_highest_prio_err (|vl|)\/
  s = (mutexpost_exwt_return_prio_succ (|vl|)
                                        ?? mutexpost_exwt_no_return_prio_succ (|vl|))
       ;;isched;; END Some (V$NO_ERR) \/                             
  s = mutexpost_original_not_holder_err (|vl|) ??
                                        mutexpost_prio_err (|vl|) ?? mutexpost_wl_highest_prio_err (|vl|) \/
  s = mutexpost_exwt_return_prio_succ (|vl|);;isched;; END Some (V$NO_ERR) \/
  s = mutexpost_exwt_no_return_prio_succ (|vl|);;isched;; END Some (V$NO_ERR) \/
  s = spec_done None ;;isched;; END Some (V$NO_ERR) \/
  s = isched;; END Some (V$NO_ERR) \/
  s = (ASSUME sc;; sched) ;; END Some (V$NO_ERR) \/
  s = (spec_done None;;sched) ;;END Some (V$NO_ERR) \/
  s = sched;; END Some (V$NO_ERR) \/
  s = ASSUME nsc;;END Some (V$NO_ERR) \/
  s = END None;;END Some (V$NO_ERR) \/
  s = mutexpost_original_not_holder_err (|vl|) \/
  s = mutexpost_prio_err (|vl|)  ?? mutexpost_wl_highest_prio_err (|vl|) \/
  s = mutexpost_prio_err (|vl|) \/
  s = mutexpost_wl_highest_prio_err (|vl|) \/
  exists v, s = spec_done v.

Definition GoodTick s:=
  s = timetick_spec (|nil|);;
                    ((isched;; END None)
                            ?? END None) \/
  s = spec_done None;;
                    ( (isched;; END None)
                            ?? END None) \/
  s =  ( (isched;; END None)
                            ?? END None)  \/
  s = (isched;; END None) \/
  s = (ASSUME sc;; sched) ;; END None \/
  s = (spec_done None;;sched) ;;END None \/
  s = sched;; END None \/
  s = ASSUME nsc;;END None \/
  s = spec_done None;;END None \/
  exists v, s = spec_done v.

Definition GoodToy s:=
  s = toyint_spec (|nil|);;
                    ((isched;; END None)
                            ?? END None) \/
  s = spec_done None;;
                    ( (isched;; END None)
                            ?? END None) \/
  s =  ( (isched;; END None)
                            ?? END None)  \/
  s = (isched;; END None) \/
  s = (ASSUME sc;; sched) ;; END None \/
  s = (spec_done None;;sched) ;;END None \/
  s = sched;; END None \/
  s = ASSUME nsc;;END None \/
  s = spec_done None;;END None \/
  exists v, s = spec_done v.

Definition good_api_stmt s:=
  (exists vl, GoodAcc s vl) \/
  (exists vl, GoodCre s vl) \/
  (exists vl, GoodDel s vl) \/
  (exists vl, GoodPend s vl) \/
  (exists vl, GoodPost s vl) \/
  ( GoodTick s ) \/
  ( GoodToy s ).

Fixpoint goodstmt_h (s : stmts) {struct s} : Prop :=
  match s with
    | sskip _ => True
    | sassign _ _ => True
    | sif _ s1 s2 => goodstmt_h s1 /\ goodstmt_h s2
    | sifthen _ s => goodstmt_h s
    | swhile _ s' => goodstmt_h s'
    | sret => True
    | srete _ => True
    | scall f _ => True
    | scalle _ f _ => True
    | sseq s1 s2 => goodstmt_h s1 /\ goodstmt_h s2
    | sprint _ => True
    | sfexec _ _ _ => True
    | sfree _ _ => True
    | salloc _ _ => True
    | sprim _ => False
    | hapi_code s => good_api_stmt s
  end.

Definition goodeval_h (c:cureval):=
  match c with
    | cure _ => True
    | curs s => goodstmt_h s
  end.

Fixpoint goodks_h ks:=
  match ks with
    | kint _ _ _ _ => False
    | kevent c ke ks' => goodeval_h c /\ goodks_h ks'
    | kstop => True
    | kcall _ s _ ks' => goodks_h ks' /\ goodstmt_h s
    | kseq s ks' => goodks_h ks' /\ goodstmt_h s
    | kassignr _ _ ks' => goodks_h ks'
    | kassignl _ _ ks' => goodks_h ks'
    | kfuneval _ _ _ _ ks' => goodks_h ks'
    | kif s1 s2 ks' => goodks_h ks' /\ goodstmt_h s1 /\ goodstmt_h s2
    | kwhile _ s ks' => goodks_h ks' /\ goodstmt_h s
    | kret ks' => goodks_h ks'
  end.

Definition goodcode_h (c:code):=
  match c with
    | (c,(ke,ks)) => goodeval_h c /\ goodks_h ks
  end.

Definition goodtasks_h T:=
  forall t c, TasksMod.get T t = Some c -> goodcode_h c.


Definition no_nest_client (client_code:progunit) O T cst:=
  forall  T' cst' O',
    hpstepstar (client_code, os_spec') T cst O T' cst' O' ->
    NO_NEST_PENDING_O O'.


Definition good_client_code client_code :=
      (forall (f : fid) (a : type) (b c : decllist) (s : stmts),
       client_code f = Some (a, b, c, s) -> GoodStmt_h s).

Definition INV_PROP (client_code:progunit) O T cst :=
  good_client_code client_code /\ no_nest_client  client_code O T cst /\ GOOD_ST O.

Definition apibound (api: fid -> option osapi)   T  (O:osabst) : Prop :=
  exists t  C ks cd f tl,
         exists (s:spec_code) tp  vl,
     OSAbstMod.get O curtid = Some (oscurt t) /\
     TasksMod.get T t = Some C /\
     C = (curs (hapi_code (cd vl)), (kenil,ks))
     /\ api f = Some (cd, (tp,tl))  /\ s = cd vl.


Definition intbound (ints : hid -> option int_code) 
           (T : TasksMod.map)  (O:osabst) : Prop := 
  exists cd h  t ke ks  c s C,
      OSAbstMod.get O curtid = Some (oscurt t) /\
      TasksMod.get T t = Some C /\
      C = (curs (hapi_code s), (kenil, kevent c ke ks))
       /\ ints h = Some cd /\ s = cd.

Require Import auxdef.
Lemma good_clt_imp :
  forall C pc, good_clt C pc -> 
      ~(exists s' ke' ks', C = (curs (hapi_code s'), (ke',ks'))).
Proof.
  intros.
  introv Hf.
  mytac.
  simpl in H.
  mytac.
  auto.
Qed.

Lemma cstep_good_clt_hold:
  forall pc C m C' m' ,
    good_clt C pc ->
    cstep pc C m C' m' ->
    good_clt C' pc.
 Proof.
   introv Hgood Hcs.
   inverts Hcs.
   inverts H0; simpl; auto.
   inverts H0; simpl; auto; simpl in Hgood;
   mytac; auto.
   rewrite H in H2.
   tryfalse.
   eapply step_prop.good_clt_scont_callcont; eauto.
Qed.   
 

 Definition nhapi T pc :=
   forall  t C,  TasksMod.get T t = Some C ->  good_clt C pc .


 Lemma nhapi_set_hold:
   forall T C t pc,          
     nhapi T pc-> 
     good_clt C pc ->
     nhapi (TasksMod.set T t C) pc.
 Proof.   
   introv Hnp Hne.
   unfolds in Hnp.
   unfolds.
   intros.
   rewrite TasksMod.set_sem in H.
   assert (t=t0 \/ t <> t0) by tauto.
   destruct H0.
   subst .
   rewrite tidspec.eq_beq_true in H; auto.
   inverts H.
   auto.
   rewrite tidspec.neq_beq_false in H; eauto.
 Qed.

Lemma cstep_nhapi_hold:
  forall pc C m C' m' t T,
    nhapi T pc->
    cstep pc C m C' m' ->
    TasksMod.get T t = Some C ->
    nhapi (TasksMod.set T t C') pc.
Proof.
  introv Hcs Hget Hn.
  apply Hcs in  Hn.
  lets Hres : cstep_good_clt_hold Hget; eauto.
  eapply nhapi_set_hold; eauto.
Qed.


Ltac destruct_inverts1 H:=
  let Hx:= fresh in
  match type of H with
    | ?H1 \/ ?H2 => destruct H as [Hx | H]; [inverts Hx | destruct_inverts1 H]
    | exists _, _ = _ => let x:= fresh in (destruct H as (x&H);inverts H)
    | _ => idtac
  end.

Lemma callcont_goodks:
  forall ks f s le ks',
    callcont ks = Some (kcall f s le ks') ->
    goodks_h ks ->
    goodks_h ks'.
Proof.
  induction ks;intros;simpl in *;auto;tryfalse;mytac.
  apply IHks in H;auto.
  inverts H;auto.
  apply IHks in H;auto.
  apply IHks in H;auto.
  apply IHks in H;auto.
  apply IHks in H;auto.
  apply IHks in H;auto.
  apply IHks in H;auto.
  apply IHks in H;auto.
Qed.

Open Scope nat_scope.
Lemma hapistep_goodcode:
  forall C O c O',
    goodcode_h C->
    goodcode_h C -> 
    goodcode_h C ->
    goodcode_h C ->
    goodcode_h C ->
    goodcode_h C ->
    goodcode_h C -> 
    hapistep os_spec' C O c O' ->
    goodcode_h c.
Proof.
  intros.
  clear H2 H0.
  
  inverts H6.
  unfolds in H0.
  inverts H0.
  unfolds in H9.
  simpl in H9.
  remember (Zeq_bool OSMutexAccept f) as X.
  destruct X.
  inverts H9.
  simpl in H1.
  simpl.
  mytac;auto.
  unfolds.
  left.
  exists vl.
  unfolds.
  left;auto.
  remember (Zeq_bool OSMutexCreate f) as X0.
  destruct X0.
  inverts H9.
  simpl in H1.
  simpl.
  mytac;auto.
  unfolds.
  right;left.
  exists vl.
  unfolds.
  left;auto.
  remember (Zeq_bool OSMutexDel f) as X1.
  destruct X1.
  inverts H9.
  simpl in H1.
  simpl.
  mytac;auto.
  unfolds.
  right;right;left.
  exists vl.
  unfolds.
  left;auto.
  remember (Zeq_bool OSMutexPend f) as X1.
  destruct X1.
  inverts H9.
  simpl in H1.
  simpl.
  mytac;auto.
  unfolds.
  right;right;right;left.
  exists vl.
  unfolds.
  unfold mutexpend.
  left;auto.

  remember (Zeq_bool OSMutexPost f) as X1.
  destruct X1.
  inverts H9.
  simpl in H1.
  simpl.
  mytac;auto.
  unfolds.
  right;right;right;right;left.
  exists vl.
  unfolds.
  unfold mutexpost.
  left;auto.
  
  tryfalse.

  (*----------------*)
  simpl in H1.
  simpl;mytac;auto.
  unfolds in H1.

  (* acc *)
  destruct H1.
  unfold GoodAcc in H1.
  mytac.
  destruct_inverts1 H1.
  inverts H0;tryfalse.
  unfolds.
  left.
  eexists;unfolds.
  right;left;auto.
  unfolds.
  left.
  eexists;unfolds.
  right;right;left;auto.
  inverts H0.
  unfolds.
  left.
  eexists;unfolds.
  right;right;right.
  branch 7%nat.
  eexists;eauto.
  inverts H0.
  unfolds.
  left.
  eexists;unfolds.
  branch 4;eauto.
  unfolds.
  left.
  eexists;unfolds.
  branch 5;eauto.
  inverts H0.
  unfolds.
  left.
  eexists;unfolds.
  right;right;right;branch 7.
  eexists;eauto.
  inverts H0.
  unfolds.
  left.
  eexists;unfolds.
  branch 6;eauto.
  unfolds.
  left.
  eexists;unfolds.
  branch 7;eauto.
  inverts H0.
  left.
  eexists;unfolds.
  right;right;right;branch 7.
  eexists;eauto.
  inverts H0.
  unfolds.
  left.
  eexists;unfolds.
  branch 8;eauto.
  unfolds.
  left.
  eexists;unfolds.
  right;branch 8;eauto.
  inverts H0.
  unfolds.
  left.
  eexists;unfolds.
  right;right;right;branch 7.
  eexists;eauto.
  inverts H0.
  unfolds.
  left.
  eexists;unfolds.
  right;right;right;branch 7.
  eexists;eauto.
  inverts H0.
  (* cre *)
  destruct H1.
  unfold GoodCre in H1.
  mytac.
  destruct_inverts1 H1.
  inverts H0;tryfalse.
  unfolds.
  right;left.
  eexists;unfolds.
  right;left;eauto.
  unfolds.
  right;left.
  eexists;unfolds.
  right;right;left;eauto.

  inverts H0;tryfalse.
  unfolds.
  right;left.
  eexists;unfolds.
  branch 4;eauto.

  inverts H0;tryfalse.
  unfolds.
  right;left.
  eexists;unfolds.
  branch 4;eauto.

  inverts H0.

  (*del*)
  destruct H1.
  unfold GoodDel in H1.
  mytac.

  destruct_inverts1 H1.
  inverts H0;tryfalse.
  unfolds.
  branch 3.
  eexists;unfolds.
  branch 2;auto.
  unfolds;branch 3.
  eexists;unfolds.
  branch 3;eauto.

  inverts H0.
  unfolds.
  branch 3.
  eexists;unfolds.
  right;right;right;right;branch 8.
  eexists;eauto.
  inverts H0.
  unfolds.
  branch 3.
  eexists;unfolds.
  branch 4;auto.
  unfolds.
  branch 3.
  eexists;unfolds.
  branch 5;auto.

  inverts H0.
  unfolds;branch 3.
  eexists;unfolds.
  right;right;right;right;branch 8.
  eauto.

  inverts H0.
  unfolds;branch 3.
  eexists;unfolds.
  branch 6;auto.
  unfolds;branch 3.
  eexists;unfolds.
  branch 7;auto.

  inverts H0.
  unfolds;branch 3.
  eexists;unfolds.
  right;right;right;right;branch 8.
  eexists;eauto.

  inverts H0.
  unfolds;branch 3.
  eexists;unfolds.
  branch 8;auto.
  unfolds;branch 3.
  eexists;unfolds.
  right;branch 8;auto.

  inverts H0.
  unfolds;branch 3.
  eexists;unfolds.
  right;right;right;right;branch 8.
  eexists;eauto.

  inverts H0.
  unfolds;branch 3.
  eexists;unfolds.
  right;right;branch 8.
  eauto.

  unfolds;branch 3.
  eexists;unfolds.
  branch 8.
  branch 4;eauto.

  inverts H0.
  unfolds;branch 3.
  eexists;unfolds.
  right;right;right;right;branch 8.
  eexists;eauto.

  inverts H0.
  unfolds;branch 3.
  eexists;unfolds.
  right;right;right;right;branch 8.
  eexists;eauto.
  inverts H0.
  
  (*pend*)
  destruct H1.
  unfold GoodPend in H1.
  mytac.

  destruct_inverts1 H1.
  
  inverts H0;tryfalse.
  unfolds;branch 4.
  eexists;unfolds.
  branch 2;auto.
  unfolds;branch 4.
  eexists;unfolds.
  branch 3;simpl;eauto.

  inverts H0;tryfalse.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8;branch 8;branch 8;branch 5.
  eauto.

  inverts H0;tryfalse.
  unfolds;branch 4.
  eexists;unfolds.
  branch 4;auto.
  unfolds;branch 4.
  eexists;unfolds.
  branch 5;auto.
  
  inverts H0;tryfalse.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8;branch 8;branch 8;branch 5.
  eauto.

  inverts H0;tryfalse.
  unfolds;branch 4.
  eexists;unfolds.
  branch 6;auto.
  unfolds;branch 4.
  eexists;unfolds.
  branch 7;eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8;branch 8;branch 8;branch 5;eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;auto.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8.
  branch 2;auto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8;branch 8;branch 8;branch 5.
  eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8.
  branch 3;auto.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8.
  branch 4;auto.
  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8;branch 8;branch 8;branch 5;eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8.
  branch 5;auto.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8.
  branch 6;auto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8;branch 8;branch 8;branch 5;eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8.
  branch 7;auto.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8.
  branch 8;auto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8;branch 8;branch 8;branch 5;eauto.

  inverts H0.
  unfolds.
  branch 4.
  eexists;unfolds.
  branch 8.
  branch 8.
  right.
  left.
  eauto.

  unfolds;branch 4.
  eexists;unfolds.
  branch 8.
  branch 8.
  branch 3;eauto.
  
  inverts H0.
  inverts H12.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8.
  branch 7;auto.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8;branch 8;auto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 4;eauto.

  
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 5;eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds;branch 8;branch 8;branch 8;branch 8;branch 8;branch 5.
  eauto.
  
  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 6;auto.

  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 7;auto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds;branch 8;branch 8;branch 8;branch 8;branch 8;branch 5.
  eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8;auto.

  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8;eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds;branch 8;branch 8;branch 8;branch 8;branch 8;branch 5.
  eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds;branch 8;branch 8;branch 8;branch 3.
  eauto.
  
  unfolds;branch 4.
  eexists;unfolds;branch 8;branch 8;branch 8.
  branch 4.
  eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds;branch 8;branch 8;branch 8;branch 8;branch 8;branch 5.
  eauto.
  
  inverts H0.
  unfolds;branch 4.
  eexists;unfolds;branch 8;branch 8;branch 8.
  branch 5.
  eauto.

  unfolds;branch 4.
  eexists;unfolds;branch 8;branch 8;branch 8.
  branch 6.
  eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds;branch 8;branch 8;branch 8;branch 8;branch 8;branch 5.
  eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds;branch 8;branch 8;branch 8;branch 8;branch 8;branch 5.
  eauto.

  inverts H0.
  inverts H12.
  unfolds in H7.
  mytac.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8.
  branch 8.
  branch 2.
  auto.

  inverts H0.
  inverts H12.
  unfolds in H7.
  mytac.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8; branch 8.
  branch 2.
  auto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8; branch 8.
  branch 3.
  auto.

  inverts H12.

  inverts H0.
  inverts H12.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8;branch 8.
  branch 4;auto.

  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8;branch 8.
  branch 7;auto.

  inverts H0.
  inverts H12.
  inverts H11.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8.
  branch 8.
  branch 5;auto.

  inverts H0.
  inverts H12.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8.
  branch 8.
  branch 6;auto.

  inverts H11.

  inverts H0.
  inverts H12.

  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8.
  branch 8;branch 8;eauto.

  inverts H0.
  inverts H12.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8.
  branch 8;branch 8;eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8.
  branch 8;branch 8;eauto.

  inverts H12.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8.
  branch 8;branch 8;eauto.

  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8.
  branch 8;branch 8;eauto.
  
  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8.
  branch 8;branch 8;branch 5;eauto.

  inverts H0.
  unfolds;branch 4.
  eexists;unfolds.
  branch 8;branch 8;branch 8.
  branch 8;branch 8;branch 5;eauto.

  inverts H0.
  
  (* post *)
  destruct H1.
  unfold GoodPost in H1.
  mytac.
  destruct_inverts1 H1.
  
  inverts H0;tryfalse.
  unfolds;branch 5.
  eexists;unfolds.
  branch 2;auto.
  unfolds;branch 5.
  eexists;unfolds.
  branch 3;simpl;eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8.
  branch 8.
  branch 8.
  branch 8.
  eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 4;auto.
  unfolds;branch 5.
  eexists;unfolds.
  branch 5;simpl;eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8;branch 8;branch 8;eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 6;auto.
  unfolds;branch 5.
  eexists;unfolds.
  branch 7;simpl;eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8;branch 8;branch 8;eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;auto.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8.
  branch 2;simpl;eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8;branch 8;branch 8;eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;auto.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8.
  branch 4;simpl;eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8;branch 8;branch 8;eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 5.
  eauto.
  
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 6.
  eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8;branch 8;branch 8;eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 7.
  auto.

  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8.
  left.
  auto.

  inverts H0.
  inverts H12.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8.
  branch 2;auto.

  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8.
  branch 3;auto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8.
  branch 4.
  auto.

  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8.
  branch 5.
  auto.

  inverts H0.
  inverts H12.
  unfolds;branch 5.
  inverts H7.
  mytac.
  eexists;unfolds.
  branch 8;branch 8.
  branch 4;auto.

  inverts H0.
  inverts H12.
  inverts H7.
  mytac.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8.
  branch 4;auto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8.
  branch 5;auto.

  inverts H12.
  
  inverts H0.
  inverts H12.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8.
  branch 6;auto.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8.
  branch 2;auto.
  
  inverts H0.
  inverts H12.
  inverts H11.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8.
  branch 7;auto.

  inverts H0.
  inverts H12.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8;auto.
  
  inverts H11.
  inverts H0.
  inverts H12.
  unfolds;branch 5.
  eexists;unfolds.
  
  branch 8;branch 8;branch 8.
  branch 3;auto.
  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8.
  branch 8.
  branch 3.
  inverts H12.
  auto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8;branch 8.
  branch 8;eauto.

  inverts H12.
  
  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8;branch 8.
  branch 8.
  eauto.
  
  inverts H0.
  unfolds.
  branch 5.
  eexists.
  unfolds.
  branch 8;branch 8;branch 8.
  branch 6;eauto.

  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8;branch 8.
  branch 7.
  eauto.

  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8;branch 8.
  branch 8.
  eauto.
  inverts H0.
  unfolds;branch 5.
  eexists;unfolds.
  branch 8;branch 8;branch 8.
  branch 8.
  eauto.

  inverts H0.
  (*timetick*)
  destruct H1.
  unfold GoodTick in H1.
  mytac.
  destruct_inverts1 H1;clear H H3 H4 H5.

  inverts H0.
  inverts H8.
  inverts H3;mytac.
  unfolds;branch 6.
  unfolds.
  branch 2;auto.

  inverts H0.
  unfolds;branch 6.
  unfolds.
  branch 3;auto.
  inverts H8.

  inverts H0.
  unfolds;branch 6.
  unfolds.
  branch 4;auto.
  unfolds;branch 6.
  unfolds.
  branch 8.
  branch 3;eauto.
  
  inverts H0.
  inverts H8.
  unfolds.
  branch 6.
  unfolds.
  branch 5;auto.

  unfolds.
  branch 6.
  unfolds.
  branch 8;auto.
  
  inverts H0.
  inverts H8.
  inverts H7.
  unfolds;branch 6.
  unfolds.
  branch 6;auto.

  inverts H0.
  inverts H8.
  unfolds;branch 6.
  unfolds.
  branch 7;auto.

  inverts H7.
  inverts H0.
  inverts H8.
  unfolds;branch 6.
  unfolds.
  branch 8.
  branch 2;auto.
  inverts H0.
  unfolds;branch 6.
  unfolds.
  branch 8.
  inverts H8.
  branch 2;eauto.

  inverts H0.
  unfolds;branch 6.
  unfolds.
  branch 8.
  branch 3;eauto.
  inverts H8.
  inverts H0.

  (*toy*)
  unfold GoodToy in H1.
  mytac.
  destruct_inverts1 H1;clear H H3 H4 H5.

  inverts H0.
  inverts H8.
  inverts H3;mytac.
  unfolds;branch 7.
  unfolds.
  branch 2;auto.

  inverts H0.
  unfolds;branch 7.
  unfolds.
  branch 3;auto.
  inverts H8.

  inverts H0.
  unfolds;branch 7.
  unfolds.
  branch 4;auto.
  unfolds;branch 7.
  unfolds.
  branch 8.
  branch 3;eauto.
  
  inverts H0.
  inverts H8.
  unfolds.
  branch 7.
  unfolds.
  branch 5;auto.

  unfolds.
  branch 7.
  unfolds.
  branch 8;auto.
  
  inverts H0.
  inverts H8.
  inverts H7.
  unfolds;branch 7.
  unfolds.
  branch 6;auto.

  inverts H0.
  inverts H8.
  unfolds;branch 7.
  unfolds.
  branch 7;auto.

  inverts H7.
  inverts H0.
  inverts H8.
  unfolds;branch 7.
  unfolds.
  branch 8.
  branch 2;auto.
  inverts H0.
  inverts H8.
  unfolds;branch 7.
  unfolds.
  branch 8.
  branch 2;eauto.

  inverts H0.
  unfolds;branch 7.
  unfolds.
  branch 8.
  branch 3;eauto.
  inverts H8.
  inverts H0.
 

  simpl in H.
  simpl;mytac;auto.
  simpl.
  simpl in H5.
  mytac;auto.
  Grab Existential Variables.
  trivial. trivial. trivial. trivial. trivial.
  trivial. trivial. trivial. 
  trivial.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
  exact nil.
Qed.

Lemma htstep_goodcode_h:
  forall pc t C cst O c cst' O',
    good_client_code pc ->
    htstep (pc, os_spec') t C cst O c cst' O' ->
    goodcode_h C ->
    goodcode_h c.
Proof.
  intros.
  inverts H0.

  inverts H2.

  inverts H3.
  inverts H2;simpl in H1;simpl;mytac;auto;tryfalse.
  
  inverts H2;simpl in H1;simpl;mytac;auto;tryfalse.
  apply H in H4.
  clear -H4.
  induction s;simpl in H4;simpl;auto;tryfalse.
  mytac.
  eapply IHs1;eauto.
  eapply IHs2;eauto.
  mytac.
  eapply IHs1;eauto.
  eapply IHs2;eauto.

  eapply callcont_goodks;eauto.

  inverts H2.

  eapply hapistep_goodcode;eauto.
Qed.


Lemma hpstep_goodcode_h:
  forall pc T cst O T' cst' O',
    goodtasks_h T ->
    good_client_code pc ->
    hpstep (pc,os_spec') T cst O T' cst' O' ->
    goodtasks_h T'.
Proof.
  intros.
  inverts H1.
  unfolds;intros.
  assert ( t <> t0 \/ t = t0) by tauto.
  destruct H5.
  rewrite TasksMod.set_a_get_a' in H1;[ | apply tidspec.neq_beq_false;auto].
  apply H in H1;auto.

  rewrite TasksMod.set_a_get_a in H1;[ | apply tidspec.eq_beq_true;auto]. 
  inverts H1.
  subst t0.
  apply H in H4.
  eapply htstep_goodcode_h;eauto.

  inverts H6.
  unfolds;intros.
  assert ( t <> t0 \/ t = t0) by tauto.
  destruct H6.
  rewrite TasksMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
  apply H in H5;auto.

  rewrite TasksMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto]. 
  inverts H5.
  subst t0.
  apply H in H4.
  simpl in H4.
  simpl.
  mytac;auto.
  unfolds in H1.
  simpl in H1.
  destruct i.
  inverts H1.
  unfolds.
  branch 6.
  unfold timetick.
  unfold GoodTick.
  left;auto.
  destruct i.
  inverts H1.
  unfolds.
  branch 7.
  unfold toyint.
  unfold GoodToy.
  left;auto.
  inverts H1.

  unfolds.
  intros.
  assert (t <> t0 \/ t = t0) by tauto.
  destruct H6.
  rewrite TasksMod.set_a_get_a' in H1;[ | apply tidspec.neq_beq_false;auto].
  apply H in H1;auto.
  rewrite TasksMod.set_a_get_a in H1;[ | apply tidspec.eq_beq_true;auto]. 
  inverts H1.
  subst t0.
  apply H in H5.
  unfold goodcode_h in *.
  mytac;auto.
  unfold goodeval_h in *.
  unfold goodstmt_h in *.
  unfold good_api_stmt in *.
  destruct H1.
  mytac.
  unfolds in H1.
  destruct H1;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.

  destruct H1.
  unfold GoodCre in H1;mytac.
  destruct H1;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.

  destruct H1.
  unfold GoodDel in H1;mytac.
  destruct H1;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  
  destruct H1.
  unfold GoodPend in H1;mytac.
  destruct H1;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  branch 4.
  exists x.
  unfolds.
  branch 8.
  branch 8.
  branch 8.
  branch 8.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  
  destruct H2;inverts H1.
  inverts H2.
  
  destruct H2;inverts H1.
  inverts H2.

  branch 8.
  eauto.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2.
  inverts H1.
  mytac.
  inverts H1.

  destruct H1.
  Focus 1.
  unfold GoodPost in H1;mytac.
  destruct H1;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  branch 5.
  exists x.
  unfolds.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  eexists;eauto.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2.
  inverts H1.
  destruct H1.
  inverts H1.
  destruct H1;inverts H1.
  
  destruct H1.
  unfold GoodTick in H1.
  mytac.
  destruct H1;inverts H1.
  inverts H2.
  
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  branch 6.
  unfolds.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  eexists;auto.
  inverts H2.
  inverts H2.
  inverts H1.
  destruct H1;inverts H1.

  unfold GoodToy in H1.
  mytac.
  destruct H1;inverts H1.
  inverts H2.
  
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  inverts H2.
  destruct H2;inverts H1.
  branch 6.
  unfolds.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  eexists;auto.
  inverts H2.
  inverts H2.
  inverts H1.
  destruct H1;inverts H1.
  (*
  unfolds.
  intros.
  assert (t0 = t' \/ t0 <> t') by tauto.
  destruct H2.
  subst.
  rewrite TasksMod.map_get_set in H1.
  inverts H1.
  simpl.
  split;auto.
  unfolds in H0.
  apply H0 in H9.
  clear -H9.
  inductions s;simpl in *;mytac;auto;tryfalse.
  
  SearchAbout (_<>_ -> TasksMod.get _ _ = _ ).
  rewrite tasks_set_get_neq in H1.
  assert (t0 = t \/ t0 <> t) by tauto.
  destruct H3.
  subst.
  rewrite TasksMod.map_get_set in H1.
  inverts H1.
  simpl.*)
  unfolds in H.
  apply H in H4.
  simpl in H4.
  destruct H4.
  unfolds in H1.
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  unfolds in H.
  apply H in H4.
  simpl in H4.
  destruct H4.
  unfolds in H1.
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  unfolds in H.
  apply H in H2.
  simpl in H2.
  destruct H2.
  unfolds in H1.
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
Qed.

Lemma hpstepstar_goodcode_h:
  forall pc T cst O T' cst' O',
    hpstepstar (pc,os_spec') T cst O T' cst' O' ->
    goodtasks_h T ->
    good_client_code pc ->
    goodtasks_h T'.
Proof.
  intros.
  inductions H;auto.
  eapply IHhpstepstar;eauto.
  eapply hpstep_goodcode_h;eauto.
Qed.

Lemma hpstep_goodcode_goodapi:
  forall pc T cst O T' cst' O',
    goodtasks_h T ->
    good_client_code pc ->
    hpstep (pc,os_spec') T cst O T' cst' O' ->
    O = O' \/ GOOD_API_CODE O T.
Proof.
  intros.
  inverts H1.
  inverts H3;try solve [left;auto].

  (*api step*)

  inverts H1.
  lets Hx: H H4.
  inverts H5;try solve [left;auto].
  simpl in Hx.
  mytac.
  unfolds in H3.
  destruct H3.

  (*acc*)
  unfold GoodAcc in H3;mytac.
  destruct_inverts1 H3;inverts H1;try solve [left;auto].
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.

  right.
  unfolds.
  exists (curs (hapi_code (mutexacc_succ (|x|))), (ke, ks)) t.
  mytac;auto.
  left;do 3 eexists;eauto.

  (*cre*)
  destruct H3.
  unfold GoodCre in H3;mytac.
  destruct_inverts1 H3;inverts H1;try solve [left;auto].
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.

  right.
  unfolds.
  exists (curs (hapi_code (mutexcre_succ (|x|))), (ke, ks)) t.
  mytac;auto.
  right;left;do 3 eexists;eauto.

  (*del*)
  destruct H3.
  unfold GoodDel in H3;mytac.
  destruct_inverts1 H3;inverts H1;try solve [left;auto].
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.

  right.
  unfolds.
  exists (curs (hapi_code (mutexdel_succ (|x|))), (ke, ks)) t.
  mytac;auto.
  right;right;left;do 3 eexists;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  (*pend*)
  destruct H3.
  unfold GoodPend in H3;mytac.
  destruct_inverts1 H3;inverts H1;try solve [left;auto].
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  
  right.
  unfolds.
  exists (curs (hapi_code (mutexpend_get_succ (|x|))), (ke, ks)) t.
  mytac;auto.
  right;right;right;left;do 3 eexists;eauto.

  inverts H12.
  left;auto.
  left;auto.
  inverts H8.
  left;eapply map_join_deter;eauto.
  
  unfolds in H8.
  mytac.
  left;eapply map_join_deter;eauto.

  inverts H8.
  mytac.
  left;eapply map_join_deter;eauto.

  
  inverts H8.
  mytac.
  left;eapply map_join_deter;eauto.
  
  inverts H8.
  mytac.
  left;eapply map_join_deter;eauto.
  
  inverts H8.
  mytac.
  left;eapply map_join_deter;eauto.
  
  right.
  unfolds.
  exists (curs
            (hapi_code
               (mutexpend_block_lift (|x|);;
                isched;; (mutexpend_to (|x|) ?? mutexpend_block_get (|x|)))),
         (ke, ks)) t.
  mytac;auto.
  right;right;right;right;right;left.
  do 4 eexists;eauto.

  right.
  unfolds.
  exists (curs
            (hapi_code
               (mutexpend_block_no_lift (|x|);;
                isched;; (mutexpend_to (|x|) ?? mutexpend_block_get (|x|)))),
         (ke, ks)) t.
  mytac;auto.
  right;right;right;right;left.
  do 4 eexists;eauto.

  inverts H12.

  inverts H12.
  left;auto.
  left;auto.
  inverts H12.
  inverts H11.
  left;auto.
  inverts H12.
  left;auto.
  inverts H11.

  right.
  unfolds.
  exists (curs
            (hapi_code
               (sched;; (mutexpend_to (|x|) ?? mutexpend_block_get (|x|)))),
         (ke, ks)) t.
  mytac;auto.
  branch 8.
  branch 5.
  do 3 eexists;eauto.

  inverts H12;left;auto.

  inverts H12.
  inverts H8.
  mytac.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;left;eapply map_join_deter;eauto.

  (*post*)
  destruct H3.
  unfold GoodPost in H3;mytac.
  destruct_inverts1 H3;inverts H1;try solve [left;auto].
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.
  inverts H8;mytac;subst.
  left;eapply map_join_deter;eauto.

  right.
  unfolds.
  exists  (curs
            (hapi_code
               (mutexpost_nowt_return_prio_succ (|x|))), (ke, ks)) t.
  mytac;auto.
  branch 7.
  do 3 eexists;eauto.

  right.
  unfolds.
  exists  (curs
            (hapi_code
               (mutexpost_nowt_no_return_prio_succ (|x|))), (ke, ks)) t.
  mytac;auto.
  branch 8.
  left;do 3 eexists;eauto.

  inverts H12;left;auto.
  
  right.
  unfolds.
  exists  (curs
            (hapi_code
               (mutexpost_exwt_return_prio_succ (|x|);;
                isched;; END Some (V$NO_ERR))), (ke, ks)) t.
  mytac;auto.
  branch 8.
  branch 2.
  do 3 eexists;eauto.

  right.
  unfolds.
  exists  (curs
            (hapi_code
               (mutexpost_exwt_no_return_prio_succ (|x|);;
                isched;; END Some (V$NO_ERR))), (ke, ks)) t.
  mytac;auto.
  branch 8.
  branch 3.
  do 3 eexists;eauto.

  inverts H12.
  inverts H12;left;auto.
  inverts H12.
  inverts H11;left;auto.

  inverts H12;left;auto.
  inverts H11.

  right.
  unfolds.
  exists  (curs (hapi_code (sched;; END Some (V$NO_ERR))), (ke, ks)) t.
  mytac;auto.
  branch 8.
  branch 5.
  do 3 eexists;eauto.

  inverts H12;left;auto.
  inverts H12.
  inverts H8;mytac;left;eapply map_join_deter;eauto.
  inverts H8;mytac;left;eapply map_join_deter;eauto.
  inverts H8;mytac;left;eapply map_join_deter;eauto.
  (*timetick*)
  destruct H3.
  unfold GoodTick in H3.
  mytac.
  destruct_inverts1 H3;inverts H1;try solve [left;auto].

  right.
  unfolds.
  exists (curs
            (hapi_code
               (timetick_spec (|nil|);;
                ( isched;; END None ?? END None
                 ))), (ke, ks)) t.
  mytac;auto.
  branch 8.
  branch 4.
  do 3 eexists;eauto.
  inverts H12.
  inverts H12;left;auto.
  inverts H12.
  inverts H11;left;auto.
  inverts H12;left;auto.
  inverts H11.
  inverts H12;left;auto.
  inverts H12;left;auto.
  inverts H12.
 
  (*toy int*)
  unfold GoodToy in H3.
  mytac.
  destruct_inverts1 H3;inverts H1;try solve [left;auto].

  left.
  inverts H12.
  unfolds in H7.
  mytac;eapply map_join_deter;eauto.
 
  inverts H12.
  inverts H12;left;auto.
  inverts H12.
  inverts H11;left;auto.
  inverts H12;left;auto.
  inverts H11.
  inverts H12;left;auto.
  inverts H12;left;auto.
  inverts H12.


  (*int step*)
  inverts H6.
  left;auto.
  (*sched*)
  right.
  unfolds.
  exists (curs (hapi_code (sched;; s)), (ke, ks)) t.
  mytac;auto.
  branch 8.
  branch 5.
  do 3 eexists;eauto.

    unfolds in H.
  apply H in H4.
  simpl in H4.
  destruct H4.
  unfolds in H1.
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  unfolds in H.
  apply H in H4.
  simpl in H4.
  destruct H4.
  unfolds in H1.
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  unfolds in H.
  apply H in H2.
  simpl in H2.
  destruct H2.
  unfolds in H1.
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  destruct H1.
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
  unfolds in H1.
  repeat progress (destruct H1;tryfalse).
Qed.

Lemma init_goodks_h:
  forall T client_code cst O,
    InitTasks T client_code cst O ->
    INV_PROP client_code O T cst ->
    goodtasks_h T .
Proof.
  intros.
  unfolds in H.
  unfolds.
  intros.
  mytac.
  apply H2 in H1.
  mytac.
  unfolds in H0.
  mytac.
  unfolds in H0.
  apply H0 in H3.
  clear -H3.
  unfolds.
  unfolds in H3.
  induction x;simpl in *;auto;tryfalse.
  mytac.
  apply IHx1;auto.
  apply IHx2;auto.
  mytac.
  apply IHx1;auto.
  apply IHx2;auto.
Qed.

Lemma code_exe_prop1:
  forall client_code T cst O T' cst' O' T'' O'' cst'',
    good_client_code client_code  ->
    goodtasks_h T -> 
    hpstepstar (client_code, os_spec') T cst O T' cst' O' ->
    hpstep (client_code, os_spec') T' cst' O' T'' cst'' O''->
    O' = O'' \/ GOOD_API_CODE O' T'.
Proof.
  intros.
  eapply hpstep_goodcode_goodapi;eauto.
  eapply hpstepstar_goodcode_h;eauto.
Qed.



Lemma  tcbjoinsig_set_sub_sub:
  forall t x tcbls tcbls' tls y tls',
    TcbMod.joinsig t x tcbls tcbls' ->
    TcbMod.set tls t y = tls' ->
    TcbMod.sub tcbls' tls ->
    TcbMod.sub tcbls tls'.
Proof.
  intros.
  unfolds; intros.
  unfold TcbMod.joinsig in H.
  unfold TcbMod.sub in H1.
  unfold TcbMod.lookup in *.
  pose proof H a.
  substs.
  rewrite H2 in H3.
  destruct (tidspec.beq t a) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.get_sig_some in H3; tryfalse.
  pose proof tidspec.beq_false_neq _ _ eq1.
  rewrite TcbMod.get_sig_none in H3; auto.
  destruct (TcbMod.get tcbls' a) eqn : eq2; tryfalse.
  apply H1 in eq2; substs.
  rewrite TcbMod.set_a_get_a'; auto.
Qed.



Lemma sub_joinsig_get:
  forall tls_used tls t x tls_used',
    TcbMod.sub tls_used tls -> TcbMod.joinsig t x tls_used' tls_used -> TcbMod.get tls t = Some x.
Proof.
  intros.
  pose proof H0 t.
  rewrite TcbMod.get_sig_some in H1.
  destruct (TcbMod.get tls_used' t); tryfalse.
  destruct (TcbMod.get tls_used t) eqn : eq1; tryfalse.
  substs.
  unfolds in H.
  unfold TcbMod.lookup in H.
  apply H in eq1; auto.
Qed.

Lemma tickchange_goodst:
  forall tls els tls' els' st' t0 p st msg0,
    NO_NEST_PENDING tls els -> 
    TcbMod.get tls t0 = Some (p, st, msg0)->
    (rdy_notin_wl tls els /\

     owner_prio_prop tls els /\
     task_stat_prop tls /\
     op_p_prop tls els /\
     wait_prop tls els /\ no_owner_prio_prop tls els) ->
    tickchange t0 st els st' els' ->
    TcbMod.set tls t0 (p, st', msg0) = tls' ->
    (rdy_notin_wl tls' els' /\

     owner_prio_prop tls' els' /\
     task_stat_prop tls' /\
     op_p_prop tls' els' /\ wait_prop tls' els' /\ no_owner_prio_prop tls' els'
    ).
Proof.
  intros.
  inverts H2;auto;tryfalse.
  (*================*)
  rewrite TcbMod.get_set_same in H3;auto.
  subst;auto.

  (*=============*)
  destructs H1.
  unfold task_stat_prop in *.
  apply H4 in H0.
  destruct H0.
  inverts H0.
  do 2 destruct H0.
  tryfalse.

  (*==============*)
  destructs H1.
  unfold task_stat_prop in *.
  apply H4 in H0.
  destruct H0.
  inverts H0.
  do 2 destruct H0.
  tryfalse.


  (*=============*)
  mytac.
  unfold rdy_notin_wl in *.
  mytac.
  intros.
  assert (t0 <> t).
  intro.
  subst t0.
  rewrite TcbMod.set_a_get_a in H12;[ | apply tidspec.eq_beq_true;auto].
  inverts H12.
  rewrite TcbMod.set_a_get_a' in H12;[ | apply tidspec.neq_beq_false;auto].
  apply H1 in H12;auto.

  intros.
  assert (t0 <> t \/ t0 = t) by tauto.
  destruct H13.
  rewrite TcbMod.set_a_get_a' in H12;[ | apply tidspec.neq_beq_false;auto].
  apply H3 in H12;auto.
  subst t0.
  rewrite TcbMod.set_a_get_a in H12;[ | apply tidspec.eq_beq_true;auto].
  inverts H12.
  apply H3 in H0.
  auto.
  
  intros.
  apply H11 in H12.
  mytac.
  assert (t0 <> t \/ t0 = t) by tauto.
  destruct H13.
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.

  subst t0.
  rewrite H12 in H0;inverts H0.
  rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  do 3 eexists;eauto.

  (*---------------------*)
  unfold owner_prio_prop in *.
  intros.

  assert (t0 <> t \/ t0 = t) by tauto.
  destruct H12.
  eapply H2;eauto.
  rewrite TcbMod.set_a_get_a' in H3;[ | apply tidspec.neq_beq_false;auto].
  eauto.
  subst t0.
  eapply H2;eauto.
  rewrite TcbMod.set_a_get_a in H3;[ | apply tidspec.eq_beq_true;auto].
  inverts H3.
  eauto.

  (*-----------------------*)
  unfold task_stat_prop in *.
  intros.
  assert (t0 <> t \/ t0 = t) by tauto.
  destruct H11.
  eapply H4;eauto.
  rewrite TcbMod.set_a_get_a' in H3;[ | apply tidspec.neq_beq_false;auto].
  eauto.

  subst t0.
  rewrite TcbMod.set_a_get_a in H3;[ | apply tidspec.eq_beq_true;auto].
  inverts H3.
  right.
  apply H4 in H0.
  destruct H0;tryfalse.
  mytac.
  inverts H0.
  do 2 eexists;eauto.

  (*----------------------*)
  unfold op_p_prop in *.
  intros.
  assert (t = t0 \/ t <> t0) by tauto.
  destruct H12.
  subst t0.
  rewrite TcbMod.set_a_get_a in H3;[ | apply tidspec.eq_beq_true;auto].
  inverts H3.
  eapply H7;eauto.
  eapply GET_OP_st_irrel;eauto.
  rewrite TcbMod.set_a_get_a' in H3;[ | apply tidspec.neq_beq_false;auto].
  eapply H7;eauto.
  eapply GET_OP_st_irrel with (t:=t0);eauto.
  
  (*--------------------*)
  unfold wait_prop in *.
  intros.
  assert (t = t0 \/ t <> t0) by tauto.
  destruct H11.
  subst t0.
  rewrite TcbMod.set_a_get_a in H3;[ | apply tidspec.eq_beq_true;auto].
  inverts H3.
  lets Hx:H8 H0.
  mytac.
  assert (x<>t).
  intro.
  subst x.
  rewrite H0 in H11.
  inverts H11.
  do 3 eexists;splits;eauto.
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  eauto.
  intros.
  eapply H13;eauto.
  eapply GET_OP_st_irrel with (t:=t);eauto.

  rewrite TcbMod.set_a_get_a' in H3;[ | apply tidspec.neq_beq_false;auto].
  apply H8 in H3.
  mytac.
  assert (x0<>t0).
  intro.
  subst x0.
  rewrite H0 in H12.
  inverts H12.
  do 3 eexists;splits;eauto.
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  eauto.
  intros.
  apply H14.
  eapply GET_OP_st_irrel with (t:=t0);eauto.

  (*--------------------*)
  unfold no_owner_prio_prop in *.
  intros.
  assert (t0 = t \/ t0 <> t) by tauto.
  destruct H13.
  subst t0.
  rewrite TcbMod.set_a_get_a in H3;[ | apply tidspec.eq_beq_true;auto].
  inverts H3.
  eapply H9;eauto.
  eapply GET_OP_st_irrel with (t:=t);eauto.

  rewrite TcbMod.set_a_get_a' in H3;[ | apply tidspec.neq_beq_false;auto].
  eapply H9;eauto.
  eapply GET_OP_st_irrel with (t:=t0);eauto.

  (*=======================*)
  destructs H1.
  unfolds in H5.
  lets Hx:H5 H0.
  destruct H4;subst.
  destruct Hx;tryfalse.
  do 2 destruct H3;tryfalse.
  
  destruct H4;subst.
  destruct Hx;tryfalse.
  do 2 destruct H3;tryfalse.

  destruct H3;subst.
  destruct Hx;tryfalse.
  do 2 destruct H3;tryfalse.

  clear Hx.

  mytac.

  (*---------------*)
  unfold rdy_notin_wl in *.
  mytac.
  intros.
  assert (t = t0 \/ t <> t0) by tauto.
  destruct H11.
  subst t0.
  rewrite TcbMod.set_a_get_a in H10;[ | apply tidspec.eq_beq_true;auto].
  inverts H10.

  eapply tickchange_not_waiting;eauto.
  unfolds;splits;eauto.
  rewrite TcbMod.set_a_get_a' in H10;[ | apply tidspec.neq_beq_false;auto].
  apply H1 in H10.
  intro.
  destruct H10.
  lets Hx:H3 H0.
  unfolds in Hx.
  mytac.
  unfolddef.
  unfold get in *.
  simpl in *.
  rewrite H7 in H10;inverts H10.
  eapply post_iswait;eauto.

  intros.
  assert (t0 = t \/ t0 <> t) by tauto.
  destruct H11.
  subst t0.
  rewrite TcbMod.set_a_get_a in H10;[ | apply tidspec.eq_beq_true;auto].
  inverts H10.
  rewrite TcbMod.set_a_get_a' in H10;[ | apply tidspec.neq_beq_false;auto].
  lets Hx:H3 H10.
  assert (eid0 = eid \/ eid0 <> eid) by tauto.
  destruct H12.
  subst eid0.
  lets Hy:Hx.
  unfolds in Hy.
  mytac.
  unfolddef.
  unfold get in *.
  simpl in *.
  rewrite H12 in H7;inverts H7.
  eapply post_iswait' in Hx;eauto.
  unfolds in Hx.
  unfolds.
  mytac.
  do 3 eexists;split;eauto.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  eauto.

  intros.
  assert (t = t0 \/ t <> t0) by tauto.
  destruct H11.
  subst t0.
  apply H3 in H0.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H11.
  subst eid0.
  unfolds in H10.
  mytac.
  rewrite EcbMod.set_a_get_a in H10;[ | apply tidspec.eq_beq_true;auto].
  inverts H10.

  false;eapply remove_tid_in_false;eauto.
  assert (IS_WAITING_E t eid0 els).
  unfolds in H10.
  unfolds.
  mytac.
  rewrite EcbMod.set_a_get_a' in H10;[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;split;eauto.
  apply H4 in H12.
  apply H4 in H0.
  mytac.
  rewrite H0 in H12;inverts H12;tryfalse.
  apply H3 in H0.
  unfolds in H0.
  mytac.
  unfolddef.
  unfold get in *.
  simpl in *.
  rewrite H7 in H0;inverts H0.
  assert (IS_WAITING_E t eid0 els).
  eapply post_iswait';eauto.
  apply H4 in H0.
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  mytac;do 3 eexists;eauto.

  (*----------------*)
  unfold owner_prio_prop in *.
  intros.
  assert (t0 =t \/ t0 <> t) by tauto.
  destruct H10.
  subst t0.
  rewrite TcbMod.set_a_get_a in H3;[ | apply tidspec.eq_beq_true;auto].
  inverts H3.
  unfolds in H1;destructs H1.
  lets Hx:H3 H0.
  unfolds in Hx.
  destruct Hx.
  do 2 destruct H11.
  destruct H11.
  unfolddef.
  unfold get in *.
  simpl in *.
  rewrite H7 in H11;inverts H11.
  assert (eid0=eid \/ eid0 <> eid) by tauto.
  destruct H11.
  subst eid0.
  rewrite EcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  unfolds in H.
  assert (TcbMod.get tls t <> None ).
  intro.
  rewrite H4 in H0;inverts H0.
  apply H with (qid:=eid) in H4.
  destruct H4.
  destruct H4.
  unfolds.
  do 4 eexists;split;eauto.
  unfolds.
  do 3 eexists;eauto.
  rewrite EcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  eapply H2;eauto.

  rewrite TcbMod.set_a_get_a' in H3;[ | apply tidspec.neq_beq_false;auto].
  unfolds in H1.
  destructs H1.
  lets Hx:H11 H0.
  unfolds in Hx.
  destruct Hx.
  do 3 destruct H13.
  unfolddef.
  unfold get in *.
  simpl in *.
  rewrite H7 in H13;inverts H13.
  assert (eid0 = eid \/ eid0<>eid) by tauto.
  destruct H13.
  subst eid0.
  rewrite EcbMod.set_a_get_a in H4;[ | apply tidspec.eq_beq_true;auto].
  inverts H4.
  eapply H2;eauto.
  rewrite EcbMod.set_a_get_a' in H4;[ | apply tidspec.neq_beq_false;auto].
  eapply H2;eauto.


  (*------------------------*)
  unfold task_stat_prop in *.
  intros.
  assert (t=t0\/t<>t0) by tauto.
  destruct H4.
  subst t0.
  rewrite TcbMod.set_a_get_a in H3;[ | apply tidspec.eq_beq_true;auto].
  inverts H3;auto.
  rewrite TcbMod.set_a_get_a' in H3;[ | apply tidspec.neq_beq_false;auto].
  apply H5 in H3;auto.

  (*-----------------------*)
  unfold op_p_prop in *.
  intros.
  assert (t =t0 \/ t <> t0) by tauto.
  destruct H10.
  subst t0.
  rewrite TcbMod.set_a_get_a in H3;[ | apply tidspec.eq_beq_true;auto].
  inverts H3.
  eapply H6;eauto.
  eapply GET_OP_remove_tid_irrel;eauto.
  eapply GET_OP_st_irrel;eauto.

  rewrite TcbMod.set_a_get_a' in H3;[ | apply tidspec.neq_beq_false;auto].  
  eapply H6;eauto.
  eapply GET_OP_remove_tid_irrel with (t:=t0);eauto.
  eapply GET_OP_st_irrel with (t:=t0);eauto.

  (*------------------------*)
  unfold wait_prop in *.
  intros.
  assert (t = t0 \/ t <> t0) by tauto.
  destruct H4.
  subst t0.
  rewrite TcbMod.set_a_get_a in H3;[ | apply tidspec.eq_beq_true;auto].
  inverts H3.
  
  rewrite TcbMod.set_a_get_a' in H3;[ | apply tidspec.neq_beq_false;auto].
  lets Hx:H8 H3.
  mytac.
  assert (x<>t0).
  intro.
  subst.
  rewrite H11 in H0;inverts H0.
  exists x.
  rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 2 eexists;splits;eauto.
  assert (eid0=eid \/ eid0<>eid) by tauto.
  destruct H15.
  subst eid0.
  unfolds;unfolds in H10.
  mytac.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  unfolddef.
  unfold get in *.
  simpl in *.
  rewrite H10 in H7;inverts H7.
  do 3 eexists;eauto.
  unfolds in H10;unfolds;mytac.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;eauto.
  intros.
  apply H13.
  eapply GET_OP_remove_tid_irrel with (t:=t0);eauto.
  eapply GET_OP_st_irrel with (t:=t0);eauto.

  (*------------------------*)
  unfold no_owner_prio_prop in *.
  intros.
  assert (t = t0 \/ t <> t0) by tauto.
  destruct H11.
  subst t0.
  rewrite TcbMod.set_a_get_a in H3;[ | apply tidspec.eq_beq_true;auto].
  inverts H3.
  eapply H9;eauto.
  intro.
  destruct H4.
  mytac.
  exists x.
  eapply IS_OWNER_remove_tid_irrel';eauto.
  eapply GET_OP_remove_tid_irrel;eauto.
  eapply GET_OP_st_irrel;eauto.

  rewrite TcbMod.set_a_get_a' in H3;[ | apply tidspec.neq_beq_false;auto].
  eapply H9;eauto.
  intro.
  destruct H4.
  mytac.
  exists x.
  eapply IS_OWNER_remove_tid_irrel';eauto.
  eapply GET_OP_remove_tid_irrel with (t:=t0);eauto.
  eapply GET_OP_st_irrel with (t:=t0);eauto.
  Grab Existential Variables.
Qed.


Lemma tickstep_goodst:
  forall tls els tls' els' tls_sub,
    TcbMod.sub tls_sub tls ->
    tickstep' tls els tls' els' tls_sub ->
    NO_NEST_PENDING tls els ->
    NO_NEST_PENDING tls' els' ->
    (rdy_notin_wl tls els /\
     owner_prio_prop tls els /\
     task_stat_prop tls /\
     op_p_prop tls els /\
     wait_prop tls els /\ no_owner_prio_prop tls els) ->
    rdy_notin_wl tls' els' /\
    owner_prio_prop tls' els' /\
    task_stat_prop tls' /\
    op_p_prop tls' els' /\
    wait_prop tls' els' /\
    no_owner_prio_prop tls' els'.
Proof.
  intros.
  induction H0.
  auto.
  eapply IHtickstep';eauto.
  eapply tcbjoinsig_set_sub_sub;eauto.
  eapply tickchange_nonestpend;eauto.
  eapply sub_joinsig_get;eauto.
  eapply tickchange_goodst with (tls':=tls') (els':=els') in H3;eauto.
  eapply sub_joinsig_get;eauto.
Qed.

Lemma code_exe_prop2:
  forall client_code T' cst' O' T'' O'' cst'',
    O' = O'' \/ GOOD_API_CODE O' T' ->
    NO_NEST_PENDING_O O' ->
    GOOD_ST O' ->
    hpstep (client_code, os_spec') T' cst' O' T'' cst'' O''->
    NO_NEST_PENDING_O O'' ->
    GOOD_ST O''.
Proof.
  intros.
  rename H3 into Hnnp'.
  destruct H;subst;auto.
  inverts H2.
  inverts H4;auto;tryfalse.
  inverts H6;subst;auto;tryfalse.

  inverts H2.
  inverts H4;auto.

  unfolds in H.
  mytac.
  unfolddef.
  unfold get in *.
  simpl in *.
  rewrite H in H3;inverts H3.
  rewrite H5 in H4;inverts H4.
  destruct H10.
  mytac.

  (*mutex acc*)
  clear -H0 H1 H2 H8 H9 Hnnp'.
  rename H2 into H5.
  rename H9 into H12.
  inverts H5.
  mytac.
  assert (get O' curtid = Some (oscurt x8)) as Hct.
  eapply join_get_get_l;eauto.
  assert (get O' absecblsid = Some (absecblist x0)) as Hels.
  eapply join_get_get_l;eauto.
  assert (get O' abstcblsid = Some (abstcblist x2)) as Htls.
  eapply join_get_get_l;eauto.

  assert (O''= set O'  absecblsid
                   (absecblist (set x0 x (absmutexsem x3 (Some (x8, x5)), x4)))).
  eapply join_get_set_eq;eauto.
  clear H2 H5 H4.
  remember O' as Ox.
  clear HeqOx.
  rename x8 into ct.
  rename x0 into els.
  rename x2 into tls.
  subst O''.
  
  unfolds.
  intros.
  unfolds in Hnnp'.
  lets Hnnp'':Hnnp' H H2.
  clear Hnnp'.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H2;auto.
  unfold get in *;simpl in *.
  rewrite H2 in Htls;inverts Htls.
  unfolds in H1.
  lets Hgoodst: H1 Hels H2.
  assert (rdy_notin_wl tls (EcbMod.set els x (absmutexsem x3 (Some (ct, x5)), x4))) as Hrdynotintwl.
  mytac.
  unfolds.
  unfolds in H.
  mytac.
  intros.
  apply H in H15.
  intro.
  destruct H15.
  unfold IS_WAITING in *.
  mytac.
  assert (x = x0 \/ x <> x0) by tauto.
  destruct H17.
  subst x0.
  rewrite EcbMod.set_a_get_a in H15.
  2: apply tidspec.eq_beq_true;auto.
  inverts H15.
  do 4 eexists;splits;eauto.
  rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
  do 4 eexists;splits;eauto.
  
  (*---------------*)
  intros.
  apply H13 in H15.
  unfold IS_WAITING_E in *.
  mytac.
  assert (x = eid \/ x <> eid) by tauto.
  destruct H17.
  subst x.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  rewrite H15 in H9;inverts H9.
  do 3 eexists;splits;eauto.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;splits;eauto.
  (*----------------*)
  intros.
  assert (IS_WAITING_E t eid els).
  unfold IS_WAITING_E in *.
  mytac.
  assert (x = eid \/ x <> eid) by tauto.
  destruct H17.
  subst x.
  rewrite EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
  inverts H15.
  do 3 eexists;splits;eauto.
  rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;splits;eauto.
  eapply H14 in H16;eauto.

  mytac.

    (* rdy_notin_wl *)
    auto.
    

    (*owner_prio_prop*)
    unfold owner_prio_prop in *.
    intros.
    assert (x = eid \/ x <> eid) by tauto.
    destruct H15.
    subst x.
    rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
    inverts H14.
    rewrite H13 in H6;inverts H6.
    split;auto.
    rewrite EcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    eapply H3;eauto.

    (*task_stat_prop*)
    auto.

    (*op_p_prop*)
    unfold op_p_prop in *.
    intros.
    eapply H5;eauto.
    assert (t = ct \/ t <> ct) by tauto.
    destruct H15.
    Focus 2.
    eapply set_neq_getop_eq;eauto.
    intro.
    rewrite H13 in H16;tryfalse.
    subst t.

    rewrite H6 in H13;inverts H13.
    lets Hnoowner: no_nest_pending_set_none H6 H9 Hnnp''.
    lets Heq: no_nest_pending_set_prio_eq Hnnp'' H14 H6.
    subst p.
    unfolds.
    intro.
    right.
    split;auto.
    do 2 eexists;eauto.

    unfold wait_prop in *.
    intros.
    assert (TcbMod.get tls t = Some (p, wait (os_stat_mutexsem eid) tm, m)) as Ht;auto.
    apply H10 in H13.
    mytac.
    do 3 eexists;splits;eauto.
    unfold IS_OWNER in *.
    assert (x = eid \/ x <> eid) by tauto.
    destruct H17.
    subst.
    mytac.
    rewrite H13 in H9;inverts H9.
    mytac.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.
    assert (t = ct \/ t <> ct ) by tauto.
    destruct H17.
    subst t.
    intros.
    rewrite Ht in H6;inverts H6.
    unfolds in Hnnp''.
    eapply no_nest_pending_set_prio_eq;eauto.
    
    intros.
    eapply H16.
    eapply set_neq_getop_eq;eauto.
    intro.
    rewrite Ht in H19;tryfalse.

    
    unfold no_owner_prio_prop in *.
    intros.
    assert (t = ct \/ t <> ct ) by tauto.
    destruct H16.
    subst t.
    rewrite H6 in H13;inverts H13.
    eapply no_nest_pending_set_prio_eq;eauto.
    eapply H11;eauto.

    
    intro.
    destruct H14.
    mytac;eexists;eapply is_owner_set_other;eauto.
    eapply set_neq_getop_eq;eauto.
    intro.
    rewrite H13 in H17;tryfalse.

    (*mutex cre*)
    destruct H3;mytac.
    clear -H0 H1 H2 H8 H9 Hnnp'.
    rename H2 into H5.
    inverts H5.
    mytac.
    
    assert (get O' absecblsid = Some (absecblist x0)) as Hels.
    eapply join_get_get_l;eauto.
    assert (get O' abstcblsid = Some (abstcblist x4)) as Htls.
    eapply join_get_get_l;eauto.
    assert (O''= set O' absecblsid (absecblist x2)).
    eapply join_get_set_eq;eauto.
    subst O''.
    clear H3 H4.
    remember O' as Ox.
    clear HeqOx.
    rename x4 into tls.
    rename x0 into els.
    unfold GOOD_ST in *.
    intros.
    unfolds in Hnnp'.
    lets Hnnp'': Hnnp' H H2.
    clear Hnnp'.
    unfolds in H0.
    lets Hnnp: H0 Hels Htls.
    clear H0.
    rewrite OSAbstMod.map_get_set in H.
    inverts H.
    rewrite abst_set_get_neq in H2;auto.
    unfold get in *;simpl in *.
    rewrite Htls in H2;inversion H2;subst tls0.
    clear H2.
    lets Hgoodst: H1 Hels Htls.
    clear H1.

    mytac.
    (*ryd_notin_wl*)
    unfold rdy_notin_wl in *.
    mytac;intros.
    apply H in H12.
    intro.
    destruct H12.
    eapply iswaiting_cre_hold;eauto.
    (*----------*)
    apply H10 in H12.
    unfolds.
    unfolds in H12.
    mytac.
    do 3 eexists;split;eauto.
    eapply ecb_joinsig_get_eq;eauto.
    (*----------*)
    apply H11.
    unfold IS_WAITING_E in *.
    mytac.
    exists x0 x1 x2.
    split;auto.
    assert (eid = x3 \/ eid <> x3) by tauto.
    destruct H14.
    subst x3.
    unfolds in H7.
    eapply EcbMod.join_sig_get in H7;eauto.
    rewrite H12 in H7;inverts H7;simpl in H13;tryfalse.

    eapply joinsig_neq_get;eauto.

    (*owner_prio_prop*)
    unfold owner_prio_prop in *.
    intros.
    eapply H0;eauto.


    eapply ecb_joinsig_get_eq';eauto.
    (*task_stat_prop*)
    auto.

    (*op_p_prop*)
    unfold op_p_prop in *.
    intros.
    eapply H2 in H10;eauto.
    eapply getop_cre_hold;eauto.
    (*wait_prop*)
    unfold wait_prop in *.
    intros.
    apply H3 in H10.
    mytac.
    do 3 eexists;splits;eauto.
    unfold IS_OWNER in *.
    mytac.
    eapply ecb_joinsig_get_eq in H10;eauto.
    intros.
    apply H13.
    eapply getop_cre_hold;eauto.

    (*no_owner_prio_prop*)
    unfold no_owner_prio_prop in *.
    intros.
    eapply H4;eauto.
    intro.
    destruct H11.
    mytac.
    exists x0.
    unfold IS_OWNER in *.
    mytac.
    eapply ecb_joinsig_get_eq in H11;eauto.
    eapply getop_cre_hold;eauto.
    
    (*mutex del*)
    destruct H3;mytac.
    clear -H0 H1 H2 H8 H9 Hnnp'.
    rename H2 into H5.
    inverts H5.
    mytac.
     
    assert (get O' absecblsid = Some (absecblist x0)) as Hels.
    eapply join_get_get_l;eauto.
    assert (O''= set O' absecblsid (absecblist x2)).
    eapply join_get_set_eq;eauto.
    subst O''.
    clear H2.
    remember O' as Ox.
    clear HeqOx.
    rename x0 into els.
    unfold GOOD_ST in *.
    intros.
    unfolds in Hnnp'.
    lets Hnnp'': Hnnp' H H2.
    clear Hnnp'.
    unfolds in H0.
    assert (OSAbstMod.get Ox abtcblsid = Some (abstcblist tls)) as Htls.
    rewrite abst_set_get_neq in H2;auto.
    lets Hnnp: H0 Hels Htls.
    clear H0.
    rewrite OSAbstMod.map_get_set in H.
    inverts H.
    rewrite abst_set_get_neq in H2;auto.
    clear H2.
    lets Hgoodst: H1 Hels Htls.
    clear H1.

    unfold get in *;simpl in *.
    mytac.
    (*ryd_notin_wl*)
    unfold rdy_notin_wl in *.
    mytac;intros.
    apply H in H11.
    intro.
    destruct H11.
    eapply iswaiting_del_hold;eauto.
    (*----------*)
    apply H7 in H11.
    unfolds.
    unfolds in H11.
    mytac.
    do 3 eexists;split;eauto.
    assert (eid <> x).
    intro.
    subst x.
    
    rewrite H11 in H3;inverts H3.
    simpl in H12;tryfalse.
    eapply EcbMod.join_comm in H5.
    lets Hx: EcbMod.join_sig_get H5;eauto.
    eapply joinsig_neq_get;eauto.

    (*----------*)
    apply H10.
    unfold IS_WAITING_E in *.
    mytac.
    exists x0 x1 x2.
    split;auto.
    eapply ecb_joinsig_get_eq;eauto.
    unfolds.
    eapply EcbMod.join_comm in H5;eauto.

    (*owner_prio_prop*)
    unfold owner_prio_prop in *.
    intros.
    eapply H0;eauto.
    eapply ecb_joinsig_get_eq;eauto.
    unfolds.
    eapply EcbMod.join_comm in H5;eauto.
    (*task_stat_prop*)
    auto.

    (*op_p_prop*)
    unfold op_p_prop in *.
    intros.
    eapply H2 in H7;eauto.
    eapply getop_del_hold;eauto.
    (*wait_prop*)
    unfold wait_prop in *.
    intros.
    apply H4 in H7.
    mytac.
    do 3 eexists;splits;eauto.
    unfold IS_OWNER in *.
    mytac.
    eapply ecb_joinsig_get_eq' in H7;eauto.
    unfolds.
    eapply EcbMod.join_comm in H5;eauto.
    intros.
    apply H12.
    eapply getop_del_hold;eauto.

    (*no_owner_prio_prop*)
    unfold no_owner_prio_prop in *.
    intros.
    eapply H6;eauto.
    intro.
    destruct H10.
    mytac.
    exists x0.
    unfold IS_OWNER in *.
    mytac.
    eapply ecb_joinsig_get_eq' in H10;eauto.
    unfolds.
    eapply EcbMod.join_comm in H5;eauto.
    eapply getop_del_hold;eauto.
    (*mutex pend get succ*)  
    destruct H3;mytac.
    clear -H0 H1 H2 H8 H9 Hnnp'.
    rename H2 into H5.
    rename H8 into H12.
    inverts H5.
    mytac.

    assert (get O' curtid = Some (oscurt x8)) as Hct.
    eapply join_get_get_l;eauto.
    assert (get O' absecblsid = Some (absecblist x2)) as Hels.
    eapply join_get_get_l;eauto.
    assert (get O' abtcblsid = Some (abstcblist x4)) as Htls.
    eapply join_get_get_l;eauto.
    
    assert (O''= set O' absecblsid
            (absecblist (set x2 x (absmutexsem x7 (Some (x8, x5)), nil)))).
    eapply join_get_set_eq;eauto.
    subst O''.
    clear H2 H3 H4.
    remember O' as Ox.
    clear HeqOx.
    rename x8 into ct.
    rename x2 into els.
    rename x4 into tls.

    unfolds.
    intros.
    unfolds in Hnnp'.
    lets Hnnp'':Hnnp' H H2.
    clear Hnnp'.
    rewrite OSAbstMod.map_get_set in H.
    inverts H.
    rewrite abst_set_get_neq in H2;auto.
    unfold get in *;simpl in *.
    rewrite H2 in Htls;inverts Htls.
    unfolds in H1.
    lets Hgoodst: H1 Hels H2.
    assert (rdy_notin_wl tls (EcbMod.set els x (absmutexsem x7 (Some (ct, x5)), nil))) as Hrdynotintwl.
    mytac.
    unfolds.
    unfolds in H.
    mytac.
    intros.
    apply H in H15.
    intro.
    destruct H15.
    unfold IS_WAITING in *.
    mytac.
    assert (x = x1 \/ x <> x1) by tauto.
    destruct H17.
    subst x1.
    rewrite EcbMod.set_a_get_a in H15.
    2: apply tidspec.eq_beq_true;auto.
    inverts H15.
    do 4 eexists;splits;eauto.
    rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
    do 4 eexists;splits;eauto.
    
    (*---------------*)
    intros.
    apply H13 in H15.
    unfold IS_WAITING_E in *.
    mytac.
    assert (x = eid \/ x <> eid) by tauto.
    destruct H17.
    subst x.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    rewrite H15 in H5;inverts H5.
    do 3 eexists;splits;eauto.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;splits;eauto.
    (*----------------*)
    intros.
    assert (IS_WAITING_E t eid els).
    unfold IS_WAITING_E in *.
    mytac.
    assert (x = eid \/ x <> eid) by tauto.
    destruct H17.
    subst x.
    rewrite EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
    inverts H15.
    do 3 eexists;splits;eauto.
    rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;splits;eauto.
    eapply H14 in H16;eauto.
    Focus 1.
    -
      mytac.
      +
        (* rdy_notin_wl *)
        auto.
      +
        (*owner_prio_prop*)
        unfold owner_prio_prop in *.
        intros.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H15.
        subst x.
        rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
        inverts H14.
        rewrite H13 in H6;inverts H6.
        split;auto.
        rewrite EcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
        eapply H3;eauto.
      +
        (*task_stat_prop*)
        auto.
      +
        (*op_p_prop*)
        unfold op_p_prop in *.
        intros.
        eapply H8;eauto.
        assert (t = ct \/ t <> ct) by tauto.
        destruct H15.
        Focus 2.
        eapply set_neq_getop_eq;eauto.
        intro.
        rewrite H13 in H16;tryfalse.
        subst t.

        rewrite H6 in H13;inverts H13.
        lets Hnoowner: no_nest_pending_set_none H6 H5 Hnnp''.
        lets Heq: no_nest_pending_set_prio_eq Hnnp'' H14 H6.
        subst p.
        unfolds.
        intro.
        right.
        split;auto.
        do 2 eexists;eauto.
      +
        (*wait_prop*)
        unfold wait_prop in *.
        intros.
        assert (TcbMod.get tls t = Some (p, wait (os_stat_mutexsem eid) tm, m)) as Ht;auto.
        apply H10 in H13.
        mytac.
        do 3 eexists;splits;eauto.
        unfold IS_OWNER in *.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H17.
        subst.
        mytac.
        rewrite H13 in H5;inverts H5.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.
        assert (t = ct \/ t <> ct ) by tauto.
        destruct H17.
        subst t.
        intros.
        rewrite Ht in H6;inverts H6.
        intros.
        eapply H16.
        eapply set_neq_getop_eq;eauto.
        intro.
        rewrite Ht in H19;tryfalse.
      +
        (*no_owner_prio_prop*)      
        unfold no_owner_prio_prop in *.
        intros.
        assert (t = ct \/ t <> ct ) by tauto.
        destruct H16.
        subst t.
        rewrite H6 in H13;inverts H13.
        eapply no_nest_pending_set_prio_eq;eauto.
        eapply H11;eauto.
        intro.
        destruct H14.
        mytac;eexists;eapply is_owner_set_other;eauto.
        eapply set_neq_getop_eq;eauto.
        intro.
        rewrite H13 in H17;tryfalse.
        +
   destruct H3;mytac.
   destruct H3;mytac.
   destruct H3;mytac.

    clear -H0 H1 H2 H8 H9 Hnnp'.
    rename H2 into H6.
    rename H9 into H12.
    inverts H6.
    mytac.
    assert (get O' curtid = Some (oscurt x9)) as Hct.
    eapply join_get_get_l;eauto.
    assert (get O' absecblsid = Some (absecblist x0)) as Hels.
    eapply join_get_get_l;eauto.
    assert (get O' abtcblsid = Some (abstcblist x2)) as Htls.
    eapply join_get_get_l;eauto.
    
    assert (O''=(set (set O' abtcblsid (abstcblist (set x2 x9 (x6, x7, x8))))
                     absecblsid (absecblist (set x0 x (absmutexsem x5 None, nil))))).

    eapply join_get_set_eq_2;eauto.
    clear H2 H3 H4.
    subst O''.
    remember O' as Ox.
    clear HeqOx.
    rename x9 into ct.
    rename x0 into els.
    rename x2 into tls.
    unfold GOOD_ST in *.
    intros.
    unfolds in Hnnp'.
    lets Hnnp'': Hnnp' H H2.
    clear Hnnp'.
    unfolds in H0.
    lets Hnnp: H0 Hels Htls.
    clear H0.
    rewrite OSAbstMod.map_get_set in H.
    inverts H.
    rewrite abst_set_get_neq in H2;auto.
    rewrite OSAbstMod.map_get_set in H2.
    inverts H2.
    lets Hgoodst: H1 Hels Htls.
    clear H1.
    unfold get in *;simpl in *.
    mytac.
      
        unfold rdy_notin_wl in *;mytac.
        (*--------------*)
        intros.
        assert (t=ct\/t<>ct) by tauto.
        destruct H11.
        subst t.
        rewrite TcbMod.set_a_get_a in H10;[ | apply tidspec.eq_beq_true;auto].
        inverts H10.
        unfolds in Hnnp.
        assert ( TcbMod.get tls ct <> None ).
        intro.
        rewrite H10 in H6;tryfalse.
        apply Hnnp with (qid:=x) in H10.
        destruct H10.
        intro.
        destruct H10.
        unfolds in H13.
        unfolds.
        mytac.
        assert (x <> x0).
        intro.
        subst x0.
        rewrite EcbMod.set_a_get_a in H10;[ | apply tidspec.eq_beq_true;auto].
        inverts H10.
        simpl in H13;tryfalse.
        rewrite EcbMod.set_a_get_a' in H10;[ | apply tidspec.neq_beq_false;auto].
        do 4 eexists;split;eauto.
        unfolds.
        do 3 eexists;eauto.

        rewrite  TcbMod.set_a_get_a' in H10;[ | apply tidspec.neq_beq_false;auto].
        apply H in H10.
        intro.
        destruct H10.
        unfolds in H13.
        unfolds.
        mytac.
        assert (x <> x0).
        intro.
        subst x0.
        rewrite EcbMod.set_a_get_a in H10;[ | apply tidspec.eq_beq_true;auto].
        inverts H10.
        simpl in H13;tryfalse.
        rewrite EcbMod.set_a_get_a' in H10;[ | apply tidspec.neq_beq_false;auto].
        do 4 eexists;split;eauto.

        (*------------------*)
        intros.
        assert (t=ct\/t<>ct) by tauto.
        destruct H11.
        subst t.
        rewrite TcbMod.set_a_get_a in H10;[ | apply tidspec.eq_beq_true;auto].
        inverts H10.
        unfolds in Hnnp.
        assert ( TcbMod.get tls ct <> None ).
        intro.
        rewrite H10 in H6;tryfalse.
        apply Hnnp with (qid:=x) in H10.
        destruct H10.
        destruct H10.
        eapply H7 in H6.
        unfolds.
        unfolds in H6.
        mytac.
        do 4 eexists;split;eauto.
        unfolds.
        do 3 eexists;eauto.

        rewrite TcbMod.set_a_get_a' in H10;[ | apply tidspec.neq_beq_false;auto].
        apply H7 in H10.
        unfolds in H10.
        unfolds.
        mytac.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H14.
        subst x.

        rewrite H10 in H5;inverts H5.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;split;eauto.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;split;eauto.

        (*-----------------------*)
        intros.
        assert (t=ct\/t<>ct) by tauto.
        destruct H11.
        subst t.
        unfolds in Hnnp.
        assert ( TcbMod.get tls ct <> None ).
        intro.
        rewrite H11 in H6;tryfalse.
        apply Hnnp with (qid:=x) in H11.
        destruct H11.
        destruct H11.

        unfolds in H10.
        mytac.
        assert (eid <> x).
        intro.
        subst x.
        rewrite EcbMod.set_a_get_a in H10;[ | apply tidspec.eq_beq_true;auto].
        inverts H10;simpl in H11;tryfalse.
        rewrite EcbMod.set_a_get_a' in H10;[ | apply tidspec.neq_beq_false;auto].
        unfolds.
        do 4 eexists;split;eauto.
        unfolds.
        do 3 eexists;eauto.

        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        apply H9.
        unfolds in H10.
        mytac.
        assert (eid <> x).
        intro.
        subst x.
        rewrite EcbMod.set_a_get_a in H10;[ | apply tidspec.eq_beq_true;auto].
        inverts H10;simpl in H11;tryfalse.
        rewrite EcbMod.set_a_get_a' in H10;[ | apply tidspec.neq_beq_false;auto].
        unfolds.
        do 3 eexists;split;eauto.

        unfolds.
        intros.
        assert (t = ct \/ t <> ct ) by tauto.
        destruct H10.
        subst t.
        
        assert (eid <> x).
        intro.
        subst x.
        rewrite EcbMod.set_a_get_a in H9;[ | apply tidspec.eq_beq_true;auto].
        inverts H9.

        unfolds in Hnnp.
        rewrite EcbMod.set_a_get_a' in H9;[ | apply tidspec.neq_beq_false;auto].
        assert (TcbMod.get tls ct <> None).
        intro.
        rewrite H11 in H6;tryfalse.
        apply Hnnp with (qid:=eid) in H11.
        destruct H11.
        destruct H13.
        exists x.
        split;auto.
        unfolds;do 3 eexists;eauto.
        unfolds;do 3 eexists;eauto.

        (*--------------*)
        unfolds in H0.
        rewrite TcbMod.set_a_get_a' in H7;[ | apply tidspec.neq_beq_false;auto].
        eapply H0;eauto.
        assert (eid <> x).
        intro.
        subst x.
        rewrite EcbMod.set_a_get_a in H9;[ | apply tidspec.eq_beq_true;auto].
        inverts H9.
        rewrite EcbMod.set_a_get_a' in H9;[ | apply tidspec.neq_beq_false;auto].
        eauto.

        unfolds.
        intros.
        assert (t = ct \/ t <> ct ) by tauto.
        destruct H9.
        subst.
        rewrite TcbMod.set_a_get_a in H7;[ | apply tidspec.eq_beq_true;auto].
        inverts H7.
        unfolds in H1.
        apply H1 in H6.
        auto.

        unfolds in H1.
        rewrite TcbMod.set_a_get_a' in H7;[ | apply tidspec.neq_beq_false;auto].
        eapply H1;eauto.


        unfold op_p_prop in *.
        intros.
        assert (t= ct \/ t <> ct) by tauto.
        destruct H10.
        subst.
        rewrite TcbMod.set_a_get_a in H7;[ | apply tidspec.eq_beq_true;auto].
        inverts H7.
        unfolds in H9.

        assert ( TcbMod.get (TcbMod.set tls ct (p, st, m)) ct <> None ).
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        apply H9 in H7.
        destruct H7.
        mytac.
        assert (x0 <> x).
        intro.
        subst x0.
        unfolds in H7.
        mytac.
        rewrite EcbMod.set_a_get_a in H7;[ | apply tidspec.eq_beq_true;auto].
        inverts H7.
        unfolds in H7.
        rewrite EcbMod.set_a_get_a' in H7;[ | apply tidspec.neq_beq_false;auto].
        mytac.

        unfolds in Hnnp.
        assert (TcbMod.get tls ct <> None).
        intro.
        rewrite H11 in H6;tryfalse.
        apply Hnnp with (qid:=x) in H11.
        destruct H11.
        destruct H13.
        exists x0.
        split;auto.
        unfolds;do 3 eexists;eauto.
        unfolds;do 3 eexists;eauto.
        destruct H7.
        rewrite TcbMod.set_a_get_a in H10;[ | apply tidspec.eq_beq_true;auto]. 
        mytac.
        inverts H10.
        right.
        clear.
        int auto.

        (*-------------------*)
        rewrite TcbMod.set_a_get_a' in H7;[ | apply tidspec.neq_beq_false;auto].
        eapply H2;eauto.
        eapply post_nowt_return_getop_t;eauto.
        

        unfold wait_prop in *.
        intros.
        assert (t = ct \/ t <> ct ) by tauto.
        destruct H9.
        subst.
        rewrite TcbMod.set_a_get_a in H7;[ | apply tidspec.eq_beq_true;auto].
        inverts H7.
        unfolds in Hnnp.
        assert ( TcbMod.get tls ct <> None ).
        intro.
        rewrite H7 in H6;tryfalse.
        apply Hnnp with (qid:=x) in H7.
        mytac.
        destruct H7.
        unfolds in H.
        mytac.
        apply H7 in H6.
        unfolds.
        unfolds in H6.
        mytac.
        do 4 eexists;split;eauto.
        unfolds;do 3 eexists;eauto.

        (*---------------*)
        rewrite TcbMod.set_a_get_a' in H7;[ | apply tidspec.neq_beq_false;auto].
        lets Hx:H3 H7.
        mytac.
        
        assert (x0 = ct \/ x0 <> ct) by tauto.
        destruct H15.
        subst x0.
        unfolds in H.
        destructs H.
        lets Hy:H15 H7.
        unfolds in Hy.
        mytac.
        unfolds in H10.
        mytac.
        assert (eid = x \/ eid <> x) by tauto.
        destruct H19.
        subst x.
        rewrite H17 in H5.
        inverts H5.
        simpl in H18;tryfalse.

        rewrite H10 in H17;inverts H17.
        unfolds in Hnnp.
        assert (TcbMod.get tls ct <> None).
        intro.
        rewrite H17 in H6;tryfalse.
        apply Hnnp with (qid:=eid) in H17.
        destruct H17.
        destruct H20.
        exists x;split;auto.
        unfolds;do 3 eexists;eauto.
        unfolds;do 3 eexists;eauto.

        (*-----------------*)
        exists x0.
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 2 eexists;splits;eauto.
        unfolds in H10;unfolds.
        mytac.
        assert (x<> eid).
        intro.
        subst x.
        rewrite H10 in H5;inverts H5;tryfalse.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.
        intros.
        apply H14.
        eapply post_nowt_return_getop_t;eauto.

        unfold no_owner_prio_prop in *.
        intros.
        assert (t = ct \/ t <> ct ) by tauto.
        destruct H11.
        subst.
        rewrite TcbMod.set_a_get_a in H7;[ | apply tidspec.eq_beq_true;auto].
        inverts H7.
        unfolds in H10.
        assert (TcbMod.get (TcbMod.set tls ct (p, st, m)) ct <> None).
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        apply H10 in H7.

        destruct H7.
        mytac.
        assert (x0 <> x).
        intro.
        subst x0.
        unfolds in H7.
        mytac.
        rewrite EcbMod.set_a_get_a in H7;[ | apply tidspec.eq_beq_true;auto].
        inverts H7.
        unfolds in H7.
        rewrite EcbMod.set_a_get_a' in H7;[ | apply tidspec.neq_beq_false;auto].
        mytac.

        unfolds in Hnnp.
        assert (TcbMod.get tls ct <> None).
        intro.
        rewrite H13 in H6;tryfalse.
        apply Hnnp with (qid:=x) in H13.
        destruct H13.
        destruct H14.
        exists x0.
        split;auto.
        unfolds;do 3 eexists;eauto.
        unfolds;do 3 eexists;eauto.
        
        destruct H7.
        rewrite TcbMod.set_a_get_a in H11;[ | apply tidspec.eq_beq_true;auto]. 
        mytac.
        inverts H11.
        auto.

        (*---------------*)
        rewrite TcbMod.set_a_get_a' in H7;[ | apply tidspec.neq_beq_false;auto].
        eapply H4;eauto.
        intro.
        destruct H9.
        mytac.
        exists x0.
        assert (x0 <> x).
        intro.
        subst x0.
        unfolds in H9.
        mytac.
        rewrite H9 in H5;inverts H5.
        tryfalse.
        unfolds in H9.
        unfolds.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. 
        mytac.
        do 3 eexists;eauto.
        eapply post_nowt_return_getop_t;eauto.

   destruct H3;mytac.

   clear -H0 H1 H2 H8 H9 Hnnp'.
   rename H2 into H6.
   rename H9 into H12.
   inverts H6.
   mytac.

   assert (get O' curtid = Some (oscurt x9)) as Hct.
   eapply join_get_get_l;eauto.
   assert (get O' absecblsid = Some (absecblist x0)) as Hels.
   eapply join_get_get_l;eauto.
   assert (get O' abtcblsid = Some (abstcblist x2)) as Htls.
   eapply join_get_get_l;eauto.

   assert (O'' = (set O' absecblsid
                      (absecblist (set x0 x (absmutexsem x4 None, nil))))).
   eapply join_get_set_eq;eauto.
   subst O''.
   clear H2 H3 H4.
   remember O' as Ox.
   clear HeqOx.
   rename x9 into ct.
   rename x0 into els.
   rename x2 into tls.
   unfold GOOD_ST in *.
   intros.
   unfolds in Hnnp'.
   lets Hnnp'': Hnnp' H H2.
   clear Hnnp'.
   unfolds in H0.
   lets Hnnp: H0 Hels Htls.
   clear H0.
   rewrite OSAbstMod.map_get_set in H.
   inverts H.
   rewrite abst_set_get_neq in H2;auto.
   unfold get in *;simpl in *.
   rewrite Htls in H2;inversion H2;subst tls0.
   lets Hgoodst: H1 Hels Htls.
   clear H1.
   clear H2.
   mytac.
  
    (* rdy_notin_wl*)
    unfold rdy_notin_wl in *.
    mytac.
    intros.
    apply H in H11.
    intro.
    destruct H11.
    unfold IS_WAITING in *.
    mytac.
    assert (x <> x0).
    intro.
    subst x0.
    rewrite EcbMod.set_a_get_a in H11;[ | apply tidspec.eq_beq_true;auto]. 
    inverts H11.
    simpl in H13.
    tryfalse.
    
    rewrite EcbMod.set_a_get_a' in H11;[ | apply tidspec.neq_beq_false;auto]. 
    do 4 eexists;split;eauto.

    (*-----------------*)
    intros.
    apply H9 in H11.

    unfolds in H11.
    unfolds.
    mytac.
    assert (x <> eid).
    intro.
    subst x.
    rewrite H11 in H5.
    inverts H5.
    simpl in H13;tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. 
    do 3 eexists;split;eauto.

    (*-----------------*)
    intros.
    assert (x <> eid).
    intro.
    subst x.
    unfolds in H11.
    mytac.
    rewrite EcbMod.set_a_get_a in H11;[ | apply tidspec.eq_beq_true;auto]. 
    inverts H11.
    simpl in H13.
    tryfalse.

    apply H10.
    unfolds in H11.
    unfolds.
    mytac.
    rewrite EcbMod.set_a_get_a' in H11;[ | apply tidspec.neq_beq_false;auto]. 
    do 3 eexists;split;eauto.

    (* owner_prio_prop *)

    unfold owner_prio_prop in *.
    intros.
    assert (x <> eid).
    intro.
    subst x.
    rewrite EcbMod.set_a_get_a in H10;[ | apply tidspec.eq_beq_true;auto]. 
    inverts H10.
    rewrite EcbMod.set_a_get_a' in H10;[ | apply tidspec.neq_beq_false;auto].
    eapply H0;eauto.

    (* task_stat_prop *)
    unfold task_stat_prop in *.
    intros.
    eapply H1;eauto.

    (* op_p_prop *)
    unfold op_p_prop in *.
    intros.
    eapply H2;eauto.
    assert (t = ct \/ t <> ct) by tauto.
    destruct H11.
    subst t.
    unfolds.
    intros.
    left.
    exists x.
    unfolds.
    unfolds in H10.
    lets Hx: H10 H11.
    destruct Hx.
    mytac.
    unfolds in H13.
    mytac.
    assert (x=x0\/x<>x0) by tauto.
    destruct H14.
    subst x0.
    rewrite EcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.
    rewrite EcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    unfolds in Hnnp.
    apply Hnnp with (qid:=x) in H11.
    destruct H11.
    destruct H15.
    exists x0.
    split;auto.
    unfolds.
    do 3 eexists;eauto.
    unfolds;do 3 eexists;eauto.
    destruct H13.
    mytac.
    rewrite H14 in H9;inverts H9.
    unfolds in H0.
    lets Hx:H0 H14 H5.
    rewrite H6 in H14;inverts H14.
    mytac.
    destruct H9.
    subst.
    clear -H7;int auto.
    subst x5.
    do 2 eexists;eauto.
    (*------------------*)
    unfolds.
    intros.
    unfolds in H10.
    lets Hx:H10 H13.
    destruct Hx.
    left.
    mytac.
    assert (x0 <> x).
    intro.
    subst x0.
    unfolds in H14.
    rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
    mytac.
    inverts H14.
    unfolds in H14.
    rewrite EcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    mytac.
    exists x0.
    unfolds.
    do 2 eexists.
    eauto.
    right.
    mytac.
    intro.
    destruct H14.
    mytac.
    exists x2.
    unfolds in H14.
    unfolds.
    mytac.
    assert (x<>x2).
    intro.
    subst x2.
    rewrite H5 in H14;inverts H14;tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.
    do 2 eexists;eauto.

    (* wait_prop *)
    unfolds.
    intros.
    assert (t <> ct).
    intro.
    subst t.
    unfolds in H.
    mytac.
    lets Hx: H10 H9.
    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H13 in H6;inverts H6.
    apply Hnnp with (qid:=x) in H13.
    destruct H13.
    destruct H13.
    unfolds.
    unfolds in Hx.
    mytac.
    do 4 eexists;split;eauto.
    do 3 eexists;eauto.
    (*----------------*)
    unfolds in H3.
    lets Hx:H3 H9.
    mytac.
    exists x0.
    assert (x0<>ct).
    intro.
    subst x0.
    assert (eid = x \/ eid <> x) by tauto.
    destruct H16.
    subst x.
    unfolds in H.
    mytac.
    lets Hy:H16 H9.
    unfolds in Hy.
    mytac.
    rewrite H18 in H5.
    inverts H5.
    simpl in H19;tryfalse.
    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H17 in H6;inverts H6.
    eapply Hnnp in H17.
    destruct H17.
    destruct H18.
    exists x.
    split;eauto.
    unfolds.
    do 3 eexists;eauto.
    unfolds in H11.
    mytac.
    unfolds;do 3 eexists;eauto.

    assert (eid = x \/ eid <> x) by tauto.
    destruct H17.
    subst x.
    unfolds in H.
    mytac.
    lets Hy:H17 H9.
    unfolds in Hy.
    mytac.
    rewrite H19 in H5.
    inverts H5.
    simpl in H20;tryfalse.
    do 2 eexists.
    splits;eauto.
    unfolds.
    unfolds in H11.
    mytac.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.
    (*------------------*)
    intros.
    apply H15.
    unfolds.
    intro.
    unfolds in H18.
    lets Hx: H18 H19.
    destruct Hx.
    mytac.
    assert (x3 <> x).
    intro.
    subst x3.
    unfolds in H20.
    mytac.
    rewrite EcbMod.set_a_get_a in H20;[ | apply tidspec.eq_beq_true;auto].
    inverts H20.
    
    left.
    exists x3.
    unfolds.
    unfolds in H20.
    mytac.
    rewrite EcbMod.set_a_get_a' in H20;[ | apply tidspec.neq_beq_false;auto].
    do 2 eexists.
    eauto.
    right.
    mytac.
    intro.
    destruct H20.
    mytac.
    exists x10.
    assert (x10 <> x).
    intro.
    subst x10.
    unfolds in H20.
    mytac.
    rewrite H20 in H5;inverts H5;tryfalse.
    unfolds in H20.
    unfolds.
    mytac.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.
    do 2 eexists;eauto.

    (*no_owner_prio_prop*)
    unfold no_owner_prio_prop in *.
    intros.
    assert (t = ct \/ t <> ct) by tauto.
    destruct H13.
    subst t.
    unfolds in H11.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H9 in H13;tryfalse.
    lets Hx:H11 H13;clear H11.
    destruct Hx.
    mytac.
    assert (x0 = x \/ x0 <> x) by tauto.
    destruct H14.
    subst x0.
    unfolds in H11.
    mytac.
    rewrite EcbMod.set_a_get_a in H11;[ | apply tidspec.eq_beq_true;auto].
    inverts H11.
    unfolds in Hnnp.
    eapply Hnnp in H13.
    destruct H13.
    destruct H15.
    exists x;split;eauto.
    unfolds.
    do 3 eexists;eauto.
    unfolds in H11.
    unfolds.
    mytac.
    rewrite EcbMod.set_a_get_a' in H11;[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.

    destruct H11.
    mytac.
    rewrite H14 in H9;inverts H9;auto.

    (*---------------------*)
    eapply H4;eauto.
    intro.
    destruct H10.
    mytac.
    exists x0.
    unfolds in H10.
    mytac.
    unfolds.
    assert (x0 <> x).
    intro.
    subst x0.
    rewrite H10 in H5.
    inverts H5;tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.

    unfolds.
    intro.
    unfolds in H11.
    lets Hx: H11 H14.
    destruct Hx.
    mytac.
    assert (x0 <> x).
    intro.
    subst x0.
    unfolds in H15.
    mytac.
    rewrite EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
    inverts H15.
    
    left.
    exists x0.
    unfolds.
    unfolds in H15.
    mytac.
    rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
    do 2 eexists.
    eauto.
    right.
    mytac.
    intro.
    destruct H15.
    mytac.
    exists x2.
    assert (x2 <> x).
    intro.
    subst x2.
    unfolds in H15.
    mytac.
    rewrite H15 in H5;inverts H5;tryfalse.
    unfolds in H15.
    unfolds.
    mytac.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.
    do 2 eexists;eauto.
   
   destruct H3;mytac.
   destruct H3;mytac.
   destruct H3;mytac.
   +
    unfolds in H.
    mytac.
    unfold get in *;simpl in *.
    rewrite H in H3;inverts H3.
    rewrite H4 in H5.
    inverts H5.
    destruct H6;mytac.
    destruct H3;mytac.
    destruct H3;mytac.
    destruct H3;mytac.
    inverts H2;auto.
    Focus 2.
    destruct H3;mytac.
    destruct H2;mytac.
    destruct H2;mytac.
    destruct H2;mytac.
    destruct H2;mytac.
    destruct H2;mytac.
    destruct H2;mytac.

    (*mutex pend block no lift*)
    Focus 1.
    destruct H3;mytac.
    clear -H0 H1 H5 H8 H9 Hnnp'.
    rename H5 into H6.
    rename H9 into H12.
    inverts H6.
    mytac.
    
   assert (get O' curtid = Some (oscurt x14)) as Hct.
   eapply join_get_get_l;eauto.
   assert (get O' absecblsid = Some (absecblist x5)) as Hels.
   eapply join_get_get_l;eauto.
   assert (get O' abtcblsid = Some (abstcblist x3)) as Htls.
   eapply join_get_get_l;eauto.

   assert (O'' = (set
             (set O' abtcblsid
                (abstcblist
                   (set x3 x14 (x12, wait (os_stat_mutexsem x) x0, Vnull))))
             absecblsid
             (absecblist
                (set x5 x (absmutexsem x8 (Some (x9, x10)), x14 :: x7))))).
   eapply join_get_set_eq_2;eauto.
   subst O''.
   clear H2 H3 H4.
   remember O' as Ox.
    clear HeqOx.
    rename x14 into ct.
    rename x5 into els.
    rename x3 into tls.
    unfold GOOD_ST in *.
    intros.
    unfolds in Hnnp'.
    lets Hnnp'': Hnnp' H H2.
    clear Hnnp'.
    rewrite OSAbstMod.map_get_set in H.
    inverts H.
    rewrite abst_set_get_neq in H2;auto.
    rewrite OSAbstMod.map_get_set in H2.
    inverts H2.
    lets Hgoodst: H1 Hels Htls.
    clear H1.
    unfold get in *;simpl in *.
    -
      mytac.
      +
        unfold rdy_notin_wl in *.
        mytac;intros;auto.
        assert (t = ct \/ t <> ct) by tauto.
        destruct H16.
        subst t.
        rewrite TcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
        inverts H15.
        rewrite TcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        apply H in H15.
        intro.
        destruct H15.
        eapply pend_no_lift_iswating;eauto.
        (*----------------------*)
        assert (t = ct \/ t <> ct) by tauto.
        destruct H16.
        subst t.
        unfolds.
        rewrite TcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
        inverts H15.
        do 3 eexists;split;auto.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        simpl;auto.
        rewrite TcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        apply H13 in H15.
        unfolds in H15.
        unfolds.
        mytac.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H18.
        subst x.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        rewrite H15 in H5.
        inverts H5.
        do 3 eexists;split;auto.
        simpl.
        right;auto.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;split;eauto.
        
        assert (t = ct \/ t <> ct) by tauto.
        destruct H16.
        subst t.
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        unfolds in H15.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H16.
        subst x.
        rewrite EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
        mytac.
        do 3 eexists;eauto.
        apply H in H6.
        rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        destruct H6.
        unfolds.
        mytac.
        do 4 eexists;split;eauto.
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        apply H14.
        unfold IS_WAITING_E in *.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H17.
        subst x.
        rewrite EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
        mytac.
        inverts H15.
        do 3 eexists;split;eauto.
        simpl in H17.
        destruct H17;auto;tryfalse.
        rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        auto.

        unfold owner_prio_prop in *.
        intros.
        assert (t = ct \/ t <> ct) by tauto.
        destruct H15.
        subst t.
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        assert (x=eid \/ x<>eid) by tauto.
        destruct H13.
        subst x.
        rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
        inverts H14.
        rewrite H6 in H7;inverts H7.
        eapply H1;eauto.
        rewrite EcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
        eapply H1;eauto.

        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        assert (x=eid \/ x<>eid) by tauto.
        destruct H16.
        subst x.
        rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
        inverts H14.
        eapply H1;eauto.
        rewrite EcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
        eapply H1;eauto.

        unfold task_stat_prop in *.
        intros.
        assert (t = ct \/ t <> ct) by tauto.
        destruct H14.
        subst t.
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        right.
        do 2 eexists;auto.
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        eapply H2;eauto.

        unfold op_p_prop in *.
        intros.
        assert (t = ct \/ t <> ct) by tauto.
        destruct H15.
        Focus 2.
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        eapply H3;eauto.
        eapply pend_no_lift_getop with (ct:=ct);eauto.

        subst t.
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        eapply H3;eauto.        
        unfolds.

        unfolds in H14.
        rewrite TcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
        assert (Some (p, wait (os_stat_mutexsem x) x0, Vnull) <> None) by auto.
        apply H14 in H13.
        destruct H13.
        intros.
        unfolds in Hnnp''.
        assert (TcbMod.get
             (TcbMod.set tls ct (p, wait (os_stat_mutexsem x) x0, Vnull)) ct <>
                None).
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        destruct H13.
        eapply Hnnp'' with (qid:=x1) in H16;eauto.
        destruct H16.
        destruct H16.
        unfolds.
        exists x.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto]. 
        do 3 eexists;split;simpl;auto.
        simpl;left;auto.
        unfolds.
        unfolds in H13.
        mytac.
        do 3 eexists;eauto.
        destruct H13.
        mytac.
        inverts H15.
        intros.
        right.
        unfolds in Hnnp''.
        assert (TcbMod.get
             (TcbMod.set tls ct (op, wait (os_stat_mutexsem x) x0, Vnull)) ct <>
                None).
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        split.
        intro.
        destruct H13.
        mytac.
        exists x1.
        unfold IS_OWNER in *.
        mytac.
        assert (x= x1 \/ x <> x1) by tauto.
        destruct H17.
        subst x.
        rewrite H13 in H5;inverts H5.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto]. 
        do 3 eexists;simpl;auto.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. 
        do 3 eexists;simpl;eauto.
        do 2 eexists;eauto.

        (*wait_prop*)
        unfold wait_prop in *.
        intros.
        assert (t=ct \/ t<>ct) by tauto.
        destruct H14.
        subst t.
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        exists x9 x11 x13.
        splits.
        unfolds.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        assert (x9 <> ct).
        intro.
        subst x9.
        unfolds in Hnnp''.
        assert (TcbMod.get
             (TcbMod.set tls ct (p, wait (os_stat_mutexsem eid) tm, Vnull)) ct <>
                None).
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        eapply Hnnp'' with (qid:=eid) in H13.
        destruct H13.
        destruct H13.
        unfolds.
        exists eid.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;split;auto.
        simpl;left;auto.
        unfolds.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        assert (IS_OWNER x9 eid els).
        unfolds.
        do 3 eexists;eauto.
        unfolds in H0.
        lets Hxx:H0 Hels Htls.
        unfolds in Hxx.
        assert (TcbMod.get tls x9 <> None).
        intro.
        rewrite H15 in H7;tryfalse.
        lets Hx:Hxx H15 H14.
        unfolds in H2.
        lets Hy: H2 H7.
        destruct Hy;subst;auto.

        destruct H9.
        assert (Int.eq x11 x8 = true).
        clear -H9.
        int auto.
        lets Hx: Int.eq_spec x11 x8.
        rewrite H13 in Hx.
        subst;auto.
        lets Hx: H1 H7 H5.
        destruct Hx.
        destruct H13;subst;auto.

        intros.
        unfolds in H13.
        assert (TcbMod.get
          (TcbMod.set tls ct (p, wait (os_stat_mutexsem eid) tm, Vnull)) ct <>
                None ).
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        apply H13 in H14.
        clear H13.
        destruct H14.
        destruct H13.
        unfolds in Hnnp''.
        assert (TcbMod.get
          (TcbMod.set tls ct (p, wait (os_stat_mutexsem eid) tm, Vnull)) ct <>
                None ).
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.

        apply Hnnp'' with (qid:=x)in H14.
        destruct H14.
        destruct H14.
        unfolds.
        exists eid.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;split;auto.
        simpl;left;auto.
        unfolds in H13.
        unfolds.
        mytac.
        do 3 eexists;eauto.
        destruct H13.
        rewrite TcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
        mytac.
        inverts H14.
        auto.
        (*----------*)
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        apply H4 in H13.
        mytac.
        exists x1.
        do 2 eexists;splits;eauto.
        clear -H13 H5.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H.
        subst x.
        unfold IS_OWNER in *.
        mytac.
        rewrite H in H5;inverts H5.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.

        assert (x1 <> ct).
        intro;subst x1.
        unfolds in Hnnp''.
        assert ( TcbMod.get
             (TcbMod.set tls ct (x12, wait (os_stat_mutexsem x) x0, Vnull)) ct <>
                 None).
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        eapply Hnnp'' with (qid:=eid) in H18.
        destruct H18.
        destruct H18.
        unfolds.
        exists x.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;split;auto.
        simpl;left;auto.
        
        clear -H13 H5.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H.
        subst x.
        unfold IS_OWNER in *.
        mytac.
        rewrite H in H5;inverts H5.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        eauto.

        intros.
        apply H17.
        eapply pend_no_lift_getop with (ct:=ct);eauto.

        (*no_owner_prio_prop*)
        unfold no_owner_prio_prop in *.
        intros.
        assert (t = ct \/ t <> ct ) by tauto.
        destruct H16.
        (*------------*)
        subst t.
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        lets Hx:pend_no_lift_getop H6 H5 H15.
        eapply H11;eauto.
        intro.
        mytac.
        unfolds in Hnnp''.
        assert (TcbMod.get
             (TcbMod.set tls ct (p, wait (os_stat_mutexsem x) x0, Vnull)) ct <>
                None).
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        apply Hnnp'' with (qid:=x1) in H16.
        destruct H16.
        destruct H16.
        unfolds.
        exists x.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        split;auto.
        simpl;left;auto.

        clear -H13 H5.
        assert (x = x1 \/ x <> x1) by tauto.
        destruct H.
        subst x1.
        unfold IS_OWNER in *.
        mytac.
        rewrite H in H5;inverts H5.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.

        (*-----------------*)
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        eapply H11;eauto.
        intro.
        destruct H14.
        mytac.
        exists x1.

        clear -H14 H5.
        assert (x = x1 \/ x <> x1) by tauto.
        destruct H.
        subst x.
        unfold IS_OWNER in *.
        mytac.
        rewrite H in H5;inverts H5.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.
        eapply pend_no_lift_getop with (ct:=ct);eauto.

    (*mutex pend lift*)
    destruct H2;mytac.
    Focus 1.
    clear -H0 H1 H5 H8 H9 Hnnp'.
    rename H5 into H6.
    rename H9 into H12.
    rename H8 into Hff.
    inverts H6.
    mytac.
    
    assert (get O' curtid = Some (oscurt x15)) as Hct.
    eapply join_get_get_l;eauto.
    assert (get O' absecblsid = Some (absecblist x6)) as Hels.
    eapply join_get_get_l;eauto.
    assert (get O' abtcblsid = Some (abstcblist x3)) as Htls.
    eapply join_get_get_l;eauto.

    assert (O'' = (set
             (set O' abtcblsid
                (abstcblist
                   (set (set x3 x15 (x13, wait (os_stat_mutexsem x) x0, x2))
                      x10 (x9, rdy, x14)))) absecblsid
             (absecblist
                (set x6 x (absmutexsem x9 (Some (x10, x11)), x15 :: x8))))).
    eapply join_get_set_eq_2;eauto.
    subst O''.
    clear H2 H3 H4.
    remember O' as Ox.
    clear HeqOx.
    rename x15 into ct.
    rename x6 into els.
    rename x3 into tls.
    unfold GOOD_ST in *.
    intros.
    unfolds in Hnnp'.
    lets Hnnp'': Hnnp' H H2.
    clear Hnnp'.
    rewrite OSAbstMod.map_get_set in H.
    inverts H.
    rewrite abst_set_get_neq in H2;auto.
    rewrite OSAbstMod.map_get_set in H2.
    inverts H2.
    lets Hgoodst: H1 Hels Htls.
    clear H1.
    -
      assert (x10 <> ct) as Hneq.
      intro Hneq.
      subst x10.
      unfolds in Hnnp''.
      assert (TcbMod.get
             (TcbMod.set
                (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2))
                ct (x9, rdy, x14)) ct <> None).
      rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
      auto.
      apply Hnnp'' with (qid:=x) in H.
      destruct H.
      destruct H.
      unfolds.
      exists x.
      rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
      do 3 eexists;split;auto.
      simpl;left;auto.
      unfolds.
      rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
      do 3 eexists;split;auto.
      unfold get in *;simpl in *.
      mytac.
      +
        unfold rdy_notin_wl in *.
        mytac;intros;auto.
        (*------------*)
        assert (t = ct \/ t <> ct) by tauto.
        destruct H16.
        subst t.
        rewrite TcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
        inverts H15.

        assert (t = x10 \/ t <> x10) by tauto.
        destruct H17.
        subst t.

        rewrite TcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
        inverts H15.
        apply H in H7.
        intro.
        destruct H7.
        eapply pend_no_lift_iswating;eauto.

        rewrite TcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        apply H in H15.
        intro.
        destruct H15.
        eapply pend_no_lift_iswating with (ct:=ct);eauto.
        (*----------------------*)
        assert (t = ct \/ t <> ct) by tauto.
        destruct H16.
        subst t.
        unfolds.
        rewrite TcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
        inverts H15.
        do 3 eexists;split;auto.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        simpl;auto.

        assert (t = x10 \/ t <> x10) by tauto.
        destruct H17.
        subst.
        rewrite TcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
        inverts H15.

        rewrite TcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        apply H13 in H15.
        unfolds in H15.
        unfolds.
        mytac.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H19.
        subst x.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        rewrite H15 in H5.
        inverts H5.
        do 3 eexists;split;auto.
        simpl.
        right;auto.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;split;eauto.
        (*-------------------*)
        assert (t = ct \/ t <> ct) by tauto.
        destruct H16.
        subst t.
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        unfolds in H15.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H16.
        subst x.
        rewrite EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
        mytac.
        do 3 eexists;eauto.
        apply H in H6.
        rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        destruct H6.
        unfolds.
        mytac.
        do 4 eexists;split;eauto.

        assert (t=x10 \/ t<>x10) by tauto.
        destruct H17.
        subst.
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        assert (IS_WAITING_E x10 eid els).
        unfold IS_WAITING_E in *.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H17.
        subst x.
        rewrite EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
        mytac.
        inverts H15.
        do 3 eexists;split;eauto.
        simpl in H17.
        destruct H17;auto;tryfalse.
        rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        auto.
        apply H14 in H17.
        mytac.
        rewrite H17 in H7;inverts H7.

        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        apply H14.
        unfold IS_WAITING_E in *.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H18.
        subst x.
        rewrite EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
        mytac.
        inverts H15.
        do 3 eexists;split;eauto.
        simpl in H18.
        destruct H18;auto;tryfalse.
        rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
        auto.

        unfold owner_prio_prop in *.
        intros.
        assert (t = ct \/ t <> ct) by tauto.
        destruct H15.
        subst t.
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        assert (x=eid \/ x<>eid) by tauto.
        destruct H13.
        subst x.
        rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
        inverts H14.
        rewrite H6 in H7;inverts H7.
        eapply H1;eauto.
        rewrite EcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
        eapply H1;eauto.

        assert (t = x10 \/ t <> x10) by tauto.
        destruct H16.
        subst t.
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        assert (x=eid \/ x<>eid) by tauto.
        destruct H13.
        subst x.
        rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
        inverts H14.
        lets Hx: H1 H7 H5.
        destruct Hx.
        split;auto.
        rewrite EcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
        unfolds in H0.
        lets Hx:H0 Hels Htls.
        unfolds in Hx.
        assert (IS_OWNER x10 eid els).
        unfolds.
        do 3 eexists;eauto.
        lets Hy:Hx H16.
        intro.
        rewrite H17 in H7;tryfalse.
        destruct Hy.
        destruct H18.
        exists x;split;auto.
        unfolds;do 3 eexists;eauto.
        
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        assert (x=eid \/ x<>eid) by tauto.
        destruct H17.
        subst x.
        rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
        inverts H14.
        eapply H1;eauto.
        rewrite EcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
        eapply H1;eauto.

        unfold task_stat_prop in *.
        intros.
        assert (t = ct \/ t <> ct) by tauto.
        destruct H14.
        subst t.
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        right.
        do 2 eexists;auto.

        assert (t=x10\/t<>x10) by tauto.
        destruct H15.
        subst t.
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        eapply H2;eauto.
        
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        eapply H2;eauto.

        unfold op_p_prop in *.
        intros.
        assert (t = ct \/ t <> ct) by tauto.
        destruct H15.
        Focus 2.
        assert (t <> x10 \/ t = x10) by tauto.
        destruct H16.
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        eapply H3;eauto.
        eapply pend_lift_getop_t with (ct:=ct) (x10:=x10);eauto.

        subst t.
        unfolds in H14.
        assert (TcbMod.get
          (TcbMod.set
             (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2)) x10
             (x9, rdy, x14)) x10 <> None).
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        lets Hx: H14 H16.
        clear H14.
        destruct Hx.
        destruct H14.
        assert (x1 = x \/ x1 <> x) by tauto.
        destruct H17.
        subst x1.
        unfolds in H14.
        rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
        mytac.
        inverts H14.
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        left.
        clear -H9 H10;int auto.

        unfolds in Hnnp''.
        assert (IS_OWNER x10 x1
                         (EcbMod.set els x (absmutexsem x9 (Some (x10, x11)), ct :: x8))).
        unfolds.
        unfolds in H14.
        mytac.
        do 3 eexists;eauto.
        lets Hx:Hnnp'' H16 H18.
        destruct Hx.
        destruct H20.
        exists x.
        split;auto.
        unfolds.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.

        destruct H14.
        destruct H14.
        exists x.
        unfolds.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        (*---------------*)

        subst t.
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        eapply H3;eauto.        
        unfolds.

        unfolds in H14.
        rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
        assert (Some (p, wait (os_stat_mutexsem x) x0, m) <> None) by auto.
        apply H14 in H13.
        destruct H13.
        intros.
        unfolds in Hnnp''.
        assert (TcbMod.get
             (TcbMod.set
                (TcbMod.set tls ct (p, wait (os_stat_mutexsem x) x0, m)) x10
                (x9, rdy, x14)) ct <>
                None).
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        destruct H13.
        eapply Hnnp'' with (qid:=x1) in H16;eauto.
        destruct H16.
        destruct H16.
        unfolds.
        exists x.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto]. 
        do 3 eexists;split;simpl;auto.
        simpl;left;auto.
        unfolds.
        unfolds in H13.
        mytac.
        do 3 eexists;eauto.
        destruct H13.
        mytac.
        inverts H15.
        intros.
        right.
        unfolds in Hnnp''.
        assert ( TcbMod.get
             (TcbMod.set
                (TcbMod.set tls ct (op, wait (os_stat_mutexsem x) x0, x2))
                x10 (x9, rdy, x14)) ct <>
                None).
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        split.
        intro.
        destruct H13.
        mytac.
        exists x1.
        unfold IS_OWNER in *.
        mytac.
        assert (x= x1 \/ x <> x1) by tauto.
        destruct H17.
        subst x.
        rewrite H13 in H5;inverts H5.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto]. 
        do 3 eexists;simpl;auto.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. 
        do 3 eexists;simpl;eauto.
        do 2 eexists;eauto.

        (*wait_prop*)
        unfold wait_prop in *.
        intros.
        assert (t=ct \/ t<>ct) by tauto.
        destruct H14.
        subst t.
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        exists x10 x9 x14.
        splits.
        unfolds.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        auto.

        intros.
        unfolds in H13.
        assert (TcbMod.get
                  (TcbMod.set
                     (TcbMod.set tls ct (p, wait (os_stat_mutexsem eid) tm, m)) x10
                     (x9, rdy, x14)) ct <> None).
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        apply H13 in H14.
        clear H13.
        destruct H14.
        destruct H13.
        unfolds in Hnnp''.
        assert (TcbMod.get
                  (TcbMod.set
                     (TcbMod.set tls ct (p, wait (os_stat_mutexsem eid) tm, m)) x10
                     (x9, rdy, x14)) ct <> None).
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.

        apply Hnnp'' with (qid:=x)in H14.
        destruct H14.
        destruct H14.
        unfolds.
        exists eid.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;split;auto.
        simpl;left;auto.
        unfolds in H13.
        unfolds.
        mytac.
        do 3 eexists;eauto.
        destruct H13.
        rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
        mytac.
        inverts H14.
        auto.
        (*----------*)
        assert (t <> x10 \/ t = x10) by tauto.
        destruct H15.
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        assert (TcbMod.get tls t = Some (p, wait (os_stat_mutexsem eid) tm, m)) as Hgett.
        auto.
        apply H4 in H13.
        mytac.
        
        assert (x1<>x10 \/ x1 = x10) by tauto.
        destruct H19.
        rename H19 into Hf.
        exists x1.
        do 2 eexists;splits;eauto.
        clear -H13 H5.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H.
        subst x.
        unfold IS_OWNER in *.
        mytac.
        rewrite H in H5;inverts H5.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.

        assert (x1 <> ct).
        intro;subst x1.
        unfolds in Hnnp''.
        assert ( TcbMod.get
             (TcbMod.set
                (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2))
                x10 (x9, rdy, x14)) ct <>
                 None).
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        eapply Hnnp'' with (qid:=eid) in H19.
        destruct H19.
        destruct H19.
        unfolds.
        exists x.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;split;auto.
        simpl;left;auto.
        
        clear -H13 H5.
        assert (x = eid \/ x <> eid) by tauto.
        destruct H.
        subst x.
        unfold IS_OWNER in *.
        mytac.
        rewrite H in H5;inverts H5.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.
        
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        eauto.

        intros.
        apply H18.
        eapply pend_lift_getop_t with (ct:=ct);eauto.
        (*--------------*)
        subst x1.
        assert (x <> eid \/ x = eid) by tauto.
        destruct H19.
        unfolds in Hnnp''.
        assert ( TcbMod.get
             (TcbMod.set
                (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2))
                x10 (x9, rdy, x14)) x10 <> None ).

        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        apply Hnnp'' with (qid:=eid) in H20.
        destruct H20.
        destruct H21.
        exists x.
        split;auto.
        unfold IS_OWNER in *.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        mytac;do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.
        subst x.
        
        exists x10 x9 x14.
        splits.
        unfolds.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.

        assert (IS_OWNER x10 eid els).
        unfolds.
        do 3 eexists;eauto.
        auto.
        auto.
        unfolds in H0.
        lets Hxx:H0 Hels Htls.
        unfolds in Hxx.
        assert (TcbMod.get tls x10 <> None).
        intro.
        rewrite H16 in H7;tryfalse.
        lets Hx:Hxx H20 H13.
        unfolds in H2.
        lets Hy: H2 H7.
        destruct Hy;mytac;subst;auto;tryfalse.
        mytac.
        unfolds in H.
        mytac.

        rewrite H7 in H16;inverts H16.
        unfolds in H1.
        lets Hx:H1 H7 H5.
        destruct Hx.
        destruct H16;subst;auto.
        clear -H25 H17.
        int auto.

        intros.
        apply H18.
        eapply pend_lift_getop_t with (ct:=ct) (x10:=x10) in H19;eauto.

        (*--------------*)
        subst t.
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.
        
        (*no_owner_prio_prop*)
        unfold no_owner_prio_prop in *.
        intros.
        assert (t = ct \/ t <> ct ) by tauto.
        destruct H16.
        (*------------*)
        subst t.
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
        inverts H13.

        lets Hx:pend_lift_getop_ct H6 H5 H15;eauto.
        eapply H11;eauto.
        intro.
        mytac.
        unfolds in Hnnp''.
        assert (TcbMod.get
             (TcbMod.set
                (TcbMod.set tls ct (p, wait (os_stat_mutexsem x) x0, m)) x10
                (x9, rdy, x14)) ct <>
                None).
        rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        auto.
        apply Hnnp'' with (qid:=x1) in H16.
        destruct H16.
        destruct H16.
        unfolds.
        exists x.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        split;auto.
        simpl;left;auto.

        clear -H13 H5.
        assert (x = x1 \/ x <> x1) by tauto.
        destruct H.
        subst x1.
        unfold IS_OWNER in *.
        mytac.
        rewrite H in H5;inverts H5.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.

        (*-----------------*)
        assert (t <> x10 \/ t = x10) by tauto.
        destruct H17.
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
        eapply H11;eauto.
        intro.
        destruct H14.
        mytac.
        exists x1.

        clear -H14 H5.
        assert (x = x1 \/ x <> x1) by tauto.
        destruct H.
        subst x.
        unfold IS_OWNER in *.
        mytac.
        rewrite H in H5;inverts H5.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.
        unfold IS_OWNER in *.
        mytac.
        rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
        do 3 eexists;eauto.
        eapply pend_lift_getop_t with (ct:=ct);eauto.
        
        (*------------------*)
        subst t.
        destruct H14.
        exists x.
        unfolds.
        rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
        do 3 eexists;auto.

    destruct H2;mytac.
    destruct H2;mytac.
    destruct H2;mytac.

  (* post exwt return *)
    clear -H0 H1 H5 H8 H9 Hnnp'.
    rename H5 into H6.
    rename H9 into H12.
    rename H8 into Hfff.
    inverts H6.
    mytac.
    assert (get O' curtid = Some (oscurt x15)) as Hct.
    eapply join_get_get_l;eauto.
    assert (get O' absecblsid = Some (absecblist x0)) as Hels.
    eapply join_get_get_l;eauto.
    assert (get O' abtcblsid = Some (abstcblist x2)) as Htls.
    eapply join_get_get_l;eauto.

    assert (O'' =  (set
             (set O' abtcblsid
                (abstcblist
                   (set (set x2 x15 (x8, x9, x10)) x12 (x7, rdy, Vptr x))))
             absecblsid
             (absecblist
                (set x0 x
                   (absmutexsem x6 (Some (x12, x7)), remove_tid x12 x11))))).
    eapply join_get_set_eq_2;eauto.
    subst O''.
    clear H2 H3 H4.
    remember O' as Ox.
    clear HeqOx.
    rename x15 into ct.
    rename x0 into els.
    rename x2 into tls.
    unfold GOOD_ST in *.
    intros.
    unfolds in Hnnp'.
    lets Hnnp'': Hnnp' H H2.
    clear Hnnp'.
    unfolds in H0.
    lets Hnnp: H0 Hels Htls.
    clear H0.
    rewrite OSAbstMod.map_get_set in H.
    inverts H.
    rewrite abst_set_get_neq in H2;auto.
    rewrite OSAbstMod.map_get_set in H2.
    inverts H2.
    unfold get in *;simpl in *.
    lets Hgoodst: H1 Hels Htls.
    clear H1.
    destructs Hgoodst.
    assert (ct <> x12) as Hneq.
    intro.
    subst x12.
    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H10 in H8;tryfalse.
    apply Hnnp with (qid:=x) in H10.
    mytac.
    destruct H10.
    unfolds.
    do 4 eexists;split;eauto.
    unfolds in H7.
    mytac;auto.
    unfolds.
    do 3 eexists;eauto.

    assert (~ IS_WAITING ct els) as Hctnwait.
    intro.
    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H11 in H8;tryfalse.
    apply Hnnp with (qid:=x) in H11.
    mytac.
    destruct H11.
    auto.
    unfolds.
    do 3 eexists;eauto.

    
    (*rdy_notin_wl*)
    unfold rdy_notin_wl in *.
    mytac.
    intros.
    assert (t = ct \/ t <> ct) by tauto.
    destruct H14.
    subst t.
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.
    apply H in H8.
    intro.

    destruct H8.
    eapply post_iswait;eauto.
    assert (t = x12 \/ t <> x12) by tauto.
    destruct H15.
    subst x12.
    rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.

    eapply nnp_remove_nwait;eauto.
    unfolds;splits;eauto.
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    apply H in H13.
    intro.
    destruct H13.


    eapply remove_is_wait_neq;eauto.
    (*--------------------*)
    intros.
    assert (t = ct \/ t <> ct) by tauto.
    destruct H14.
    subst t.
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.
    lets Hx:H10 H8.
    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H13 in H8;tryfalse.
    apply Hnnp with(qid:=x)in H13.
    destruct H13.
    destruct H13.
    unfolds in Hx;mytac;unfolds;do 4 eexists;eauto.
    unfolds;do 3 eexists;eauto.

    assert (t <> x12).
    intro.
    subst x12.
    rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.
    
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    apply H10 in H13.
    eapply post_iswait' in H15;eauto.
    destruct H15;eauto.

    (*----------------*)
    intros.
    assert (t = ct \/ t <> ct) by tauto.
    destruct H14.
    subst t.
    assert (IS_WAITING_E ct eid els).
    eapply post_iswait';eauto.
    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H15 in H8;tryfalse.
    apply Hnnp with(qid:=x)in H15.
    destruct H15.
    destruct H15.
    unfolds in H14;mytac;unfolds;do 4 eexists;eauto.
    unfolds;do 3 eexists;eauto.

    assert (t = x12 \/ t <> x12) by tauto.
    destruct H15.
    subst t.
    lets Hx: nnp_remove_nwait Hnnp H7 H5 H9.
    unfolds;split;auto.
    destruct Hx.
    unfolds in H13;mytac.
    unfolds;do 4 eexists;split;eauto.
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    eapply H11;eauto.
    eapply post_iswait';eauto.

    (*owner_prio_prop*)
    unfold owner_prio_prop in *.
    intros.

    assert (t = ct \/ t <> ct ) by tauto.
    destruct H15.
    subst t.
    
    assert (eid <> x).
    intro.
    subst x.
    rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
    inverts H14;tryfalse.

    unfolds in Hnnp.
    rewrite EcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H16 in H8;tryfalse.
    apply Hnnp with (qid:=eid) in H16.
    destruct H16.
    destruct H17.
    exists x.
    split;auto.
    unfolds;do 3 eexists;eauto.
    unfolds;do 3 eexists;eauto.

    (*--------------*)
    assert (t <> x12 \/ t = x12) by tauto.
    destruct H16.
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    eapply H0;eauto.
    assert (eid <> x).
    intro.
    subst x.
    rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
    inverts H14;tryfalse.
    rewrite EcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    eauto.

    subst x12.
    rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.

    assert (eid = x \/ eid <> x ) by tauto.
    destruct H13.
    subst x.
    rewrite  EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
    inverts H14.
    split;auto.
    unfolds in H3.
    assert (IS_WAITING_E t eid els).
    unfolds.
    do 3 eexists;split;eauto.
    unfolds in H7;mytac;auto.
    apply H11 in H13.
    mytac.
    rewrite H13 in H9;inverts H9.
    apply H3 in H13.
    mytac.
    unfolds in H9.
    mytac.
    rewrite H9 in H5;inverts H5.
    rewrite H13 in H8;inverts H8.
    auto.

    rewrite EcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    eauto.

    (*task_stat_prop*)
    unfolds.
    intros.
    assert (t = ct \/ t <> ct ) by tauto.
    destruct H14.
    subst t.
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13;auto.
    apply H1 in H8;auto.

    assert (t = x12 \/ t <> x12 ) by tauto.
    destruct H15.
    subst t.
    rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13;auto.

    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    apply H1 in H13.
    auto.

    (*op_p_prop*)
    unfold op_p_prop in *.
    intros.
    assert (t= ct \/ t <> ct) by tauto.
    destruct H15.
    subst.
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.
    unfolds in H14.

    assert ( TcbMod.get
          (TcbMod.set (TcbMod.set tls ct (p, st, m)) x12 (x7, rdy, Vptr x))
          ct <> None ).
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    auto.
    apply H14 in H13.
    destruct H13.
    mytac.
    assert (x0 <> x).
    intro.
    subst x0.
    unfolds in H13.
    mytac.
    rewrite EcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13;tryfalse.
    unfolds in H13.
    rewrite EcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    mytac.

    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H16 in H8;tryfalse.
    apply Hnnp with (qid:=x) in H16.
    destruct H16.
    destruct H17.
    exists x0.
    split;auto.
    unfolds;do 3 eexists;eauto.
    unfolds;do 3 eexists;eauto.
    destruct H13.
    rewrite TcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto]. 
    mytac.
    inverts H15.
    right.
    clear.
    int auto.

    (*-------------------*)
    assert (t <> x12 \/ t = x12) by tauto.
    destruct H16.
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    eapply H2;eauto.

    unfolds.
    intro.
    unfolds in H14.
    assert (TcbMod.get
          (TcbMod.set (TcbMod.set tls ct (x8, x9, x10)) x12 (x7, rdy, Vptr x))
          t <> None).
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    auto.
    apply H14 in H18.
    destruct H18.
    mytac.
    left.
    exists x0.
    assert (x0 <> x).
    intro.
    subst x0.
    unfolds in H18.
    rewrite EcbMod.set_a_get_a in H18;[ | apply tidspec.eq_beq_true;auto].
    mytac.
    inverts H18;tryfalse.
    unfolds in H18.
    mytac.
    rewrite EcbMod.set_a_get_a' in H18;[ | apply tidspec.neq_beq_false;auto].
    unfolds.
    do 2 eexists;eauto.
    right.
    rewrite TcbMod.set_a_get_a' in H18;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a' in H18;[ | apply tidspec.neq_beq_false;auto].
    mytac.
    intro.
    destruct H18.
    mytac.
    exists x2.
    unfolds in H18.
    mytac.
    unfolds.
    assert (x <> x2).
    intro.
    subst x2.
    rewrite H18 in H5;inverts H5.
    tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.
    do 2 eexists;eauto.

    (*--------------------------*)
    subst t.
    rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.
    unfolds in H14.
    assert (TcbMod.get
          (TcbMod.set (TcbMod.set tls ct (x8, x9, x10)) x12 (p, rdy, Vptr x))
          x12 <> None ).
    rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    auto.
    apply H14 in H13.
    destruct H13.
    mytac.
    assert (x <> x0 \/ x = x0) by tauto.
    destruct H16.
    unfolds in Hnnp''.
    assert (TcbMod.get
             (TcbMod.set (TcbMod.set tls ct (x8, x9, x10)) x12
                (p, rdy, Vptr x)) x12 <> None).
    intro.
    rewrite TcbMod.set_a_get_a in H17;[ | apply tidspec.eq_beq_true;auto].
    tryfalse.
    apply Hnnp'' with (qid:=x) in H17.
    mytac.
    destruct H18.
    exists x0.
    split;auto.
    unfolds in H13.
    mytac.
    unfolds.
    do 3 eexists;eauto.
    unfolds.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    do 3 eexists;eauto.
    subst x0.
    unfolds in H13.
    mytac.
    rewrite EcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.
    right;clear;int auto.

    destruct H13.
    destruct H13.
    exists x.
    unfolds.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    do 3 eexists;eauto.

    (*wait_prop*)
    unfold wait_prop in *.
    intros.
    assert (t = ct \/ t <> ct ) by tauto.
    destruct H14.
    subst.
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.
    unfolds in Hnnp.
    assert ( TcbMod.get tls ct <> None ).
    intro.
    rewrite H13 in H8;tryfalse.
    apply Hnnp with (qid:=x) in H13.
    mytac.
    destruct H13.
    mytac.
    apply H10 in H8.
    unfolds.
    unfolds in H8.
    mytac.
    do 4 eexists;split;eauto.
    unfolds;do 3 eexists;eauto.

    (*---------------*)
   
    assert (t <> x12 \/ t = x12) by tauto.
    destruct H15.
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    lets Hx:H3 H13.
    mytac.
    
    assert (x0 = ct \/ x0 <> ct) by tauto.
    destruct H20.
    subst x0.
    lets Hy:H10 H13.
    unfolds in Hy.
    mytac.
    unfolds in H16.
    mytac.
    assert (eid = x \/ eid <> x) by tauto.
    destruct H22.
    subst x.
    rewrite H20 in H5.
    inverts H5.
    rewrite H20 in H16;inverts H16.
    rewrite H17 in H8.
    inverts H8.
    exists x12 x7 (Vptr eid).
    mytac.
    unfolds.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    do 3 eexists;eauto.
    rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    auto.
    unfolds in H7.
    lets Hx: H10 H13.
    unfolds in Hx.
    mytac.
    rewrite H5 in H20;inverts H20.
    eapply H22 with (t':=t) in H8;eauto.
    unfold get in *;simpl in *.
    rewrite H16 in H9;inverts H9.
    mytac.
    rewrite H8 in H13;inverts H13;auto.
    
    intros.

    unfolds in H5.
    apply H19.
    unfolds.
    intro.
    rewrite TcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
    apply H5 in H8.
    destruct H8.
    left.
    mytac.
    unfolds in H8.
    mytac.
    assert (eid <> x).
    intro.
    subst eid.
    rewrite EcbMod.set_a_get_a in H8;[ | apply tidspec.eq_beq_true;auto].
    inverts H8.
    tryfalse.
    rewrite EcbMod.set_a_get_a' in H8;[ | apply tidspec.neq_beq_false;auto].
    exists x;unfolds.
    do 2 eexists;eauto.

    right.
    mytac.
    intro.
    destruct H8.
    mytac.
    exists x1.
    unfolds.
    assert (x1 <> eid).
    intro.
    subst x1.
    unfolds in H8.
    mytac.
    rewrite H8 in H20;inverts H20.
    tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    unfolds in H8;mytac.
    do 3 eexists;eauto.
    do 2 eexists;eauto.

    rewrite H16 in H20;inverts H20.
    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H20 in H8;tryfalse.
    apply Hnnp with (qid:=eid) in H20.
    destruct H20.
    destruct H23.
    exists x;split;auto.
    unfolds;do 3 eexists;eauto.
    unfolds;do 3 eexists;eauto.

    (*-----------------*)

    exists x0.
    assert (x0 <> x12).
    intro.
    subst x0.
    unfolds in Hnnp.
    assert (TcbMod.get tls x12  <> None).
    intro.
    rewrite H21 in H17;tryfalse.
    apply Hnnp with (qid:=eid) in H21.
    destruct H21.
    destruct H21.
    unfolds.
    exists x.
    do 3 eexists;split;eauto.
    unfolds in H7;mytac;auto.
    auto.
    
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 2 eexists;splits;eauto.
    unfolds in H16;unfolds.
    mytac.
    assert (x <> eid).
    intro.
    subst x.
    rewrite H16 in H5;inverts H5;tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.

    intros.
    unfolds in H22.
    assert (x0 <> x12).
    intro.
    subst x0.
    unfolds in Hnnp.
    assert (TcbMod.get tls x12 <> None).
    intro.
    rewrite H17 in H23;tryfalse.
    apply Hnnp with (qid:=eid) in H23.
    destruct H23.
    destruct H23.
    unfolds.
    do 4 eexists;split;eauto.
    unfolds in H7;mytac;auto.
    auto.
    apply H19.
    unfolds.
    intro.
    rewrite TcbMod.set_a_get_a' in H22;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a' in H22;[ | apply tidspec.neq_beq_false;auto].
    apply H22 in H24.
    destruct H24.
    left.
    mytac.
    unfolds in H24.
    mytac.
    assert (x3 <> x).
    intro.
    subst x3.
    rewrite EcbMod.set_a_get_a in H24;[ | apply tidspec.eq_beq_true;auto].
    inverts H24.
    tryfalse.
    rewrite EcbMod.set_a_get_a' in H24;[ | apply tidspec.neq_beq_false;auto].
    exists x3;unfolds.
    do 2 eexists;eauto.

    right.
    mytac.
    intro.
    destruct H24.
    mytac.
    exists x5.
    unfolds.
    assert (x5 <> x).
    intro.
    subst x.
    unfolds in H24.
    mytac.
    rewrite H24 in H5;inverts H5.
    tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    unfolds in H24;mytac.
    do 3 eexists;eauto.
    do 2 eexists;eauto.
    
    (*------------------------*)
    subst t.
    rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.


    (*no_owner_prio_prop*)
    unfold no_owner_prio_prop in *.
    intros.
    assert (t = ct \/ t <> ct ) by tauto.
    destruct H16.
    subst.
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.
    unfolds in H15.
    assert ( TcbMod.get
          (TcbMod.set (TcbMod.set tls ct (p, st, m)) x12 (x7, rdy, Vptr x))
          ct <> None).
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    auto.
    apply H15 in H13.

    destruct H13.
    mytac.
    assert (x0 <> x).
    intro.
    subst x0.
    unfolds in H13.
    mytac.
    rewrite EcbMod.set_a_get_a in H13;[ | apply tidspec.eq_beq_true;auto].
    inverts H13.
    tryfalse.
    unfolds in H13.
    rewrite EcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    mytac.

    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H17 in H8;tryfalse.
    apply Hnnp with (qid:=x) in H17.
    destruct H17.
    destruct H18.
    exists x0.
    split;auto.
    unfolds;do 3 eexists;eauto.
    unfolds;do 3 eexists;eauto.
    
    destruct H13.
    rewrite TcbMod.set_a_get_a' in H16;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a in H16;[ | apply tidspec.eq_beq_true;auto]. 
    mytac.
    inverts H16.
    auto.

    (*---------------*)
    assert (t = x12 \/ t <> x12) by tauto.
    destruct H17.
    subst t.
    destruct H14.
    exists x.
    unfolds.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    do 3 eexists;eauto.

    
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a' in H13;[ | apply tidspec.neq_beq_false;auto].
    eapply H4;eauto.
    intro.
    destruct H14.
    mytac.
    exists x0.
    assert (x0 <> x).
    intro.
    subst x0.
    unfolds in H14.
    mytac.
    rewrite H14 in H5;inverts H5.
    tryfalse.
    unfolds in H14.
    unfolds.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. 
    mytac.
    do 3 eexists;eauto.

    unfolds.
    unfolds in H15.
    intros.

    rewrite TcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
    rewrite TcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
    apply H15 in H18.
    destruct H18.
    left.
    mytac.
    unfolds in H18.
    mytac.
    assert (x0 <> x).
    intro.
    subst x0.
    rewrite EcbMod.set_a_get_a in H18;[ | apply tidspec.eq_beq_true;auto].
    inverts H18.
    tryfalse.
    rewrite EcbMod.set_a_get_a' in H18;[ | apply tidspec.neq_beq_false;auto].
    exists x0;unfolds.
    do 2 eexists;eauto.

    right.
    mytac.
    intro.
    destruct H18.
    mytac.
    exists x2.
    unfolds.
    assert (x2 <> x).
    intro.
    subst x.
    unfolds in H18.
    mytac.
    rewrite H18 in H5;inverts H5.
    tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    unfolds in H18;mytac.
    do 3 eexists;eauto.
    do 2 eexists;eauto.

  destruct H2.
  mytac.
  (* post exwt no return *)
    clear -H0 H1 H5 H8 H9 Hnnp'.
    rename H5 into H6.
    rename H9 into H12.
    rename H8 into Hfff.
    inverts H6.
    mytac.
    assert (get O' curtid = Some (oscurt x5)) as Hct.
    eapply join_get_get_l;eauto.
    assert (get O' absecblsid = Some (absecblist x0)) as Hels.
    eapply join_get_get_l;eauto.
    assert (get O' abtcblsid = Some (abstcblist x2)) as Htls.
    eapply join_get_get_l;eauto.

    assert (O'' =  (set (set O' abtcblsid (abstcblist (set x2 x13 (x7, rdy, Vptr x))))
             absecblsid
             (absecblist
                (set x0 x
                   (absmutexsem x6 (Some (x13, x7)), remove_tid x13 x12))))).
    eapply join_get_set_eq_2;eauto.
    subst O''.
    clear H2 H3 H4.
    
    remember O' as Ox.
    clear HeqOx.
    rename x5 into ct.
    rename x0 into els.
    rename x2 into tls.
    unfold GOOD_ST in *.
    intros.
    unfolds in Hnnp'.
    unfold get in *;simpl in *.
    lets Hnnp'': Hnnp' H H2.
    clear Hnnp'.
    unfolds in H0.
    lets Hnnp: H0 Hels Htls.
    clear H0.
    rewrite OSAbstMod.map_get_set in H.
    inverts H.
    rewrite abst_set_get_neq in H2;auto.
    rewrite OSAbstMod.map_get_set in H2.
    inverts H2.
    lets Hgoodst: H1 Hels Htls.
    clear H1.
    destructs Hgoodst.
    assert (ct <> x13) as Hneq.
    intro.
    subst x13.
    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H11 in H9;tryfalse.
    apply Hnnp with (qid:=x) in H11.
    mytac.
    destruct H11.
    unfolds.
    do 4 eexists;split;eauto.
    unfolds in H7.
    mytac;auto.
    unfolds.
    do 3 eexists;eauto.
    
    (*rdy_notin_wl*)
    unfold rdy_notin_wl in *.
    mytac.
    intros.
    assert (t = ct \/ t <> ct) by tauto.
    destruct H15.
    subst t.
    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    apply H in H14.
    intro.
    destruct H14.
    eapply post_iswait;eauto.
    assert (t = x13 \/ t <> x13) by tauto.
    destruct H16.
    subst x13.
    rewrite TcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
    inverts H14.

    eapply nnp_remove_nwait;eauto.
    unfolds;splits;eauto.
    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    apply H in H14.
    intro.
    destruct H14.
    eapply remove_is_wait_neq;eauto.
    (*--------------------*)
    intros.
    assert (t = ct \/ t <> ct) by tauto.
    destruct H15.
    subst t.
    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    lets Hx:H11 H14.
    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H15 in H14;tryfalse.
    apply Hnnp with(qid:=x)in H15.
    destruct H15.
    destruct H15.
    unfolds in Hx;mytac;unfolds;do 4 eexists;eauto.
    unfolds;do 3 eexists;eauto.

    assert (t <> x13).
    intro.
    subst x13.
    rewrite TcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
    inverts H14.
    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    apply H11 in H14.
    eapply post_iswait' in H16;eauto.
    destruct H16;eauto.
    (*----------------*)
    intros.
    assert (t = ct \/ t <> ct) by tauto.
    destruct H15.
    subst t.
    assert (IS_WAITING_E ct eid els).
    eapply post_iswait';eauto.
    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H16 in H9;tryfalse.
    apply Hnnp with(qid:=x)in H16.
    destruct H16.
    destruct H16.
    unfolds in H15;mytac;unfolds;do 4 eexists;eauto.
    unfolds;do 3 eexists;eauto.

    assert (t = x13 \/ t <> x13) by tauto.
    destruct H16.
    subst t.
    lets Hx: nnp_remove_nwait Hnnp H7 H5 H10.
    unfolds;split;auto.
    destruct Hx.
    unfolds in H14;mytac.
    unfolds;do 4 eexists;split;eauto.
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    eapply H13;eauto.
    eapply post_iswait';eauto.

    (*owner_prio_prop*)
    unfold owner_prio_prop in *.
    intros.

    assert (t = ct \/ t <> ct ) by tauto.
    destruct H16.
    subst t.
    
    assert (eid <> x).
    intro.
    subst x.
    rewrite EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
    inverts H15;tryfalse.

    unfolds in Hnnp.
    rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H17 in H9;tryfalse.
    apply Hnnp with (qid:=eid) in H17.
    destruct H17.
    destruct H18.
    exists x.
    split;auto.
    unfolds;do 3 eexists;eauto.
    unfolds;do 3 eexists;eauto.

    (*--------------*)
    assert (t <> x13 \/ t = x13) by tauto.
    destruct H17.
    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    eapply H0;eauto.
    assert (eid <> x).
    intro.
    subst x.
    rewrite EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
    inverts H15;tryfalse.
    rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
    eauto.

    subst x13.
    rewrite TcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
    inverts H14.

    assert (eid = x \/ eid <> x ) by tauto.
    destruct H14.
    subst x.
    rewrite  EcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto].
    inverts H15.
    split;auto.
    unfolds in H3.
    assert (IS_WAITING_E t eid els).
    unfolds.
    do 3 eexists;split;eauto.
    unfolds in H7;mytac;auto.
    apply H13 in H14.
    mytac.
    rewrite H14 in H10;inverts H10.
    apply H3 in H14.
    mytac.
    unfolds in H10.
    mytac.
    rewrite H10 in H5;inverts H5.
    rewrite H14 in H9;inverts H9.
    auto.

    lets Hx:H0 H14 H10.
    destruct Hx.
    destruct H5;subst.
    auto.
    clear -H9 H15.
    int auto.
    
    rewrite EcbMod.set_a_get_a' in H15;[ | apply tidspec.neq_beq_false;auto].
    eauto.

    (*task_stat_prop*)
    unfolds.
    intros.
    assert (t = ct \/ t <> ct ) by tauto.
    destruct H15.
    subst t.
    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    apply H1 in H14;auto.

    assert (t = x13 \/ t <> x13 ) by tauto.
    destruct H16.
    subst t.
    rewrite TcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
    inverts H14;auto.

    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    apply H1 in H14.
    auto.

    (*op_p_prop*)
    unfold op_p_prop in *.
    intros.
    assert (t= ct \/ t <> ct) by tauto.
    destruct H16.
    subst.
    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    unfolds in H15.

    assert (TcbMod.get (TcbMod.set tls x13 (x7, rdy, Vptr x)) ct <> None ).
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    intro.
    rewrite H16 in H14;tryfalse.
    apply H15 in H16.
    destruct H16.
    mytac.
    assert (x0 <> x).
    intro.
    subst x0.
    unfolds in H16.
    mytac.
    rewrite EcbMod.set_a_get_a in H16;[ | apply tidspec.eq_beq_true;auto].
    inverts H16;tryfalse.
    unfolds in H16.
    rewrite EcbMod.set_a_get_a' in H16;[ | apply tidspec.neq_beq_false;auto].
    mytac.

    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H18 in H14;tryfalse.
    apply Hnnp with (qid:=x) in H18.
    destruct H18.
    destruct H19.
    exists x0.
    split;auto.
    unfolds;do 3 eexists;eauto.
    unfolds;do 3 eexists;eauto.
    destruct H16.
    rewrite TcbMod.set_a_get_a' in H17;[ | apply tidspec.neq_beq_false;auto].

    mytac.
    rewrite H14 in H17;inverts H17.
    right.
    clear.
    int auto.

    (*-------------------*)
    assert (t <> x13 \/ t = x13) by tauto.
    destruct H17.
    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    eapply H2;eauto.

    unfolds.
    intro.
    unfolds in H15.
    assert ( TcbMod.get (TcbMod.set tls x13 (x7, rdy, Vptr x)) t <> None ).
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    auto.
    apply H15 in H19.
    destruct H19.
    mytac.
    left.
    exists x0.
    assert (x0 <> x).
    intro.
    subst x0.
    unfolds in H19.
    rewrite EcbMod.set_a_get_a in H19;[ | apply tidspec.eq_beq_true;auto].
    mytac.
    inverts H19;tryfalse.
    unfolds in H19.
    mytac.
    rewrite EcbMod.set_a_get_a' in H19;[ | apply tidspec.neq_beq_false;auto].
    unfolds.
    do 2 eexists;eauto.
    right.
    rewrite TcbMod.set_a_get_a' in H19;[ | apply tidspec.neq_beq_false;auto].
    mytac.
    intro.
    destruct H19.
    mytac.
    exists x2.
    unfolds in H19.
    mytac.
    unfolds.
    assert (x <> x2).
    intro.
    subst x2.
    rewrite H19 in H5;inverts H5.
    tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.
    do 2 eexists;eauto.

    (*--------------------------*)
    subst t.
    rewrite TcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
    inverts H14.
    unfolds in H15.
    assert (TcbMod.get (TcbMod.set tls x13 (p, rdy, Vptr x)) x13 <> None ).
    rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    auto.
    apply H15 in H14.
    destruct H14.
    mytac.
    assert (x <> x0 \/ x = x0) by tauto.
    destruct H17.
    unfolds in Hnnp''.
    assert (TcbMod.get (TcbMod.set tls x13 (p, rdy, Vptr x)) x13 <> None).
    intro.
    rewrite TcbMod.set_a_get_a in H18;[ | apply tidspec.eq_beq_true;auto].
    tryfalse.
    apply Hnnp'' with (qid:=x) in H18.
    mytac.
    destruct H19.
    exists x0.
    split;auto.
    unfolds in H14.
    mytac.
    unfolds.
    do 3 eexists;eauto.
    unfolds.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    do 3 eexists;eauto.
    subst x0.
    unfolds in H14.
    mytac.
    rewrite EcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
    inverts H14.
    right;clear;int auto.

    destruct H14.
    destruct H14.
    exists x.
    unfolds.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    do 3 eexists;eauto.

    (*wait_prop*)
    unfold wait_prop in *.
    intros.
    assert (t = ct \/ t <> ct ) by tauto.
    destruct H15.
    subst.
    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    unfolds in Hnnp.
    assert ( TcbMod.get tls ct <> None ).
    intro.
    rewrite H15 in H9;tryfalse.
    apply Hnnp with (qid:=x) in H15.
    mytac.
    destruct H15.
    mytac.
    apply H11 in H14.
    unfolds.
    unfolds in H14.
    mytac.
    do 4 eexists;split;eauto.
    unfolds;do 3 eexists;eauto.

    (*---------------*)
    assert (t <> x13 \/ t = x13) by tauto.
    destruct H16.
    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    lets Hx:H3 H14.
    mytac.
    
    assert (x0 = ct \/ x0 <> ct) by tauto.
    destruct H21.
    subst x0.
    lets Hy:H11 H14.
    unfolds in Hy.
    mytac.
    unfolds in H17.
    mytac.
    assert (eid = x \/ eid <> x) by tauto.
    destruct H23.
    subst x.
    rewrite H21 in H5.
    inverts H5.
    rewrite H21 in H17;inverts H17.
    rewrite H18 in H9.
    inverts H9.
    exists x13 x7 (Vptr eid).
    mytac.
    unfolds.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    do 3 eexists;eauto.
    rewrite TcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    auto.
    unfolds in H7.
    lets Hx: H11 H14.
    unfolds in Hx.
    mytac.
    rewrite H5 in H21;inverts H21.
    eapply H23 with (t':=t) in H9;eauto.
    unfold get in *;simpl in *.
    rewrite H17 in H10;inverts H10.
    mytac.
    rewrite H9 in H14;inverts H14;auto.
    
    intros.
    unfolds in H5.
    apply H20.
    unfolds.
    intro.
    rewrite TcbMod.set_a_get_a' in H5;[ | apply tidspec.neq_beq_false;auto].
    apply H5 in H9.
    destruct H9.
    left.
    mytac.
    unfolds in H9.
    mytac.
    assert (eid <> x).
    intro.
    subst eid.
    rewrite EcbMod.set_a_get_a in H9;[ | apply tidspec.eq_beq_true;auto].
    inverts H9.
    tryfalse.
    rewrite EcbMod.set_a_get_a' in H9;[ | apply tidspec.neq_beq_false;auto].
    exists x;unfolds.
    do 2 eexists;eauto.

    right.
    mytac.
    intro.
    destruct H9.
    mytac.
    exists x1.
    unfolds.
    assert (x1 <> eid).
    intro.
    subst x1.
    unfolds in H9.
    mytac.
    rewrite H9 in H21;inverts H21.
    tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    unfolds in H9;mytac.
    do 3 eexists;eauto.
    do 2 eexists;eauto.

    rewrite H17 in H21;inverts H21.
    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H21 in H9;tryfalse.
    apply Hnnp with (qid:=eid) in H21.
    destruct H21.
    destruct H24.
    exists x;split;auto.
    unfolds;do 3 eexists;eauto.
    unfolds;do 3 eexists;eauto.

    (*-----------------*)

    exists x0.
    assert (x0 <> x13).
    intro.
    subst x0.
    unfolds in Hnnp.
    assert (TcbMod.get tls x13  <> None).
    intro.
    rewrite H22 in H18;tryfalse.
    apply Hnnp with (qid:=eid) in H22.
    destruct H22.
    destruct H22.
    unfolds.
    exists x.
    do 3 eexists;split;eauto.
    unfolds in H7;mytac;auto.
    auto.
    
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 2 eexists;splits;eauto.
    unfolds in H17;unfolds.
    mytac.
    assert (x <> eid).
    intro.
    subst x.
    rewrite H17 in H5;inverts H5;tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.

    intros.
    unfolds in H23.
    assert (x0 <> x13).
    intro.
    subst x0.
    unfolds in Hnnp.
    assert (TcbMod.get tls x13 <> None).
    intro.
    rewrite H18 in H24;tryfalse.
    apply Hnnp with (qid:=eid) in H24.
    destruct H24.
    destruct H24.
    unfolds.
    do 4 eexists;split;eauto.
    unfolds in H7;mytac;auto.
    auto.
    apply H20.
    unfolds.
    intro.
    rewrite TcbMod.set_a_get_a' in H23;[ | apply tidspec.neq_beq_false;auto].
    apply H23 in H25.
    destruct H25.
    left.
    mytac.
    unfolds in H25.
    mytac.
    assert (x3 <> x).
    intro.
    subst x3.
    rewrite EcbMod.set_a_get_a in H25;[ | apply tidspec.eq_beq_true;auto].
    inverts H25.
    tryfalse.
    rewrite EcbMod.set_a_get_a' in H25;[ | apply tidspec.neq_beq_false;auto].
    exists x3;unfolds.
    do 2 eexists;eauto.

    right.
    mytac.
    intro.
    destruct H25.
    mytac.
    exists x5.
    unfolds.
    assert (x5 <> x).
    intro.
    subst x.
    unfolds in H25.
    mytac.
    rewrite H25 in H5;inverts H5.
    tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    unfolds in H25;mytac.
    do 3 eexists;eauto.
    do 2 eexists;eauto.
    
    (*------------------------*)
    subst t.
    rewrite TcbMod.set_a_get_a in H14;[ | apply tidspec.eq_beq_true;auto].
    inverts H14.


    (*no_owner_prio_prop*)
    unfold no_owner_prio_prop in *.
    intros.
    assert (t = ct \/ t <> ct ) by tauto.
    destruct H17.
    subst.
    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    unfolds in H16.
    assert ( TcbMod.get (TcbMod.set tls x13 (x7, rdy, Vptr x)) ct <> None).
    rewrite TcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    intro.
    rewrite H17 in H14;tryfalse.

    apply H16 in H17.
    destruct H17.
    mytac.
    assert (x0 <> x).
    intro.
    subst x0.
    unfolds in H17.
    mytac.
    rewrite EcbMod.set_a_get_a in H17;[ | apply tidspec.eq_beq_true;auto].
    inverts H17.
    tryfalse.
    unfolds in H17.
    rewrite EcbMod.set_a_get_a' in H17;[ | apply tidspec.neq_beq_false;auto].
    mytac.

    unfolds in Hnnp.
    assert (TcbMod.get tls ct <> None).
    intro.
    rewrite H19 in H9;tryfalse.
    apply Hnnp with (qid:=x) in H19.
    destruct H19.
    destruct H20.
    exists x0.
    split;auto.
    unfolds;do 3 eexists;eauto.
    unfolds;do 3 eexists;eauto.
    
    destruct H17.
    rewrite TcbMod.set_a_get_a' in H18;[ | apply tidspec.neq_beq_false;auto].
    mytac.
    rewrite H18 in H14.
    inverts H14.
    auto.

    (*---------------*)
    assert (t = x13 \/ t <> x13) by tauto.
    destruct H18.
    subst t.
    destruct H15.
    exists x.
    unfolds.
    rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
    do 3 eexists;eauto.

    
    rewrite TcbMod.set_a_get_a' in H14;[ | apply tidspec.neq_beq_false;auto].
    eapply H4;eauto.
    intro.
    destruct H15.
    mytac.
    exists x0.
    assert (x0 <> x).
    intro.
    subst x0.
    unfolds in H15.
    mytac.
    rewrite H15 in H5;inverts H5.
    tryfalse.
    unfolds in H15.
    unfolds.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto]. 
    mytac.
    do 3 eexists;eauto.

    unfolds.
    unfolds in H16.
    intros.

    rewrite TcbMod.set_a_get_a' in H16;[ | apply tidspec.neq_beq_false;auto].
    apply H16 in H19.
    destruct H19.
    left.
    mytac.
    unfolds in H19.
    mytac.
    assert (x0 <> x).
    intro.
    subst x0.
    rewrite EcbMod.set_a_get_a in H19;[ | apply tidspec.eq_beq_true;auto].
    inverts H19.
    tryfalse.
    rewrite EcbMod.set_a_get_a' in H19;[ | apply tidspec.neq_beq_false;auto].
    exists x0;unfolds.
    do 2 eexists;eauto.

    right.
    mytac.
    intro.
    destruct H19.
    mytac.
    exists x2.
    unfolds.
    assert (x2 <> x).
    intro.
    subst x.
    unfolds in H19.
    mytac.
    rewrite H19 in H5;inverts H5.
    tryfalse.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    unfolds in H19;mytac.
    do 3 eexists;eauto.
    do 2 eexists;eauto.


  destruct H2.
  mytac.
  (*------timetick---------*)
    clear -H0 H1 H5 H8 H9 Hnnp'.
    rename H5 into H6.
    rename H9 into H12.
    rename H8 into Hfff.
    inverts H6.
    mytac.
    assert (get O' absecblsid = Some (absecblist x0)) as Hels.
    eapply join_get_get_l;eauto.
    assert (get O' abtcblsid = Some (abstcblist x)) as Htls.
    eapply join_get_get_l;eauto.
    assert (get O' ostmid = Some (ostm x1)) as Htm.
    eapply join_get_get_l;eauto.

    assert (O'' =  (set
                      (set (set O' absecblsid (absecblist x3)) abtcblsid
                           (abstcblist x2)) ostmid (ostm (x1 +ᵢ  Int.one)))).
    eapply join_get_set_eq_3;eauto.
    subst O''.
    clear H2 H3 H.
    remember O' as Ox.
    clear HeqOx.
    rename x0 into els.
    rename x into tls.
    unfold GOOD_ST in *.
    intros.
    unfolds in Hnnp'.
    lets Hnnp'': Hnnp' H H2.
    clear Hnnp'.
    unfolds in H0.
    lets Hnnp: H0 Hels Htls.
    clear H0.
    unfold get in *;simpl in *.
    rewrite abst_set_get_neq in H;auto.
    rewrite abst_set_get_neq in H;auto.
    rewrite OSAbstMod.map_get_set in H.
    inverts H.
    rewrite abst_set_get_neq in H2;auto.
    rewrite OSAbstMod.map_get_set in H2.
    inverts H2.

    lets Hgoodst: H1 Hels Htls.
    clear H1.
    unfolds in H6.

    eapply tickstep_goodst;eauto.
    apply TcbMod.sub_refl.
  
  mytac.
  +
  inverts H7.
  auto.
  +
  (* Sched *)
  unfolds.
  intros.
  rewrite abst_set_get_neq in H2;auto.
  rewrite abst_set_get_neq in H7;auto.
  +
    unfolds in H.
    mytac.
    unfold get in *;simpl in *.
    rewrite H in H8;inverts H8.
    repeat progress (destruct H3;[ mytac;rewrite H2 in H5;tryfalse | ]).
    mytac.
    rewrite H2 in H5;tryfalse.
  +
    unfolds in H.
    mytac.
    unfold get in *;simpl in *.
    rewrite H in H8;inverts H8.
    repeat progress (destruct H3;[ mytac;rewrite H2 in H5;tryfalse | ]).
    mytac.
    rewrite H2 in H5;tryfalse.
  +
    unfolds in H.
    mytac.
    unfold get in *;simpl in *.
    rewrite H in H13;inverts H13.
    repeat progress (destruct H4;[ mytac;rewrite H2 in H3;tryfalse | ]).
    mytac.
    rewrite H2 in H3;tryfalse.
Qed.

  
Lemma timetick_weakpif:
  forall tls tls0 els els0 tlsx ct t p_ct p_t,
    (rdy_notin_wl tls els /\

         owner_prio_prop tls els /\
         task_stat_prop tls /\
         op_p_prop tls els /\ wait_prop tls els /\ no_owner_prio_prop tls els) ->
    TcbMod.sub tlsx tls ->
    (forall p_ct',
       GET_OP ct tls els p_ct' ->
       NO_NEST_PENDING tls els ->
       HighestRdy tls ct ->
        ~ (exists eid, IS_OWNER ct eid els) ->
       forall (t0 : addrval) (p_t0 : int32),
         t0 <> ct ->
         TcbMod.get tls t0 <> None ->
         GET_OP t0 tls els p_t0 ->
         IS_WAITING t0 els -> Int.ltu p_ct' p_t0 = true) ->
    t <> ct ->
    TcbMod.get tls0 t <> None ->
    GET_OP ct tls0 els0 p_ct ->
    GET_OP t tls0 els0 p_t ->
    NO_NEST_PENDING tls els ->
    NO_NEST_PENDING tls0 els0 ->
    HighestRdy tls0 ct ->
    ~ (exists eid, IS_OWNER ct eid els0) ->
    IS_WAITING t els0 ->
    tickstep' tls els tls0 els0 tlsx ->
    Int.ltu p_ct p_t = true.
Proof.
   introv Hgoodst.
  intros.
  induction H10.
  eapply H0;eauto.
  assert (TcbMod.get tls t0 = Some (p, st, msg0) ).
  eapply sub_joinsig_get;eauto.
  lets Hgoodst': tickchange_goodst H5 H14 Hgoodst H11 H12.
  eapply IHtickstep';eauto.
  eapply tcbjoinsig_set_sub_sub;eauto. 
  intros.

  assert (exists pct stct mct,TcbMod.get tls ct = Some (pct,stct,mct)).

  eapply tickchange_exct;eauto.
  destruct H23 as (pct&stct&mct&H23).
  destruct Hgoodst as (Hrdyninwl&Hownerpp&Htaskstp&Hoppprop&Hwaitexowner&Hnoownerp).
  unfolds in Htaskstp.
  lets Hx:Htaskstp H23.
  destruct Hx.
  subst stct.
  
  eapply H0;eauto.
  eapply tickchange_getop_eq with (t0:=t0);eauto.
  eapply tickchange_highestrdy_rdy with (t0:=t0);eauto.
  eapply tickchange_no_owner with (t0:=t0);eauto.
  eapply tickchange_nonone with (t0:=t0);eauto.
  eapply tickchange_getop_eq with (t0:=t0);eauto.
  eapply tickchange_iswait with (t0:=t0);eauto.

  destruct H24 as (eid&tm&H24).
  subst stct.
  assert ( p_ct' = pct).
  unfolds in Hnoownerp.
  eapply Hnoownerp;eauto.

  clear -H5 H23 Hrdyninwl.
  unfolds in H5.
  intro.
  destruct H.
  lets Hx: H5 H.
  intro.
  rewrite H0 in H23;tryfalse.
  destruct Hx.
  destruct H0.
  unfolds in Hrdyninwl.
  destructs Hrdyninwl.
  lets Hx: H2 H23.
  unfolds in Hx.
  mytac.
  unfolds.
  do 4 eexists;eauto.
  eapply tickchange_getop_eq with (t0:=t0);eauto.
  subst pct.

  assert (exists p st m, TcbMod.get tls' t1 = Some (p,st,m)).
  remember (TcbMod.get tls' t1) as X;destruct X;tryfalse.
  destruct b.
  destruct p0.
  do 3 eexists;eauto.
  destruct Hgoodst' as (Hrdyninwl'&Hownerpp'&Htaskstp'&Hoppprop'&Hwaitexowner'&Hnoownerp').
  clear IHtickstep'.
  unfolds in Htaskstp'.
  mytac.
  lets Htaskstpx:Htaskstp' H24.

  destruct Htaskstpx.
  subst x0.
  unfolds in H17.
  mytac.

  lets Hx:tickchange_eq_prio ct H11 H14 H23 H12.
  auto.
  subst x0.
  lets Hx:H17 H19 H24.
  unfolds in Hoppprop'.
  lets Hy:Hoppprop' H24 H21.
  clear -Hx Hy.
  destruct Hy;int auto.
  
  mytac;subst.
  unfolds in Hwaitexowner'.
  lets Hx:Hwaitexowner' H24.
  mytac.

  assert (x0 <> ct ).
  intro.
  subst x0.

  lets Hx:tickchange_nonest_ct H11 H14 H12 H23 H5.
  eauto.
  auto.
  auto.
  unfolds in H17.
  mytac.
  lets Hx:tickchange_eq_prio ct H11 H14 H23 H17.
  auto.
  subst x6.
  lets Hz: H29 H28 H25.
  lets Hy:H27 H21.
  clear -H26 Hz Hy.
  subst x.
  int auto.

  eapply tickchange_nonestpend with (t0:=t0);eauto.
Qed.

Theorem no_nest_pif:
  forall client_code T cst O T' cst' O',
    NO_NEST_PENDING_O O ->
    NO_NEST_PENDING_O O' ->
    (O = O' \/ (GOOD_API_CODE O T)) ->
    GOOD_ST O ->
    WEAK_PIF O ->
    hpstep (client_code, os_spec') T cst O T' cst' O' ->
    WEAK_PIF O'.
Proof.
  introv Hnonesto Hnonesto' Hgoodapicode Hgoodst.
  intros.
  unfold os_spec in *.
  assert (GOOD_ST O') as Hgoodst'.
  eapply code_exe_prop2;eauto.
  inversion H0;subst.
  unfold get in *;simpl in *.
  -
    clear H0.
    rename H3 into Htget.
    inverts H2.
    
    
      (*task step*)
        (*client step*)
        auto.

        (*no cre del api step*)
        inverts H0;auto.
        inverts H3;auto.
        inverts H0;auto.
        destruct Hgoodapicode.
        subst O'.
        assert (O0 =O'0) as Hx.
        apply join_comm in H6.
        apply join_comm in H5.
        eapply join_unique_r;eauto.
        subst.
        auto.
        unfolds in H0.
        mytac.
        rewrite H1 in H0;inverts H0.
        rewrite Htget in H7;inverts H7.
        destruct H8.
        mytac.

        (*mutex acc*)
        clear -H H2 H5 H6 Hgoodst Hnonesto' Hnonesto.
        rename H2 into H1.
        rename H5 into Hfff.
        rename H6 into Hffff.
        inverts H1.
        
        mytac.
        clear H6;rename H7 into H6.
        assert (get O curtid = Some (oscurt x8)) as Hct.
        eapply join_get_get_l;eauto.
        assert (get O absecblsid = Some (absecblist x0)) as Hels.
        eapply join_get_get_l;eauto.
        assert (get O abtcblsid = Some (abstcblist x1)) as Htls.
        eapply join_get_get_l;eauto.

        assert (O' = (set O absecblsid
            (absecblist (set x0 x (absmutexsem x3 (Some (x8, x5)), x4))))).
        eapply join_get_set_eq;eauto.
        subst O'.
        remember O as Ox.
        clear HeqOx.
        rename x8 into ct.
        rename x0 into els.
        rename x1 into tls.

        unfold get in *;simpl in *.
        unfolds.
        intros.
        rewrite OSAbstMod.map_get_set in H0.
        inverts H0.
        rewrite abst_set_get_neq in H7;auto.
        rewrite H7 in Hct;inverts Hct.
        destruct H11.
        exists x.
        unfolds.
        exists x3 x5 x4.
        rewrite EcbMod.set_a_get_a.
        auto.
        apply tidspec.eq_beq_true;auto.
        
       
        Lemma set_getop_eq:
          forall ct tls x4 x3 x6 x7 p_ct x0 x1,
            TcbMod.get tls ct = Some (p_ct, x0, x1) ->
            EcbMod.get x4 x3 = Some (absmutexsem x6 None, x7) ->
            GET_OP ct tls (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, p_ct)), x7)) p_ct ->
            NO_NEST_PENDING tls
                            (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, p_ct)), x7)) ->
            GET_OP ct tls x4 p_ct.
        Proof.
          intros.
          rename H2 into Hnonest.
          unfolds in H1.
          unfolds;intros.
          apply H1 in H2.
          clear H1.
          destruct H2.
          right.
          split;eauto.
          eapply no_nest_pending_set_none;eauto.
          right;split;eauto.
          eapply no_nest_pending_set_none;eauto.
        Qed.

        (*mutex cre*)
        destruct H0.
        mytac.
        unfold mutexcre_succ in H2.
        mytac.
        assert (O' = (set O absecblsid (absecblist x5))).
        eapply join_get_set_eq;eauto.
        subst O'.
        remember O as Ox.
        clear Htget H3 H4 H6.
        unfold WEAK_PIF in *.
        intros.
        rewrite OSAbstMod.map_get_set in H0.
        inverts H0.
        rewrite abst_set_get_neq in H2;auto.
        rewrite abst_set_get_neq in H3;auto.
        rewrite H1 in H3;inverts H3.
        lets Hgetop: getop_cre_hold H4 H11.
        lets Hnonest: no_nest_pending_cre_hold H6 H11.
        assert (OSAbstMod.get Ox absecblsid = Some (absecblist x4)).
        subst.
        eapply join_get_l in H7;eauto.
        unfolds in H7;simpl in *;auto.
        rewrite H2 in H7;inverts H7.
        eapply join_get_l in H8;eauto.
        unfold get in *;simpl in *.
        lets Hx:H H0 H2 H1 Hgetop Hnonest.
        lets Hgetop': getop_cre_hold H16 H11.
        lets Hiswait: iswaiting_cre_hold H11 H17;auto.
        lets Hnoowner: no_owner_cre H13 H11.
        lets Hx': Hx H12 Hnoowner H15 Hiswait;eauto.

        (*mutex del*)
        destruct H0.
        mytac.
        unfold mutexdel_succ in H2.
        mytac.
        assert (O'= (set O absecblsid (absecblist x5))).
        eapply join_get_set_eq;eauto.
        subst O'.
        clear H6.
        remember O as Ox.
        subst O.
        eapply join_get_l in H2;eauto.
        
        unfold get in *;simpl in *.
        clear Htget H3 H4.
        unfold WEAK_PIF in *.
        intros.
        rewrite OSAbstMod.map_get_set in H0.
        inverts H0.
        rewrite abst_set_get_neq in H3;auto.
        rewrite abst_set_get_neq in H4;auto.
        rewrite H1 in H4;inverts H4.
        assert (OSAbstMod.get Ox absecblsid = Some (absecblist x4)).
        auto.
        lets Hgetop: getop_del_hold H14 H9.
        lets Hgetop':getop_del_hold H6 H9.
        lets Hnonest: no_nest_pending_del H8 H9.
        lets Hx': H H0 H3 H1 Hgetop' Hnonest.

        lets Hiswait:iswaiting_del_hold H9 H15.
        lets Hnoowner: no_owner_del H11 H9.
        lets Hx'': Hx' H10 Hnoowner Hgetop Hiswait;auto.

        (*mutex pend get succ *)
        destruct H0.
        mytac.
        clear -H H2 H5 H6 Hgoodst Hnonesto' Hnonesto.
        rename H2 into H1.
        rename H5 into Hfff.
        rename H6 into Hffff.
        inverts H1.
        mytac.
        clear H6.
        assert (get O curtid = Some (oscurt x8)) as Hct by (eapply join_get_l;eauto).
        assert (get O absecblsid = Some (absecblist x1)) as Hels by (eapply join_get_l;eauto).
        assert (get O abtcblsid = Some (abstcblist x4)) as Htls by (eapply join_get_l;eauto).
        assert (O' = (set O absecblsid
                          (absecblist (set x1 x (absmutexsem x7 (Some (x8, x5)), nil))))).
        eapply join_get_set_eq;eauto.
        subst O'.
        clear H1 H2 H3 Hffff Hfff.
        remember O as Ox.
        clear HeqOx.
        rename x8 into ct.
        rename x1 into els.
        rename x4 into tls.
        unfold get in *;simpl in *.
        unfolds.
        intros.
        rewrite OSAbstMod.map_get_set in H0.
        inverts H0.
        rewrite abst_set_get_neq in H2;auto.
        rewrite H2 in Hct;inverts Hct.
        destruct H8.
        exists x.
        unfolds.
        do 3 eexists.
        rewrite EcbMod.set_a_get_a.
        auto.
        apply tidspec.eq_beq_true;auto.
        
        (*---------------*)
        destruct H0;mytac.
        destruct H0;mytac.
        destruct H0;mytac.

        clear -H H2 H5 H6 Hnonesto Hgoodst Hgoodst'.
        rename H2 into H3.
        rename H5 into Hfff.
        rename H6 into Hffff.
        unfolds in H3.
        assert (NO_NEST_PENDING_O O) as H4 by auto.
        assert (GOOD_ST O) as H5 by auto.
        
        mytac.
        clear H4 H5.
        assert (get O curtid = Some (oscurt x9)) as Hct by (eapply join_get_l;eauto).
        assert (get O absecblsid = Some (absecblist x0)) as Hels by (eapply join_get_l;eauto).
        assert (get O abtcblsid = Some (abstcblist x1)) as Htls by (eapply join_get_l;eauto).
        assert (O' = (set (set O abtcblsid (abstcblist (set x1 x9 (x6, x7, x8))))
               absecblsid (absecblist (set x0 x (absmutexsem x5 None, nil))))).
        eapply join_get_set_eq_2;eauto.
        subst O'.
        clear H1 H2 H3 Hffff Hfff.
        remember O as Ox.
        rename x9 into ct.
        rename x0 into els.
        rename x1 into tls.
        clear HeqOx.

        unfold get in *;simpl in *.
        unfold WEAK_PIF in *.
        intros.

        rewrite OSAbstMod.map_get_set in H0;inverts H0.
        rewrite abst_set_get_neq in H1;auto.
        rewrite OSAbstMod.map_get_set in H1;inverts H1.
        rewrite abst_set_get_neq in H2;auto.
        rewrite abst_set_get_neq in H2;auto.
        rewrite H2 in Hct;inverts Hct.
        assert (HighestRdy (TcbMod.set tls ct (x6, x7, x8)) ct) as Hhighest by auto.
        unfolds in H5.
        mytac.
        rewrite TcbMod.set_a_get_a in H0.
        inverts H0.
        unfolds in Hgoodst'.
        rewrite OSAbstMod.map_get_set in Hgoodst'.
        rewrite abst_set_get_neq in Hgoodst';auto.
        rewrite OSAbstMod.map_get_set in Hgoodst'.

        assert (Some (absecblist (EcbMod.set els x (absmutexsem x5 None, nil))) =
                Some (absecblist (EcbMod.set els x (absmutexsem x5 None, nil)))).
        auto.
        assert (Some (abstcblist (TcbMod.set tls ct (x0, rdy, x1))) =
                Some (abstcblist  (TcbMod.set tls ct (x0, rdy, x1)))).
        auto.
        lets Hgoodstx:Hgoodst' H0 H5.
        clear H0 Hgoodst' H5.
        destruct Hgoodstx as (Hrdyninwl&Hownerpp&Htaskstp&Hoppprop&Hwaitexowner&Hnoownerp).
        unfolds in Htaskstp.
        assert (exists p st m, TcbMod.get (TcbMod.set tls ct (x0, rdy, x1)) t = Some (p,st,m)).
        remember (TcbMod.get (TcbMod.set tls ct (x0, rdy, x1)) t) as X;destruct X;tryfalse.
        destruct b.
        destruct p.
        do 3 eexists;eauto.
        destruct H10;auto.
        mytac.
        assert (TcbMod.get tls t = Some (x2, x3, x4)).
        rewrite TcbMod.set_a_get_a' in H0;[ | apply tidspec.neq_beq_false;auto];auto.
        lets Htaskstp':Htaskstp H0.

        lets Hpct:post_lift_get_op_ct Hnonesto Hels Htls H6 H3;auto.
        subst x0.
        
        destruct Htaskstp'.
        subst x3.
        lets Hx:H1 H9 H0.
        unfolds in Hoppprop.
        lets Hy:Hoppprop H0 H11.
        clear -Hx Hy.
        destruct Hy;int auto.
        mytac;subst.
        unfolds in Hwaitexowner.
        lets Hx:Hwaitexowner H0.
        mytac.

        lets Hx:post_lift_ct_nowner Hnonesto Hels Htls H6 H13;auto.
        eauto.
        lets Hz: H1 Hx H14.
        lets Hy:H16 H11.
        clear -H15 Hz Hy.
        subst x2.
        int auto.
        apply tidspec.eq_beq_true;auto.
        
        destruct H0;mytac.

        (*mutex post nowt no return*)
        clear -H H2  H5 H6 Hnonesto Hgoodst Hgoodst'.
        rename H2 into H3.
        rename H5 into Hfff.
        rename H6 into Hffff.
        unfolds in H3.
        assert ( NO_NEST_PENDING_O O) as H4 by auto.
        assert ( NO_NEST_PENDING_O O) as H5 by auto.
        mytac.
        clear H4 H5.
        assert (get O curtid = Some (oscurt x9)) as Hct by (eapply join_get_l;eauto).
        assert (get O absecblsid = Some (absecblist x0)) as Hels by (eapply join_get_l;eauto).
        assert (get O abtcblsid = Some (abstcblist x1)) as Htls by (eapply join_get_l;eauto).
        assert (O' =(set O absecblsid
               (absecblist (set x0 x (absmutexsem x4 None, nil))))).
        eapply join_get_set_eq;eauto.
        subst O'.
        clear H1 H2 H3 Hffff Hfff.
        remember O as Ox.
        rename x9 into ct.
        rename x0 into els.
        rename x1 into tls.
        clear HeqOx.
        unfold get in *;simpl in *.
        unfold WEAK_PIF in *.
        intros.
        rename H10 into Hn.
        rewrite OSAbstMod.map_get_set in H0;inverts H0.
        rewrite abst_set_get_neq in H1;auto.
        rewrite Htls in H1;inversion H1;subst tls0.
        rewrite abst_set_get_neq in H2;auto.
        rewrite H2 in Hct;inverts Hct.
        unfolds in H5.
        mytac.
        unfolds in Hgoodst'.
        rewrite OSAbstMod.map_get_set in Hgoodst'.
        rewrite abst_set_get_neq in Hgoodst';auto.

        assert (Some (absecblist (EcbMod.set els x (absmutexsem x4 None, nil))) =
                Some (absecblist (EcbMod.set els x (absmutexsem x4 None, nil)))).
        auto.
        
        lets Hgoodstx:Hgoodst' H1 Htls.
        clear Hgoodst' H1.
        destruct Hgoodstx as (Hrdyninwl&Hownerpp&Htaskstp&Hoppprop&Hwaitexowner&Hnoownerp).
        unfolds in Htaskstp.
        assert (exists p st m, TcbMod.get tls t = Some (p,st,m)).
        remember (TcbMod.get tls t) as X;destruct X;tryfalse.
        destruct b.
        destruct p.
        do 3 eexists;eauto.
        mytac.
        lets Htaskstp':Htaskstp H1.

        rewrite H7 in H0;inverts H0.
        assert (x0 = x5).
        clear -Hgoodst H8 H7 H6 Htls Hels.
        unfolds in Hgoodst.
        lets Hx:Hgoodst Hels Htls.
        mytac.
        unfolds in H0.
        lets Hx: H0 H7 H6.
        destruct Hx.
        destruct H5;auto.
        subst x0.
        false.
        clear -H8.
        int auto.

        subst x5.
        lets Hpct:post_nolift_get_op_ct Hnonesto Hels Htls H6 H3;auto.
        eauto.
        subst x0.
        
        destruct Htaskstp'.
        subst x3.
        lets Hx:H5 Hn H1.
        unfolds in Hoppprop.
        lets Hy:Hoppprop H1 H12.
        clear -Hx Hy.
        destruct Hy;int auto.
        mytac;subst.
        unfolds in Hwaitexowner.
        lets Hx:Hwaitexowner H1.
        mytac.

        lets Hx:post_no_lift_ct_nowner Hnonesto Hels Htls H6 H0;auto.
        eauto.
        lets Hz: H5 Hx H10.
        lets Hy:H15 H12.
        clear -H14 Hz Hy.
        subst x2.
        int auto.
        
        destruct H0;mytac.
        destruct H0;mytac.
        destruct H0;mytac.
        
        destruct Hgoodapicode;subst;auto.
        unfolds in H0.
        mytac.
        rewrite H0 in H1;inverts H1.
        rewrite Htget in H3.
        inverts H3.
        destruct H4;mytac.
        destruct H1;mytac.
        destruct H1;mytac.
        destruct H1;mytac.

        (*mutex pend block no lift*)
        destruct H1;mytac.
        clear -H H2.
        rename H2 into H1.
        inverts H1.
        rename H7 into Hfff.
        rename H11 into Hffff.
        unfolds in H3.
        mytac.
        clear H10.
        clear H4 H5.
        assert (get O curtid = Some (oscurt x14)) as Hct by (eapply join_get_l;eauto).
        assert (get O absecblsid = Some (absecblist x5)) as Hels by (eapply join_get_l;eauto).
        assert (get O abtcblsid = Some (abstcblist x3)) as Htls by (eapply join_get_l;eauto).
        assert (O' =(set
               (set O abtcblsid
                  (abstcblist
                     (set x3 x14 (x12, wait (os_stat_mutexsem x) x0, Vnull))))
               absecblsid
               (absecblist
                  (set x5 x (absmutexsem x8 (Some (x9, x10)), x14 :: x7))))).
        eapply join_get_set_eq_2;eauto.
        subst O'.
        clear H1 H2 H3 Hffff Hfff.
        remember O as Ox.
        rename x14 into ct.
        rename x5 into els.
        rename x3 into tls.
        clear HeqOx.
        unfold get in *;simpl in *.
        unfold WEAK_PIF.
        intros.
        rewrite OSAbstMod.map_get_set in H0;inverts H0.
        rewrite abst_set_get_neq in H1;auto.
        rewrite OSAbstMod.map_get_set in H1;inverts H1.
        rewrite abst_set_get_neq in H2;auto.
        rewrite abst_set_get_neq in H2;auto.

        rewrite H2 in Hct;inverts Hct.
        unfolds in H5.
        mytac.
        
        rewrite TcbMod.set_a_get_a in H0.
        inverts H0.
        apply tidspec.eq_beq_true;auto.

        (*mutex pend lift*)
        destruct H1;mytac.
        clear -H H2 Hgoodst.
        rename H2 into H1.
        inverts H1.
        rename H7 into Hfff.
        rename H11 into Hffff.
        unfolds in H3.
        mytac.
        clear H11.
        clear H4 H5.
        assert (get O curtid = Some (oscurt x15)) as Hct by (eapply join_get_l;eauto).
        assert (get O absecblsid = Some (absecblist x6)) as Hels by (eapply join_get_l;eauto).
        assert (get O abtcblsid = Some (abstcblist x3)) as Htls by (eapply join_get_l;eauto).
        assert (O' = (set
               (set O abtcblsid
                  (abstcblist
                     (set
                        (set x3 x15 (x13, wait (os_stat_mutexsem x) x0, x2))
                        x10 (x9, rdy, x14)))) absecblsid
               (absecblist
                  (set x6 x (absmutexsem x9 (Some (x10, x11)), x15 :: x8))))).
        eapply join_get_set_eq_2;eauto.
        subst O'.
        clear H1 H2 H3 Hffff Hfff.
        remember O as Ox.
        rename x15 into ct.
        rename x6 into els.
        rename x3 into tls.
        clear HeqOx.
        unfold get in *;simpl in *.
        unfold WEAK_PIF in *.
        intros.
        rewrite OSAbstMod.map_get_set in H0;inverts H0.
        rewrite abst_set_get_neq in H1;auto.
        rewrite OSAbstMod.map_get_set in H1;inverts H1.
        rewrite abst_set_get_neq in H2;auto.
        rewrite abst_set_get_neq in H2;auto.
        rewrite H2 in Hct;inverts Hct.
        unfolds in H5.
        mytac.
        assert (x10 = ct \/ x10 <> ct) by tauto.
        destruct H5;try subst x10.


        unfolds in H4.
        assert (TcbMod.get
         (TcbMod.set
            (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2)) ct
            (x9, rdy, x14)) ct <> None).
        intro.
        unfold set in *;simpl in *.
        rewrite H5 in H0;tryfalse.

        eapply H4 with (qid:=x) in H5.
        destruct H5.
        destruct H5.
        unfolds.
        do 4 eexists.
        split.
        rewrite EcbMod.set_a_get_a;eauto.
        apply tidspec.eq_beq_true;auto.
        simpl;auto.
        unfolds.
        do 3 eexists.
        rewrite EcbMod.set_a_get_a;eauto.
        apply tidspec.eq_beq_true;auto.
        
        rewrite TcbMod.set_a_get_a' in H0;[ | apply tidspec.neq_beq_false;auto].
        rewrite TcbMod.set_a_get_a in H0.
        inverts H0.
        apply tidspec.eq_beq_true;auto.

   
        destruct H1;mytac.
        destruct H1;mytac.

        (*mutex post exwt return*)
        destruct H1.
        mytac.
        rename H2 into H1.
        clear -H H1 Hnonesto Hgoodst Hgoodst'.
        inverts H1.
        rename H7 into Hfff.
        rename H11 into Hffff.
        unfolds in H3.
        mytac.
        clear H4 H5.
        assert (get O curtid = Some (oscurt x15)) as Hct by (eapply join_get_l;eauto).
        assert (get O absecblsid = Some (absecblist x0)) as Hels by (eapply join_get_l;eauto).
        assert (get O abtcblsid = Some (abstcblist x2)) as Htls by (eapply join_get_l;eauto).
        assert (O' =  (set
               (set O abtcblsid
                  (abstcblist
                     (set (set x2 x15 (x8, x9, x10)) x12 (x7, rdy, Vptr x))))
               absecblsid
               (absecblist
                  (set x0 x
                     (absmutexsem x6 (Some (x12, x7)), remove_tid x12 x11))))).
        eapply join_get_set_eq_2;eauto.
        subst O'.
        clear H1 H2 H3 Hffff Hfff.
        remember O as Ox.
        rename x15 into ct.
        rename x0 into els.
        rename x2 into tls.
        clear HeqOx.
        unfold get in *;simpl in *.
        lets Hneq: post_ex_wait_ct_neq Hnonesto Hels Htls H6 H8.
        
        unfold WEAK_PIF in *.
        intros.
        unfold set in *;simpl in *.
        rewrite OSAbstMod.map_get_set in H0;inverts H0.
        rewrite abst_set_get_neq in H1;auto.
        rewrite OSAbstMod.map_get_set in H1;inverts H1.
        rewrite abst_set_get_neq in H2;auto.
        rewrite abst_set_get_neq in H2;auto.
        rewrite H2 in Hct;inverts Hct.
        unfolds in H5.
        mytac.
        rewrite TcbMod.set_a_get_a' in H0.
        rewrite TcbMod.set_a_get_a in H0.
        inverts H0.
        unfolds in Hgoodst'.
        rewrite OSAbstMod.map_get_set in Hgoodst'.
        rewrite abst_set_get_neq in Hgoodst';auto.
        rewrite OSAbstMod.map_get_set in Hgoodst'.

        assert ( Some
               (absecblist
                  (EcbMod.set els x
                     (absmutexsem x6 (Some (x12, x7)), remove_tid x12 x11))) =
                Some
               (absecblist
                  (EcbMod.set els x
                     (absmutexsem x6 (Some (x12, x7)), remove_tid x12 x11)))).
        auto.
        assert ( Some
               (abstcblist
                  (TcbMod.set (TcbMod.set tls ct (x0, rdy, x1)) x12
                     (x7, rdy, Vptr x)))   =
                Some
               (abstcblist
                  (TcbMod.set (TcbMod.set tls ct (x0, rdy, x1)) x12
                     (x7, rdy, Vptr x)))  ).
        auto.
        lets Hgoodstx:Hgoodst' H0 H5.
        clear H0 Hgoodst' H5.
        destruct Hgoodstx as (Hrdyninwl&Hownerpp&Htaskstp&Hoppprop&Hwaitexowner&Hnoownerp).
        unfolds in Htaskstp.
        assert (exists p st m, TcbMod.get  (TcbMod.set (TcbMod.set tls ct (x0, rdy, x1)) x12 (x7, rdy, Vptr x)) t = Some (p,st,m)).
        remember (TcbMod.get (TcbMod.set (TcbMod.set tls ct (x0, rdy, x1)) x12 (x7, rdy, Vptr x)) t) as X;destruct X;tryfalse.
        destruct b.
        destruct p.
        do 3 eexists;eauto.
        destruct H13;auto.
        mytac.
        assert (t = x12 \/ t <> x12) by tauto.
        destruct H5.
        subst x12.
        Focus 2.
        assert (TcbMod.get tls t = Some (x2, x3, x4)).
        
        rewrite TcbMod.set_a_get_a' in H0;[ | apply tidspec.neq_beq_false;auto];auto.
        rewrite TcbMod.set_a_get_a' in H0;[ | apply tidspec.neq_beq_false;auto];auto.
        
        lets Htaskstp':Htaskstp H0.

        lets Hpct:post_lift_exwt_get_op_ct Hneq Hnonesto Hels Htls H3;auto.
        eauto.
        subst x0.
        
        destruct Htaskstp'.
        subst x3.
        lets Hx:H1 H12 H0.
        unfolds in Hoppprop.
        lets Hy:Hoppprop H0 H14.
        clear -Hx Hy.
        destruct Hy;int auto.
        mytac;subst.
        unfolds in Hwaitexowner.
        lets Hx:Hwaitexowner H0.
        mytac.

        lets Hx:post_lift_exwt_ct_nowner Hnonesto Hels Htls H17 Hneq;auto.
        eauto.
        eauto.
        lets Hz: H1 Hx H18.
        lets Hy:H20 H14.
        clear -H19 Hz Hy.
        subst x2.
        int auto.

        lets Hpct:post_lift_exwt_get_op_ct Hneq Hnonesto Hels Htls H3;auto.
        eauto.
        subst x0.
        assert (x3 = rdy).
        rewrite TcbMod.set_a_get_a in H0;[ | apply tidspec.eq_beq_true;auto];auto.
        inverts H0.
        auto.
        subst x3.
        lets Hx:H1 H12 H0.
        unfolds in Hoppprop.
        lets Hy:Hoppprop H0 H14.
        clear -Hx Hy.
        destruct Hy;int auto.
        mytac;subst.
        apply tidspec.eq_beq_true;auto.
        apply tidspec.neq_beq_false;auto.

        (*mutex post exwt no return*)
        destruct H1.
        mytac.
        rename H2 into H1.
        clear -H H1 Hnonesto Hgoodst Hgoodst'.
        inverts H1.
        rename H7 into Hfff.
        rename H11 into Hffff.
        unfolds in H3.
        mytac.
        clear H4 H5.
        assert (get O curtid = Some (oscurt x5)) as Hct by (eapply join_get_l;eauto).
        assert (get O absecblsid = Some (absecblist x0)) as Hels by (eapply join_get_l;eauto).
        assert (get O abtcblsid = Some (abstcblist x2)) as Htls by (eapply join_get_l;eauto).
        assert (O' = (set
               (set O abtcblsid (abstcblist (set x2 x13 (x7, rdy, Vptr x))))
               absecblsid
               (absecblist
                  (set x0 x
                     (absmutexsem x6 (Some (x13, x7)), remove_tid x13 x12))))).
        eapply join_get_set_eq_2;eauto.
        subst O'.
        clear H1 H2 H3 Hffff Hfff.
        remember O as Ox.
        rename x5 into ct.
        rename x0 into els.
        rename x2 into tls.
        clear HeqOx.
        lets Hneq: post_ex_wait_ct_neq Hnonesto Hels Htls H6 H8.
        unfold get in *;unfold set in *;simpl in *.
        unfold WEAK_PIF in *.
        intros.
        rewrite OSAbstMod.map_get_set in H0;inverts H0.
        rewrite abst_set_get_neq in H1;auto.
        rewrite OSAbstMod.map_get_set in H1;inverts H1.
        rewrite abst_set_get_neq in H2;auto.
        rewrite abst_set_get_neq in H2;auto.
       
        rewrite H2 in Hct;inverts Hct.
        unfolds in H5.
        mytac.
        unfolds in Hgoodst'.
        rewrite OSAbstMod.map_get_set in Hgoodst'.
        rewrite abst_set_get_neq in Hgoodst';auto.
        rewrite OSAbstMod.map_get_set in Hgoodst'.
        assert ( Some
               (absecblist
                  (EcbMod.set els x
                     (absmutexsem x6 (Some (x13, x7)), remove_tid x13 x12)))=
                 Some
               (absecblist
                  (EcbMod.set els x
                     (absmutexsem x6 (Some (x13, x7)), remove_tid x13 x12)))).
        auto.
        assert (Some (abstcblist (TcbMod.set tls x13 (x7, rdy, Vptr x))) =Some (abstcblist (TcbMod.set tls x13 (x7, rdy, Vptr x)))).
        auto.
        
        lets Hgoodstx:Hgoodst' H5 H17.
        clear Hgoodst' H5 H17.
        destruct Hgoodstx as (Hrdyninwll&Hownerpp&Htaskstp&Hoppprop&Hwaitexowner&Hnoownerp).
        unfolds in Htaskstp.
        assert (exists p st m, TcbMod.get (TcbMod.set tls x13 (x7, rdy, Vptr x)) t = Some (p,st,m)).
        remember (TcbMod.get (TcbMod.set tls x13 (x7, rdy, Vptr x)) t) as X;destruct X;tryfalse.
        destruct b.
        destruct p.
        do 3 eexists;eauto.
        mytac.
        assert (t = x13 \/ t <> x13) by tauto.
        destruct H17.
        Focus 2.
        lets Htaskstp':Htaskstp H5.
        rewrite TcbMod.set_a_get_a' in H0;[ | apply tidspec.neq_beq_false;auto];auto.
        unfold get in *;unfold set in *;simpl in *.
        rewrite H0 in H10;inverts H10.

        assert (x8 = x9).
        clear -Hgoodst H9 H0 H6 Htls Hels.
        unfolds in Hgoodst.
        lets Hx:Hgoodst Hels Htls.
        mytac.
        unfolds in H1.
        lets Hx: H1 H0 H6.
        destruct Hx.
        destruct H7;auto.
        subst x8.
        false.
        clear -H9.
        int auto.
        subst x8.

        lets Hpct:post_nolift_exwt_get_op_ct Hnonesto Hels Htls H6 H3;auto.
        eauto.
        subst x9.
        
        destruct Htaskstp'.
        subst x3.
        lets Hx:H1 H13 H5.
        unfolds in Hoppprop.
        lets Hy:Hoppprop H5 H15.
        clear -Hx Hy.
        destruct Hy;int auto.
        mytac;subst.
        unfolds in Hwaitexowner.
        lets Hx:Hwaitexowner H5.
        mytac.
        
        lets Hx:post_nolift_exwt_ct_nowner Hnonesto Hels Htls H10 Hneq;auto.
        eauto.
        eauto.
        lets Hz: H1 Hx H18.
        lets Hy:H20 H15.
        clear -H19 Hz Hy.
        subst x2.
        int auto.

        rewrite TcbMod.set_a_get_a' in H0;[ | apply tidspec.neq_beq_false;auto];auto.
        inverts H0.
        lets Hpct:post_nolift_exwt_get_op_ct Hnonesto Hels Htls H6 H3;auto.
        eauto.
        subst x0.
        assert (x3 = rdy).
        rewrite TcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto];auto.
        inverts H5.
        auto.
        subst x3.
        lets Hx:H1 H13 H5.
        unfolds in Hoppprop.
        lets Hy:Hoppprop H5 H15.
        clear -Hx Hy.
        destruct Hy;int auto.

        (* -------time tick---------- *)
        destruct H1;mytac.
        rename H2 into H1.
        clear -H H1 Hnonesto Hgoodst Hgoodst'.
        inverts H1.
        rename H7 into Hfff.
        rename H11 into Hffff.
        unfolds in H3.
        mytac.
        clear H4 H5.
        assert (get O ostmid = Some (ostm x1)) as Htm by (eapply join_get_l;eauto).
        assert (get O absecblsid = Some (absecblist x0)) as Hels by (eapply join_get_l;eauto).
        assert (get O abtcblsid = Some (abstcblist x)) as Htls by (eapply join_get_l;eauto).
        assert (O' =(set
               (set (set O absecblsid (absecblist x3)) abtcblsid
                  (abstcblist x2)) ostmid (ostm (x1 +ᵢ  Int.one)))).
        eapply join_get_set_eq_3;eauto.
        subst O'.
        clear H1 H2 H0 Hffff Hfff.
        remember O as Ox.
        rename x1 into tm.
        rename x0 into els.
        rename x into tls.
        clear HeqOx.
        unfold tickstep in H7.
        unfold WEAK_PIF in *.
        intros.

        rewrite abst_set_get_neq in H0;auto.
        rewrite abst_set_get_neq in H0;auto.
        rewrite OSAbstMod.map_get_set in H0;inverts H0.
        rewrite abst_set_get_neq in H1;auto.
        rewrite OSAbstMod.map_get_set in H1;inverts H1.

        rewrite abst_set_get_neq in H2;auto.
        rewrite abst_set_get_neq in H2;auto.
        rewrite abst_set_get_neq in H2;auto.
        lets Hx:H Hels Htls H2.
        
        unfolds in Hgoodst'.
        rewrite abst_set_get_neq in Hgoodst';auto.
        rewrite abst_set_get_neq in Hgoodst';auto.

        unfolds in Hgoodst.
        lets Hxx': Hgoodst Hels Htls.

        eapply timetick_weakpif;eauto.
        eapply TcbMod.sub_refl;eauto.

        inverts H2.

    +
      inverts H3;auto.
  -
    inverts H1.
    inverts H5;auto.
  -
    (*swi step*)
    inverts H1.
    rename H2 into H1.
    rename H3 into H2.
    rename H4 into H3.
    assert (t' = t \/ t' <> t) by tauto.
    destruct H4.
    subst t'.
    assert ((OSAbstMod.set O curtid (oscurt t)) = O).
    rewrite OSAbstMod.get_set_same;auto.
    unfold set in *;simpl in *.
    rewrite H4 in *.
    auto.

    destruct Hgoodapicode.
    rewrite <- H5;auto.

    destruct H5.
    mytac.
    unfold get in *;simpl in *.
    rewrite H2 in H5;inverts H5.
    rewrite H3 in H6;inverts H6.
    destruct H7;mytac;tryfalse.
    repeat progress (destruct H5;mytac;tryfalse).
    unfolds.
    intros.
    rewrite OSAbstMod.map_get_set in H7;inverts H7.
    unfolds in H1.
    mytac.

    unfold get in *;unfold set in *;simpl in *.
    unfolds in Hgoodst'.
    lets Hgoodstx: Hgoodst' H5 H6.
    
    rewrite abst_set_get_neq in H5;auto.
    rewrite abst_set_get_neq in H6;auto.
    rewrite H1 in H6;inverts H6.
    destruct Hgoodstx as (Hrdyninwl&Hownerpp&Htaskstp&Hoppprop&Hwaitexowner&Hnoownerp).
    unfolds in Htaskstp.
    assert (exists p st m, TcbMod.get tls t = Some (p,st,m)).
    remember (TcbMod.get tls t) as X;destruct X;tryfalse.
    destruct b.
    destruct p.
    do 3 eexists;eauto.
    mytac.
    lets Htaskstp':Htaskstp H6.

    unfolds in Hnoownerp.
    lets Hx:Hnoownerp H7 H11 H8.
    subst x4.
    
    destruct Htaskstp'.
    subst x7.
    assert (isrdy rdy).
    unfolds.
    auto.
    lets Hx:H17 H12 H6 H18.
    unfolds in Hoppprop.
    lets Hy:Hoppprop H6 H14.
    clear -Hx Hy.
    destruct Hy;int auto.
    mytac;subst.
    unfolds in Hwaitexowner.
    lets Hx:Hwaitexowner H6.
    mytac.
    assert (x7 <> ct).
    intro.
    subst x7.
    destruct H11.
    eexists;eauto.
    assert (isrdy rdy).
    unfolds.
    auto.
    lets Hx:H17 H22 H19 H23.
    lets Hy:H21 H14.
    clear -H20 Hy Hx.
    subst x3.
    int auto.
  -
    destruct Hgoodapicode.
    rewrite <- H1.
    auto.
    unfolds in H1.
    mytac.
    unfold get in *;simpl in *.
    rewrite H1 in H6;inverts H6.
    rewrite H3 in H2;inverts H2.
    destruct H4.
    mytac.
    repeat progress (destruct H2;mytac).
  -
    destruct Hgoodapicode.
    rewrite <- H1.
    auto.
    unfolds in H1.
    mytac.
    unfold get in *;simpl in *.
    rewrite H1 in H6;inverts H6.
    rewrite H3 in H2;inverts H2.
    destruct H4.
    mytac.
    repeat progress (destruct H2;mytac).
  -
    destruct Hgoodapicode.
    rewrite <- H2.
    auto.
    unfolds in H2.
    mytac.
    unfold get in *;simpl in *.
    rewrite H2 in H11;inverts H11.
    rewrite H3 in H1;inverts H1.
    destruct H4.
    mytac.
    repeat progress (destruct H1;mytac).
    Grab Existential Variables.
    trivial.
Qed.

Lemma no_nest_prop_step_hold:
  forall client_code T cst O T' cst' O' ,
    no_nest_client client_code O T cst ->
    hpstep (client_code, os_spec') T cst O T' cst' O' ->
    no_nest_client client_code O' T' cst'.
Proof.
  introv Hn Hp.
  unfolds in Hn.
  unfolds.
  intros.
  eapply Hn.
  constructors; eauto.
Qed.



Lemma hpstep_inv_prop_hold:
  forall client_code T cst O T' cst' O' ,
    goodtasks_h T ->
    hpstep (client_code, os_spec') T cst O T' cst' O' ->
    INV_PROP client_code O T cst ->
    INV_PROP client_code O' T' cst'.
Proof.
  introv Hgoodtasks.
  introv Hp Hinv.
  unfolds in Hinv.
  destruct Hinv as (Hinv1 & Hinv2 & Hinv3).
  splits; auto.
  eapply no_nest_prop_step_hold; eauto.
  lets Hps :  code_exe_prop2 Hinv3 Hp.
  eauto.
  eapply code_exe_prop1; eauto.
  constructors.
  unfolds in Hinv2.
  eapply Hinv2.
  constructors.
  eapply Hps.
  unfolds in Hinv2.
  eapply Hinv2.
  constructors;eauto.
  constructors.
Qed.
   
Lemma hpstep_wpif_hold:
  forall client_code T cst O T' cst' O',
    goodtasks_h T ->
    INV_PROP client_code O T cst ->
    WEAK_PIF O ->
    hpstep (client_code, os_spec') T cst O T' cst' O' ->
    WEAK_PIF O'.
Proof.    
  introv Hgoodtasks Hinv Hw Hsptep.
  unfolds in Hinv.
  destruct Hinv as (Hic & Hn & Hgood).
  unfolds in Hic.
  unfolds in Hn.
  assert (hpstepstar (client_code, os_spec') T cst O T cst O).
  constructors.
  lets Hnest: Hn H.
  lets Hres : no_nest_pif Hnest Hw Hsptep; eauto.
  eapply Hn.
  constructors;eauto.
  constructors.
  eapply code_exe_prop1; eauto.
Qed.  

Lemma hpstep_pif_hold
: forall (client_code : progunit) (T : TasksMod.map) 
         (cst : clientst) (O : osabst) (T' : tasks) 
         (cst' : clientst) (O' : osabst),
    goodtasks_h T ->
    INV_PROP client_code O T cst ->
    PIF O ->
    hpstep (client_code, os_spec') T cst O T' cst' O' -> PIF O'.
Proof.
  intros.
  unfolds.
  intros.
  lets Hx:hpstep_wpif_hold H H0 H2.
  unfolds in H1.
  unfolds.
  intros.
  eapply H1;eauto.
  unfolds in Hx.
  eapply Hx;eauto.
  unfolds in H0.
  mytac.
  unfolds in H13.
  assert (NO_NEST_PENDING_O O').
  unfolds in H14.
  eapply H13;eauto.
  constructors.
  eauto.
  constructors.
  unfolds in H15.
  lets Hy:H15 H3 H4.
  auto.
Qed.

Theorem Priority_Inversion_Free_Prop:
  forall client_code T cst O T' cst' O',
    InitTasks T client_code cst O ->
    INV_PROP client_code O T cst ->
    hpstepstar (client_code, os_spec') T cst O T' cst' O' ->
    PIF O ->
    PIF O'.
Proof.
  introv Hinittasks.
  intros.
  lets hgoodtasks:init_goodks_h Hinittasks H.
  clear Hinittasks.
  inductions H0.
  auto.
  eapply IHhpstepstar;eauto.
  eapply hpstep_inv_prop_hold; eauto.
  eapply hpstep_pif_hold; eauto.
  eapply hpstep_goodcode_h;eauto.
  unfolds in H;mytac;auto.
Qed.

Definition init_st O:=
  exists tls,
    OSAbstMod.get O absecblsid = Some (absecblist EcbMod.emp) /\
    OSAbstMod.get O abstcblsid = Some (abstcblist tls) /\
    forall t, exists p msg, TcbMod.get tls t = Some (p,rdy,msg).

Theorem GOOD_ST_Prop':
  forall client_code T cst O T' cst' O',
    goodtasks_h T ->
    good_client_code client_code ->
    GOOD_ST O->
    good_client_code client_code ->
    no_nest_client client_code O T cst ->
    hpstepstar (client_code, os_spec') T cst O T' cst' O' ->
    GOOD_ST O'.
Proof.
  intros.
  inductions H4;auto.
  eapply IHhpstepstar with (O:=O') (T:=T');eauto.
  2:eapply hpstep_goodcode_h;eauto.
  2:eapply no_nest_prop_step_hold;eauto.
  eapply code_exe_prop2 with (O':=O) (O'':=O');eauto.
  eapply hpstep_goodcode_goodapi;eauto.
  unfolds in H3.
  eapply H3.
  constructors.
  unfolds in H3.
  eapply H3.
  eapply hp_stepS.
  2:constructors.
  eauto.
Qed.

Lemma init_goodks_h':
  forall T client_code cst O,
    InitTasks T client_code cst O ->
    good_client_code client_code ->
    goodtasks_h T .
Proof.
  intros.
  unfolds in H.
  unfolds.
  intros.
  mytac.
  apply H2 in H1.
  mytac.
  unfolds in H0.
  mytac.
  apply H0 in H3.
  clear -H3.
  unfolds.
  unfolds in H3.
  induction x;simpl in *;auto;tryfalse.
  mytac.
  apply IHx1;auto.
  apply IHx2;auto.
  mytac.
  apply IHx1;auto.
  apply IHx2;auto.
Qed.

  
Theorem GOOD_ST_Prop:
  forall client_code T cst O T' cst' O',
    InitTasks T client_code cst O ->
    init_st O ->
    good_client_code client_code ->
    no_nest_client client_code O T cst ->
    hpstepstar (client_code, os_spec') T cst O T' cst' O' ->
    GOOD_ST O'.
Proof.
  intros.
  eapply GOOD_ST_Prop';eauto.
  eapply init_goodks_h';eauto.

  unfolds.
  unfolds in H0.
  mytac.
  intros.
  rewrite H0 in H6.
  inverts H6.
  rewrite H4 in H7;inverts H7.
  splits.
  unfolds.
  splits.
  intros.
  intro.
  unfolds in H7.
  mytac.
  rewrite EcbMod.emp_sem in H7;tryfalse.
  intros.
  lets Hx:H5 t.
  mytac.
  rewrite H6 in H7;inverts H7.
  intros.
  unfolds in H6.
  mytac.
  rewrite EcbMod.emp_sem in H6;tryfalse.
  unfolds.
  intros.
  rewrite EcbMod.emp_sem in H7;tryfalse.
  unfolds.
  intros.
  left.
  lets Hx:H5 t.
  mytac.
  rewrite H6 in H7;inverts H7;auto.
  unfolds.
  intros.
  unfolds in H7.
  right.
  assert (TcbMod.get tls t <> None).
  intro.
  rewrite H6 in H8;inverts H8.
  apply H7 in H8.
  destruct H8.
  mytac.
  unfolds in H8.
  mytac.
  rewrite EcbMod.emp_sem in H8;tryfalse.
  destruct H8.
  mytac.
  rewrite H9 in H6;inverts H6.
  clear.
  int auto.
  unfolds.
  intros.
  lets Hx:H5 t.
  mytac.
  rewrite H7 in H6;inverts H6.
  unfolds.
  intros.
  unfolds in H8.
  assert (TcbMod.get tls t <> None).
  intro.
  rewrite H6 in H9;inverts H9.
  apply H8 in H9.
  destruct H9.
  mytac.
  unfolds in H9.
  mytac.
  rewrite EcbMod.emp_sem in H9;tryfalse.
  destruct H9.
  mytac.
  rewrite H6 in H10;inverts H10;auto.
Qed.


  
Theorem Priority_Inversion_Free_Proof:
  forall client_code T cst O T' cst' O',
    InitTasks T client_code cst O ->
    init_st O ->
    good_client_code client_code ->
    no_nest_client client_code O T cst ->
    hpstepstar (client_code, os_spec') T cst O T' cst' O' ->
    PIF O'.
Proof.
  intros.
  eapply Priority_Inversion_Free_Prop;eauto.
  unfolds;splits;auto.
  unfolds.
  unfolds in H0.
  mytac.
  intros.
  rewrite H0 in H6.
  inverts H6.
  rewrite H4 in H7;inverts H7.
  splits.
  unfolds.
  splits.
  intros.
  intro.
  unfolds in H7.
  mytac.
  rewrite EcbMod.emp_sem in H7;tryfalse.
  intros.
  lets Hx:H5 t.
  mytac.
  rewrite H6 in H7;inverts H7.
  intros.
  unfolds in H6.
  mytac.
  rewrite EcbMod.emp_sem in H6;tryfalse.
  unfolds.
  intros.
  rewrite EcbMod.emp_sem in H7;tryfalse.
  unfolds.
  intros.
  left.
  lets Hx:H5 t.
  mytac.
  rewrite H6 in H7;inverts H7;auto.
  unfolds.
  intros.
  unfolds in H7.
  right.
  assert (TcbMod.get tls t <> None).
  intro.
  rewrite H6 in H8;inverts H8.
  apply H7 in H8.
  destruct H8.
  mytac.
  unfolds in H8.
  mytac.
  rewrite EcbMod.emp_sem in H8;tryfalse.
  destruct H8.
  mytac.
  rewrite H9 in H6;inverts H6.
  clear.
  int auto.
  unfolds.
  intros.
  lets Hx:H5 t.
  mytac.
  rewrite H7 in H6;inverts H6.
  unfolds.
  intros.
  unfolds in H8.
  assert (TcbMod.get tls t <> None).
  intro.
  rewrite H6 in H9;inverts H9.
  apply H8 in H9.
  destruct H9.
  mytac.
  unfolds in H9.
  mytac.
  rewrite EcbMod.emp_sem in H9;tryfalse.
  destruct H9.
  mytac.
  rewrite H6 in H10;inverts H10;auto.

  unfolds.
  intros.
  unfolds in H13.
  mytac.
  unfolds in H0.
  mytac.
  rewrite H0 in H4;inverts H4.
  rewrite EcbMod.emp_sem in H13;tryfalse.
Qed.

Theorem Old_Priority_Inversion_Free_Proof':
  forall client_code T cst O T' cst' O',
    InitTasks T client_code cst O ->
    init_st O ->
    good_client_code client_code ->
    no_nest_client client_code O T cst ->
    hpstepstar (client_code, os_spec') T cst O T' cst' O' ->
    OLD_PIF O'.
Proof.
  intros.
  lets Hx: GOOD_ST_Prop H H0 H1 H2 H3.
  unfolds in Hx.
  unfolds.
  intros.
  unfolds.
  intro.
  lets Hy :Hx H4 H5.
  mytac.
  unfolds in H6.
  unfolds in H11.
  mytac.
  unfolds in H6.
  mytac.
  rewrite H6 in H13;inverts H13.
  lets Hz:H11 H6.
  mytac.
  unfolds in H13.
  mytac.
  rewrite H13 in H16;inverts H16.
  rewrite H14 in H17;inverts H17.
  clear -H15 H18.
  int auto.
Qed.


Definition O_PI_CHAIN tls els :=
  exists t t_owner p p_owner st st_owner msg msg_owner,
    WAIT_CHAIN t t_owner tls els /\
    TcbMod.get tls t = Some (p,st,msg) /\
    TcbMod.get tls t_owner = Some (p_owner,st_owner,msg_owner) /\
    Int.ltu p p_owner = true.

Definition O_PIF_CHAIN tls els := ~ O_PI_CHAIN tls els.

Definition OLD_PIF_CHAIN O:=
  forall els tls,
    OSAbstMod.get O absecblsid = Some (absecblist els) ->
    OSAbstMod.get O abtcblsid = Some (abstcblist tls) ->
    O_PIF_CHAIN tls els.

  
Definition UPIF (O:osabst) :=
  forall els tls ct p_ct,
    OSAbstMod.get O absecblsid = Some (absecblist els) ->
    OSAbstMod.get O abtcblsid = Some (abstcblist tls) ->
    OSAbstMod.get O curtid = Some (oscurt ct) ->
    GET_OP ct tls els p_ct ->
    ~ (exists eid, IS_OWNER ct eid els)  ->
    forall t p_t,
      t <> ct ->
      TcbMod.get tls t <> None ->
      GET_OP t tls els p_t ->
      (exists t', WAIT_CHAIN t t' tls els) ->
      Int.ltu p_ct p_t = true \/ Int.eq p_ct p_t = true.

Theorem Unbounded_Priority_Inversion_Free_Proof:
  forall client_code T cst O T' cst' O',
    InitTasks T client_code cst O ->
    init_st O ->
    good_client_code client_code ->
    no_nest_client client_code O T cst ->
    hpstepstar (client_code, os_spec') T cst O T' cst' O' ->
    PREEMP O' ->
    UPIF O'.
Proof.
  intros.
  rename H4 into Hpreemp.
  unfolds;intros.
  left.
  eapply Priority_Inversion_Free_Proof;eauto.
  assert (GOOD_ST O').
  eapply GOOD_ST_Prop;eauto.
  unfolds in H13.
  lets Hx:H13 H4 H5.
  mytac.
  clear H13.  

  inverts H12.
  destruct H13.
  unfolds in H12.
  mytac.
  unfolds in H14.
  mytac.
  apply H21 in H12.
  unfolds in H12;unfolds.
  mytac;do 4 eexists;eauto.
  unfolds in H13.
  mytac.
  unfolds in H14.
  mytac.
  apply H21 in H12.
  unfolds in H12;unfolds;mytac.
  do 4 eexists;eauto.
Qed.

Theorem Old_Priority_Inversion_Free_Proof:
  forall client_code T cst O T' cst' O',
    InitTasks T client_code cst O ->
    init_st O ->
    good_client_code client_code ->
    no_nest_client client_code O T cst ->
    hpstepstar (client_code, os_spec') T cst O T' cst' O' ->
    OLD_PIF_CHAIN O'.
Proof.
  intros.
  lets Hx: GOOD_ST_Prop H H0 H1 H2 H3.
  lets Hy: Old_Priority_Inversion_Free_Proof' H H0 H1 H2 H3.
  unfolds.
  intros.
  unfolds.
  intro.
  unfolds in Hy.
  lets Hz:Hy H4 H5.
  unfolds in Hz.
  destruct Hz.
  unfolds in H6.
  unfolds.
  mytac.
  exists x x0;do 6 eexists;splits;eauto.
  inverts H6.
  destruct H10;auto.
  unfolds in H10.
  mytac.
  unfolds in H2.
  lets Hw:H2 H3.
  unfolds in Hw.
  lets Hv:Hw H4 H5.
  unfolds in Hv.
  
  inverts H11.
  destruct H12.
  unfolds in H11.
  mytac.
  assert (TcbMod.get tls t' <> None).
  intro.
  rewrite H14 in H11;inverts H11.
  eapply Hv with (qid:=x7) in H14;eauto.
  destruct H14.
  destruct H14.
  unfolds in Hx.

  lets Hu: Hx H4 H5.
  mytac.
  unfolds in H14.
  destructs H14.
  apply H21 in H11.
  unfolds in H11.
  unfolds.
  mytac;do 4 eexists;eauto.
  unfolds.
  do 3 eexists;eauto.
  
  unfolds in H12.
  mytac.
  assert (TcbMod.get tls t' <> None).
  intro.
  rewrite H14 in H11;inverts H11.
  eapply Hv with (qid:=x7) in H14;eauto.
  destruct H14.
  destruct H14.
  unfolds in Hx.

  lets Hu: Hx H4 H5.
  mytac.
  unfolds in H14.
  destructs H14.
  apply H21 in H11.
  unfolds in H11.
  unfolds.
  mytac;do 4 eexists;eauto.
  unfolds.
  do 3 eexists;eauto.
Qed.
