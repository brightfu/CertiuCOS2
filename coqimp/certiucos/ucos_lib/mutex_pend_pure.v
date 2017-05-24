Require Import include_frm.
Require Import math_auto.
Require Import ucos_include.
Require Import os_ucos_h.
Require Import OSTimeDlyPure.
Require Import OSMutex_common.
Require Import sem_common.
Require Import OSQPostPure.
Local Open Scope code_scope.

Open Scope list_scope.

Lemma mutex_pend_join1_auto:
  forall (A B T : Type) (MC : PermMap A B T) tls1 tls2 tls' tls head x2,
    usePerm = false ->
    join tls1 tls2 tls' ->
    join (sig head x2) tls' tls ->
    join (sig head x2) tls1 (set tls1 head x2).
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.

Lemma mutex_pend_join1:
  forall tls1 tls2 tls' tls head x2,
    TcbMod.join tls1 tls2 tls' ->
    TcbMod.join (sig head x2) tls' tls ->
    TcbMod.join (sig head x2) tls1 (set tls1 head x2).
  intros.
  change (join (sig head x2) tls1 (set tls1 head x2)).
  eapply mutex_pend_join1_auto; ica.
Qed.

Lemma mutex_pend_join2_auto:
  forall (A B T : Type) (MC : PermMap A B T) tls1 tls2 tls' tls head x2,
    usePerm = false ->
    join tls1 tls2 tls' ->
    join (sig head x2) tls' tls ->
    join (set tls1 head x2) tls2 tls.
  intros.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.
  
Lemma mutex_pend_join2:
  forall tls1 tls2 tls' tls head x2,
    TcbMod.join tls1 tls2 tls' ->
    TcbMod.join (sig head x2) tls' tls ->
    TcbMod.join (set tls1 head x2) tls2 tls.
  intros.
  change (join (set tls1 head x2) tls2 tls).
  eapply mutex_pend_join2_auto; ica.
Qed.  

Lemma TCBList_P_split_by_tcbls_verbose :
  forall l tls tid htcb s head hprev tail tnext rtbl P,
    TcbMod.get tls tid = Some htcb ->
    TCBList_P head l rtbl tls ->
    s |= tcbdllseg head hprev tail tnext l ** P ->
    exists l1 tcbnode l2 tls1 tls2 tail1,
      s |= tcbdllseg head hprev tail1 (Vptr tid) l1 **
        tcbdllseg (Vptr tid) tail1 tail tnext (tcbnode :: l2) ** P /\
      TCBList_P head l1 rtbl tls1 /\
      TCBList_P (Vptr tid) (tcbnode :: l2) rtbl tls2 /\
      TcbMod.join tls1 tls2 tls /\
      l = l1 ++ (tcbnode :: l2) /\
      get_last_tcb_ptr l1 head = Some (Vptr tid). 
Proof.
  inductions l; intros.
  simpl in H0; substs.
  rewrite TcbMod.emp_sem in H; tryfalse.
  
  simpl in H0.
  mytac.

  assert (Fbeq: tid = x \/ tid <> x) by tauto.
  destruct Fbeq. 
  (** x = tid **)
  subst.
  exists (nil(A:=vallist)) a l TcbMod.emp tls hprev.
  swallow.
  sep cancel 1%nat 2%nat.
  sep cancel P.
  unfold tcbdllseg.
  unfold dllseg.
  sep pauto.

  unfolds.
  unfold empenv.
  simpl.
  auto.

  simpl.
  swallow; eauto.

  apply TcbMod.join_emp.
  auto.

  auto.
  unfold get_last_tcb_ptr.
  auto.
  
  (** x <> tid **)
  unfold tcbdllseg in H1.
  unfold dllseg in H1; fold dllseg in H1.
  sep split in H1.
  sep normal in H1.
  sep destruct H1.
  sep split in H1.
  rewrite H7 in H2.
  inverts H2.
  
  (** prepare using induction hypothesis **)
  rename x into head.
  rename H5 into Hy2.
  rename x0 into head'.
  rename x1 into tls'.
  
  assert (Hy1: TcbMod.get tls' tid = Some htcb).
  {
(* ** ac:     SearchAbout TcbMod.get. *)
    lets Htmp: TcbMod.join_get_or H3 H.
    destruct Htmp.
(* ** ac:     SearchAbout TcbMod.get. *)
(* ** ac:     Check TcbMod.get_sig_none. *)
    assert (Hneq: head <> tid) by auto.
    generalize (@TcbMod.get_sig_none _ _ x2 Hneq); intro.
    unfold sig in H2; simpl in H2.
    rewrite H5 in H2.
    tryfalse.
    auto.
  }

  assert (Hy3: s |= tcbdllseg head' (Vptr head) tail tnext l ** node (Vptr head) a OS_TCB_flag ** P).
  {
    unfold tcbdllseg.
    sep pauto.
  }

  lets Hi: IHl Hy1 Hy2 Hy3.
  (** induction hypo finished **)
  destruct Hi as (l1 & tcbnode & l2 & tls1 & tls2 & tail1 & Hi).
  clear IHl.

  (** using inductino hypo to instant exists variable **)
  exists (a::l1).
  exists (tcbnode).
  exists (l2).
  exists (set tls1 head x2).
  exists (tls2).
  exists tail1.

  clear H1 Hy3.
  heat.
  
  
  swallow.
  (** tcbdllseg **)
  sep pauto.
(* ** ac:   SearchAbout tcbdllseg. *)
  unfold tcbdllseg.
  unfold dllseg.
  fold dllseg.
  unfold tcbdllseg in H1.
  sep pauto.

  (** TCBList_P **)
  simpl.
  swallow; eauto.

  eapply mutex_pend_join1; eauto.

  eauto.


  eapply mutex_pend_join2; eauto.
  eauto.
  eapply get_last_tcb_ptr_prop.
  eauto.
  eauto.
Qed.

Lemma lzh_tcb_list_split:
  forall s P head headpre tail tailnext l tid abstcb tcbls rtbl,
    s |= tcbdllseg head headpre tail tailnext l ** P ->
    TcbMod.get tcbls tid = Some abstcb ->
    TCBList_P head l rtbl tcbls ->
    s |= EX ltcb l1 l2 p p_pre p_next tcbls1 tcbls2' tcbls2,
  [| p = Vptr tid |] **
                     tcbdllseg head headpre p_pre p l1 **
                     node p ltcb OS_TCB_flag **
                     [| V_OSTCBNext ltcb = Some p_next |] **
                     [| get_last_tcb_ptr l1 head = Some p |] **
                     [| V_OSTCBPrev ltcb = Some p_pre |] **
                     tcbdllseg p_next p tail tailnext l2 **
                     [| l = l1 ++ ltcb :: l2 |] **
                     [| TcbMod.join tcbls1 tcbls2' tcbls |] **
                     [| TcbMod.joinsig tid abstcb tcbls2 tcbls2' |] **
                     [| TCBNode_P ltcb rtbl abstcb |] **
                     [| TCBList_P head l1 rtbl tcbls1 |] **
                     [| TCBList_P p_next l2 rtbl tcbls2 |] ** P.
  intros.
  lets F1: TCBList_P_split_by_tcbls_verbose H0 H1 H.
  simpljoin.
  rename H7 into Fzero.
  unfold TCBList_P in H4.
  fold TCBList_P in H4.
  simpljoin.
  inverts H4.
  assert (abstcb = x8).
  {
    unfold TcbJoin in *.
    assert (Htmp: TcbMod.get tcbls x5 = Some x8).
    {
      eapply TcbMod.join_get_get_r.
      eapply H5.
      eapply TcbMod.join_sig_get.
      eauto.
    }
    rewrite Htmp in H0.
    inverts H0.
    auto.
  }
  subst x8.
  sep pauto.
  sep cancel tcbdllseg.
  2: eauto.
  2: eauto.
  2: eauto.
  2: eauto.
  2: eauto.
  3: eauto.
  3: eauto.
  unfold tcbdllseg in *.
  unfold dllseg in H2.
  fold dllseg in H2.
  sep pauto.
  rewrite H6 in H10.
  inverts H10.
  auto.
  {
    unfold tcbdllseg in *.
    unfold dllseg in *.
    fold dllseg in *.
    sep pauto.
  }
Qed.

Lemma mund_int_a1:
  forall i,
    Int.unsigned i <= 65535 ->
    Int.unsigned (i>>ᵢ$ 8) <= 255.
  apply acpt_intlemma10.
Qed.  


Lemma mund_int_a2:
  forall i,
    Int.unsigned i <= 255 ->
    (if Int.unsigned i <=? Byte.max_unsigned then true else false) = true.
  intros.
  apply leb_bytemax_true_intro in H.
  rewrite H.
  auto.
Qed.


Lemma mund_val_inj_a0:
  forall (b:bool),
    val_inj
      (if b
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)) <> Vundef.
  intros; pure_auto.
Qed.


Lemma mund_val_inj_a1:
  forall (b1 b2:bool),
    val_inj
      (bool_or
         (val_inj
            (if b1
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))
         (val_inj
            (if b2
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) <> Vundef.
  intros; pure_auto.
Qed.


Lemma mund_int_ltu_revers:
  forall x y,
    Int.ltu x y = true \/ Int.eq x y = true ->
    Int.ltu y x = false.
  intros.
  destruct H.
  unfold Int.ltu in *.
  destruct (zlt (Int.unsigned x) (Int.unsigned y)).
  destruct (zlt (Int.unsigned y) (Int.unsigned x)).
  omega.
  auto.
  tryfalse.
  lzh_simpl_int_eq.
  subst.
  unfold Int.ltu in *.
  destruct (zlt (Int.unsigned y) (Int.unsigned y)).
  omega.
  auto.
Qed.


Lemma mund_int_a3:
  forall i,
    Int.unsigned i <= 65535 ->
    Int.unsigned (i&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <= 255.
  intros.
  apply postintlemma3.
Qed.


Lemma mund_int_byte_modulus:
  Byte.modulus = 256.
  unfold Byte.modulus.
  unfold Byte.wordsize.
  unfold Wordsize_8.wordsize.
  unfold two_power_nat.
  int auto.
Qed.  


Lemma mund_int_mod:
  forall i,
    Int.unsigned i <= 255 ->
    $ Int.unsigned i mod 256 = i.
  intros.
  rewrite Coqlib.Zmod_small.
  apply Int.repr_unsigned.
  int auto.
Qed.


Lemma lzh_ecb_join_set_one:
  forall ml a b ml1 ml2 ml1' med b',
    RLH_ECBData_P med b' ->
    EcbMod.get ml a = Some b -> 
    EcbMod.joinsig a
                   b ml1' ml1 ->
    EcbMod.join ml2 ml1 ml -> 
    exists ml1n, EcbMod.joinsig a b' ml1' ml1n /\ EcbMod.join ml2 ml1n (EcbMod.set ml a b'). 
Proof.
  intros.
  exists (EcbMod.set ml1 a b').
  split.
  eapply EcbMod.joinsig_set; eauto.
  eapply EcbMod.joinsig_set_set; eauto.
Qed.


Lemma TCBList_get_head:
  forall tcbls tid abstcb vl l rtbl,
    TCBList_P (Vptr tid) (vl :: l) rtbl tcbls ->
    TcbMod.get tcbls tid = Some abstcb ->
    TCBNode_P vl rtbl abstcb.
Proof.
  intros.
  unfolds in H.
  mytac.
  clear H4.
  inverts H.
  unfolds in H2.
  assert (Hget: TcbMod.get tcbls x = Some x2).
  eapply TcbMod.join_get_l.
  eauto.
  go.
  rewrite tidspec.eq_beq_true.
  auto.
  auto.
  rewrite Hget in H0.
  inverts H0.
  auto.
Qed.


Lemma mund_ltu_a1:
  Int.ltu Int.zero Int.zero = false.
  int auto.
Qed.

Lemma mund_ltu_a2:
  Int.ltu Int.zero Int.one = true.
  int auto.
Qed.  


Lemma mund_int_byte_max_unsigned:
  Byte.max_unsigned = 255.
  unfold Byte.max_unsigned.
  rewrite mund_int_byte_modulus.
  simpl.
  auto.
Qed.


Lemma mund_to_nat_a1:
  forall i,
    Int.unsigned i < 64 ->
    (Z.to_nat (Int.unsigned i) < 64)%nat.
  intros.
  apply intlt2nat in H.
  int auto.
Qed.

Lemma mund_nth_val_a1:
  forall i v'32,
    Int.unsigned i < 64 ->
    array_type_vallist_match OS_TCB ∗ v'32 ->
    length v'32 = 64%nat ->
    (exists v, (nth_val' (Z.to_nat (Int.unsigned i)) v'32) = Vptr v) \/
    (nth_val' (Z.to_nat (Int.unsigned i)) v'32) = Vnull.
Proof.
  intros.
  Require Import symbolic_lemmas.
  lets F: array_type_vallist_match_imp_rule_type_val_match H0.
  rewrite H1.
  instantiate (1:=(Z.to_nat (Int.unsigned i))).
  apply mund_to_nat_a1.
  auto.
  lets F': rule_type_val_match_ptr_elim F.
  unfold isptr in F'.
  destruct F'; auto.
Qed.

Lemma mutex_eventtype_neq_mutex:
  forall s P a msgq mq t,
    s |= AEventData a msgq ** P ->
    RLH_ECBData_P msgq mq ->
    V_OSEventType a = Some (Vint32 t) ->
    t <> ($ OS_EVENT_TYPE_MUTEX) ->
    s |= AEventData a msgq **
      [| (~ exists pr owner wls, mq = (absmutexsem pr owner, wls)) |] ** P.
Proof.
  intros.

  unfold AEventData in *.
  destruct msgq eqn:Hmsgq.
  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.
  
  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.

  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.

  sep split in H.
  rewrite H3 in H1.
  inverts H1.
  tryfalse.
Qed.

Lemma mutex_triangle:
  (* 3种表示方式的关系 *)
  forall s P a x y msgq mq,
    s |= AEventData a msgq ** P ->
    RLH_ECBData_P msgq mq ->
    V_OSEventType a = Some (V$OS_EVENT_TYPE_MUTEX) ->
    V_OSEventCnt a = Some x ->
    V_OSEventPtr a = Some y ->
    s |= AEventData a msgq ** 
      [| exists pr own wls, msgq = DMutex x y
                            /\ mq = (absmutexsem pr own, wls)
                            /\ MatchMutexSem x y pr own
                            /\ RH_ECB_P mq|] ** P.
  intros.
  sep pauto.
  unfold AEventData in *.
  destruct msgq eqn:Hmsgq; sep split in H. 
  - rewrite H1 in H5; tryfalse.
  - rewrite H1 in H4; tryfalse.
  - rewrite H1 in H4; tryfalse. 
  - unfold RLH_ECBData_P in H0.
    rewrite H2 in *.
    rewrite H3 in *.
    inverts H5; inverts H6.
    clear H4 H2 H3.
    destruct mq; destruct e eqn:Hmq; tryfalse.
    exists i o w.
    mytac.
    auto.
Qed.  

(* ** ac: Locate "::". *)
Open Scope list_scope.

Lemma TCBList_imp_TCBNode:
  forall v v'52 v'26 x12 x11 i8 i7 i6 i5 i4 i3 i1 v'37 v'38 v'47,
    TCBList_P (Vptr v)
              ((v'52
                  :: v'26
                  :: x12
                  :: x11
                  :: Vint32 i8
                  :: Vint32 i7
                  :: Vint32 i6
                  :: Vint32 i5
                  :: Vint32 i4
                  :: Vint32 i3 :: Vint32 i1 :: nil) :: v'37)
              v'38 v'47 ->
    exists abstcb,
      TCBNode_P 
        (v'52
           :: v'26
           :: x12
           :: x11
           :: Vint32 i8
           :: Vint32 i7
           :: Vint32 i6
           :: Vint32 i5
           :: Vint32 i4 :: Vint32 i3 :: Vint32 i1 :: nil)
        v'38 abstcb /\
      TcbMod.get v'47 v = Some abstcb /\
      exists st, abstcb = (i6, st, x11).
Proof.
  intros.
  unfolds in H.
  simpljoin.
  exists x2.
  fold TCBList_P in H3.
  split.
  auto.
  unfold TCBNode_P in H2.
  destruct x2; destruct p.
  simpljoin.
  inverts H; inverts H2; inverts H4.
  split.
  eapply TcbMod.join_get_l.
  unfold TcbJoin in *.
  eauto.
  eapply TcbMod.get_a_sig_a.
  eapply CltEnvMod.beq_refl.
  exists t.
  auto.
Qed.

Lemma tcbdllflag_hold_node2:
  forall l1 l1' l2 node1 node1' node2 node2',
    eq_dllflag (node1::nil) (node1'::nil) ->
    eq_dllflag (node2::nil) (node2'::nil) ->
    eq_dllflag ((l1 ++ node1 :: l1') ++ (node2 :: l2)) ((l1 ++ node1' :: l1') ++ (node2' :: l2)).
Proof.
  induction l1.
  {
    intros.
    simpl in H.
    simpl.
    mytac.
    swallow; auto.
    eapply tcbdllflag_hold_middle.
    auto.
  }
  {
    intros.
    simpl.
    swallow; auto.
  }
Qed.

Lemma tcbdllflag_hold_node2' :
  forall (l1 l1' l2 : list vallist)
    (node1 node1' node2 node2' : vallist),
    eq_dllflag (node1 :: nil) (node1' :: nil) ->
    eq_dllflag (node2 :: nil) (node2' :: nil) ->
    eq_dllflag (l1 ++ node1 :: l1' ++ node2 :: l2)
               (l1 ++ node1' :: l1' ++ node2' :: l2).
Proof.
  induction l1.
  {
    intros.
    simpl in H.
    simpl.
    mytac.
    swallow; auto.
    eapply tcbdllflag_hold_middle.
    auto.
  }
  {
    intros.
    simpl.
    swallow; auto.
  }
Qed.

Close Scope list_scope.
