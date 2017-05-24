Require Import include_frm.
Require Import os_inv.
Require Import abs_op.
Require Import sep_auto.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import os_code_defs.

Local Open Scope int_scope.
Local Open Scope Z_scope.

(* create *)
Lemma absimp_qcre_err_return :
  forall P i sch, 
    can_change_aop P -> 
    (Int.unsigned i <=? 65535 = true) -> 
    absinfer sch ( <|| qcre (Vint32 i :: nil)||> ** P) ( <|| END  (Some Vnull) ||> ** P).
Proof.
  infer_solver 0%nat.
  (* introv Hc Hi.
   * unfolds qcre.
   * eapply absinfer_trans.
   * eapply absinfer_choice1; eauto.
   * eapply absinfer_prim; eauto.
   * unfolds.
   * intros.
   * sep split in H.
   * simpl in H0.
   * subst.
   * exists O (END Some Vnull).
   * split; try sep auto.
   * eapply hmstep_merge_emp.
   * constructors; eauto.
   * unfolds.
   * eexists.
   * splits; eauto. *)
Qed.

Lemma absimp_qcre_succ_return:
  forall P i qid  qls  tcbls curtid tm sch,
    can_change_aop P ->
    Int.ltu ($ Q_SIZE) i  = false ->
    EcbMod.get qls qid = None ->
    absinfer sch ( <||  qcre (Vint32 i :: nil) ||>
                    **HECBList qls **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
             ( <||  END  (Some (Vptr qid)) ||> **                                                                                                                 
                    HECBList (EcbMod.set qls qid (absmsgq (nil:list val)
                                                          i,
                                                  nil:list tid)) **HTCBList tcbls **  HTime tm **
                    HCurTCB curtid **P).
Proof.
  infer_solver 1%nat.
  (* introv Hc Hi Hjs.
   * unfolds qcre.
   * eapply absinfer_trans.
   * eapply absinfer_choice2.
   * pauto.
   * 2:sep auto.
   * pauto.
   * eapply absinfer_prim; eauto.
   * pauto.
   * pauto.
   * unfolds.
   * intros.
   * exists (OSAbstMod.set O absecblsid (absecblist (EcbMod.set qls qid (absmsgq nil i, nil)))).
   * exists (END Some (Vptr qid)).
   * splits.
   * 2: cancel_absdata; sep auto.
   * sep split in H.
   * simpl in H0.
   * subst gamma.
   * eapply specstep_merge_emp.
   * constructors; eauto.
   * unfolds.
   * eexists.
   * splits; eauto.
   * do 3 eexists; splits; eauto.
   * absdata_solver.
   * eapply get_none_joinisig; eauto.
   * eapply abst_get_set_eqdom.
   * absdata_solver.
   * unfolds; auto.
   * eapply tidsame_set;eauto. *)
Qed.

(* delete  *)

Lemma absinfer_qdel_err1_return :
  forall P sch, 
    can_change_aop P ->
    absinfer sch (<|| qdel (Vnull :: nil) ||> ** P)
             ( <|| END (Some  (V$ OS_ERR_PEVENT_NULL)) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_qdel_err2_return :
  forall x a P  sch, 
    can_change_aop P ->
    ~ (exists x0 y wls, EcbMod.get x a = Some (absmsgq x0 y, wls)) ->
    absinfer sch (<|| qdel (Vptr a :: nil) ||> ** HECBList x ** P)
             ( <|| END (Some  (V$ OS_ERR_PEVENT_NULL)) ||> ** HECBList x ** P).
Proof.
  infer_solver 1%nat.
  (* introv Hc Hnt.
   * unfold qdel.
   * eapply absinfer_trans.
   * eapply absinfer_choice2.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   * eapply absinfer_trans.
   * eapply absinfer_choice1.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   * eapply absinfer_prim; can_change_aop_solver.
   * unfolds.
   * intros.
   * sep split in H.
   * simpl in H0.
   * subst.
   * exists O ( END Some (V$OS_ERR_PEVENT_NULL)).
   * splits.
   * eapply specstep_merge_emp.
   * constructors; eauto.
   * unfolds.
   * eexists; splits; eauto.
   * eexists; splits; eauto.
   * absdata_solver.
   * sep auto. *)
Qed.

Lemma absinfer_qdel_succ_return :
  forall ecbls ecbls' x y a P tid tcbls t sch, 
    can_change_aop P ->
    EcbMod.get ecbls a = Some (absmsgq x y, nil) ->
    EcbMod.join ecbls' (EcbMod.sig a (absmsgq x y, nil)) ecbls -> 
    absinfer sch (<|| qdel (Vptr a :: nil) ||> ** HECBList ecbls **
              HTCBList tcbls ** HTime t **  HCurTCB tid **  P) ( <|| END (Some  (V$NO_ERR)) ||> **
                         HECBList ecbls' ** HTCBList tcbls ** HTime t **  HCurTCB tid  ** P).
Proof.
  infer_solver 4%nat.
  (* introv Hc Hg Hj.
   * unfold qdel.
   * eapply absinfer_trans.
   * eapply absinfer_choice2.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   * eapply absinfer_trans.
   * eapply absinfer_choice2.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   *  eapply absinfer_trans.
   * eapply absinfer_choice2.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   * eapply absinfer_trans.
   * eapply absinfer_choice2.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   * eapply absinfer_prim; can_change_aop_solver.
   * unfolds.
   * intros.
   * sep split in H.
   * simpl in H0.
   * subst.
   * 
   * exists (OSAbstMod.set O absecblsid (absecblist ecbls'))  ( END Some (V$NO_ERR)).
   * splits.
   * eapply specstep_merge_emp.
   * constructors; try absdata_solver.
   * unfolds.
   * eexists.
   * splits; eauto.
   * do 4 eexists; splits; try absdata_solver; eauto.
   * eapply abst_get_set_eqdom.
   * absdata_solver.
   * unfold eqtls; auto.
   * eapply tidsame_set; eauto.
   * apply OSAbstMod.disj_emp_r.
   * cancel_absdata.
   * sep auto. *)
Qed.


Lemma absinfer_qdel_err3_return :
  forall x a P  sch, 
    can_change_aop P ->
    (exists d,
       EcbMod.get x a = Some d /\ ~ (exists x y wls, d = (absmsgq x y, wls))) ->
    absinfer sch (<|| qdel (Vptr a :: nil) ||> ** HECBList x **
                P) ( <|| END (Some  (V$ OS_ERR_EVENT_TYPE)) ||> ** HECBList x ** P).
Proof.
  infer_solver 2%nat.
  (* introv Hc Hnt.
   * unfold qdel.
   * eapply absinfer_trans.
   * eapply absinfer_choice2.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   * eapply absinfer_trans.
   * eapply absinfer_choice2.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   * eapply absinfer_trans.
   * eapply absinfer_choice1.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   * eapply absinfer_prim; can_change_aop_solver.
   * unfolds.
   * intros.
   * sep split in H.
   * simpl in H0.
   * subst.
   * exists O ( END Some (V$OS_ERR_EVENT_TYPE)).
   * splits.
   * eapply specstep_merge_emp.
   * constructors; eauto.
   * unfolds.
   * eexists; splits; eauto.
   * eexists; splits; eauto.
   * absdata_solver.
   * sep auto. *)
Qed.

Lemma absinfer_qdel_err4_return :
  forall x a P  sch, 
    can_change_aop P ->
    (exists  t' tl z y,
       get x a = Some  (absmsgq z y, t' :: tl)) ->
    absinfer sch (<|| qdel (Vptr a :: nil) ||> ** HECBList x **
                P) ( <|| END (Some  (V$ OS_ERR_TASK_WAITING)) ||> ** HECBList x ** P).
Proof.
  intros.
  simpljoin.
  infer_solver 3%nat.
  (* introv Hc Hnt.
   * unfold qdel.
   * eapply absinfer_trans.
   * eapply absinfer_choice2.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   *  eapply absinfer_trans.
   * eapply absinfer_choice2.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   * eapply absinfer_trans.
   * eapply absinfer_choice2.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   * eapply absinfer_trans.
   * eapply absinfer_choice1.
   * 3: sep auto.
   * can_change_aop_solver.
   * can_change_aop_solver.
   * eapply absinfer_prim; can_change_aop_solver.
   * unfolds.
   * intros.
   * sep split in H.
   * simpl in H0.
   * subst.
   * exists O ( END Some (V$OS_ERR_TASK_WAITING)).
   * splits.
   * eapply specstep_merge_emp.
   * constructors; eauto.
   * unfolds.
   * eexists; splits; eauto.
   * mytac.
   * do 5  eexists; splits; eauto;  try absdata_solver.
   * sep auto. *)
Qed.


(* acc *)

Lemma qacc_absinfer_no_msg:
  forall P mqls x qmaxlen wl sch, 
    can_change_aop P ->  
    EcbMod.get mqls x = Some (absmsgq nil qmaxlen,wl) -> 
    absinfer sch
      (<|| qacc (Vptr x :: nil) ||>  ** HECBList mqls ** P) 
      (<|| END Some Vnull ||>  ** HECBList mqls ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma qacc_absinfer_get_msg:
  forall P mqls x qmaxlen wl v vl v1 v3 v4  sch, 
    can_change_aop P ->  
    EcbMod.get mqls x = Some (absmsgq (v::vl) qmaxlen,wl) -> 
    absinfer sch
      (<|| qacc (Vptr x :: nil) ||>  ** 
           HECBList mqls **  HTCBList v1 ** HTime v3 ** HCurTCB v4 ** P) 
      (<|| END Some v ||>  ** HECBList (EcbMod.set mqls x (absmsgq vl qmaxlen,wl)) **  HTCBList v1 ** HTime v3 ** HCurTCB v4 ** P).
Proof.
  infer_solver 3%nat.
Qed.

Lemma qacc_absinfer_null:
    forall P sch, can_change_aop P ->
              absinfer sch (<|| qacc (Vnull :: nil) ||>  ** P) (<|| END (Some Vnull) ||> ** P).
  Proof.
    infer_solver 0%nat.
    (* intros.
     * unfold qacc.
     * eapply absinfer_trans; auto.
     * eapply absinfer_choice1; eauto.
     * eapply absinfer_prim; auto.
     * 
     * unfolds; intros.
     * destruct s as [[[[]]]].
     * simpl in H0; mytac.
     * exists O (END Some Vnull).
     * split.
     * eapply hmstep_merge_emp.
     * constructors.
     * unfolds; auto.
     * apply eqdomO_same.
     * apply eqtid_same.
     * unfolds; intros; rewrite OSAbstMod.emp_sem.
     * destruct(OSAbstMod.get O a); auto.
     * 
     * sep auto. *)
  Qed.

  Lemma qacc_absinfer_no_q :
    forall P mqls x sch,
      can_change_aop P ->
      (~ exists a b wl,EcbMod.get mqls x = Some (absmsgq a b,wl)) ->
      absinfer sch (<|| qacc (Vptr x :: nil) ||> ** HECBList mqls ** P)
               (<|| END Some Vnull ||> ** HECBList mqls ** P).
  Proof.
    infer_solver 1%nat.
    (* intros.
     * unfold qacc.
     * eapply absinfer_trans.
     * eapply absinfer_choice2 with (q:=(HECBList mqls ** P)); can_change_aop_solver.
     * eapply absinfer_trans.
     * eapply absinfer_choice1 with (q:=(HECBList mqls ** P)); can_change_aop_solver.
     * 
     * eapply absinfer_prim; can_change_aop_solver.
     * unfolds; intros.
     * destruct s as [[[[]]]].
     * eexists O, (END Some Vnull).
     * split.
     * simpl in H1; mytac.
     * eapply hmstep_merge_emp.
     * constructors.
     * unfolds.
     * exists x.
     * split; auto.
     * exists mqls.
     * repeat (split;auto).
     *   Ltac join_get_solver :=
     * match goal with 
     *   | H: OSAbstMod.join (OSAbstMod.sig ?x ?y) _ ?O |- OSAbstMod.get ?O ?x = Some ?y =>
     *     eapply OSAbstMod.join_get_get_l; eauto
     *   | H: OSAbstMod.join ?O1 ?O2 ?O |- OSAbstMod.get ?O ?x = Some ?y =>
     *     eapply OSAbstMod.join_get_get_r; [eauto | join_get_solver]
     * end. 
     * join_get_solver.
     * apply eqdomO_same.
     * apply eqtid_same.
     * unfolds; intros; rewrite OSAbstMod.emp_sem.
     * destruct(OSAbstMod.get O a); auto.
     * 
     * sep auto. *)
  Qed.
 
  (* pend *)


  
Lemma qpend_absinfer_null:
  forall P vl sch, 
    can_change_aop P -> 
    (*tl_vl_match tl vl = true -> *)
    absinfer sch
     ( <|| qpend  (Vnull :: vl) ||>  **
     P) (<|| END (Some (V$OS_ERR_PEVENT_NULL)) ||>  **
     P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma qpend_absinfer_no_q:
  forall P mqls x v sch,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->  
    (~ exists a b wl,EcbMod.get mqls x = Some (absmsgq a b,wl)) -> 
    absinfer sch
      ( <|| qpend (Vptr x :: Vint32 v :: nil) ||>  ** 
            HECBList mqls ** P) 
      (<|| END (Some (Vint32 (Int.repr MSGQ_NULL_ERR))) ||>  ** HECBList mqls ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma qpend_absinfer_get:
  forall P mqls x v msg ml p m t ct tls n wl sch,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    EcbMod.get mqls x = Some (absmsgq (msg::ml) n, wl) ->
    TcbMod.get tls ct = Some (p,rdy,m) ->
    absinfer sch
      ( <|| qpend (Vptr x :: Vint32 v :: nil) ||>  ** 
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<|| END (Some (Vint32 (Int.repr NO_ERR))) ||>  ** HECBList (EcbMod.set mqls x (absmsgq ml n,wl)) ** HTCBList (TcbMod.set tls ct (p,rdy, msg) ) ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 2%nat.
Qed. 

Lemma qpend_absinfer_block:
  forall P mqls qid v wl p m t ct tls n sch,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    EcbMod.get mqls qid = Some (absmsgq nil n, wl) ->
    TcbMod.get tls ct = Some (p,rdy,m) ->
    absinfer sch
      ( <|| qpend (Vptr qid :: Vint32 v :: nil) ||>  ** 
            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<|| isched ;; (qpend_to (|Vptr qid :: Vint32 v :: nil|) ?? qpend_block_get (|Vptr qid :: Vint32 v :: nil|)) ||>  ** HECBList (EcbMod.set mqls qid (absmsgq nil n,ct::wl)) ** HTCBList (TcbMod.set tls ct (p,wait (os_stat_q qid) v, Vnull) ) ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 4%nat.
Qed.

Lemma qpend_absinfer_to:
  forall P mqls qid v t ct tls st prio sch,
    Int.unsigned v <= 65535 ->
    TcbMod.get tls ct = Some (prio, st, Vnull) ->
    can_change_aop P ->
    absinfer sch
      ( <||   (qpend_to (|Vptr qid :: Vint32 v :: nil|) ?? qpend_block_get (|Vptr qid :: Vint32 v :: nil|)) ||>  ** 
             HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<||  END (Some (Vint32 (Int.repr TIME_OUT)))||>  ** HECBList mqls  ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma qpend_absinfer_block_get:
  forall P mqls qid v p t ct tls m st sch,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    TcbMod.get tls ct = Some (p,st,m) ->
    m<>Vnull ->
    absinfer sch
      ( <||  (qpend_to (|Vptr qid :: Vint32 v :: nil|) ?? qpend_block_get (|Vptr qid :: Vint32 v :: nil|)) ||>  ** 
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<||  END (Some (Vint32 (Int.repr NO_ERR)))||>  ** HECBList mqls  ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma OSQPend_high_step_null :
  forall qid timeout P sch,
     qid = Vnull ->
     Int.unsigned timeout <= 65535 ->
     can_change_aop P ->
     absinfer sch ( <|| qpend (qid :: Vint32 timeout :: nil) ||>  ** P)
              ( <|| END Some (V$OS_ERR_PEVENT_NULL) ||>  ** P).
Proof.
  intros.
  subst qid.
  infer_solver 0%nat.
Qed.


Lemma OSQPend_high_step_to :
   forall P mqls qid v t ct tls st prio sch,
    Int.unsigned v <= 65535 ->
    TcbMod.get tls ct = Some (prio, st, Vnull) ->
    can_change_aop P ->
    absinfer sch
      ( <||  (qpend_to (|Vptr qid :: Vint32 v :: nil|) ?? qpend_block_get (|Vptr qid :: Vint32 v :: nil|)) ||>  ** 
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<||  END (Some (Vint32 (Int.repr TIME_OUT)))||>  ** HECBList mqls  ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 0%nat.
Qed.


Lemma OSQPend_high_step_block_get :
  forall P mqls qid v p t ct tls m st sch,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    TcbMod.get tls ct = Some (p,st,m) ->
    m<>Vnull ->
    absinfer sch
      ( <||  (qpend_to (|Vptr qid :: Vint32 v :: nil|) ?? qpend_block_get (|Vptr qid :: Vint32 v :: nil|)) ||>  ** 
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<|| END (Some (Vint32 (Int.repr NO_ERR)))||>  ** HECBList mqls  ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 1%nat.
Qed.



Lemma OSQPend_high_step_get_succ :
  forall qid timeout msg ml n wl ecbls tls t tcur prio  m P sch,
     Int.unsigned timeout <= 65535 ->
     EcbMod.get ecbls qid = Some (absmsgq (msg :: ml) n, wl) ->
     TcbMod.get tls tcur = Some (prio, rdy, m)->
     can_change_aop P ->
     absinfer sch  ( <|| qpend (Vptr qid :: Vint32 timeout :: nil) ||> ** 
                                HECBList ecbls ** HTCBList tls ** HTime t ** HCurTCB tcur ** P)
             (<|| END (Some (V$NO_ERR)) ||>  ** 
                                Aabsdata absecblsid (absecblist (EcbMod.set ecbls qid (absmsgq ml n, wl))) **
                                Aabsdata abtcblsid (abstcblist (TcbMod.set tls tcur (prio, rdy, msg))) ** 
                                HTime t ** HCurTCB tcur ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma qpend_absinfer_idle :
  forall P ecbls tcbls t ct st msg v x sch,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls ct = Some (Int.repr OS_IDLE_PRIO, st, msg) ->
    can_change_aop P ->
    absinfer sch (<|| qpend (Vptr x :: Vint32 v :: nil) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P)
           (<|| END (Some (Vint32 (Int.repr MSGQ_NULL_ERR)))||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 3%nat.
Qed.


Lemma OSQPend_high_step_block :
  forall qid timeout wl n ecbls tls t tcur prio m P sch,
     Int.unsigned timeout <= 65535 ->
     EcbMod.get ecbls qid = Some (absmsgq nil n, wl) ->
     TcbMod.get tls tcur = Some (prio, rdy, m)->
     can_change_aop P ->
     absinfer sch  ( <|| qpend (Vptr qid :: Vint32 timeout :: nil) ||> ** 
                                HECBList ecbls ** HTCBList tls ** HTime t ** HCurTCB tcur ** P)
             (<|| isched ;; (qpend_to (|Vptr qid :: Vint32 timeout :: nil|) ?? qpend_block_get (|Vptr qid :: Vint32 timeout :: nil|)) ||>  ** 
                                Aabsdata absecblsid (absecblist (EcbMod.set ecbls qid (absmsgq nil n, tcur::wl))) **
                                Aabsdata abtcblsid (abstcblist (TcbMod.set tls tcur (prio, wait (os_stat_q qid) timeout, Vnull))) ** 
                                HTime t ** HCurTCB tcur ** P).
Proof.
  infer_solver 4%nat.
Qed.

Lemma qpend_absimp_stat_err :
  forall P ecbls tcbls t ct st msg v x prio sch,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls ct = Some (prio, st, msg) ->
    ~ st = rdy ->
    can_change_aop P ->
    absinfer sch (<|| qpend (Vptr x :: Vint32 v :: nil) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P)
           (<|| END (Some (Vint32 (Int.repr MSGQ_NULL_ERR)))||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 5%nat.
Qed.


(* post *)

Lemma qpost_absinfer_null:
  forall P (*tl*) vl sch, 
    can_change_aop P -> 
(*    tl_vl_match tl vl = true -> *)
    absinfer sch
     ( <|| qpost (Vnull :: vl) ||>  **
     P) (<|| END Some (V$OS_ERR_PEVENT_NULL) ||>  **
     P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma qpost_absinfer_msg_null:
  forall P v sch, 
    can_change_aop P -> 
    (*type_val_match (Tptr OS_EVENT) v = true ->*)
    absinfer sch
     ( <|| qpost (v :: Vnull ::nil) ||>  **
     P) (<|| END Some (Vint32 (Int.repr  OS_ERR_POST_NULL_PTR)) ||>  **
     P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma qpost_absinfer_no_q:
  forall P mqls x v sch, 
    can_change_aop P ->  
    (*type_val_match (Tptr Tvoid) v = true ->*)
    (~ exists a b wl,EcbMod.get mqls x = Some (absmsgq a b,wl)) -> 
    absinfer sch
      ( <|| qpost (Vptr x :: v :: nil) ||>  ** 
            HECBList mqls ** P) 
      (<|| END Some (Vint32 (Int.repr MSGQ_NULL_ERR)) ||>  ** HECBList mqls ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma qpost_absinfer_ovf:
  forall P mqls x v a b wl sch, 
    can_change_aop P ->  
    (*type_val_match (Tptr Tvoid) v = true -> *)
    EcbMod.get mqls x = Some (absmsgq a b,wl) ->
    Z.ge (Z_of_nat (length a)) (Int.unsigned b) ->
    absinfer sch
      ( <|| qpost (Vptr x :: v :: nil) ||>  ** 
            HECBList mqls ** P) 
      (<|| END Some (Vint32 (Int.repr MSGQ_OVF_ERR)) ||>  ** HECBList mqls ** P).
Proof.
  infer_solver 3%nat.
Qed.


Lemma qpost_absinfer_nowt_succ: 
  forall P mqls x v a b tcbls t ct sch, 
    can_change_aop P ->  
    (*type_val_match (Tptr Tvoid) v = true ->*)
    EcbMod.get mqls x = Some (absmsgq a b,nil) ->
    Z.lt (Z_of_nat (length a)) (Int.unsigned b) ->
    absinfer sch
      ( <|| qpost (Vptr x :: v :: nil) ||>  ** 
            HECBList mqls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P) 
      (<||  END Some (Vint32 (Int.repr NO_ERR)) ||>  ** HECBList (EcbMod.set mqls x (absmsgq (a++(v::nil)) b,nil))** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 4%nat.
Qed.
  
Lemma qpost_absinfer_exwt_succ: 
  forall P mqls x v n wl tls t ct p st m t' vl sch, 
    can_change_aop P ->  
    (*type_val_match (Tptr Tvoid) v = true ->*)
    get mqls x = Some (absmsgq vl n,wl) ->
    ~ wl=nil ->
    GetHWait tls wl t' ->
    get tls t' = Some (p,st,m) ->
    absinfer sch
      ( <|| qpost (Vptr x :: v :: nil) ||>  ** 
            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<|| isched ;; END Some (Vint32 (Int.repr NO_ERR)) ||>  ** HECBList (EcbMod.set mqls x (absmsgq nil n,(remove_tid t' wl))) ** HTCBList (TcbMod.set tls t' (p,rdy ,v) ) ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 5%nat.
Qed.


Lemma OSQGetMsg_high_level_step : forall P prio state msg hecbls htcbls htime hcurtcb sd,
  TcbMod.get htcbls hcurtcb = Some (prio, state, msg) ->
  can_change_aop P ->
  absinfer sd
     (<|| getmsg nil ||>  **
      HECBList hecbls **
      HTCBList htcbls **
      HTime htime ** HCurTCB hcurtcb ** P)
     ( <|| END (Some msg) ||>  **
      HECBList hecbls **
      HTCBList (TcbMod.set htcbls hcurtcb (prio, state, Vnull))
      ** HTime htime ** HCurTCB hcurtcb ** P).
Proof.
  infer_solver 0%nat.
Qed.
