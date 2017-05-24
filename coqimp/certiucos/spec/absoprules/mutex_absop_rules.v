Require Import include_frm.
Require Import os_inv.
Require Import abs_op.
Require Import sep_auto.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import os_code_defs.


Local Open Scope int_scope.
Local Open Scope Z_scope.
(* pend *)

Lemma absinfer_mutex_pend_null_return:
   forall P x sch, 
    can_change_aop P ->
    tl_vl_match  (Tint16 :: nil) x = true ->
    absinfer sch
      (<|| mutexpend (Vnull :: x) ||> ** P)
      (<|| END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_mbox_pend_p_not_legal_return :
  forall x a P b v'33 v'16 v'35 sch, 
    can_change_aop P ->
    Int.unsigned b<=65535 ->
    EcbMod.get x a = None ->
    absinfer sch
      (<|| mutexpend (Vptr a ::Vint32 b:: nil) ||> **
           HECBList x **
           HTCBList v'33 **
           HTime v'16 **
           HCurTCB v'35 ** P)
      (<|| END (Some  (V$ OS_ERR_PEVENT_NO_EX)) ||> **
           HECBList x **
           HTCBList v'33 **
           HTime v'16 **
           HCurTCB v'35 ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma absinfer_mutex_pend_wrong_type_return :
  forall x a b P v'33 v'16 v'35 sch, 
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists d,
       EcbMod.get x a = Some d /\ ~ (exists x y wls, d = (absmutexsem x y, wls))) ->
    absinfer sch
      (<|| mutexpend (Vptr a :: Vint32 b :: nil) ||> **
           HECBList x **
           HTCBList v'33 **
           HTime v'16 **
           HCurTCB v'35 ** P)
      (<|| END (Some  (V$ OS_ERR_EVENT_TYPE)) ||> **
           HECBList x **
           HTCBList v'33 **
           HTime v'16 **
           HCurTCB v'35 ** P).
Proof.
  infer_solver 2%nat.
Qed.  

Lemma absinfer_mutex_pend_from_idle_return :
  forall x a b P y t ct sch, 
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists st msg, get y ct = Some (Int.repr OS_IDLE_PRIO, st, msg)) ->
    absinfer sch
      (<|| mutexpend (Vptr a :: Vint32 b :: nil) ||> **
           HECBList x **
           HTCBList y **
           HTime t **
           HCurTCB ct ** P)
      ( <|| END (Some  (V$ OS_ERR_IDLE)) ||> **
            HECBList x **
            HTCBList y **
            HTime t **
            HCurTCB ct ** P).
Proof.
  intros.
  simpljoin.
  infer_solver 3%nat.
Qed.  

Lemma absinfer_mutex_pend_not_ready_return :
  forall P ecbls tcbls t ct st msg v x prio sch,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls ct = Some (prio, st, msg) ->
    ~ st = rdy ->
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr x :: Vint32 v :: nil) ||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P)
      (<|| END (Some (Vint32 (Int.repr OS_ERR_STAT)))||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P).
Proof.
  infer_solver 4%nat.
Qed.  

Lemma absinfer_mutex_pend_cur_prio_higher:
  forall P ecbls tcbls t ct v prio st msg pr owner wls eid sch,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls ct = Some (prio, st, msg) ->
    EcbMod.get ecbls eid = Some (absmutexsem pr owner, wls) ->
    Int.ltu pr prio = false ->
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr eid :: Vint32 v :: nil) ||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P)
      (<|| END (Some (Vint32 (Int.repr OS_ERR_MUTEX_PRIO)))||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P).
  infer_solver 5%nat.
(*  repeat tri_exists_and_solver1. *)
Qed.


Lemma absinfer_mutex_pend_available_return:
  forall P v sid prio m pr els tls t ct sch,
    can_change_aop P ->
    Int.unsigned v <= 65535 ->
    TcbMod.get tls ct = Some (prio, rdy, m) ->
    EcbMod.get els sid = Some (absmutexsem pr None, nil) ->
    Int.ltu pr prio = true ->
    absinfer sch
      ( <|| mutexpend (Vptr sid :: Vint32 v :: nil) ||> **
        HECBList els **
        HTCBList tls **
        HTime t **
        HCurTCB ct ** P)
      ( <|| END (Some (Vint32 (Int.repr NO_ERR))) ||> **
        HECBList (EcbMod.set els sid (absmutexsem pr (Some (ct, prio)), nil)) **
        HTCBList tls **
        HTime t **
        HCurTCB ct ** P).
  infer_solver 6%nat.
Qed.

(** this is 7%nat **)
Lemma absinfer_mutex_pend_lift_is_rdy_block:
  forall P mqls qid v wl p m t ct tls tid opr pr m' p' sch,
    ct <>tid ->
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    EcbMod.get mqls qid = Some (absmutexsem pr (Some (tid, p')), wl) ->
    TcbMod.get tls ct = Some (p, rdy, m) ->
    TcbMod.get tls tid = Some (opr, rdy, m') ->
    Int.eq opr pr = false ->
    Int.ltu p p' = true ->
    Int.ltu pr p = true ->
    absinfer sch
      ( <|| mutexpend (Vptr qid :: Vint32 v :: nil) ||>  ** 
           HECBList mqls **
           HTCBList tls **
           HTime t **
           HCurTCB ct ** P) 
      (<|| isched;;
           (mutexpend_to (|Vptr qid :: Vint32 v :: nil|) ??
            mutexpend_block_get (|Vptr qid :: Vint32 v :: nil|)) ||> **
           HECBList ( EcbMod.set mqls qid (absmutexsem pr (Some (tid, p')), ct :: wl) ) **
           HTCBList (TcbMod.set
                       (TcbMod.set tls
                          ct (p,wait (os_stat_mutexsem qid) v, m))
                       tid (pr, rdy, m')) **
           HTime t **
           HCurTCB ct ** P).
Proof.
  intros.
  unfold mutexpend.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice1.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  2:eapply absinfer_seq_end.
  4:intros;eauto.
  2:simpl;splits;auto.
  2:simpl;splits;auto.
  eapply absinfer_seq.
  simpl;splits;auto.
  simpl;splits;auto.
  subst.
  eapply absinfer_trans.
  apply absinfer_choice1.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.

  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H8.
  subst.
  rewrite H3 in H4.
  inverts H4.
  tryfalse.

  infer_solver 0%nat.
  (* ** ac: SearchAbout (get (set _ _ _) _). *)
  rewrite map_get_set'.
  eauto.
  auto.
Qed.

Lemma mutexpend_block_no_lift_step:
  forall P els tls tm ct i eid els' tls' t' pt m m' px p' wl p sch,
    can_change_aop P ->
    EcbMod.get els eid = Some (absmutexsem p (Some (t', p')), wl) ->
    TcbMod.get tls ct = Some (pt, rdy, m) ->
    TcbMod.get tls t' = Some (px, rdy, m') ->
    (Int.eq px p <> false \/ Int.ltu p' pt = true) ->
    els' = EcbMod.set els eid (absmutexsem p (Some (t', p')), ct :: wl) ->
    tls' = TcbMod.set tls ct (pt, wait (os_stat_mutexsem eid) i, Vnull) ->
    Int.ltu p pt = true ->
    absinfer sch
             (<|| mutexpend (Vptr eid :: Vint32 i :: nil) ||> **
                  HECBList els **
                  HTCBList tls **
                  HTime tm **
                  HCurTCB ct ** P) 
             (<|| isched;;(mutexpend_to (| Vptr eid :: Vint32 i :: nil |) ?? mutexpend_block_get (|Vptr eid :: Vint32 i :: nil|)) ||> **
                  HECBList els' **
                  HTCBList tls' **
                  HTime tm **
                  HCurTCB ct ** P).
Proof.
  intros.
  unfold mutexpend.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice2.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  apply absinfer_choice1.
  simpl;splits;auto.
  2:intros;eauto.
  simpl;splits;auto.
  eapply absinfer_trans.
  2:eapply absinfer_seq_end.
  4:intros;eauto.
  2:simpl;splits;auto.
  2:simpl;splits;auto.
  eapply absinfer_seq.
  simpl;splits;auto.
  simpl;splits;auto.
  subst.
  infer_solver 1%nat.
Qed.


Lemma mutexpend_block_timeout_step:
  forall P els tls tm ct i eid st pt sch,
     can_change_aop P ->
    TcbMod.get tls ct = Some (pt, st, Vnull) ->
    absinfer sch
             (<||
                mutexpend_to (|Vptr eid :: Vint32 i :: nil|)
                ?? mutexpend_block_get
                (|Vptr eid :: Vint32 i :: nil|) ||> **
                HECBList els **
                HTCBList tls **
                HTime tm **
                HCurTCB ct ** P) 
             (<|| END (Some (Vint32 (Int.repr TIME_OUT))) ||> **
                  HECBList els **
                  HTCBList tls **
                  HTime tm **
                  HCurTCB ct ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexpend_block_get_step:
  forall P els tls tm ct i eid st pt m sch,
     can_change_aop P ->
    TcbMod.get tls ct = Some (pt, st, m) ->
    m <> Vnull ->
    absinfer sch
             (<||
                mutexpend_to (|Vptr eid :: Vint32 i :: nil|)
                ?? mutexpend_block_get
                (|Vptr eid :: Vint32 i :: nil|) ||> **
                HECBList els **
                HTCBList tls **
                HTime tm **
                HCurTCB ct ** P) 
             (<|| END (Some (Vint32 (Int.repr OS_NO_ERR))) ||> **
                  HECBList els **
                  HTCBList tls **
                  HTime tm **
                  HCurTCB ct ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma absinfer_mutex_pend_pip_is_not_hold:
  forall P ecbls tcbls t ct v eid sch,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr eid :: Vint32 v :: nil) ||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P)
      (<|| END (Some (Vint32 (Int.repr OS_ERR_MUTEXPR_NOT_HOLDER)))||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P).
  infer_solver 8%nat.
Qed.

Lemma absinfer_mutex_pend_ptcb_is_not_rdy:
  forall P ecbls tcbls t ct v pr wls eid p' ptcb st msg ptcb_prio cur_prio m sch,
    Int.unsigned v <= 65535 ->
    EcbMod.get ecbls eid = Some (absmutexsem pr (Some (ptcb, p')), wls) ->
    TcbMod.get tcbls ptcb = Some (ptcb_prio ,st,msg) ->
    TcbMod.get tcbls ct = Some (cur_prio,rdy,m) ->
    ~ st = rdy -> 
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr eid :: Vint32 v :: nil) ||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P)
      (<|| END (Some (Vint32 (Int.repr OS_ERR_NEST)))||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P).
  infer_solver 9%nat.
Qed.

Lemma absinfer_mutex_pend_ptcb_is_cur:
  forall P ecbls tcbls t ct v pr wls eid p' ptcb sch,
    Int.unsigned v <= 65535 ->
    EcbMod.get ecbls eid = Some (absmutexsem pr (Some (ptcb, p')), wls) ->
    ptcb = ct ->                                                                   
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr eid :: Vint32 v :: nil) ||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P)
      (<|| END (Some (Vint32 (Int.repr OS_ERR_MUTEX_DEADLOCK)))||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P).
  infer_solver 10%nat.
Qed.

Lemma absinfer_mutex_pend_msg_not_null_return :
  forall P ecbls tcbls t ct st msg v x prio sch,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls ct = Some (prio, st, msg) ->
    ~ msg = Vnull ->
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr x :: Vint32 v :: nil) ||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P)
      (<|| END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P).
Proof.
  infer_solver 11%nat.
Qed.  

Lemma absinfer_mutex_pend_cur_prio_eql_mprio:
  forall P ecbls tcbls t ct v pr wls eid p' ptcb st msg cur_prio sch,
    Int.unsigned v <= 65535 ->
    EcbMod.get ecbls eid = Some (absmutexsem pr (Some (ptcb, p')), wls) ->
    TcbMod.get tcbls ct = Some (cur_prio ,st,msg) ->
    p' = cur_prio -> 
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr eid :: Vint32 v :: nil) ||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P)
      (<|| END (Some (Vint32 (Int.repr OS_ERR_MUTEX_DEADLOCK)))||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P).
  infer_solver 12%nat.
Qed.

Lemma absinfer_mutex_pend_ptcb_is_idle:
  forall P ecbls tcbls t ct v pr wls eid p' ptcb st msg sch,
    Int.unsigned v <= 65535 ->
    EcbMod.get ecbls eid = Some (absmutexsem pr (Some (ptcb, p')), wls) ->
    TcbMod.get tcbls ptcb = Some (Int.repr OS_IDLE_PRIO,st,msg) ->
    can_change_aop P ->
    absinfer sch
      (<|| mutexpend (Vptr eid :: Vint32 v :: nil) ||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P)
      (<|| END (Some (Vint32 (Int.repr OS_ERR_MUTEX_IDLE)))||> **
           HECBList ecbls **
           HTCBList tcbls **
           HTime t **
           HCurTCB ct ** P).
  infer_solver 13%nat.
Qed.


(* post *)

Lemma absinfer_mutex_post_null_return : forall P sch, 
                                          can_change_aop P ->
                                          absinfer sch (<|| mutexpost (Vnull :: nil) ||> ** P) ( <|| END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_mutex_post_p_not_legal_return : forall x a P tcbls t ct sch, 
                                                 can_change_aop P ->
                                                 EcbMod.get x a = None ->
                                                 absinfer sch (<|| mutexpost (Vptr a :: nil) ||> ** HECBList x** HTCBList tcbls ** HTime t ** HCurTCB ct  **
                                                               P) ( <|| END (Some  (V$ OS_ERR_PEVENT_NO_EX)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct  ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma absinfer_mutex_post_wrong_type_return : forall x a P tcbls t ct sch, 
                                                can_change_aop P ->
                                                (exists d,
                                                   EcbMod.get x a = Some d /\ ~ (exists x y wls, d = (absmutexsem x y, wls))) ->
                                                absinfer sch (<|| mutexpost (Vptr a :: nil) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct **
                                                              P) ( <|| END (Some  (V$OS_ERR_EVENT_TYPE)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma absinfer_mutex_post_no_owner_return : forall x a P tcbls t ct y y0 wl sch, 
                                              can_change_aop P ->
                                              EcbMod.get x a = Some (absmutexsem y0 y, wl) ->
                                              (~ exists p, y =Some  (ct,p))  ->
                                              absinfer sch (<|| mutexpost (Vptr a :: nil) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct **
                                                            P) ( <|| END (Some  (V$OS_ERR_NOT_MUTEX_OWNER)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 3%nat.
Qed.

Lemma absinfer_mutexpost_return_nowt_succ: 
  forall P mqls x tls t ct st m pr op sch, 
    can_change_aop P ->  
    EcbMod.get mqls x = Some (absmutexsem pr (Some (ct, op)) ,nil) ->
    TcbMod.get tls ct= Some (pr,  st,  m)  ->
    Int.eq pr op = false -> 
    absinfer sch
      ( <|| mutexpost (Vptr x :: nil) ||>  ** 
            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<|| END (Some (Vint32 (Int.repr NO_ERR))) ||>  ** HECBList (EcbMod.set mqls x (absmutexsem pr None, nil)) ** HTCBList (TcbMod.set tls ct (op, st, m))  ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  infer_solver 4%nat.
Qed.

Lemma absinfer_mutexpost_nowt_no_return_prio_succ :
  forall qls qls' qid p p' p'' t tm tls st m P sch,
    can_change_aop P -> 
    EcbMod.get qls qid = Some (absmutexsem p (Some (t, p')), nil) ->
    TcbMod.get tls t = Some (p'', st, m) ->
    Int.eq p'' p = false ->
    qls' = EcbMod.set qls qid (absmutexsem p None, nil) ->
    absinfer sch
      (<|| mutexpost (Vptr qid :: nil) ||> **
           HECBList qls ** HTCBList tls ** HTime tm ** HCurTCB t ** P)
      (<|| END Some (V$NO_ERR) ||> **
           HECBList qls' ** HTCBList tls ** HTime tm ** HCurTCB t ** P).
Proof.
  intros.
  substs.
  infer_solver 5%nat.
Qed.

Require Import join_lib.
Lemma indom_eq:
  forall {A B T:Type} {MC: PermMap A B T} a b c m,
    indom m a -> (indom m c <-> indom (set m a b) c).
  intros.
  split.
  intros.
  indom_rewrite.
  unfold indom.
  infer_set (set m a b) c.
  exists b; auto.
  exists x; auto.

  intros.
  indom_rewrite.
  unfold indom.
  infer' (pnil, m, set m a b) c; crush. 
  eexists; auto.
  eexists; auto.
Qed.  
(* double 6, they are NOT same*)

Lemma absinfer_mutexpost_return_exwt_succ: 
  forall P mqls x wl tls t ct st m m' st'  t' p' pr op sch, 
    can_change_aop P ->  
    get mqls x = Some (absmutexsem pr (Some (ct, op)) ,wl) ->
    ~ wl=nil ->
    GetHWait tls wl t' ->
    get tls ct= Some (pr,  st,  m)  ->
    get tls t' = Some (p', st', m') ->
    absinfer sch
      ( <|| mutexpost (Vptr x :: nil) ||>  ** 
            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<|| isched;;END (Some (Vint32 (Int.repr NO_ERR))) ||>  ** HECBList (EcbMod.set mqls x (absmutexsem pr (Some (t', p')), (remove_tid t' wl))) ** HTCBList (TcbMod.set (TcbMod.set tls ct (op, st, m)) t' (p', rdy, (Vptr x)) ) ** HTime t ** HCurTCB ct ** P).
Proof.
  try match goal with
        | |- context [ <|| ?x _ ||> ] => unfold x
      end; intros.
  infer_branch 6%nat.

  (* ** ac: Print Ltac multi_step_handler. *) 
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  Focus 3.
  (* ** ac: SearchAbout absinfer. *)
  (* ** ac: Print absinfer. *)
  apply absinfer_seq_end.
  2: can_change_aop_solver.
  Focus 2.
  intro.
  intros.
  eauto.
  can_change_aop_solver.
  can_change_aop_solver.

  infer_part1 0%nat.
  assert ( exists tttt,  get (set tls ct (op, st, m)) t' = Some tttt).
 
  assert (ct = t' \/ ct <> t') by tauto.
  unfolds in H2.
  simpljoin.
  elim H5; intros.
  subst t'.
  rewrite map_get_set.
  eauto.
  eexists.
  apply get_set_neq.
  auto.
  eauto.
  simpljoin.
 
  infer_part2.
Qed.

Lemma absinfer_mutexpost_noreturn_exwt_succ: 
  forall P mqls x wl tls t ct st m m' st'  t' p' pr op p sch, 
   can_change_aop P ->  
    EcbMod.get mqls x = Some (absmutexsem pr (Some (ct, op)) ,wl) ->
    Int.eq p pr = false /\
    ~ wl=nil ->
    GetHWait tls wl t' ->
    get tls ct= Some (p,  st,  m)  ->
    get tls t' = Some (p', st', m') ->
    absinfer sch
      ( <|| mutexpost (Vptr x :: nil) ||>  ** 
            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<|| isched;;END (Some (Vint32 (Int.repr NO_ERR))) ||>  ** HECBList (EcbMod.set mqls x (absmutexsem pr (Some (t', p')), (remove_tid t' wl))) ** HTCBList (TcbMod.set  tls  t' (p', rdy, (Vptr x)) ) ** HTime t ** HCurTCB ct ** P).
Proof.
  try match goal with
        | |- context [ <|| ?x _ ||> ] => unfold x
      end; intros.
  simpljoin.
  infer_branch 6%nat.

  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  Focus 3.
  apply absinfer_seq_end.
  2: can_change_aop_solver.
  Focus 2.
  intro.
  intros.
  eauto.
  can_change_aop_solver.
  can_change_aop_solver.

  infer_part1 1%nat.
  infer_part2.
Qed.


Lemma absinfer_mutex_post_original_not_holder_err_return : forall x a P tcbls t ct sch,
                                                             can_change_aop P ->
                                                             absinfer sch (<|| mutexpost (Vptr a :: nil) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct **
                                                                           P) ( <|| END (Some  (V$OS_ERR_ORIGINAL_NOT_HOLDER)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 7%nat.
Qed.

Lemma absinfer_mutex_post_prio_err_return : forall x a P tcbls t ct p stp wl prio st msg sch,
                                              can_change_aop P ->
                                              EcbMod.get x a = Some (absmutexsem p stp,wl) ->
                                              TcbMod.get tcbls ct = Some (prio,st,msg) ->
                                              Int.ltu prio p = true ->
                                              absinfer sch (<|| mutexpost (Vptr a :: nil) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct **
                                                            P) ( <|| END (Some  (V$OS_ERR_MUTEX_PRIO)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 8%nat.
Qed.

Lemma absinfer_mutex_post_wl_highest_prio_err_return : forall x a P tcbls t ct pr opr wl sometid somepr somest somemsg sch, 
                                                         can_change_aop P ->
                                                         EcbMod.get x a = Some (absmutexsem pr opr, wl) ->
                                                         In sometid wl ->
                                                         TcbMod.get tcbls sometid = Some (somepr, somest, somemsg) ->
                                                         Int.ltu pr somepr = false -> 
                                                         absinfer sch (<|| mutexpost (Vptr a :: nil) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct **
                                                                       P) ( <|| END (Some  (V$OS_ERR_MUTEX_WL_HIGHEST_PRIO)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 9%nat.
Qed.

(* acc *)

Lemma mutexacc_null_absinfer :forall P sch, can_change_aop P -> absinfer sch
     ( <|| mutexacc (Vnull :: nil) ||>  **
     P) (<|| END (Some (V$0)) ||>  **
     P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexacc_no_mutex_err_absinfer:
  forall P mqls x v1 v3 ct sch,
    can_change_aop P ->
    (~ exists a b wl,EcbMod.get mqls x = Some (absmutexsem a b,wl)) ->
    absinfer sch
      ( <|| mutexacc  (Vptr x :: nil) ||>  ** HECBList mqls **  HTCBList v1 **
      HTime v3 **
      HCurTCB ct **
            P)
      (<|| END (Some (V$0)) ||>  ** HECBList mqls **  HTCBList v1 **
      HTime v3 **
      HCurTCB ct **
     P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma mutexacc_no_available_absinfer:
  forall P mqls x wl p o v1 v3 ct sch,  
    can_change_aop P ->  
    EcbMod.get mqls x = Some (absmutexsem p (Some o),wl)-> 
    absinfer sch
      ( <|| mutexacc (Vptr x :: nil) ||>  ** 
            HECBList mqls **  HTCBList v1 **
      HTime v3 **
      HCurTCB ct ** P) 
      (<|| END (Some (V$0)) ||>  ** HECBList mqls **  HTCBList v1 **
      HTime v3 **
      HCurTCB ct **
                    P).
Proof.
  infer_solver 2%nat.
Qed.


  Lemma  mutexacc_prio_err_absinfer:
    forall P mqls x wl p v1 v3 ct pt st m owner sch,  
      can_change_aop P ->  
      EcbMod.get mqls x = Some (absmutexsem p owner,wl)-> TcbMod.get v1 ct = Some (pt,st,m) -> 
      Int.ltu p pt = false ->
      absinfer sch
        ( <|| mutexacc (Vptr x :: nil) ||>  ** 
              HECBList mqls **  HTCBList v1 **
              HTime v3 **
              HCurTCB ct ** P) 
        (<|| END (Some (V$0)) ||>  ** HECBList mqls **  HTCBList v1 **
             HTime v3 **
             HCurTCB ct **
             P).
  Proof.
    infer_solver 3%nat.
  Qed.


Lemma mutexacc_succ_absinfer:
  forall P mqls x wl v1 v3 ct p pt st m sch, 
    can_change_aop P ->  
    EcbMod.get mqls x = Some (absmutexsem p None,wl) ->
    TcbMod.get v1 ct = Some (pt,st,m) ->
   Int.ltu p pt = true->
    absinfer sch
      ( <|| mutexacc (Vptr x :: nil) ||>  ** 
            HECBList mqls **  HTCBList v1 **
      HTime v3 **
      HCurTCB ct **
       P) 
      (<|| END (Some (V$1)) ||>  ** HECBList (EcbMod.set mqls x (absmutexsem p (Some (ct,pt)),wl)) **  HTCBList v1 **
      HTime v3 **
      HCurTCB ct **
                    P).
Proof.
  infer_solver 4%nat.
Qed.
(*
Lemma mutexacc_idle_err_absinfer:
  forall P mqls x v1 v3 ct st m, 
    can_change_aop P ->  
    TcbMod.get v1 ct = Some (Int.repr OS_IDLE_PRIO, st, m) ->
    absinfer sch
      ( <|| mutexacc (Vptr x :: nil) ||>  ** 
            HECBList mqls **  HTCBList v1 **
      HTime v3 **
      HCurTCB ct **
       P) 
      (<|| END (Some (V$0)) ||>  ** HECBList mqls **  HTCBList v1 **
      HTime v3 **
      HCurTCB ct **
                    P).
Proof.
  infer_solver 5%nat.
Qed.
*)  

(* create *)
 
Lemma mutexcre_error_absinfer :
  forall P i sch, 
    can_change_aop P -> 
    (Int.unsigned i <=? 255 = true) -> 
    absinfer sch ( <|| mutexcre (Vint32 i :: nil) ||> ** P)
           ( <|| END (Some Vnull) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexcre_succ_absinfer :
  forall P i qid  qls  tcbls curtid tm sch,
    can_change_aop P ->
    (Int.unsigned i <=? 255 = true) -> 
    prio_available i tcbls ->
    Int.ltu i (Int.repr OS_LOWEST_PRIO)= true ->
    EcbMod.get qls qid = None  ->
    absinfer sch ( <|| mutexcre (Vint32 i :: nil) ||>
                 **HECBList qls **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
           ( <|| END (Some (Vptr qid)) ||> **                                                                                                                 
                 HECBList (EcbMod.set qls qid (absmutexsem i
                                                       None,
                                               nil:list tid)) **HTCBList tcbls **  HTime tm **
                 HCurTCB curtid **P).
Proof.
  infer_solver 1%nat.
Qed.

(* delete *)

Lemma mutexdel_null_absinfer:
  forall P  sch, 
    can_change_aop P ->
    absinfer sch (<|| mutexdel (Vnull :: nil) ||> ** P)
           ( <|| END (Some  (V$ OS_ERR_PEVENT_NULL)) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutexdel_no_mutex_err_absinfer:
  forall x a P tcbls tm curtid sch, 
    can_change_aop P ->
    EcbMod.get x a = None ->
    absinfer sch (<|| mutexdel (Vptr a :: nil) ||>  ** HECBList x ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
           ( <|| END (Some  (V$ OS_ERR_PEVENT_NO_EX)) ||>  ** HECBList x ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
Proof.
   infer_solver 1%nat.
Qed.

Lemma mutexdel_type_err_absinfer:
  forall ecbls a P X tcbls tm curtid sch, 
    can_change_aop P ->
    EcbMod.get ecbls a = Some X ->
    (~ exists x y wl, X = (absmutexsem x y, wl))->
    absinfer sch (<|| mutexdel (Vptr a :: nil) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
           ( <|| END (Some  (V$OS_ERR_EVENT_TYPE)) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
Proof.
  infer_solver 2%nat.
Qed.


Lemma mutexdel_ex_wt_err_absinfer:
  forall x a P p o tl tcbls tm curtid  sch,
    can_change_aop P ->
    EcbMod.get x a = Some (absmutexsem p (Some o), tl)->
    absinfer sch (<|| mutexdel (Vptr a :: nil) ||> ** HECBList x  ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
           ( <|| END (Some  (V$ OS_ERR_TASK_WAITING)) ||> ** HECBList x  ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
Proof.
  infer_solver 3%nat.
Qed.

Lemma mutexdel_succ_absinfer:
  forall x a P z  x' tid t tcbls  sch, 
    can_change_aop P ->
    EcbMod.get x a = Some (absmutexsem z None, nil) ->
    EcbMod.join x' (EcbMod.sig a (absmutexsem z None, nil)) x ->
    absinfer sch (<|| mutexdel (Vptr a :: nil) ||> **
                HECBList x ** HTCBList tcbls ** HTime t **  HCurTCB tid  ** P)
           ( <|| END (Some  (V$ NO_ERR)) ||> ** HECBList x' ** HTCBList tcbls **
                 HTime t **  HCurTCB tid  ** P).
Proof.
  infer_solver 4%nat.
Qed.

Lemma mutexdel_pr_not_holder_err_absinfer:
  forall P tcbls x curtid tm a sch,
    can_change_aop P ->
    absinfer sch (<|| mutexdel (Vptr a ::nil)||>  ** HECBList x  ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P) ( <|| END (Some (V$ OS_ERR_MUTEXPR_NOT_HOLDER))||>  ** HECBList x  ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
Proof.
  infer_solver 5%nat.
Qed.

