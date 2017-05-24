Require Import include_frm.
Require Import os_inv.
Require Import abs_op.
Require Import sep_auto.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import os_code_defs.

Local Open Scope int_scope.
(* create absop rules *)
Lemma absimp_mbox_create_no_free:
  forall P i sch,
    can_change_aop P ->
    isptr i ->
    absinfer sch ( <|| mbox_create (i :: nil) ||> ** P)
             ( <|| END (Some Vnull) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absimp_mbox_create_err_return :
  forall P i sch, 
    can_change_aop P ->
    isptr i ->
    absinfer sch ( <|| mbox_create  ( i :: nil) ||> ** P)
             ( <|| END (Some Vnull) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.


Lemma absimp_mbox_create_succ_return :
  forall P i qid  qls  tcbls curtid tm sch,
    can_change_aop P ->
    isptr i ->
    EcbMod.get qls qid = None  ->
    absinfer sch ( <|| mbox_create ( i :: nil) ||>
                 **HECBList qls **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
           ( <|| END (Some (Vptr qid)) ||> **                                                                                                                 
                 HECBList (EcbMod.set qls qid (absmbox i,
                                               nil:list tid)) **HTCBList tcbls **  HTime tm **
                 HCurTCB curtid **P).
Proof.
  infer_solver 1.
Qed.

(* del absop rules *)

Lemma absinfer_mbox_del_null_return :
  forall P sch, 
can_change_aop P ->
absinfer sch (<|| mbox_del (Vnull :: nil) ||> ** P) ( <|| END (Some (Vint32 (Int.repr MBOX_DEL_NULL_ERR))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_mbox_del_p_not_legal_return :
  forall x a P tcbls tm curtid sch, 
    can_change_aop P ->
    ~ (exists x0 wls, EcbMod.get x a = Some (absmbox x0, wls)) ->
    absinfer sch (<|| mbox_del (Vptr a :: nil) ||> ** HECBList x **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P) ( <|| END (Some  (V$ MBOX_DEL_P_NOT_LEGAL_ERR)) ||> ** HECBList x **   HTCBList tcbls ** HTime tm **  HCurTCB curtid  ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma absinfer_mbox_del_wrong_type_return :
  forall x a P tcbls tm curtid sch,
    can_change_aop P ->
    (exists d,
       EcbMod.get x a = Some d /\ ~ (exists x wls, d = (absmbox x, wls))) ->
    absinfer sch (<||mbox_del (Vptr a :: nil) ||>  ** HECBList x **   HTCBList tcbls ** HTime tm **  HCurTCB curtid **  P) ( <|| END (Some  (V$ OS_ERR_EVENT_TYPE)) ||> ** HECBList x **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
Proof.
  infer_solver 2%nat.
Qed.


Lemma absinfer_mbox_del_task_wt_return :
  forall x a P tcbls tm curtid sch,
    can_change_aop P ->
    (exists y t tl,
       get x a = Some (absmbox y, t::tl)) ->
    absinfer sch (<|| mbox_del (Vptr a :: nil) ||>  ** HECBList x **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P) ( <|| END (Some  (V$ MBOX_DEL_TASK_WAITING_ERR)) ||>   ** HECBList x **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
Proof.
  infer_solver 3%nat.
  simpljoin.
  tri_exists_and_solver.
Qed.

Lemma absinfer_mbox_del_succ_return :
  forall ecbls ecbls' x a P tid tcbls t sch,
    can_change_aop P ->
    EcbMod.get ecbls a = Some (absmbox x, nil) ->
    EcbMod.join ecbls' (EcbMod.sig a (absmbox x, nil)) ecbls -> 
    absinfer sch (<|| mbox_del (Vptr a :: nil) ||> ** HECBList ecbls **
                  HTCBList tcbls ** HTime t **  HCurTCB tid **  P) ( <||  END (Some  (V$NO_ERR)) ||> **
                                                                          HECBList ecbls' ** HTCBList tcbls ** HTime t **  HCurTCB tid  ** P).
Proof.
  infer_solver 4%nat.
Qed.

(* acc absop rules *)

Lemma absinfer_mbox_acc_err_return :
  forall P x sch,
    can_change_aop P ->
    isptr x ->
    absinfer sch (<|| mbox_acc (x :: nil) ||>  **  P) ( <|| END (Some Vnull) ||>  **  P).
Proof.
  infer_solver 0%nat.
Qed.


Lemma  absinfer_mbox_acc_succ_return:
  forall P mqls x wl v v1 v3 v4 a sch,
    can_change_aop P ->  
    v = Vptr a -> 
    EcbMod.get mqls x = Some (absmbox v, wl) -> 
    absinfer sch
      ( <|| mbox_acc (Vptr x :: nil) ||>  ** 
            HECBList mqls **  HTCBList v1 **
            HTime v3 **
            HCurTCB v4 **
            P) 
      (<|| END (Some v) ||>  ** HECBList (EcbMod.set mqls x (absmbox Vnull, nil)) **  HTCBList v1 **
           HTime v3 **
           HCurTCB v4 **
           P).
Proof.
  infer_solver 1%nat.
Qed.

(* pend absop rules *)

Lemma absinfer_mbox_pend_null_return :
  forall P x sch,
    can_change_aop P ->
    tl_vl_match  (Tint16 :: nil) x = true ->
    absinfer sch (<|| mbox_pend (Vnull :: x) ||> ** P) ( <|| END (Some (Vint32 (Int.repr MBOX_PEND_NULL_ERR))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Local Open Scope Z_scope.

Lemma absinfer_mbox_pend_p_not_legal_return :
  forall x a P b v'33 v'16 v'35 sch,
    can_change_aop P ->
    Int.unsigned b<=65535 ->
    EcbMod.get x a = None ->
    absinfer sch (<|| mbox_pend (Vptr a ::Vint32 b:: nil) ||> ** HECBList x **
                  HTCBList v'33 **
                  HTime v'16 **
                  HCurTCB v'35 **
                  P) ( <|| END (Some  (V$ MBOX_PEND_P_NOT_LEGAL_ERR)) ||> ** HECBList x **
                           HTCBList v'33 **
                           HTime v'16 **
                           HCurTCB v'35 ** P).
Proof.
  infer_solver 1%nat.
Qed.


Lemma absinfer_mbox_pend_wrong_type_return :
  forall x a b P v'33 v'16 v'35 sch,
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists d,
       EcbMod.get x a = Some d /\ ~ (exists x wls, d = (absmbox x, wls))) ->
    absinfer sch (<|| mbox_pend (Vptr a :: Vint32 b :: nil) ||> ** HECBList x **
                  HTCBList v'33 **
                  HTime v'16 **
                  HCurTCB v'35 **
                  P) ( <|| END (Some  (V$MBOX_PEND_WRONG_TYPE_ERR)) ||> ** HECBList x **
                           HTCBList v'33 **
                           HTime v'16 **
                           HCurTCB v'35 ** P).
Proof.
  intros.
  simpljoin.
  destruct x0.
  infer_solver 2%nat.
  repeat tri_exists_and_solver1.
  intro.
  apply H2.
  simpljoin.
  eauto.
Qed.

Lemma absinfer_mbox_pend_from_idle_return :
  forall x a b P y t ct sch,
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists st msg, get y ct = Some (Int.repr OS_IDLE_PRIO, st, msg)) ->
    absinfer sch (<|| mbox_pend (Vptr a :: Vint32 b :: nil) ||> ** HECBList x ** HTCBList y ** HTime t ** HCurTCB ct **
                  P) ( <|| END (Some  (V$MBOX_PEND_FROM_IDLE_ERR)) ||> ** HECBList x ** HTCBList y ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  simpljoin.
  infer_solver 3%nat.
Qed.

Lemma absinfer_mbox_pend_not_ready_return :
  forall P ecbls tcbls t ct st msg v x prio sch,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls ct = Some (prio, st, msg) ->
    ~ st = rdy ->
    can_change_aop P ->
    absinfer sch (<|| mbox_pend (Vptr x :: Vint32 v :: nil) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P)
             (<|| END (Some (Vint32 (Int.repr MBOX_PEND_NOT_READY_ERR)))||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 4%nat.
Qed.


Lemma  absinfer_mbox_pend_inst_get_return:
  forall P mqls x wl v v1 v3 v4 a v00 msg p sch,
    can_change_aop P ->  
    v = Vptr a -> 
    Int.unsigned v00 <= 65535 ->
    get mqls x = Some (absmbox v, wl) -> 
    get v1 v4 = Some (p, rdy, msg) ->
    absinfer sch
      ( <|| mbox_pend (Vptr x ::Vint32 v00 :: nil) ||>  ** 
            HECBList mqls **  HTCBList v1 **
            HTime v3 **
            HCurTCB v4 **
            P) 
      (<|| END (Some (Vint32 (Int.repr MBOX_PEND_SUCC))) ||>  ** HECBList (set mqls x (absmbox Vnull, nil)) **  HTCBList (set v1 v4 (p, rdy, v)) **
           HTime v3 **
           HCurTCB v4 **
           P).
Proof.
  infer_solver 5%nat.
Qed.

Lemma absinfer_mbox_pend_block:
  forall P mqls qid v wl p m t ct tls sch,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    EcbMod.get mqls qid = Some (absmbox Vnull, wl) ->
    TcbMod.get tls ct = Some (p,rdy,m) ->
    absinfer sch
      ( <|| mbox_pend (Vptr qid :: Vint32 v :: nil) ||>  ** 
            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<|| isched;; (mbox_pend_timeout_err (|Vptr qid :: Vint32 v :: nil|) ?? mbox_pend_block_get_succ (|Vptr qid :: Vint32 v :: nil|))||>  ** HECBList (EcbMod.set mqls qid (absmbox Vnull,ct::wl)) ** HTCBList (TcbMod.set tls ct (p,wait (os_stat_mbox qid) v, Vnull) ) ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 6%nat.
Qed.


(* post *)
Local Open Scope code_scope.

Lemma absinfer_mbox_post_null_return :
  forall P x sch, 
    can_change_aop P ->
    tl_vl_match  ((Void) ∗ :: nil) x = true ->
    absinfer sch (<|| mbox_post (Vnull :: x) ||> ** P) ( <|| END (Some (Vint32 (Int.repr MBOX_POST_NULL_ERR))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_mbox_post_msg_null_return:
  forall P v sch, 
    can_change_aop P -> 
    absinfer sch
      ( <|| mbox_post (Vptr v :: Vnull ::nil) ||>  **
            P) (<|| END (Some (Vint32 (Int.repr  OS_ERR_POST_NULL_PTR))) ||>  **
                    P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma absinfer_mbox_post_p_not_legal_return :
  forall x a P b tcbls t ct sch, 
    can_change_aop P ->
    EcbMod.get x a = None ->
    absinfer sch (<|| mbox_post (Vptr a ::Vptr b:: nil) ||> ** HECBList x** HTCBList tcbls ** HTime t ** HCurTCB ct  **
                      P) ( <|| END (Some  (V$ MBOX_POST_P_NOT_LEGAL_ERR)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct  ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma absinfer_mbox_post_wrong_type_return :
  forall x a b P tcbls t ct sch, 
    can_change_aop P ->
    (exists d,
       get x a = Some d /\ ~ (exists x wls, d = (absmbox x, wls))) ->
    absinfer sch (<|| mbox_post (Vptr a :: Vptr b :: nil) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct **
                      P) ( <|| END (Some  (V$MBOX_POST_WRONG_TYPE_ERR)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  intros; simpljoin.
  infer_solver 3%nat.
  
  destruct x0.
  repeat tri_exists_and_solver1.
  intro.
  apply H1.
  simpljoin.
  eauto.
Qed.

Lemma absinfer_mbox_post_full_return :
  forall P mqls x a wl y tcbls t ct sch, 
    can_change_aop P ->  
    EcbMod.get mqls x = Some (absmbox a,wl) ->
    (exists b, a= Vptr b) ->
    absinfer sch
      ( <|| mbox_post (Vptr x :: Vptr y :: nil) ||>  **HECBList mqls ** 
            HTCBList tcbls ** HTime t ** HCurTCB ct ** P) 
      (<|| END (Some (Vint32 (Int.repr MBOX_POST_FULL_ERR))) ||> **HECBList mqls ** HTCBList tcbls ** HTime t ** HCurTCB ct  ** P).
Proof.
  infer_solver 4%nat.
Qed.



Lemma absinfer_mbox_post_exwt_succ: 
  forall P mqls x v wl tls t ct p st m m'  t' sch, 
    can_change_aop P ->  
    get mqls x = Some (absmbox m ,wl) ->
    ~ wl=nil ->
    GetHWait tls wl t' ->
    get tls t' = Some (p,st, m') ->
    absinfer sch
      ( <|| mbox_post (Vptr x :: Vptr v :: nil) ||>  ** 
            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<|| isched;;END (Some (Vint32 (Int.repr NO_ERR))) ||>  ** HECBList (set mqls x (absmbox m, (remove_tid t' wl))) ** HTCBList (set tls t' (p,rdy , (Vptr v)) ) ** HTime t ** HCurTCB ct ** P).
Proof.
  unfold mbox_post; intros.
  infer_branch 5%nat.
  eapply absinfer_trans.
  Focus 2.
  eapply absinfer_seq_end.
  3:sep auto.
  can_change_aop_solver.
  can_change_aop_solver.
  instantiate (1:= (Some (V$NO_ERR))).
  eapply absinfer_seq.
  can_change_aop_solver.
  can_change_aop_solver.
  infer_part2.
Qed.


Lemma absinfer_mbox_post_put_mail_return :
  forall P x m mqls tcbls t ct sch,
    can_change_aop P ->
    EcbMod.get mqls x = Some (absmbox Vnull, nil) ->
    absinfer sch (<|| mbox_post (Vptr x :: Vptr m ::nil) ||> **HECBList mqls** HTCBList tcbls ** HTime t ** HCurTCB ct ** P) (<|| END (Some (Vint32 (Int.repr MBOX_POST_SUCC))) ||> **HECBList (EcbMod.set mqls x (absmbox (Vptr m),nil))** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 6%nat.
Qed.


