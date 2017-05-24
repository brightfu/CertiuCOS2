Require Import include_frm.
Require Import os_inv.
Require Import abs_op.
Require Import sep_auto.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import os_code_defs.

Local Open Scope int_scope.
Local Open Scope Z_scope.
(*************************** sem create *******************************)

Lemma semcre_absimp_no_free:
  forall P n sch,
    can_change_aop P ->
    (Z.leb (Int.unsigned n) Int16.max_unsigned) = true ->
    absinfer sch ( <|| semcre (Vint32 n :: nil) ||> ** P)
             ( <|| END (Some Vnull) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma semcre_absimp_succ:
  forall P sid n els tcbls tm curtid sch,
    can_change_aop P ->
    (Z.leb (Int.unsigned n) Int16.max_unsigned) = true ->
    get els sid = None ->
    absinfer sch ( <|| semcre (Vint32 n :: nil) ||> **
             HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
           ( <|| END (Some (Vptr sid)) ||> **
             HECBList (set els sid (abssem n, nil:list tid)) **
             HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 1%nat.
Qed.

(*********************** sem acc **************************************)
Lemma semacc_absimp_null:
  forall sid P sch,
    sid = Vnull ->
    can_change_aop P -> 
    absinfer sch ( <|| semacc (sid :: nil) ||> ** P)
             ( <|| END (Some (Vint32 Int.zero)) ||> ** P ).
Proof.
  infer_solver 0%nat.
Qed.  
  

Lemma semacc_absimp_no_sem:
  forall P els tcbls tm curtid sid sch,
    can_change_aop P ->
    (~ exists n wls, EcbMod.get els sid = Some (abssem n, wls)) ->
    absinfer sch 
      ( <|| semacc (Vptr sid :: nil) ||> ** 
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| END (Some (Vint32 Int.zero)) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
  infer_solver 1%nat.
Qed.
  
Lemma semacc_absimp_no_source:
  forall P els tcbls tm curtid sid wls sch,
    can_change_aop P ->
    get els sid = Some (abssem Int.zero, wls) ->
    absinfer sch
      ( <|| semacc (Vptr sid :: nil) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| END (Some (Vint32 Int.zero)) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma semacc_absimp_succ:
  forall P wls els sid n v1 v3 v4 sch,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    absinfer sch
      ( <|| semacc (Vptr sid :: nil) ||> **
        HECBList els **
        HTCBList v1 **
        HTime v3 **
        HCurTCB v4 ** P)
      ( <|| END (Some (Vint32 n)) ||> **
        HECBList (set els sid (abssem (Int.sub n Int.one), wls)) **
        HTCBList v1 **
        HTime v3 **
        HCurTCB v4 ** P).
  infer_solver 3%nat.
Qed.
(******************************************* sem del *********************************)
Lemma semdel_absimp_null:
  forall sid P sch,
    sid = Vnull ->
    can_change_aop P -> 
    absinfer sch ( <|| semdel (sid :: nil) ||> ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) ||> ** P ).
  infer_solver 0%nat.
Qed.
  
Lemma semdel_absimp_no_sem:
  forall P els tcbls tm curtid sid sch,
    can_change_aop P ->
    (~ exists n wls, EcbMod.get els sid = Some (abssem n, wls)) ->
    absinfer sch 
      ( <|| semdel (Vptr sid :: nil) ||> ** 
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
  infer_solver 1%nat.
Qed.
  
Lemma semdel_absimp_type_err:
  forall P els tcbls tm curtid sid sch,
    can_change_aop P ->
    (~ exists n wls, EcbMod.get els sid = Some (abssem n, wls)) ->
    absinfer sch 
      ( <|| semdel (Vptr sid :: nil) ||> ** 
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid  ** P)
      ( <|| END (Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE))) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
  infer_solver 2%nat.
Qed.
  
Lemma semdel_absimp_task_waiting:
  forall P els tcbls tm curtid n sid w wls sch,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, w::wls) ->
    absinfer sch
      ( <|| semdel (Vptr sid :: nil) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| END (Some (Vint32 (Int.repr OS_ERR_TASK_WAITING))) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
  infer_solver 3%nat.
Qed.

  
Lemma semdel_absimp_succ:
  forall P els els' sid n v1 v3 v4 sch,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, nil) ->
    EcbMod.join els' (EcbMod.sig sid (abssem n,nil)) els ->
    absinfer sch
      ( <|| semdel (Vptr sid :: nil) ||> **
        HECBList els **
        HTCBList v1 **
        HTime v3 **
        HCurTCB v4 ** P)
      ( <|| END (Some (Vint32 (Int.repr NO_ERR))) ||> **
        HECBList els' **
        HTCBList v1 **
        HTime v3 **
        HCurTCB v4 ** P).
  infer_solver 4%nat.
Qed.
  
(******************************************** sem post *************************************)
Lemma absimp_sem_post_null_return:
  forall sid P sch,
    sid = Vnull ->
    can_change_aop P -> 
    absinfer sch ( <|| sem_post (sid :: nil) ||> ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) ||> ** P ).
  infer_solver 0%nat.
Qed.
  
Lemma absimp_sem_post_p_not_legal_return:
  forall P els tcbls tm curtid sid sch,
    can_change_aop P ->
    EcbMod.get els sid = None ->
    absinfer sch ( <|| sem_post ((Vptr sid) :: nil) ||> **
               HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) ||> **
               HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 1%nat.
Qed.  

Lemma absimp_sem_post_wrong_type_return:
  forall P els tcbls tm curtid sid sch,
    can_change_aop P ->
    (exists d,
      EcbMod.get els sid = Some d /\ ~ (exists n wls, d = (abssem n, wls))) ->
    absinfer sch
      ( <|| sem_post ((Vptr sid) :: nil) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma absimp_sem_post_ovf_err_return:
  forall P els tcbls tm curtid sid n wls sch,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = false ->
    absinfer sch
      ( <|| sem_post ((Vptr sid) :: nil) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P)
      ( <|| END (Some (Vint32 (Int.repr OS_SEM_OVF))) ||> **
        HECBList els ** HTCBList tcbls ** HTime tm ** HCurTCB curtid ** P).
Proof.
  infer_solver 3%nat.
Qed.  

Lemma absimp_sem_post_put_sem_return:
  forall P els sid n wls tcbls t ct sch,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = true ->
    absinfer sch
      ( <|| sem_post ((Vptr sid) :: nil) ||> **
            HECBList els **
            HTCBList tcbls **
            HTime t ** HCurTCB ct ** P)
      ( <|| END (Some (Vint32 (Int.repr OS_NO_ERR))) ||> **
        HECBList (EcbMod.set els sid (abssem (Int.add n Int.one), wls)) **
        HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  infer_solver 5%nat.
Qed.  
  
Lemma absimp_sem_post_ex_wt_succ_return:
  forall P els sid tls t t' n wls p st m ct mid sch,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    ~ wls = nil ->
    GetHWait tls wls t' ->
    TcbMod.get tls t' = Some (p, st, m) ->
    absinfer sch
      ( <|| sem_post ((Vptr sid) :: nil) ||> **
        HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P )
      ( <|| isched;;END (Some (Vint32 (Int.repr OS_NO_ERR))) ||> **
        HECBList (EcbMod.set els sid (abssem n, (remove_tid t' wls))) **
        HTCBList (TcbMod.set tls t' (p, rdy, Vptr mid)) **
        HTime t ** HCurTCB ct ** P ).
Proof.
  infer_solver 4%nat.
Qed.


(******************************************* sem_pend **********************************)

Lemma absinfer_sem_pend_null_return :
  forall P x sch, 
    can_change_aop P ->
    tl_vl_match  (Tint16 :: nil) x = true ->
    absinfer sch
      (<|| sem_pend (Vnull :: x) ||> ** P)
      (<|| END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Local Open Scope Z_scope.

Lemma absinfer_sem_pend_p_not_legal_return :
  forall x a P b v'33 v'16 v'35 sch, 
    can_change_aop P ->
    Int.unsigned b<=65535 ->
    EcbMod.get x a = None ->
    absinfer sch
      (<|| sem_pend (Vptr a ::Vint32 b:: nil) ||> **
           HECBList x **
           HTCBList v'33 **
           HTime v'16 **
           HCurTCB v'35 ** P)
      (<|| END (Some  (V$ OS_ERR_PEVENT_NULL)) ||> **
           HECBList x **
           HTCBList v'33 **
           HTime v'16 **
           HCurTCB v'35 ** P).
Proof.
  infer_solver 1%nat.
Qed.  

Lemma absinfer_sem_pend_wrong_type_return :
  forall x a b P v'33 v'16 v'35 sch, 
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists d,
       EcbMod.get x a = Some d /\ ~ (exists x wls, d = (abssem x, wls))) ->
    absinfer sch
      (<|| sem_pend (Vptr a :: Vint32 b :: nil) ||> **
           HECBList x **
           HTCBList v'33 **
           HTime v'16 **
           HCurTCB v'35 ** P)
      (<|| END (Some  (V$ OS_ERR_PEVENT_NULL)) ||> **
           HECBList x **
           HTCBList v'33 **
           HTime v'16 **
           HCurTCB v'35 ** P).
Proof.
  infer_solver 2%nat.
Qed.  
  
Lemma absinfer_sem_pend_from_idle_return :
  forall x a b P y t ct sch, 
    can_change_aop P ->
    Int.unsigned b <= 65535 ->
    (exists st msg, TcbMod.get y ct = Some (Int.repr OS_IDLE_PRIO, st, msg)) ->
    absinfer sch
      (<|| sem_pend (Vptr a :: Vint32 b :: nil) ||> **
           HECBList x **
           HTCBList y **
           HTime t **
           HCurTCB ct ** P)
      ( <|| END (Some  (V$ OS_ERR_PEVENT_NULL)) ||> **
            HECBList x **
            HTCBList y **
            HTime t **
            HCurTCB ct ** P).
Proof.
  intros.
  simpljoin.
  infer_solver 3%nat.
Qed.

Lemma absinfer_sem_pend_not_ready_return :
  forall P ecbls tcbls t ct st msg v x prio sch,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls ct = Some (prio, st, msg) ->
    ~ st = rdy ->
    can_change_aop P ->
    absinfer sch
      (<|| sem_pend (Vptr x :: Vint32 v :: nil) ||> **
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
  infer_solver 4%nat.
Qed.  

Lemma absinfer_sem_pend_inst_get_return:
  forall P wls els sid n v1 v3 v4 v sch,
    can_change_aop P ->
    Int.unsigned v <= 65535 ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    absinfer sch
      ( <|| sem_pend (Vptr sid :: Vint32 v :: nil) ||> **
        HECBList els **
        HTCBList v1 **
        HTime v3 **
        HCurTCB v4 ** P)
      ( <|| END (Some (Vint32 (Int.repr OS_NO_ERR))) ||> **
        HECBList (EcbMod.set els sid (abssem (Int.sub n Int.one), wls)) **
        HTCBList v1 **
        HTime v3 **
        HCurTCB v4 ** P).
Proof.
  infer_solver 5%nat.
Qed.  

Lemma absinfer_sem_pend_msg_not_null_return :
  forall P ecbls tcbls t ct st msg v x prio sch,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls ct = Some (prio, st, msg) ->
    ~ msg = Vnull ->
    can_change_aop P ->
    absinfer sch
      (<|| sem_pend (Vptr x :: Vint32 v :: nil) ||> **
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
  infer_solver 6%nat.
Qed.  

Lemma absinfer_sem_pend_block:
  forall P mqls qid v wl p m t ct tls sch,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    EcbMod.get mqls qid = Some (abssem Int.zero, wl) ->
    TcbMod.get tls ct = Some (p,rdy,m) ->
    absinfer sch
      ( <|| sem_pend (Vptr qid :: Vint32 v :: nil) ||>  ** 
           HECBList mqls **
           HTCBList tls **
           HTime t **
           HCurTCB ct ** P) 
      (<|| isched;;
           (sem_pend_timeout_err (|Vptr qid :: Vint32 v :: nil|) ??
            sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: nil|)) ||> **
           HECBList (EcbMod.set mqls qid (abssem Int.zero ,ct::wl)) **
           HTCBList (TcbMod.set tls ct (p,wait (os_stat_sem qid) v, m) ) **
           HTime t **
           HCurTCB ct ** P).
Proof.
  infer_solver 7%nat.
Qed.  


Lemma absinfer_sem_pend_to_timeout :
   forall P mqls qid t ct tls v st prio m sch,
    Int.unsigned v <= 65535 ->
    TcbMod.get tls ct = Some (prio, st, m) ->
    m = Vnull ->
    can_change_aop P ->
    absinfer sch
      ( <|| sem_pend_timeout_err (|Vptr qid :: Vint32 v :: nil|)
            ?? sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: nil|) ||>  ** 
            HECBList mqls **
            HTCBList tls **
            HTime t **
            HCurTCB ct ** P) 
      (<||  END (Some (Vint32 (Int.repr OS_TIMEOUT)))||> **
            HECBList mqls **
            HTCBList tls **
            HTime t **
            HCurTCB ct ** P).
Proof.
  intros.
  subst m.
  infer_solver 0%nat.
Qed.  

Lemma absinfer_sem_pend_to_succ:
      forall (P : asrt) mqls (qid : addrval) 
         (v : int32) (p : priority) (t : ostime) (ct : tidspec.A)
         (tls : TcbMod.map) (m : msg) (st : taskstatus) sch,
       Int.unsigned v <= 65535 ->
       can_change_aop P ->
       TcbMod.get tls ct = Some (p, st, m) ->
       ~ (m = Vnull) ->
       absinfer sch
         ( <|| sem_pend_timeout_err (|Vptr qid :: Vint32 v :: nil|)
               ?? sem_pend_block_get_succ (|Vptr qid :: Vint32 v :: nil|) ||> **
               HECBList mqls **
               HTCBList tls **
               HTime t **
               HCurTCB ct ** P)
         ( <|| END (Some (V$ OS_NO_ERR)) ||>  **
               HECBList mqls **
               HTCBList tls **
               HTime t **
               HCurTCB ct ** P).
Proof.
  infer_solver 1%nat.
Qed.  

