Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Definition PRIO_ERR := OS_PRIO_INVALID.
Definition PRIO_EXIST_ERR := OS_PRIO_EXIST.
Definition NO_TCB_ERR := OS_NO_MORE_TCB .
Definition NO_ERR := OS_NO_ERR.
Definition MAX_TCB := OS_MAX_TASKS.

Definition get_tls_len (tm:TcbMod.map) :=
  length (TcbMod.lst tm).

Definition get_els_len (tm:EcbMod.map) :=
  length (EcbMod.lst tm).

Definition DEL_IDLE_ERR := OS_TASK_DEL_IDLE.
Definition DEL_NO_EXIST_ERR := OS_TASK_DEL_ERR.
Definition SELF := OS_PRIO_SELF.

Fixpoint remove_tid (t:tid) (tl:list tid):=
  match tl with
    | nil => nil
    | t'::tl' => if (beq_tid t t') then remove_tid t tl' else (t'::(remove_tid t tl'))
  end.


Definition isrdy (st:taskstatus):=
  match st with
    | rdy => True
    | _ => False
  end.


Notation abtcblsid:=abstcblsid.

Definition GetHPrio (O:osabst) (t:tid) :Prop:= 
 (exists tls prio st msg,
    get O abstcblsid = Some (abstcblist tls) /\ get tls t = Some (prio,st,msg) /\isrdy st/\
    forall i prio' st' msg',i <> t -> get tls i = Some (prio',st',msg') -> isrdy st'-> 
              Int.ltu prio prio'=true).

Definition nsc (O : osabst) :=
  exists t t', get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t = t'.

Definition sc (O : osabst) :=
  exists t t',  get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t <> t'.

Definition isched := (ASSUME sc;; sched) ?? (ASSUME nsc).


Definition timedly_zero (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) => exists v,
       vl= ((Vint32 v)::nil) /\
       opv = None /\ v = Int.zero /\ O2=O1
  end.

Definition timedly_succ (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      exists v,
      vl= ((Vint32 v)::nil) /\
      opv = None /\ Int.ltu Int.zero v=true/\
      exists tls p msg t,
         get O1 curtid = Some (oscurt t) /\ 
         get O1 abtcblsid = Some (abstcblist tls) /\  
        get tls t = Some (p,rdy,msg) /\
        O2=set O1 abtcblsid (abstcblist (set tls t (p,wait os_stat_time v,msg)))
  end.
 
Definition timedly_nop (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists v,
       vl= ((Vint32 v)::nil) /\
       (
         opv =  None /\ Int.ltu Int.zero v=true/\
         exists tls p st msg t,
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abtcblsid = Some (abstcblist tls) /\  
           get tls t = Some (p,st,msg)/\
           (st <> rdy) /\
           O2=O1        
       )
  end.

Definition timedly_idle  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists v,
       vl= ((Vint32 v)::nil) /\
       (
         opv =  None /\
         exists tls st msg t,
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abtcblsid = Some (abstcblist tls) /\  
           get tls t = Some (Int.repr OS_IDLE_PRIO,st,msg)/\
           O2=O1        
       )
  end.

Definition tmdlycode (vl : vallist) :=
  timedly_zero (|vl|) ?? (timedly_succ  (|vl|) ;; isched ;; END None) ??
               timedly_nop (|vl|) ?? timedly_idle (|vl|).

Definition dlyapi:=(tmdlycode,(Tvoid,Tint16::nil)).


Definition timeget   (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
        vl= nil/\
        (
          exists tm,
             get O1 ostmid = Some (ostm tm)/\
            opv =  (Some (Vint32 tm))/\
            O2 = O1
        )
  end.

Definition tmgetcode (vl : vallist):= timeget(|vl|).

Definition tmgetapi:=(tmgetcode,(Tint32,(nil:typelist))).

(**************************** sem_absop begin ****************************)
Definition TIME_OUT := OS_TIMEOUT.
Definition GetHWait (tls:TcbMod.map) (wl:list tid) (t:tid) := 
  In t wl /\ 
  exists p st msg,
    get tls t = Some (p,st,msg)/\
    forall t', t<>t' -> In t' wl -> exists p' st' msg', get tls t' = Some (p',st',msg') /\ (Int.ltu p p' = true)%Z.

(****************************** sem acc ************************************)

Definition semacc_null (vl: vallist) (O1 : osabst) (rst : option val * osabst) :=
  match rst with
    | (opv, O2) =>
      vl = (Vnull :: nil) /\
      opv = Some (Vint32 Int.zero) /\ O2 = O1
  end.

Definition semacc_no_sem_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    | (opv, O2) =>
      exists sid,
        vl = ((Vptr sid) :: nil) /\
        exists els,
          opv = Some (Vint32 Int.zero) /\
           get O1 absecblsid = Some (absecblist els) /\
          (~ exists n wls, get els sid = Some (abssem n, wls)) /\
          O2 = O1
  end.

Definition semacc_no_source (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    | (opv, O2) =>
      exists sid,
        vl = ((Vptr sid) :: nil) /\
        exists els,
          opv = (Some (Vint32 Int.zero)) /\
           get O1 absecblsid = Some (absecblist els) /\
          (exists wls, get els sid = Some (abssem Int.zero, wls)) /\
          O2 = O1
  end.

Definition semacc_succ (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    | (opv, O2) =>
      exists sid,
        vl = ((Vptr sid) :: nil) /\
        exists els n wls,
          opv = (Some (Vint32 n)) /\
           get O1 absecblsid = Some (absecblist els) /\
          get els sid = Some (abssem n, wls) /\
          Int.ltu Int.zero n = true /\
          O2 =  set O1 absecblsid (absecblist (set els sid (abssem (Int.sub n Int.one), wls)))
  end.

Definition semacc (vl: vallist) :=
  semacc_null (|vl|)
  ?? semacc_no_sem_err (|vl|)
  ?? semacc_no_source (|vl|)
  ?? semacc_succ (|vl|).

Definition semaccapi:=(semacc, (Tint16,(Tptr OS_EVENT)::nil)).
(**************************** sem cre ******************************************)

Definition semcre_no_free (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    | (opv, O2) =>
      exists n,
        vl = ((Vint32 n) :: nil) /\
        (Z.leb (Int.unsigned n) Int16.max_unsigned) = true /\
        opv = Some Vnull /\
        O2 = O1
  end.

Definition semcre_succ (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    | (opv, O2) =>
      exists n,
        vl = ((Vint32 n) :: nil) /\
        (Z.leb (Int.unsigned n) Int16.max_unsigned) = true /\
        exists sls sls' sid,
          opv = Some (Vptr sid) /\
           get O1 absecblsid = Some (absecblist sls) /\
          get sls sid = None /\
          sls' = set sls sid (abssem n, nil) /\
          O2= ( set O1 absecblsid (absecblist sls')) 
  end.

Definition semcre (vl: vallist) :=
  semcre_no_free (|vl|)
  ?? semcre_succ (|vl|).

Definition semcreapi:=(semcre,(Tptr OS_EVENT, Tint16 ::nil)).

(*********************************** sem del *********************************************)

Definition SEM_NULL_ERR := OS_ERR_PEVENT_NULL.
Definition SEM_DEL_EX_ERR := OS_ERR_TASK_WAITING.

Definition semdel_null (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    | (opv, O2) =>
      vl = (Vnull :: nil) /\
      opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) /\
      O1 = O2
  end.

Definition semdel_no_sem_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    | (opv, O2) =>
      exists sid,
        vl = ((Vptr sid) :: nil) /\
        exists els,
           get O1 absecblsid = Some (absecblist els) /\
          (~ exists n wls,get els sid = Some (abssem n,wls) )/\
          opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
          O2 = O1
  end.

Definition semdel_sem_type_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    | (opv, O2) =>
      exists sid,
        vl = ((Vptr sid) :: nil) /\
        exists els,
           get O1 absecblsid = Some (absecblist els) /\
          (~ exists n wls,get els sid = Some (abssem n,wls) )/\
          opv = (Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)))/\
          O2 = O1
  end.

Definition semdel_ex_wt_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    | (opv, O2) =>
      exists sid, 
         vl = ((Vptr sid)::nil) /\
         exists els t' tl n,
            get O1 absecblsid = Some (absecblist els) /\
           get els sid = Some (abssem n,t'::tl) /\
           opv = (Some (Vint32 (Int.repr OS_ERR_TASK_WAITING)))/\
           O2 = O1                                    
  end.

Definition semdel_succ (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    |(opv, O2) =>
     exists sid,
       vl= ((Vptr sid)::nil) /\
       exists sls sls' n,
          get O1 absecblsid = Some (absecblist sls) /\
         get sls sid = Some (abssem n,nil) /\
         opv = (Some (Vint32 (Int.repr NO_ERR)))/\
         join sls' (sig sid (abssem n,nil)) sls/\
         O2 = ( set O1 absecblsid (absecblist sls')) 
 end.

Definition semdel (vl: vallist) :=
  semdel_null (|vl|)
  ?? semdel_no_sem_err (|vl|)
  ?? semdel_sem_type_err (|vl|)
  ?? semdel_ex_wt_err (|vl|)
  ?? semdel_succ (|vl|).

Definition semdelapi:=(semdel ,(Tint8,Tptr OS_EVENT::nil)).

(*************************************** sem post **************************************)

Definition sem_post_null_err (vl: vallist) (O1: osabst) (rst: option val * osabst) := 
  match rst with
    | (opv, O2) =>
      vl = (Vnull :: nil) /\
      opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) /\
      O1 = O2
  end.

Definition sem_post_p_not_legal_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    | (opv, O2) => 
      exists qid,
       vl = ((Vptr qid) :: nil) /\
       exists els,
          get O1 absecblsid = Some (absecblist els) /\
         get els qid = None /\
         opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
         O2=O1                                    
  end.

Definition sem_post_wrong_type_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    | (opv, O2) => 
      exists qid,
        vl= ((Vptr qid) :: nil) /\
        exists els,
           get O1 absecblsid = Some (absecblist els) /\
          (exists d,get els qid = Some d /\ (~exists n wls, d = (abssem n, wls)) )/\
          opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
          O2=O1                                    
  end.        

Definition sem_post_ovf_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    | (opv, O2) =>
      exists sid,
         vl=  (Vptr sid :: nil) /\
         exists sls n wl,
            get O1 absecblsid = Some (absecblist sls) /\
           get sls sid = Some (abssem n,wl) /\
           (Int.ltu n (Int.repr 65535) = false)/\
           opv = (Some (Vint32 (Int.repr OS_SEM_OVF)))/\
           O2 = O1                                    
  end.

Definition sem_post_ex_wt_succ (vl: vallist) (O1: osabst) (rst:option val * osabst) := 
  match rst with
    | (opv, O2) =>
      exists qid, 
        vl = (Vptr qid :: nil) /\
        exists els tls t' wl tls' els' p st m n, exists mid,
           get O1 abtcblsid = Some (abstcblist tls) /\
           get O1 absecblsid = Some (absecblist els) /\
          (get els qid = Some (abssem n, wl)) /\
          (~ wl = nil ) /\
          (GetHWait tls wl t') /\
          opv = (Some (Vint32 (Int.repr OS_NO_ERR))) /\
          get tls t' = Some (p,st,m) /\
          tls' = set tls t' (p,rdy, Vptr mid) /\
          els' = set els qid (abssem n, (remove_tid t' wl)) /\
          O2 =  set ( set O1 abtcblsid (abstcblist tls')) absecblsid (absecblist els')
  end.

Definition sem_post_put_sem_in_succ (vl: vallist) (O1: osabst) (rst: option val * osabst) := 
  match rst with
    | (opv, O2) =>
      exists qid, 
        vl = (Vptr qid :: nil) /\
        exists els n wls,
           get O1 absecblsid = Some (absecblist els) /\
          (get els qid = Some (abssem n, wls)) /\
          Int.ltu n (Int.repr 65535) = true /\
          opv = (Some (Vint32 (Int.repr OS_NO_ERR ))) /\
          O2 =  set O1 absecblsid (absecblist (set els qid (abssem (Int.add n Int.one), wls)))
  end.

Definition sem_post (vl: vallist) :=
  sem_post_null_err (|vl|)
  ?? sem_post_p_not_legal_err (|vl|)
  ?? sem_post_wrong_type_err (|vl|)
  ?? sem_post_ovf_err (|vl|)
  ?? (sem_post_ex_wt_succ (|vl|) ;; isched ;; END (Some (Vint32 (Int.repr OS_NO_ERR))))
  ?? sem_post_put_sem_in_succ (|vl|).

Definition sem_postapi := (sem_post, (Tint8, Tptr OS_EVENT :: nil)).

(******************************************** sem_pend *************************************)
Definition sem_pend_null_err (vl: vallist) (O1: osabst) (rst: option val * osabst):=
  match rst with
    |(opv, O2) =>
     exists vl',
       vl = (Vnull::vl') /\
       opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
       O1 = O2
  end.

Definition sem_pend_p_not_legal_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    |(opv, O2) => 
     exists qid v ,
       vl= ((Vptr qid)::(Vint32 v) ::nil)/\
       (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
             get els qid = None /\
             opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
             O2=O1                                    
       )
  end.

Definition sem_pend_wrong_type_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    |(opv, O2) => 
     exists qid v,
       vl= ((Vptr qid)::(Vint32 v)::nil)/\
       (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
             (exists d,get els qid = Some d /\ (~exists x wls, d = (abssem x, wls)) )/\
             opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
             O2=O1                                    
       )
  end.        

Definition sem_pend_from_idle_err (vl: vallist) (O1: osabst) (rst: option val * osabst):=
  match rst with
    |(rv, O2) =>
     (
       exists qid v,
         vl=(Vptr qid::Vint32 v::nil) /\
         exists tls st msg t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (Int.repr OS_IDLE_PRIO,st,msg) /\
           rv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
           O2=O1         
     )
  end.

Definition sem_pend_not_ready_err (vl: vallist) (O1: osabst) (rst: option val * osabst):=
  match rst with
    |(rv, O2) =>
     (
       exists qid v,
         vl=(Vptr qid::Vint32 v::nil) /\
         exists tls st msg prio t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (prio,st,msg) /\
           ~ st = rdy /\
           rv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
           O2=O1         
     )
  end.


Definition sem_pend_inst_get_succ (vl: vallist) (O1: osabst) (rst: option val * osabst) := 
  match rst with
    |  (opv, O2) =>
       (exists qid v,
          vl=((Vptr qid) ::Vint32 v ::nil) /\ 
          exists els n wls,
             get O1 absecblsid = Some (absecblist els) /\
            Int.ltu Int.zero n = true /\
            get els qid = Some (abssem n, wls) /\
            O2 =  set O1 absecblsid
                               (absecblist (set els qid (abssem (Int.sub n Int.one), wls))) /\
            opv = (Some (Vint32 (Int.repr OS_NO_ERR))))
        end.

Definition sem_pend_msg_not_null_err (vl: vallist) (O1: osabst) (rst: option val * osabst):=
  match rst with
    |(rv, O2) =>
     (
       exists qid v,
         vl=(Vptr qid::Vint32 v::nil) /\
         exists tls st msg prio t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (prio,st,msg) /\
           ~ msg = Vnull /\
           rv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
           O2=O1         
     )
  end.

Definition sem_pend_block (vl: vallist) (O1: osabst) (rst: option val * osabst) := 
  match rst with
    |(opv, O2) =>
     (
       (
        exists qid v m,
           vl=(Vptr qid::Vint32 v::nil) /\
           exists tls tls' qls qls' wl p st t,
              get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abtcblsid = Some (abstcblist tls) /\ 
             get qls qid = Some (abssem Int.zero, wl) /\
             qls'=set qls qid (abssem Int.zero, t::wl)/\
             get tls t = Some (p,st,m) /\
             tls' = set tls t (p,wait (os_stat_sem qid) v,m)/\
             O2= set ( set O1 abtcblsid (abstcblist tls') ) 
                              absecblsid (absecblist qls')/\
             opv = None
       )
     )
  end.

Definition sem_pend_timeout_err (vl: vallist) (O1: osabst) (rst: option val * osabst) := 
  match rst with
    |(rv, O2) =>
     exists qid v,
       vl=(Vptr qid::Vint32 v::nil) /\
       (
         (
           exists st tls p t,
              get O1 curtid = Some (oscurt t) /\
              get O1 abtcblsid = Some (abstcblist tls)/\
             get tls t =Some (p,st,Vnull)/\
             O1 = O2 /\
             rv= (Some (Vint32 (Int.repr OS_TIMEOUT)))
         )
       )
  end.

Definition sem_pend_block_get_succ (vl: vallist) (O1: osabst) (rst: option val * osabst) := 
  match rst with
    |(rv, O2) =>
     exists qid v,
       vl= (Vptr qid::Vint32 v::nil) /\
       (
         exists tls p m st t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abtcblsid = Some (abstcblist tls)/\
           get tls t =Some (p,st,m)/\
           m <> Vnull /\
           O1 = O2 /\
           rv=(Some (Vint32 (Int.repr OS_NO_ERR)))
       )
  end.

Definition sem_pend  (vl: vallist):=
  sem_pend_null_err (|vl|)
  ?? sem_pend_p_not_legal_err (|vl|)
  ?? sem_pend_wrong_type_err (|vl|)
  ?? sem_pend_from_idle_err (|vl|)
  ?? sem_pend_not_ready_err (|vl|)
  ?? sem_pend_inst_get_succ (|vl|)
  ?? sem_pend_msg_not_null_err (|vl|)
  ?? ( sem_pend_block (|vl|) ;; isched ;;
                      ( sem_pend_timeout_err (|vl|) ?? sem_pend_block_get_succ (|vl|))).

Definition sem_pendapi:=(sem_pend,(Tint8,Tptr OS_EVENT::Tint16::nil)).



(***************************** sem_absop end *****************************)



Definition Q_SIZE := OS_MAX_Q_SIZE.

Definition qcre_error  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists v ,
        vl= ((Vint32 v)::nil)/\
        opv= (Some Vnull)/\
        O2=O1
  end.

Definition qcre_succ  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists v,
        vl= ((Vint32 v)::nil)/\
        exists qls qls' qid,
              opv= (Some (Vptr qid))/\
               get O1 absecblsid = Some (absecblist qls) /\
             (* Z.to_nat OS_MAX_EVENTS > (get_els_len qls)/\*)
              Int.ltu (Int.repr Q_SIZE) v=false/\
              EcbMod.joinsig qid (absmsgq (nil:list val) v,(nil:list tid)) qls qls'/\
              O2= set O1 absecblsid (absecblist qls')
  end.

Definition qcre (vl : vallist) :=
  qcre_error (|vl|) ?? qcre_succ (|vl|).

Definition qcreapi:=(qcre,(Tptr OS_EVENT, Tint16::nil)).

Definition qacc_null (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>  (vl =  (Vnull::nil) /\ opv =  (Some Vnull) /\ O2 = O1)
  end.

Definition qacc_no_q_err  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (exists qid,
       vl= ((Vptr qid)::nil)/\
         (
           exists qls, 
             opv =  (Some Vnull)/\
              get O1 absecblsid = Some (absecblist qls) /\
             (~ exists x y wls,get qls qid = Some (absmsgq x y,wls) )/\
             O2=O1
         )
     )
  end.

Definition qacc_no_msg  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (exists qid,
       vl= ((Vptr qid)::nil)/\
       (
           exists qls, 
             opv =  (Some Vnull)/\
              get O1 absecblsid = Some (absecblist qls) /\
             (exists wls n,get qls qid =Some (absmsgq nil n,wls))/\
             O2=O1
         )
     )
  end.

Definition qacc_succ  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (exists qid,
       vl= ((Vptr qid)::nil)/\
       (
          exists qls msg mls n wl, 
             opv =  (Some msg)/\
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid =Some (absmsgq (msg::mls) n,wl)/\
             O2= set O1 absecblsid (absecblist (set qls qid (absmsgq mls n,wl)))
       )
     )
  end.

Definition qacc (vl : vallist) :=
  qacc_null (|vl|) ??  qacc_no_q_err (|vl|) ?? qacc_no_msg (|vl|) ?? qacc_succ (|vl|).

Definition qaccapi := (qacc,(Tptr Tvoid, Tptr OS_EVENT::nil)).

Definition MSGQ_NULL_ERR := OS_ERR_PEVENT_NULL.
Definition MSGQ_DEL_EX_ERR := OS_ERR_TASK_WAITING.

Definition qdel_null  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     vl =  (Vnull::nil) /\
     opv =  (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
     O1 = O2
  end.


Definition qdel_no_q_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid,
       vl=  ((Vptr qid)::nil)/\
       (
         (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
             (~ exists x y wls,get els qid = Some (absmsgq x y,wls) )/\
             opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
             O2=O1                                    
         )
       )
  end.


Definition qdel_q_type_err  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid,
       vl=  ((Vptr qid)::nil)/\
       (
         (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
             (exists d, get els qid = Some d /\
                       ~exists x y wls, d = (absmsgq x y,wls)) /\
             opv =  (Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)))/\
             O2=O1                                    
         )
       )
  end.



Definition qdel_ex_wt_err  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid, 
         vl=  ((Vptr qid)::nil)/\
         (
           exists qls t' tl x y,
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid = Some (absmsgq x y,t'::tl) /\
             opv =  (Some (Vint32 (Int.repr OS_ERR_TASK_WAITING)))/\
             O2=O1                                    
         )
  end.

Definition qdel_succ (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid,
       vl=  ((Vptr qid)::nil)/\
       (
           exists qls qls' x y,
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid = Some (absmsgq x y,nil) /\
             opv =  (Some (Vint32 (Int.repr NO_ERR)))/\
             join qls' (sig qid (absmsgq x y,nil)) qls/\
             O2= ( set O1 absecblsid (absecblist qls')) 
       )
 end.

Definition qdel  (vl:vallist):=
  qdel_null (|vl|) ?? qdel_no_q_err (|vl|) ??
   qdel_q_type_err (|vl|) ?? qdel_ex_wt_err (|vl|) ?? qdel_succ (|vl|).


Definition qdelapi:=(qdel,(Tint8,Tptr OS_EVENT::nil)).

Definition qpend_null (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists vl',
       vl =  (Vnull::vl') /\
       opv =  (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
       O1 = O2
  end.

Definition qpend_no_q_err  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       exists qid v,
         vl= (Vptr qid::Vint32 v::nil) /\
         exists qls,
                  get O1 absecblsid = Some (absecblist qls) /\
                 (~ exists x y wls,get qls qid = Some (absmsgq x y,wls) )/\
                 opv =  (Some (Vint32 (Int.repr MSGQ_NULL_ERR)))/\
                 O2=O1         
     )
  end.

Definition qpend_idle_err  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       exists qid v,
         vl= (Vptr qid::Vint32 v::nil) /\
         exists tls st msg t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (Int.repr OS_IDLE_PRIO,st,msg) /\
           opv =  (Some (Vint32 (Int.repr MSGQ_NULL_ERR)))/\
           O2=O1         
     )
  end.

Definition qpend_stat_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       exists qid v,
         vl=  (Vptr qid::Vint32 v::nil) /\
         exists tls st msg prio t,
             get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (prio,st,msg) /\
           ~ st = rdy /\
           opv =  (Some (Vint32 (Int.repr MSGQ_NULL_ERR)))/\
           O2=O1         
     )
  end.

Definition qpend_get_succ   (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
         exists qid v,
           vl= (Vptr qid::Vint32 v::nil) /\
           (
             (
               exists qls n qls' tcbls tcbls',
                 exists msg ml prio m wl t,
                    get O1 curtid = Some (oscurt t) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                  get O1 abstcblsid = Some (abstcblist tcbls) /\
                 get qls qid = Some (absmsgq (msg::ml) n,wl) /\
                 get tcbls t = Some (prio,rdy ,m)/\
                 qls'=set qls qid (absmsgq ml n,wl)/\
                 tcbls' = set tcbls t (prio,rdy ,msg) /\
                 O2= set ( set O1 abstcblsid (abstcblist tcbls'))
                                    absecblsid (absecblist qls') /\
                 opv= (Some (Vint32 (Int.repr NO_ERR)))
             ) 
           
       )
     )
  end.


Definition qpend_block  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       (
         exists qid v m,
           vl= (Vptr qid::Vint32 v::nil) /\
           exists tls tls' qls qls' wl p st n t,
               get O1 curtid = Some (oscurt t) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                 get qls qid = Some (absmsgq nil n,wl) /\
                 qls'=set qls qid (absmsgq nil n,t::wl)/\
                  get O1 abtcblsid = Some (abstcblist tls) /\ 
                 get tls t = Some (p,st,m) /\
                 tls' = set tls t (p,wait (os_stat_q qid) v,Vnull)/\
                 O2= set ( set O1 abtcblsid (abstcblist tls') ) 
                                   absecblsid (absecblist qls')/\
                 opv=  None 
         )
     )
  end.

Definition qpend_to  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid v,
       vl= (Vptr qid::Vint32 v::nil) /\
       (
         (
           exists st tls p m t,
              get O1 curtid = Some (oscurt t) /\
              get O1 abtcblsid = Some (abstcblist tls)/\
             get tls t =Some (p,st,m)/\
             m = Vnull /\
             O1 = O2 /\
             opv=   (Some (Vint32 (Int.repr TIME_OUT)))
         )
       )
  end.

Definition qpend_block_get (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid v,
       vl= (Vptr qid::Vint32 v::nil) /\
       (
         exists tls p m st t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abtcblsid = Some (abstcblist tls)/\
           get tls t =Some (p,st,m)/\
           m<>Vnull /\
           O1 = O2 /\
           opv= (Some (Vint32 (Int.repr NO_ERR)))
       )
  end.

Definition qpend  (vl:vallist):=
  qpend_null (|vl|) ?? qpend_no_q_err (|vl|) ??
             qpend_get_succ (|vl|) ??  qpend_idle_err (|vl|) ??
             (qpend_block (|vl|) ;; isched ;; (qpend_to  (|vl|) ?? qpend_block_get (|vl|))) ??
              qpend_stat_err  (|vl|).  

Definition qpendapi:=(qpend,(Tint8,Tptr OS_EVENT::Tint16::nil)).

Definition MSG_NULL_ERR := OS_ERR_POST_NULL_PTR.
Definition MSGQ_OVF_ERR := OS_Q_FULL.

Definition qpost_null (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists vl',
       vl =  (Vnull::vl') /\
       opv =  (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
       O1 = O2
  end.

Definition qpost_msg_null (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists v,
       vl =  (v::Vnull::nil) /\
       opv =  (Some (Vint32 (Int.repr OS_ERR_POST_NULL_PTR)))/\
       O1 = O2
  end.


Definition qpost_q_no_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid msg,
       vl= (Vptr qid::msg::nil) /\
       (
         (
           exists qls,
              get O1 absecblsid = Some (absecblist qls) /\
             (~ exists x y wls,get qls qid = Some (absmsgq x y,wls) )/\
             opv =  (Some (Vint32 (Int.repr MSGQ_NULL_ERR)))/\
             O2=O1                                    
         )
       )
  end.

Definition qpost_ovf_err(vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid msg,
       vl= (Vptr qid::msg::nil) /\
       (
         (
           exists qls n wl ml,
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid = Some (absmsgq ml n,wl) /\
             Z.ge (Z_of_nat (length ml)) (Int.unsigned n)/\ 
             opv =  (Some (Vint32 (Int.repr MSGQ_OVF_ERR)))/\
             O2=O1      
         )
       )
  end.

Definition qpost_nowt_succ(vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid msg,
       vl=  (Vptr qid::msg::nil) /\
       (
         (
           exists qls n ml,
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid = Some (absmsgq ml n,nil) /\
             Z.lt (Z_of_nat (length ml)) (Int.unsigned n)/\ 
             opv =  (Some (Vint32 (Int.repr NO_ERR)))/\
             O2= set O1 absecblsid (absecblist (set qls qid (absmsgq (ml++(msg::nil)) n,nil)))
         )
       )
  end.


Definition qpost_exwt_succ(vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid msg,
       vl= (Vptr qid::msg::nil) /\
       (
         (
           exists qls vl wl qls' t' tls tls' m,  
               exists p st n,
                  get O1 abtcblsid = Some (abstcblist tls) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                 get qls qid = Some (absmsgq vl n,wl) /\
                 ~ wl =nil /\
                 GetHWait tls wl t'/\
                 opv =  (Some (Vint32 (Int.repr NO_ERR)))/\
                 get tls t' = Some (p,st,m)/\
                 tls'=set tls t' (p,rdy,msg)/\
                 qls' = set qls qid (absmsgq nil n,(remove_tid t' wl))/\
                 O2= set ( set O1   abtcblsid (abstcblist tls')) 
                                                  absecblsid (absecblist qls')
         )
       )
  end.


Definition qpost (vl:vallist):=
  qpost_null (|vl|) ??  qpost_msg_null (|vl|) ??
             qpost_q_no_err (|vl|) ??  qpost_ovf_err (|vl|) ?? qpost_nowt_succ  (|vl|) ??
             qpost_exwt_succ (|vl|) ;; isched ;; END Some (Vint32 (Int.repr NO_ERR)).                                   


Definition qpostapi:=(qpost,(Tint8,Tptr OS_EVENT::Tptr Tvoid::nil)).


Definition getmsg_succ (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     vl= nil /\ 
     exists tcbls t,
        get O1 curtid = Some (oscurt t) /\
        get O1 abstcblsid = Some (abstcblist tcbls) /\
       (
         exists prio st msg,
           get tcbls t = Some (prio,st,msg) /\
           opv =  (Some msg)/\
           O2= set O1 abstcblsid (abstcblist (set tcbls t (prio,st,Vnull)))
       )
  end.

Definition getmsg (vl : vallist) :=  getmsg_succ (|vl|).

Definition getmsgapi:=(getmsg,(Tptr Tvoid,(nil:typelist))).

(*mutex semphore*)

(*mutex create*)
Definition mutexcre_error  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists v ,
        vl= ((Vint32 v)::nil)/\
        opv= (Some Vnull)/\
        O2=O1
  end.

Definition prio_available prio tls:=
  forall t p x y, get tls t = Some (p, x, y) -> Int.eq prio p = false.

Definition mutexcre_succ  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists v,
        vl= ((Vint32 v)::nil)/\
        exists qls qls' qid tls,
          opv= (Some (Vptr qid))/\
           get O1 abstcblsid = Some (abstcblist tls) /\
           get O1 absecblsid = Some (absecblist qls) /\
          Int.ltu v (Int.repr OS_LOWEST_PRIO)= true /\
          prio_available v tls /\
          EcbMod.joinsig qid (absmutexsem v None,(nil:list tid)) qls qls' /\
          O2= set O1 absecblsid (absecblist qls')
  end.


Definition mutexcre  (vl : vallist):=
   mutexcre_error (|vl|) ??  mutexcre_succ (|vl|).

Definition mutexcreapi:=(mutexcre,(Tptr OS_EVENT, Tint8::nil)).

(*mutex acc*)
Definition mutexacc_null (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      (vl =  (Vnull::nil) /\ opv =  (Some (Vint32 (Int.repr 0))) /\ O2 = O1)
  end.

Definition mutexacc_no_mutex_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (exists qid,
       vl= ((Vptr qid)::nil)/\
         (
           exists qls, 
             opv =  (Some (Vint32 (Int.repr 0)))/\
              get O1 absecblsid = Some (absecblist qls) /\
             (~ exists x y wls,get qls qid = Some (absmutexsem x y,wls) )/\
             O2=O1
         )
     )
  end.
(*
Definition mutexacc_own_err (t:tid) (beg res:prod stval osabst):=
  match beg,res with
    |(vl,O1),(opv,O2) =>
     (exists qid,
       vl=inits ((Vptr qid)::nil)/\
         (
           exists qls qid' x y wls, 
             opv = dones (Some (Vint32 (Int.repr 0)))/\
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid' = Some (absmutexsem x (Some (t,y)),wls) /\
             O2=O1
         )
     )
  end.*)

Definition mutexacc_no_available  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (exists qid,
       vl= ((Vptr qid)::nil)/\
       (
           exists qls, 
             opv =  (Some (Vint32 (Int.repr 0)))/\
              get O1 absecblsid = Some (absecblist qls) /\
             (exists wls p o,get qls qid =Some (absmutexsem p (Some o),wls))/\
             O2=O1
         )
     )
  end.

Definition mutexacc_prio_err  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      (exists qid,
         vl= ((Vptr qid)::nil)/\
         (
           exists qls tls st wls pt stt m t p,
              get O1 curtid = Some (oscurt t) /\
             opv =  (Some (Vint32 (Int.repr 0))) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
             get qls qid =Some (absmutexsem p st,wls)/\
             get tls t = Some (pt,stt,m) /\
             Int.ltu p pt = false /\
             O2=O1
      )
)
end.


Definition mutexacc_succ  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (exists qid,
       vl= ((Vptr qid)::nil)/\
       (
         exists qls tls p wl pt st m t,
             get O1 curtid = Some (oscurt t) /\
             opv =  (Some (Vint32 (Int.repr 1)))/\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
             get tls t = Some (pt,st,m) /\
             Int.ltu p pt = true /\
             get qls qid =Some (absmutexsem p None, wl)/\
             O2= set O1 absecblsid (absecblist (set qls qid (absmutexsem p (Some (t,pt)),wl)))
       )
     )
  end.

Definition mutexacc  (vl:vallist):=
  mutexacc_null (|vl|) ??
                mutexacc_no_mutex_err (|vl|) ??
                 mutexacc_no_available (|vl|) ?? mutexacc_prio_err (|vl|) ?? mutexacc_succ (|vl|).

Definition mutexaccapi := (mutexacc,(Tint8, Tptr OS_EVENT::nil)).

(*mutex del*)

Definition mutexdel_null  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     vl =  (Vnull::nil) /\
     opv =  (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
     O1 = O2
  end.


Definition mutexdel_no_mutex_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid,
       vl=  ((Vptr qid)::nil)/\
       (
         (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
              get els qid = None/\
             opv =  (Some (Vint32 (Int.repr OS_ERR_PEVENT_NO_EX)))/\
             O2=O1                                    
         )
       )
  end.


Definition mutexdel_type_err  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid,
       vl=  ((Vptr qid)::nil)/\
       (
         (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
             (exists d, get els qid = Some d /\
                       ~exists x y wls, d = (absmutexsem x y,wls)) /\
             opv =  (Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)))/\
             O2=O1                                    
         )
       )
  end.



Definition mutexdel_ex_wt_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid, 
         vl=  ((Vptr qid)::nil)/\
         (
           exists qls tl x y,
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid = Some (absmutexsem x (Some y),tl) /\
             opv =  (Some (Vint32 (Int.repr OS_ERR_TASK_WAITING)))/\
             O2=O1                                    
         )
  end.

Definition mutexdel_succ (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid,
       vl=  ((Vptr qid)::nil)/\
       (
           exists qls qls' x,
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid = Some (absmutexsem x None,nil) /\ 
             opv =  (Some (Vint32 (Int.repr NO_ERR)))/\
             join qls' (sig qid (absmutexsem x None,nil)) qls/\
             O2= ( set O1 absecblsid (absecblist qls')) 
       )
 end.

Definition mutexdel_pr_not_holder_err (vl: vallist) (O1: osabst) (rst : option val * osabst) :=
        match rst with
              | (opv, O2) =>
                        opv = Some (Vint32 (Int.repr OS_ERR_MUTEXPR_NOT_HOLDER)) /\
                        O2 = O1
        end.

Definition mutexdel  (vl : vallist):=
  mutexdel_null (|vl|) ??  mutexdel_no_mutex_err (|vl|) ??
   mutexdel_type_err (|vl|) ?? mutexdel_ex_wt_err (|vl|) ?? mutexdel_succ (|vl|)  ?? mutexdel_pr_not_holder_err(|vl|) .


Definition mutexdelapi:=(mutexdel,(Tint8,Tptr OS_EVENT::nil)).

(*mutex pend*)

Definition mutexpend_null(vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists vl',
       vl =  (Vnull::vl') /\
       opv =  (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
       O1 = O2
  end.

Definition mutexpend_no_mutex_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       exists qid v,
         vl= (Vptr qid::Vint32 v::nil) /\
         exists qls,
                  get O1 absecblsid = Some (absecblist qls) /\
                 get qls qid = None /\
                 opv =  (Some (Vint32 (Int.repr OS_ERR_PEVENT_NO_EX)))/\
                 O2=O1         
     )
  end.

Definition mutexpend_type_err(vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       exists qid v,
         vl=  (Vptr qid::Vint32 v::nil) /\
         exists qls,
            get O1 absecblsid = Some (absecblist qls) /\
           (exists d, get qls qid = Some d /\
                      (~ exists x y wl,d = (absmutexsem x y ,wl))) /\
           opv =  (Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)))/\
           O2=O1         
     )
  end.


Definition mutexpend_idle_err(vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       exists qid v,
         vl= (Vptr qid::Vint32 v::nil) /\
         exists tls st msg t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (Int.repr OS_IDLE_PRIO,st,msg) /\
           opv =  (Some (Vint32 (Int.repr OS_ERR_IDLE)))/\
           O2=O1         
     )
  end.

Definition mutexpend_stat_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       exists qid v,
         vl=  (Vptr qid::Vint32 v::nil) /\
         exists tls st msg prio t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (prio,st,msg) /\
           ~ st = rdy /\
           opv =  (Some (Vint32 (Int.repr OS_ERR_STAT)))/\
           O2=O1         
     )
  end.

Definition mutexpend_msg_not_null_err (vl: vallist) (O1: osabst) (rst: option val * osabst):=
  match rst with
    |(rv, O2) =>
     (
       exists qid v,
         vl=(Vptr qid::Vint32 v::nil) /\
         exists tls st msg prio t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (prio,st,msg) /\
           ~ msg = Vnull /\
           rv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
           O2=O1         
     )
  end.

(** cur_prio <= pip: err *)
Definition mutexpend_prio_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       exists qid v qls,
         vl=  (Vptr qid::Vint32 v::nil) /\
         exists tls st msg prio t p stp wl,
            get O1 curtid = Some (oscurt t) /\
            get O1 absecblsid = Some (absecblist qls) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get qls qid = Some (absmutexsem p stp,wl) /\
           get tls t = Some (prio,st,msg) /\
           Int.ltu p prio = false /\
           opv =  (Some (Vint32 (Int.repr OS_ERR_MUTEX_PRIO)))/\
           O2=O1         
     )
  end.


Definition mutexpend_get_succ  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
         exists qid v,
           vl= (Vptr qid::Vint32 v::nil) /\
           (
             (
               exists qls qls' tcbls,
                 exists prio m  p t,
                    get O1 curtid = Some (oscurt t) /\
                    get O1 absecblsid = Some (absecblist qls) /\
                    get O1 abstcblsid = Some (abstcblist tcbls) /\
                   get qls qid = Some (absmutexsem p None,nil) /\
                   get tcbls t = Some (prio,rdy,m)/\
                   Int.ltu p prio = true /\
                   qls'=set qls qid (absmutexsem p (Some (t,prio)),nil)/\
                   O2= set O1 absecblsid (absecblist qls') /\
                   opv =  (Some (Vint32 (Int.repr NO_ERR)))
             ) 
               
       )
     )
  end.

(** ptcb is not ready *)
Definition mutexpend_nest_err  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       (
         exists qid v m,
           vl= (Vptr qid::Vint32 v::nil) /\
           exists tls qls,
             exists wl p t' p' px  pt st' m' t,
                get O1 curtid = Some (oscurt t) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                  get O1 abtcblsid = Some (abstcblist tls) /\
                 
                 get qls qid = Some (absmutexsem p (Some (t',p')),wl) /\
                 get tls t = Some (pt,rdy,m) /\
                 get tls t' = Some (px,st',m') /\
                 st' <> rdy /\
                 O2=O1 /\
                 opv = (Some (Vint32 (Int.repr OS_ERR_NEST)))
         )
     )
  end.

(** ptcb == cur : err *)
Definition mutexpend_deadlock_err  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       (
         exists qid v,
           vl= (Vptr qid::Vint32 v::nil) /\
           exists tls qls,
             exists wl p p' t t',
                get O1 curtid = Some (oscurt t) /\
                get O1 absecblsid = Some (absecblist qls) /\
                get O1 abtcblsid = Some (abstcblist tls) /\
               get qls qid = Some (absmutexsem p (Some (t',p')),wl) /\
               t = t' /\
               O2=O1 /\
               opv = (Some (Vint32 (Int.repr OS_ERR_MUTEX_DEADLOCK)))
         )
     )
  end.

Definition mutexpend_block_lift  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       (
         exists qid v m,
           vl= (Vptr qid::Vint32 v::nil) /\
           exists tls tls' tls'' qls qls',
             exists wl p t' p' px  pt  m' t,
                get O1 curtid = Some (oscurt t) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                  get O1 abtcblsid = Some (abstcblist tls) /\
                 
                 get qls qid = Some (absmutexsem p (Some (t',p')),wl) /\
                 get tls t = Some (pt,rdy,m) /\
                 get tls t' = Some (px,rdy,m') /\

                 Int.eq px p = false /\
                 Int.ltu pt p' = true /\
                 Int.ltu p pt = true /\
                 
                 qls' = set qls qid (absmutexsem p (Some (t',p')),t::wl) /\
                 tls' = set tls t (pt,wait (os_stat_mutexsem qid) v,m) /\
                 tls'' = set tls' t' (p,rdy,m') /\
                 O2= set ( set O1 abtcblsid (abstcblist tls'') ) 
                                   absecblsid (absecblist qls') /\
                 opv = None
         )
     )
  end.


Definition mutexpend_block_no_lift (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       (
         exists qid v m,
           vl= (Vptr qid::Vint32 v::nil) /\
           exists tls tls' qls qls',
             exists wl p t' p' px pt m' t,
                get O1 curtid = Some (oscurt t) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                  get O1 abtcblsid = Some (abstcblist tls) /\
                 
                 get qls qid = Some (absmutexsem p (Some (t',p')),wl) /\
                 get tls t = Some (pt,rdy,m) /\
                 get tls t' = Some (px,rdy,m') /\

                 ( ~(Int.eq px p = false) \/ (Int.ltu p' pt = true) ) /\
                 Int.ltu p pt = true /\
                 
                 qls' = set qls qid (absmutexsem p (Some (t',p')),t::wl) /\
                 tls' = set tls t (pt,wait (os_stat_mutexsem qid) v,Vnull) /\
                 O2= set ( set O1 abtcblsid (abstcblist tls') ) 
                                   absecblsid (absecblist qls') /\
                 opv = None
         )
     )
  end.

Definition mutexpend_to  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid v,
       vl= (Vptr qid::Vint32 v::nil) /\
       (
         (
           exists st tls p m t,
              get O1 curtid = Some (oscurt t) /\
              get O1 abtcblsid = Some (abstcblist tls)/\
             get tls t =Some (p,st,m)/\
             m = Vnull /\
             O1 = O2 /\
             opv =   (Some (Vint32 (Int.repr TIME_OUT)))
         )
       )
  end.

Definition mutexpend_block_get  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid v,
       vl= (Vptr qid::Vint32 v::nil) /\
       (
         exists tls p m st t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abtcblsid = Some (abstcblist tls)/\
           get tls t =Some (p,st,m)/\
           m<>Vnull /\
           O1 = O2 /\
           opv =  (Some (Vint32 (Int.repr NO_ERR)))
       )
  end.

(** pip is not hold *)
Definition mutexpend_pr_not_holder_err (vl: vallist) (O1: osabst) (rst : option val * osabst) :=
        match rst with
              | (opv, O2) =>
                        opv = Some (Vint32 (Int.repr OS_ERR_MUTEXPR_NOT_HOLDER)) /\
                        O2 = O1
        end.

(** ptcb_prio = idle: err *)
Definition mutexpend_ptcb_prio_eql_idle_err  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       (
         exists qid v,
           vl= (Vptr qid::Vint32 v::nil) /\
           exists tls qls,
             exists wl p p' t t' st msg,
                get O1 curtid = Some (oscurt t) /\
                get O1 absecblsid = Some (absecblist qls) /\
                get O1 abtcblsid = Some (abstcblist tls) /\
               get qls qid = Some (absmutexsem p (Some (t',p')),wl) /\
               get tls t' = Some (Int.repr OS_IDLE_PRIO,st,msg) /\
               O2=O1 /\
               opv = (Some (Vint32 (Int.repr OS_ERR_MUTEX_IDLE)))
         )
     )
  end.

(** mprio = cur_prio : err *)
Definition mutexpend_cur_prio_eql_mprio_err  (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       (
         exists qid v,
           vl= (Vptr qid::Vint32 v::nil) /\
           exists tls qls,
             exists wl p p' t t' prio st msg,
                get O1 curtid = Some (oscurt t) /\
                get O1 absecblsid = Some (absecblist qls) /\
                get O1 abtcblsid = Some (abstcblist tls) /\
               get qls qid = Some (absmutexsem p (Some (t',p')),wl) /\
               get tls t = Some (prio ,st,msg) /\
               p' = prio /\
               O2=O1 /\
               opv = (Some (Vint32 (Int.repr OS_ERR_MUTEX_DEADLOCK)))
         )
     )
  end.

Definition mutexpend  (vl: vallist):=
  mutexpend_null (|vl|) ??
  mutexpend_no_mutex_err (|vl|) ??
  mutexpend_type_err  (|vl|) ?? 
  mutexpend_idle_err  (|vl|) ??
  mutexpend_stat_err  (|vl|) ??
  mutexpend_prio_err  (|vl|) ?? (* 5:cur_prio <= pip *)
  (*mutexpend_own_err t beg res \/*)
  mutexpend_get_succ  (|vl|) ??
  ((mutexpend_block_lift  (|vl|) ??  mutexpend_block_no_lift  (|vl|)) ;; isched ;;
  (mutexpend_to (|vl|) ?? mutexpend_block_get (|vl|)))  ??
  mutexpend_pr_not_holder_err (|vl|) ?? (* 8:pip is not hold *)
  mutexpend_nest_err (|vl|) ??(* 9:ptcb is not rdy *)
  mutexpend_deadlock_err (|vl|) ?? (*  10:ptcb = cur *)
  mutexpend_msg_not_null_err (|vl|) ?? (* 11:msg != null *)
  mutexpend_cur_prio_eql_mprio_err (|vl|) ?? (* 12:cur_prio = mprio *)
  mutexpend_ptcb_prio_eql_idle_err (|vl|). (* 13:ptcb_prio = idle *) 

Definition mutexpendapi:=(mutexpend,(Tint8,Tptr OS_EVENT::Tint16::nil)).

(*mutex post*)

Definition mutexpost_null (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
       vl =  (Vnull::nil) /\
       opv =  (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
       O1 = O2
  end.

Definition mutexpost_no_mutex_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid,
       vl= (Vptr qid::nil) /\
       (
         (
           exists qls,
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid = None/\
             opv =  (Some (Vint32 (Int.repr OS_ERR_PEVENT_NO_EX)))/\
             O2=O1                                    
         )
       )
  end.


Definition mutexpost_type_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid,
       vl= (Vptr qid::nil) /\
       (
         (
           exists qls,
              get O1 absecblsid = Some (absecblist qls) /\
             (exists d, get qls qid = Some d /\
                        ~ exists x y wl, d = (absmutexsem x y,wl)
             )/\
             opv =  (Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)))/\
             O2=O1                                    
         )
       )
  end.

Definition mutexpost_no_owner_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid,
       vl= (Vptr qid::nil) /\
       (
         (
           exists qls wl x y t,
              get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid = Some (absmutexsem x y,wl) /\
             (~ exists p, y =Some  (t,p)) /\ 
             opv =  (Some (Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER)))/\
             O2=O1      
         )
       )
  end.

Definition mutexpost_nowt_return_prio_succ
           (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid,
       vl= (Vptr qid::nil) /\
       (
         (
           exists qls tls qls' tls' p p' st m t,
              get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
             
             get qls qid = Some (absmutexsem p (Some (t,p')),nil) /\
             get tls t = Some (p,st,m) /\
             tls' = set tls t (p',st,m) /\
             qls' = set qls qid (absmutexsem p None,nil) /\
             
             opv = (Some (Vint32 (Int.repr OS_NO_ERR)))/\
             O2= set ( set O1 abtcblsid (abstcblist tls') ) 
                                   absecblsid (absecblist qls')
         )
       )
  end.


Definition mutexpost_nowt_no_return_prio_succ
           (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     exists qid,
       vl= (Vptr qid::nil) /\
       (
         (
           exists qls tls qls' p p' p'' st m t,
              get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
             get qls qid = Some (absmutexsem p (Some (t,p')),nil) /\
             get tls t = Some (p'',st,m) /\
             Int.eq p'' p = false /\
             qls' = set qls qid (absmutexsem p None,nil) /\
             opv =(Some (Vint32 (Int.repr OS_NO_ERR)))/\
             O2= set O1 absecblsid (absecblist qls')
         )
       )
  end.

Definition mutexpost_exwt_return_prio_succ
           (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      exists qid,
      vl= (Vptr qid::nil) /\
      (
        (
          exists qls tls qls' tls' tls'',
            exists p p' pt st m wl t' st' m' t,
               get O1 curtid = Some (oscurt t) /\
               get O1 absecblsid = Some (absecblist qls) /\
               get O1 abstcblsid = Some (abstcblist tls) /\
              get qls qid = Some (absmutexsem p (Some (t,pt)),wl) /\
              wl <> nil /\
              GetHWait tls wl t'/\ 
              get tls t = Some (p,st,m) /\
              get tls t' = Some (p',st',m') /\
              
              tls' = set tls t (pt,st,m) /\
              tls''= set tls' t' (p',rdy,Vptr qid)/\
              qls' = set qls qid (absmutexsem p (Some (t',p')),remove_tid t' wl) /\
              
              opv = None /\
              O2= set ( set O1 abtcblsid (abstcblist tls'') ) 
                               absecblsid (absecblist qls')
        )
      )
  end.


Definition mutexpost_exwt_no_return_prio_succ
           (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      exists qid,
       vl= (Vptr qid::nil) /\
       (
         (
           exists qls tls qls' tls' t,
             exists p p' p'' pt st m wl t' st' m' ,
               get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
             
             get qls qid = Some (absmutexsem p (Some (t,pt)),wl) /\
             wl <> nil /\
             GetHWait tls wl t'/\
             Int.eq p'' p = false /\
             get tls t = Some (p'',st,m) /\
             get tls t' = Some (p',st',m') /\
             
             tls'= set tls t' (p',rdy,Vptr qid)/\
             qls' = set qls qid (absmutexsem p (Some (t',p')),remove_tid t' wl) /\
             
             opv = None /\
             O2= set ( set O1 abtcblsid (abstcblist tls') ) 
                                   absecblsid (absecblist qls')
         )
       )
  end.

Definition mutexpost_original_not_holder_err (vl: vallist) (O1: osabst) (rst : option val * osabst) :=
        match rst with
              | (opv, O2) =>
                        exists qid,
                                vl=(Vptr qid ::nil) /\
                                opv = Some (Vint32 (Int.repr OS_ERR_ORIGINAL_NOT_HOLDER))  /\
                                O2 = O1
        end.

Definition mutexpost_prio_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
     (
       exists qid qls ,
         vl= (Vptr qid::nil) /\
         (*vl=  (Vptr qid::Vint32 v::nil) /\*)
         exists tls st msg prio t p stp wl,
            get O1 curtid = Some (oscurt t) /\
            get O1 absecblsid = Some (absecblist qls) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get qls qid = Some (absmutexsem p stp,wl) /\
           get tls t = Some (prio,st,msg) /\
           Int.ltu prio p = true /\
           opv =  (Some (Vint32 (Int.repr OS_ERR_MUTEX_PRIO)))/\
           O2=O1         
     )
  end.

Definition mutexpost_wl_highest_prio_err (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
  |   (opv, O2)=>
                  exists eid els tls,
                  vl=(Vptr eid ::nil) /\
                  exists pr opr wl sometid somepr somest somemsg,
                   get O1 absecblsid = Some (absecblist els) /\
                   get O1 abstcblsid = Some (abstcblist tls) /\
                  get els eid = Some (absmutexsem pr opr, wl) /\
                  In sometid wl /\
                  get tls sometid = Some (somepr, somest, somemsg) /\
                  Int.ltu pr somepr = false /\
                  opv = (Some (Vint32 (Int.repr OS_ERR_MUTEX_WL_HIGHEST_PRIO))) /\
                  O2 = O1
  end.


Definition mutexpost (vl:vallist):=
  mutexpost_null (|vl|) ??
  mutexpost_no_mutex_err (|vl|) ??
  mutexpost_type_err (|vl|) ??
  mutexpost_no_owner_err (|vl|) ??
  mutexpost_nowt_return_prio_succ (|vl|) ??
  mutexpost_nowt_no_return_prio_succ (|vl|) ?? ((
  mutexpost_exwt_return_prio_succ (|vl|) ??
  mutexpost_exwt_no_return_prio_succ  (|vl|));;isched;; END  (Some (Vint32 (Int.repr NO_ERR))))??
  mutexpost_original_not_holder_err (|vl|) ??
  mutexpost_prio_err(|vl|) ??
  mutexpost_wl_highest_prio_err(|vl|).
                                                                  

Definition mutexpostapi:=(mutexpost,(Tint8,Tptr OS_EVENT::nil)).



(* mailbox absop *)

Definition mbox_create_err (vl: vallist) (O1 : osabst) (rst  : option val * osabst) :=
        match rst with
        | (opv, O2) =>
                        exists v,
                                (*isptr v /\*)
                                vl= (v :: nil) /\
                                opv= (Some Vnull) /\
                                O2=O1
        end.

Definition mbox_create_succ (vl: vallist) (O1 : osabst) (rst  : option val * osabst) :=
        match rst with
        | (opv, O2) =>
                        exists v eid sls sls',
                                (*isptr v /\*)
                                vl = (v:: nil) /\
                                opv = (Some (Vptr eid)) /\
                                 get O1 absecblsid = Some (absecblist sls) /\
                                EcbMod.joinsig eid ((absmbox v),(nil:list tid)) sls sls'/\
                                O2= ( set O1 absecblsid (absecblist sls')) 
        end.  

Definition mbox_create (vl : vallist) :=
        mbox_create_err (|vl|) ?? mbox_create_succ (|vl|).

Definition mbox_createapi := (mbox_create, (Tptr OS_EVENT, (Tptr Tvoid) :: nil)).

(* mbox delete *)

Definition mbox_del_null_err (vl: vallist) (O1: osabst) (rst:option val * osabst ) :=
	match rst with
	| (opv, O2) =>
			vl = Vnull::nil /\
			opv = Some (Vint32 (Int.repr MBOX_DEL_NULL_ERR)) /\
			O1 = O2
	end.

Definition mbox_del_p_not_legal_err (vl: vallist) (O1: osabst) (rst:option val * osabst ) :=
	match rst with
	|(opv, O2) => 
			exists qid,
			vl= (Vptr qid)::nil /\
			(
			exists els,
			 get O1 absecblsid = Some (absecblist els) /\
			(~ exists x wls,get els qid = Some (absmbox x ,wls) )/\
			opv = Some (Vint32 (Int.repr MBOX_DEL_P_NOT_LEGAL_ERR)) /\
			O2=O1                                    
			)
	end.

Definition mbox_del_wrong_type_err (vl: vallist) (O1: osabst) (rst:option val * osabst ) :=
    match rst with
    |(opv, O2) => 
		exists qid,
		vl= (Vptr qid)::nil /\
		(
		exists els,
		 get O1 absecblsid = Some (absecblist els) /\
		(exists d, get els qid = Some d /\
		~exists x wls, d = (absmbox x,wls)) /\
		opv = Some (Vint32 (Int.repr MBOX_DEL_WRONG_TYPE_ERR))/\
		O2=O1                                    
		)
	end.

Definition mbox_del_task_wt_err (vl: vallist) (O1: osabst) (rst:option val * osabst ) :=
    match rst with
    |(opv, O2) =>
		exists qid, 
		vl= (Vptr qid)::nil /\
		(
		exists qls t' tl x,
		 get O1 absecblsid = Some (absecblist qls) /\
		get qls qid = Some (absmbox x ,t'::tl) /\
		opv = Some (Vint32 (Int.repr MBOX_DEL_TASK_WAITING_ERR))/\
		O2=O1                                    
		)
    end.

Definition mbox_del_succ (vl: vallist) (O1: osabst) (rst:option val * osabst ) :=
    match rst with
    |(opv, O2) =>
		exists qid,
		vl= (Vptr qid)::nil /\
		(
		exists qls qls' x ,
		 get O1 absecblsid = Some (absecblist qls) /\
		get qls qid = Some (absmbox x,nil) /\
		opv = Some (Vint32 (Int.repr MBOX_DEL_SUCC))/\
		join qls' (sig qid (absmbox x,nil)) qls/\
		O2= ( set O1 absecblsid (absecblist qls')) 
		)
    end.

Definition mbox_del (vl:vallist) :=
  mbox_del_null_err (|vl|) ?? mbox_del_p_not_legal_err (|vl|) ??
   mbox_del_wrong_type_err (|vl|) ?? mbox_del_task_wt_err (|vl|) ?? mbox_del_succ (|vl|).

Definition mbox_delapi:=(mbox_del,(Tint8,Tptr OS_EVENT::nil)).

(* mbox accept *)

Definition mbox_acc_err (vl: vallist) (O1: osabst) (rst:option val * osabst ) :=
        match rst with 
                |  (opv, O2) => opv = Some Vnull /\ O2 = O1
        end.

Definition mbox_acc_succ (vl: vallist) (O1: osabst) (rst:option val * osabst ) :=
        match rst with
        |  (opv, O2) =>
                        (
                        exists qid, vl=(Vptr qid) ::nil /\ 
                        (
                        exists qls msg wl x,
                        msg = Vptr x /\
                        opv = (Some msg) /\
                         get O1 absecblsid = Some (absecblist qls) /\
                        get qls qid = Some (absmbox msg, wl) /\
                        O2 =  set O1 absecblsid (absecblist (set qls qid (absmbox Vnull, nil )))
                        )
                        )
        end.

Definition mbox_acc (vl:vallist) :=
  mbox_acc_err (|vl|) ?? mbox_acc_succ (|vl|).

Definition mbox_accapi := ( mbox_acc, (Tptr Tvoid, Tptr OS_EVENT::nil)).

(* mbox post *)

Definition mbox_post_null_err (vl: vallist) (O1: osabst) (rst: option val * osabst ) := 
        match rst with
        |(opv, O2) =>
                        exists vl', 
                        vl = Vnull::vl' /\
                        opv = (Some (Vint32 (Int.repr MBOX_POST_NULL_ERR)))/\
                        O1 = O2
        end.

Definition mbox_post_msg_null_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    |(opv, O2) =>
     exists v,
       vl = ((Vptr v)::Vnull::nil) /\
       opv = (Some (Vint32 (Int.repr MBOX_POST_MSG_NULL_ERR)))/\
       O1 = O2
  end.

Definition mbox_post_p_not_legal_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    |(opv, O2) => 
     exists qid msg ,
       vl= ((Vptr qid)::(Vptr msg) ::nil)/\
       (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
             get els qid = None /\
             opv = (Some (Vint32 (Int.repr MBOX_POST_P_NOT_LEGAL_ERR)))/\
             O2=O1                                    
       )
  end.

Definition mbox_post_wrong_type_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    |(opv, O2) => 
     exists qid msg,
       vl= ((Vptr qid)::(Vptr msg)::nil)/\
       (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
             (exists x wls,get els qid = Some (x ,wls) /\ (~exists y, x= absmbox y) )/\
             opv = (Some (Vint32 (Int.repr MBOX_POST_WRONG_TYPE_ERR)))/\
             O2=O1                                    
       )
  end.        

Definition mbox_post_full_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    |(opv, O2) => 
     exists qid msg,
       vl= ((Vptr qid)::(Vptr msg):: nil)/\
       (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
             (exists x wls,get els qid = Some (absmbox x ,wls) /\ (exists y, x= Vptr y))/\
             opv = (Some (Vint32 (Int.repr MBOX_POST_FULL_ERR )))/\
             O2=O1                                    
       )
  end.

Definition mbox_post_ex_wt_succ (vl: vallist) (O1: osabst) (rst: option val * osabst) := 
        match rst with
        |  (opv, O2) =>
                exists qid msg, 
                        vl = (Vptr qid :: Vptr msg ::nil) /\
                        (exists els tls t' wl tls' els' p st m prem,
                                 get O1 abtcblsid = Some (abstcblist tls) /\
                                 get O1 absecblsid = Some (absecblist els) /\
                                (get els qid = Some (absmbox prem, wl)) /\
                                (~ wl = nil ) /\
                                (GetHWait tls wl t') /\
                                opv = (Some (Vint32 (Int.repr MBOX_POST_SUCC))) /\
                                get tls t' = Some (p,st,m) /\
                                tls' = set tls t' (p,rdy,(Vptr msg)) /\
                                els' = set els qid (absmbox prem, (remove_tid t' wl)) /\
                                O2=  set ( set O1 abtcblsid (abstcblist tls')) absecblsid (absecblist els')
                                )
        end.
Definition mbox_post_put_mail_in_succ (vl: vallist) (O1: osabst) (rst: option val * osabst) := 
        match rst with
        |  (opv, O2) =>
                        exists qid msg, 
                        vl=(Vptr qid:: Vptr msg ::nil) /\
                        (
                                exists els,
                                         get O1 absecblsid = Some (absecblist els) /\
                                        (get els qid = Some (absmbox Vnull, nil)) /\
                                        opv = (Some (Vint32 (Int.repr MBOX_POST_SUCC ))) /\
                                        O2 =  set O1 absecblsid (absecblist (set els qid (absmbox (Vptr msg), nil))))
        end.

Definition mbox_post (vl: vallist)  := 
        mbox_post_null_err (|vl|) ?? mbox_post_msg_null_err (|vl|) ?? mbox_post_p_not_legal_err (|vl|) ?? mbox_post_wrong_type_err (|vl|) ?? mbox_post_full_err (|vl|) ?? (mbox_post_ex_wt_succ (|vl|);;isched;;END (Some (Vint32 (Int.repr NO_ERR)))) ?? mbox_post_put_mail_in_succ (|vl|).

Definition mbox_postapi := (mbox_post, (Tint8, Tptr OS_EVENT :: Tptr Tvoid :: nil)).

(* mbox pend *)
Definition mbox_pend_null_err (vl: vallist) (O1: osabst) (rst: option val * osabst):=
  match rst with
    |(opv, O2) =>
     exists vl',
       vl = (Vnull::vl') /\
       opv = (Some (Vint32 (Int.repr MBOX_PEND_NULL_ERR)))/\
       O1 = O2
  end.

Definition mbox_pend_p_not_legal_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    |(opv, O2) => 
     exists qid v ,
       vl= ((Vptr qid)::(Vint32 v) ::nil)/\
       (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
             get els qid = None /\
             opv = (Some (Vint32 (Int.repr MBOX_PEND_P_NOT_LEGAL_ERR)))/\
             O2=O1                                    
       )
  end.

Definition mbox_pend_wrong_type_err (vl: vallist) (O1: osabst) (rst: option val * osabst) :=
  match rst with
    |(opv, O2) => 
     exists qid v,
       vl= ((Vptr qid)::(Vint32 v)::nil)/\
       (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
             (exists x wls,get els qid = Some (x ,wls) /\ (~exists y, x= absmbox y) )/\
             opv = (Some (Vint32 (Int.repr MBOX_PEND_WRONG_TYPE_ERR)))/\
             O2=O1                                    
       )
  end.        

Definition mbox_pend_from_idle_err (vl: vallist) (O1: osabst) (rst: option val * osabst):=
  match rst with
    |(rv, O2) =>
     (
       exists qid v,
         vl=(Vptr qid::Vint32 v::nil) /\
         exists tls st msg t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (Int.repr OS_IDLE_PRIO,st,msg) /\
           rv = (Some (Vint32 (Int.repr MBOX_PEND_FROM_IDLE_ERR)))/\
           O2=O1         
     )
  end.

Definition mbox_pend_not_ready_err (vl: vallist) (O1: osabst) (rst: option val * osabst):=
  match rst with
    |(rv, O2) =>
     (
       exists qid v,
         vl=(Vptr qid::Vint32 v::nil) /\
         exists tls st msg prio t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (prio,st,msg) /\
           ~ st = rdy /\
           rv = (Some (Vint32 (Int.repr MBOX_PEND_NOT_READY_ERR)))/\
           O2=O1         
     )
  end.

Definition mbox_pend_inst_get_succ (vl: vallist) (O1: osabst) (rst: option val * osabst) := 
        match rst with
           |  (opv, O2) => 
                           (exists qid v, vl=((Vptr qid) ::Vint32 v ::nil) /\ 
                           (
                                exists tcbls tcbls' qls msg wl x t prio m,
                                   get O1 curtid = Some (oscurt t) /\
                                   get O1 abstcblsid = Some (abstcblist tcbls) /\
                                   get O1 absecblsid = Some (absecblist qls) /\
                                  msg = Vptr x /\
                                  get qls qid = Some (absmbox msg, wl) /\
                                  get tcbls t = Some (prio,rdy ,m)/\
                                  tcbls' =  set tcbls t (prio,rdy ,msg) /\
                                  O2 =  set ( set O1 abstcblsid (abstcblist tcbls')) absecblsid (absecblist (set qls qid (absmbox Vnull, nil ))))) /\
                                  opv = (Some (Vint32 (Int.repr MBOX_PEND_SUCC)))
        end.

Definition mbox_pend_block (vl: vallist) (O1: osabst) (rst: option val * osabst) := 
  match rst with
    |(opv, O2) =>
     (
       (
         exists qid v m,
           vl=(Vptr qid::Vint32 v::nil) /\
           exists tls tls' qls qls' wl p st t,
              get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abtcblsid = Some (abstcblist tls) /\ 
             get qls qid = Some (absmbox Vnull, wl) /\
             qls'=set qls qid (absmbox Vnull, t::wl)/\
             get tls t = Some (p,st,m) /\
             tls' = set tls t (p,wait (os_stat_mbox qid) v,Vnull)/\
             O2= set ( set O1 abtcblsid (abstcblist tls') ) 
                              absecblsid (absecblist qls')/\
             opv = None
       (*rv=blockings (Vptr qid::Vint32 v::nil) *)
       )
     )
  end.

Definition mbox_pend_timeout_err (vl: vallist) (O1: osabst) (rst: option val * osabst) := 
  match rst with
    |(rv, O2) =>
     exists qid v,
       vl=(Vptr qid::Vint32 v::nil) /\
       (
         (
           exists st tls p t,
              get O1 curtid = Some (oscurt t) /\
              get O1 abtcblsid = Some (abstcblist tls)/\
             get tls t =Some (p,st,Vnull)/\
             O1 = O2 /\
             rv= (Some (Vint32 (Int.repr MBOX_PEND_TIMEOUT_ERR)))
         )
       )
  end.

Definition mbox_pend_block_get_succ (vl: vallist) (O1: osabst) (rst: option val * osabst) := 
  match rst with
    |(rv, O2) =>
     exists qid v,
       vl= (Vptr qid::Vint32 v::nil) /\
       (
         exists tls p m st t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abtcblsid = Some (abstcblist tls)/\
           get tls t =Some (p,st,m)/\
           m <> Vnull /\
           O1 = O2 /\
           rv=(Some (Vint32 (Int.repr MBOX_PEND_SUCC)))
       )
  end.

Definition mbox_pend  (vl: vallist):=
  mbox_pend_null_err (|vl|) ?? mbox_pend_p_not_legal_err (|vl|) ?? mbox_pend_wrong_type_err (|vl|) ??
  mbox_pend_from_idle_err (|vl|) ?? mbox_pend_not_ready_err (|vl|) ?? mbox_pend_inst_get_succ (|vl|) ?? ( mbox_pend_block (|vl|) ;; isched ;; ( mbox_pend_timeout_err (|vl|) ?? mbox_pend_block_get_succ (|vl|))).

Definition mbox_pendapi:=(mbox_pend,(Tint8,Tptr OS_EVENT::Tint16::nil)).
(* end of mailbox absop *)

(*interrupts*)

Inductive tickchange : tid -> taskstatus -> EcbMod.map -> taskstatus -> EcbMod.map -> Prop:=
| rdy_change: forall t st els eid, (st=rdy) \/ ( st = wait (os_stat_sem eid) Int.zero)\/ ( st =wait (os_stat_q eid) Int.zero)\/ ( st =wait (os_stat_mbox eid) Int.zero) \/ ( st =wait (os_stat_mutexsem eid) Int.zero)  ->
                                tickchange t st els st els
| wait_change: forall t st els st' n, st =wait os_stat_time n -> (Int.eq Int.one n = false) -> st' =wait os_stat_time (Int.sub n Int.one) ->
                                        tickchange t st els st' els
| wait_rdy_change: forall t st els st', st = wait os_stat_time Int.one -> st' = rdy->
                                          tickchange t st els st' els
| waite_change: forall t st els st' eid n x, 
                  st=wait x n ->
                  (x = (os_stat_q eid) \/ x=(os_stat_sem eid) \/
                   x=(os_stat_mbox eid) \/ x=(os_stat_mutexsem eid))->
                  (Int.eq Int.one n = false /\ Int.eq Int.zero n = false ) ->
                  st' = wait x (Int.sub n Int.one) ->
                  tickchange t st els st' els
| waite_rdy_change: forall t st els els' st' eid m wl x,
                      (x = (os_stat_q eid) \/ x=(os_stat_sem eid) \/
                       x=(os_stat_mbox eid) \/ x=(os_stat_mutexsem eid)) ->
                      st =wait x Int.one -> st' = rdy ->
                      get els eid = Some (m,wl) ->
                      els' = set els eid (m,remove_tid t wl)->
                      tickchange t st els st' els'.   

Inductive tickstep': TcbMod.map -> EcbMod.map -> TcbMod.map -> EcbMod.map -> TcbMod.map -> Prop :=
  endtls_step : forall (tls:TcbMod.map) (qls : EcbMod.map),
                  tickstep' tls qls tls qls emp
  | ext_step : forall (tls tls' tls'' : TcbMod.map)
                 (els els' els'' : EcbMod.map) (t : tidspec.A) 
                 (p : priority) (st st' : taskstatus) 
                 (msg0 : msg) tls_used tls_used',
                 TcbMod.joinsig t (p, st, msg0) tls_used' tls_used ->
                 tickchange t st els st' els' ->
                 set tls t (p, st', msg0) = tls' ->
                 tickstep' tls' els' tls'' els'' tls_used'->
                 tickstep' tls els tls'' els'' tls_used.

Definition tickstep tls els tls' els' := tickstep' tls els tls' els' tls.

Definition timetick_spec (vl: vallist) (O : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O') =>
  exists tls els tm,
    exists tls' els' tm',
       get O abstcblsid = Some (abstcblist tls) /\
       get O absecblsid = Some (absecblist els)/\
       get O ostmid = Some (ostm tm) /\
      O'=
      ( set ( set ( set O absecblsid (absecblist els')) abstcblsid (abstcblist tls'))
      ostmid (ostm tm')) /\
      tm'=(Int.add tm Int.one)/\
      tickstep tls els tls' els'/\
      opv = None
  end.



Definition timetick :=
  timetick_spec (|nil|);; (isched ;; END None ?? END None).


Definition toyint_spec  (vl: vallist) (O : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O') => O = O'/\
      opv = None
  end.

Definition toyint := toyint_spec (|nil|);; (isched ;; END None ?? END None).



(* task *)


(* task create *)


(*  TASKCRE *)

Definition taskcre_err_prio_invalid (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr PRIO_ERR))) /\
      O2=O1 /\
      (exists v1 v2 v3,
         vl= (v1::v2::(Vint32 v3)::nil)/\
         Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true
      )
  end.

Definition taskcre_err_prio_already_exists (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_EXIST))) /\
      O2=O1 /\
      (
        exists v1 v2 v3,
          vl= (v1::v2::(Vint32 v3)::nil)
          (* cannot describe vholder
            exists tls,
              get O1 abstcblsid = Some (abstcblist tls) /\
              (exists tid st msg, TcbMod.get tls tid= Some (v3, st, msg)) 
          *)
      )
  end.


Definition taskcre_err_no_more_tcb (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_NO_MORE_TCB))) /\
      O2=O1
  end.

Definition taskcre_succ (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      exists v1 v2 v3,
      vl= (v1::v2::(Vint32 v3)::nil)/\
          (
            opv = None /\
            Int.lt (Int.repr 63) v3 = false /\ 
            exists tls,
              OSAbstMod.get O1 abtcblsid = Some (abstcblist tls) /\
              (~ exists t' st msg, TcbMod.get tls t'= Some (v3,st,msg)) /\
              exists tls' t',
                TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls'/\
                O2=OSAbstMod.set O1 abtcblsid (abstcblist tls')
          )
  end.


Definition scrt (vl : vallist) :=
  match vl with
    | v1 :: v2 :: (Vint32 v3) :: nil => spec_crt v1 v2 (Vint32 v3)
    | _ => spec_done None
  end.

Definition taskcrecode (vl : vallist) :=
  taskcre_err_prio_invalid (|vl|) ?? taskcre_err_prio_already_exists (|vl|) ?? taskcre_err_no_more_tcb (|vl|) ?? (scrt vl ;; (* taskcre_succ  (|vl|) ;;  *)isched ;; END (Some (Vint32 (Int.repr NO_ERR)))).

Definition taskcreapi:=(taskcrecode,(Tint8, Tptr Tvoid ::Tptr Tvoid::Tint8::nil)).


(* task delete *)

Definition taskdel_err_prio_is_idle (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_IDLE))) /\
      O2=O1 /\
      (exists v3,
         vl= ((Vint32 v3)::nil)/\
         (Int.eq (Int.repr OS_IDLE_PRIO) v3 = true  
          (* Int.eq (Int.repr OS_PRIO_SELF) v3 =  true  (* /\ current is idle *) *)
         )
      )
  end.


Definition taskdel_err_prio_invalid (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_INVALID))) /\
      O2=O1 /\
      (exists v3,
         vl= ((Vint32 v3)::nil)/\
         Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true 
         (* Int.eq (Int.repr OS_PRIO_SELF) v3 = false *)
      )
  end.

 (* placeholder or null *)
Definition taskdel_err_no_such_tcb (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_ERR))) /\
      O2=O1 /\
      (
        exists v3,
          vl= ((Vint32 v3)::nil) /\
          (exists tls,
             get O1 abstcblsid = Some (abstcblist tls) /\
             (~ exists tid st msg, TcbMod.get tls tid= Some (v3, st, msg)) 
          )
      )
  end.

Definition taskdel_err_is_some_mutex_owner (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER))) /\
      O2=O1 /\
      (
        exists v3,
          vl= ((Vint32 v3)::nil) /\
          (exists tls els eid tid t m opr wls pr,
             get O1 abstcblsid = Some (abstcblist tls) /\
             get O1 absecblsid = Some (absecblist els) /\
             get tls tid = Some (v3, t, m) /\
             get els eid = Some (absmutexsem pr (Some (tid, opr)), wls) 
          )
      )
  end.

Definition taskdel_err_has_no_next (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT))) /\
      O2=O1 
  end.

Definition isWait4Ecb x t :=
      x = os_stat_sem t \/ x = os_stat_q t \/ x = os_stat_mbox t \/ x = os_stat_mutexsem t.


Definition taskdel_clear_waitls_bit (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
      exists v3,
      vl= (Vint32 v3)::nil/\
          (
            opv = None /\
            exists tls els tid eid st msg ehb wl els' t,
              get O1 abtcblsid = Some (abstcblist tls) /\
              get O1 absecblsid = Some (absecblist els) /\
              get tls tid = Some (v3, wait st t, msg) /\
              isWait4Ecb st eid /\
              get els eid = Some (ehb, wl) /\
              els' = set els eid (ehb, (remove_tid tid wl)) /\
              O2= set O1 absecblsid (absecblist els')
          )
  end.


Definition sdel (vl : vallist) :=
  match vl with
    | (Vint32 v3) :: nil => spec_del (Vint32 v3)
    | _ => spec_done None
  end.

Definition taskdelcode (vl : vallist) :=
  taskdel_err_prio_invalid (|vl|)
                           ?? taskdel_err_no_such_tcb (|vl|)
                           ?? taskdel_err_prio_is_idle (|vl|)
                           ?? taskdel_err_is_some_mutex_owner  (|vl|)
                           ??  taskdel_err_has_no_next (|vl|)
                           ?? (sdel vl ;; isched ;; END (Some (Vint32 (Int.repr NO_ERR))))
                           ?? ( taskdel_clear_waitls_bit (|vl|) ;; sdel vl ;; isched ;; END (Some (Vint32 (Int.repr NO_ERR)))).

Definition taskdelapi:=(taskdelcode,(Tint8, Tint8::nil)).

