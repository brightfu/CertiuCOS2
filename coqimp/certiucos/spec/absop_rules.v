Require Export mbox_absop_rules.
Require Export mutex_absop_rules.
Require Export sem_absop_rules.
Require Export msgq_absop_rules.
Require Export time_absop_rules.




(*
Lemma OSTimeGet_high_level_step :
  forall P  mqls tcbls  t ct  sc,
    can_change_aop P ->
    absinfer sc  (<|| tmgetcode nil ||> ** 
    HECBList mqls ** HTCBList tcbls  ** HTime t ** HCurTCB ct ** P)
           (<|| END (Some (Vint32 t)) ||> ** 
           HECBList mqls ** HTCBList tcbls ** HTime t ** HCurTCB ct  ** P)  .
Proof.
(* Admitted. *)
(*
  intros.
  unfold tmgetcode.
  eapply absinfer_prim; eauto.
  can_change_aop_solver.
   can_change_aop_solver.
  unfolds.
  intros.
  exists O  ( END Some (Vint32 t)).
  splits.
  eapply  abs_infer_step.hmstep_merge_emp.
  sep split in H0.
  simpl in H1.
  subst .
  eapply spec_prim_step.
  constructors; auto.
  eexists; splits; eauto.

  apply eqdomO_same.
  apply eqtid_same.
  apply OSAbstMod.disj_emp_r.
  sep auto.
Qed.
*)
 
(*---------OS Time Delay-------------------------*)


Lemma  OSTimeDly_high_level_step_1 :
  forall i P,
    i = Int.zero ->
    can_change_aop P ->
    absinfer (<||tmdlycode (Vint32 i :: nil)||> ** P )
           ( <|| END None ||>  ** P).
Proof.
  intros.
  unfold tmdlycode.
  eapply absinfer_trans.
  eapply absinfer_choice1;eauto.
  eapply absinfer_prim; eauto.
  unfolds.
  intros.
  exists O (END None).
  simpl in H1.
  mytac.
  eapply hmstep_merge_emp.
  constructors.
  constructors; eauto.
  unfolds.
  splits.
  split; auto.
  intros.
  eexists; splits; eauto.
  unfolds.
  intros; split; auto.
  auto.
  eapply OSAbstMod.disj_emp_r.
  destruct s as [[[[]]]].
  simpl in H7.
  subst.
  simpl in H2.
  mytac.
  simpl substaskst in H6.
  sep auto.
Qed.


Lemma OSTimeDly_high_level_step_2 :
  forall i P ecbls tcbls t ct pri  msg,
    TcbMod.get tcbls ct = Some (pri, rdy, msg) ->
    Int.ltu Int.zero i = true ->
    can_change_aop P ->
    absinfer (<||tmdlycode (Vint32 i :: nil)||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P)
             ( <|| isched;; END None ||> ** HECBList ecbls ** HTCBList (TcbMod.set tcbls ct (pri, wait os_stat_time i, msg)) ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  unfold tmdlycode.
  eapply absinfer_trans; eauto.
  eapply absinfer_choice2.  
  can_change_aop_solver.
  2: sep auto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_choice1.  
  can_change_aop_solver.
  2: sep auto.
  can_change_aop_solver.
  eapply absinfer_trans.
  Focus 2.
  eapply absinfer_seq_end.
  3: sep auto.
  can_change_aop_solver.
  can_change_aop_solver.
  instantiate (1:=None).
  eapply absinfer_seq.
  can_change_aop_solver.
  can_change_aop_solver.
  eapply absinfer_prim;  can_change_aop_solver.
  unfolds.
  intros.
  exists  (OSAbstMod.set O abtcblsid (abstcblist (TcbMod.set tcbls ct (pri, wait os_stat_time i, msg)))).
  exists (END None).
  splits.
  eapply  specstep_merge_emp.
  sep split in H2.
  simpl in H3.
  subst gamma.
  constructors; eauto.
  unfolds.
  eexists.
  splits; eauto.
  do 4 eexists.
  splits; eauto.
  absdata_solver.
  absdata_solver.
  eapply abst_get_set_eqdom; eauto.
  absdata_solver.
   
  try solve [simpl;auto| simpl;eapply tls_get_set_indom;eauto].

  eapply tidsame_set;eauto.
  cancel_absdata.
  sep auto.
Qed.


  
Lemma OSTimeDly_high_level_step_4 :
  forall i P ecbls tcbls t ct st msg,
    TcbMod.get tcbls ct = Some (Int.repr OS_IDLE_PRIO, st, msg) ->
    can_change_aop P ->
    absinfer (<||tmdlycode (Vint32 i :: nil)||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P)
             (<|| END None ||>  ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  unfold tmdlycode.
  intros.
  eapply absinfer_trans; eauto.
  eapply absinfer_choice2.  
  can_change_aop_solver.
  2: sep auto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_choice2.  
  can_change_aop_solver.
  2: sep auto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_choice2.  
  can_change_aop_solver.
  2: sep auto.
  can_change_aop_solver.
  eapply absinfer_prim;  can_change_aop_solver.
  unfolds.
  intros.
  exists O (END None).
  sep split in H1.
  simpl in H2.
  subst gamma.
  splits.
  eapply hmstep_merge_emp.
  constructors.
  unfolds.
  do 7 eexists; splits; eauto.
  absdata_solver.
  absdata_solver.
  auto.
  auto.
  eapply OSAbstMod.disj_emp_r.
  sep auto.
Qed.


Lemma OSTimeDly_high_level_step_3 :
  forall i P ecbls tcbls t ct pri st msg,
    TcbMod.get tcbls ct = Some (pri, st, msg) ->
    ~ (st =rdy) -> 
    Int.ltu Int.zero i = true ->
    can_change_aop P ->
    absinfer (<||tmdlycode (Vint32 i :: nil)||>  ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P)
             (<|| END None ||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  unfold tmdlycode.
  intros.
  eapply absinfer_trans; eauto.
  eapply absinfer_choice2.  
  can_change_aop_solver.
  2: sep auto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_choice2.  
  can_change_aop_solver.
  2: sep auto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_choice1.  
  can_change_aop_solver.
  2: sep auto.
  can_change_aop_solver.
  eapply absinfer_prim;  can_change_aop_solver.
  unfolds.
  intros.
  exists O (END None).
  sep split in H3.
  simpl in H4.
  subst gamma.
  splits.
  eapply hmstep_merge_emp.
  constructors.
  unfolds.
  eexists; splits; eauto.
  do 5 eexists; splits; eauto.
  absdata_solver.
  absdata_solver.
  auto.
  auto.
  eapply OSAbstMod.disj_emp_r.
  sep auto.
Qed.


(*
(* ------------------- OS Q Msg Get -------------------------*)
Lemma OSQGetMsg_high_level_step : forall P prio state msg hecbls htcbls htime hcurtcb,
  TcbMod.get htcbls hcurtcb = Some (prio, state, msg) ->
  can_change_aop P ->
  absimp
     (<|| rapiop (getmsg, ((Void) ∗, nil)) nil ||>  **
      HECBList hecbls **
      HTCBList htcbls **
      HTime htime ** HCurTCB hcurtcb ** P)
     ( <|| rendop ret msg ||>  **
      HECBList hecbls **
      HTCBList (TcbMod.set htcbls hcurtcb (prio, state, Vnull))
      ** HTime htime ** HCurTCB hcurtcb ** P).
Proof.
  absimp_step 0%nat.
Qed.



(* ------------------- OS Q Accept -------------------------*)
Lemma qacc_absimp_null:forall P, can_change_aop P -> absimp
     ( <|| rapiop (qacc, (Tptr (Tvoid), Tptr OS_EVENT :: nil)) (Vnull :: nil) ||>  **
     P) (<|| rendop (Some Vnull) ||>  **
     P).
Proof.
  absimp_step 1.
Qed.


Lemma qacc_absimp_no_q:forall P mqls x, can_change_aop P ->  (~ exists a b wl,EcbMod.get mqls x = Some (absmsgq a b,wl)) -> absimp
     ( <|| rapiop (qacc, ((Tptr Tvoid), Tptr OS_EVENT :: nil)) (Vptr x :: nil) ||>  ** HECBList mqls **
     P) (<|| rendop (Some Vnull) ||>  ** HECBList mqls **
     P).
Proof.
  absimp_step 2.
Qed.

Lemma qacc_absimp_no_msg:
  forall P mqls x qmaxlen wl, 
    can_change_aop P ->  
    EcbMod.get mqls x = Some (absmsgq nil qmaxlen,wl) -> 
    absimp
      ( <|| rapiop (qacc, (Tptr Tvoid, Tptr OS_EVENT:: nil)) (Vptr x :: nil) ||>  ** 
            HECBList mqls ** P) 
      (<|| rendop (Some Vnull) ||>  ** HECBList mqls **
                    P).
Proof.
  absimp_step 3.
Qed.


Lemma qacc_absimp_get_msg:
  forall P mqls x qmaxlen wl v vl v1 v3 v4 , 
    can_change_aop P ->  
    EcbMod.get mqls x = Some (absmsgq (v::vl) qmaxlen,wl) -> 
    absimp
      ( <|| rapiop (qacc, ((Tptr Tvoid) ,Tptr OS_EVENT :: nil)) (Vptr x :: nil) ||>  ** 
            HECBList mqls **  HTCBList v1 **
      HTime v3 **
      HCurTCB v4 **
       P) 
      (<|| rendop (Some v) ||>  ** HECBList (EcbMod.set mqls x (absmsgq vl qmaxlen,wl)) **  HTCBList v1 **
      HTime v3 **
      HCurTCB v4 **
                    P).
Proof.
  absimp_step 4.
Qed.

(*-----------OS Q Post-------------------*)

Lemma qpost_absimp_null:
  forall P tl vl, 
    can_change_aop P -> 
    tl_vl_match tl vl = true ->
    absimp
     ( <|| rapiop (qpost, (Tint8, Tptr OS_EVENT :: tl)) (Vnull :: vl) ||>  **
     P) (<|| rendop (Some (V$OS_ERR_PEVENT_NULL)) ||>  **
     P).
Proof.
  absimp_step 1.
Qed.

Lemma qpost_absimp_msg_null:
  forall P v, 
    can_change_aop P -> 
    type_val_match (Tptr OS_EVENT) v = true ->
    absimp
     ( <|| rapiop (qpost, (Tint8, Tptr OS_EVENT :: Tptr Tvoid :: nil)) (v :: Vnull ::nil) ||>  **
     P) (<|| rendop (Some (Vint32 (Int.repr  OS_ERR_POST_NULL_PTR))) ||>  **
     P).
Proof.
  absimp_step 2.
Qed.

Lemma qpost_absimp_no_q:
  forall P mqls x v, 
    can_change_aop P ->  
    type_val_match (Tptr Tvoid) v = true ->
    (~ exists a b wl,EcbMod.get mqls x = Some (absmsgq a b,wl)) -> 
    absimp
      ( <|| rapiop (qpost, (Tint8, Tptr OS_EVENT :: Tptr Tvoid :: nil)) (Vptr x :: v :: nil) ||>  ** 
            HECBList mqls ** P) 
      (<|| rendop (Some (Vint32 (Int.repr MSGQ_NULL_ERR))) ||>  ** HECBList mqls ** P).
Proof.
  absimp_step 3.
Qed.

Lemma qpost_absimp_ovf:
  forall P mqls x v a b wl, 
    can_change_aop P ->  
    type_val_match (Tptr Tvoid) v = true ->
    EcbMod.get mqls x = Some (absmsgq a b,wl) ->
    Z.ge (Z_of_nat (length a)) (Int.unsigned b) ->
    absimp
      ( <|| rapiop (qpost, (Tint8, Tptr OS_EVENT :: Tptr Tvoid :: nil)) (Vptr x :: v :: nil) ||>  ** 
            HECBList mqls ** P) 
      (<|| rendop (Some (Vint32 (Int.repr MSGQ_OVF_ERR))) ||>  ** HECBList mqls ** P).
Proof.
  absimp_step 4.
Qed.


Lemma qpost_absimp_nowt_succ: 
  forall P mqls x v a b tcbls t ct, 
    can_change_aop P ->  
    type_val_match (Tptr Tvoid) v = true ->
    EcbMod.get mqls x = Some (absmsgq a b,nil) ->
    Z.lt (Z_of_nat (length a)) (Int.unsigned b) ->
    absimp
      ( <|| rapiop (qpost, (Tint8, Tptr OS_EVENT :: Tptr Tvoid :: nil)) (Vptr x :: v :: nil) ||>  ** 
            HECBList mqls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P) 
      (<|| rendop (Some (Vint32 (Int.repr NO_ERR))) ||>  ** HECBList (EcbMod.set mqls x (absmsgq (a++(v::nil)) b,nil))** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  absimp_step 5.
Qed.

Lemma qpost_absimp_exwt_succ: 
  forall P mqls x v n wl tls t ct p st m t' vl, 
    can_change_aop P ->  
    type_val_match (Tptr Tvoid) v = true ->
    EcbMod.get mqls x = Some (absmsgq vl n,wl) ->
    ~ wl=nil ->
    GetHWait tls wl t' ->
    TcbMod.get tls t' = Some (p,st,m) ->
    absimp
      ( <|| rapiop (qpost, (Tint8, Tptr OS_EVENT :: Tptr Tvoid :: nil)) (Vptr x :: v :: nil) ||>  ** 
            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<|| rendop (Some (Vint32 (Int.repr NO_ERR))) ||>  ** HECBList (EcbMod.set mqls x (absmsgq nil n,(remove_tid t' wl))) ** HTCBList (TcbMod.set tls t' (p,rdy ,v) ) ** HTime t ** HCurTCB ct ** P).
Proof.
  absimp_step 6.
  eexists.
  splits;first [absdata_solver | eauto].
  splits;first [absdata_solver | eauto].
Qed.


(*-------------OS Q Pend---------------------*)


Lemma qpend_absimp_null:
  forall P tl vl, 
    can_change_aop P -> 
    tl_vl_match tl vl = true ->
    absimp
     ( <|| rapiop (qpend, (Tint8, Tptr OS_EVENT :: tl)) (Vnull :: vl) ||>  **
     P) (<|| rendop (Some (V$OS_ERR_PEVENT_NULL)) ||>  **
     P).
Proof.
  absimp_step 1.
Qed.


Lemma qpend_absimp_no_q:
  forall P mqls x v,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->  
    (~ exists a b wl,EcbMod.get mqls x = Some (absmsgq a b,wl)) -> 
    absimp
      ( <|| rapiop (qpend, (Tint8, Tptr OS_EVENT :: Tint16 :: nil)) (Vptr x :: Vint32 v :: nil) ||>  ** 
            HECBList mqls ** P) 
      (<|| rendop (Some (Vint32 (Int.repr MSGQ_NULL_ERR))) ||>  ** HECBList mqls ** P).
Proof.
  absimp_step 2.
Qed.

Lemma qpend_absimp_get:
  forall P mqls x v msg ml p m t ct tls n wl,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    EcbMod.get mqls x = Some (absmsgq (msg::ml) n, wl) ->
    TcbMod.get tls ct = Some (p,rdy,m) ->
    absimp
      ( <|| rapiop (qpend, (Tint8, Tptr OS_EVENT :: Tint16 :: nil)) (Vptr x :: Vint32 v :: nil) ||>  ** 
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<|| rendop (Some (Vint32 (Int.repr NO_ERR))) ||>  ** HECBList (EcbMod.set mqls x (absmsgq ml n,wl)) ** HTCBList (TcbMod.set tls ct (p,rdy, msg) ) ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  absimp_id_mstep.
  branch 3.
  do 14 eexists;(first [ absdata_solver | eauto  ]);
  try (splits; (first [ absdata_solver | eauto  ])).
Qed.


Lemma qpend_absimp_block:
  forall P mqls qid v wl p m t ct tls n,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    EcbMod.get mqls qid = Some (absmsgq nil n, wl) ->
    TcbMod.get tls ct = Some (p,rdy,m) ->
    absimp
      ( <|| rapiop (qpend, (Tint8, Tptr OS_EVENT :: Tint16 :: nil)) (Vptr qid :: Vint32 v :: nil) ||>  ** 
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<||  rapiop (qpend, (Tint8, Tptr OS_EVENT :: Tint16 :: nil)) (Vptr qid :: Vint32 v :: nil) ||>  ** HECBList (EcbMod.set mqls qid (absmsgq nil n,ct::wl)) ** HTCBList (TcbMod.set tls ct (p,wait (os_stat_q qid) v, Vnull) ) ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  absimp_ib_mstep.
  branch 4.
  absop_step.
Qed.


Lemma qpend_absimp_to:
  forall P mqls qid v t ct tls st prio,
    Int.unsigned v <= 65535 ->
    TcbMod.get tls ct = Some (prio, st, Vnull) ->
    can_change_aop P ->
    absimp
      ( <|| rapiop (qpend, (Tint8, Tptr OS_EVENT :: Tint16 :: nil)) (Vptr qid :: Vint32 v :: nil) ||>  ** 
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<||  rendop (Some (Vint32 (Int.repr TIME_OUT)))||>  ** HECBList mqls  ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  introv Hx.
  introv Hh.
  intros.
  apply absimp'_imp_absimp; unfold absimp'; intros.
  sep split in H0; mytac; simpl getabsop in *; subst; exists_O_aop.
  cancel_absdata';sep auto.
  disj_solver.
  apply hmstepS_One; eapply retbd_mstep.
  eqdomO_solver.
  absdata_solver.
  absdata_solver.
  absdata_solver.
  absdata_solver.
  apply tcblistdomsubeq_true.
  apply tcblistdomsubeq_true.
  unfold qpendapi.
  auto.
  auto.
  simpl;pauto.
  unfold qpend.
  branch 5.
  absop_step.
Qed.


Lemma qpend_absimp_block_get:
  forall P mqls qid v p t ct tls m st,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    TcbMod.get tls ct = Some (p,st,m) ->
    m<>Vnull ->
    absimp
      ( <|| rapiop (qpend, (Tint8, Tptr OS_EVENT :: Tint16 :: nil)) (Vptr qid :: Vint32 v :: nil) ||>  ** 
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<||  rendop (Some (Vint32 (Int.repr NO_ERR)))||>  ** HECBList mqls  ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  introv Hv.
  intros.
  apply absimp'_imp_absimp; unfold absimp'; intros.
  sep split in H2; mytac; simpl getabsop in *; subst; exists_O_aop.
  cancel_absdata';sep auto.
  disj_solver.
  apply hmstepS_One; eapply retbd_mstep.
  eqdomO_solver.
  absdata_solver.
  absdata_solver.
  absdata_solver.
  absdata_solver.
  apply tcblistdomsubeq_true.
  apply tcblistdomsubeq_true.
  unfold qpendapi.
  auto.
  auto.
  simpl;pauto.
  unfold qpend.
  branch 6.
  absop_step.
Qed.

Ltac tl_vl_match_solver := simpl; repeat (erewrite if_true_false_eq_true_intro;eauto);
                           try eapply Zle_imp_le_bool; eauto. 


Lemma OSQPend_high_step_null :
  forall qid timeout P,
     qid = Vnull ->
     Int.unsigned timeout <= 65535 ->
     can_change_aop P ->
     absimp ( <|| rapiop qpendapi (qid :: Vint32 timeout :: nil) ||>  ** P)
              ( <|| rendop ret (V$OS_ERR_PEVENT_NULL) ||>  ** P).
Proof.
  intros.
  subst qid.
  unfold absimp.
  intros s O gamma Hs HO.
  exists O (rendop (Some (V$ OS_ERR_PEVENT_NULL))).
  split; auto. 
  split. eapply hm_stepS.
  eapply ret_mstep.
  sep split in Hs.
  eauto. auto.
  tl_vl_match_solver.
  instantiate (2 := (1%positive, Int.zero)).
  unfold qpend.
  left. 
  unfold qpend_null.
  eexists.
  split; auto.
  apply hm_stepO.
  sep split in Hs.
  sep split.
  sep auto.
  simpl; auto. 
Qed.
 

Lemma OSQPend_high_step_no_q_err :
  forall qid timeout ecbls P,
     Int.unsigned timeout <= 65535 ->
     EcbMod.get ecbls qid = None ->
     can_change_aop P ->
     absimp ( <|| rapiop qpendapi (Vptr qid :: Vint32 timeout :: nil) ||>  ** HECBList ecbls ** P)
              ( <|| rendop (Some (V$MSGQ_NULL_ERR)) ||>  ** HECBList ecbls ** P).
Proof.
  intros.
  unfold absimp.
  intros s O gamma Hs Of HO.
  exists O (rendop (Some (V$MSGQ_NULL_ERR))).
  split; auto.
  split. eapply hm_stepS.
  eapply ret_mstep.  
  sep split in Hs.
  eauto. auto.
  tl_vl_match_solver.
  instantiate (2 := (1%positive, Int.zero)).
  unfold qpend.
  right. left.
  unfold qpend_no_q_err.
  exists qid timeout.
  split; auto.
  exists ecbls.
  split.
  absdata_solver.
  split; auto.
  red. intros.
  do 3 destruct H2.
  rewrite H0 in H2.
  false.
  eapply hm_stepO.
  sep auto.
Qed.


Lemma OSQPend_high_step_get_succ :
  forall qid timeout msg ml n wl ecbls tls t tcur prio  m P,
     Int.unsigned timeout <= 65535 ->
     EcbMod.get ecbls qid = Some (absmsgq (msg :: ml) n, wl) ->
     TcbMod.get tls tcur = Some (prio, rdy, m)->
     can_change_aop P ->
     absimp  ( <|| rapiop qpendapi (Vptr qid :: Vint32 timeout :: nil) ||> ** 
                                HECBList ecbls ** HTCBList tls ** HTime t ** HCurTCB tcur ** P)
             (<|| rendop (Some (V$NO_ERR)) ||>  ** 
                                Aabsdata absecblsid (absecblist (EcbMod.set ecbls qid (absmsgq ml n, wl))) **
                                Aabsdata abtcblsid (abstcblist (TcbMod.set tls tcur (prio, rdy, msg))) ** 
                                HTime t ** HCurTCB tcur ** P).
Proof.
  intros.
  unfold qpendapi.
  eapply qpend_absimp_get;eauto.
Qed.


Lemma OSQPend_high_step_block :
  forall qid timeout wl n ecbls tls t tcur prio m P,
     Int.unsigned timeout <= 65535 ->
     EcbMod.get ecbls qid = Some (absmsgq nil n, wl) ->
     TcbMod.get tls tcur = Some (prio, rdy, m)->
     can_change_aop P ->
     absimp  ( <|| rapiop qpendapi (Vptr qid :: Vint32 timeout :: nil) ||> ** 
                                HECBList ecbls ** HTCBList tls ** HTime t ** HCurTCB tcur ** P)
             (<|| rapiop qpendapi (Vptr qid :: Vint32 timeout :: nil) ||>  ** 
                                Aabsdata absecblsid (absecblist (EcbMod.set ecbls qid (absmsgq nil n, tcur::wl))) **
                                Aabsdata abtcblsid (abstcblist (TcbMod.set tls tcur (prio, wait (os_stat_q qid) timeout, Vnull))) ** 
                                HTime t ** HCurTCB tcur ** P).
Proof.
  intros.
  unfold qpendapi.
  eapply qpend_absimp_block;eauto.
Qed.


Lemma OSQPend_high_step_to :
   forall P mqls qid v t ct tls st prio,
    Int.unsigned v <= 65535 ->
    TcbMod.get tls ct = Some (prio, st, Vnull) ->
    can_change_aop P ->
    absimp
      ( <|| rapiop (qpend, (Tint8, Tptr OS_EVENT :: Tint16 :: nil)) (Vptr qid :: Vint32 v :: nil) ||>  ** 
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<||  rendop (Some (Vint32 (Int.repr TIME_OUT)))||>  ** HECBList mqls  ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  introv Hx.
  introv Hh.
  intros.
  apply absimp'_imp_absimp; unfold absimp'; intros.
  sep split in H0; mytac; simpl getabsop in *; subst; exists_O_aop.
  cancel_absdata';sep auto.
  disj_solver.
  apply hmstepS_One; eapply retbd_mstep.
  eqdomO_solver.
  absdata_solver.
  absdata_solver.
  absdata_solver.
  absdata_solver.
  apply tcblistdomsubeq_true.
  apply tcblistdomsubeq_true.
  unfold qpendapi.
  auto.
  auto.
  simpl;pauto.
  unfold qpend.
  branch 5.
  absop_step.
Qed.



Lemma OSQPend_high_step_block_get :
  forall P mqls qid v p t ct tls m st,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    TcbMod.get tls ct = Some (p,st,m) ->
    m<>Vnull ->
    absimp
      ( <|| rapiop (qpend, (Tint8, Tptr OS_EVENT :: Tint16 :: nil)) (Vptr qid :: Vint32 v :: nil) ||>  ** 
           HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<||  rendop (Some (Vint32 (Int.repr NO_ERR)))||>  ** HECBList mqls  ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  introv Hv.
  intros.
  apply absimp'_imp_absimp; unfold absimp'; intros.
  sep split in H2; mytac; simpl getabsop in *; subst; exists_O_aop.
  cancel_absdata';sep auto.
  disj_solver.
  apply hmstepS_One; eapply retbd_mstep.
  eqdomO_solver.
  absdata_solver.
  absdata_solver.
  absdata_solver.
  absdata_solver.
  apply tcblistdomsubeq_true.
  apply tcblistdomsubeq_true.
  unfold qpendapi.
  auto.
  auto.
  simpl;pauto.
  unfold qpend.
  branch 6.
  absop_step.
Qed.

Lemma qpend_absimp_idle :
  forall P ecbls tcbls t ct st msg v x,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls ct = Some (Int.repr OS_IDLE_PRIO, st, msg) ->
    can_change_aop P ->
    absimp (<|| rapiop (qpend, (Tint8, Tptr OS_EVENT :: Tint16 :: nil)) (Vptr x :: Vint32 v :: nil) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P)
           (<|| rendop (Some (Vint32 (Int.repr MSGQ_NULL_ERR)))||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  apply absimp'_imp_absimp; unfold absimp'; intros.
  sep split in H2; mytac; simpl getabsop in *; subst; exists_O_aop.
  sep auto.
  auto.
  apply hmstepS_One; eapply retid_mstep.
  eqdomO_solver.
  absdata_solver.
  absdata_solver.
  absdata_solver.
  absdata_solver.
  apply tcblistdomsubeq_true.
  apply tcblistdomsubeq_true.
  eauto.
  eauto.
  simpl;auto.
  pauto.
  unfolds.
  branch 7.
  absop_step.
Qed.


Lemma qpend_absimp_stat_err :
  forall P ecbls tcbls t ct st msg v x prio,
    Int.unsigned v <= 65535 ->
    TcbMod.get tcbls ct = Some (prio, st, msg) ->
    ~ st = rdy ->
    can_change_aop P ->
    absimp (<|| rapiop (qpend, (Tint8, Tptr OS_EVENT :: Tint16 :: nil)) (Vptr x :: Vint32 v :: nil) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P)
           (<|| rendop (Some (Vint32 (Int.repr MSGQ_NULL_ERR)))||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  apply absimp'_imp_absimp; unfold absimp'; intros.
  sep split in H3; mytac; simpl getabsop in *; subst; exists_O_aop.
  sep auto.
  auto.
  apply hmstepS_One; eapply retid_mstep.
  eqdomO_solver.
  absdata_solver.
  absdata_solver.
  absdata_solver.
  absdata_solver.
  apply tcblistdomsubeq_true.
  apply tcblistdomsubeq_true.
  eauto.
  eauto.
  simpl;auto.
  pauto.
  unfolds.
  branch 8.
  absop_step.
Qed.
(*-------------OS Q GetMsg---------------------*)

Lemma getmsg_absimp:
  forall P mqls st p t ct tls m,
    can_change_aop P ->
    TcbMod.get tls ct = Some (p,st,m) ->
    absimp
      ( <|| rapiop (getmsg, (Tptr Tvoid,(nil:typelist)))  (nil:vallist) ||>  ** 
            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
      (<||  rendop (Some m)||>  ** HECBList mqls  ** HTCBList (TcbMod.set tls ct (p,st,Vnull) ) ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  absimp_id_mstep.
  absop_step.
Qed.


(*---------------OS Q Create--------------*)

Lemma absimp_qcre_err_return : forall P i, 
   can_change_aop P -> 
(Int.unsigned i <=? 65535 = true) -> 
absimp ( <|| rapiop (qcre, (OS_EVENT ∗, Int16u :: nil)) (Vint32 i :: nil) ||> ** P) ( <|| rendop (Some Vnull) ||> ** P).
Proof.
  absimp_step 1%nat.
Qed.


Lemma absimp_qcre_succ_return' :
  forall P i qid  qls  tcbls curtid tm,
    can_change_aop P ->
    Int.ltu ($ Q_SIZE) i  = false ->
    EcbMod.get qls qid = None  ->
    absimp ( <|| rapiop (qcre, (OS_EVENT ∗, Int16u :: nil)) (Vint32 i :: nil) ||>
                 **HECBList qls **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
           ( <|| rendop (Some (Vptr qid)) ||> **                                                                                                                 
                 HECBList (EcbMod.set qls qid (absmsgq (nil:list val)
                                                       i,
                                               nil:list tid)) **HTCBList tcbls **  HTime tm **
                 HCurTCB curtid **P).
Proof.
  intros.
  absimp_id_mstep.
  unfold Q_SIZE in *.
  unfold OS_MAX_Q_SIZE in *.
  
  Lemma true_if_else_true: forall x, x =true -> (if x then true else false) = true.
  Proof.
    intros.
    rewrite H.
    auto.
  Qed.

  apply true_if_else_true.
  apply true_if_else_true.
  apply Zle_is_le_bool.

  unfold Int.ltu in H0.
  destruct (zlt (Int.unsigned ($ 20)) (Int.unsigned i));tryfalse.
  rewrite Int.unsigned_repr in g.

  rewrite int16_max_unsigned_val.
  omega.
  rewrite max_unsigned_val.
  split;omega.

  branch 2.
  absop_step.
Qed.



Lemma absimp_qcre_succ_return:
  forall P i qid  qls qls' tcbls curtid tm,
    can_change_aop P ->
    Int.ltu ($ Q_SIZE) i  = false ->
    EcbMod.joinsig qid (absmsgq (nil:list val)
                                i,
                        nil:list tid) qls qls' ->
    absimp ( <|| rapiop (qcre, (OS_EVENT ∗, Int16u :: nil)) (Vint32 i :: nil) ||>
                 **HECBList qls **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
           ( <|| rendop (Some (Vptr qid)) ||> **                                                                                                                 
                 HECBList qls'**HTCBList tcbls **  HTime tm **
                 HCurTCB curtid **P).
Proof.
  intros.
  apply joinisig_get_none in H1.
  destruct H1;subst.
  eapply absimp_qcre_succ_return';eauto.
Qed.

(*------------------OSQ Del-----------------------*)

Lemma absimp_qdel_err1_return : forall P , 
can_change_aop P ->
absimp (<|| rapiop (qdel, (Int8u, OS_EVENT∗ :: nil)) (Vnull :: nil) ||> ** P) ( <|| rendop (Some  (V$ OS_ERR_PEVENT_NULL)) ||> ** P).
Proof.
  absimp_step 1%nat.
Qed.






Lemma absimp_qdel_err2_return : forall x a P , 
                                  can_change_aop P ->
                                  ~ (exists x0 y wls, EcbMod.get x a = Some (absmsgq x0 y, wls)) ->
absimp (<|| rapiop (qdel, (Int8u, OS_EVENT∗ :: nil)) (Vptr a :: nil) ||> ** HECBList x **
            P) ( <|| rendop (Some  (V$ OS_ERR_PEVENT_NULL)) ||> ** HECBList x ** P).
Proof.
   absimp_step 2%nat.
Qed.

Lemma absimp_qdel_succ_return :
  forall ecbls ecbls' x y a P tid tcbls t, 
    can_change_aop P ->
    EcbMod.get ecbls a = Some (absmsgq x y, nil) ->
    EcbMod.join ecbls' (EcbMod.sig a (absmsgq x y, nil)) ecbls -> 
    absimp (<|| rapiop (qdel, (Int8u, OS_EVENT∗ :: nil)) (Vptr a :: nil) ||> ** HECBList ecbls **
              HTCBList tcbls ** HTime t **  HCurTCB tid **  P) ( <|| rendop (Some  (V$NO_ERR)) ||> **
                         HECBList ecbls' ** HTCBList tcbls ** HTime t **  HCurTCB tid  ** P).
Proof.
  intros.
  apply absimp'_imp_absimp; unfold absimp'; intros.
  exists (OSAbstMod.set O absecblsid (absecblist ecbls')).
  exists ( rendop ret (V$NO_ERR)).
  splits; auto.
  cancel_absdata'.
  sep auto.
  disj_solver.
  apply hmstepS_One; eapply retid_mstep.
  eqdomO_solver.
  absdata_solver.
  eapply get_set_idneq; [ disj_solver | absdata_solver | auto ].
  absdata_solver.
  eapply get_set_idneq; [ disj_solver | absdata_solver | auto ].
  try (eapply tcblistdomsubeq_set; eauto );
    apply tcblistdomsubeq_true.
  try (eapply tcblistdomsubeq_set; eauto );
    apply tcblistdomsubeq_true.
  sep split in H2.
  eauto.
  eauto.
  simpl; pauto.
  try instantiate ( 1 := (1%positive, Int.zero) ) ; unfolds .
  branch 5.
  absop_step.
Qed.


Lemma absimp_qdel_err3_return : forall x a P , 
                                  can_change_aop P ->
 (exists d,
  EcbMod.get x a = Some d /\ ~ (exists x y wls, d = (absmsgq x y, wls))) ->
absimp (<|| rapiop (qdel, (Int8u, OS_EVENT∗ :: nil)) (Vptr a :: nil) ||> ** HECBList x **
            P) ( <|| rendop (Some  (V$ OS_ERR_EVENT_TYPE)) ||> ** HECBList x ** P).
Proof.
  absimp_step 3%nat.
Qed.

Lemma absimp_qdel_err4_return : forall x a P , 
                                  can_change_aop P ->
 (exists  t' tl z y,
    EcbMod.get x a = Some  (absmsgq z y, t' :: tl)) ->
absimp (<|| rapiop (qdel, (Int8u, OS_EVENT∗ :: nil)) (Vptr a :: nil) ||> ** HECBList x **
            P) ( <|| rendop (Some  (V$ OS_ERR_TASK_WAITING)) ||> ** HECBList x ** P).
Proof.
  absimp_step 4%nat.
Qed.


(* ------------------- OS MUTEX Accept -------------------------*)
Lemma mutexacc_null_absimp:forall P, can_change_aop P -> absimp
     ( <|| rapiop (mutexacc, (Tint8, Tptr OS_EVENT :: nil)) (Vnull :: nil) ||>  **
     P) (<|| rendop (Some (V$0)) ||>  **
     P).
Proof.
  absimp_step 1.
Qed.


Lemma mutexacc_no_mutex_err_absimp:
  forall P mqls x,
    can_change_aop P ->
    (~ exists a b wl,EcbMod.get mqls x = Some (absmutexsem a b,wl)) ->
    absimp
      ( <|| rapiop (mutexacc, (Tint8, Tptr OS_EVENT :: nil)) (Vptr x :: nil) ||>  ** HECBList mqls **
            P)
      (<|| rendop (Some (V$0)) ||>  ** HECBList mqls **
     P).
Proof.
  absimp_step 2.
Qed.

Lemma mutexacc_no_available_absimp:
  forall P mqls x wl p o, 
    can_change_aop P ->  
    EcbMod.get mqls x = Some (absmutexsem p (Some o),wl)-> 
    absimp
      ( <|| rapiop (mutexacc, (Tptr Tvoid, Tptr OS_EVENT:: nil)) (Vptr x :: nil) ||>  ** 
            HECBList mqls ** P) 
      (<|| rendop (Some (V$0)) ||>  ** HECBList mqls **
                    P).
Proof.
  absimp_step 3.
Qed.


Lemma mutexacc_succ_absimp:
  forall P mqls x wl v1 v3 ct p pt st m, 
    can_change_aop P ->  
    EcbMod.get mqls x = Some (absmutexsem p None,wl) ->
    TcbMod.get v1 ct = Some (pt,st,m) ->
    absimp
      ( <|| rapiop (mutexacc, ((Tptr Tvoid) ,Tptr OS_EVENT :: nil)) (Vptr x :: nil) ||>  ** 
            HECBList mqls **  HTCBList v1 **
      HTime v3 **
      HCurTCB ct **
       P) 
      (<|| rendop (Some (V$1)) ||>  ** HECBList (EcbMod.set mqls x (absmutexsem p (Some (ct,pt)),wl)) **  HTCBList v1 **
      HTime v3 **
      HCurTCB ct **
                    P).
Proof.
  absimp_step 4.
Qed.


(*------------------- OS MUTEX Create -------------------------*)

Lemma mutexcre_error_absimp :
  forall P i, 
    can_change_aop P -> 
    (Int.unsigned i <=? 255 = true) -> 
    absimp ( <|| rapiop (mutexcre, (OS_EVENT ∗, Int8u :: nil)) (Vint32 i :: nil) ||> ** P)
           ( <|| rendop (Some Vnull) ||> ** P).
Proof.
  absimp_step 1%nat.
Qed.

Lemma mutexcre_succ_absimp :
  forall P i qid  qls  tcbls curtid tm,
    can_change_aop P ->
    (Int.unsigned i <=? 255 = true) -> 
    prio_available i tcbls ->
    Int.ltu i (Int.repr OS_LOWEST_PRIO)= true ->
    EcbMod.get qls qid = None  ->
    absimp ( <|| rapiop (mutexcre, (OS_EVENT ∗, Int8u :: nil)) (Vint32 i :: nil) ||>
                 **HECBList qls **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
           ( <|| rendop (Some (Vptr qid)) ||> **                                                                                                                 
                 HECBList (EcbMod.set qls qid (absmutexsem i
                                                       None,
                                               nil:list tid)) **HTCBList tcbls **  HTime tm **
                 HCurTCB curtid **P).
Proof.
  absimp_step 2.
Qed.

(*------------------- OS MUTEX Delete---------------------------*)


Lemma mutexdel_null_absimp:
  forall P , 
    can_change_aop P ->
    absimp (<|| rapiop (mutexdel, (Int8u, OS_EVENT∗ :: nil)) (Vnull :: nil) ||> ** P)
           ( <|| rendop (Some  (V$ OS_ERR_PEVENT_NULL)) ||> ** P).
Proof.
  absimp_step 1%nat.
Qed.

Lemma mutexdel_no_mutex_err_absimp:
  forall x a P , 
    can_change_aop P ->
    EcbMod.get x a = None ->
    absimp (<|| rapiop (mutexdel, (Int8u, OS_EVENT∗ :: nil)) (Vptr a :: nil) ||> ** HECBList x ** P)
           ( <|| rendop (Some  (V$ OS_ERR_PEVENT_NO_EX)) ||> ** HECBList x ** P).
Proof.
   absimp_step 2%nat.
Qed.

Lemma mutexdel_type_err_absimp:
  forall ecbls a P X tcbls tm curtid, 
    can_change_aop P ->
    EcbMod.get ecbls a = Some X ->
    (~ exists x y wl, X = (absmutexsem x y, wl))->
    absimp (<|| rapiop (mutexdel, (Int8u, OS_EVENT∗ :: nil)) (Vptr a :: nil) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
           ( <|| rendop (Some  (V$OS_ERR_EVENT_TYPE)) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
Proof.
  absimp_step 3.
Qed.


Lemma mutexdel_ex_wt_err_absimp:
  forall x a P p o t tl, 
    can_change_aop P ->
    EcbMod.get x a = Some (absmutexsem p o,t::tl)->
    absimp (<|| rapiop (mutexdel, (Int8u, OS_EVENT∗ :: nil)) (Vptr a :: nil) ||> ** HECBList x ** P)
           ( <|| rendop (Some  (V$ OS_ERR_TASK_WAITING)) ||> ** HECBList x ** P).
Proof.
  absimp_step 4%nat.
Qed.



Lemma mutexdel_succ_absimp:
  forall x a P z y x' tid t tcbls, 
    can_change_aop P ->
    EcbMod.get x a = Some (absmutexsem z y, nil) ->
    EcbMod.join x' (EcbMod.sig a (absmutexsem z y, nil)) x ->
    absimp (<|| rapiop (mutexdel, (Int8u, OS_EVENT∗ :: nil)) (Vptr a :: nil) ||> **
                HECBList x ** HTCBList tcbls ** HTime t **  HCurTCB tid  ** P)
           ( <|| rendop (Some  (V$ NO_ERR)) ||> ** HECBList x' ** HTCBList tcbls **
                 HTime t **  HCurTCB tid  ** P).
Proof.
  intros.
  apply absimp'_imp_absimp; unfold absimp'; intros.
  exists (OSAbstMod.set O absecblsid (absecblist x')).
  exists ( rendop ret (V$NO_ERR)).
  splits; auto.
  cancel_absdata'.
  sep auto.
  disj_solver.
  apply hmstepS_One; eapply retid_mstep.
  eqdomO_solver.
  absdata_solver.
  eapply get_set_idneq; [ disj_solver | absdata_solver | auto ].
  absdata_solver.
  eapply get_set_idneq; [ disj_solver | absdata_solver | auto ].
  try (eapply tcblistdomsubeq_set; eauto );
    apply tcblistdomsubeq_true.
  try (eapply tcblistdomsubeq_set; eauto );
    apply tcblistdomsubeq_true.
  sep split in H2.
  eauto.
  eauto.
  simpl; pauto.
  try instantiate ( 1 := (1%positive, Int.zero) ) ; unfolds .
  branch 5.
  absop_step.
Qed.

(*--------------------OS MUTEX Pend----------------------------*)



Lemma mutexpend_null_absimp:
  forall P tl vl, 
    can_change_aop P ->
    tl_vl_match tl vl = true ->
    absimp (<|| rapiop (mutexpend, (Int8u, OS_EVENT∗ :: tl)) (Vnull :: vl) ||> ** P)
           ( <|| rendop (Some  (V$ OS_ERR_PEVENT_NULL)) ||> ** P).
Proof.
  absimp_step 1%nat.
Qed.

Lemma mutexpend_no_mutex_err_absimp:
  forall x a P v, 
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    EcbMod.get x a = None ->
    absimp (<|| rapiop (mutexpend, (Int8u, OS_EVENT∗ :: Tint16 :: nil)) (Vptr a ::Vint32 v:: nil) ||> ** HECBList x ** P)
           ( <|| rendop (Some  (V$ OS_ERR_PEVENT_NO_EX)) ||> ** HECBList x ** P).
Proof.
  absimp_step 2.
Qed.


Lemma mutexpend_type_err_absimp:
  forall ecbls a P X tcbls tm curtid v,
    Int.unsigned v <= 65535 ->
    can_change_aop P ->
    EcbMod.get ecbls a = Some X ->
    (~ exists x y wl, X = (absmutexsem x y, wl))->
    absimp (<|| rapiop (mutexpend, (Int8u, OS_EVENT∗ :: Tint16 :: nil)) (Vptr a :: Vint32 v :: nil) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P)
           ( <|| rendop (Some  (V$OS_ERR_EVENT_TYPE)) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
Proof.
  absimp_step 3.
Qed.

*)

(*-------------------------------------------------------------*)
Ltac hoare_forward_abscsq step:=
  hoare_abscsq;[ eapply step;[can_change_aop_solver | simpl;pauto] | ].  

Close Scope code_scope.                                                                                                                                                                                  

*)
