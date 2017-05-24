Require Import include_frm.
Require Import sep_auto.

Ltac join_emp_eq_sub :=
  match goal with
    | H: join _ empabst _ |- _ => apply map_join_emp'  in H; subst; join_emp_eq_sub
    | H: join empabst _ _ |- _ => apply map_join_emp'' in H; subst; join_emp_eq_sub
    | _ => auto
  end.
(* in sep auto *)
Import DeprecatedTactic.

Theorem rete_rule' :
  forall (Spec : funspec) (I : Inv) (r : option val -> asrt)
          (p : asrt) (v : val) (e : expr) 
         (t: type) sc li tid,
    p ==> Rv e @ t == v ->
    p ==> r (Some v) ->
    {|Spec , sc,  li, I, r, Afalse|} |- tid {{p}}srete e {{Afalse}}.
Proof.
  intros.
  eapply rete_rule .
  intros.
  split; eauto.
Qed.


Notation ret_rule' := ret_rule.
Notation iret_rule' := iret_rule.


Theorem call_rule' :
  forall (f : fid)
         Spec
         (I : Inv) (r : retasrt) (ri : asrt)
          (pre : fpre) 
         (post : fpost) (p P: asrt) (el : exprlist) 
         (vl : vallist) (tp : type) 
         (tl : typelist) (logicl:list logicvar) sc li tid,
    Spec f = Some (pre, post, (tp, tl)) ->
    P ==> Rvl el @ tl == vl ->
    P ==> PRE  [pre, vl,logicl,tid] ** p ->
    GoodFrm p ->
    EX v , POST [post, vl, v, logicl,tid] ==>
                            EX lg : list logicvar, p_local li tid lg ** Atrue ->
   PRE [pre, vl, logicl, tid] ==> EX lg : list logicvar, p_local li tid lg ** Atrue  ->
    tl_vl_match tl vl =true ->
    {|Spec , sc , li, I, r, ri|} |- tid
                           {{ P}}
                           scall f el
                           {{ EX v,  POST  [post, vl, v,logicl,tid] ** p}}.
Proof.
  intros.
  eapply call_rule;eauto.
  intros.
  apply H4 in H6.
  unfolds CurLINV.
  sep auto.
  intros.
  apply H3 in H6.
  unfold CurLINV.
  sep auto.
Qed.


Theorem calle_rule' :
  forall (f : fid) (e : expr) (l : addrval)
        Spec (I : Inv) 
         (r : retasrt) (ri : asrt) 
         (pre : fpre) (post : fpost) 
         (p P : asrt) (el : exprlist) (v' : val) 
         (vl : vallist) (tp : type) 
         (tl : typelist) logicl sc li tid,
    Spec f = Some (pre, post, (tp, tl)) ->
    P ==> PRE  [pre, vl,logicl,tid] ** PV l @ tp |-> v' ** p ->
    GoodFrm p ->
    retpost post ->
    P ==> Rvl el @ tl == vl ->
    PV l @ tp |-> v' ** p ==> Lv e @ tp == l ->
    tl_vl_match tl vl =true ->
    EX v , POST [post, vl, v, logicl,tid] ==>
                            EX lg : list logicvar, p_local li tid lg ** Atrue ->
    PRE [pre, vl, logicl, tid] ==> EX lg : list logicvar, p_local li tid lg ** Atrue  ->
    {|Spec , sc , li, I , r, ri|} |- tid
                           {{ P }}
                           scalle e f el
                           {{EX v,  POST  [post, vl, Some v,logicl,tid] ** PV l @ tp |-> v ** p}}.
Proof.
  intros.
  eapply calle_rule;eauto.
  intros.
  apply H7 in H8.
  unfolds CurLINV.
  sep auto.
  intros.
  apply H6 in H8.
  unfold CurLINV.
  sep auto.
Qed.

Theorem calle_rule_lvar' :
  forall (f : fid)  (x : var)
         Spec (I : Inv) 
         (r : retasrt) (ri : asrt) 
         (pre : fpre) (post : fpost) 
         (p P : asrt) (el : exprlist) (v' : val) 
         (vl : vallist)  (tp : type) 
         (tl : typelist) logicl sc li tid,
    Spec f = Some (pre, post, (tp, tl)) ->
    P ==> Rvl el @ tl == vl ->
    P ==> PRE  [pre, vl, logicl,tid] ** LV x @ tp |-> v' ** p ->
    GoodFrm p ->
    retpost post ->
    tl_vl_match tl vl =true ->
    ( EX v : option val, POST [post, vl, v, logicl, tid]   ==> EX lg, p_local li tid lg ** Atrue) ->
    PRE [pre, vl, logicl, tid] ==> EX lg : list logicvar, p_local li tid lg ** Atrue  ->
    {|Spec , sc, li, I, r, ri|} |- tid
                           {{  P }}
                           scalle (evar x) f el
                           {{EX v,  POST  [post, vl, Some v,logicl,tid] ** LV x @ tp |-> v ** p}}.
Proof.
  intros.
  eapply calle_rule_lvar; eauto.
  intros.
  apply H6 in H7.
  unfolds CurLINV.
  sep auto.
  intros.
  apply H5 in H7.
  unfold CurLINV.
  sep auto.
Qed.


Theorem forward_rule1 :
  forall Spec I r ri p q q' s sc li tid,
    q ==> q' ->
    {|Spec , sc, li, I, r, ri|} |- tid {{p}}s {{q}} ->
    {|Spec , sc, li, I, r, ri|} |- tid {{p}}s {{q'}}.
Proof.
  intros.
  eapply conseq_rule; eauto.
Qed.

Theorem forward_rule2 :
  forall Spec I r ri  p q q' s sc li tid,
    {|Spec , sc, li, I, r, ri|} |- tid {{p}}s {{q}} ->
    q ==> q' ->
    {|Spec , sc, li, I, r, ri|} |- tid {{p}}s {{q'}}.
Proof.
  intros.
  eapply conseq_rule; eauto.
Qed.

Theorem backward_rule1 :
  forall Spec I r ri  p p' q s sc li tid,
    p' ==> p ->
    {|Spec, sc, li, I, r, ri|} |- tid {{p}}s {{q}} ->
    {|Spec, sc, li, I, r, ri|} |- tid {{p'}}s {{q}}.
Proof.
  intros.
  eapply conseq_rule; eauto.
Qed.

Theorem backward_rule2 :
  forall Spec I r ri  p p' q s sc li tid,
    {|Spec , sc, li, I, r, ri|} |- tid {{p}}s {{q}} ->
    p' ==> p ->
    {|Spec , sc, li, I, r, ri|} |- tid {{p'}}s {{q}}.
Proof.
  intros.
  eapply conseq_rule; eauto.
Qed.

Theorem forward_rule3 :
  forall Spec I r ri  p q q' R s sc li tid,
    q ==> q' ->
    {|Spec , sc, li, I, r, ri|} |- tid {{p }}s {{q //\\ R}} ->
    {|Spec , sc, li, I, r, ri|} |- tid {{p }}s {{q' //\\ R}}.
Proof.
  intros.
  eapply conseq_rule.
  eauto.
  eapply aconj_mono; eauto.
  auto.
Qed.

Theorem forward_rule4 :
  forall Spec I r ri  p q q' R s sc li tid,
    {|Spec , sc, li, I, r, ri|} |- tid {{p}}s {{q //\\ R}} ->
    q ==> q' ->
    {|Spec , sc, li, I, r, ri|} |- tid {{p}}s {{q'//\\R}}.
Proof.
  intros.
  eapply conseq_rule.
  eauto.
  eapply aconj_mono; eauto.
  auto.
Qed.

Theorem backward_rule3 :
  forall Spec I r ri  p p' q R s sc li tid,
    p' ==> p ->
    {|Spec, sc, li, I, r, ri|} |- tid {{p //\\ R}}s {{q}} ->
    {|Spec, sc, li, I, r, ri|} |- tid {{p'//\\R}}s {{q}}.
Proof.
  intros.
  eapply conseq_rule.
  eapply aconj_mono; eauto.
  eauto.
  auto.
Qed.

Theorem backward_rule4 :
  forall Spec I r ri  p p' q R s sc li tid,
    {|Spec, sc, li, I, r, ri|} |- tid {{p //\\ R}}s {{q}} ->
    p' ==> p ->
    {|Spec, sc, li, I, r, ri|} |- tid {{p' //\\ R}}s {{q}}.
Proof.
  intros.
  eapply conseq_rule.
  eapply aconj_mono; eauto.
  eauto.
  auto.
Qed.


Theorem frame_rule' : 
  forall (Spec : funspec) (I : Inv) 
          (p q frm : asrt) (s : stmts) 
         (aop aop' : absop) r ri sc li tid,
    GoodI I sc li ->
    GoodStmt' s ->
    GoodFrm frm ->
    p ==> EX lg, p_local li tid lg ** Atrue ->
    {|Spec, sc, li, I, arfalse, Afalse|} |- tid {{ <|| aop ||> ** p }}s {{ <|| aop' ||> ** q }} ->
                                   {|Spec, sc, li, I, r, ri|} |- tid
                                                                    {{ <|| aop ||> ** frm ** p }}s
                                                                    {{ <|| aop' ||> ** frm ** q }}.
Proof.
  intros.
  eapply retspec_intro_rule;eauto.
  eapply conseq_rule with (p :=  <|| aop ||>  ** p ** frm) (q :=  <|| aop' ||>  ** q ** frm); intros.
  sep auto.
  sep auto.
  apply frame_rule; auto.
  intros.
  apply H2 in H4.
  unfold CurLINV.
  sep auto.
Qed.


Theorem frame_rule_all' : 
  forall (Spec : funspec) (I : Inv) 
          (r : retasrt) (ri p q p' frm : asrt)
         (s : stmts) (aop : absop) sc li tid,
    GoodI I sc li ->
    GoodStmt' s ->
    GoodFrm frm ->
    p ==>  <|| aop ||> ** p'  ->
    p ==> EX lg, p_local li tid lg ** Atrue ->
    {|Spec, sc, li, I, r, ri|} |- tid {{p}}s {{q}} ->
                         {|Spec, sc, li, I, fun v : option val => r v ** frm,
                                                           ri ** frm|} |- tid {{ frm ** p }}s {{ frm ** q }}.
Proof.
  intros.
  eapply conseq_rule; intros.
  sep comm in H5; exact H5.
  sep comm; exact H5.
  eapply frame_rule_all; eauto.
  intros.
  apply H3 in H5.
  unfold CurLINV.
  sep auto.
Qed.

Theorem assign_rule' :
  forall (Spec : funspec) (I : Inv) 
         (r : retasrt) (ri : asrt) 
         (p : asrt) (e1 e2 : expr) (l : addrval) 
         (v1 v2 : val) (tp1 tp2 : type) 
         (aop : absop) sc li tid,
    assign_type_match tp1 tp2 ->
    PV l @ tp1 |-> v1 ** p ==> Lv e1 @ tp1 == l //\\ Rv e2 @ tp2 == v2 ->
    (p ** PV l @ tp1 |-> v2 ==>  EX lg, p_local li tid lg ** Atrue) ->
    {|Spec, sc, li, I, r, ri|} |- tid
                           {{ <|| aop ||> ** PV l @ tp1 |-> v1 ** p }}
                           sassign e1 e2 {{ <|| aop ||> ** PV l @ tp1 |-> v2 ** p }}.
Proof.
  intros.
  eapply conseq_rule with (p:=  <|| aop ||> ** p ** PV l @ tp1 |-> v1 ) (q:=  <|| aop ||> ** p ** PV l @ tp1 |-> v2 ); intros.
  sep auto.
  sep auto.
  eapply assign_rule; eauto.
  intros.
  sep comm in H2.
  apply H0 in H2.
  auto.
  intros.
  apply H1 in H2.
  unfold CurLINV.
  sep auto.
Qed.

Theorem encrit1_rule' :
  forall Spec I r ri  i isr is cs frm aop p sc li tid ,
    p ==> Aisr isr ** Aie true ** Ais is ** Acs cs ** ATopis i ** [| i <= INUM |] ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    {|Spec, sc, li, I, r, ri|} |- tid 
                 {{ <|| aop ||> ** p }} sprim encrit
                 {{ <|| aop ||> ** Aisr isr ** Aie false ** Ais is ** Acs (true::cs) ** invlth_isr I 0 i ** frm }}.
Proof.
  intros.
  eapply backward_rule1 with (p := <|| aop ||> ** OS [ isr, true, is, cs ] ** ATopis i ** [| i <= INUM |] ** frm ).
  intros.
  sep auto; apply H in H2; sep auto || sep pure.
  eapply forward_rule1 with (q := <|| aop ||>  ** OS  [isr, false, is, true :: cs] ** invlth_isr I 0 i ** frm).
  sep auto.
  eapply encrit1_rule;eauto.
Qed.



Theorem encrit2_rule' :
  forall Spec I r ri isr is cs frm aop p sc li tid,
    p ==> Aisr isr ** Aie false ** Ais is ** Acs cs ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    {|Spec, sc, li, I, r, ri|} |- tid 
                 {{  <|| aop ||> ** p }} sprim encrit
                 {{  <|| aop ||> ** Aisr isr ** Aie false ** Ais is ** Acs (false::cs) ** frm }}.
Proof.
  intros.
  apply backward_rule1 with (<|| aop ||> ** OS [isr,false,is,cs] ** frm).
  intros.
  sep auto; apply H in H2; sep auto || sep pure.
  apply forward_rule1 with (<|| aop ||> ** OS [isr,false,is,false::cs] ** frm ).
  sep auto.
  eapply encrit2_rule;eauto.
Qed.

Theorem excrit1_rule' :
  forall Spec I r ri i isr is cs frm aop p sc li tid lg,
    p ==> Aisr isr ** Aie false ** Ais is ** Acs (true::cs) ** ATopis i ** invlth_isr I 0 i ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    frm  ==>  p_local li tid lg ** Atrue ->
    {|Spec, sc, li, I, r, ri|} |- tid 
                 {{ <|| aop ||> ** p }} sprim excrit
                 {{ <|| aop ||> ** Aisr isr ** Aie true ** Ais is ** Acs cs ** frm }}.
Proof.
  intros.
  eapply backward_rule1 with (<|| aop ||>  ** OS  [isr, false, is, true :: cs] ** ATopis i ** invlth_isr I 0 i ** frm).
  intros.
  sep auto; apply H in H3; sep auto || sep pure.
  eapply forward_rule1 with (<|| aop ||> ** OS  [isr, true, is, cs] ** frm).
  sep auto.
  eapply excrit1_rule;eauto.
  intros.
  apply H2 in H3.
  unfold CurLINV.
  sep auto.
Qed.

Theorem excrit2_rule' :
  forall Spec I r ri isr is cs frm aop p sc li tid,
    p ==> Aisr isr ** Aie false ** Ais is ** Acs (false::cs) ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    {|Spec, sc, li, I, r, ri|} |- tid 
                 {{ <|| aop ||> ** p }} sprim excrit
                 {{ <|| aop ||> ** Aisr isr ** Aie false ** Ais is ** Acs cs ** frm }}.
Proof.
  intros.
  eapply backward_rule1 with (<|| aop ||>  ** OS [isr,false,is,false::cs] ** frm).
  intros.
  sep auto; apply H in H2; sep auto || sep pure.
  eapply forward_rule1 with ( <|| aop ||> ** OS [isr,false,is,cs] ** frm).
  sep auto.
  eapply excrit2_rule;eauto.
Qed.

Theorem cli1_rule' :
  forall (Spec : funspec) (I : Inv) (r : retasrt) 
         (ri : asrt)  (isr : isr) 
         (is : is) (i : hid) (aop : absop) frm p sc li tid,
    p ==> Aisr isr ** Aie true ** Ais is ** Acs nil ** ATopis i ** [|i <= INUM|] ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    {|Spec, sc, li, I, r, ri|} |- tid
                           {{ <|| aop ||> ** p }}sprim cli
                           {{ <|| aop ||> ** Aisr isr ** Aie false ** Ais is ** Acs nil ** invlth_isr I 0 i ** frm }}.
Proof.
  intros.
  apply backward_rule1 with (<|| aop ||> ** OS  [isr, true, is, nil] ** ATopis i ** [|i <= INUM|] ** frm); intros.
  sep auto; apply H in H2; sep auto || sep pure.
  apply forward_rule1 with (<|| aop ||> ** OS  [isr, false, is, nil] ** invlth_isr I 0 i ** frm).
  sep auto.
  eapply cli1_rule;eauto.
Qed.

Theorem cli2_rule' :
  forall (Spec : funspec) (I : Inv) (r : retasrt) 
         (ri : asrt) (isr : isr) 
         (is : is) (aop : absop) p frm sc li tid,
    p ==> Aisr isr ** Aie false ** Ais is ** Acs nil ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    {|Spec, sc, li, I, r, ri|} |- tid
                           {{ <|| aop ||> ** p }}
                           sprim cli {{ <|| aop ||> ** Aisr isr ** Aie false ** Ais is ** Acs nil ** frm }}.
Proof.
  intros.
  apply backward_rule1 with (<|| aop ||> ** OS  [isr, false, is, nil] ** frm ); intros.
  sep auto; apply H in H2; sep auto || sep pure.
  apply forward_rule1 with (<|| aop ||> ** OS  [isr, false, is, nil] ** frm); intros.
  sep auto.
  eapply cli2_rule;eauto.
Qed.

Theorem sti1_rule' :
  forall (Spec : funspec) (I : Inv) (r : retasrt) 
         (ri : asrt)  (isr : isr) 
         (i : hid) (is : is) (aop : absop) p frm sc li tid lg,
    p ==> Aisr isr ** Aie false ** Ais is ** Acs nil ** ATopis i ** invlth_isr I 0 i ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    frm ==>  p_local li tid lg ** Atrue ->
    {|Spec, sc, li, I, r, ri|} |- tid
                           {{ <|| aop ||> ** p }}sprim sti
                           {{ <|| aop ||> ** Aisr isr ** Aie true ** Ais is ** Acs nil ** frm }}.
Proof.
  intros.
  eapply backward_rule1 with (<|| aop ||> ** OS  [isr, false, is, nil] ** ATopis i ** invlth_isr I 0 i ** frm); intros.
  sep auto; apply H in H3; sep auto || sep pure.
  eapply forward_rule1 with (<|| aop ||> ** OS  [isr, true, is, nil] ** frm).
  sep auto.
  eapply sti1_rule;eauto.
  intros.
  apply H2 in H3.
  unfold CurLINV.
  sep auto.
Qed.

Theorem sti2_rule' :
  forall (Spec : funspec) (I : Inv) (r : retasrt) 
         (ri : asrt) (isr : isr) 
         (is : is) (aop : absop) frm p sc li tid,
    p ==> Aisr isr ** Aie true ** Ais is ** Acs nil ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    {|Spec, sc, li, I, r, ri|} |- tid
                           {{ <|| aop ||> ** p}}
                           sprim sti {{ <|| aop ||> ** Aisr isr ** Aie true ** Ais is ** Acs nil ** frm }}.
Proof.
  intros.
  apply backward_rule1 with (<|| aop ||> ** OS  [isr, true, is, nil] ** frm ); intros.
  sep auto; apply H in H2; sep auto || sep pure.
  apply forward_rule1 with (<|| aop ||> ** OS  [isr, true, is, nil] ** frm); intros.
  sep auto.
  eapply sti2_rule;eauto.
Qed.


Theorem switch_rule' :
  forall (Spec : funspec) (I : Inv) 
         (r : retasrt) (ri : asrt) 
         (x : var) (aop : absop) is cs P sc li tid lg Px P',
    P ==> P' ** Px ->
    P' ==> SWINVt I tid ** Ais is ** Acs cs ** <||sched;; aop ||>  -> 
    P' ==> SWPRE_NDEAD sc x tid ->
    GoodFrm Px ->
    Px ==> LINV li tid lg ** Atrue ->
    {|Spec, sc, li, I, r, ri|} |- tid {{ P }}
                           sprim (switch x) {{ <|| aop ||> ** SWINVt I tid ** Ais is ** Acs cs ** Px}}.
Proof.
  intros.
  eapply switch_rule;eauto.
  intros.
  apply H0 in H4.
  sep auto.
Qed.

Theorem eoi_ieon_rule' :
  forall (Spec : funspec) (I : Inv) 
         (r : retasrt) (ri : asrt)
         (isr : isr) (is : list nat) (id : int32) 
         (cs : cs) (i : nat) (aop : absop) p frm sc li tid lg,
    (0 <= Int.unsigned id < Z.of_nat INUM)%Z ->
    i = Z.to_nat (Int.unsigned id) ->
    p ==> Aisr isr ** Aie true ** Ais (i::is) ** Acs cs ** getinv (I i) ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    frm  ==>  p_local li tid lg ** Atrue ->
    isr i = true ->
    {|Spec, sc, li, I, r, ri|} |- tid
                           {{ <|| aop ||> ** p }}sprim (eoi id)
                           {{ <|| aop ||> ** Aisr (isrupd isr i false) ** Aie true ** Ais (i::is) ** Acs cs ** frm }}.
Proof.
  intros.
  eapply conseq_rule with (p := <|| aop ||> ** OS[isr, true, i::is, cs] ** getinv (I i) ** frm)
                            (q := <|| aop ||> ** OS[isrupd isr i false, true, i::is, cs] ** frm ); intros.
  sep cancel 1 1.
  apply H1 in H6; sep auto.
  sep auto.
  eapply eoi_ieon_rule; eauto.
  intros.
  apply H4 in H6.
  unfold CurLINV.
  sep auto.
Qed.

Theorem eoi_ieoff_rule' :
  forall (Spec : funspec) (I : Inv) 
         (r : retasrt) (ri : asrt)  
         (isr : isr) (is : list nat) 
         (id : int32) (i : nat) (cs : cs) 
         (aop : absop) p frm sc li tid,
    (0 <= Int.unsigned id < Z.of_nat INUM)%Z ->
    i = Z.to_nat (Int.unsigned id) ->
    p ==> Aisr isr ** Aie false ** Ais (i::is) ** Acs cs ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    {|Spec, sc, li, I, r, ri|} |- tid {{ <|| aop ||> ** p }}
                            sprim (eoi id)
                            {{ <|| aop ||> ** Aisr (isrupd isr i false) ** Aie false ** Ais (i::is) ** Acs cs ** frm }}.
Proof.
  intros.
  eapply conseq_rule with (p := <|| aop ||> ** OS[isr, false, i::is, cs] ** frm)
                            (q := <|| aop ||> ** OS[isrupd isr i false, false, i::is, cs] ** frm); intros.
  sep cancel 1 1.
  apply H1 in H4; sep auto.
  sep auto.
  eapply eoi_ieoff_rule; eauto.
Qed.



Theorem ex_intro_rule' :
  forall Spec I r ri {tp:Type} (p q: tp -> asrt) s sc li tid,
    (forall v' : tp, {| Spec, sc, li, I, r, ri|} |- tid {{ p v' }} s {{ q v' }}) ->
    {| Spec, sc, li, I, r, ri |} |- tid {{ EX v, p v }} s {{ EX v, q v }}.
Proof.
  intros.
  eapply ex_intro_rule.
  intros.
  eapply forward_rule1 with (q:= q v').
  intros; eexists; eauto.
  auto.
Qed.

Theorem pure_intro_rule': forall (Spec : funspec) (I : Inv) (r : retasrt) 
                                 (ri : asrt)  (p q : asrt) 
                                 (pu : Prop) (s : stmts) sc li tid,
                            (pu -> {|Spec, sc, li, I, r, ri|} |- tid {{ [| pu |] ** p}}s {{q}}) ->
                            {|Spec, sc, li, I, r, ri|} |- tid {{ [|pu|]**p}}s {{q}}.
Proof.
  intros.
  apply backward_rule1 with (([|pu|] ** p) ** [|pu|]).
  intros;sep auto.
  apply pure_split_rule.
  auto.
Qed.

Theorem pure_split_rule': forall (Spec : funspec) (I : Inv) (r : retasrt) 
                                 (ri : asrt)  (p q : asrt) 
                                 (pu : Prop) (s : stmts) sc li tid,
                            (pu -> {|Spec, sc, li, I, r, ri|} |- tid {{ p}}s {{q}}) ->
                            {|Spec, sc, li, I, r, ri|} |- tid {{ [|pu|]**p}}s {{q}}.
Proof.
  intros.
  apply backward_rule1 with (p ** [|pu|]).
  intros;sep auto.
  apply pure_split_rule.
  auto.
Qed.

Theorem prop_intro_rule :
  forall Spec I r ri p s q (P:Prop) sc li tid,
    (P -> {| Spec, sc, li, I, r, ri |} |- tid {{ p }} s {{ q }}) ->
    (forall s, s |= p -> P) ->
    {| Spec, sc, li, I, r, ri |} |- tid {{ p }} s {{ q }}.
Proof.
  intros.
  apply backward_rule1 with (p ** [| P |]).
  intros; sep auto.
  apply H0 in H1; sep auto.
  apply pure_split_rule.
  auto.
Qed.

Lemma abscsq_rule' :
  forall (Spec : funspec) (I : Inv) (r : retasrt) 
         (ri : asrt)  (p' p q : asrt) (s : stmts) sc li tid,
    NoAbs li ->
    absinfer sc p' p ->
    {|Spec, sc, li, I, r, ri|} |- tid {{p}}s {{q}} ->
    {|Spec, sc, li, I, r, ri|} |- tid {{p'}}s {{q}}.
Proof.
  intros.
  eapply abscsq_rule; eauto.
  unfold absimp.
  apply absinfer_eq.
Qed.


Lemma abscsq_rule'' :
  forall (Spec : funspec) (I : Inv) (r : retasrt) 
         (ri : asrt)  (q' p q : asrt) (s : stmts) sc li tid,
    NoAbs li ->
    absinfer sc q q' ->
    {|Spec, sc, li, I, r, ri|} |- tid {{p}}s {{q}} ->
    {|Spec, sc, li, I, r, ri|} |- tid {{p}}s {{q'}}.
Proof.
  intros.
  eapply abscsq_rule; eauto.
  apply absinfer_eq.
Qed.

Lemma disj_rule' :
  forall (Spec : funspec) (I : Inv) (r : retasrt) 
         (ri p1 p2 : asrt) (s : stmts) (q1 q2 : asrt) sc li tid,
       {|Spec, sc, li, I, r, ri|} |- tid {{p1}}s {{q1 }} ->
       {|Spec, sc, li, I, r, ri|} |- tid {{p2}}s {{q2 }} ->
                             {|Spec, sc, li, I, r, ri|} |- tid {{p1 \\// p2}}s {{q1 \\// q2}}.
Proof.
  intros.
  eapply disj_rule.
  eapply forward_rule2; eauto.
  intros; left; auto.
  eapply forward_rule2; eauto.
  intros; right; auto.
Qed.

Lemma checkis_rule' :
  forall Spec I r ri isr ie is cs frm aop p v x sc li tid lg,
    p ==> Aisr isr ** Aie ie ** Ais is ** Acs cs ** LV x @ Tint32 |-> v ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    frm ==>  p_local li tid lg ** Atrue ->
    {|Spec, sc, li, I, r, ri|} |- tid 
    {{ <|| aop ||> ** p }} (sprim (checkis x))
                           {{ <|| aop ||> ** Aisr isr ** Aie ie ** Ais is ** Acs cs **
                                  LV x @ Tint32 |->  is_length is  ** frm }}.
Proof.
  intros.
  eapply backward_rule1 with (p := <|| aop ||> ** OS [ isr, ie, is, cs ] **  LV x @ Tint32 |-> v ** frm ).
  intros.
  sep auto; apply H in H3; sep auto || sep pure.
  eapply forward_rule1 with (q := <|| aop ||>   ** OS  [isr, ie, is, cs] ** LV x @ Tint32 |->  is_length is ** frm ).
  sep auto.
  eapply checkis_rule;eauto.
  intros.
  apply H2 in H3.
  unfold CurLINV.
  sep auto.
Qed.

(*Require Import tst_prop.*)

Definition invlth_noisr' I high:=
  match high with
    | 0 => Aemp
    | _ => starinv_noisr I 0 (high -1)
  end.

Ltac trysimplsall := repeat progress (simpl substmo in *;
                                       simpl substaskst in *;
                                       simpl getmem in *;
                                       simpl getabst in *;
                                       simpl substmo in *;
                                       simpl getisr in *;
                                       simpl getis in *;
                                       simpl getie in *;
                                       simpl gettopis in *;
                                       simpl getcs in *;
                                       simpl get_smem in *;
                                       simpl get_mem in *;
                                       simpl gettopis in *;
                                       simpl starinv_isr in * ).

Lemma starinv_prop1: forall  j i I,
                       (starinv_isr I i (S j))  ==> 
                                                (starinv_isr I i j) ** (starinv_isr I (S (i+j)) 0)%nat.
Proof.
  inductions j.
  introv Hsat.
  trysimplsall.
  assert (S i = S (i+0)) by omega.
  rewrite <- H.
  auto.
  introv Hsat.
  trysimplsall.
  assert (S (i + S j) = S (S i + j)) by omega.
  sep cancel 1%nat 1%nat.
  rewrite H.
  eapply IHj in Hsat.
  sep auto.
Qed.

Lemma starinvnoisr_prop1_rev: forall  j i I,
                                (starinv_noisr I i j) ** (starinv_noisr I (S (i+j)) 0)%nat ==> 
                                                      (starinv_noisr I i (S j)).
Proof.
  inductions j.
  introv Hsat.
  trysimplsall.
  assert (S i = S (i+0)) by omega.
  rewrite <- H in Hsat.
  auto.
  introv Hsat.
  simpl starinv_noisr in *.
  assert (S (i + S j) = S (S i + j)) by omega.
  rewrite H in *.
  sep auto.
Qed.

Lemma invisr_imply_noisr : forall j ge le M ir aux O ab I , ( forall i : hid, ir i = false) -> 
                                                            (ge, le, M, ir, aux, O, ab) |= starinv_isr I 0 j -> 
                                                            (ge, le, M, ir, aux, O, ab) |= starinv_noisr I 0 j.
Proof.
  inductions j.
  intros.
  unfold starinv_noisr.
  unfold starinv_isr in H0.
  destruct H0; mytac.
  destruct H0; mytac.
  destruct H0;mytac; tryfalse.
  simpl in H0; simpl in H1; mytac.
  lets Hs :  H 0; tryfalse.
  destruct H0; mytac.
  trysimplsall.
  destruct H4; mytac.
  simpl in H0; simpl in H2; mytac.
  join_emp_eq_sub.
  auto.
  introv Hsat Hss.
  apply starinv_prop1 in Hss.
  destruct Hss;mytac.
  trysimplsall.
  destruct H4; mytac.
  destruct H; mytac.
  destruct H; mytac.
  simpl in H; simpl in  H1; mytac.
  lets Hs : Hsat (S j); tryfalse.
  destruct H; mytac.
  destruct H6; mytac.
  trysimplsall.
  simpl in H; simpl in  H4; mytac.
  lets Hres : IHj Hsat H3.
  eapply starinvnoisr_prop1_rev.
  replace (S (0 + j)) with (S j) by omega.
  do 6 eexists; mytac;eauto.
Qed.

Lemma invisr_imply_noisr' : 
forall j ge le M ir aux O ab I , ( forall i : hid, i <= j -> ir i = false) -> 
                                                             (ge, le, M, ir, aux, O, ab) |= starinv_isr I 0 j -> 
                                                             (ge, le, M, ir, aux, O, ab) |= starinv_noisr I 0 j.
Proof.
  inductions j.
  intros.
  unfold starinv_noisr.
  unfold starinv_isr in H0.
  destruct H0; mytac.
  destruct H0; mytac.
  destruct H0;mytac; tryfalse.
  simpl in H0; simpl in H1; mytac.
  lets Hs :  H 0; tryfalse.
  assert (0<=0) by omega.
  apply Hs in H1; tryfalse.
  destruct H0; mytac.
  trysimplsall.
  destruct H4; mytac.
  simpl in H0; simpl in H2; mytac.
  join_emp_eq_sub.
  introv Hsat Hss.
  apply starinv_prop1 in Hss.
  destruct Hss;mytac.
  trysimplsall.
  destruct H4; mytac.
  destruct H; mytac.
  destruct H; mytac.
  simpl in H; simpl in  H1; mytac.
  lets Hs : Hsat (S j); tryfalse.
  assert (S j <= S j) by omega.
  join_emp_eq_sub.
  apply Hs in H0; tryfalse.
  destruct H; mytac.
  destruct H6; mytac.
  trysimplsall.
  simpl in H; simpl in  H4; mytac.
  assert (forall i : hid, i <= j -> x1 i = false).
  introv Hij.
  eapply Hsat; omega.
  lets Hres : IHj H1 H3.
  eapply starinvnoisr_prop1_rev.
  replace (S (0 + j)) with (S j) by omega.
  do 6 eexists; mytac;eauto.
Qed.


Lemma isr_false_inv_eq:
  forall (i : nat) (ge le : env) (M : mem) (ir : isr) 
         (ie0  : ie) (is0 : is) (cs0 : cs) (O0 : osabst) 
         (ab : absop) (I : Inv),
    i <= INUM ->
    (forall j : nat, 0 <= j < i -> ir j = false) ->
    (ge, le, M, ir, (ie0, is0, cs0), O0, ab) |= invlth_isr I 0 i ->
    (ge, le, M, ir, (ie0, is0, cs0), O0, ab)
      |= invlth_noisr' I i  **
      ([|ir i = true|] \\//
                       [|ir i = false|] ** getinv (I i)).
Proof.
  inductions i.
  intros.
  unfold invlth_isr in H1.
  unfold invlth_noisr'.
  simpl starinv_isr in H1.
  destruct H1.
  destruct H1.
  simpl in H1.
  mytac.
  simpl.
  do 6 eexists;mytac.
  left.
  mytac;auto.
  simpl in H1.
  mytac.
  simpl.
  do 6 eexists;mytac;eauto.
  right.
  do 6 eexists;mytac;eauto.
  join_emp_eq_sub.
  intros.
  assert ((ge, le, M, ir, (ie0, is0, cs0), O0, ab) |= invlth_isr I 0 (S i -1) ** ([|ir (S i) = true|] \\// [|ir (S i) = false|] ** getinv (I (S i)))).
  clear -H1.
  assert (S i -1 = i).
  omega.
  rewrite H.
  clear H.
  unfold invlth_isr in *.
  apply starinv_prop1 in H1.
  simpl starinv_isr in H1 at 2.
  assert (i - 0 =i).
  omega.
  rewrite H in *.
  simpl in H1.
  mytac.
  clear H.
  destruct H5;mytac.
  simpl.
  do 6 eexists;mytac;eauto.
  mytac.
  mytac.
  left;mytac;auto.
  simpl.
  do 6 eexists;mytac;eauto.
  right.
  do 6 eexists;mytac;eauto.
  clear H1.
  unfold invlth_noisr'.
  join_emp_eq_sub.
  simpl in H2.
  mytac.
  destruct H6;mytac;
  join_emp_eq_sub.
  simpl.
  do 6 eexists;mytac;eauto.
  apply map_join_emp;auto.
  apply OSAbstMod.join_comm.
  apply OSAbstMod.join_emp;auto.
  unfold invlth_isr in H5.
  apply invisr_imply_noisr'.
  intros.
  apply H0.
  omega.
  assert (i-0-0 = i-0) by omega.
  rewrite H2 in H5.
  auto.
  left;mytac;auto.
  join_emp_eq_sub.
  simpl.
  exists x x0 M x2 x3 O0.
  mytac;auto.
  unfold invlth_isr in H5.
  apply invisr_imply_noisr'.
  intros.
  apply H0.
  omega.
  assert (i-0-0 = i-0) by omega.
  rewrite H1 in H5.
  auto.
  right.
  do 6 eexists;mytac;eauto.
Qed.



Lemma starinv_prop1': forall  j i I,
                        (starinv_noisr I i (S j))  ==> 
                                                   (starinv_noisr I i j) ** (starinv_noisr I (S (i+j)) 0)%nat.
Proof.
  inductions j.
  introv Hsat.
  simpl starinv_noisr in *.
  assert (S i = S (i+0)) by omega.
  rewrite <- H.
  auto.
  introv Hsat.
  simpl starinv_noisr in *.
  assert (S (i + S j) = S (S i + j)) by omega.
  sep auto.
  lets Hrs : IHj Hsat.
  sep auto.
  assert ((S (i + S j)) =  (S (S i + j))) by omega.
  rewrite H1.
  auto.
Qed.

Lemma starinv_prop1_rev: forall  j i I,
                           (starinv_isr I i j) ** (starinv_isr I (S (i+j)) 0)%nat ==> 
                                               (starinv_isr I i (S j)).
Proof.
  inductions j.
  introv Hsat.
  simpl starinv_isr in *.
  assert (S i = S (i+0)) by omega.
  rewrite <- H in *.
  auto.
  introv Hsat.
  simpl starinv_isr in *.
  assert (S (i + S j) = S (S i + j)) by omega.
  sep cancel 1%nat 1%nat.
  eapply IHj;eauto.
  assert ((S (i + S j)) =  (S (S i + j))) by omega.
  rewrite H0 in *.
  auto.
Qed.

Lemma invnoisr_imply_isr' :
  forall j ge le M ir aux O ab I , ( forall i : hid, i <= j -> ir i = false) -> 
                                   (ge, le, M, ir, aux, O, ab) |= starinv_noisr I 0 j -> 
                                   (ge, le, M, ir, aux, O, ab) |= starinv_isr I 0 j.
Proof.
  inductions j.
  intros.
  unfold starinv_noisr in H0.
  unfold starinv_isr.
  exists ir;right.
  simpl.
  do 6 eexists;mytac;auto.
  introv Hsat Hss.
  eapply starinv_prop1' in Hss.
  apply starinv_prop1_rev.
  simpl in Hss.
  mytac.
  simpl.
  do 6 eexists;mytac;eauto.
  exists ir.
  right.
  do 6 eexists;mytac;eauto.
Qed.

Lemma isr_false_inv_eq':
  forall (i : nat) (ge le : env) (M : mem) (ir : isr) 
         (ie0  : ie) (is0 : is) (cs0 : cs) (O0 : osabst) 
         (ab : absop) (I : Inv),
    i <= INUM ->
    (forall j : nat, 0 <= j < i -> ir j = false)  ->
    (ge, le, M, ir, (ie0, is0, cs0), O0, ab)
      |= invlth_noisr' I i  **
      ([|ir i = true|] \\//
                       [|ir i = false|] ** getinv (I i)) ->
    (ge, le, M, ir, (ie0, is0, cs0), O0, ab) |= invlth_isr I 0 i.
Proof.
  inductions i.
  intros.
  unfold invlth_isr.
  unfold invlth_noisr' in H1.
  simpl starinv_isr.
  apply astar_l_aemp_elim  in H1.
  destruct H1.
  simpl in H1.
  mytac.
  exists ir.
  left;simpl;mytac;auto.
  exists ir.
  right.
  simpl in H1.
  simpl.
  mytac.
  join_emp_eq_sub.
  do 6 eexists.
  mytac;eauto.
  intros.

  assert ((ge, le, M, ir, (ie0, is0, cs0), O0, ab) |= invlth_isr I 0 (S i -1) ** ([|ir (S i) = true|] \\// [|ir (S i) = false|] ** getinv (I (S i)))).
  simpl in H1.
  mytac.
  destruct H6;mytac.
  join_emp_eq_sub.

  simpl.
  do 6 eexists;mytac;eauto.
  apply map_join_emp.
  apply OSAbstMod.join_comm.
  apply OSAbstMod.join_emp.
  auto.
  2:left;mytac;auto.
  unfold invlth_isr.

  assert (i - 0 - 0 = i - 0) by omega.
  rewrite H2.
  eapply invnoisr_imply_isr';eauto.
  intros.
  apply H0;auto.
  omega.
  join_emp_eq_sub.
  apply invnoisr_imply_isr' in H5.
  unfold invlth_isr.
  simpl.
  do 6 eexists;mytac;eauto.
  assert (i - 0 - 0 = i - 0) by omega.
  rewrite H1.
  auto.
  right.
  do 6 eexists;mytac;eauto.
  intros.
  apply H0.
  omega.
  unfold invlth_isr in *.
  clear H1.
  assert (S i - 0 = S i) by omega.
  rewrite H1.

  eapply starinv_prop1_rev;eauto.
  unfold starinv_isr at 2.
  assert (0 + i = i) by omega.
  rewrite H3 in *.
  clear -H2.
  simpl in H2.
  mytac.
  destruct H4;mytac.
  join_emp_eq_sub.
  simpl.
  do 6 eexists;mytac;eauto.
  apply map_join_emp.
  auto.
  apply OSAbstMod.join_comm.
  apply OSAbstMod.join_emp.
  auto.
  assert (i -0 -0 = i) by omega.
  rewrite H0 in H3.
  auto.
  exists ir.
  left;mytac;auto.
  simpl.
  do 6 eexists;mytac;eauto.
  assert ( (i - 0 - 0) = i) by omega.
  rewrite H in *.
  auto.
  exists ir.
  right.
  do 6 eexists.
  mytac;eauto.
Qed.

Theorem if_rule' :
  forall Spec I r ri p q1 q2 e tp s1 s2 sc li ct,
    {| Spec, sc, I, r, ri , li|}|- ct {{ p //\\ Aistrue e }} s1 {{ q1 }} ->
                           {| Spec, sc, I, r, ri, li |}|-ct {{ p //\\ Aisfalse e }} s2 {{ q2 }} ->
                                                  p ==> EX v : val, Rv e @ tp == v ->
                                                                    {| Spec, sc, I, r, ri,li|}|-ct  {{ p }} sif e s1 s2 {{ q1 \\// q2 }}.
Proof.
  intros.
  eapply if_rule; eauto.
  eapply forward_rule1.
  2 : eauto.
  intros; left; eauto.
  eapply forward_rule1.
  2 : eauto.
  intros; right; eauto.
Qed.

Theorem while_rule' :
  forall Spec I r ri p q e s tp sc li ct,
    {| Spec, sc, I, r, ri, li|}|-ct {{ p //\\ Aistrue e }} s {{ p }} ->
                           p ==> EX v : val, Rv e @ tp ==  v ->
                                             p //\\ Aisfalse e ==> q ->
                                             {| Spec, sc, I, r, ri,li |}|-ct {{ p }} swhile e s {{ q }}.
Proof.
  intros.
  eapply forward_rule1; eauto.
  eapply while_rule; eauto.
Qed.


Theorem if_rule2 :
  forall Spec I r ri p q1 q2 e tp s1 s2 v sc li ct,
    p ==> Rv e @ tp == v ->
    {| Spec, sc, I, r, ri,li |}|- ct {{ p ** [| v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef |] }} s1 {{ q1 }} ->
                          {| Spec, sc, I, r, ri,li |}|-ct {{ p ** [| v = Vint32 Int.zero \/ v = Vnull |] }} s2 {{ q2 }} ->
                                                {| Spec, sc, I, r, ri,li |}|-ct {{ p }} sif e s1 s2 {{ q1 \\// q2 }}.
Proof.
  intros.
  eapply if_rule'.
  3: intros;eexists;apply H;auto.
  eapply backward_rule1.
  eapply sep_aconj_r_aistrue_to_astar;eauto.
  auto.
  eapply backward_rule1.
  eapply sep_aconj_r_aisfalse_to_astar;eauto.
  auto.
Qed.


Theorem if_rule2' :
  forall Spec I r ri p q1 q2 e tp s1 s2 v sc li ct,
    p ==> Rv e @ tp == v ->
    {| Spec, sc, I, r, ri, li|}|-ct {{ p ** [| v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef |] }} s1 {{ q1 }} ->
                          {| Spec, sc, I, r, ri,li |}|-ct {{ p ** [| v = Vint32 Int.zero \/ v = Vnull |] }} s2 {{ q2 }} ->
                                                {| Spec, sc, I, r, ri,li |}|- ct {{ p }} sif e s1 s2 {{ q1 ** [| v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef |] \\// q2 ** [| v = Vint32 Int.zero \/ v = Vnull |] }}.
Proof.
  intros.
  eapply if_rule'.
  3: intros;eexists;apply H;auto.
  eapply backward_rule1.
  eapply sep_aconj_r_aistrue_to_astar;eauto.
  apply pure_split_rule;intro.
  apply forward_rule1 with q1.
  sep auto.
  apply backward_rule1 with (p ** [|v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef|]).
  sep auto.
  auto.
  eapply backward_rule1.
  eapply sep_aconj_r_aisfalse_to_astar;eauto.
  apply pure_split_rule;intro.
  apply forward_rule1 with q2.
  sep auto.
  apply backward_rule1 with (p ** [|v = Vint32 Int.zero \/ v = Vnull|]).
  sep auto.
  auto.
Qed.

Theorem aconj_aistrue_rule :
  forall Spec I r ri s P e t v Q sc li ct,
    P ==> Rv e @ t == v ->
    {| Spec, sc, I, r, ri, li|} |- ct
    	  {{ P ** [| v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef |] }} s {{ Q }} ->
                          {| Spec, sc, I, r, ri, li|}|- ct {{ P //\\ Aistrue e }} s {{ Q }}.
Proof.
  intros.
  eapply backward_rule1.
  eapply sep_aconj_r_aistrue_to_astar;eauto.
  auto.
Qed.

Theorem aconj_aisfalse_rule :
  forall Spec I r ri s P e t v Q sc li ct,
    P ==> Rv e @ t == v ->
    {| Spec, sc, I, r, ri, li|}|-ct {{ P ** [| v = Vint32 Int.zero \/ v = Vnull |] }} s {{ Q }} ->
                          {| Spec, sc, I, r, ri, li |}|-ct {{ P //\\ Aisfalse e }} s {{ Q }}.
Proof.
  intros.
  eapply backward_rule1.
  eapply sep_aconj_r_aisfalse_to_astar;eauto.
  auto.
Qed.


Lemma pure_ex_intro_rule :
  forall Spec I r ri {tp:Type} (P:tp->Prop) p s q sc li ct,
    {| Spec, sc, li, I, r, ri |} |-ct {{ EX x, [| P x |] ** p }} s {{ q }} ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ [| exists x, P x |] ** p }} s {{ q }}.
Proof.
  intros.
  eapply backward_rule2; eauto.
  intros.
  sep split in H0.
  destruct H1.
  sep auto.
  eauto.
Qed.


Lemma prop_elim_rule1 :
  forall Spec I r ri (P:Prop)  p s q sc li ct,
    {| Spec, sc, li, I, r, ri |} |-ct {{ [| P |] ** p }} s {{ q }} ->
    (forall s0 : RstateOP, s0 |= p -> P) ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ p }} s {{ q }}.
Proof.
  intros.
  eapply backward_rule2; eauto.
  sep auto.
  apply H0 in H1; auto.
Qed.

Lemma prop_elim_rule2 :
  forall Spec I r ri (P:Prop)  p s q sc li ct,
    (forall s0 : RstateOP, s0 |= p -> P) ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ [| P |] ** p }} s {{ q }} ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ p }} s {{ q }}.
Proof.
  intros.
  eapply backward_rule2; eauto.
  sep auto.
  apply H in H1; auto.
Qed.


Lemma ift_rule_general :
  forall (Spec : funspec) (I : Inv) (r : retasrt) 
         (ri : asrt)  (p q1 q2 : asrt) (e : expr) 
         (tp : type) (s : stmts) sc li ct,
    p ==> EX v : val, Rv e @ tp == v ->
    p //\\ Aisfalse e ==> q2 ->
    {|Spec, sc, li, I, r, ri|}|-ct {{p //\\ Aistrue e}}s {{q1}} ->
    {|Spec, sc, li, I, r, ri|}|-ct {{p}}sifthen e s {{q1 \\// q2}}.
Proof.
  intros.
  eapply ift_rule; intros; eauto.
  apply H0 in H2; right; auto.
  eapply forward_rule2; eauto.
  intros; left; eauto.
Qed.

Lemma ift_rule' :
  forall (Spec : funspec) (I : Inv) (r : retasrt) 
         (ri : asrt)  (p q : asrt) (e : expr) 
         (tp : type) (s : stmts) (v:val) sc li ct,
    p ==> Rv e @ tp == v ->
    {|Spec, sc, li, I, r, ri|}|-ct {{ p ** [|v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef|] }}s {{ q }} ->
    {|Spec, sc, li, I, r, ri|}|-ct {{ p }}sifthen e s {{ q \\// (p ** [|v = Vint32 Int.zero \/ v = Vnull|]) }}.
Proof.
  intros.
  eapply ift_rule_general; intros; eauto.
  apply H in H1; eexists; eauto.
  eapply sep_aconj_r_aisfalse_to_astar; eauto.
  eapply backward_rule2.
  2 : eapply sep_aconj_r_aistrue_to_astar; eauto.
  auto.
Qed.

Lemma ift_rule'' :
  forall (Spec : funspec) (I : Inv) (r : retasrt) 
         (ri : asrt)  (p q : asrt) (e : expr) 
         (tp : type) (s : stmts) (v:val) sc li ct,
    p ==> Rv e @ tp == v ->
    {|Spec, sc, li, I, r, ri|}|-ct {{ p ** [|v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef|] }}s {{ q }} ->
    {|Spec, sc, li, I, r, ri|}|-ct {{ p }}sifthen e s {{ (q ** [|v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef|])\\// (p ** [|v = Vint32 Int.zero \/ v = Vnull|]) }}.
Proof.
  intros.
  eapply ift_rule_general; intros; eauto.
  apply H in H1; eexists; eauto.
  eapply sep_aconj_r_aisfalse_to_astar; eauto.
  eapply backward_rule2.
  2 : eapply sep_aconj_r_aistrue_to_astar; eauto.
  apply pure_split_rule;intro.
  apply forward_rule1 with q.
  sep auto.
  apply backward_rule1 with (p ** [|v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef|]).
  sep auto.
  auto.
Qed.



Lemma hoare_disj_afalse_l_pre :
  forall Spec I r ri P s Q sc li ct, 
    {| Spec, sc, li, I, r, ri |} |-ct {{ P }} s {{ Q }} ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ Afalse \\// P }} s {{ Q }}.
Proof.
  intros.
  apply backward_rule1 with (P).
  intros.
  destruct H0.
  tryfalse.
  auto.
  auto.
Qed.

Lemma hoare_disj_afalseP_r_pre :
  forall Spec I r ri P s Q P' sc li ct,
    {| Spec, sc, li, I, r, ri |} |-ct {{ P }} s {{ Q }} ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ P \\// Afalse ** P' }} s {{ Q }}.
Proof.
  intros.
  apply backward_rule1 with (P).
  intros.
  destruct H0.
  auto.
  simpl in H0;mytac.
  tryfalse.
  auto.
Qed.

Lemma hoare_disj_afalseP_l_pre :
  forall Spec I r ri P s Q P' sc li ct,
    {| Spec, sc, li, I, r, ri |} |-ct {{ P }} s {{ Q }} ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ Afalse ** P' \\// P }} s {{ Q }}.
Proof.
  intros.
  apply backward_rule1 with (P).
  intros.
  destruct H0.
  simpl in H0;mytac;tryfalse.
  auto.
  auto.
Qed.

Lemma hoare_disj_afalse_r_pre :
  forall Spec I r ri P s Q sc li ct,
    {| Spec, sc, li, I, r, ri |} |-ct {{ P }} s {{ Q }} ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ P \\// Afalse }} s {{ Q }}.
Proof.
  intros.
  apply backward_rule1 with (P).
  intros.
  destruct H0.
  auto.
  tryfalse.
  auto.
Qed.


