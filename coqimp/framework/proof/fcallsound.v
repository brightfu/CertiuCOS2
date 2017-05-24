Require Import sound_include.




Lemma call_ignore_exprlist_sim: 
  forall el tl vl  Spec sd  I r ri q vl' tl' ks ge le M ir aux aop O v f li t, 
    satp (ge, le, M, ir, aux) O (CurLINV li t) ->
    evalexprlist' el tl vl (ge,le,M) ->  
    MethSimMod Spec sd 
               (curs (sfexec f ((List.rev vl) ++ (cons v nil) ++ vl') ((List.rev tl) ++ tl')), (kenil, ks)) 
               (ge, le, M, ir, aux) aop O li I r ri q t ->
    MethSimMod Spec sd 
               (curs (sskip (Some v)), (kenil, kfuneval f vl' tl' el  ks))
               (ge, le, M, ir, aux) aop O li I r ri q t .
Proof.
  introv Hsat  Heval.
  inductions Heval gen v vl' tl'.
  introv Hss.
  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hstep.
  invertstep idtac.
  exists aop OO  (ge, le, M, ir, aux) Ms O Os.
  splits; eauto.
  constructors.

  introv _ _ _  Hf.
  apply Hf.
  eexists. exists o2.
  destruct o2 as [[[[]]]].
  eapply ostc_step;eauto.
  eapply stmt_step; eauto.
  constructors; eauto.

  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hstep.
  invertstep idtac.
  exists aop OO  (ge, le, M, ir, aux) Ms O Os.
  splits; eauto.
  constructors.
  eapply skip_expr_eval_msim_hold; eauto.
  eapply IHHeval;eauto.
  unfolds in Hjm1.
  unfold joinmem in Hjm1.
  simp join.

  lets Heqq : evaltype_GE_eq  H1 H16.
  subst t0.
  simpl in H2.
  rewrite  List.app_assoc.
  assert ((rev tl ++ t1:: nil) ++ tl'=  (rev tl ++ t1 :: tl')).
  rewrite <-  List.app_assoc.
  simpl.
  auto.
  rewrite H3 in H2.
  auto.
  introv Hjm1 Hjm2 Hinv Hf.
  apply Hf.
  unfolds in Hjm2.
  unfold joinmem in Hjm2.
  simp join.
  do 2 eexists.
  eapply ostc_step;eauto.
  eapply stmt_step; eauto.
  constructors; eauto.
  eapply evaltype_eq_prop; eauto.
Qed.

Lemma call_rule_sound : 
  forall f Spec sd  I r ri pre post p P el vl  tp tl logicl pa t ,
    GoodFrm p ->
    Spec f = Some (pre, post, (tp, tl)) ->
    P ==> PRE [pre, vl, logicl, t] ** p ->
    P ==> Rvl el @ tl == vl ->
    tl_vl_match tl vl = true ->
    PRE [pre, vl, logicl, t] ==> CurLINV pa t -> 
    EX v : option val, POST [post, vl, v, logicl, t]  ==> CurLINV pa t->
                       RuleSem Spec  sd pa I r ri P (scall f el) 
                               (EX v,POST[post, vl,v,logicl,t] ** p) t.
Proof.
  introv Hpem Hf Hx Hpre Htlvlmatch Him1 Him2.
  introv Hsat.
  lets Hel :  Hpre  Hsat.
  simpl in Hel.
  destruct o as [[[[ge le] M] ir] aux].
  simpl in Hel.
  lets Hres :  evalexprlist_imply_evalexprlist' Hel.
  destruct el.
  inverts Hres.
  eapply identity_step_msim_hold;eauto.
  unfolds nilcont.
  unfold notabortm.
  splits.
  introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  splits;
    introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  introv.
  unfolds nilcont.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors; eauto.
  destruct Hsat; auto.
  constructors; introv Hfalse; tryfalse.
  false.
  apply Hfalse.
  do 4 eexists.  eauto.
  inverts Hfalse.

  
  (***)
  introv Hinv Hdisj Hjoin.
  destruct Hsat as (Hsat & Hlinv).
  apply Hx in Hsat.
  simpl in Hsat.
  destruct Hsat as (M1&M2&M0&o1&o2&oo&Heq1&Hmj1&Heq2&Haj&Hppre & Hpp).
  subst.
  exists aop OO (ge, le, M1,ir,aux) M2   O Os.
  exists o1 o2  pre post tp logicl.
  splits;eauto.
  constructors.
  unfolds. 
  clear -Hmj1. join auto.
  splits; auto.
  unfolds; intros.
  eapply absinfer_sound.local_inv_aop_irev with aop.
  eapply Him1; eauto.
  introv Hsat.
  assert ((o0, O1, gamma'') |= EX v, POST [post, rev nil, v, logicl, t]).
  sep auto.
  split.
  unfolds.
  intros.
  eapply absinfer_sound.local_inv_aop_irev with gamma''.
  eapply Him2; eauto.
  
  introv  Hjms Hjoink  Henv.
  constructors; introv Hfa; tryfalse.
  introv _ _ _ Hstep.
  invertstep idtac.
  inverts Hfa.
  introv Hivnv1 Hdisj1 Hjj1.
  exists gamma''  OO0 O'' Os0.
  splits; eauto.
  constructors.
  assert ((o0, O1, gamma'') |= EX v, POST [post, rev nil, v, logicl, t]).
  sep auto.
  lets Hks : Him2 H0.
  assert (  satp o0 O1 (CurLINV pa t)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfold lift.
  exists v0.
  destruct o0 as [[[[GG EE]MM ]isrr ]auxx].
  unfolds in Hjms .
  simp join.
  exists x1 M2 x2  O1 o2 O''.
  simpl.
  splits; eauto.

  unfolds in Henv.
  simp join.
  eapply goodfrm_prop; eauto.
  destruct Hfa as (_&_&Hff&_).
  false. apply Hff.
  eexists; eauto.
  destruct Hfalse as (Hff&_).
  false. apply Hff.
  eexists; eauto.
  inverts Hres.
  eapply identity_step_msim_hold;eauto.
  unfolds nilcont.
  splits. introv Hfalse; unfolds in Hfalse; simp join; tryfalse.  
  splits; introv Hfalse; unfolds in Hfalse; simp join; tryfalse.  
  introv.
  unfolds nilcont.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply spcall_step with (t:=t0);eauto.
  destruct Hsat; auto.
  destruct Hsat as (Hsat & Hlinv).
  eapply skip_expr_eval_msim_hold; eauto.
  eapply call_ignore_exprlist_sim; eauto.
  constructors; introv Hfalse; tryfalse.
  false.
  apply Hfalse.
  do 4 eexists.  eauto.
  inverts Hfalse.
  introv  Hinv Hdisj Hmdijs.
  apply Hx in Hsat.
  simpl in Hsat.
  destruct Hsat as (M1&M2&M0&o1&o2&oo&Heq1&Hmj1&Heq2&Haj&Hppre & Hpp).
  subst.
  exists aop OO (ge, le, M1,ir,aux) M2 O Os.
  exists o1 o2  pre post tp logicl.
  splits;eauto.
  constructors.
  unfolds. 
  clear -Hmj1. join auto.
  assert (t0::nil=rev(t0::nil)).
  simpl;auto.
  rewrite H.
  assert (v::nil=rev(v::nil)).
  simpl;auto.
  rewrite H0.
  assert (rev(t0::nil++tl0) = rev tl0 ++ rev (t0:: nil)).
  rewrite <- rev_app_distr;auto.
  rewrite <- H4.
  assert (rev(v::nil++vl0) = rev vl0 ++ rev (v :: nil)).
  rewrite <- rev_app_distr;auto.
  rewrite <- H5.


  apply tl_vl_match_rev.
  simpl;auto.
  rewrite rev_app_distr.
  simpl.
  rewrite rev_involutive.
  auto.

  rewrite <- list_rev_prop.
  eapply good_fun_asrt_absop; eauto.
  apply (getprop (pre (v :: vl0) logicl t)). 
  split; auto.
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with aop; eauto.
  split; eauto.

  introv Hsat.
  assert ((o0, O1, gamma'') |= EX v0, POST [post, rev (rev vl0 ++ v :: nil), v0, logicl, t]).
  sep auto.
  split.
  unfolds.
  intros.
  eapply absinfer_sound.local_inv_aop_irev with gamma''.
  eapply Him2; eauto.
  rewrite  list_rev_prop .
  sep auto.
  introv  Hjms Hjoink  Henv.
  constructors; introv Hfa; tryfalse.
  introv _ _ _ Hstep.
  invertstep idtac.
  inverts Hfa.
  introv Hivnv1 Hdisj1 Hjj1.
  exists gamma''  OO0 O'' Os0.
  splits; eauto.
  constructors.

  assert ((o0, O1, gamma'') |= EX v1, POST [post, rev (rev vl0 ++ v :: nil), v1, logicl, t]).
  sep auto.
  unfolds.
  intros.
  rewrite <- list_rev_prop in H0.
  lets Hks : Him2 H0.
  assert (  satp o0 O1 (CurLINV pa t)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfold lift.
  exists v1.
  destruct o0 as [[[[GG EE]MM ]isrr ]auxx].
  unfolds in Hjms .
  simp join.
  exists x1 M2 x2  O1 o2 O''.
  simpl.
  unfolds in Henv.
  simp join.
  splits; eauto.
  rewrite  list_rev_prop ; auto.
  eapply goodfrm_prop; eauto.
  destruct Hfa as (_&_&Hff&_).
  false. apply Hff.
  eexists; eauto.
  destruct Hfalse as (Hff&_).
  false. apply Hff.
  eexists; eauto.
Qed.




Lemma calle_rule_sound: 
  forall f e l Spec sd  I r ri pre post P p el v' vl  tp tl logicl t pa,   
    GoodFrm p ->
    retpost post ->
    Spec f = Some (pre, post, (tp, tl)) ->
    P ==> PRE [pre, vl, logicl, t] ** PV l @ tp |-> v' ** p ->
    P ==> Rvl el @ tl == vl ->
    PV l @ tp |-> v' ** p ==> Lv e @ tp == l ->
    tl_vl_match tl vl = true ->
    PRE [pre, vl, logicl, t] ==> CurLINV pa t -> 
    EX v : option val, POST [post, vl, v, logicl, t]  ==> CurLINV pa t->
                       RuleSem Spec sd  pa I r ri (P)
                               (scalle e f el) (EX v : val,
                                                       POST [post, vl, Some v, logicl, t] ** PV l @ tp |-> v ** p) t.
Proof.
  introv Hgf Hpem Hret Hpre Hf Hx  Htlvlmatch Him1 Him2.
  introv Hsat.
  destruct Hsat as (Hsat & Hlinv).
  lets Hel :  Hpre  Hsat.
  simpl in Hel.
  simp join.
  destruct o as [[[[ge le] M] ir] aux].
  unfolds in H10.
  subst x8.
  simpl in H8,H9,H5,H0,H3.
  assert (x9 = x3) by join auto.
  subst x9.
  clear H7.
  assert ( (ge, le, x0, ir, aux, x3, aop) |= ( (addrval_to_addr l) # tp |-> v') ** p).
  simpl; join auto.
  lets Hte : Hx H.
  simpl in Hte.
  destruct Hte as (Hadd & Htp).
  lets Hk : Hf Hsat.
  simpl in Hk.
  lets Hres :  evalexprlist_imply_evalexprlist' Hk.
  clear Hk.
  destruct el.
  inverts Hres.
  clear Htlvlmatch Hf.
  eapply identity_step_msim_hold;eauto.
  unfolds nilcont.
  unfold notabortm.
  splits.
  introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  splits;
    introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  introv.
  unfolds nilcont.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors; eauto.
  eapply evaltype_eq_prop; eauto.
  eapply identity_step_msim_hold;eauto.
  unfold notabortm.
  splits.
  introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  splits;
    introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  introv.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors; eauto.
  constructors; introv Hfalse; tryfalse.
  false.
  apply Hfalse.
  do 4 eexists.  eauto.
  inverts Hfalse.

  introv Hinv Hdisj Hjoin.
  simpl in Hinv.
  unfold getmem in Hdisj.
  simpl in Hdisj.
  exists aop OO  (ge, le, x, ir, aux)  x0. 
  exists O Os.
  exists x2 x3 pre post tp logicl.
  splits;eauto.
  constructors.
  unfolds; join auto.
  splits; auto.
  unfolds; intros.
  eapply absinfer_sound.local_inv_aop_irev with aop.
  eapply Him1; eauto.
  introv Hpost.
  assert ((o1, O1, gamma'') |= EX v, POST [post, rev nil, v, logicl, t]).
  sep auto.
  split.
  unfolds.
  intros.
  eapply absinfer_sound.local_inv_aop_irev with gamma''.
  eapply Him2; eauto.

  
  introv  Hjms Hjoink  Henv.
  constructors; introv Hfa; tryfalse.
  introv Hinvs Hjm11 Hjm22 Hstep.
  invertstep idtac.
  destruct o' as [[[[]]]].
  unfolds in Henv.
  simp join.
  unfolds in Hjm11.
  unfold joinmem in Hjm11.
  simp join.
  unfold joinmem in Hjms.
  simp join.
  simpl substaskst in *.
  exists gamma'' OO0.
  exists ((x1, x12, x15, x16, x17)) Ms0 O'' Os0.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem.
  join auto.
  
  assert ((x1, x12, x13, x16, x17, O1, gamma'') |= EX v, POST [post, rev nil, v, logicl, t]).
  sep auto.
  lets Hks : Him2 H4.
  assert (  satp (x1, x12, x13, x16, x17) O1 (CurLINV pa t)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds.
  join auto.
  eapply skip_expr_eval_msim_hold; eauto.
  assert (join x0 x13 x15) by join auto.
  lets Hevvv :  evaladdr_mono H4  Hadd.
  lets Hvee : evaladdr_val_eq  Hevvv; eauto.
  eapply evaltype_eq_prop; eauto.
  assert ((x1, x12, x13, x16, x17, O1, gamma'') |= EX v, POST [post, rev nil, v, logicl, t]).
  sep auto.
  lets Hks : Him2 H4.
  assert (  satp (x1, x12, x13, x16, x17) O1 (CurLINV pa t)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds.
  join auto.
  constructors; introv Hfff; tryfalse.
  introv Hiinn Hjjm1 Hjjm2 Hstepp.
  invertstep idtac.
  
  unfolds in Hjjm1.
  unfold joinmem in Hjjm1.
  simp join.
  simpl in Hiinn.
  assert ((x7, x10, x6, x18, x19, x3, gamma'') |= p)  as Hpar.
  eapply goodfrm_prop; eauto.


  lets Hreas : store_exists_fcall H22 H8  H5 H7 Hpost. 
  
  lets Hreea : Hreas  Hpar; eauto.
  clear Hreas.
  simp join.
  exists gamma'' OO1  (x7, x10,x12, x18, x19) Ms1 O'' Os1.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem; join auto.
  assert ((x7, x10, x13, x18, x19, O1, gamma'') |= EX v, POST [post, rev nil, v, logicl, t]).
  sep auto.
  lets Hks : Him2 H17.
  assert (  satp (x7, x10, x13, x18, x19) O1 (CurLINV pa t)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds; join auto.
  constructors; introv Hfca; tryfalse.
  introv _ _ _ Hsffs.
  invertstep idtac.
  inverts Hfca.
  unfold getmem.
  simpl get_smem in *.
  simpl get_mem in *.
  simpl substaskst in *.
  introv Hmaaj Hivvv Hdssss.
  exists gamma'' OO2  O'' Os2.
  splits; eauto.
  constructors.
  assert ((x7, x10, x13, x18, x19, O1, gamma'') |= EX v, POST [post, rev nil, v, logicl, t]).
  sep auto.
  lets Hks : Him2 H17.
  assert (  satp (x7, x10, x13, x18, x19) O1 (CurLINV pa t)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds; join auto.
  unfold lift.
  exists v0.
  exists x13 x4 x12 O1 x3 O''.
  
  splits; eauto.
  simpl substmo.
  exists x1 x6 x4  empabst x3 x3.
  simpl.
  splits; eauto.
  join auto.
  splits; auto.
  unfolds; auto.

  destruct Hfca as (_&_&Hfru & _).
  false. apply Hfru.
  eexists; eauto.
  introv Hdj1   Hdinv Hddsij Hss.
  apply Hss.
  destruct o2 as [[[[]]]].
  unfolds in Hdinv.
  unfold joinmem in Hdinv.
  simp join.
  lets Hestore :  store_exist_join tp H8 H5 H7 H15.
  destruct Hestore as (M'' & Hstto).
  lets Hssx : store_mono H13 Hstto.  
  simp join.
  do 2 eexists.
  eapply ostc_step; eauto.
  eapply stmt_step ; eauto.
  constructors; eauto.
  introv _ _ _  Hlst.
  apply Hlst.
  lets Hevv : Hpem Hpost.
  destruct v;tryfalse.
  destruct o2 as  [[[[]]]].
  do 2 eexists.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply sassignrv_step; eauto.
  destruct Hfalse as (Hffz &_).
  false. apply Hffz.
  do 4 eexists;eauto.

  inverts Hres.
  eapply identity_step_msim_hold;eauto.
  splits.
  introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  splits;
    introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  introv.
  unfold nilcont.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors; eauto.
  eapply evaltype_eq_prop; eauto.
  eapply identity_step_msim_hold;eauto.
  splits.
  introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  splits;
    introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  introv.
  unfolds nilcont.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply spcall_step with (t:=t0); eauto.
  eapply skip_expr_eval_msim_hold; eauto.
  eapply call_ignore_exprlist_sim; eauto.
  constructors; introv Hfalse; tryfalse.
  false.
  apply Hfalse.
  do 4 eexists.  eauto.
  inverts Hfalse.


  introv Hinv Hdisj Hjoin.
  simpl in Hinv.
  unfold getmem in Hdisj.
  simpl in Hdisj.
  exists aop OO  (ge, le, x, ir, aux)  x0. 
  exists O Os.
  exists x2 x3 pre post tp logicl.
  splits;eauto.
  constructors.
  unfolds; join auto.
  assert (t0::nil=rev(t0::nil)).
  simpl;auto.
  rewrite H1.
  assert (v::nil=rev(v::nil)).
  simpl;auto.
  rewrite H4.
  assert (rev(t0::nil++tl0) = rev tl0 ++ rev (t0 :: nil)).
  rewrite <- rev_app_distr;auto.
  rewrite <- H11.
  assert (rev(v::nil++vl0) = rev vl0 ++ rev (v :: nil)).
  rewrite <- rev_app_distr;auto.
  rewrite <- H12.
  apply tl_vl_match_rev.
  simpl;auto.
  rewrite rev_app_distr.
  simpl.
  rewrite rev_involutive.
  auto.
  rewrite <- list_rev_prop.
  eapply good_fun_asrt_absop; eauto.
  apply getprop.
  split; auto.
  unfolds; intros.
  eapply absinfer_sound.local_inv_aop_irev with aop.
  eapply Him1; eauto.
  splits; eauto.
  introv Hpost.
  assert ((o1, O1, gamma'') |= EX v0, POST [post, rev (rev vl0 ++ v :: nil), v0, logicl, t]).
  sep auto.
  split.
  unfolds.
  intros.
  eapply absinfer_sound.local_inv_aop_irev with gamma''.
  eapply Him2; eauto.
  rewrite  list_rev_prop;auto.

  introv  Hjms Hjoink  Henv.
  constructors; introv Hfa; tryfalse.
  introv Hinvs Hjm11 Hjm22 Hstep.
  invertstep idtac.
  destruct o' as [[[[]]]].
  unfolds in Henv.
  simp join.
  unfolds in Hjm11.
  unfold joinmem in Hjm11.
  simp join.
  unfold joinmem in Hjms.
  simp join.
  simpl substaskst in *.
  exists gamma'' OO0.
  exists ((x1, x12, x15, x16, x17)) Ms0 O'' Os0.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem.
  join auto.
  
  assert ((x1, x12, x13, x16, x17, O1, gamma'') |= EX v1, POST[post, rev (rev vl0 ++ v :: nil),v1, logicl, t]).
  sep auto.
  rewrite  <- list_rev_prop in H4.
  lets Hks : Him2 H4.
  assert (  satp (x1, x12, x13, x16, x17) O1 (CurLINV pa t)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds.
  join auto.
  eapply skip_expr_eval_msim_hold with (e:=eaddrof e); eauto.
  assert (join x0 x13 x15) by join auto.
  lets Hevvv :  evaladdr_mono H4  Hadd.
  lets Hvee : evaladdr_val_eq  Hevvv; eauto.
  eapply evaltype_eq_prop; eauto.

  assert ((x1, x12, x13, x16, x17, O1, gamma'') |=EX v1,  POST [post, rev (rev vl0 ++ v :: nil),  v1, logicl, t]).
  sep auto.
  rewrite  <- list_rev_prop in H4.
  lets Hks : Him2 H4.
  assert (  satp (x1, x12, x13, x16, x17) O1 (CurLINV pa t)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds.
  join auto.
  constructors; introv Hfff; tryfalse.
  introv Hiinn Hjjm1 Hjjm2 Hstepp.
  invertstep idtac.
  
  unfolds in Hjjm1.
  unfold joinmem in Hjjm1.
  simp join.
  simpl in Hiinn.
  assert ((x7, x10, x6, x18, x19, x3, gamma'') |= p)  as Hpar.
  eapply goodfrm_prop; eauto.
  lets Hreas : store_exists_fcall H26 H8  H5 H12  Hpost. 
  
  lets Hreea : Hreas  Hpar; eauto.
  clear Hreas.
  simp join.
  exists gamma'' OO1  (x7, x10,x12, x18, x19) Ms1 O'' Os1.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem; join auto.
  assert ((x7, x10, x13, x18, x19, O1, gamma'') |= EX v1, POST  [post, rev (rev vl0 ++ v :: nil),  v1, logicl, t]).
  sep auto.
  rewrite  <- list_rev_prop in H21.
  lets Hks : Him2 H21.
  assert (  satp (x7, x10, x13, x18, x19) O1 (CurLINV pa t)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds; join auto.
  constructors; introv Hfca; tryfalse.
  introv _ _ _ Hsffs.
  invertstep idtac.
  inverts Hfca.
  unfold getmem.
  simpl get_smem in *.
  simpl get_mem in *.
  simpl substaskst in *.
  introv Hmaaj Hivvv Hdssss.
  exists gamma'' OO2  O'' Os2.
  splits; eauto.
  constructors.
  assert ((x7, x10, x13, x18, x19, O1, gamma'') |= EX v1, POST  [post, rev (rev vl0 ++ v :: nil),  v1, logicl, t]).
  sep auto.
  rewrite  <- list_rev_prop in H21.
  lets Hks : Him2 H21.
  assert (  satp (x7, x10, x13, x18, x19) O1 (CurLINV pa t)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds; join auto.
  unfold lift.
  exists v1.
  exists x13 x4 x12 O1 x3 O''.
  
  splits; eauto.
  simpl substmo.
  rewrite   list_rev_prop; auto.
  exists x1 x6 x4  empabst x3 x3.
  simpl.
  splits; eauto.
  join auto.
  splits; auto.
  unfolds; auto.

  destruct Hfca as (_&_&Hfru & _).
  false. apply Hfru.
  eexists; eauto.
  introv Hdj1   Hdinv Hddsij Hss.
  apply Hss.
  destruct o2 as [[[[]]]].
  unfolds in Hdinv.
  unfold joinmem in Hdinv.
  simp join.
  lets Hestore :  store_exist_join tp H8  H5 H19; eauto.
  destruct Hestore as (M'' & Hstto).
  lets Hssx : store_mono H17 Hstto.  
  simp join.
  do 2 eexists.
  eapply ostc_step; eauto.
  eapply stmt_step ; eauto.
  constructors; eauto.
  introv _ _ _  Hlst.
  apply Hlst.
  lets Hevv : Hpem Hpost.
  destruct v0;tryfalse.
  destruct o2 as  [[[[]]]].
  do 2 eexists.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply sassignrv_step; eauto.
  destruct Hfalse as (Hffz &_).
  false. apply Hffz.
  do 4 eexists;eauto.
Qed.


Lemma calle_rule_lvar_sound: 
  forall f x (Spec:funspec) sd t I r ri pre post P p el v' vl  tp tl logicl tid pa,  
    GoodFrm  p ->  
    retpost post ->
    Spec f = Some (pre, post,  (tp ,tl))->
    P ==> (PRE[pre,vl,logicl,tid] ** LV x @ t |-> v' ** p) ->
    P ==> Rvl el @ tl ==  vl ->
    tl_vl_match tl vl = true ->
    PRE [pre, vl, logicl, tid] ==> CurLINV pa tid -> 
    EX v : option val, POST [post, vl, v, logicl, tid]  ==> CurLINV pa tid->
    RuleSem Spec  sd pa I r ri P
            (scalle (evar x) f el) (EX v, POST[post, vl, Some v,logicl,tid] ** LV x @ t |-> v ** p ) tid.
Proof.
  introv Hgf Hpem Hret Hpre Hf   Htlvlmatch Him1 Him2.
  introv Hsat.
  destruct Hsat as (Hsat & Hlinv).
  lets Hel :  Hpre  Hsat.
  destruct o as [[[[ge le] M] ir] aux].
  simpl in Hel.
  simp join.
  unfold emposabst in H18, H15.
  subst.
  assert (x14=x6) by join auto.
  assert (empabst= x9) by join auto.
  subst x14 x9.
  assert (x10 = x4) by join auto.
  subst x10.
  clear H10 H7 H12.
  lets Hk : Hf Hsat.
  simpl in Hk.
  lets Hres :  evalexprlist_imply_evalexprlist' Hk.
  clear Hk.
  destruct el.
  inverts Hres.
  clear    Hf.
  eapply identity_step_msim_hold;eauto.
  unfolds nilcont.
  unfold notabortm.
  splits.
  introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  splits;
    introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  introv.
  unfolds nilcont.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors; eauto.
  simpl.
  rewrite H13; eauto.
  eapply identity_step_msim_hold;eauto.
  unfold notabortm.
  splits.
  introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  splits;
    introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  introv.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors; eauto.
  constructors; introv Hfalse; tryfalse.
  false.
  apply Hfalse.
  do 4 eexists.  eauto.
  inverts Hfalse.

  introv Hinv Hdisj Hjoin.
  simpl in Hinv.
  unfold getmem in Hdisj.
  simpl in Hdisj.
  exists aop OO  (ge, le, x0, ir, aux)  x1. 
  exists O Os.
  exists x3 x4 pre post tp logicl.
  splits;eauto.
  constructors.
  unfolds; join auto.
  splits; auto.
  unfolds; intros.
  eapply absinfer_sound.local_inv_aop_irev with aop.
  eapply Him1; eauto.
  introv Hpost.
  assert ((o1, O1, gamma'') |= EX v, POST [post, rev nil, v, logicl, tid]).
  sep auto.
  split.
  unfolds.
  intros.
  eapply absinfer_sound.local_inv_aop_irev with gamma''.
  eapply Him2; eauto.
  
  introv  Hjms Hjoink  Henv.
  constructors; introv Hfa; tryfalse.
  introv Hinvs Hjm11 Hjm22 Hstep.
  invertstep idtac.
  destruct o' as [[[[]]]].
  unfolds in Henv.
  simp join.
  unfolds in Hjm11.
  unfold joinmem in Hjm11.
  simp join.
  unfold joinmem in Hjms.
  simp join.
  simpl substaskst in *.
  exists gamma'' OO0.
  exists ((x2, x13, x16, x17, x18)) Ms0 O'' Os0.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem.
  join auto.
  
  assert ((x2, x13, x14, x17, x18, O1, gamma'') |= EX v, POST [post, rev nil, v, logicl, tid]).
  sep auto.
  lets Hks : Him2 H1.
  assert (  satp (x2, x13, x14, x17, x18) O1 (CurLINV pa tid)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds.
  join auto.
  eapply skip_expr_eval_msim_hold; eauto.
  simpl.
  rewrite H13; eauto.

  assert ((x2, x13, x14, x17, x18, O1, gamma'') |= EX v, POST [post, rev nil, v, logicl, tid]).
  sep auto.
  lets Hks : Him2 H1.
  assert (  satp (x2, x13, x14, x17, x18) O1 (CurLINV pa tid)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds.
  join auto.
  constructors; introv Hfff; tryfalse.
  introv Hiinn Hjjm1 Hjjm2 Hstepp.
  invertstep idtac.
  
  unfolds in Hjjm1.
  unfold joinmem in Hjjm1.
  simp join.
  simpl in Hiinn.
  assert ((x8, x11, x7, x20 ,x21, x4, gamma'') |= p)  as Hpar.
  eapply goodfrm_prop; eauto.

  lets Hreas : store_exists_fcall H22  H14  H5 H6 Hpost. 
  lets Hreea : Hreas  Hpar; eauto.
  clear Hreas.
  simp join.
  exists gamma'' OO1  (x8, x11,x13, x20, x21) Ms1 O'' Os1.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem; join auto.
  assert ((x8, x11, x14, x20, x21, O1, gamma'') |= EX v, POST [post, rev nil, v, logicl, tid]).
  sep auto.
  lets Hks : Him2 H17.
  assert (  satp (x8, x11, x14, x20, x21) O1 (CurLINV pa tid)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds; join auto.
  constructors; introv Hfca; tryfalse.
  introv _ _ _ Hsffs.
  invertstep idtac.
  inverts Hfca.
  unfold getmem.
  simpl get_smem in *.
  simpl get_mem in *.
  simpl substaskst in *.
  introv Hmaaj Hivvv Hdssss.
  exists gamma'' OO2  O'' Os2.
  splits; eauto.
  constructors.
  assert ((x8, x11, x14, x20, x21, O1, gamma'') |= EX v, POST [post, rev nil, v, logicl, tid]).
  sep auto.
  lets Hks : Him2 H17.
  assert (  satp (x8, x11, x14, x20, x21) O1 (CurLINV pa tid)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds; join auto.
  unfold lift.
  exists v0.
  exists x14 x5 x13 O1 x4 O''.
  
  splits; eauto.
  simpl substmo.
  exists x2 x7 x5  empabst x4 x4.
  simpl.
  splits; eauto.
  join auto.
  exists x19 empmem x2 x2 empabst empabst.  
  exists empabst.
  splits; eauto.
  join auto.
  join auto.
  exists x19.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.

  destruct Hfca as (_&_&Hfru & _).
  false. apply Hfru.
  eexists; eauto.
  introv Hdj1   Hdinv Hddsij Hss.
  apply Hss.
  destruct o2 as [[[[]]]].
  unfolds in Hdinv.
  unfold joinmem in Hdinv.
  simp join.
  lets Hestore :  store_exist_join t H14 H5 H6 H15. 
  destruct Hestore as (M'' & Hstto).
  lets Hssx : store_mono H11 Hstto.  
  simp join.
  do 2 eexists.
  eapply ostc_step; eauto.
  eapply stmt_step ; eauto.
  constructors; eauto.
  introv _ _ _  Hlst.
  apply Hlst.
  lets Hevv : Hpem Hpost.
  destruct v;tryfalse.
  destruct o2 as  [[[[]]]].
  do 2 eexists.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply sassignrv_step; eauto.
  destruct Hfalse as (Hffz &_).
  false. apply Hffz.
  do 4 eexists;eauto.

  inverts Hres.
  eapply identity_step_msim_hold;eauto.
  splits.
  introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  splits;
    introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  introv.
  unfold nilcont.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  constructors; eauto.
  simpl; rewrite H13; eauto.
  eapply identity_step_msim_hold;eauto.
  splits.
  introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  splits;
    introv Hfalse; unfolds in Hfalse; simp join; tryfalse.
  introv.
  unfolds nilcont.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply spcall_step with (t:=t0); eauto.
  eapply skip_expr_eval_msim_hold; eauto.
  eapply call_ignore_exprlist_sim; eauto.
  constructors; introv Hfalse; tryfalse.
  false.
  apply Hfalse.
  do 4 eexists.  eauto.
  inverts Hfalse.


  introv Hinv Hdisj Hjoin.
  simpl in Hinv.
  unfold getmem in Hdisj.
  simpl in Hdisj.
  exists aop OO  (ge, le, x0, ir, aux)  x1. 
  exists O Os.
  exists x3 x4 pre post tp logicl.
  splits;eauto.
  constructors.
  unfolds; join auto.
  assert (t0::nil=rev(t0::nil)).
  simpl;auto.
  rewrite H.
  assert (v::nil=rev(v::nil)).
  simpl;auto.
  rewrite H1.
  assert (rev(t0::nil++tl0) = rev tl0 ++ rev (t0 :: nil)).
  rewrite <- rev_app_distr;auto.
  rewrite <- H8.
  assert (rev(v::nil++vl0) = rev vl0 ++ rev (v :: nil)).
  rewrite <- rev_app_distr;auto.
  rewrite <- H10.
  apply tl_vl_match_rev.
  simpl;auto.
  rewrite rev_app_distr.
  simpl.
  rewrite rev_involutive.
  auto.
  rewrite <- list_rev_prop.
  eapply good_fun_asrt_absop; eauto.
  apply getprop.
  split; auto.
  unfolds; intros.
  eapply absinfer_sound.local_inv_aop_irev with aop.
  eapply Him1; eauto.
  splits; eauto.
  introv Hpost.
  assert ((o1, O1, gamma'') |= EX v0, POST [post, rev (rev vl0 ++ v :: nil), v0, logicl, tid]).
  sep auto.
  split.
  unfolds.
  intros.
  eapply absinfer_sound.local_inv_aop_irev with gamma''.
  eapply Him2; eauto.
  rewrite  list_rev_prop;auto.

  introv  Hjms Hjoink  Henv.
  constructors; introv Hfa; tryfalse.
  introv Hinvs Hjm11 Hjm22 Hstep.
  invertstep idtac.
  destruct o' as [[[[]]]].
  unfolds in Henv.
  simp join.
  unfolds in Hjm11.
  unfold joinmem in Hjm11.
  simp join.
  unfold joinmem in Hjms.
  simp join.
  simpl substaskst in *.
  exists gamma'' OO0.
  exists ((x2, x13, x16, x17, x18)) Ms0 O'' Os0.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem.
  join auto.
  
  assert ((x2, x13, x14, x17, x18, O1, gamma'') |= EX v1, POST[post, rev (rev vl0 ++ v :: nil),v1, logicl, tid]).
  sep auto.
  rewrite  <- list_rev_prop in H1.
  lets Hks : Him2 H1.
  assert (  satp (x2, x13, x14, x17, x18) O1 (CurLINV pa tid)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds.
  join auto.
  eapply skip_expr_eval_msim_hold with (e:=eaddrof (evar x)); eauto.
  simpl.
  rewrite H13; eauto.
  assert ((x2, x13, x14, x17, x18, O1, gamma'') |=EX v1,  POST [post, rev (rev vl0 ++ v :: nil),  v1, logicl, tid]).
  sep auto.
  rewrite  <- list_rev_prop in H1.
  lets Hks : Him2 H1.
  assert (  satp (x2, x13, x14, x17, x18) O1 (CurLINV pa tid)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds.
  join auto.
  constructors; introv Hfff; tryfalse.
  introv Hiinn Hjjm1 Hjjm2 Hstepp.
  invertstep idtac.
  
  unfolds in Hjjm1.
  unfold joinmem in Hjjm1.
  simp join.
  simpl in Hiinn.
  assert ((x8, x11, x7, x20, x21, x4, gamma'') |= p)  as Hpar.
  eapply goodfrm_prop; eauto.
  lets Hreas : store_exists_fcall H26 H14  H5  H10  Hpost.   
  lets Hreea : Hreas  Hpar; eauto.
  clear Hreas.
  simp join.
  exists gamma'' OO1  (x8, x11,x13, x20, x21) Ms1 O'' Os1.
  splits; eauto.
  constructors.
  unfolds.
  unfold joinmem; join auto.
  assert ((x8, x11, x14, x20, x21, O1, gamma'') |= EX v1, POST  [post, rev (rev vl0 ++ v :: nil),  v1, logicl, tid]).
  sep auto.
  rewrite  <- list_rev_prop in H21.
  lets Hks : Him2 H21.
  assert (  satp (x8, x11, x14, x20, x21) O1 (CurLINV pa tid)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds; join auto.
  constructors; introv Hfca; tryfalse.
  introv _ _ _ Hsffs.
  invertstep idtac.
  inverts Hfca.
  unfold getmem.
  simpl get_smem in *.
  simpl get_mem in *.
  simpl substaskst in *.
  introv Hmaaj Hivvv Hdssss.
  exists gamma'' OO2  O'' Os2.
  splits; eauto.
  constructors.
  assert ((x8, x11, x14, x20, x21, O1, gamma'') |= EX v1, POST  [post, rev (rev vl0 ++ v :: nil),  v1, logicl, tid]).
  sep auto.
  rewrite  <- list_rev_prop in H21.
  lets Hks : Him2 H21.
  assert (  satp (x8, x11, x14, x20, x21) O1 (CurLINV pa tid)).
  unfolds.
  eapply absinfer_sound.local_inv_aop_irev with gamma''; eauto.
  eapply absinfer_sound.join_satp_local_inv; eauto.
  unfolds; join auto.
  unfold lift.
  exists v1.
  exists x14 x5 x13 O1 x4 O''.
  
  splits; eauto.
  simpl substmo.
  rewrite   list_rev_prop; auto.
  exists x2 x7 x5  empabst x4 x4.
  simpl.
  splits; eauto.
  join auto.
  exists x19 empmem x2 x2 empabst empabst.  
  exists empabst.
  splits; eauto.
  join auto.
  join auto.
  exists x19.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.

  destruct Hfca as (_&_&Hfru & _).
  false. apply Hfru.
  eexists; eauto.
  introv Hdj1   Hdinv Hddsij Hss.
  apply Hss.
  destruct o2 as [[[[]]]].
  unfolds in Hdinv.
  unfold joinmem in Hdinv.
  simp join.
  lets Hestore :  store_exist_join t H14  H5 H19; eauto.
  destruct Hestore as (M'' & Hstto).
  lets Hssx : store_mono H17 Hstto.  
  simp join.
  do 2 eexists.
  eapply ostc_step; eauto.
  eapply stmt_step ; eauto.
  constructors; eauto.
  introv _ _ _  Hlst.
  apply Hlst.
  lets Hevv : Hpem Hpost.
  destruct v0;tryfalse.
  destruct o2 as  [[[[]]]].
  do 2 eexists.
  eapply ostc_step; eauto.
  eapply stmt_step; eauto.
  eapply sassignrv_step; eauto.
  destruct Hfalse as (Hffz &_).
  false. apply Hffz.
  do 4 eexists;eauto.
Qed.


