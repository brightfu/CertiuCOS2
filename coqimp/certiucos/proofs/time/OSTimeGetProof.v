(************************uc/OS-II*****************************)  
(************************OS_TIME.c****************************)
(***************Proofs for API: INT32U OSTimeGet (void)*******)
(**********************C Source Code:*************************)
(**             INT32U  OSTimeGet (void)                    **)
(**              {                                          **)
(**              1  OS_ENTER_CRITICAL();                    **)
(**              2  ticks = OSTime;                         **)
(**              3  OS_EXIT_CRITICAL();                     **)
(**              4  return (ticks);                         **)
(**              }                                          **)
(*************************************************************)

Require Import ucos_include.
Require Import absop_rules.
Open Scope code_scope.

Lemma OSTimeGetRight: 
  forall r p tid, 
    Some r = BuildRetA' os_api OSTimeGet tmgetapi nil OSLInv tid init_lg->
    Some p = BuildPreA' os_api OSTimeGet tmgetapi nil OSLInv tid init_lg ->
    exists t decl1 decl2 s,
      os_api OSTimeGet = Some (t,decl1,decl2,s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |-tid {{p}} s {{Afalse}}.
Proof.  
  init spec. (*Initialize Specification*)
  hoare forward prim. (*L1:  OS_ENTER_CRITICAL();*)
  hoare unfold pre.
  (*L2: ticks = OSTime; *)
  hoare forward.
  hoare normal pre.
  hoare abscsq.
  apply noabs_oslinv.
  eapply OSTimeGet_high_level_step.
  pauto.
  hoare forward prim.
  sep_unfold; sep pauto.
  pure_auto.
  hoare forward.   (*L4: return (ticks); *)
Qed.

(*
Lemma OSTimeGetRight': 

    Some r = BuildRetA' os_api OSTimeGet tmgetapi nil ->
    Some p = BuildPreA' os_api OSTimeGet tmgetapi nil ->
    exists t decl1 decl2 s,
      os_api OSTimeGet = Some (t,decl1,decl2,s) /\
      {|OSQ_spec , GetHPrio, I, r, Afalse|} |- {{p}} s {{Afalse}}.
Proof.
  intros.
  unfold BuildRetA' in H.
  simpl in H.
  inverts H.
  unfold BuildPreA' in H0.
  (let xy := fresh in
   remember (os_api OSTimeGet) as xy;
   destruct xy as [xy| ];
   tryfalse;
   (let a := fresh in
    destruct xy as (((?, a)));
    (let b := fresh in
     remember (dl_vl_match a (rev nil)) as b;
     destruct b;
     tryfalse))).
  inverts H0.
  apply eq_sym in HeqH2.
  simpl in HeqH2.
  destruct H1.
  simpl in HeqH2.
  2:tryfalse.
  clear HeqH2.
  unfolds in HeqH.
  unfold api_fun_list in HeqH.
  simpl in HeqH.
  inverts HeqH.
  remember (buildp (dladd ⌞ ⌟ ⌞ticks @ Int32u ⌟) nil) as X.
  destruct X.
  inverts H2.
  do 4 eexists.
  split.
  eauto.
  Focus 2.
  tryfalse.
  eapply backward_rule1.
  apply Aop_Aop'_eq'.
  eapply r_conseq_rule.
  intros.
  apply Aop_Aop'_eq.
  exact H.
  intros.
  exact H.
  simpl in HeqX.
  inverts HeqX.
  hoare normal pre.
  hoare_ex_intro.
  eapply seq_rule.
  eapply forward_rule2.
  eapply backward_rule1.
  intros.
  let t := toTree ( LV ticks @ Int32u |-> v' **
                       <|| tmgetcode nil ||>  **
                       Aie true **
                       Ais nil **
                       Acs nil ** Aisr empisr ** A_dom_lenv ((ticks, Int32u) :: nil)) in
  pose (H' := sliftE t 4);
    cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                          myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
    apply H' in H;
    clear H'.
  exact H.
  eapply backward_rule1.
  intros.
  let t := toTree (Acs nil **
         LV ticks @ Int32u |-> v' **
          <|| tmgetcode nil ||>  **
         Aie true **
         Ais nil ** Aisr empisr ** A_dom_lenv ((ticks, Int32u) :: nil)) in
  pose (H' := sliftE t 4);
    cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                          myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
    apply H' in H;
    clear H'.
  eauto.
  eapply backward_rule1.
  intros.
  let t := toTree (  Ais nil **
   Acs nil **
   LV ticks @ Int32u |-> v' **
    <|| tmgetcode nil ||>  **
   Aie true ** Aisr empisr ** A_dom_lenv ((ticks, Int32u) :: nil)) in
  pose (H' := sliftE t 4);
    cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                          myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
    apply H' in H;
    clear H'.
  eauto.
  eapply backward_rule1.
  intros.
  let t := toTree (Aie true **
         Ais nil **
         Acs nil **
         LV ticks @ Int32u |-> v' **
          <|| tmgetcode nil ||>  **
         Aisr empisr ** A_dom_lenv ((ticks, Int32u) :: nil)) in
  pose (H' := sliftE t 5);
    cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                          myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
    apply H' in H;
    clear H'.
  eauto.
  eapply backward_rule1.
  intros.
  let t := toTree (Aisr empisr **
     Aie true **
     Ais nil **
     Acs nil **
     LV ticks @ Int32u |-> v' **
      <|| tmgetcode nil ||>  ** A_dom_lenv ((ticks, Int32u) :: nil))  in
  pose (H' := sliftE t 5);
    cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                          myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
    apply H' in H;
    clear H'.
  eauto.
  eapply encrit1_rule'_ISnil_ISRemp.
  intros.
  exact H.
  simpl.
  splits;auto.
  intros.
  exact H.
  unfold OSInv.
  hoare normal pre.
  hoare_ex_intro.
  eapply backward_rule1.
  intros.
  match type of H with
    | _ |= ?A => 
      let t := toTree A in
      pose (H' := sliftE t 18);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                              myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
        apply H' in H;
        clear H'
  end.
  eauto.
  eapply backward_rule1.
  intros.
  match type of H with
    | _ |= ?A => 
      let t := toTree A in
      pose (H' := sliftE t 18);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                              myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
        apply H' in H;
        clear H'
  end.
  eauto.
  apply pure_split_rule'.
  intros.
  apply pure_split_rule'.
  intros.
  unfold AOSTime.
  eapply seq_rule.
  eapply backward_rule1.
  intros.
  let H' := fresh in
  match type of H1 with
    | _ |= ?A => 
      let t := toTree A in
      pose (H' := sliftE t 24);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                              myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
        apply H' in H1;
        clear H'
  end.
  eauto.
  eapply backward_rule1.
  intros.
  match type of H1 with
    | _ |= ?A => 
      let t := toTree A in
      pose (H' := sliftE t 19);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                              myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
        apply H' in H1;
        clear H'
  end.
  eauto.
  eapply assign_rule_lvar.
  intros.
  split.
  intros.
  exact H1.
  intros.
  exact H1.
  intros.
  let H' := fresh in
  match type of H1 with
    | _ |= ?A => 
      let t := toTree A in
      pose (H' := sliftE t 12);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                              myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
        apply H' in H1;
        clear H'
  end.
  eauto.
  let H' := fresh in
  match type of H1 with
    | _ |= ?A => 
      let t := toTree A in
      pose (H' := sliftE t 24);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                              myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
        apply H' in H1;
        clear H'
  end.
  eauto.
  eapply gvar_rv.
  exact H1.
  simpl.
  auto.
  simpl.
  auto.
  apply eq_int.
  split.
  eauto.
  eauto.
  eapply backward_rule1.
  intros.
  let H' := fresh in
  match type of H1 with
    | _ |= ?A => 
      let t := toTree A in
      pose (H' := sliftE t 17);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                              myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
        apply H' in H1;
        clear H'
  end.
  eauto.
  eapply backward_rule1.
  intros.
  match type of H1 with
    | _ |= ?A => 
      let t := toTree A in
      pose (H' := sliftE t 17);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                              myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
        apply H' in H1;
        clear H'
  end.
  eauto.
  eapply backward_rule1.
  intros.
  match type of H1 with
    | _ |= ?A => 
      let t := toTree A in
      pose (H' := sliftE t 17);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                              myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
        apply H' in H1;
        clear H'
  end.
  eauto.
  eapply backward_rule1.
  intros.
  match type of H1 with
    | _ |= ?A => 
      let t := toTree A in
      pose (H' := sliftE t 17);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                              myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
        apply H' in H1;
        clear H'
  end.
  eauto.
  eapply backward_rule1.
  intros.
  match type of H1 with
    | _ |= ?A => 
      let t := toTree A in
      pose (H' := sliftE t 4);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                              myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
        apply H' in H1;
        clear H'
  end.
  eauto.
  eapply abscsq_rule'.
  eapply OSTimeGet_high_level_step.
  pauto.
  eapply seq_rule.
  eapply excrit1_rule'_ISnil_ISRemp'.
  intros.
  unfold OSInv.
  sep normal.
  sep eexists.
  sep split.
  sep split in H1.
  instantiate (1:=A_dom_lenv ((ticks, Int32u) :: nil) **LV ticks @ Int32u |-> Vint32 v'15 ).
  sep split.
  let H := fresh in
      match goal with
        | |- _ |= ?A =>
          let t := toTree A in
          pose (H := sliftI t 19);
            cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
            apply H;
            clear H
      end.
  let H := fresh in
  match goal with
    | |- _ |= ?A =>
      let t := toTree A in
      pose (H := sliftI t 16);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
        apply H; clear H
  end.
  let H := fresh in
  match goal with
    | |- _ |= ?A =>
      let t := toTree A in
      pose (H := sliftI t 16);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
        apply H; clear H
  end.
  let H := fresh in
  match goal with
    | |- _ |= ?A =>
      let t := toTree A in
      pose (H := sliftI t 16);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
        apply H; clear H
  end.
  let H := fresh in
  match goal with
    | |- _ |= ?A =>
      let t := toTree A in
      pose (H := sliftI t 16);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
        apply H; clear H
  end.
  exact H1.
  auto.
  sep split in H1.
  eauto.
  sep split in H1.
  eauto.
  sep split in H1.
  eauto.
  sep split in H1.
  eauto.
  eauto.
  eauto.
  simpl.
  split;auto.
  eapply rete_rule'.
  intros.
  match type of H1 with
    | _ |= ?A => 
      let t := toTree A in
      pose (H' := sliftE t 6);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn'
                              myAppAsrtTree list_to_asrtTree_simpl unTree] in H';
        apply H' in H1; clear H'
  end.
  eapply lvar_rv.
  eauto.
  simpl.
  auto.
  intros.
  sep normal.
  exists (Vint32 v'15).
  let H := fresh in
  match goal with
    | |- _ |= ?A =>
      let t := toTree A in
      pose (H := sliftI t 5);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
        apply H; clear H
  end.
  let H := fresh in
  match goal with
    | |- _ |= ?A =>
      let t := toTree A in
      pose (H := sliftI t 4);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
        apply H; clear H
  end.
  let H := fresh in
  match goal with
    | |- _ |= ?A =>
      let t := toTree A in
      pose (H := sliftI t 4);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
        apply H; clear H
  end.
  let H := fresh in
  match goal with
    | |- _ |= ?A =>
      let t := toTree A in
      pose (H := sliftI t 4);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
        apply H; clear H
  end.
  let H := fresh in
  match goal with
    | |- _ |= ?A =>
      let t := toTree A in
      pose (H := sliftI t 5);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
        apply H; clear H
  end.
  let H := fresh in
  match goal with
    | |- _ |= ?A =>
      let t := toTree A in
      pose (H := sliftI t 6);
        cbv [asrtTree_to_list asrtTree_to_list' listliftn listliftn' myAppAsrtTree list_to_asrtTree_simpl unTree] in H;
        apply H; clear H
  end.
  auto.
Qed.*)

Close Scope code_scope.
