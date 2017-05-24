Require Import Coq.Bool.IfProp.
Require Import Coq.Logic.Classical_Prop.
Require Import Recdef.
Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import include_frm.
Require Import sep_auto.
Require Import hoare_conseq.
Require Import derived_rules.
Require Import symbolic_execution.
Require Import math_auto.
Require Import pure.
Require Import os_code_defs.
Require Import tv_match.
Require Import os_inv.
Require Import inv_prop.
Require Import abs_op.
Require Import cancel_abs.
Require Import hoare_assign.
Require Import hoare_tactics.
Require Import ucos_frmaop.
Set Implicit Arguments.



Open Scope nat_scope.

Lemma empisr_isr_is_prop:
  forall is, isr_is_prop empisr is.
Proof.
  intros.
  unfolds.
  intros.
  unfold empisr.
  auto.
Qed.

Lemma empisr_isr_is_prop_P:
  forall s P,
    getisr (gettaskst s) = empisr ->
    s |=  P ->
    s |= (([|empisr
               2%nat = true|] //\\ Aisr empisr) \\//
                                                ([|empisr 2%nat = false|] //\\ Aisr empisr) ** aemp_isr_is) ** P.
Proof.
  intros.
  remember  (([|empisr 2%nat = true|] //\\ Aisr empisr) \\//
                                                        ([|empisr 2%nat = false|] //\\ Aisr empisr) ** aemp_isr_is) as X.
  simpl in *;simpljoin.
  destruct_s s.
  trysimplall.
  subst.
  exists (emp:mem) m.
  do 4 eexists;simpljoin;eauto.
  splits;eauto;simpljoin.
  right.
  unfold aemp_isr_is.
  simpl.
  do 6 eexists;splits;simpljoin;eauto.
  instantiate (2:= emp).
  simpljoin.
  instantiate (2:= emp).
  simpljoin.
  splits;auto.
  splits;auto.
  unfolds;auto.
  unfolds;auto.
  do 6 eexists;splits;simpljoin;eauto.
  instantiate (2:= emp).
  simpljoin.
  instantiate (2:= emp).
  simpljoin.
  split;auto.
  unfolds;auto.
  do 8 eexists;splits;simpljoin;eauto.
  instantiate (2:= emp).
  simpljoin.
  instantiate (2:= emp).
  simpljoin.
  splits;eauto.
  unfolds;auto.
  do 6 eexists;splits;simpljoin;eauto.
  simpljoin.
  instantiate (1:=emp).
  simpljoin.
  splits;eauto.
  unfolds;auto.
  apply empisr_isr_is_prop.
  unfolds;auto.
Qed.

Lemma atoy_inv_elim:
  forall P, OSInv ** atoy_inv ** P ==> OSInv ** atoy_inv' ** P.
Proof.
  intros.
  sep cancel 3%nat 3 %nat.
  unfold atoy_inv in *.
  sep cancel 2%nat 2%nat.
  unfold OSInv in *;unfold A_isr_is_prop in *.
  sep auto.
Qed.

Lemma atoy_inv_add:
  forall P, OSInv ** atoy_inv' ** P ==> OSInv ** atoy_inv ** P.
Proof.
  intros.
  sep cancel 3%nat 3 %nat.
  unfold atoy_inv in *.
  sep cancel 2%nat 2%nat.
  unfold OSInv in *;unfold A_isr_is_prop in *.
  sep auto.
Qed.

Lemma simpl_inv_encrit':
  forall P,
    Aisr empisr ** invlth_isr I 0%nat INUM ** P ==> Aisr empisr ** OSInv ** atoy_inv ** P.
Proof.
  intros.
  unfold invlth_isr in *.
  unfold starinv_isr in *.
  rewrite NPeano.Nat.sub_0_r in *.
  unfold INUM in *.
  unfold I in *.
  unfold getinv in *.
  sep normal in H.
  sep destruct H.
  sep cancel 5%nat 4%nat.
  sep split in H.
  sep split; auto.
  unfold sat in *; fold sat in *;
  destruct_s s; trysimplall; simpljoin.
  destruct H4, H9, H10; simpljoin; try solve [ unfold empisr in *; tryfalse ].
  exists x7 x17 x3 x14 x20 x6.
  splits;eauto.
  assert (x23 = x2).
  join auto.
  subst x23.
  simpl in H30.
  simpljoin.
  join auto.
  join auto.
  assert (x26 = x5).
  join auto.
  subst x26.
  simpl in H30.
  join auto.
  join auto.
Qed.

Lemma simpl_inv_encrit:
  forall P,
    Aisr empisr ** invlth_isr I 0%nat INUM ** P ==> Aisr empisr ** OSInv ** atoy_inv' ** P.
Proof.
  intros.
  apply simpl_inv_encrit' in H.
  sep cancel 1%nat 1%nat.
  apply atoy_inv_elim;auto.
Qed.

Lemma simpl_inv_excrit' :
  forall P,
    Aisr empisr ** OSInv ** atoy_inv ** P ==> Aisr empisr ** invlth_isr I 0%nat INUM ** P.
Proof.
  intros.
  sep cancel 4%nat 3%nat.
  unfold invlth_isr in *.
  unfold starinv_isr in *.
  rewrite NPeano.Nat.sub_0_r in *.
  unfold INUM in *.
  unfold I in *.
  unfold getinv in *.
  destruct_s s.
  sep split in H.
  simpl in H0.
  subst i.
  sep normal.
  exists empisr empisr empisr.
  sep split; auto.  
  eapply empisr_isr_is_prop_P.
  simpl;auto.
  unfold sat in *; fold sat in *;
  trysimplall; simpljoin.
  exists x0 x m x3 x2 o;simpljoin;splits;auto;try solve [join auto].
  right.
  exists (emp:mem) x0 x0.
  exists (emp:osabst) x3 x3.
  simpljoin;splits;auto;try solve[join auto].
  right; do 6 eexists; simpljoin; auto.
  splits;eauto.
  simpljoin.
  simpljoin.
  splits;simpl;auto;try solve [unfolds;simpl;auto].
  splits;unfolds;simpl;auto.
Qed.

Lemma simpl_inv_excrit :
  forall P,
    Aisr empisr ** OSInv ** atoy_inv' ** P ==> Aisr empisr ** invlth_isr I 0%nat INUM ** P.
Proof.
  intros.
  apply simpl_inv_excrit'.
  sep cancel 1%nat 1%nat.
  apply atoy_inv_add;auto.
Qed.


Lemma encrit1_rule'_ISnil :
  forall (Spec : funspec) (I : Inv) (r : retasrt) 
         (ri : asrt)  (frm : asrt) isr cs
         (aop : absop) (p : asrt) sc li ct ,
    p ==> Aisr isr ** Aie true ** Ais nil ** Acs cs ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    {|Spec, sc, li, I, r, ri|}|-ct {{ <|| aop ||>  ** p}}
                           sprim encrit
                           {{ <|| aop ||>  **
                                  Aisr isr ** Aie false **
                                  Ais nil ** Acs (true::cs) ** invlth_isr I 0%nat INUM ** frm}}.
Proof.
  intros.
  eapply encrit1_rule'; eauto.
  intros.
  apply H in H2.
  sep auto.
  destruct_s s; trysimplall; subst; auto.
Qed.

Lemma excrit1_rule'_ISnil :
  forall (Spec : funspec) (I : Inv) (r : retasrt) 
         (ri : asrt) (isr : isr) 
         (cs : list bool) (frm : asrt) (aop : absop) 
         (p : asrt) sc li ct lg,
    p ==> Aisr isr ** Aie false ** Ais nil ** Acs (true::cs) ** invlth_isr I 0%nat INUM ** frm ->
    GoodI I sc li ->
    GoodFrm frm ->
    frm ==> p_local li ct lg ** Atrue ->
    {|Spec, sc, li, I, r, ri|}|-ct {{ <|| aop ||>  ** p}}
                           sprim excrit
                           {{ <|| aop ||>  ** Aisr isr ** Aie true ** Ais nil ** Acs cs ** frm}}.
Proof.
  intros.
  eapply excrit1_rule'; eauto.
  intros.
  apply H in H3.
  sep auto.
  gen H6; clear; intros.
  destruct_s s; trysimplall; subst; auto.
Qed.


Lemma disj_star_elim_disj:
  forall p q r, ( p \\// q )** r ==> (p ** r) \\// (q ** r).
Proof.
  intros.
  simpl in *;simpljoin.
  destruct H3;simpljoin.
  left.
  do 6 eexists;splits;eauto.
  right.
  do 6 eexists;splits;eauto.
Qed.

Lemma aemp_isr_elim:
  forall o O ab P,
    (o, O , ab) |= aemp_isr_is ** P -> (o, O, ab) |= P.
Proof.
  introv Hsat.
  simpl in Hsat.
  simpljoin.
  destruct o as [[[[]]]].
  simpl in *.
  destruct l.
  destruct p.
  assert (m=x0) by join auto.
  assert (O=x3) by join auto.
  subst.
  auto.
Qed.


Lemma atoy_abst_elim :
  forall o O ab P,
    (o,O,ab) |= atoy_inv ** P ->
    exists o', (o',O,ab) |= P.
Proof.
  introv Hsat.
  unfold atoy_inv in Hsat.
  simpl in Hsat.
  simpljoin.
  destruct o as [[[[]]]].
  simpl in *.
  simpljoin.
  destruct l.
  destruct p.
  eexists .
  assert (O = x3) by join auto.
  subst.
  eauto.
Qed.


Lemma encrit1_rule'_ISnil_ISRemp :
  forall (Spec : funspec) (r : retasrt) 
         (ri : asrt) (frm : asrt) cs
         (aop : absop) (p : asrt) ct,
    p ==> Aisr empisr ** Aie true ** Ais nil ** Acs cs ** frm ->
    GoodFrm frm ->
    {|Spec, GetHPrio, OSLInv, I, r, ri|}|-ct {{ <|| aop ||>  ** p}}
                           sprim encrit
                           {{ <|| aop ||>  **
                                  Aisr empisr ** Aie false **
                                  Ais nil ** Acs (true::cs) ** OSInv ** atoy_inv' ** frm}}.
Proof.
  intros.
  eapply forward_rule2.
  eapply encrit1_rule'_ISnil; eauto.
  apply GoodI_I.
  intros.
  sep lifts (2::6::7::nil)%nat.
  apply simpl_inv_encrit.
  sep auto.
Qed.

Lemma excrit1_rule'_ISnil_ISRemp :
  forall (Spec : funspec) (r : retasrt) 
         (ri : asrt)
         (cs : list bool) (frm : asrt) (aop : absop) 
         (p : asrt) ct lg,
    p ==> Aisr empisr ** Aie false ** Ais nil ** Acs (true::cs) ** OSInv ** atoy_inv' ** frm ->
    GoodFrm frm ->
    frm ==> p_local OSLInv ct lg ** Atrue ->
    {|Spec , GetHPrio, OSLInv, I, r, ri|}|-ct {{ <|| aop ||>  ** p}}
                           sprim excrit
                           {{ <|| aop ||>  ** Aisr empisr ** Aie true ** Ais nil ** Acs cs ** frm}}.
Proof.
  intros.
  eapply backward_rule2.
  eapply excrit1_rule'_ISnil; eauto.
  apply GoodI_I.
  intros.
  sep lifts (2::6::nil)%nat.
  sep cancel 1%nat 3%nat.
  apply H in H2.
  apply simpl_inv_excrit.
  sep auto.
Qed.


Lemma excrit1_rule'_ISnil_ISRemp':
  forall (Spec : funspec) (r : retasrt) (ri : asrt) 
         (cs : list bool) (frm : asrt) (aop : absop) 
         (p: asrt) ct lg,
    p ==>
      OSInv ** atoy_inv' **
      Aisr empisr **
      Aie false ** Ais nil ** Acs (true :: cs) **  frm ->
    frm ==> p_local OSLInv ct lg ** Atrue ->
    GoodFrm frm ->
    {|Spec, GetHPrio, OSLInv, I, r, ri|}|-ct {{ <|| aop ||>  ** p}}
                                     (sprim excrit)
                                     {{  <|| aop ||>  ** Aisr empisr ** Aie true ** Ais nil ** Acs cs ** frm }}.
Proof.
  intros.
  eapply forward_rule1.
  2: eapply excrit1_rule'_ISnil_ISRemp;eauto.
  eauto.
  intros.
  apply H in H2.
  sep semiauto.
Qed.

Lemma excrit1_rule'_ISnil_ISRemp'':
  forall (Spec : funspec) (r : retasrt) (ri : asrt) 
         (cs : list bool) (frm : asrt) (aop : absop) 
         (p: asrt) ct lg,
    p ==>
      OSInv ** atoy_inv' **
      Aisr empisr **
      Aie false ** Ais nil ** Acs (true :: cs) **  (p_local OSLInv ct lg ** frm) ->
    GoodFrm frm ->
    {|Spec, GetHPrio, OSLInv, I, r, ri|}|-ct {{ <|| aop ||>  ** p}}
                                         (sprim excrit)
                                         {{  <|| aop ||>  ** Aisr empisr ** Aie true ** Ais nil ** Acs cs ** (p_local OSLInv ct lg ** frm) }}.
Proof.
  intros.
  eapply forward_rule1.
  2: eapply excrit1_rule'_ISnil_ISRemp';eauto.
  sep auto.
  intros;sep auto.
  good_frm_sovler.
  simpl.
  eauto.
Qed.

Lemma excrit1_rule'_ISnil_ISRemp''':
  forall (Spec : funspec) (r : retasrt) (ri : asrt) 
         (cs : list bool) (frm : asrt) (aop : absop) 
         (p: asrt) ct,
    p ==>
      OldOSInvWL ct init_lg ** atoy_inv' **
      Aisr empisr **
      Aie false ** Ais nil ** Acs (true :: cs) ** frm ->
    GoodFrm frm ->
    {|Spec, GetHPrio, OSLInv, I, r, ri|}|-ct {{ <|| aop ||>  ** p}}
                                         (sprim excrit)
                                         {{  <|| aop ||>  ** Aisr empisr ** Aie true ** Ais nil ** Acs cs ** (p_local OSLInv ct init_lg ** frm) }}.
Proof.
  intros.
  eapply excrit1_rule'_ISnil_ISRemp'';eauto.
  intros.
  apply H in H1.
  sep lifts (1::7::nil).
  apply inv_change in H1.
  sep auto.
Qed.

(* auto unfold *)
Ltac unfold_dll := 
  try unfold tcbdllseg; 
  try unfold dllseg; 
  try fold dllseg;
  try unfold node.

Ltac unfold_sll :=  
  try unfold sll; 
  try unfold sllseg; 
  try fold sllseg;
  try unfold node.

Ltac unfold_qblkfsll :=
  try unfold qblkf_sll;
  try unfold qblkf_sllseg;
  try fold qblkf_sllseg;
  try unfold node.
  

Ltac unfold_msgslleg :=  
  try unfold evsllseg;  
  try fold evsllseg; 
  try unfold AEventNode; 
  try unfold node. 


Ltac unfold_ecbfsll :=  
  try unfold ecbf_sll;
  try unfold ecbf_sllseg;  
  try fold ecbf_sllseg; 
  try unfold node. 

Ltac unfold_gvar_array := 
  try unfold AOSTCBPrioTbl in *;
  try unfold AOSMapTbl in *;
  try unfold AOSUnMapTbl in *;
  try unfold AOSRdyTblGrp in *; 
  try unfold AOSRdyTbl in *;
  try unfold AOSRdyGrp in *;
  try unfold AOSTime in *; 
  try unfold AGVars in *;
  try unfold AOSIntNesting in *.

Ltac destr_event :=
  match goal with
    | H : _ |- context [match ?d with
                          | DMsgQ _ _ _ _ => _
                          | DSem _ => _
                        end] => destruct d
    |_ => fail
  end.

Ltac unfold_msg := 
  try unfold AEventNode;
  try destr_event;
  try unfold AMsgData;
  try unfold AOSEvent;
  try unfold AOSEventTbl;
  try unfold AOSQCtr;
  try unfold AOSQBlk;
  try unfold node. 



Ltac find_first_stmt' stmts :=
  match stmts with
    | sseq ?s _ => find_first_stmt' s
    | _ => constr:(stmts)
  end.

Ltac find_first_stmt :=
  match goal with
    | |- {|_ , _, _, _, _, _|}|- _ {{_}}?s {{_}} => find_first_stmt' s
  end. 

Ltac find_first_exprs :=
  match find_first_stmt with
    | sif ?e _ _ => constr:((e::nil)%list)
    | sifthen ?e _ => constr:((e::nil)%list)
    | swhile ?e _ => constr:((e::nil)%list)
    | sret _ ?e  => constr:((e::nil)%list)
    | scall _ ?el => constr: ((el)%list)
    | scall ?e ?el => constr:((e::el)%list)
    | sassign ?e1 ?e2 => constr:((e1::e2::nil)%list)
    | _ =>  constr:(@nil expr)%list
  end.


Ltac unfold_var x := 
   match x with
    | OSQFreeBlk =>  try unfold OSInv; try unfold AOSQFreeBlk;  unfold_qblkfsll 
    | OSQFreeList =>  try unfold OSInv; try unfold AOSQFreeList;  unfold_sll
    | OSEventFreeList => try unfold OSInv; try unfold AOSEventFreeList; unfold_ecbfsll
    | OSEventList => try unfold OSInv; try unfold AECBList; unfold_msgslleg
    | OSTCBCur => try unfold OSInv; try unfold AOSTCBList;unfold_dll
    | OSTCBList => try unfold OSInv; try unfold AOSTCBList
    | OSRdyTbl => try unfold OSInv; try unfold AOSRdyTblGrp; try unfold AOSRdyTbl
    | OSRdyGrp => try unfold OSInv; try unfold AOSRdyTblGrp; try unfold AOSRdyGrp
    | OSTCBPrioTbl => try unfold OSInv; try unfold AOSTCBPrioTbl
    | OSTime => try unfold OSInv; try unfold AOSTime
    | 999%Z =>  unfold_msg
    | OSIntNesting => try unfold OSInv; try unfold AOSIntNesting
    | OSRunning => try unfold OSInv; try unfold AGVars
    | _ => idtac
   end.


Ltac unfold_exprlist ls :=  
  match ls with 
    | ((eunop _ ?e) :: ?l)%list => unfold_exprlist ((e::l)%list)
    | ((ebinop _ ?e1 ?e2) :: ?l)%list =>  unfold_exprlist ((e1::e2::l)%list)
    | ((ederef ?e) :: ?l)%list =>  unfold_exprlist ((e::l)%list)
    | ((eaddrof ?e) :: ?l)%list =>  unfold_exprlist ((e::l)%list)
    | ((efield ?e ?id) :: ?l)%list =>  unfold_exprlist ((e::(evar 999%Z) :: l)%list)
    | ((ecast ?e _) :: ?l)%list =>  unfold_exprlist ((e::l)%list)
    | ((earrayelem ?e1 ?e2) :: ?l)%list => unfold_exprlist ((e1::e2::l)%list)
    | ((evar ?x) ::?l)%list => unfold_var x; unfold_exprlist l
    | (enull:: ?l)%list => unfold_exprlist l
    | ((econst32 _) :: ?l) => unfold_exprlist l
    | (@nil expr)%list => idtac
  end. 


Ltac unfold_field_fun :=
  try unfold V_OSQPtr in *;
  try unfold V_OSEventListPtr in *;
  try unfold V_OSTCBNext in *;
  try unfold V_OSTCBPrev in *;
  try unfold V_OSTCBEventPtr in *;
  try unfold V_OSTCBMsg in *;
  try unfold V_OSTCBDly in *;
  try unfold V_OSTCBStat in *;
  try unfold V_OSTCBPrio in *;
  try unfold V_OSTCBX in *;
  try unfold V_OSTCBY in *;
  try unfold V_OSTCBBitX in *;
  try unfold V_OSTCBBitY in *;
  try unfold V_OSEventType in *;
  try unfold V_OSEventGrp  in *;
  try unfold V_OSEventCnt in *;
  try unfold V_OSEventPtr  in *;
  try unfold V_OSQStart in *;
  try unfold V_OSQEnd in *;
  try unfold V_OSQIn in *;
  try unfold V_OSQOut in *; 
  try unfold V_OSQSize in *;
  try unfold V_OSQEntries in *;
  try unfold V_qfreeblk  in *;
  try unfold V_nextblk in *;
  try unfold V_next  in *;
  try unfold V_qeventptr in *.

(*
Ltac try_unfold_funspecs :=
  try (unfold OS_EventSearch_spec)(*;try (unfold OS_QPtrRemove_spec);try (unfold OS_EventTaskRdy_spec);try (unfold OS_EventTaskWait_spec);try (unfold OS_EventTO_spec)*).
*)

Ltac sep_unfold' := 
  match goal with
    | H : ?s |= ?p |- ?s |= ?q => 
      match p with
        | context [OSTCBCur] => 
          match q with
            | context [AOSTCBList] => 
              try unfold AOSTCBList;
                unfold_dll
            | _ => fail
          end
        | context [OSEventFreeList] => 
          match q with
            | context [AOSEventFreeList] => 
              try unfold AOSEventFreeList;  
                unfold_sll     
            | _ => fail
          end
        | context [OSQFreeList] => 
          match q with
            | context [AOSQFreeList] => 
              try unfold AOSQFreeList;
                unfold_sll    
            | _ => fail
          end
        | context [OSQFreeBlk] => 
          match q with
            | context [AOSQFreeBlk] =>
              try unfold AOSQFreeBlk;
                unfold_sll    
            | _ => fail
          end
        | _ => idtac
      end
  end.

Ltac sep_unfold := 
  intros;  
  try unfold OSInv;
  unfold_gvar_array;
  repeat progress sep_unfold'.

Tactic Notation "sep" "semiauto" :=
  first [ solve [ sep_unfold; sep_semiauto; sep_pure ]
        | sep_unfold; sep_semiauto ].

Tactic Notation "sep" "auto" :=
  first [ solve [ sep_unfold; sep_auto; sep_pure ]
        | sep_unfold; sep_auto ].






Ltac seg_isptr := 
  match goal with
    | H : _ |= evsllseg ?v Vnull _ _ ** ?A |- isptr ?v =>
      apply  evsllseg_head_isptr in H; auto
    | H : _ |= ecbf_sllseg ?v Vnull _ _ _ ** ?A |- isptr ?v =>
      apply  ecbfsllseg_head_isptr in H; auto
    | H : _ |= qblkf_sllseg ?v Vnull _ _ _ ** ?A |- isptr ?v =>
      apply  qblkfsllseg_head_isptr in H; auto
    | H : _ |= sllseg ?v Vnull _ _ _  ** ?A |- isptr ?v =>
      apply sllseg_head_isptr in H; auto
    | H : _ |= dllseg ?v  _  _ Vnull _  _  _  _ ** ?A |- isptr ?v =>
      apply   dllseg_head_isptr in H; auto
    | H : isptr ?v |- isptr ?v => exact H; clear H
    | H : _ |= ?A ** ?B  |- isptr _  =>  sep lower 1%nat in  H; seg_isptr
    | _ => fail 1
end.  


Ltac isptr_intro_evsllseg :=
  match goal with
    | H:_
      |- {|_ , _, _, _, _, _|}|-_ {{?p}}_ {{_}} =>
      match p with
        | context [evsllseg ?v Vnull _ _] =>
          first [ let x:= fresh in 
                  assert (isptr v) as x by auto; clear x  
                | hoare_assert_pure (isptr v); [ seg_isptr | idtac ]]
      end
    | _ => idtac
  end.
Ltac isptr_intro_qblkf :=
  match goal with
    | H:_
      |- {|_ , _, _, _, _, _|}|- _ {{?p}}_ {{_}} =>
      match p with
        | context [qblkf_sllseg ?v Vnull _ _ _ ] =>
          first [ let x:= fresh in 
                  assert (isptr v) as x by auto; clear x  
                | hoare_assert_pure (isptr v); [ seg_isptr | idtac ]]
      end
    | _ => idtac
  end.

Ltac isptr_intro_ecbf :=
  match goal with
    | H:_
      |- {|_ , _, _, _, _, _|}|- _ {{?p}}_ {{_}} =>
      match p with
          
        | context [ecbf_sllseg ?v Vnull _ _ _ ] =>
          first [ let x:= fresh in 
                  assert (isptr v) as x by auto; clear x  
                | hoare_assert_pure (isptr v); [ seg_isptr | idtac ]]
                
      end
    | _ => idtac
  end.


Ltac isptr_intro_sll :=
  match goal with
    | H:_
      |- {|_ , _, _, _, _, _ |}|- _ {{?p}}_ {{_}} =>
      match p with
          
        | context [sllseg ?v Vnull _ _ _] =>
          first [ let x:= fresh in 
                  assert (isptr v) as x by auto; clear x  
                | hoare_assert_pure (isptr v); [ seg_isptr | idtac ]]
                
      end
    | _ => idtac
  end.

Ltac isptr_intro_dll :=
  match goal with
    | H:_
      |- {|_ , _, _, _, _, _|}|- _ {{?p}}_ {{_}} =>
      match p with
        | context [dllseg ?v _ _ Vnull _ _ _ _] =>
          first [ let x:= fresh in 
                  assert (isptr v) as x by auto; clear x  
                | hoare_assert_pure (isptr v); [ seg_isptr | idtac ]]
      end
    | _ => idtac
  end.

Ltac isptr_intro' :=
  isptr_intro_evsllseg;
  isptr_intro_qblkf;
  isptr_intro_ecbf;
  isptr_intro_sll;
  isptr_intro_dll.

Ltac isptr_intro :=
match goal with
  | H:_
    |- {|_ , _, _, _, _, _|}|- _ {{?p}}_ {{_}} =>
        match p with
        | context [evsllseg ?v Vnull _ _] =>
                 first [ let x:= fresh in 
                          assert (isptr v) as x by auto; clear x  
                        | hoare_assert_pure (isptr v); [ seg_isptr | idtac ]]
        | context [qblkf_sllseg ?v Vnull _ _ _ ] =>
                 first [ let x:= fresh in 
                          assert (isptr v) as x by auto; clear x  
                       | hoare_assert_pure (isptr v); [ seg_isptr | idtac ]]
        | context [ecbf_sllseg ?v Vnull _ _ _ ] =>
                 first [ let x:= fresh in 
                          assert (isptr v) as x by auto; clear x  
                        | hoare_assert_pure (isptr v); [ seg_isptr | idtac ]]
        | context [sllseg ?v Vnull _ _ _] =>
                  first [ let x:= fresh in 
                          assert (isptr v) as x by auto; clear x  
                        | hoare_assert_pure (isptr v); [ seg_isptr | idtac ]]
             
        | context [dllseg ?v _ _ Vnull _ _ _ _] =>
          first [ let x:= fresh in 
                          assert (isptr v) as x by auto; clear x  
                        | hoare_assert_pure (isptr v); [ seg_isptr | idtac ]]
        end
  | _ => idtac
end.

Ltac simpl_field_eq :=
  unfold_field_fun; simpl nth_val in *; 
  repeat match goal with
           | H  : Some _ = Some _ |- _ =>  inverts H
           | H : Vptr _ = Vptr _ |- _ => inverts H
           | H : Vint32 _ = Vint32 _ |- _ => inverts H
           | _ => idtac
         end.

Ltac pure_intro := hoare_split_pure_all; 
                   isptr_intro; 
                   array_leneq_intro;
                   hoare_split_pure_all; 
                   simpljoin;
                   struct_type_vallist_match_elim ; 
                   simpl_field_eq.

Ltac pure_intro2 := hoare_split_pure_all; 
                   isptr_intro'; 
                   array_leneq_intro;
                   hoare_split_pure_all; 
                   simpljoin;
                   struct_type_vallist_match_elim ; 
                   simpl_field_eq.



Ltac hoare_unfold' := 
   try unfold OSInv; try unfold_funpost;
   match goal with
   | H: _ |- {|_ , _, _, _, _, _|}|-_ {{_}} _ {{_}} =>
     hoare_split_pure_all;
       let x := find_first_exprs in
       unfold_exprlist x; pure_intro2
   | _ => idtac        
   end.


Ltac hoare_unfold := 
   try unfold OSInv; try unfold_funpost;
   match goal with
   | H: _ |- {|_ , _, _, _, _, _|}|- _ {{_}} _ {{_}} =>
     hoare_split_pure_all;
       let x := find_first_exprs in
       unfold_exprlist x; pure_intro
   | _ => idtac        
   end.


Tactic Notation "pure" "intro" := pure_intro.


Tactic Notation "hoare" "unfold" :=
  hoare_unfold.

Tactic Notation  "hoare" "unfold" "pre" :=
  hoare_unfold'.






(* hoare forward prim*)

Ltac find_OSInv' P :=
  match P with
    | ?A ** ?B => 
      match find_OSInv' A with
        | some ?m => constr:(some m)
        | none ?m => 
          match find_OSInv' B with
            | some ?n => constr:(some (m + n)%nat)
            | none ?n => constr:(none (m + n)%nat)
          end
      end
    | OSInv => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_OSInv P :=
  let y := find_OSInv' P in
  eval compute in y.

Ltac trycancel := try 
                    (sep cancel Aisr;sep cancel Aie;
                     sep cancel Ais;
                     sep cancel Acs);
                  try sep cancel AOSEventFreeList;
                  try sep cancel AOSQFreeList;
                  try sep cancel AOSQFreeBlk;
                  try sep cancel  AOSTCBFreeList;
                 (* try sep cancel AOSEventPtrFreeList;*)
                  try sep cancel AECBList;
                  try sep cancel AOSMapTbl;
                  try sep cancel AOSUnMapTbl;
                  try sep cancel AOSTCBPrioTbl;
                  try sep cancel AOSIntNesting;
                  try sep cancel AOSTCBList;
                  try sep cancel AOSRdyTblGrp;
                  try sep cancel AOSTime;
                  try sep cancel AGVars;
                  try sep cancel AOSRdyTbl;
                  try sep cancel AOSRdyGrp.



Ltac hoare_enter_critical :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {|_ , _, ?li , _, _, _|}|-_ {{?P}} (sprim encrit) {{_}} =>
      match find_aop P with 
        | none _ => idtac 1 "no absop in the pre condition"; fail 1
        | some ?a =>
          match find_aisr P with
            | none _ => idtac 2 "no isr in the pre condition"; fail 2
            | some ?b =>
              match find_aie P with
                | none _ => idtac 3 "no ie in the pre condition"; fail 3
                | some ?c =>
                  match find_ais P with
                    | none _ => idtac 4 "no is in the pre condition"; fail 4
                    | some ?d =>
                      match find_acs P with
                        | none _ => idtac 5 "no cs in the pre condition"; fail 5
                        | some ?e =>
                          hoare lifts (a::b::c::d::e::nil) pre;
                            eapply encrit1_rule'_ISnil_ISRemp;
                            [ intros s H; exact H
                            | good_frm_sovler;simpl;auto
                            ]
                      end
                  end
              end
          end
      end
  end.



Ltac hoare_exit_critical :=
  match goal with
    | |- {|_ , _, ?li , _, _, _|}|- _ {{?P}} (sprim excrit) {{_}} =>
      match find_aop P with
        | some ?n => 
          hoare lifts (n::nil) pre;
            eapply excrit1_rule'_ISnil_ISRemp'''; 
            [ intros; try (unfold OldOSInvWL); sep pauto;trycancel
            | idtac
            ]                
        | _ => fail 1
      end   
  end.

Ltac find_osinv' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_osinv' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_osinv' B with
            | some ?b => constr:(some (a + b))
            | none ?b => constr:(none (a + b))
          end
      end
    |  OSInv  => constr:(some 1)
    | _ => constr:(none 1)
  end.

Ltac find_osinv Hp := let x := find_osinv' Hp in
                      eval compute in x.

Ltac find_local' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_local' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_local' B with
            | some ?b => constr:(some (a + b))
            | none ?b => constr:(none (a + b))
          end
      end
    |  p_local _ _ _  => constr:(some 1)
    | _ => constr:(none 1)
  end.

Ltac find_local Hp := let x := find_local' Hp in
                      eval compute in x.


Ltac hoare_invchange:=
  match goal with
    | |- {|_, _, _, _, _, _|}|- _ {{?P}} _ {{_}} =>
      match find_osinv P with
        | none _ =>  fail 1
        | some ?a =>
          match find_local P with
            | none _ =>  fail 2
            | some ?b =>
              hoare lifts (a :: b :: nil) pre;
                eapply backward_rule1;[eapply inv_change | unfold OldOSInvWL]
          end
      end
  end.

Ltac hoare_forward_prim_first :=
  first [ hoare_enter_critical
        | hoare_exit_critical
        | idtac ].


Ltac hoare_forward_prim' :=
  let s := fresh in
  let H := fresh in
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} (sseq _ _) {{ _ }} =>
    eapply seq_rule; [ hoare_forward_prim'
                     | try hoare_invchange ]
  | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
    eapply forward_rule2; [ hoare_forward_prim_first
                          | first [ intros s H; exact H
                                  | sep pauto ] ]
  end.



Ltac hoare_forward_prim :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalse_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse }} _ {{ _ }} =>
      apply hoare_disj_afalse_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse ** ?P \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalseP_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse **?P }} _ {{ _ }} =>
      apply hoare_disj_afalseP_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// _ }} _ {{ _ }} =>
      eapply disj_rule
    | _ => hoare normal pre; hoare_ex_intro;  hoare_forward_prim'
  end.


Ltac hoare_forward_prim'_nsepauto :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} (sseq _ _) {{ _ }} =>
      eapply seq_rule; [ hoare_forward_stmts'_nsepauto
                       | idtac ]
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
      eapply forward_rule2; [ hoare_forward_prim_first
                            | ]
  end.



Ltac hoare_forward_prim_nsepauto :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalse_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse }} _ {{ _ }} =>
      apply hoare_disj_afalse_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse ** ?P \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalseP_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse **?P }} _ {{ _ }} =>
      apply hoare_disj_afalseP_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// _ }} _ {{ _ }} =>
      eapply disj_rule
    | _ => hoare normal pre; hoare_ex_intro;  hoare_forward_prim'_nsepauto
  end.


Tactic Notation "hoare" "forward" "prim":= hoare_forward_prim.

Close Scope nat_scope.
