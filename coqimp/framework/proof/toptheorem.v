

(** This file contains most of the side conditions and definitions used in the top tule and its semantics.     **)
(** "verified_os'" is the most important lemma for the top rule soundness.                                     **)


Require Import include_frm.
Require Import auxdef.
Require Import oscorrectness.
Require Import simulation.
Require Import base_tac.
Require Import seplog_tactics.
Require Import lemmasfortoptheo.
(*
Require Import tst_prop.
Require Import soundness.
 *)
Import  DeprecatedTactic.

Definition TaskOK :=
  fun (T : tasks) (p : progunit) (O : osabst) =>
    eqdomto T O /\
    (forall (t : tidspec.A) (C : CodeSpec.B),
       TasksMod.get T t = Some C ->
       exists s f d1 d2 t0, C = nilcont s /\ p f = Some (t0, d1, d2, s)).

Definition good_call := 
fun (pc po pi : progunit) (ip : intunit) =>
no_call_api_pu po po /\ no_call_api_pu pi po /\ no_call_api_ipu ip po /\ no_call_api_pu pc pi. 

Definition good_os_pu (pu:progunit) :=
  (forall f t d1 d2 s, pu f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true /\ GoodStmt' s).

Fixpoint Good_Clt_Stmt (s : stmts)  {struct s} : Prop :=
  match s with
    | sskip _ => True
    | sassign _ _ => True
    | sif _ s1 s2 => Good_Clt_Stmt s1 /\ Good_Clt_Stmt s2
    | sifthen _ s0 => Good_Clt_Stmt s0
    | swhile _ s' => Good_Clt_Stmt s'
    | sret => True
    | srete _ => True
    | scall f _ => True
    | scalle _ f _ => True
    | sseq s1 s2 => Good_Clt_Stmt s1 /\ Good_Clt_Stmt s2
    | sprint _ => True
    | sfexec _ _ _ => False
    | sfree _ _ => False
    | salloc _ _ => False
    | sprim _ => False
    | hapi_code _ => False
  end.

Definition good_cli_pu (pu:progunit):=
  (forall f t d1 d2 s, pu f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true /\ Good_Clt_Stmt s).

Definition ProgOK Pl :=
  exists pc po pi ip,
    Pl = (pc,(po,pi,ip)) /\
    no_fun_same pc po /\ no_fun_same pc pi /\ no_fun_same po pi /\
    good_call pc po pi ip /\
    good_os_pu po /\ good_os_pu pi /\ good_cli_pu pc.

Definition GOOD_OS := 
fun (Os : oscode) (A : osspec) (init : InitAsrt) =>
  forall (t : tid) (pc : progunit)
         (Wl : progunit * oscode * tasks * clientst * osstate * tid)
         (Wh : progunit * osspec * tasks * clientst * OSAbstMod.map) 
         (T : tasks) (S : osstate) (cst : clientst) (O : OSAbstMod.map),
    OSAbstMod.get O curtid = Some (oscurt t) ->
    TaskOK T pc O ->
    ProgOK (pc,Os) ->
    init S O ->
    Wl = (pc, Os, T, cst, S, t) ->
    Wh = (pc, A, T, cst, O) ->
    TasksMod.indom T t ->
    etrace_subset Wl Wh.

Definition WFIFun := 
  fun (P : progunit) (FSpec : funspec) (sd : ossched) (I : Inv) (pa:LocalInv) =>
    EqDom P FSpec /\
    (forall (f : fid) (pre : fpre) (post : fpost) (t : type) (tl : typelist),
       FSpec f = Some (pre, post, (t, tl)) ->
       exists d1 d2 s,
         P f = Some (t, d1, d2, s) /\
         tlmatch tl d1 /\
         (forall (vl : vallist) (p : asrt) (r : retasrt) (logicl : list logicvar) tid,
            Some p = BuildPreI P f vl logicl pre tid ->
            Some r = BuildRetI P f vl logicl post tid ->
            {|FSpec, sd, pa, I, r, Afalse|}|-tid {{p}}s {{Afalse}})).


Definition WFAPI :=
  fun (P:progunit) (apispec:osapispec) pa (Spec:funspec) (sd : ossched) (I : Inv) lg =>
    EqDomAPI P apispec /\
    (
      forall (f:fid) ab vl p r ft tid, 
        apispec f = Some (ab,ft) ->
        Some p = BuildPreA' P f (ab,ft) vl pa tid lg->
        Some r = BuildRetA' P f (ab,ft) vl pa tid lg->
        (
          exists  t d1 d2 s,
            P f = Some (t, d1, d2, s) /\
            InfRules Spec sd pa I r Afalse p s Afalse tid
        )
    ).

Definition WFInt :=
  fun (P:intunit) (intspec:osintspec) pa (Spec:funspec) (sd : ossched) (I : Inv) =>
    EqDomInt P intspec /\
    (
      forall i isrreg si p r lg t,
        Some p = BuildintPre i intspec isrreg si I pa t lg->
        Some r = BuildintRet i intspec isrreg si I pa t lg->
        exists s,
          P i = Some s /\
          {|Spec , sd, pa, I, retfalse, r|}|-t {{p}}s {{Afalse}}
                                                    
    ).

(*
Definition side_condition' I schedmethod init:=
  (
    GoodI I schedmethod /\
    (forall tid S O,  init S O ->
                      (forall o, (projS S tid) = Some o ->
                                 exists o', 
                                   o' = substaskstm o empmem /\
                                   (InitTaskSt (pair o' OSAbstMod.emp)) /\
                                   (forall ab,sat ((pair o O),ab) (INV I)) ) /\ eqdomSO S O)
  ).
*)

Theorem verified_os':
  forall osc A (init:InitAsrt) li (I:Inv) (Spec:funspec) pa pi ip apispec intspec schedmethod,
    osc = (pa,pi,ip) ->
    A = (apispec,intspec,schedmethod) ->
    
    WFAPI pa apispec li Spec schedmethod I init_lg ->
    WFInt ip intspec li Spec schedmethod I ->
    WFIFun pi Spec schedmethod I li ->
    side_condition I li schedmethod init init_lg ->
    
    GOOD_OS osc A init.
Proof.
  introv Hosc HA.
  subst.
  intros.
  (*
  assert (side_condition' I schedmethod init).
  clear -H2.
  unfolds.
  unfolds in H2.
  mytac;auto.
  intros.
  apply H0 with (tid:=tid) in H1.
  mytac;auto.
  clear H2.
  intro x.
  destruct x as [[[[]]]].
  intros.
  eapply H1 with (ab:=absopx) in H2.
  exists (e, b, empmem, i, b0).
  splits;auto.
  unfolds.
  simpl.
  unfold init_asrt in H2.
  unfold sat in H2;fold sat in H2.
  mytac;auto.
  simpl in H14.
  apply asrtLib.eqdomenv_nil_enil;auto.
  simpl in H19;subst.
  destruct b0.
  destruct p.
  simpl in H22,H28,H27;subst.
  auto.
  intros.
  unfold init_asrt in H2.
  assert ( (e, b, m, i, b0, O, absopx) |= INV I).
  sep auto.
  clear H2.
  eapply asrtLib.INV_irrev_prop in H3;eauto.
  clear H2.
  rename H3 into H2.
   *)
  unfolds.
  intros.
  rename H9 into Hsc.
  assert (OSCorrect (pa,pi,ip) (apispec, intspec, schedmethod) init).
  unfolds in H5;mytac.
  
  eapply toptheorem;eauto.
  simpl.
  unfolds.
  unfolds in H12.
  mytac;auto.
  simpl.
  unfolds in H2.
  mytac;eauto.
  unfolds in H0.
  mytac;auto.
  intros.
  eapply e0 in H5.
  mytac;eexists;mytac;eauto.
  simpl in H0;auto.
  
  unfolds in H.
  simpl.
  destruct H;auto.
  unfolds.
  unfolds in H1.
  mytac;auto.
  intros.
  apply H5 in H7.
  mytac.
  do 3 eexists;splits;eauto.
  unfolds in H14.
  apply H14 in H7.
  mytac;auto.
  unfolds in H2.
  split.
  simpl.
  unfolds in H.
  unfolds in  H0.
  destruct H0;destruct H;auto.
  unfolds in H0.
  unfolds in H.
  destruct H.
  splits;auto.
  split.
  mytac;auto.
  destruct H2;auto.
  (*
  lets Hx:H7 tid H5.
  destruct Hx;auto.
  destruct H2.
  lets Hx:H7 tid H5.
  destruct Hx;auto.
   *)
  unfolds in H9.
  eapply H9;eauto.
  
  unfolds.
  unfolds.
  mytac;auto.
  intros.
  unfolds in H5.
  mytac.
  simpl.
  clear -H12 H15 H7.
  unfolds in H12.
  mytac.
  unfolds in H2.
  lets Hx: H2 H7.
  unfolds in H15.
  lets Hy: H15 H7.
  mytac.
  clear -Hx H4.
  gen Hx H4.
  induction s;intros;simpl;auto.
  simpl in H4,Hx.
  mytac.
  apply IHs1;auto.
  apply IHs2;auto.
  simpl in Hx,H4.
  mytac.
  apply IHs1;auto.
  apply IHs2;auto.
  unfolds in H5.
  clear -H5.
  mytac.
  unfolds in H0;destruct H0.
  simpl;auto.
  unfolds in H5.
  clear -H5.
  mytac.
  unfolds in H0;destruct H0.
  simpl;auto.
Qed.



Theorem Soundness:
  forall  osc A (init:InitAsrt),
    TopRule osc A init ->
    GOOD_OS osc A init.
Proof.
  intros.
  inverts H.
  inverts H2.
  inverts H3.
  inverts H4.
  eapply verified_os';eauto.
  unfolds;split;eauto.
  unfolds;split;eauto.
  unfolds;split;eauto.
Qed.
