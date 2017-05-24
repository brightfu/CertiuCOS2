Require Export ucos_include.
Require Export os_ucos_h.

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

Ltac lzh_inverts_logic :=
  match goal with
    | H : context [logic_code _ ] |- _ =>
        inverts H
    | H : context [logic_val _] |- _ =>
        inverts H
    | H : context [logic_lv _] |- _ =>
        inverts H
    | H : context [logic_llv _] |- _ =>
        inverts H
  end.

Ltac lzh_destruct_event :=
  match goal with
    | |- context [match ?d with
                    | DMsgQ _ _ _ _ => _
                    | DSem _ => _
                    | DMbox _ => _
                    | DMutex _ _ => _
                  end] => destruct d
    | _ => fail
  end.


Ltac lzh_unfold_event := 
  try unfold AEventNode;
    try unfold AEventData; 
      try lzh_destruct_event;
      try unfold AMsgData; 
      try unfold AOSQCtr; try unfold AOSQBlk;
    try unfold AOSEvent;
      try unfold AOSEventTbl;
  try unfold node. 


Ltac lzh_unfold_var x := 
   match x with
    | OSQFreeBlk =>  try unfold OSInv; try unfold AOSQFreeBlk;  unfold_qblkfsll 
    | OSQFreeList =>  try unfold OSInv; try unfold AOSQFreeList;  unfold_sll
  (*  | OSEventPtrFreeList => try unfold OSInv; try unfold AOSEventPtrFreeList;  unfold_sll
*)   
    | OSEventFreeList => try unfold OSInv; try unfold AOSEventFreeList; unfold_ecbfsll
    | OSEventList => try unfold OSInv; try unfold AECBList; unfold_msgslleg
    | OSTCBCur => try unfold OSInv; try unfold AOSTCBList;unfold_dll
    | OSTCBList => try unfold OSInv; try unfold AOSTCBList
    | OSRdyTbl => try unfold OSInv; try unfold AOSRdyTblGrp; try unfold AOSRdyTbl
    | OSRdyGrp => try unfold OSInv; try unfold AOSRdyTblGrp; try unfold AOSRdyGrp
    | OSTCBPrioTbl => try unfold OSInv; try unfold AOSTCBPrioTbl
    | OSTime => try unfold OSInv; try unfold AOSTime
    | 999%Z =>  lzh_unfold_event
    | OSIntNesting => try unfold OSInv; try unfold AOSIntNesting
    | OSRunning => try unfold OSInv; try unfold AGVars
    | _ => idtac
   end.


Ltac lzh_unfold_exprlist ls :=  
  match ls with 
    | ((eunop _ ?e) :: ?l)%list => unfold_exprlist ((e::l)%list)
    | ((ebinop _ ?e1 ?e2) :: ?l)%list =>  unfold_exprlist ((e1::e2::l)%list)
    | ((ederef ?e) :: ?l)%list =>  unfold_exprlist ((e::l)%list)
    | ((eaddrof ?e) :: ?l)%list =>  unfold_exprlist ((e::l)%list)
    | ((efield ?e ?id) :: ?l)%list =>  unfold_exprlist ((e::(evar 999%Z) :: l)%list)
    | ((ecast ?e _) :: ?l)%list =>  unfold_exprlist ((e::l)%list)
    | ((earrayelem ?e1 ?e2) :: ?l)%list => unfold_exprlist ((e1::e2::l)%list)
    | ((evar ?x) ::?l)%list => lzh_unfold_var x; unfold_exprlist l
    | (enull:: ?l)%list => unfold_exprlist l
    | ((econst32 _) :: ?l) => unfold_exprlist l
    | (@nil expr)%list => idtac
  end. 

Ltac lzh_hoare_unfold :=
  try unfold OSInv; try unfold_funpost;
  match goal with
    | |- {| _, _, _, _, _, _ |} |- ?ct {{ _ }} _ {{ _ }} =>
      hoare_split_pure_all;
        let x := find_first_exprs in
          lzh_unfold_exprlist x; pure_intro
    | _ => idtac
  end.


Ltac lzh_val_inj_solver :=
  intros be H;
  destruct be;
  match goal with
    | |- ?X = ?X => reflexivity
    | |- ?X = ?Y => 
        simpl in H;
        (* ** ac: idtac "X"; *)
        try (unfold Int.notbool in H);
        first [rewrite Int.eq_true in H |
               rewrite Int.eq_false in H | idtac];
        destruct H; tryfalse; auto
  end.


Lemma val_inj_true:
  forall (be : bool),
    val_inj
      (if be
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)) <> Vint32 Int.zero /\
    val_inj
      (if be
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)) <> Vnull /\
    val_inj
      (if be
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)) <> Vundef ->
    be = true.
  lzh_val_inj_solver.
Qed.

Lemma val_inj_false:
  forall (be : bool),
     val_inj
       (if be
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
     val_inj
       (if be
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) = Vnull ->
     be = false.
  lzh_val_inj_solver.
Qed.

Lemma val_inj_not_true:
  forall (be : bool),
    val_inj
      (notint
         (val_inj
            (if be
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) <> Vint32 Int.zero /\
       val_inj
         (notint
            (val_inj
               (if be
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) <> Vnull /\
       val_inj
         (notint
            (val_inj
               (if be
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) <> Vundef ->
    be = false.
  lzh_val_inj_solver.
Qed.

Lemma val_inj_not_false:
  forall (be : bool),
     val_inj
       (notint
          (val_inj
             (if be
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
     val_inj
       (notint
          (val_inj
             (if be
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)))) = Vnull ->
     be = true.
  lzh_val_inj_solver.
Qed.

(* ** ac: Locate val_inj_impl_Vptr. *)

(* val_inj_impl_eq is exists *)

Lemma val_inj_impl_neq:
  forall x y,
    val_inj (val_eq x y) = Vint32 Int.zero \/
    val_inj (val_eq x y) = Vnull ->
    x <> y.
  (* 对x y做destruct，需要编写通用的tactic来解决这类问题 *)
  intros.
  assert (x = y \/ x <> y) by tauto.
  destruct H0.
  subst.
  unfold val_eq in H.
  destruct y.
  unfold val_inj in H.
  destruct H; tryfalse.
  unfold val_inj in H; destruct H; tryfalse.
  rewrite Int.eq_true in H.
  unfold val_inj in H; destruct H; tryfalse.
  destruct a.
  destruct (peq b b).
  rewrite Int.eq_true in H; unfold val_inj in H; destruct H; tryfalse.
  tryfalse.
  auto.
Qed.


Ltac lzh_val_inj_simpl :=
  match goal with
    | H : val_inj ?e <> Vint32 Int.zero /\
          val_inj ?e <> Vnull /\
          val_inj ?e <> Vundef |- _ =>
      match e with
        | notint _ => apply val_inj_not_true in H
        | val_eq ?x Vnull => apply val_inj_impl_Vnull in H
        | val_eq ?x ?y => apply val_inj_impl_eq in H
        | _ => try apply val_inj_true in H
      end
   
    | H : val_inj ?e = Vint32 Int.zero \/
          val_inj ?e = Vnull |- _ =>
      match e with
        | notint _ => apply val_inj_not_false in H
        | val_eq ?x Vnull => 
          apply val_inj_impl_Vptr in H; destruct H; subst x
        | val_eq ?x ?y =>
          apply val_inj_impl_neq
        | _ => try apply val_inj_false in H
      end

    | _ => idtac
  end.

Ltac lzh_find_srete_stmt stmts :=
  match stmts with
    | sseq ?s ?rs =>
      match s with
        | srete ?e => constr:(some 1%nat)
        | _ => lzh_find_srete_stmt rs
      end
    | srete ?e => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Lemma aconj_swap:
  forall s P Q,
    s |= P //\\ Q ->
    s |= Q //\\ P.
Proof.
  intros.
  apply aconj_elim in H.
  heat.
  apply aconj_intro.
  auto.
  auto.
Qed.
  
Lemma aconj_swap_l:
  forall P Q R,
    P //\\ Q ==> R ->
    Q //\\ P ==> R.
Proof.
  intros.
  apply aconj_swap in H0.
  apply H.
  auto.
Qed.

Lemma aconj_swap_r:
  forall P Q R,
    P ==> Q //\\ R ->
    P ==> R //\\ Q.
Proof.
  intros.
  apply aconj_swap.
  apply H.
  auto.
Qed.

(* ** ac: Locate "|-". *)
(* ** ac: Locate "|-". *)
Lemma infrules_swap_l:
  forall spec sc pa I r ri P Q R s ct,
    {| spec, sc, pa, I, r, ri |} |- ct {{P //\\ Q}} s {{ R }} ->
    {| spec, sc, pa, I, r, ri |} |- ct {{Q //\\ P}} s {{ R }}.                           
Proof.
  intros.
  eapply backward_rule1.
  intros.
  eapply aconj_swap.
  eauto.
  auto.
Qed.

Lemma infrules_swap_r:
  forall spec sc pa I r ri P Q R s ct,
    {| spec, sc, pa, I, r, ri |} |- ct {{P}} s {{ Q //\\ R }} ->
    {| spec, sc, pa, I, r, ri |} |- ct {{P}} s {{ R //\\ Q }}.                           
Proof.
  intros.
  eapply forward_rule2.
  eauto.
  intros.
  eapply aconj_swap.
  eauto.
Qed.
  
Lemma ift_rule_general' :
  forall (Spec : funspec) pa ct (I : Inv) (r : retasrt) 
         (ri : asrt)  (p q1 q2 : asrt) (e : expr) 
         (tp : type) (s : stmts) sc,
    p ==> EX v : val, Rv e @ tp == v ->
    Aisfalse e //\\ p ==> q2 ->
    {|Spec, sc, pa, I, r, ri|}|- ct {{Aistrue e //\\ p}}s {{q1}} ->
    {|Spec, sc, pa, I, r, ri|}|- ct {{p}}sifthen e s {{q1 \\// q2}}.
Proof.
  intros.
  eapply ift_rule; intros; eauto.
  apply aconj_swap in H2.
  apply H0 in H2; right; auto.
  eapply infrules_swap_l.
  eapply forward_rule2; eauto.
  intros; left; eauto.
Qed.

Lemma sep_aconj_r_aistrue_to_astar' :
  forall P e t v,
    P ==> Rv e @ t == v ->
    Aistrue e //\\ P ==> [| v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef |] ** P.
Proof.
  intros.
  eapply astar_comm.
  apply aconj_swap in H0.
  eapply sep_aconj_r_aistrue_to_astar; eauto.
Qed.

Lemma sep_aconj_r_aisfalse_to_astar' :
  forall P e t v,
    P ==> Rv e @ t == v ->
    Aisfalse e //\\ P ==> [| v = Vint32 Int.zero \/ v = Vnull |] ** P.
Proof.
  intros.
  eapply astar_comm.
  apply aconj_swap in H0.
  eapply sep_aconj_r_aisfalse_to_astar; eauto.
Qed.
  
Theorem lzh_if_rule' :
  forall Spec pa ct I r ri p q1 q2 e tp s1 s2 sc,
    {| Spec, sc, pa, I, r, ri |}|- ct {{ Aistrue e //\\ p }} s1 {{ q1 }} ->
    {| Spec, sc, pa, I, r, ri |}|- ct {{ Aisfalse e //\\ p }} s2 {{ q2 }} ->
    p ==> EX v : val, Rv e @ tp == v ->
    {| Spec, sc, pa, I, r, ri |}|- ct {{ p }} sif e s1 s2 {{ q1 \\// q2 }}.
Proof.
  intros.
  eapply infrules_swap_l in H.
  eapply infrules_swap_l in H0.
  eapply if_rule; eauto.
  eapply forward_rule1.
  2 : eauto.
  intros; left; eauto.
  eapply forward_rule1.
  2 : eauto.
  intros; right; eauto.
Qed.

Lemma lzh_if_else_rule
     : forall (Spec : funspec) pa ct (I : Inv) (r : retasrt) 
         (ri p q1 q2 : asrt) (e : expr) (tp : type) 
         (s1 s2 : stmts) (v : val) sd,
         p ==> Rv e @ tp == v ->
         {| Spec, sd, pa, I, r, ri |} |- ct {{ [|v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef|] ** p }}
                                  s1 {{ q1 }} ->
         {|Spec , sd, pa, I, r, ri|} |- ct {{ [|v = Vint32 Int.zero \/ v = Vnull|] ** p }}
                                s2 {{ q2 }} ->
         {|Spec , sd, pa, I, r, ri|} |- ct {{ p }} (sif e s1 s2)   
         {{ [|v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef|] ** q1 \\//
            [|v = Vint32 Int.zero \/ v = Vnull|] ** q2 }}.
(* 这个lemme是对if_rule2'的微调,改动是把pure assertion放到了p的最前面,
   这样pure_intro的时候会更快，而且可以控制名字
 *)
  intros.
  eapply lzh_if_rule'.
  3: intros;eexists;apply H;auto.
  eapply backward_rule1.
  eapply sep_aconj_r_aistrue_to_astar';eauto.
  apply pure_split_rule';intro.
  apply forward_rule1 with q1.
  sep auto.
  apply backward_rule1 with ([|v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef|] ** p).
  sep auto.
  auto.
  eapply backward_rule1.
  eapply sep_aconj_r_aisfalse_to_astar';eauto.
  apply pure_split_rule';intro.
  apply forward_rule1 with q2.
  sep auto.
  apply backward_rule1 with ([|v = Vint32 Int.zero \/ v = Vnull|] ** p).
  sep auto.
  auto.
Qed.

Lemma lzh_if_then_rule :
  forall (Spec : funspec) pa ct (I : Inv) (r : retasrt) 
         (ri : asrt)  (p q : asrt) (e : expr) 
         (tp : type) (s : stmts) (v:val) sd,
    p ==> Rv e @ tp == v ->
    {|Spec, sd, pa, I, r, ri|}|- ct {{ [|v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef|] ** p }}s {{ q }} ->
    {|Spec, sd, pa, I, r, ri|}|- ct {{ p }}sifthen e s {{ ([|v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef|] ** q)\\// ([|v = Vint32 Int.zero \/ v = Vnull|] ** p) }}.
Proof.
  intros.
  eapply ift_rule_general'; intros; eauto.
  apply H in H1; eexists; eauto.
  eapply sep_aconj_r_aisfalse_to_astar'; eauto.
  eapply backward_rule2.
  2 : eapply sep_aconj_r_aistrue_to_astar'; eauto.
  apply pure_split_rule';intro.
  apply forward_rule1 with q.
  sep auto.
  apply backward_rule1 with ([|v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef|] ** p).
  sep auto.
  auto.
Qed.

Ltac lzh_split_first name :=
  (* precondition: fist assertion in pre must be PURE!!!!*)
  apply pure_split_rule'; intro name.


Ltac lzh_hoare_if'' :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- ?ct {{ _ }} (sif _ _ _) {{ _ }} =>
      eapply lzh_if_else_rule;
        [ symbolic execution
         | (* idtac "if true block proof"; *)
           let H := fresh "LHif_true" in
             lzh_split_first H
         | (* idtac "if false block proof"; *)
           let H := fresh "LHif_false" in
             lzh_split_first H]
    | |- {| _, _ , _, _, _, _ |} |- ?ct {{ _ }} (sifthen _ ?stmts) {{ _ }} =>
      eapply lzh_if_then_rule;
        [ symbolic execution
        | (* idtac "if true block proof"; *)
          let x := lzh_find_srete_stmt stmts in
            match x with
              | some _ => instantiate (1:=Afalse)
              | none _ => idtac
            end;
          let H := fresh "LHift_true" in
            lzh_split_first H]
  end.
            
Ltac lzh_hoare_reject_afalse :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- ?ct {{ Afalse }} _ {{ _ }} =>
      apply pfalse_rule
    | _ => idtac
  end.
            
Ltac lzh_hoare_if' :=
  eapply seq_rule;
    [ lzh_hoare_if''
    | eapply disj_rule;
      [ (* idtac "if true"; *)
        let H := fresh "Hif_true" in
          lzh_split_first H;
        lzh_hoare_reject_afalse
      | (* idtac "if false"; *)
        let H := fresh "Hif_false" in
          lzh_split_first H;
        lzh_hoare_reject_afalse]].
          
Ltac lzh_hoare_if :=
  (* auto some usual sub goals appear from symbolic execution *)
  match goal with
    | |- {| _, _, _, _, _, _ |} |- ?ct {{ _ }} sseq _ _ {{ _ }} =>
      lzh_hoare_if'
    | |- {| _, _, _, _, _, _ |} |- ?ct {{ _ }} _ {{ _ }} =>
      eapply forward_rule2; [ lzh_hoare_if''
                            | idtac ]
  end;
  try lzh_val_inj_simpl;
  go.
  (* match goal with
    | |- struct_type_vallist_match _ _ =>
      go
    | _ => idtac
  end.*)

(* used to simplify hypothesis only *)
(*
Ltac mytac_H :=
  match goal with
  | H:exists _, _ |- _ => destruct H; mytac_H
  | H:_ /\ _ |- _ => destruct H; mytac_H
  | H:emposabst _ |- _ => unfold emposabst in H; subst; mytac_H
  | H:MemMod.join empmem _ _
    |- _ => apply MemMod.join_emp_eq in H; subst; mytac_H
  | H:MemMod.join _ empmem _
    |- _ =>
        apply MemMod.join_comm in H; apply MemMod.join_emp_eq in H; subst;
         mytac_H
  | H:EnvMod.join empenv _ _
    |- _ => apply EnvMod.join_emp_eq in H; subst; mytac_H
  | H:EnvMod.join _ empenv _
    |- _ =>
        apply EnvMod.join_comm in H; apply EnvMod.join_emp_eq in H; subst;
         mytac_H
  | H:OSAbstMod.join empabst _ _
    |- _ => apply OSAbstMod.join_emp_eq in H; subst; mytac_H
  | H:OSAbstMod.join _ empabst _
    |- _ =>
        apply OSAbstMod.join_comm in H; apply OSAbstMod.join_emp_eq in H;
         subst; mytac_H
  | H:MemMod.join ?a ?b ?ab
    |- MemMod.join ?b ?a ?ab => apply MemMod.join_comm; auto
  | H:EnvMod.join ?a ?b ?ab
    |- EnvMod.join ?b ?a ?ab => apply EnvMod.join_comm; auto
  | H:OSAbstMod.join ?a ?b ?ab
    |- OSAbstMod.join ?b ?a ?ab => apply OSAbstMod.join_comm; auto
  | H:MemMod.join ?a ?b ?ab
    |- MemMod.disj ?a ?b => apply MemMod.join_disj_meq in H; destruct H; auto
  | H:EnvMod.join ?a ?b ?ab
    |- EnvMod.disj ?a ?b => apply EnvMod.join_disj_meq in H; destruct H; auto
  | H:OSAbstMod.join ?a ?b ?ab
    |- OSAbstMod.disj ?a ?b =>
        apply OSAbstMod.join_disj_meq in H; destruct H; auto
  | H:MemMod.join ?a ?b ?ab
    |- MemMod.disj ?b ?a => apply MemMod.join_comm; mytac_H
  | H:EnvMod.join ?a ?b ?ab
    |- EnvMod.disj ?b ?a => apply EnvMod.join_comm; mytac_H
  | H:OSAbstMod.join ?a ?b ?ab
    |- OSAbstMod.disj ?b ?a => apply OSAbstMod.join_comm; mytac_H
  | H:MemMod.meq _ _ |- _ => apply MemMod.meq_eq in H; mytac_H
  | H:EnvMod.meq _ _ |- _ => apply EnvMod.meq_eq in H; mytac_H
  | H:OSAbstMod.meq _ _ |- _ => apply OSAbstMod.meq_eq in H; mytac_H
  | H:(_, _) = (_, _) |- _ => inversion H; clear H; mytac_H
  | H:?x = ?x |- _ => clear H; mytac_H
  | H:True |- _ => clear H; mytac_H
  | _ => try (progress subst; mytac_H)                            
  end.
 *)
Ltac mytac_H := heat.

Ltac exact_s :=
  match goal with
    | H : ?s |= _ |- ?s |= _ =>
      exact H
  end.

Ltac transform_pre lemma cancel_tac :=
  eapply backward_rule1;
  [ intros; 
    eapply lemma; 
    match goal with
      | |- ?s |= _ => 
        cancel_tac;
        try exact_s;
        sep pauto
      | _ => solve [eauto;auto | pauto]
    end  
   | idtac ].

Lemma node_fold:
  forall s P v vl t b,
    s |= Astruct (b, Int.zero) t vl ** P ->
    v = Vptr (b, Int.zero) ->
    struct_type_vallist_match t vl ->
    s |= node v vl t ** P.
  intros.
  unfold node.
  sep pauto.
Qed.

Ltac fold_node :=
  transform_pre node_fold ltac:(sep cancel Astruct).


Lemma AOSEventTbl_fold:
  forall s P letbl etbl,
    s |= Aarray letbl (Tarray Int8u ∘OS_EVENT_TBL_SIZE) etbl ** P ->
    array_type_vallist_match Int8u etbl ->
    s |= AOSEventTbl letbl etbl ** P.
  intros; unfold AOSEventTbl; sep pauto.
Qed.

Ltac fold_AOSEventTbl :=
  transform_pre AOSEventTbl_fold ltac:(sep cancel Aarray).

Lemma AOSEvent_fold:
  forall s P losevent osevent etbl letbl egrp,
    s |= node losevent osevent OS_EVENT **
         AOSEventTbl letbl etbl ** P ->
    id_addrval' losevent OSEventTbl OS_EVENT = Some letbl ->
    V_OSEventGrp osevent = Some egrp ->
    RL_Tbl_Grp_P etbl egrp ->
    s |= AOSEvent losevent osevent etbl ** P.
  intros.
  unfold AOSEvent.
  sep pauto.
  eauto.
  eauto.
Qed.

Ltac fold_AOSEvent :=
  transform_pre AOSEvent_fold ltac:(sep cancel node;
                                    sep cancel AOSEventTbl).

Lemma AEventNode_fold:
  forall s v osevent etbl d P,
    s |= AOSEvent v osevent etbl ** 
         AEventData osevent d ** P ->
    s |= AEventNode v osevent etbl d ** P.
  intros.
  unfold AEventNode.
  sep auto.
Qed.

Ltac fold_AEventNode :=
  transform_pre AEventNode_fold ltac:(sep cancel AOSEvent;
                                      sep cancel AEventData).

Ltac fold_AEventNode_r :=
  try fold_node;
  try fold_AOSEventTbl;
  try fold_AOSEvent;
  try fold_AEventNode.

Lemma lzh_evsllseg_compose:
  forall s P (qptrl:list EventCtr) l x p msgqls tail vn qptrl1 qptrl2 msgqls1 msgqls2 tl msgq, 
    s |= AEventNode tl l x msgq **
      evsllseg p tl qptrl1 msgqls1 **
      evsllseg vn tail qptrl2 msgqls2 ** P ->
    V_OSEventListPtr l = Some vn ->
    qptrl = qptrl1 ++ ((l,x)::nil) ++ qptrl2  ->
    msgqls = msgqls1 ++ (msgq::nil) ++msgqls2 ->
    s |= evsllseg p tail qptrl msgqls ** P.
  intros.
  eapply evsllseg_compose; eauto.
Qed.

Ltac compose_evsllseg :=
  transform_pre lzh_evsllseg_compose ltac:(sep cancel AEventNode;
                                           sep cancel evsllseg;
                                           sep cancel evsllseg).

Lemma AECBList_fold:
  forall s P l ecbls els tcbls p,
    s |= evsllseg p Vnull l ecbls **
         GV OSEventList @ (Tptr OS_EVENT) |-> p ** P ->
    ECBList_P p Vnull l ecbls els tcbls ->
    s |= AECBList l ecbls els tcbls ** P.
  intros.
  unfold AECBList.
  sep pauto.
Qed.

Ltac fold_AECBList:=
  transform_pre AECBList_fold ltac:(sep cancel evsllseg).

Lemma semacc_ltu_zero_false:
  forall i,
    Int.ltu ($ 0) i = false ->
    i = $ 0.
  intros.
  int auto.
  assert (Int.unsigned i >= 0).
    int auto.
  assert (Int.unsigned i = 0) by omega.
  rewrite <- unsigned_zero in H1.
  apply unsigned_inj in H1.
  auto.
Qed.

Lemma semacc_int_eq_true:
  forall i j,
    Int.eq i j = true ->
    i = j.
  intros.
  assert (Hif: if Int.eq i j then i = j else i <> j).
    eapply Int.eq_spec.
  rewrite H in Hif.
  auto.
Qed.

(*
Ltac mytac_g :=
  match goal with
  | |- _ /\ _ => split; mytac_g
  | |- MemMod.join empmem _ _ => apply MemMod.join_emp; mytac_g
  | |- MemMod.join _ empmem _ =>
        apply MemMod.join_comm; apply MemMod.join_emp; mytac_g
  | |- EnvMod.join empenv _ _ => apply EnvMod.join_emp; mytac_g
  | |- EnvMod.join _ empenv _ =>
        apply EnvMod.join_comm; apply EnvMod.join_emp; mytac_g
  | |- OSAbstMod.join empabst _ _ => apply OSAbstMod.join_emp; mytac_g
  | |- OSAbstMod.join _ empabst _ =>
        apply OSAbstMod.join_comm; apply OSAbstMod.join_emp; mytac_g
  | |- ?x = ?x => reflexivity
  | |- MemMod.join _ ?a ?a => apply MemMod.join_emp; mytac_g
  | |- MemMod.join ?a _ ?a => apply MemMod.join_comm; mytac_g
  | |- EnvMod.join _ ?a ?a => apply EnvMod.join_emp; mytac_g
  | |- EnvMod.join ?a _ ?a => apply EnvMod.join_comm; mytac_g
  | |- OSAbstMod.join _ ?a ?a => apply OSAbstMod.join_emp; mytac_g
  | |- OSAbstMod.join ?a _ ?a => apply OSAbstMod.join_comm; mytac_g
  | |- empmem = _ => reflexivity; mytac_g
  | |- _ = empmem => reflexivity; mytac_g
  | |- empenv = _ => reflexivity; mytac_g
  | |- _ = empenv => reflexivity; mytac_g
  | |- emposabst _ => unfold emposabst; reflexivity; mytac_g
  | |- empabst = _ => reflexivity; mytac_g
  | |- _ = empabst => reflexivity; mytac_g
  | |- empisr = _ => reflexivity; mytac_g
  | |- _ = empisr => reflexivity; mytac_g
  
  | |- True => auto
  | _ => try (progress subst; mytac_g)
  | _ => try (progress intros; mytac_g)
  end.
 *)
Ltac mytac_g := swallow; jeauto2.

Lemma semacc_int_eq_false:
  forall x y,
    Int.eq x y = false ->
    x <> y.
  intros.
  lets Hif: Int.eq_spec x y.
  rewrite H in Hif.
  auto.
Qed.  
  
Ltac lzh_simpl_int_eq :=
  repeat match goal with
           | H : Int.eq _ _ = true |- _ =>
               apply semacc_int_eq_true in H
           | H : Int.eq _ _ = false |- _ =>
               apply semacc_int_eq_false in H
         end.
