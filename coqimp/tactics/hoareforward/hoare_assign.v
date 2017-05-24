Require Import sep_auto.
Require Import hoare_conseq.
Require Import derived_rules.
Require Import symbolic_lemmas.
Require Import symbolic_execution.
Require Import include_frm.

Set Implicit Arguments.

Open Scope nat_scope.

(** assign_rules *)
Open Scope code_scope.


Fixpoint assign_type_match_fun  (t1 t2:type) :=
  match t1,t2 with
    | ( t ∗), Tnull => true
    | Tnull, Tnull => true
    | Void, Void => true
    | (t ∗), (t' ∗) => true
    | Tarray t n, Tarray t' n' => andb (type_eq t t') (beq_nat n n')
    | (t ∗) , Tarray t' n => type_eq t t'
    | Tstruct id dl, Tstruct id' dl'=> andb (dl_eq dl dl') (Zeq_bool id id')
    | Tint8 , Tint8 => true
    | Tint8, Int16u => true
    | Tint8, Int32u => true
    | Int16u, Tint8 => true
    | Int16u , Int16u => true
    | Int16u, Int32u => true
    | Int32u , Tint8 =>true
    | Int32u, Int16u =>true
    | Int32u, Int32u => true
    | Tcom_ptr _ , Tnull => true
    | (t ∗), (Tcom_ptr t') => true
    | (Tcom_ptr t), (Tcom_ptr t') => true
    | (Tcom_ptr t), (t' ∗ ) => true
    | _, _ => false
  end.

Lemma dl_eq_true_eq : forall d1 d2, dl_eq d1 d2 = true -> d1 = d2.
Proof.
  intro.
  induction d1; intros.
  simpl in H; destruct d2; tryfalse; auto.
  simpl in H; destruct d2; tryfalse.
  do 2 ( apply andb_true_iff in H; destruct H).
  apply Zeq_bool_eq in H; substs.
  apply type_eq_true_eq in H1; substs.
  apply IHd1 in H0; substs.
  auto.
Qed.

Lemma assign_type_match_true: 
  forall t1 t2, 
    assign_type_match_fun t1 t2 = true -> 
    assign_type_match t1 t2.  
Proof.
  intros.
  destruct t1; destruct t2; simpl in H; tryfalse;
  try solve [apply eq_int; auto].
  apply eq_tnull; auto.
  apply eq_tvoid.
  apply eq_tnull; left; eauto.
  apply eq_vptr; eauto.
  apply eq_vcomptr; splits; eauto.
  apply array_to_vptr; apply type_eq_true_eq in H; substs; eauto.
  apply eq_tnull; branch 2;  eauto.
  apply eq_vcomptr.  splits; eauto.
  apply eq_vcomptr; splits; eauto.
  apply andb_true_iff in H; destruct H.
  apply eq_array; apply type_eq_true_eq in H; apply beq_nat_true in H0; substs; eauto.
  apply andb_true_iff in H; destruct H.
  apply Zeq_bool_eq in H0; substs.
  apply eq_struct.
  apply dl_eq_true_eq in H; substs.
  eauto.
Qed.
Close Scope code_scope.


Lemma assign_rule_general':
  forall Spec I r ri p p' e1 e2 l v1 v2 tp1 tp2 aop sc li tid,  
    assign_type_match tp1 tp2 ->  
    p ==> Lv e1 @ tp1 == l ->
    p <==>  PV l @ tp1|-> v1 ** p' ->
    p ==>  Rv e2 @ tp2 == v2 ->
    (*p ==>  EX lg, p_local li tid lg ** Atrue ->*)
    PV l @ tp1|-> v2 ** p' ==>  EX lg, p_local li tid lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-tid {{ <|| aop ||> ** p }} (sassign e1 e2) {{ <|| aop ||> ** PV l @ tp1|-> v2 ** p' }}.
Proof.
  intros.
  eapply backward_rule1 with (p:= <|| aop ||> ** PV l @tp1|-> v1 ** p'). 
  intros.
  sep auto.
  apply H1 in H4.
  auto.
  auto.
  eapply assign_rule' ;eauto.
  intros.
  apply H1 in H4.
  split; auto.
  intros.
  apply H3.
  sep auto.
Qed.

Lemma addrof_rv_to_lv :
  forall e t l,
    Rv eaddrof e @ Tptr t == Vptr l ==> Lv e @ t == l.
Proof.
  intros.
  unfold sat in *; fold sat in *; simpljoin.
  
  destruct s as [ [ [ [ [ [ ] ] ] ] ] ]; simpl in *.
  destruct e; simpl in *; tryfalse || auto.
  destruct (get e1 v), (get e0 v); tryfalse || auto.
  destruct p; auto.
  split;auto.
  inverts H0;auto.
  destruct p;inverts H0; auto.
  destruct p;inverts H0; auto.
  destruct (evaltype e (e0, e1, m)); tryfalse || auto.
  destruct t0; tryfalse || auto.
  destruct ( evaltype e (e0, e1, m));destruct (evaladdr e (e0, e1, m));inverts H0;tryfalse || auto.  
  destruct ( evaltype e (e0, e1, m));destruct (evaladdr e (e0, e1, m));inverts H0;tryfalse || auto.

  destruct t0; destruct v; tryfalse || auto.
  destruct (memory.ftype i0 d); tryfalse || auto.
  destruct (memory.ftype i0 d); tryfalse || auto.
  destruct (memory.ftype i0 d); tryfalse || auto.
  destruct (memory.ftype i0 d); tryfalse || auto.
  destruct a0.
  inverts H3;auto.
  destruct t0; tryfalse || auto.
  destruct (memory.ftype i0 d); tryfalse || auto.
  destruct (evaltype e2 (e0, e1, m)), (evaltype e3 (e0, e1, m)); tryfalse || auto.
  destruct t0, t;inverts H0; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.


  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.

  destruct t1;inverts H3; tryfalse || auto.
  destruct t1;inverts H3; tryfalse || auto.
  
  destruct t0; tryfalse || auto.
Qed.

Theorem assign_rule_general :   
  forall Spec I r ri p p' e1 e2 l v1 v2 tp1 tp2 aop sc  (li : LocalInv) (tid : tid),
    p ==> Rv (eaddrof e1) @ Tptr tp1 == Vptr l ->
    p <==>  PV l @ tp1|-> v1 ** p' ->
    p ==>  Rv e2 @ tp2 == v2 ->
    assign_type_match tp1 tp2 ->
    (*p ==> EX lg : list logicvar, p_local li tid lg ** Atrue ->*)
    PV l @ tp1 |-> v2 ** p' ==>
       EX lg : list logicvar, p_local li tid lg ** Atrue ->
    {|Spec, sc, li, I, r, ri|}|- tid {{ <|| aop ||>  ** p}} 
                                     sassign e1 e2 {{ <|| aop ||>  ** PV l @ tp1 |-> v2 ** p'}}.
Proof.
  intros.
  eapply assign_rule_general'; eauto.
  intros.
  apply H in H4.
  apply addrof_rv_to_lv; auto.
Qed.

Theorem assign_rule_lvar :
  forall Spec I r ri p p' x e v1 v2 tp1 tp2 aop sc li tid,
    p <==>  LV x @ tp1|-> v1 ** p' ->
    p ==>  Rv e @ tp2 == v2 ->
    assign_type_match tp1 tp2 ->
    (*p ==> EX lg : list logicvar, p_local li tid lg ** Atrue ->*)
    LV x @ tp1|-> v2 ** p' ==>
       EX lg : list logicvar, p_local li tid lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-tid {{ <|| aop ||> ** p}} (sassign (evar x) e) {{ <|| aop ||> ** LV x @ tp1|-> v2 ** p' }}.
Proof.
  intros.
  apply backward_rule1 with (<|| aop ||> ** LV x @ tp1 |-> v1 ** p'); intros.
  sep auto.
  apply H in H3; scancel.
  auto.
  unfold Alvarmapsto.
  hoare normal pre; hoare normal post.
  repeat (apply ex_intro_rule'; intro).
  hoare lifts (3::2::nil)%list pre. 
  hoare lifts (3::2::nil)%list post.
  eapply assign_rule_general.
  intros.
  eapply addrof_lvar_rv.
  sep lift 2 in H3; eauto.
  split; intros; eauto.
  intros.
  apply H0.
  apply H.
  unfold Alvarmapsto; sep auto.
  auto.
  intros;apply H2.
  unfold Alvarmapsto; sep auto.
Qed.

Theorem assign_rule_gvar :
  forall Spec I r ri p p' x e l v1 v2 tp1 tp2 aop sc li tid,
    p <==> A_dom_lenv l ** GV x @ tp1|-> v1 ** p' ->
    var_notin_dom x l = true ->
    p ==>  Rv e @ tp2 == v2 ->
    assign_type_match tp1 tp2 ->
    (*p ==> EX lg : list logicvar, p_local li tid lg ** Atrue ->*)
    A_dom_lenv l ** GV x @ tp1|-> v2 ** p' ==>
               EX lg : list logicvar, p_local li tid lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-tid {{ <|| aop ||> ** p }} (sassign (evar x) e) {{ <|| aop ||> ** A_dom_lenv l ** GV x @ tp1|-> v2 ** p' }}.
Proof.
  intros.
  apply backward_rule1 with (<|| aop ||> ** GV x @ tp1 |-> v1 ** A_dom_lenv l ** p'); intros.
  sep auto;auto.
  apply H in H4; sep auto;auto.
  apply H in H4.
  sep split in H4;auto.
  unfold Agvarmapsto.
  hoare normal pre; hoare normal post.
  repeat (apply ex_intro_rule'; intro).
  hoare lifts (3::2::nil)%list pre. 
  hoare lifts (3::2::nil)%list post.
  eapply assign_rule_general.
  intros.
  eapply addrof_gvar_rv.
  eapply dom_lenv_imp_notin_lenv; eauto.
  sep lifts (3::2::nil)%list in H4; eauto.
  split; intros; eauto.
  intros.
  apply H1.
  apply H.
  unfold Agvarmapsto; sep auto.
  auto.
  intros;apply H3.
  unfold Agvarmapsto; sep auto.
Qed.

Lemma assign_rule'' :
  forall Spec I r ri  p p' e1 e2 l v1 v2 tp1 tp2 aop sc li tid,  
    assign_type_match tp1 tp2 ->  
    p ==> Lv e1 @ tp1 == l ->
    p <==>  PV l @ tp1|-> v1 ** p' ->
    p ==>  Rv e2 @ tp2 == v2 ->
    (*p ==>  EX lg, p_local li tid lg ** Atrue ->*)
    PV l @ tp1|-> v2 ** p' ==>  EX lg, p_local li tid lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-tid {{ p ** <|| aop ||> }} (sassign e1 e2) {{ PV l @ tp1|-> v2 ** p' ** <|| aop ||> }}.
Proof.
  intros.
  eapply backward_rule1 with (p:= <||aop||> ** PV l @tp1|-> v1 ** p' ). 
  intros.
  sep cancel 2%nat 1%nat.
  apply H1 in H4;auto.
  eapply forward_rule1 with (<|| aop ||> ** PV l @ tp1|-> v2 ** p').
  intros;sep auto.
  eapply assign_rule';eauto.
  intros.
  split;auto.
  apply H0;apply H1;auto.
  apply H2;apply H1;auto.
  intros;apply H3;sep auto.
Qed.
(*
Lemma assign_rule''' :
  forall Spec I r ri  p p' e1 e2 l v1 v2 tp1 tp2 aop sc,  
    assign_type_match tp1 tp2 ->  
    p ==> Lv e1 @ tp1 == l ->
    p <==>  PV l @ tp1|-> v1 ** p' ->
    p ==>  Rv e2 @ tp2 == v2 ->
    {| Spec, sc, I, r, ri |} |- {{ p ** <|| aop ||> }} (sassign e1 e2) {{ PV l @ tp1|-> v2 ** p' ** <|| aop ||> }}.
Proof.
  intros.
  assert ( {| Spec, sc, I, r, ri |} |- {{ p //\\ <| aop |> }} (sassign e1 e2) {{ PV l @ tp1|-> v2 ** p' //\\ <| aop |> }}).
  eapply assign_rule'';eauto.
  apply conseq_rule with (p:=p //\\  <| aop |>) (q:=PV l @ tp1 |-> v2 ** p' //\\  <| aop |>) ;auto.
  eapply Aop_Aop'_eq;eauto.
  assert ( (PV l @ tp1 |-> v2 ** p') //\\  <| aop |>  <==>
                                     (PV l @ tp1 |-> v2 ** p') **  <|| aop ||> ).
  eapply Aop_Aop'_eq;eauto.
  intros.
  apply H4 in H5.
  sep_auto; auto.
Qed.
 *)
Lemma assign_rule_deref_ptr :
  forall Spec I r ri aop p p' tp1 tp2 l v1 v2 e1 e2 sc li tid,
    p ==> Rv e1 @ (Tptr tp1) == Vptr l ->
    p <==> PV l @ tp1 |-> v1 ** p' ->
    p ==> Rv e2 @ tp2 == v2 ->
    assign_type_match tp1 tp2 ->
    (*p ==> EX lg : list logicvar, p_local li tid lg ** Atrue ->*)
    PV l @ tp1 |-> v2 ** p' ==>
       EX lg : list logicvar, p_local li tid lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-tid {{ <|| aop ||> ** p }} (sassign (ederef e1) e2) {{ <|| aop ||> ** PV l @ tp1 |-> v2 ** p' }}.
Proof.
  intros.
  apply assign_rule_general with (v1 := v1) (tp2 := tp2); auto.
  intros; apply addrof_deref_rv; auto. 
Qed.



Lemma star3_comm: forall p q r l, p ** (q ** l) ** r <==> q ** p ** l ** r.
Proof.
  intros.
  split;intros;sep_auto.
Qed.
Lemma star3_comm':forall s p q r l, s |= p ** q ** r ** l -> s |= (p ** r) ** q ** l.
Proof.
  intros.
  sep_auto.
Qed.

Lemma eq_impl_trans: forall p q r, p <==> q -> q ==> r -> p ==> r.
Proof.
  intros.
  destruct H with s.
  apply H2 in H1.
  apply H0 in H1.
  auto.
Qed.

Lemma update_nth: forall vl n v vi, nth_val n vl = Some vi -> nth_val n (update_nth_val n vl v) = Some v.
Proof.
  intros.
  generalize dependent n.
  generalize dependent v.
  generalize dependent vi.
  induction vl.
  intros.
  destruct n;tryfalse.
  intros.
  destruct n;tryfalse.
  simpl in H.
  inverts H.
  simpl.
  auto.
  simpl in H.
  simpl.
  eapply IHvl;eauto.
Qed.

Lemma assign_rule_struct' : 
  forall Spec I r ri  p p' x id e tid decl n l vl vl' vi v tp1 tp1' tp2 aop sc li ct perm ,
    
    (forall ids dl, tp1' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), tp1' <> Tarray t'0 n0) ->
    good_decllist decl = true ->
    p <==>  LV x @ (Tptr tp1) |=> Vptr l @ perm ** Astruct l tp1 vl ** p' ->
    tp1 = Tstruct tid decl ->
    nth_val n vl = Some vi ->
    nth_id n decl = Some id ->
    ftype id decl = Some tp1' ->
    p ==>  Rv e @ tp2 == v ->
    assign_type_match tp1' tp2 -> 
    vl' = update_nth_val n vl v ->
    (*p ==> EX lg : list logicvar, p_local li ct lg ** Atrue ->*)
    LV x @ (Tptr tp1) |=> Vptr l @ perm ** Astruct l tp1 vl' ** p' ==>
       EX lg : list logicvar, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ p ** <|| aop ||> }} (sassign (efield (ederef (evar x)) id) e)  
                                                                                             {{(LV x @ (Tptr tp1) |=> Vptr l @ perm ** Astruct l tp1 vl' ** p' ** <|| aop ||>)}}.
Proof.
  introv Hnstr.
  introv Hnarr.
  intros.
  unfold Astruct in *.
  rewrite H1 in *.
  lets Hoff: nth_id_exists_off H3.
  destruct Hoff as (off&Hoff).
  destruct l as (b&i).
  assert (Astruct' (b, i) decl vl <==> PV (b,Int.add i off) @ tp1' |-> vi ** Astruct_rm (b,i) decl vl id).
  eapply struct_asrt_eq;eauto.
  lets Hrep:star_star_eq_rep H0 H9.

  assert ( LV x @ Tptr (Tstruct tid decl) |=> Vptr (b, i) @ perm **
              (PV (b, Int.add i off) @ tp1' |-> vi ** Astruct_rm (b, i) decl vl id) **
              p' ==> (Lv (efield (ederef (evar x)) id) @ tp1' == (b,Int.add i off))).
  
  eapply field_asrt_impl with (b:=b) (i:=i);eauto.
  assert (p ==> (Lv (efield (ederef (evar x)) id) @ tp1' == (b,Int.add i off))).  
  eapply eq_impl_trans;eauto.
  assert (p <==> 
            PV (b, Int.add i off) @ tp1' |-> vi **  (LV x @ Tptr (Tstruct tid decl) |=> Vptr (b, i) @ perm ** Astruct_rm (b, i) decl vl id **
                                                        p')).
  eapply asrt_eq_trans;eauto.
  split;intros;sep auto.
  clear Hrep H10 H9.
  assert ({|Spec , sc, li, I, r, ri|}|-ct  {{p **  <|| aop ||> }}
                                           sassign (efield (ederef (evar x)) id) e
                                           {{PV (b, Int.add i off) @ tp1' |-> v ** (LV x @ Tptr (Tstruct tid decl) |=> Vptr (b, i) @ perm **
                                                                                       Astruct_rm (b, i) decl vl id **
                                                                                       p') ** <|| aop ||> }}).

  eapply assign_rule'';eauto.
  intros.
  apply H8.
  sep auto.
  eapply struct_asrt_eq;eauto.
  eapply update_nth;eauto.
  sep auto.
  eapply struct_rm_update_eq;eauto.
  eapply forward_rule1.
  2:eapply H9.
  intros.
  sep auto.
  eapply struct_asrt_eq;eauto.
  eapply update_nth;eauto.
  sep auto.
  eapply struct_rm_update_eq;eauto.
Qed.


Lemma assign_rule_struct_typeneq': 
  forall Spec I r ri  p p' x id e tid decl n l vl vl' vi v tp1 tp1' tp2 aop sc li ct perm tt tid' decl',
    tt = Tstruct tid' decl' ->
    sub_decllist decl decl' = true ->
    (forall ids dl, tp1' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), tp1' <> Tarray t'0 n0) ->
    good_decllist decl = true ->
    p <==>  LV x @ (Tptr tt) |=> Vptr l @ perm ** Astruct l tp1 vl ** p' ->
    tp1 = Tstruct tid decl ->
    nth_val n vl = Some vi ->
    nth_id n decl = Some id ->
    ftype id decl = Some tp1' ->
    p ==>  Rv e @ tp2 == v ->
    assign_type_match tp1' tp2 -> 
    vl' = update_nth_val n vl v ->
    (*p ==> EX lg : list logicvar, p_local li ct lg ** Atrue ->*)
    LV x @ (Tptr tt) |=> Vptr l @ perm ** Astruct l tp1 vl' ** p' ==>
       EX lg : list logicvar, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ p ** <|| aop ||> }} (sassign (efield (ederef (evar x)) id) e)  
                                                                                             {{(LV x @ (Tptr tt) |=> Vptr l @ perm ** Astruct l tp1 vl' ** p' ** <|| aop ||>)}}.
Proof.
  introv Htt.
  introv Hsubdecl.
  introv Hnstr.
  introv Hnarr.
  subst tt.
  intros.
  unfold Astruct in *.
  rewrite H1 in *.
  lets Hoff: nth_id_exists_off H3.
  destruct Hoff as (off&Hoff).
  destruct l as (b&i).
  assert (Astruct' (b, i) decl vl <==> PV (b,Int.add i off) @ tp1' |-> vi ** Astruct_rm (b,i) decl vl id).
  eapply struct_asrt_eq;eauto.
  lets Hrep:star_star_eq_rep H0 H9.

  assert ( LV x @ Tptr (Tstruct tid' decl') |=> Vptr (b, i) @ perm **
              (PV (b, Int.add i off) @ tp1' |-> vi ** Astruct_rm (b, i) decl vl id) **
              p' ==> (Lv (efield (ederef (evar x)) id) @ tp1' == (b,Int.add i off))).
  
  eapply field_asrt_impl with (b:=b) (i:=i);eauto.
  eapply sub_decllist_ftype;eauto.
  eapply sub_decllist_offset;eauto.
  assert (p ==> (Lv (efield (ederef (evar x)) id) @ tp1' == (b,Int.add i off))).  
  eapply eq_impl_trans;eauto.
  assert (p <==> 
            PV (b, Int.add i off) @ tp1' |-> vi **  (LV x @ Tptr (Tstruct tid' decl') |=> Vptr (b, i) @ perm ** Astruct_rm (b, i) decl vl id **
                                                        p')).
  eapply asrt_eq_trans;eauto.
  split;intros;sep auto.
  clear Hrep H9 H10.
  assert ({|Spec , sc, li, I, r, ri|}|-ct  {{p **  <|| aop ||> }}
                                           sassign (efield (ederef (evar x)) id) e
                                           {{PV (b, Int.add i off) @ tp1' |-> v ** (LV x @ Tptr (Tstruct tid' decl') |=> Vptr (b, i) @ perm **
                                                                                       Astruct_rm (b, i) decl vl id **
                                                                                       p') ** <|| aop ||> }}).

  eapply assign_rule'';eauto.
  intros.
  apply H8.
  sep auto.
  eapply struct_asrt_eq;eauto.
  eapply update_nth;eauto.
  sep auto.
  eapply struct_rm_update_eq;eauto.
  eapply forward_rule1.
  2:eapply H9.
  intros.
  sep auto.
  eapply struct_asrt_eq;eauto.
  eapply update_nth;eauto.
  sep auto.
  eapply struct_rm_update_eq;eauto.
Qed.

Lemma assign_rule_struct_g' : 
  forall Spec I r ri  p p' x id e tid decl n l vl vl' vi v tp1 tp1' tp2 aop sc li ct perm ,
    (forall ids dl, tp1' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), tp1' <> Tarray t'0 n0) ->
    good_decllist decl = true ->
    p <==> (A_notin_lenv  x **  GV x @ (Tptr tp1) |=> Vptr l @ perm ) ** Astruct l tp1 vl ** p' ->
    tp1 = Tstruct tid decl ->
    nth_val n vl = Some vi ->
    nth_id n decl = Some id ->
    ftype id decl = Some tp1' ->
    p ==>  Rv e @ tp2 == v ->
    assign_type_match tp1' tp2 -> 
    vl' = update_nth_val n vl v ->
    (*p ==> EX lg : list logicvar, p_local li ct lg ** Atrue ->*)
    (A_notin_lenv x ** GV x @ (Tptr tp1) |=> Vptr l @ perm ) ** Astruct l tp1 vl' ** p' ==>
                                                     EX lg : list logicvar, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ p ** <|| aop ||> }} (sassign (efield (ederef (evar x)) id) e)  
                                      {{((A_notin_lenv x ** GV x @ (Tptr tp1) |=> Vptr l @ perm ) ** Astruct l tp1 vl' ** p' ** <|| aop ||>)}}.
Proof.
  introv Hnstr.
  introv Hnarr.
  intros.
  unfold Astruct in *.
  rewrite H1 in *.
  lets Hoff: nth_id_exists_off H3.
  destruct Hoff as (off&Hoff).
  destruct l as (b&i).
  assert (Astruct' (b, i) decl vl <==> PV (b,Int.add i off) @ tp1' |-> vi ** Astruct_rm (b,i) decl vl id).
  eapply struct_asrt_eq;eauto.
  lets Hrep:star_star_eq_rep H0 H9.

  assert ( (A_notin_lenv  x ** GV x @ Tptr (Tstruct tid decl) |=> Vptr (b, i) @ perm ) **
                                                                               (PV (b, Int.add i off) @ tp1' |-> vi ** Astruct_rm (b, i) decl vl id) **
                                                                               p' ==> (Lv (efield (ederef (evar x)) id) @ tp1' == (b,Int.add i off))).

  eapply field_asrt_impl_g with (b:=b) (i:=i);eauto.
  assert (p ==> (Lv (efield (ederef (evar x)) id) @ tp1' == (b,Int.add i off))).  
  eapply eq_impl_trans;eauto.
  assert (p <==> 
            PV (b, Int.add i off) @ tp1' |-> vi **  (A_notin_lenv  x ** GV x @ Tptr (Tstruct tid decl) |=> Vptr (b, i) @ perm ) ** Astruct_rm (b, i) decl vl id **
            p').
  eapply asrt_eq_trans;eauto.
  eapply star3_comm.
  clear Hrep H9 H10.
  assert ({|Spec, sc, li, I, r, ri|}|-ct  {{p **  <|| aop ||> }}
                                          sassign (efield (ederef (evar x)) id) e
                                          {{PV (b, Int.add i off) @ tp1' |-> v ** (A_notin_lenv  x ** GV x @ Tptr (Tstruct tid decl) |=> Vptr (b, i) @ perm **
                                                                                                 Astruct_rm (b, i) decl vl id **
                                                                                                 p') ** <|| aop ||> }}).
  eapply assign_rule'';eauto.
  split;intros.
  apply H12 in H9.
  sep auto.
  apply H12.
  sep auto.
  intros;apply H8.
  sep auto.
  erewrite struct_asrt_eq with (v:=v);eauto.
  sep auto.
  eapply struct_rm_update_eq;eauto.
  eapply update_nth;eauto.
  eapply forward_rule1.
  2:eauto.
  intros.
  sep auto.
  eapply struct_asrt_eq;eauto.
  eapply update_nth;eauto.
  sep auto.
  eapply struct_rm_update_eq;eauto.
Qed.


Lemma assign_rule_struct_g_typeneq' : 
  forall Spec I r ri  p p' x id e tid decl n l vl vl' vi v tp1 tp1' tp2 aop sc li ct perm tt tid' decl',
    tt = Tstruct tid' decl' ->
    sub_decllist decl decl' = true ->
    (forall ids dl, tp1' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), tp1' <> Tarray t'0 n0) ->
    good_decllist decl = true ->
    p <==> (A_notin_lenv  x **  GV x @ (Tptr tt) |=> Vptr l @ perm ) ** Astruct l tp1 vl ** p' ->
    tp1 = Tstruct tid decl ->
    nth_val n vl = Some vi ->
    nth_id n decl = Some id ->
    ftype id decl = Some tp1' ->
    p ==>  Rv e @ tp2 == v ->
    assign_type_match tp1' tp2 -> 
    vl' = update_nth_val n vl v ->
    (*p ==> EX lg : list logicvar, p_local li ct lg ** Atrue ->*)
    (A_notin_lenv x ** GV x @ (Tptr tt) |=> Vptr l @ perm ) ** Astruct l tp1 vl' ** p' ==>
                                                     EX lg : list logicvar, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ p ** <|| aop ||> }} (sassign (efield (ederef (evar x)) id) e)  
                                      {{((A_notin_lenv x ** GV x @ (Tptr tt) |=> Vptr l @ perm ) ** Astruct l tp1 vl' ** p' ** <|| aop ||>)}}.
Proof.
  introv Htt.
  introv Hsubdecl.
  introv Hnstr.
  introv Hnarr.
  subst tt.
  intros.
  unfold Astruct in *.
  rewrite H1 in *.
  lets Hoff: nth_id_exists_off H3.
  destruct Hoff as (off&Hoff).
  destruct l as (b&i).
  assert (Astruct' (b, i) decl vl <==> PV (b,Int.add i off) @ tp1' |-> vi ** Astruct_rm (b,i) decl vl id).
  eapply struct_asrt_eq;eauto.
  lets Hrep:star_star_eq_rep H0 H9.

  assert ( (A_notin_lenv  x ** GV x @ Tptr (Tstruct tid' decl') |=> Vptr (b, i) @ perm ) **
                                                                               (PV (b, Int.add i off) @ tp1' |-> vi ** Astruct_rm (b, i) decl vl id) **
                                                                               p' ==> (Lv (efield (ederef (evar x)) id) @ tp1' == (b,Int.add i off))).

  eapply field_asrt_impl_g with (b:=b) (i:=i);eauto.
  eapply sub_decllist_ftype;eauto.
  eapply sub_decllist_offset;eauto.
  assert (p ==> (Lv (efield (ederef (evar x)) id) @ tp1' == (b,Int.add i off))).  
  eapply eq_impl_trans;eauto.
  assert (p <==> 
            PV (b, Int.add i off) @ tp1' |-> vi **  (A_notin_lenv  x ** GV x @ Tptr (Tstruct tid' decl') |=> Vptr (b, i) @ perm ) ** Astruct_rm (b, i) decl vl id **
            p').
  eapply asrt_eq_trans;eauto.
  eapply star3_comm.
  clear Hrep H9 H10.
  assert ({|Spec, sc, li, I, r, ri|}|-ct  {{p **  <|| aop ||> }}
                                          sassign (efield (ederef (evar x)) id) e
                                          {{PV (b, Int.add i off) @ tp1' |-> v ** (A_notin_lenv  x ** GV x @ Tptr (Tstruct tid' decl') |=> Vptr (b, i) @ perm **
                                                                                                 Astruct_rm (b, i) decl vl id **
                                                                                                 p') ** <|| aop ||> }}).
  eapply assign_rule'';eauto.
  split;intros.
  apply H12 in H9.
  sep auto.
  apply H12.
  sep auto.
  intros;apply H8.
  sep auto.
  erewrite struct_asrt_eq with (v:=v);eauto.
  sep auto.
  eapply struct_rm_update_eq;eauto.
  eapply update_nth;eauto.
  eapply forward_rule1.
  2:eauto.
  intros.
  sep auto.
  eapply struct_asrt_eq;eauto.
  eapply update_nth;eauto.
  sep auto.
  eapply struct_rm_update_eq;eauto.
Qed.

Lemma loadbytes_local: 
  forall m1 m2 m bls b i t, 
    join m1 m2 m -> 
    loadbytes m1 (b,i) (typelen t) = Some bls -> 
    loadbytes m (b,i) (typelen t) = Some bls.
Proof.
  intros.
  gen m1 m2 m bls b i.
  induction (typelen t); intros.
  simpl in H0.
  inversion H0.
  substs.
  simpl.
  auto.

  simpl in H0.
  unfold get in H0; simpl in H0.
  remember (HalfPermMap.get m1 (b,i)) as Haf.
  destruct Haf; tryfalse.
  destruct b0.
  remember (loadbytes m1 (b, (i+1)%Z) n) as Hx.
  destruct Hx; tryfalse.
  inverts H0.
  simpl.
  unfold get ; simpl.
  apply eq_sym in HeqHaf.
  lets Hasx : map_get_join_val H HeqHaf.
  simp join.
  rewrite H0.
  apply eq_sym in HeqHx.
  lets Hab : IHn H HeqHx.
  replace (loadbytes m (b, (i + 1)%Z) n) with (Some l).
  auto.
Qed.


Lemma field_array_asrt_impl:
  forall p p' b i t m id e2 x decl n n' te2 sid off perm, 
    field_offset id decl = Some off ->
    nth_id n' decl = Some id ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z.of_nat m)) -> 
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    ftype id decl = Some (Tarray t n) -> 
    p ==>  
      LV x @ Tptr (Tstruct sid decl) |=> Vptr (b,i) @ perm ** p' ->
    p ==>  Lv earrayelem (efield (ederef (evar x)) id) e2 @ t ==
    (b,
     Int.add (Int.add i off)
             (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                      (Int.repr (BinInt.Z.of_nat m)))).
Proof.
  introv Hoff.
  intros.
  lets He2:H0 H4.
  lets Hg: H3 H4.
  clear H0 H3 H4.
  destruct s as [[]].
  destruct t0 as [[[[]]]].
  simpl in *;simpljoin.
  rewrite H11.
  rewrite H2.
  apply mapstoval_loadbytes in H12.
  destruct H12 as (bls&H12).
  destruct H12.
  apply map_join_emp'' in H8.
  inverts H8.
  lets Hl:loadbytes_local H3 H0.
  rewrite Int.unsigned_zero in Hl.
  assert (loadbytes m0 (x13, BinNums.Z0) (typelen (Tptr (Tstruct sid decl))) = Some bls).
  auto.
  unfold load;unfold loadm.
  rewrite H8.
  rewrite H4.
  unfold getoff.
  simpl.
  rewrite H11.
  rewrite Hoff.
  rewrite H17.
  simpl addr_to_addrval.
  rewrite Int.repr_unsigned.
  rewrite Int.repr_unsigned.
  auto.
  simpl;auto.
  rewrite H18.
  split;auto.
  destruct H1;subst;auto.
  destruct H1;subst;auto.
  simpl;auto.
Qed.

Lemma field_array_asrt_impl_g:
  forall p p' b i t m id e2 x decl  n' n te2 sid off perm, 
    field_offset id decl = Some off ->
    nth_id n' decl = Some id ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z.of_nat m)) -> 
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    ftype id decl = Some (Tarray t n) -> 
    p ==>  
      A_notin_lenv x ** GV x @ Tptr (Tstruct sid decl) |=> Vptr (b,i) @ perm ** p' ->
    p ==>  Lv earrayelem (efield (ederef (evar x)) id) e2 @ t ==
    (b,
     Int.add (Int.add i off)
             (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                      (Int.repr (BinInt.Z.of_nat m)))).
Proof.
  introv Hoff.
  intros.
  lets He2:H0 H4.
  lets Hg: H3 H4.
  clear H0 H3 H4.
  destruct s as [[]].
  destruct t0 as [[[[]]]].
  simpl in *;simpljoin.
  apply map_join_emp'' in H3;inverts H3.
  apply map_join_emp'' in H13;inverts H13.
  apply EnvMod.nindom_get in H6.
  unfold get in *.
  simpl in *.
  rewrite H6.
  rewrite H16.
  rewrite H2.
  apply mapstoval_loadbytes in H17.
  destruct H17 as (bls&H17).
  destruct H17.
  lets Hl:loadbytes_local H8 H4.
  rewrite Int.unsigned_zero in Hl.
  assert (loadbytes m0 (x19, BinNums.Z0) (typelen (Tptr (Tstruct sid decl))) = Some bls).
  auto.
  unfold load;unfold loadm.
  rewrite H9.
  rewrite H7.
  unfold getoff.
  simpl.
  unfold get;simpl.
  rewrite H6.
  rewrite H16.
  rewrite Hoff.
  rewrite H24.
  simpl addr_to_addrval.
  rewrite Int.repr_unsigned.
  rewrite Int.repr_unsigned.
  auto.
  split;auto.
  rewrite H25.
  destruct H0;subst;auto.
  destruct H1;subst;auto.
  destruct H0;subst;auto.
  simpl;auto.
Qed.

Lemma asrt_rep_4:
  forall p q r s t u v, 
    p <==> q ** r ** s ** t ->
    s <==> u ** v -> 
    p <==> u ** q ** v ** r ** t.
Proof.
  intros.
  split;intros.
  destruct H with s0.
  sep_auto.
  apply H2 in H1.
  sep_auto.
  destruct H0 with H4.
  sep_auto.
  apply H5 in H1;auto.
  destruct H with s0.
  apply H3.
  sep_auto.
  destruct H0 with H4.
  apply H6;auto.
Qed.

Lemma asrt_rep_4':
  forall p q r s t u v,
    p <==> q ** r ** s ** t ->
    r <==> u ** v -> 
    p <==> u ** v ** q ** s ** t.
Proof.
  intros.
  split;intros.
  destruct H with s0.
  sep_auto.
  apply H2 in H1.
  sep_auto.
  destruct H0 with H4.
  sep_auto.
  apply H5 in H1;auto.
  destruct H with s0.
  apply H3.
  sep_auto.
  destruct H0 with H4.
  apply H6;auto.
Qed.

Lemma asrt_rep_5 :
  forall p f q r s t u v, 
    p <==> f ** q ** r ** s ** t -> 
    s <==> u ** v -> 
    p <==> u ** f ** q ** v ** r ** t.
Proof.
  intros.
  split;intros.
  destruct H with s0.
  sep_auto.
  apply H2 in H1.
  sep_auto.
  destruct H0 with H4.
  sep_auto.
  apply H5 in H1;auto.
  destruct H with s0.
  apply H3.
  sep_auto.
  destruct H0 with H4.
  apply H6;auto.
Qed.

Lemma asrt_rep_5':
  forall x p q r s t u v, 
    p <==> x ** q ** r ** s ** t ->
    r <==> u ** v -> 
    p <==> u ** v ** x ** q ** s ** t.
Proof.
  intros.
  split;intros.
  destruct H with s0.
  sep_auto.
  apply H2 in H1.
  sep_auto.
  destruct H0 with H4.
  sep_auto.
  apply H5 in H1;auto.
  destruct H with s0.
  apply H3.
  sep_auto.
  destruct H0 with H4.
  apply H6;auto.
Qed.

Lemma field_deref_asrt_impl: 
  forall p b i off tp1' lv decl  id tid x n p' perm,
    (
      p <==>
        PV (b, Int.add i off) @ Tptr tp1' |=> Vptr lv @ perm **
        LV x @ Tptr (Tstruct tid decl) |-> Vptr (b, i) ** p'
    ) ->  
    ftype id decl = Some (Tptr tp1') ->
    nth_id n decl = Some id ->
    field_offset id decl = Some off -> 
    ( p ==> (Lv (ederef (efield (ederef (evar x)) id)) @ tp1' == lv)).
Proof.
  intros.
  apply H in H3.
  clear H.
  destruct s as [[]].
  destruct t as [[[[]]]].
  simpl in *;simpljoin.
  rewrite H16.
  rewrite H0.
  apply mapstoval_loadbytes in H17.
  destruct H17 as (bls&H17).
  destruct H17.
  apply map_join_emp'' in H13.
  subst x14.
  lets Hl:loadbytes_local H8 H.
  apply map_join_comm in H3.
  lets Hll: loadbytes_local H3 Hl.
  clear Hl.
  rewrite Int.unsigned_zero in Hll.
  assert ( loadbytes m (x19, BinNums.Z0) (typelen (Tptr (Tstruct tid decl))) =
           Some bls);auto.
  unfold load at 1;unfold loadm at 1.
  rewrite H7.
  rewrite H4.
  unfold getoff.
  simpl evaltype.
  rewrite H16.
  rewrite H2.
  apply mapstoval_load in H6.
  apply map_join_comm in H3.
  split.
  eapply load_local;eauto.
  rewrite Int.repr_unsigned.
  unfold addrval_to_addr.
  auto.
  simpl;auto.
  simpl;auto.
  simpl;auto.
Qed.

Lemma field_deref_asrt_impl_g: 
  forall p b i off tp1' lv decl  id tid x n p' perm,
    (
      p <==>
        PV (b, Int.add i off) @ Tptr tp1' |-> Vptr lv **
        A_notin_lenv x** GV x @ Tptr (Tstruct tid decl) |=> Vptr (b, i) @ perm ** p'
    ) ->  
    ftype id decl = Some (Tptr tp1') ->
    nth_id n decl = Some id ->
    field_offset id decl = Some off -> 
    ( p ==> (Lv (ederef (efield (ederef (evar x)) id)) @ tp1' == lv)).
Proof.
  intros.
  apply H in H3.
  clear H.

  destruct s as [[]].
  destruct t as [[[[]]]].
  simpl in *;simpljoin.
  apply EnvMod.nindom_get in H11.
  unfold get at 1;simpl.
  rewrite H11.
  rewrite H21.
  rewrite H0.
  apply mapstoval_loadbytes in H22.
  destruct H22 as (bls&H22).
  destruct H22.
  apply map_join_emp'' in H18;subst x20.
  lets Hl:loadbytes_local H13 H.
  apply map_join_comm in H3.
  apply map_join_emp'' in H8;subst x7.
  lets Hll: loadbytes_local H3 Hl.
  clear Hl.
  rewrite Int.unsigned_zero in Hll.
  assert ( loadbytes m (x25, BinNums.Z0) (typelen (Tptr (Tstruct tid decl))) =
           Some bls);auto.
  unfold load at 1;unfold loadm at 1.
  assert (get e0 x = None).
  unfolds;simpl;auto.
  rewrite H8.
  unfold load at 1;unfold loadm at 1.
  rewrite H7.
  unfold getoff.
  simpl evaltype.
  rewrite H4.
  rewrite H8.
  rewrite H21.
  rewrite H2.
  apply mapstoval_load in H6.
  apply map_join_comm in H3.
  split.
  eapply load_local;eauto.
  rewrite Int.repr_unsigned.
  unfold addrval_to_addr.
  auto.
  rewrite H0.
  auto.
  simpl;auto.
  simpl;auto.
Qed.



Lemma unsigned_zero: 
  forall i , Int.unsigned i = Int.unsigned Int.zero -> i = Int.zero.
Proof.
  intros.
  assert (Int.repr (Int.unsigned i) = Int.repr (Int.unsigned Int.zero)).
  rewrite H.
  auto.
  rewrite Int.repr_unsigned in H0.
  rewrite Int.repr_unsigned in H0.
  auto.
Qed.


Lemma arrayelem_asrt_impl: 
  forall n m p p' b i t e2 x te2, 
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    p <==>
      Alvarenv x (Tarray t n) (addrval_to_addr (b, i)) ** p' ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z.of_nat m)) ->
    p ==>
      (Lv (earrayelem (evar x) e2) @ t == (b,Int.add i (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))  (Int.repr (Z.of_nat m))))).
Proof.
  introv Ht.
  intros.
  destruct H with s.
  destruct H0 with s;auto.
  clear H H0.
  apply H2 in H1.
  clear H2 H3.
  destruct H5.
  destruct s as [[]].
  destruct t0 as [[[[]]]].
  simpl in *;simpljoin.
  rewrite H6.
  rewrite H4.
  rewrite <- Int.unsigned_zero in H13.
  apply unsigned_zero in H13.
  subst i.
  auto.
  rewrite H.
  simpl in *.
  rewrite Int.unsigned_zero.
  unfold Int.zero.
  split;auto.
  destruct Ht;subst;auto.
  destruct H1;subst;auto.
Qed.

Lemma arrayelem_asrt_impl_g: 
  forall n m p p' b i te2 t e2 x, 
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    p <==>
      (A_notin_lenv x ** Agvarenv x (Tarray t n) (addrval_to_addr (b, i))) ** p' ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z.of_nat m)) ->
    p ==>
      (Lv (earrayelem (evar x) e2) @ t == (b,Int.add i (Int.mul (Int.repr (Z.of_nat (typelen t)))  (Int.repr (BinInt.Z.of_nat m))))).
Proof.
  introv Ht.
  intros.
  destruct H with s.
  destruct H0 with s;auto.
  clear H H0.
  apply H2 in H1.
  clear H2 H3.
  destruct H5.
  destruct s as [[]].
  destruct t0 as [[[[]]]].
  simpl in *;simpljoin.
  apply EnvMod.nindom_get in H11.
  unfold get in *;simpl.
  simpl in H12.
  rewrite H11.
  rewrite H12.
  rewrite H4.
  rewrite <- Int.unsigned_zero in H20.
  apply unsigned_zero in H20.
  subst i.
  simpl.
  split;auto.
  rewrite H.
  destruct Ht;subst;auto.
  destruct H1;subst;auto.
Qed.

Lemma array_rm_update_eq: 
  forall s b i vl v vi n m t,  
    m < n -> 
    nth_val m vl = Some vi -> 
    s |= Aarray_rm (b,i) n t vl m -> 
    s |= Aarray_rm (b,i) n t (update_nth_val m vl v) m.
Proof.
  intros.
  generalize dependent s.
  generalize dependent b.
  generalize dependent i.
  generalize dependent vi.
  generalize dependent n.
  generalize dependent vl.
  generalize dependent v.
  induction m.
  intros.
  destruct vl;tryfalse.
  simpl in H0;inverts H0.
  simpl in *.
  auto.
  intros.
  destruct n;tryfalse.
  omega.
  destruct vl;tryfalse.
  simpl in H0.
  assert (m<n).
  omega.
  unfold Aarray_rm in H1;fold Aarray_rm in H1.
  lets IH:IHm H2 H0.
  unfold update_nth_val;fold update_nth_val.
  unfold Aarray_rm;fold Aarray_rm.
  sep_auto.
  apply IH.
  auto.
Qed.

Theorem assign_rule_array' : 
  forall Spec I r ri  t te2 p p' x e e2 n m l vl vl' v vi tp2 aop sc li ct,
    p <==>  Alvarenv x (Tarray t n) (addrval_to_addr l) ** Aarray l (Tarray t n) vl ** p' ->
    p ==> Rv e @ tp2 == v ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z_of_nat m)) ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    nth_val m vl = Some vi ->
    m<n ->
    assign_type_match t tp2 -> 
    update_nth_val m vl v = vl' ->
    (*p ==>  EX lg, p_local li ct lg ** Atrue ->*)
    Alvarenv x (Tarray t n) (addrval_to_addr l) ** Aarray l (Tarray t n) vl' ** p'  ==>  EX lg, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct  {{ p ** <|| aop ||> }} (sassign (earrayelem (evar x) e2) e)  
                                       {{(Alvarenv x (Tarray t n) (addrval_to_addr l) ** Aarray l (Tarray t n) vl' ** p' ** <|| aop ||>)}}.
Proof.
  intros.
  unfold Aarray in *.
  destruct l as (b&i).
  assert (Aarray' (b, i) n t vl <==> PV (b,Int.add i (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                                              (Int.repr (BinInt.Z.of_nat m)))) @ t |-> vi ** Aarray_rm (b,i) n t vl m).
  eapply array_asrt_eq;eauto.
  (*apply int_Z_lt';auto.*)
  lets Hrep:star_star_eq_rep H H8.
  assert (
      p ==>
        (Lv (earrayelem (evar x) e2) @ t == (b,Int.add i (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                                                  (Int.repr (BinInt.Z.of_nat m)))))).

  eapply arrayelem_asrt_impl with (b:=b) (i:=i) (te2:=te2);eauto.
  assert (p <==> 
            
            PV (b,
                Int.add i
                        (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                 (Int.repr (BinInt.Z.of_nat m)))) @ t |-> vi **
            Alvarenv x (Tarray t n) (addrval_to_addr (b, i)) **
            Aarray_rm (b, i) n t vl m ** p').

  eapply asrt_eq_trans;eauto.
  eapply star3_comm.
  clear Hrep.
  assert ({|Spec, sc, li, I, r, ri|}|-ct {{p **  <|| aop ||> }}
                                         sassign (earrayelem (evar x) e2) e
                                         {{PV (b,  Int.add i
                                                           (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                                                    (Int.repr (BinInt.Z.of_nat m)))) @ t |-> v **  (Alvarenv x (Tarray t n) (addrval_to_addr (b, i)) **
                                                                                                                             Aarray_rm (b, i) n t vl m **
                                                                                                                             p') ** <|| aop ||> }}).
  eapply assign_rule'';eauto.
  intros.
  apply H7.
  sep auto.
  erewrite array_asrt_eq with (v:=v) (m:=m);eauto.
  sep auto.
  eapply array_rm_update_eq;eauto.
  eapply update_nth;eauto.
  eapply forward_rule1.
  2:eauto.
  intros.
  sep auto.
  eapply array_asrt_eq;eauto.
  eapply update_nth;eauto.
  sep auto.
  eapply array_rm_update_eq;eauto.
Qed.

Theorem assign_rule_ptr_array' : 
  forall Spec I r ri  t te1 te2 p p' e e1 e2 n m l vl vl' v vi tp2 aop sc li ct,
    p ==> Rv e1 @ te1 == Vptr l ->
    p <==> Aarray l (Tarray t n) vl ** p' ->
    p ==> Rv e @ tp2 == v ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z_of_nat m)) ->
    te1 = Tarray t n \/ te1 = Tptr t ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    nth_val m vl = Some vi ->
    m<n ->
    assign_type_match t tp2 -> 
    update_nth_val m vl v = vl' ->
    (*p ==>  EX lg, p_local li ct lg ** Atrue ->*)
    Aarray l (Tarray t n) vl' ** p'  ==>  EX lg, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct  {{ p ** <|| aop ||> }} (sassign (earrayelem e1 e2) e)  
                                       {{( Aarray l (Tarray t n) vl' ** p' ** <|| aop ||>)}}.
Proof.
  intros.
  unfold Aarray in *.
  destruct l as (b&i).
  assert (Aarray' (b, i) n t vl <==> PV (b,Int.add i (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                                              (Int.repr (BinInt.Z.of_nat m)))) @ t |-> vi ** Aarray_rm (b,i) n t vl m).
  eapply array_asrt_eq;eauto.
  assert (p <==> PV (b,
                     Int.add i
                             (Int.mul (Int.repr (Z.of_nat (typelen t)))
                                      (Int.repr (Z.of_nat m)))) @ t |-> vi **
            Aarray_rm (b, i) n t vl m ** p') as Hrep.
  clear - H0 H10.

  intros;split;intros.
  apply H0 in H.
  sep auto.
  apply H10;auto.
  apply H0.
  sep auto.
  apply H10;auto.

  assert (
      p ==>
        (Lv (earrayelem e1 e2) @ t == (b,Int.add i (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                                            (Int.repr (BinInt.Z.of_nat m)))))).

  clear -H H2 H3 H4.
  intros.
  lets Hx: H H0.
  lets Hy: H2 H0.
  clear H H2 H0.
  simpl in *.
  simpljoin.
  rewrite H5, H2.
  destruct H3;subst te1;rewrite H;auto.
  destruct_s s.
  simpl in *.
  split;auto.
  rewrite H0.
  destruct H4.
  subst te2;auto.
  destruct H3;subst;auto.
  split;auto.
  rewrite H0.
  destruct_s s.
  simpl.
  destruct H4;subst;auto.
  destruct H3;subst;auto.

  assert ({|Spec, sc, li, I, r, ri|}|-ct {{p **  <|| aop ||> }}
                                         sassign (earrayelem e1 e2) e
                                         {{PV (b,  Int.add i
                                                           (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                                                    (Int.repr (BinInt.Z.of_nat m)))) @ t |-> v **  (Aarray_rm (b, i) n t vl m **
                                                                                                                              p') **  <|| aop ||> }}).
  eapply assign_rule'';eauto.
  intros.
  apply H9.
  sep auto.
  erewrite array_asrt_eq with (v:=v) (m:=m);eauto.
  sep_auto.
  eapply array_rm_update_eq;eauto.
  eapply update_nth;eauto.
  eapply forward_rule1.
  2:eauto.
  intros.
  sep auto.
  erewrite array_asrt_eq with (v:=v) (m:=m);eauto.
  sep_auto.
  eapply array_rm_update_eq;eauto.
  eapply update_nth;eauto.
Qed.


Theorem assign_rule_array_g' : 
  forall Spec I r ri  t p p' x e e2 n m l vl vl' v vi tp2 aop te2 sc li ct,
    p <==>  (A_notin_lenv x ** Agvarenv x (Tarray t n) (addrval_to_addr l)) ** Aarray l (Tarray t n) vl ** p' ->
    p ==> Rv e @ tp2 == v ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z_of_nat m)) ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    nth_val m vl = Some vi ->
    m<n->
    assign_type_match t tp2 -> 
    update_nth_val m vl v = vl' ->
    (*p ==>  EX lg, p_local li ct lg ** Atrue ->*)
    (A_notin_lenv x ** 
                  Agvarenv x (Tarray t n) (addrval_to_addr l)) **
                                                               Aarray l (Tarray t n) vl' ** p'  ==> 
                                                               EX lg, p_local li ct lg ** Atrue ->
{| Spec, sc, li, I, r, ri |} |-ct  {{ p ** <|| aop ||> }} (sassign (earrayelem (evar x) e2) e)  
                                                                                                                                                       {{((A_notin_lenv x ** Agvarenv x (Tarray t n) (addrval_to_addr l)) ** Aarray l (Tarray t n) vl' ** p' ** <|| aop ||>)}}.
Proof.
  intros.
  unfold Aarray in *.
  destruct l as (b&i).
  assert (Aarray' (b, i) n t vl <==> PV (b,Int.add i (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                                              (Int.repr (BinInt.Z.of_nat m)))) @ t |-> vi ** Aarray_rm (b,i) n t vl m).
  eapply array_asrt_eq;eauto.
  lets Hrep:star_star_eq_rep H H8.
  assert (
      p ==>
        (Lv (earrayelem (evar x) e2) @ t == (b,Int.add i (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                                                  (Int.repr (BinInt.Z.of_nat m)))))).
  
  eapply arrayelem_asrt_impl_g with (b:=b) (i:=i);eauto.
  assert (p <==> 
            
            PV (b,
                Int.add i
                        (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                 (Int.repr (BinInt.Z.of_nat m)))) @ t |-> vi **
            (A_notin_lenv x ** Agvarenv x (Tarray t n) (addrval_to_addr (b, i))) **
            Aarray_rm (b, i) n t vl m ** p').

  eapply asrt_eq_trans;eauto.
  eapply star3_comm.
  clear Hrep.
  assert ({|Spec, sc, li, I, r, ri|}|-ct {{p **  <|| aop ||> }}
                                         sassign (earrayelem (evar x) e2) e
                                         {{PV (b,  Int.add i
                                                           (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                                                    (Int.repr (BinInt.Z.of_nat m)))) @ t |-> v **  (A_notin_lenv x ** Agvarenv x (Tarray t n) (addrval_to_addr (b, i)) **
                                                                                                                                 Aarray_rm (b, i) n t vl m **
                                                                                                                                 p') ** <|| aop ||> }}).
  eapply assign_rule'';eauto.
  split;intros.
  apply H10 in H11;sep auto.
  apply H10;sep auto.
  intros.
  apply H7.
  sep auto.
  erewrite array_asrt_eq with (v:=v) (m:=m);eauto.
  sep_auto.
  eapply array_rm_update_eq;eauto.
  eapply update_nth;eauto.
  eapply forward_rule1.
  2:eauto.
  intros.
  sep auto.
  erewrite array_asrt_eq with (v:=v) (m:=m);eauto.
  sep_auto.
  eapply array_rm_update_eq;eauto.
  eapply update_nth;eauto.
Qed.


Theorem assign_rule_struct_aop: 
  forall Spec I r ri p p' x id e tid decl n l vl vl' v tp1 tp1' tp2 aop sc li ct perm,
    p <==>  LV x @ (Tptr tp1) |=> Vptr l @ perm ** Astruct l tp1 vl ** p' ->
    tp1 = Tstruct tid decl ->
    good_decllist decl = true ->
    id_nth id decl = Some n ->
    ftype id decl = Some tp1' ->
    (forall ids dl, tp1' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), tp1' <> Tarray t'0 n0) ->
    p ==>  Rv e @ tp2 == v ->
    assign_type_match tp1' tp2 ->
    n < length vl ->
    update_nth_val n vl v =  vl' ->
    (*p ==> EX lg : list logicvar, p_local li ct lg ** Atrue ->*)
    LV x @ (Tptr tp1) |=> Vptr l @ perm ** Astruct l tp1 vl' ** p' ==>
       EX lg : list logicvar, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p }} (sassign (efield (ederef (evar x)) id) e)  
                                      {{ <|| aop ||> ** LV x @ (Tptr tp1) |=> Vptr l @ perm ** Astruct l tp1 vl' ** p' }}.
Proof.
  introv HH.
  intros.
  assert (update_nth_val n vl v = vl' /\ exists vi, nth_val n vl = Some vi).
  apply up_val_op_ex;auto.
  unfold update_nth_val_op.
  assert (NPeano.Nat.ltb n (length vl) = true) as H100.
  unfold NPeano.Nat.ltb.
  apply NPeano.Nat.ltb_lt; omega.
  rewrite H100.
  rewrite H8; auto.
  destruct H10.
  destruct H11.
  eapply conseq_rule.
  3:eapply assign_rule_struct';eauto.
  intros.
  instantiate (1:= aop).
  sep auto.
  intros.
  sep auto.
  eauto.
  sep auto.
  Focus 2.
  intros.
  apply H9.
  sep auto.
  eapply id_nth_eq;eauto.
Qed.

Theorem assign_rule_struct_g_aop: 
  forall Spec I r ri  p p' ls x id e tid decl n l vl vl' v tp1 tp1' tp2 aop sc li ct perm,
    p <==> A_dom_lenv ls ** GV x @ (Tptr tp1) |=> Vptr l @ perm ** Astruct l tp1 vl ** p' ->
    var_notin_dom x ls = true ->
    tp1 = Tstruct tid decl ->
    good_decllist decl = true ->
    id_nth id decl = Some n ->
    ftype id decl = Some tp1' ->
    (forall ids dl, tp1' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), tp1' <> Tarray t'0 n0) ->
    p ==> Rv e @ tp2 == v ->
    assign_type_match tp1' tp2 ->
    n < length vl ->
    update_nth_val n vl v = vl'->
    (*p ==> EX lg : list logicvar, p_local li ct lg ** Atrue ->*)
    A_dom_lenv ls ** GV x @ (Tptr tp1) |=> Vptr l @ perm ** Astruct l tp1 vl' ** p' ==>
               EX lg : list logicvar, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p }} (sassign (efield (ederef (evar x)) id) e)  
                                      {{ <|| aop ||> ** A_dom_lenv ls ** GV x @ (Tptr tp1) |=> Vptr l @ perm ** Astruct l tp1 vl' ** p' }}.
Proof.
  introv HH.
  intros.
  assert (update_nth_val n vl v = vl' /\ exists vi, nth_val n vl = Some vi).
  apply up_val_op_ex;auto.
  unfold update_nth_val_op.
  assert (NPeano.Nat.ltb n (length vl) = true) as H100.
  unfold NPeano.Nat.ltb.
  apply NPeano.Nat.ltb_lt; omega.
  rewrite H100.
  rewrite H9; auto.
  destruct H11.
  destruct H12.
  apply backward_rule1 with
  (<|| aop ||> ** A_notin_lenv x ** GV x @ (Tptr tp1) |=> Vptr l @ perm ** Astruct l tp1 vl ** A_dom_lenv ls ** p'); intros.
  sep cancel 1 1.
  apply HH in H13.
  eapply dom_lenv_imp_notin_lenv; eauto.
  sep auto.
  eapply conseq_rule.
  3:eapply assign_rule_struct_g';eauto.
  instantiate (1:= aop).
  intros;sep auto.
  apply HH.
  sep auto.
  instantiate (1:=A_dom_lenv ls ** p').
  intros;sep auto.
  split;intros.
  apply HH in H13.
  sep normal.
  eapply dom_lenv_imp_notin_lenv;eauto.
  sep auto.
  apply HH.
  sep auto.
  eapply id_nth_eq;eauto.
  intros.
  apply H10.
  sep auto.
Qed.



Theorem assign_rule_struct_aop_typeneq: 
  forall Spec I r ri p p' x id e tid decl n l vl vl' v tp1 tp1' tp2 aop sc li ct perm tt tid' decl',
    p <==>  LV x @ (Tptr tt) |=> Vptr l @ perm ** Astruct l tp1 vl ** p' ->
    tp1 = Tstruct tid decl ->
    tt = Tstruct tid' decl' ->
    sub_decllist decl decl' = true ->
    good_decllist decl = true ->
    id_nth id decl = Some n ->
    ftype id decl = Some tp1' ->
    (forall ids dl, tp1' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), tp1' <> Tarray t'0 n0) ->
    p ==>  Rv e @ tp2 == v ->
    assign_type_match tp1' tp2 ->
    n < length vl ->
    update_nth_val n vl v =  vl' ->
    (*p ==> EX lg : list logicvar, p_local li ct lg ** Atrue ->*)
    LV x @ (Tptr tt) |=> Vptr l @ perm ** Astruct l tp1 vl' ** p' ==>
       EX lg : list logicvar, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p }} (sassign (efield (ederef (evar x)) id) e)  
                                      {{ <|| aop ||> ** LV x @ (Tptr tt) |=> Vptr l @ perm ** Astruct l tp1 vl' ** p' }}.
Proof.
  introv HH.
  intros.
  assert (update_nth_val n vl v = vl' /\ exists vi, nth_val n vl = Some vi).
  apply up_val_op_ex;auto.
  unfold update_nth_val_op.
  assert (NPeano.Nat.ltb n (length vl) = true) as H100.
  unfold NPeano.Nat.ltb.
  apply NPeano.Nat.ltb_lt; omega.
  rewrite H100.
  rewrite H10; auto.
  destruct H12.
  destruct H13.
  eapply conseq_rule.
  3:eapply assign_rule_struct_typeneq';eauto.
  intros.
  instantiate (1:= aop).
  sep auto.
  intros.
  sep auto.
  eauto.
  sep auto.
  Focus 2.
  intros.
  apply H11.
  sep auto.
  eapply id_nth_eq;eauto.
Qed.

Theorem assign_rule_struct_g_aop_typeneq: 
  forall Spec I r ri  p p' ls x id e tid decl n l vl vl' v tp1 tp1' tp2 aop sc li ct perm tt tid' decl',
    p <==> A_dom_lenv ls ** GV x @ (Tptr tt) |=> Vptr l @ perm ** Astruct l tp1 vl ** p' ->
    var_notin_dom x ls = true ->
    tp1 = Tstruct tid decl ->

    tt = Tstruct tid' decl' ->
    sub_decllist decl decl' = true ->
    
    good_decllist decl = true ->
    id_nth id decl = Some n ->
    ftype id decl = Some tp1' ->
    (forall ids dl, tp1' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), tp1' <> Tarray t'0 n0) ->
    p ==> Rv e @ tp2 == v ->
    assign_type_match tp1' tp2 ->
    n < length vl ->
    update_nth_val n vl v = vl'->
    (*p ==> EX lg : list logicvar, p_local li ct lg ** Atrue ->*)
    A_dom_lenv ls ** GV x @ (Tptr tt) |=> Vptr l @ perm ** Astruct l tp1 vl' ** p' ==>
               EX lg : list logicvar, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p }} (sassign (efield (ederef (evar x)) id) e)  
                                      {{ <|| aop ||> ** A_dom_lenv ls ** GV x @ (Tptr tt) |=> Vptr l @ perm ** Astruct l tp1 vl' ** p' }}.
Proof.
  introv HH.
  intros.
  assert (update_nth_val n vl v = vl' /\ exists vi, nth_val n vl = Some vi).
  apply up_val_op_ex;auto.
  unfold update_nth_val_op.
  assert (NPeano.Nat.ltb n (length vl) = true) as H100.
  unfold NPeano.Nat.ltb.
  apply NPeano.Nat.ltb_lt; omega.
  rewrite H100.
  rewrite H11; auto.
  destruct H13.
  destruct H14.
  apply backward_rule1 with
  (<|| aop ||> ** A_notin_lenv x ** GV x @ (Tptr tt) |=> Vptr l @ perm ** Astruct l tp1 vl ** A_dom_lenv ls ** p'); intros.
  sep cancel 1 1.
  apply HH in H15.
  eapply dom_lenv_imp_notin_lenv; eauto.
  sep auto.
  eapply conseq_rule.
  3:eapply assign_rule_struct_g_typeneq';eauto.
  instantiate (1:= aop).
  intros;sep auto.
  apply HH.
  sep auto.
  instantiate (1:=A_dom_lenv ls ** p').
  intros;sep auto.
  split;intros.
  apply HH in H15.
  sep normal.
  eapply dom_lenv_imp_notin_lenv;eauto.
  sep auto.
  apply HH.
  sep auto.
  eapply id_nth_eq;eauto.
  intros.
  apply H12.
  sep auto.
Qed.

Theorem assign_rule_array : 
  forall Spec I r ri t p p' x e e2 n m l vl vl' v tp2 aop te2 sc li ct,
    p <==>  Alvarenv x (Tarray t n) (addrval_to_addr l) ** Aarray l (Tarray t n) vl ** p' ->
    p ==> Rv e @ tp2 == v ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z_of_nat m)) ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    m<n->
    assign_type_match t tp2 -> 
    update_nth_val_op m vl v = Some vl' ->
    (*p ==>  EX lg, p_local li ct lg ** Atrue ->*)
    Alvarenv x (Tarray t n) (addrval_to_addr l) ** Aarray l (Tarray t n) vl' ** p'  ==>  EX lg, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ p ** <|| aop ||> }} (sassign (earrayelem (evar x) e2) e)  
                                      {{(Alvarenv x (Tarray t n) (addrval_to_addr l) ** Aarray l (Tarray t n) vl' ** p' ** <|| aop ||>)}}.
Proof.
  intros.
  assert (update_nth_val m vl v = vl' /\ exists vi, nth_val m vl = Some vi).
  apply up_val_op_ex;auto.
  destruct H7.
  destruct H8.
  eapply assign_rule_array';eauto.
Qed.

Theorem assign_rule_array_aop' : 
  forall Spec I r ri t p p' x e e2 n m vl vl' v tp2 aop te2 sc li ct,
    p <==>  LAarray x (Tarray t n) vl ** p' ->
    p ==> Rv e @ tp2 == v ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z_of_nat m)) ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    m < n ->
    assign_type_match t tp2 -> 
    update_nth_val_op m vl v = Some vl' ->
    (*p ==>  EX lg, p_local li ct lg ** Atrue ->*)
    LAarray x (Tarray t n) vl' ** p'  ==>  EX lg, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p}}
                                      (sassign (earrayelem (evar x) e2) e)  
                                      {{ <|| aop ||> ** LAarray x (Tarray t n) vl' ** p' }}.
Proof.
  intros.
  apply backward_rule1 with ( LAarray x (Tarray t n) vl ** p' ** <|| aop ||> ).
  intros.
  sep cancel 1 3.
  apply H in H7; sep auto.
  unfold LAarray.
  hoare normal pre; hoare normal post; eapply ex_intro_rule'; intro.
  hoare lifts (1::2::4::nil)%nat post.
  apply backward_rule1 with ( (L& x @ Tarray t n == v' **
                                                       Aarray v' (Tarray t n) vl ** p') ** <||aop||> ).
  sep auto.
  eapply assign_rule_array; eauto.
  unfold Alvarenv'; split; eauto.
  intros.
  apply H0.
  apply H.
  unfold LAarray; sep auto.
  intros.
  apply H1.
  apply H.
  unfold LAarray; sep auto.
  intros.
  apply H6.
  unfold LAarray.
  unfold Alvarenv'.
  sep auto.
Qed.

Lemma update_nth_val_len_eq: 
  forall vl v x, length (update_nth_val x vl v) = length vl.
Proof.
  induction vl;  intros.
  simpl;auto.
  simpl.
  destruct x.
  simpl;auto.
  simpl.
  assert(length (update_nth_val x vl v)=length vl).
  auto.
  omega.
Qed.

Lemma len_lt_update_get_eq:
  forall x vl v, (Int.unsigned x < Z.of_nat (length vl))%Z ->
                 nth_val' (Z.to_nat (Int.unsigned x)) (update_nth_val (Z.to_nat (Int.unsigned x)) vl v) = v.
Proof.
  intros.
  assert (Z.to_nat (Int.unsigned x) < (Z.to_nat (Z.of_nat (length vl)))).
  eapply ge0_z_nat_le;eauto.
  lets H1000:Int.unsigned_range x.
  omega.
  rewrite Nat2Z.id.
  auto.
  clear H.
  rewrite Nat2Z.id in H0.
  remember (Z.to_nat (Int.unsigned x)) as X.
  clear -H0.
  gen vl X v.
  induction vl;intros.
  simpl in H0.
  omega.
  simpl.
  destruct X.
  simpl.
  auto.
  simpl.
  apply IHvl.
  simpl in H0.
  omega.
Qed.

Theorem assign_rule_ptr_array : 
  forall Spec I r ri t p p' e e1 e2 n m l vl vl' v tp2 aop te1 te2 sc li ct,
    p ==> Rv e1 @ te1 == Vptr l ->
    p <==> Aarray l (Tarray t n) vl ** p' ->
    p ==> Rv e @ tp2 == v ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z_of_nat m)) ->
    te1 = Tarray t n \/ te1 = Tptr t ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    m<n->
    assign_type_match t tp2 -> 
    update_nth_val_op m vl v = Some vl' ->
    Aarray l (Tarray t n) vl' ** p'  ==>  EX lg, p_local li ct lg ** Atrue ->
                                                 {| Spec, sc, li, I, r, ri |} |-ct {{ p ** <|| aop ||> }} (sassign (earrayelem e1 e2) e)  
                                                                                                 {{ Aarray l (Tarray t n) vl' ** p' ** <|| aop ||>}}.
Proof.
  intros.
  assert (update_nth_val m vl v = vl' /\ exists vi, nth_val m vl = Some vi).
  apply up_val_op_ex;auto.
  destruct H9.
  destruct H10.
  eapply assign_rule_ptr_array';eauto.
Qed.


Theorem assign_rule_ptr_array_aop : 
  forall Spec I r ri  t te1 te2 p p' e e1 e2 n m l vl v tp2 aop sc li ct,
    p ==> Rv e1 @ te1 == Vptr l ->
    p <==> Aarray l (Tarray t n) vl ** p' ->
    p ==> Rv e @ tp2 == v ->
    p ==> Rv e2 @ te2 == Vint32 m ->
    te1 = Tarray t n \/ te1 = Tptr t ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    ((Int.unsigned m) < Z.of_nat n)%Z ->
    assign_type_match t tp2 -> 
    (Int.unsigned m < Z.of_nat (length vl))%Z ->
    Aarray l (Tarray t n) (update_nth_val (Z.to_nat (Int.unsigned m)) vl v) ** p'  ==>  EX lg, p_local li ct lg ** Atrue ->
                                                                                               {| Spec, sc, li, I, r, ri |} |-ct  {{ <|| aop ||> ** p}} (sassign (earrayelem e1 e2) e)  
                                                                                                                                  {{( <|| aop ||> ** Aarray l (Tarray t n) (update_nth_val (Z.to_nat (Int.unsigned m)) vl v) ** p')}}.
Proof.
  intros.
  apply backward_rule1 with (p ** <|| aop ||>).
  intros.
  sep auto.
  apply forward_rule1 with (Aarray l (Tarray t n) (update_nth_val (Z.to_nat (Int.unsigned m)) vl v) ** p' ** <||aop||>).
  intros.
  sep auto.
  cut (exists i, m = Int.repr (BinInt.Z_of_nat i) /\ (0 <= Z.of_nat i <= Int.max_unsigned)%Z).
  intros.
  simpljoin.

  eapply  assign_rule_ptr_array;eauto.
  rewrite Int.unsigned_repr in H5; auto.

  apply Nat2Z.inj_lt; auto.
  unfold update_nth_val_op.
  rewrite Int.unsigned_repr in H7; auto.
  apply Nat2Z.inj_lt in H7.
  apply NPeano.Nat.ltb_lt in H7.
  rewrite H7.
  rewrite Int.unsigned_repr; auto.
  rewrite Nat2Z.id; auto.
  destruct m.
  exists (Z.to_nat intval).
  rewrite Z2Nat.id.
  2 : omega.
  split.
  2 : unfold Int.max_unsigned; omega.
  rewrite <- Int.repr_unsigned at 1.
  simpl; auto.
Qed.

Theorem assign_rule_array_aop : 
  forall Spec I r ri t p p' x e e2 n m vl v tp2 aop te2 sc li ct,
    p <==>  LAarray x (Tarray t n) vl ** p' ->
    p ==> Rv e @ tp2 == v ->
    p ==> Rv e2 @ te2 == Vint32 m ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    ((Int.unsigned m) < Z.of_nat n)%Z ->
    assign_type_match t tp2 ->
    (Int.unsigned m < Z.of_nat (length vl))%Z ->
    p ==>  EX lg, p_local li ct lg ** Atrue ->
                  LAarray x (Tarray t n) (update_nth_val (Z.to_nat (Int.unsigned m)) vl v) ** p' ==>  EX lg, p_local li ct lg ** Atrue ->
                                                                                                             {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p}}
                                                                                                                                               (sassign (earrayelem (evar x) e2) e)  
                                                                                                                                               {{ <|| aop ||> ** LAarray x (Tarray t n) (update_nth_val (Z.to_nat (Int.unsigned m)) vl v) ** p' }}.
Proof.
  intros.
  cut (exists i, m = Int.repr (BinInt.Z_of_nat i) /\ (0 <= Z.of_nat i <= Int.max_unsigned)%Z).
  intros.
  simpljoin.
  eapply assign_rule_array_aop'; eauto.
  rewrite Int.unsigned_repr in H3; auto.
  apply Nat2Z.inj_lt; auto.
  unfold update_nth_val_op.
  rewrite Int.unsigned_repr in H5; auto.
  apply Nat2Z.inj_lt in H5.
  apply NPeano.Nat.ltb_lt in H5.
  rewrite H5.
  rewrite Int.unsigned_repr; auto.
  rewrite Nat2Z.id; auto.
  destruct m.
  exists (Z.to_nat intval).
  rewrite Z2Nat.id.
  2 : omega.
  split.
  2 : unfold Int.max_unsigned; omega.
  rewrite <- Int.repr_unsigned at 1.
  simpl; auto.
Qed.

Theorem assign_rule_deref_array_elem_aop' : 
  forall Spec I r ri t n te p p' x e e1 b i i0 vl v aop sc li ct,
    p <==>  Aarray (b,i0) (Tarray t n) vl ** p' ->
    p ==> Rv e1 @ (Tptr t) == Vptr(b,i) ->
    p ==> Rv e @ te == v ->
    Int.sub i i0 = Int.mul x (Int.repr (Z_of_nat (typelen t )))->
    (0 <= Int.unsigned i - Int.unsigned i0 <= 4294967295)%Z  ->
    (Z.of_nat n < 4294967295)%Z -> 
    (Int.unsigned x < Z.of_nat n)%Z ->
    (Int.unsigned x < Z.of_nat (length vl))%Z ->
    assign_type_match t te ->
    (*p ==>  EX lg, p_local li ct lg ** Atrue ->*)
    Aarray (b,i0) (Tarray t n) (update_nth_val (Z.to_nat (Int.unsigned x)) vl v) ** p' ==>  EX lg, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p}}
                                      (sassign (ederef e1) e)  
                                      {{ <|| aop ||> ** Aarray (b,i0) (Tarray t n) (update_nth_val (Z.to_nat (Int.unsigned x)) vl v) ** p' }}.
Proof.
  intros.
  unfold Aarray in *.
  assert (forall s,s|=Aarray' (b, i0) n t vl -> s|= PV (b,i) @ t |-> (nth_val' (Z.to_nat (Int.unsigned x)) vl) ** Aarray_rm (b,i0) n t vl (Z.to_nat (Int.unsigned x))).
  intros.
  
  eapply array_asrt_eq with  (v:=nth_val' (Z.to_nat (Int.unsigned x)) vl) (m:=((Z.to_nat (Int.unsigned x)))) in H9;eauto.
  2:eapply ge0_z_nat_le;eauto.
  2:lets H1000:Int.unsigned_range x;omega.
  Focus 2.
  rewrite <- Zabs2Nat.abs_nat_nonneg at 1.
  eapply nth_val_imp_nth_val'_1;eauto.
  lets H1000:Int.unsigned_range x.
  omega.
  sep auto.
  rewrite Z2Nat.id in H9.
  2:lets H100:Int.unsigned_range x;omega.
  assert (i=Int.add i0
                    (Int.mul (Int.repr (Z.of_nat (typelen t)))
                             (Int.repr (Int.unsigned x)))).
  eapply sub_mul_eq_add_mul;eauto.
  subst i.
  auto.
  assert (forall s, s|= PV (b,i) @ t |-> (nth_val' (Z.to_nat (Int.unsigned x)) vl) ** Aarray_rm (b,i0) n t vl (Z.to_nat (Int.unsigned x)) -> s|=Aarray' (b, i0) n t vl).
  intros.
  apply array_asrt_eq with  (v:=nth_val' (Z.to_nat (Int.unsigned x)) vl) (m:=((Z.to_nat (Int.unsigned x))));eauto.
  eapply ge0_z_nat_le;eauto.
  lets H1000:Int.unsigned_range x;omega.
  rewrite <- Zabs2Nat.abs_nat_nonneg at 1.
  eapply nth_val_imp_nth_val'_1;eauto.
  lets H1000:Int.unsigned_range x.
  omega.
  sep auto.
  rewrite Z2Nat.id.
  2:lets H100:Int.unsigned_range x;omega.
  assert (i=Int.add i0
                    (Int.mul (Int.repr (Z.of_nat (typelen t)))
                             (Int.repr (Int.unsigned x)))).
  eapply sub_mul_eq_add_mul;eauto.
  subst i.
  auto.
  assert (p==>PV (b, i) @ t |-> nth_val' (Z.to_nat (Int.unsigned x)) vl **
           Aarray_rm (b, i0) n t vl (Z.to_nat (Int.unsigned x))**p').
  clear -H H9.
  intros.
  apply H in H0.
  sep auto.
  assert (PV (b, i) @ t |-> nth_val' (Z.to_nat (Int.unsigned x)) vl **
             Aarray_rm (b, i0) n t vl (Z.to_nat (Int.unsigned x))**p' ==> p).
  clear -H H10.
  intros.
  apply H.
  sep auto.
  eapply backward_rule1 with ( <|| aop ||>  **  PV (b, i) @ t |-> nth_val' (Z.to_nat (Int.unsigned x)) vl **
                                   Aarray_rm (b, i0) n t vl (Z.to_nat (Int.unsigned x)) ** p').
  sep auto.
  eapply forward_rule1 with (<|| aop ||>  **  PV (b, i) @ t |-> v **
                                 Aarray_rm (b, i0) n t vl (Z.to_nat (Int.unsigned x)) ** p').
  Focus 2.
  eapply assign_rule';eauto.
  intros.
  split.
  assert (s |=  Rv e1 @ Tptr t == Vptr (b, i)).
  apply H0.
  apply H12;auto.
  clear -H14.
  destruct_s s.
  simpl in *;simpljoin;auto.
  rewrite H0.
  auto.
  auto.
  intros.
  apply H8.
  sep auto.

  apply array_asrt_eq with (v:=nth_val' (Z.to_nat (Int.unsigned x)) ( (update_nth_val (Z.to_nat (Int.unsigned x)) vl v))) (m:=((Z.to_nat (Int.unsigned x))));eauto.
  eapply ge0_z_nat_le;eauto.
  lets H1000:Int.unsigned_range x;omega.
  rewrite <- Zabs2Nat.abs_nat_nonneg at 1.
  eapply nth_val_imp_nth_val'_1;eauto.

  rewrite update_nth_val_len_eq.
  auto.
  lets H1000:Int.unsigned_range x.
  omega.
  rewrite Z2Nat.id.
  2:lets H100:Int.unsigned_range x;omega.
  assert (i=Int.add i0
                    (Int.mul (Int.repr (Z.of_nat (typelen t)))
                             (Int.repr (Int.unsigned x)))).
  eapply sub_mul_eq_add_mul;eauto.
  rewrite <- H14.
  rewrite len_lt_update_get_eq;auto.
  sep auto.
  eapply array_rm_update_eq;eauto.
  eapply ge0_z_nat_le;eauto.
  lets H1000:Int.unsigned_range x;omega.
  rewrite <- Zabs2Nat.abs_nat_nonneg at 1.
  eapply nth_val_imp_nth_val'_1;eauto.
  lets H1000:Int.unsigned_range x.
  omega.

  intros.
  sep auto.
  apply array_asrt_eq with (v:=nth_val' (Z.to_nat (Int.unsigned x)) ( (update_nth_val (Z.to_nat (Int.unsigned x)) vl v))) (m:=((Z.to_nat (Int.unsigned x))));eauto.
  eapply ge0_z_nat_le;eauto.
  lets H1000:Int.unsigned_range x;omega.
  rewrite <- Zabs2Nat.abs_nat_nonneg at 1.
  eapply nth_val_imp_nth_val'_1;eauto.
  rewrite update_nth_val_len_eq.
  auto.
  lets H1000:Int.unsigned_range x.
  omega.
  rewrite Z2Nat.id.
  2:lets H100:Int.unsigned_range x;omega.
  assert (i=Int.add i0
                    (Int.mul (Int.repr (Z.of_nat (typelen t)))
                             (Int.repr (Int.unsigned x)))).
  eapply sub_mul_eq_add_mul;eauto.
  rewrite <- H14.
  rewrite len_lt_update_get_eq;auto.
  sep auto.
  eapply array_rm_update_eq;eauto.
  eapply ge0_z_nat_le;eauto.
  lets H1000:Int.unsigned_range x;omega.
  rewrite <- Zabs2Nat.abs_nat_nonneg at 1.
  eapply nth_val_imp_nth_val'_1;eauto.
  lets H1000:Int.unsigned_range x.
  omega.  
Qed.

Theorem assign_rule_deref_array_elem_aop'' : 
  forall Spec I r ri t t' n te p p' x e e1 l l' vl vl' v aop sc li ct,
    p <==>  Aarray l' t' vl ** p' ->
    t' = Tarray t n ->
    (Z.of_nat n < 4294967295)%Z ->
    p ==> Rv e1 @ (Tptr t) == Vptr l ->
    typelen t <> 0 ->
    (Z.of_nat (typelen t) < 4294967295)%Z ->
    fst l = fst l' ->
    Int.divu (Int.sub (snd l) (snd l')) (Int.repr (Z.of_nat (typelen t))) = x ->
    Int.modu (Int.sub (snd l) (snd l')) (Int.repr (Z.of_nat (typelen t))) = Int.zero ->
    p ==> Rv e @ te == v ->
    (Int.unsigned (snd l') <= Int.unsigned (snd l))%Z ->
    (Int.unsigned x < Z.of_nat n)%Z ->
    (forall s, s |= p -> (Int.unsigned x < Z.of_nat (length vl))%Z) ->
    assign_type_match t te ->
    update_nth_val (Z.to_nat (Int.unsigned x)) vl v = vl' ->
    (* p ==>  EX lg, p_local li ct lg ** Atrue ->*)
    Aarray l' t' vl' ** p' ==>  EX lg, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p}}
                                      (sassign (ederef e1) e)  
                                      {{ <|| aop ||> ** Aarray l' t' vl' ** p' }}.
Proof.
  intros.
  eapply backward_rule1 with ([| (Int.unsigned x < Z.of_nat (length vl))%Z |] ** <|| aop ||> ** p).
  sep auto.
  eapply H11; eauto.
  apply pure_split_rule'; intros.
  clear H11; rename H15 into H11.
  destruct l, l'.
  simpl fst in *; simpl snd in *; subst.
  eapply assign_rule_deref_array_elem_aop'; eauto.
  Focus 2.
  split.
  apply Zle_minus_le_0; auto.
  apply unsigned_minus_le_max.
  remember (Int.repr (Z.of_nat (typelen t))) as x100.
  assert (x100 <> Int.zero) as H100.
  subst x100.
  clear - H3 H4.
  intro; apply H3.
  assert (Int.unsigned (Int.repr (Z.of_nat (typelen t))) = Int.unsigned Int.zero) as H100.
  rewrite H; auto.
  rewrite Int.unsigned_zero in H100.
  rewrite Int.unsigned_repr in H100.
  assert (Z.to_nat (Z.of_nat (typelen t)) = Z.to_nat 0%Z) as H200.
  rewrite H100; auto.
  rewrite Nat2Z.id in H200.
  simpl; auto.
  rewrite max_unsigned_val; omega.
  remember (Int.sub i i0) as x200.
  clear Heqx100 Heqx200.
  lets H200 : Int.modu_divu x200 x100 H100.
  rewrite H7 in H200.
  apply sub_zero_eq; auto.
Qed.

Theorem assign_rule_deref_array_elem_aop''' : 
  forall Spec I r ri t t' n te p p' x e e1 l l' vl vl' v aop sc li ct,
    p <==>  Aarray l' t' vl ** p' ->
    t' = Tarray t n ->
    (Z.of_nat n < 4294967295)%Z ->
    p ==> Rv e1 @ (Tptr t) == Vptr l ->
    typelen t <> 0 ->
    (Z.of_nat (typelen t) < 4294967295)%Z ->
    fst l = fst l' ->
    (Int.unsigned (snd l') <= Int.unsigned (snd l))%Z ->
    ((Int.unsigned (snd l) - Int.unsigned (snd l')) / (Z_of_nat (typelen t)) = x)%Z ->
    ((Int.unsigned (snd l) - Int.unsigned (snd l')) mod (Z_of_nat (typelen t)) = 0)%Z ->
    p ==> Rv e @ te == v ->
    (x < Z.of_nat n)%Z ->
    (forall s, s |= p -> (x < Z.of_nat (length vl))%Z) ->
    assign_type_match t te ->
    update_nth_val (Z.to_nat x) vl v = vl' ->
    (* p ==>  EX lg, p_local li ct lg ** Atrue ->*)
    Aarray l' t' vl' ** p' ==>  EX lg, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p}}
                                      (sassign (ederef e1) e)  
                                      {{ <|| aop ||> ** Aarray l' t' vl' ** p' }}.
Proof.
  intros.
  cut (x = Int.unsigned (Int.divu (Int.sub (snd l) (snd l')) (Int.repr (Z.of_nat (typelen t))))).
  intro H100.
  eapply assign_rule_deref_array_elem_aop''; eauto.
  apply Int_modu_to_Z_mod; auto || omega.
  rewrite <- H100; auto.
  rewrite <- H100; auto.
  rewrite <- H100; auto.
  symmetry; apply Int_div_to_Z_div; auto.
  remember (typelen t) as len.
  clear - H3.
  omega.
Qed.

Theorem assign_rule_deref_array_elem_aop : 
  forall Spec I r ri t t' n te p p' x e e1 b i i' vl vl' v aop sc li ct,
    p ==> Rv e1 @ (Tptr t) == Vptr (b,i) ->
    p <==>  Aarray (b,i') t' vl ** p' ->
    t' = Tarray t n ->
    (Z.of_nat n < 4294967295)%Z ->    
    typelen t <> 0 ->
    (Z.of_nat (typelen t) < 4294967295)%Z ->
    (Int.unsigned i' <= Int.unsigned i)%Z ->
    ((Int.unsigned i - Int.unsigned i') / (Z_of_nat (typelen t)) = x)%Z ->
    (Z_of_nat (typelen t) * x = Int.unsigned i - Int.unsigned i')%Z ->
    p ==> Rv e @ te == v ->
    (x < Z.of_nat n)%Z ->
    (forall s, s |= p -> (x < Z.of_nat (length vl))%Z) ->
    assign_type_match t te ->
    update_nth_val (Z.to_nat x) vl v = vl' ->
    (*p ==>  EX lg, p_local li ct lg ** Atrue ->*)
    Aarray (b,i') t' vl' ** p' ==>  EX lg, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p}}
                                      (sassign (ederef e1) e)  
                                      {{ <|| aop ||> ** Aarray (b,i') t' vl' ** p' }}.
Proof.
  intros.
  eapply assign_rule_deref_array_elem_aop'''; eauto.
  simpl snd; auto.
  apply Z_div_exact_full_1; subst; auto.
Qed.

Theorem assign_rule_array_g : 
  forall Spec I r ri t p p' x e e2 n m l vl vl' v tp2 aop te2 sc li ct,
    p <==>  (A_notin_lenv x ** Agvarenv x (Tarray t n) (addrval_to_addr l)) ** Aarray l (Tarray t n) vl ** p' ->
    p ==> Rv e @ tp2 == v ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z_of_nat m)) ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    m<n->
    assign_type_match t tp2 -> 
    update_nth_val_op m vl v = Some vl' ->
    (*p ==>  EX lg, p_local li ct lg ** Atrue ->*)
    (A_notin_lenv x ** Agvarenv x (Tarray t n) (addrval_to_addr l)) ** Aarray l (Tarray t n) vl' ** p' ==>  EX lg, p_local li ct lg ** Atrue ->
                                                                                                                   {| Spec, sc, li, I, r, ri |} |-ct  {{ p ** <|| aop ||> }} (sassign (earrayelem (evar x) e2) e)  
                                                                                                                                                      {{((A_notin_lenv x ** Agvarenv x (Tarray t n) (addrval_to_addr l)) ** Aarray l (Tarray t n) vl' ** p' ** <|| aop ||>)}}.
Proof.
  intros.
  assert (update_nth_val m vl v = vl' /\ exists vi, nth_val m vl = Some vi).
  apply up_val_op_ex;auto.
  destruct H7.
  destruct H8.
  eapply assign_rule_array_g';eauto.
Qed.

Theorem assign_rule_array_g_aop' : 
  forall Spec I r ri t p p' ls x e e2 n m vl vl' v tp2 aop te2 sc li ct,
    p <==>  A_dom_lenv ls ** GAarray x (Tarray t n) vl ** p' ->
    var_notin_dom x ls = true ->
    p ==> Rv e @ tp2 == v ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z_of_nat m)) ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    m < n->
    assign_type_match t tp2 -> 
    update_nth_val_op m vl v = Some vl' ->
    (*p ==>  EX lg, p_local li ct lg ** Atrue ->*)
    A_dom_lenv ls ** GAarray x (Tarray t n) vl' ** p' ==>  EX lg, p_local li ct lg ** Atrue ->
    {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p }} (sassign (earrayelem (evar x) e2) e)  
                                      {{ <|| aop ||> ** A_dom_lenv ls ** GAarray x (Tarray t n) vl' ** p' }}.
Proof.
  intros.
  apply backward_rule1 with ( (A_dom_lenv ls ** GAarray x (Tarray t n) vl ** p' ** A_notin_lenv x) ** <|| aop ||> ).
  intros.
  sep normal.
  sep cancel 1 5.
  apply H in H8.
  sep lift 4.
  apply dom_lenv_imp_notin_lenv with ls; auto.
  sep auto.
  apply forward_rule1 with ( A_dom_lenv ls ** GAarray x (Tarray t n) vl' ** p' ** A_notin_lenv x ** <|| aop ||> ).
  sep auto.
  unfold GAarray.
  hoare normal pre; hoare normal post; apply ex_intro_rule'; intro.
  unfold Agvarenv'.
  hoare lifts (3::6::nil)%nat%list pre.
  hoare lifts (3::6::nil)%nat%list post.
  apply forward_rule1 with (
    (A_notin_lenv x **
                  Agvarenv x (Tarray t n) (addrval_to_addr v')) **
                                                                Aarray v' (Tarray t n) vl' ** (A_dom_lenv ls ** p') ** <|| aop ||> ).
  sep auto.
  apply backward_rule1 with ( (A_dom_lenv ls**
                                          Agvarenv x (Tarray t n) (addrval_to_addr v') **
                                          Aarray v' (Tarray t n) vl ** p' ** A_notin_lenv x)  **
                                                                                              <|| aop ||> ).
  sep auto.
  eapply assign_rule_array_g; eauto.
  split; sep auto.
  intros; apply H1.
  apply H; unfold GAarray, Agvarenv'; sep auto.
  intros; apply H2.
  apply H; unfold GAarray, Agvarenv'; sep auto.
  intros.
  apply H7.
  unfold GAarray, Agvarenv';sep auto.
Qed.

Theorem assign_rule_array_g_aop : 
  forall Spec I r ri t p p' ls x e e2 n m vl v tp2 aop te2 sc li ct ,
    p <==>  A_dom_lenv ls ** GAarray x (Tarray t n) vl ** p' ->
    var_notin_dom x ls = true ->
    p ==> Rv e @ tp2 == v ->
    p ==> Rv e2 @ te2 == Vint32 m ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    (Int.unsigned m < Z.of_nat n)%Z ->
    assign_type_match t tp2 ->
    (Int.unsigned m < Z.of_nat (length vl))%Z ->
    (*p ==>  EX lg, p_local li ct lg ** Atrue ->*)
    A_dom_lenv ls ** GAarray x (Tarray t n) (update_nth_val (Z.to_nat (Int.unsigned m)) vl v) ** p' ==>  EX lg, p_local li ct lg ** Atrue ->
                                                                                                                  {| Spec, sc, li, I, r, ri |} |-ct  {{ <|| aop ||> ** p }} (sassign (earrayelem (evar x) e2) e)  
                                                                                                                                                     {{ <|| aop ||> ** A_dom_lenv ls ** GAarray x (Tarray t n) (update_nth_val (Z.to_nat (Int.unsigned m)) vl v) ** p' }}.
Proof.
  intros.
  cut (exists i, m = Int.repr (BinInt.Z_of_nat i) /\ (0 <= Z.of_nat i <= Int.max_unsigned)%Z).
  intros.
  simpljoin.
  eapply assign_rule_array_g_aop'; eauto.
  rewrite Int.unsigned_repr in H4; auto.
  apply Nat2Z.inj_lt; auto.
  unfold update_nth_val_op.
  rewrite Int.unsigned_repr in H6; auto.
  apply Nat2Z.inj_lt in H6.
  apply NPeano.Nat.ltb_lt in H6.
  rewrite H6.
  rewrite Int.unsigned_repr; auto.
  rewrite Nat2Z.id; auto.
  destruct m.
  exists (Z.to_nat intval).
  rewrite Z2Nat.id.
  2 : omega.
  split.
  2 : unfold Int.max_unsigned; omega.
  rewrite <- Int.repr_unsigned at 1.
  simpl; auto.
Qed.


(* tactics hoare_assign *)

Ltac find_aop' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_aop' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_aop' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | Aop ?l => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_aop Hp :=
  let x := find_aop' Hp in
  eval compute in x.

Ltac li_sepauto li:= 
  sep auto.

Ltac hoare_assign_var :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {| _, _, ?li, _, _ ,_ |} |-?ct  {{ ?P }} (sassign (evar ?x) _) {{ _ }} =>
      match find_lvarmapsto P x with
        | some ?m =>
          match find_aop P with
            | none _ => fail 1
            | some ?n =>
              hoare lifts (n::m::nil)%list pre;
                eapply assign_rule_lvar;
                [ intro s; split; intro H; exact H
                | symbolic execution
                | apply assign_type_match_true; simpl; auto | li_sepauto li]
          end
        | none _ =>
          match find_dom_lenv P with
            | (none _, _) => fail 2
            | (some ?m, Some ?ls) =>
              let ret1 := constr:(var_notin_dom x ls) in
              let ret2 := (eval compute in ret1) in
              match ret2 with
                | true =>
                  match find_aop P with
                    | none _ => fail 1
                    | some ?n =>
                      match find_gvarmapsto P x with
                        | none _ => fail 3
                        | some ?o =>
                          hoare lifts (n::m::o::nil)%list pre;
                            eapply assign_rule_gvar;
                            [ intro s; split; intro H; exact H
                            | simpl; auto
                            | symbolic execution
                            | apply assign_type_match_true; simpl; auto  | li_sepauto li ]
                      end
                  end
                | false => fail
              end
          end
      end
  end.

Ltac hoare_assign_struct :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct  {{ ?P }} (sassign (efield (ederef (evar ?x)) _) _) {{ _ }} =>
      match find_lvarmapsto P x with
        | some ?m =>
          match find_aop P with
            | none _ => fail 1
            | some ?n =>
              hoare lifts (n::m::nil)%list pre;
                match goal with
                  | |- {| _, _, _, _, _, _ |} |- ?ct  {{ <|| _ ||> ** LV x @ Tptr _ |=> Vptr ?l @ _ ** ?P' }} _ {{ _ }} =>
                    match find_ptrstruct P' l with
                      | none _ => fail 2
                      | some ?o =>
                        hoare lifts (1::2::(S (S o))::nil)%list pre;
                          eapply assign_rule_struct_aop_typeneq;
                          [ intro s; split; intro H; exact H
                          | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                          | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                          | simpl;auto
                          | simpl; auto
                          | unfold id_nth; simpl; auto
                          | simpl; auto
                          | intros; intro; tryfalse
                          | intros; intro; tryfalse
                          | symbolic execution
                          | apply assign_type_match_true; simpl; auto
                          | simpl; try omega
                          | simpl; auto
                          | li_sepauto li ]
                    end
                end
          end
        | none _ =>
          match find_dom_lenv P with
            | (none _, _) => fail 3
            | (some ?m, Some ?ls) =>
              let ret1 := constr:(var_notin_dom x ls) in
              let ret2 := (eval compute in ret1) in
              match ret2 with
                | true =>
                  match find_aop P with
                    | none _ => fail 1
                    | some ?n =>
                      match find_gvarmapsto P x with
                        | none _ => fail 4
                        | some ?o =>
                          hoare lifts (n::m::o::nil)%list pre;
                            match goal with
                              | |- {| _, _, _, _, _, _ |} |- ?ct {{ <|| _ ||> ** A_dom_lenv _ ** GV x @ Tptr _ |=> Vptr ?l @ _ ** ?P' }} _ {{ _ }} =>
                                match find_ptrstruct P' l with
                                  | none _ => fail 5
                                  | some ?p =>
                                    hoare lifts (1::2::3::(S (S (S p)))::nil)%list pre;
                                      eapply assign_rule_struct_g_aop_typeneq;
                                      [ intro s; split; intro H; exact H
                                      | simpl; auto
                                      | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                                      | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                                      | simpl;auto
                                      | simpl; auto
                                      | unfold id_nth; simpl; auto
                                      | simpl; auto
                                      | intros; intro; tryfalse
                                      | intros; intro; tryfalse
                                      | symbolic execution
                                      | apply assign_type_match_true; simpl; auto
                                      | simpl; try omega
                                      | simpl; auto
                                      | li_sepauto li ]
                                end
                            end
                      end
                  end
                | false => fail 6
              end
          end
      end
  end.

Ltac hoare_assign_array :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} (sassign (earrayelem (evar ?x) _) _) {{ _ }} =>
      match find_lvararray P x with
        | some ?m =>
          match find_aop P with
            | none _ => fail 1
            | some ?n =>
              hoare lifts (n::m::nil)%list pre;
                eapply assign_rule_array_aop;
                [ intro s; split; intro H; exact H
                | symbolic execution
                | symbolic execution
                | intuition auto
                | try omega
                | apply assign_type_match_true; simpl; auto
                | try omega
                | li_sepauto li ]
          end
        | none _ =>
          match find_dom_lenv P with
            | (none _, _) => fail 2
            | (some ?m, Some ?ls) =>
              let ret1 := constr:(var_notin_dom x ls) in
              let ret2 := (eval compute in ret1) in
              match ret2 with
                | true =>
                  match find_aop P with
                    | none _ => fail 1
                    | some ?n =>
                      match find_gvararray P x with
                        | none _ => fail 3
                        | some ?o =>
                          hoare lifts (n::m::o::nil)%list pre;
                            eapply assign_rule_array_g_aop;
                            [ intro s; split; intro H; exact H
                            | simpl; auto
                            | symbolic execution
                            | symbolic execution
                            | intuition auto
                            | try omega
                            | apply assign_type_match_true; simpl; auto
                            | try omega
                            | li_sepauto li]
                      end
                  end
                | false => fail
              end
          end
      end
    | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} (sassign (earrayelem _  _) _) {{ _ }} =>
      eapply assign_rule_ptr_array_aop;
        [ symbolic execution;try solve [eauto | simpl;eauto] 
        | intro s;split;intro H;
          [
            match goal with
              | H' : ?s |= ?P |- ?s |= Aarray ?l _ _ ** _ =>
                match find_ptrarray P l with
                  | (some ?n) => sep lift n in H'; try exact H'
                  | _ => fail 4
                end 
            end
          | match goal with 
              | H': ?s |= Aarray ?l _ _ ** _ |- ?s |= ?P =>
                match find_ptrarray P l with
                  | (some ?n) => sep lift n ; try exact H'
                  | _ => fail 4
                end
            end
          ]
        | symbolic execution 
        | symbolic execution
        | intuition auto
        | intuition auto
        | simpl;try omega
        | simpl;auto
        | simpl;try omega
        | li_sepauto li
        ]
  end.

Ltac hoare_assign_deref_ptr :=
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} (sassign (ederef _) _) {{ _ }} =>
      match find_aop P with
        | none _ => fail 1
        | some ?a =>
          hoare lift a pre;
            eapply assign_rule_deref_ptr;
            [ symbolic execution
            | match goal with
                | |- ?P' <==> PV ?l @ _ |-> _ ** _ =>
                  match find_ptrmapsto P' l with
                    | none _ => fail 2
                    | some ?b => 
                      intros until s; split; intro H;
                      [ sep lift b in H; exact H
                      | sep lift b;  exact H ]
                  end
              end
            | symbolic execution
            | apply assign_type_match_true; simpl; auto
            | li_sepauto li ]
      end
  end.


Ltac hoare_assign_deref_array_elem :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} (sassign (ederef _) _) {{ _ }} =>
      match find_aop P with
        | none _ => fail 1
        | some ?a =>
          hoare lift a pre;
            eapply assign_rule_deref_array_elem_aop;
            [ symbolic execution
            | match goal with
                | |- ?P' <==> Aarray (?b,_) _ _ ** _ =>
                  match find_ptrarray_by_block P' b with
                    | none _ => fail 2
                    | some ?b => 
                      intros; split; intro H;
                      [ sep lift b in H; exact H |
                        sep lift b; exact H]
                  end
              end
            | match goal with
                | |- ?t = Tarray _ _ => try unfold t; auto
              end
            | simpl; try omega
            | simpl; auto
            | simpl; try omega
            | try (simpl typelen;simpl Z.of_nat);try omega
            | try (simpl typelen;simpl Z.of_nat);try omega
            | try (simpl typelen;simpl Z.of_nat);try omega
            | symbolic execution
            | simpl; try omega
            | intros s H; try omega
            | apply assign_type_match_true; simpl; auto
            | simpl; auto
            | li_sepauto li ]
      end                  
  end.

Ltac hoare_assign :=
  first [ hoare_assign_var 
        | hoare_assign_struct 
        | hoare_assign_array
        | hoare_assign_deref_ptr
        | hoare_assign_deref_array_elem ].

(* assign_rule_struct_array *)

(* assign_rule_deref_struct *)

Close Scope nat_scope.




