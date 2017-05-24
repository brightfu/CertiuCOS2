Require Import include_frm.
Require Import sep_auto.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import tv_match.
Require Import hoare_tactics.

Open Scope code_scope.

Fixpoint decllen (lst :decllist): nat :=
  match lst with 
  | dnil => O
  | dcons _ _ lst' => S (decllen lst')
  end.

Lemma dl_vl_match_dv_same_length :
  forall (dl:decllist) (vl: list val),
    dl_vl_match dl vl = true -> decllen dl = length vl.
Proof.
  intro.
  induction dl.
  intros.
  induction vl.
  reflexivity.
  inversion H.
  intros.
  induction vl.
  inversion H.
  simpl.
  cut (decllen dl = length vl).
  intro.
  rewrite H0.
  reflexivity.
  apply IHdl.
  simpl in H.
  cut (type_val_match t a =true).
  intro.
  rewrite H0 in H.
  assumption.
  remember (type_val_match t a) as Hbool.
  destruct Hbool; tryfalse.
  auto.
Qed.

Lemma len_exist_0 :
  forall (vl: list val),
    length (rev vl) = 0%nat -> vl = nil.
Proof.
  inductions vl; intros; tryfalse; auto.
  rewrite rev_length in H.
  simpl in H; tryfalse.
Qed.


Lemma len_exist_1 :
  forall (vl: list val),
    length (rev vl) = 1%nat ->
    exists v1 , vl = v1 :: nil.  
Proof.
  inductions vl; intros; tryfalse; simpl; auto.
  simpl in H.
  rewrite app_length in H.
  simpl in H.
  rewrite plus_comm in H.  
  inverts H.    
  apply len_exist_0 in H1.
  simpljoin; eauto.
Qed.


Lemma len_exist_2 :
  forall (vl: list val),
    length (rev vl)  = 2%nat ->
    exists v1 v2, vl = v1 :: v2 :: nil.  
Proof.
  inductions vl; intros; tryfalse; simpl; auto.
  simpl in H.
  rewrite app_length in H.
  simpl in H.
  rewrite plus_comm in H.  
  inverts H.    
  apply len_exist_1 in H1.
  simpljoin; eauto.
Qed.


Lemma len_exist_3 :
  forall (vl: list val),
    length (rev vl)  = 3%nat ->
    exists v1 v2 v3, vl = v1 :: v2 :: v3 :: nil.  
Proof.
  inductions vl; intros; tryfalse; simpl; auto.
  simpl in H.
  rewrite app_length in H.
  simpl in H.
  rewrite plus_comm in H.  
  inverts H.    
  apply len_exist_2 in H1.
  simpljoin; eauto.
Qed.


Lemma len_exist_4 :
  forall (vl: list val),
    length (rev vl)  = 4%nat ->
    exists v1 v2 v3 v4, vl = v1 :: v2 :: v3 :: v4 ::  nil.  
Proof.
  inductions vl; intros; tryfalse; simpl; auto.
  simpl in  H.
  rewrite app_length in H.
  simpl in H.  
  rewrite plus_comm in H.
  inverts H.
  apply len_exist_3 in H1.
  simpljoin; eauto.
Qed.

Lemma len_exist_5 :
  forall (vl: list val),
    length (rev vl)  = 5%nat ->
    exists v1 v2 v3 v4 v5, vl = v1 :: v2 :: v3 :: v4 :: v5 :: nil.  
Proof.
  inductions vl; intros; tryfalse; simpl; auto.
  simpl in H.
  rewrite app_length in H.
  rewrite plus_comm in H.
  inverts H.    
  apply len_exist_4 in H1.
  simpljoin; eauto.
  do 5 eexists; eauto.
Qed.

Lemma len_exist_6 :
  forall (vl: list val),
    length (rev vl)  = 6%nat ->
    exists v1 v2 v3 v4 v5 v6, 
      vl = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: nil.  
Proof.
  inductions vl; intros; tryfalse; simpl; auto.
  simpl in H.
  rewrite app_length in H.
  rewrite plus_comm in H.
  inverts H.
  apply len_exist_5 in H1.
  simpljoin; eauto.
  do 6 eexists; eauto.
Qed.


Lemma dl_vl_match_0:
  forall vl , 
    dl_vl_match  dnil (rev vl) = true ->  vl = nil .
Proof.
  introv Heq.
  lets H100 :  dl_vl_match_dv_same_length  Heq.
  simpl in H100.
  apply sym_eq in H100.
  apply len_exist_0 in H100.
  auto.
Qed.

Lemma dl_vl_match_1:
  forall vl x t , 
    dl_vl_match (dcons x t dnil) (rev vl) = true -> 
    exists v, vl = v :: nil /\  type_val_match t  v  = true.
Proof.
  introv Heq.
  lets H100 :  dl_vl_match_dv_same_length  Heq.
  simpl in H100.
  apply sym_eq in H100.
  apply len_exist_1 in H100.
  simpljoin; eexists; split; eauto.
  simpl in Heq.
  remember (type_val_match t x0) as Hbool.
  destruct Hbool; tryfalse; auto.
Qed.

Lemma dl_vl_match_2:
  forall vl x1 t1 x2 t2 , 
    dl_vl_match ⌞x1 @ t1 ; x2 @ t2⌟ (rev vl) = true -> 
    exists v1 v2, vl = v1 :: v2 :: nil /\
                  type_val_match t2 v1 = true /\ 
                  type_val_match t1 v2 = true.
Proof.
  introv Heq.
  lets H100 :  dl_vl_match_dv_same_length  Heq.
  simpl in H100.
  apply sym_eq in H100.
  apply len_exist_2 in H100.
  simpljoin; do 2 eexists; splits; eauto.
  simpl in Heq.
  remember (type_val_match t1 x0) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t2 x) as Hbool.
  destruct Hbool; tryfalse; auto.
  simpl in Heq.
  remember (type_val_match t1 x0) as Hbool.
  destruct Hbool; tryfalse; auto. 
Qed.


Lemma dl_vl_match_3: forall vl x1 t1 x2 t2 x3 t3 , 
    dl_vl_match ⌞x1 @ t1 ; x2 @ t2 ;  x3 @ t3⌟ (rev vl) = true -> 
    exists v1 v2 v3, vl = v1 :: v2 :: v3 :: nil /\
                     type_val_match t3  v1 = true /\ 
                     type_val_match t2 v2 = true /\
                     type_val_match t1 v3 = true.
Proof.
  introv Heq.
  lets H100 :  dl_vl_match_dv_same_length  Heq.
  simpl in H100.
  apply sym_eq in H100.
  apply len_exist_3 in H100.
  simpljoin; do 3 eexists; splits; eauto.
  simpl in Heq.
  remember (type_val_match t1 x4) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t2 x0) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t3 x) as Hbool.
  destruct Hbool; tryfalse; auto.
  simpl in Heq.
  remember (type_val_match t1 x4) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t2 x0) as Hbool.
  destruct Hbool; tryfalse; auto.
  simpl in Heq.
  remember (type_val_match t1 x4) as Hbool.
  destruct Hbool; tryfalse; auto.
Qed.

Lemma dl_vl_match_4: forall vl x1 t1 x2 t2 x3 t3 x4 t4 , 
    dl_vl_match  ⌞x1 @ t1 ; x2 @ t2 ;  x3 @ t3 ; x4 @ t4⌟ (rev vl) = true -> 
    exists v1 v2 v3 v4, vl = v1 :: v2 :: v3 :: v4 ::  nil /\
                        type_val_match t4 v1 = true /\ 
                        type_val_match t3 v2 = true /\
                        type_val_match t2 v3 = true /\
                        type_val_match t1 v4 = true.
Proof.
  introv Heq.
  lets H100 :  dl_vl_match_dv_same_length  Heq.
  simpl in H100.
  apply sym_eq in H100.
  apply len_exist_4 in H100.
  simpljoin; do 4 eexists. 
  split.
  eauto.
  simpl in Heq.
  remember (type_val_match t1 x6) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t2 x5) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t3 x0) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t4 x) as Hbool.
  destruct Hbool; tryfalse; auto.
Qed.

Lemma dl_vl_match_5: forall vl x1 t1 x2 t2 x3 t3 x4 t4 x5 t5 , 
    dl_vl_match  ⌞x1 @ t1 ; x2 @ t2 ;  x3 @ t3 ; x4 @ t4 ; x5 @ t5⌟ (rev vl) = true -> 
    exists v1 v2 v3 v4 v5,
      vl = v1 :: v2 :: v3 :: v4 :: v5 :: nil /\  
      type_val_match t5 v1 = true /\ 
      type_val_match t4 v2 = true /\
      type_val_match t3 v3 = true /\
      type_val_match t2 v4 = true /\
      type_val_match t1 v5 = true.
Proof.
  introv Heq.
  lets H100 :  dl_vl_match_dv_same_length  Heq.
  simpl in H100.
  apply sym_eq in H100.
  apply len_exist_5 in H100.
  simpljoin; do 5 eexists. 
  split.
  eauto.
  simpl in Heq.
  remember (type_val_match t1 x8) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t2 x7) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t3 x6) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t4 x0) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t5 x) as Hbool.
  destruct Hbool; tryfalse; auto.
Qed.


Lemma   dl_vl_match_6 : 
  forall vl x1 t1 x2 t2 x3 t3 x4 t4 x5 t5 x6 t6 , 
    dl_vl_match  ⌞x1 @ t1 ; x2 @ t2 ;  x3 @ t3 ; x4 @ t4 ; x5 @ t5 ; x6 @ t6⌟ (rev vl) = true -> 
    exists v1 v2 v3 v4 v5 v6,
      vl = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: nil /\  
      type_val_match t6 v1 = true /\ 
      type_val_match t5 v2 = true /\
      type_val_match t4 v3 = true /\
      type_val_match t3 v4 = true /\
      type_val_match t2 v5 = true /\ 
      type_val_match t1 v6 = true.
Proof.
  introv Heq.
  lets H100 :  dl_vl_match_dv_same_length  Heq.
  simpl in H100.
  apply sym_eq in H100.
  apply len_exist_6 in H100.
  simpljoin; do 6 eexists. 
  split.
  eauto.
  simpl in Heq.
  remember (type_val_match t1 x10) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t2 x9) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t3 x8) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t4 x7) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t5 x0) as Hbool.
  destruct Hbool; tryfalse; auto.
  remember (type_val_match t6 x) as Hbool.
  destruct Hbool; tryfalse; auto.
  splits; auto.
Qed.


Ltac unfold_internal_pre :=
  match goal with
    | H:_
      |- context[{|_ , _, _, _,  _ , _|}|- ?ct {{?p}}_ {{_}}] =>  
      match p with
        | _  **  (?t _  _  _  ) **  _ =>  try   unfold t
      end
    | _ => idtac
  end.


Ltac unfold_internal_post :=
  match goal with
    | H:_
      |-context[ {|_ , _, _, _,  ?r , _|}|- ?ct {{_}}_ {{_}}] => 
      match r with 
        |  context[_  **  (?t  _ _ _  _) ** _ ]  =>  
             try unfold t              
      end
    | _ => idtac
  end.

Ltac init_retspec :=
  match goal with
    | H : Some _ = BuildRetI _ _ _ _ _ _ |-  _ =>
      unfold BuildRetI in H; simpl in H; inverts H;unfold_internal_post
    | H : Some _ = BuildRetA' _ _ _ _ _ _ _ |-  _ =>
      unfold BuildRetA' in H; simpl in H; inverts H
  end.

Ltac init_prespec  := 
  match goal with
    | H : Some _ = BuildPreI ?x ?y ?z _ _ _ |-  _ => 
      unfold BuildPreI in H;
        let xy:= fresh in 
        remember (x y) as xy; 
          destruct xy as [ xy | ]; tryfalse;
          let a := fresh in
          destruct xy as [ [ [ ? a ] ] ]; 
            let b := fresh in
            remember (dl_vl_match a (rev z)) as b; 
              destruct b; tryfalse
    | H: Some _ = BuildPreA' ?x ?y _ ?z _ _ _ |- _ =>
      unfold BuildPreA' in H;
        let xy := fresh in
        remember (x y) as xy;
          destruct xy as [ xy | ]; tryfalse;
          let a := fresh in
          destruct xy as [ [ [ ? a ] ] ];
            let b := fresh in    
            remember (dl_vl_match a (rev z)) as b;
              destruct b; tryfalse              
  end;
  match goal with
    | H :  Some _  =  _ _  |- _ => inverts H
  end;
  match goal with
    | H : true = _ ?l _ |- _ => apply sym_eq in H; 
        match listlen l with
          | 0%nat => apply dl_vl_match_0 in H; simpljoin
          | 1%nat => apply dl_vl_match_1 in H; simpljoin
          | 2%nat => apply dl_vl_match_2 in H; simpljoin
          | 3%nat => apply dl_vl_match_3 in H; simpljoin
          | 4%nat => apply dl_vl_match_4 in H; simpljoin
          | 5%nat => apply dl_vl_match_5 in H; simpljoin
          | 6%nat => apply dl_vl_match_6 in H; simpljoin
          | _ => fail
        end
  end;
  match goal with
    | H : Some _ = _ |- _ =>
      simpl in H; inverts H
  end;
  do 4 eexists; split; auto.

(*
Ltac init_spec_api :=
  intros; init_retspec; init_prespec; 
  hoare normal pre;
  hoare_split_pure_all;

 (* eapply backward_rule1;
  [ apply Aop_Aop'_eq'
  | idtac ];
  let H := fresh in
  eapply r_conseq_rule;
  [ intros ? ? H; apply Aop_Aop'_eq; exact H
  | intros ? H; exact H
  | idtac ];*)
  type_val_match_elim.
(*
Ltac init_spec_internal :=  intros; init_retspec; init_prespec; 
  type_val_match_elim; unfold_internal_pre_post.
*)
*)

Ltac init_spec := 
  intros; init_retspec; init_prespec; 
  unfold_internal_pre;
  hoare normal pre;
  hoare_split_pure_all;
  type_val_match_elim.

Tactic Notation "init" "spec" := init_spec.

Close Scope code_scope.
