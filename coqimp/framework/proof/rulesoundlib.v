Require Import include_frm.
Require Import sep_auto.
Require Import simulation.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import lmachLib.
Require Import join_lib.
Require Import memory_prop.
Require Import absinfer_sound.
Require Import mem_join_lemmas.
Require Import sep_lemmas_ext.
Require Import joinmemLib.
Require Import aux_map_lib.

Import DeprecatedTactic.

Open Local Scope nat_scope.

(*Continuation Properties*)

Lemma addstmts_eq_addcont : 
  forall s ks ,
    AddStmtToKs s ks = AddKsToTail (kseq s kstop) ks.
Proof.
  introv.
  inductions ks; simpls; try (rewrite IHks; auto); auto.
Qed.

Lemma addstmts_same_remove : forall s ks ks',  AddStmtToKs s ks =  AddStmtToKs s ks' -> ks =ks'. 
Proof.
  introv H.
  inductions ks; inductions ks'; tryfalse; simpl in H; try inverts H; try auto.
  rewrite  addstmts_eq_addcont in H2.
  simpl in H2.
  destruct ks'; simpl in H2; inverts H2.
  rewrite  addstmts_eq_addcont in H2.
  destruct ks; simpl in H2; inverts H2.
  apply IHks in H2.
  subst; auto.
  apply IHks in H4.
  subst; auto.
  apply IHks in H4; subst; auto.
  apply IHks in H3; subst; auto.
  apply IHks in H3; subst; auto.
  apply IHks in H5; subst; auto.
  apply IHks in H3; subst; auto.
  apply IHks in H3; subst; auto.
  apply IHks in H1; subst; auto.

  apply IHks in H3; subst; auto.

Qed.

Lemma length_addcont : forall ks ks', len_stmtcont (ks##ks') = (len_stmtcont ks) + (len_stmtcont ks').
Proof.
  intros.
  induction ks;simpl;auto.
Qed.

Lemma addcont_same_remove : forall ks ks' ks0, ks##ks0 = ks'##ks0 -> ks = ks'.
Proof.
  introv H.
  assert (len_stmtcont (ks##ks0) = len_stmtcont (ks'##ks0)).
  rewrite H;auto.
  repeat rewrite length_addcont in H0.
  inductions ks; inductions ks'; tryfalse; simpl in H; try inverts H; try auto;simpl in H0 ; try omega;
  try (do 4 decEq;eapply IHks;eauto;try omega).
Qed.

(* callcont *)
Lemma callcont_some_addstmts : forall ks s k ,  
                                 callcont ks = Some k -> callcont (AddStmtToKs s ks) 
                                                         = Some  (AddStmtToKs s k) .
Proof.
  introv  H.
  inductions ks;
    try simpl in H;
    try simpl;
    try eapply IHks; eauto;  tryfalse.
  inverts H.
  simpl.
  auto.
Qed.

Lemma callcont_some_addstmts_rev : forall s ks ks', callcont (AddStmtToKs s ks) = Some (AddStmtToKs s ks') -> 
                                                    callcont  ks = Some ks'.
Proof.
  introv Hcall.
  inductions ks;simpl; auto.
  simpl in Hcall.
  inverts Hcall.
  simpl in  Hcall.
  inverts Hcall.
  assert (AddStmtToKs s (kcall f s0 e ks) =  kcall f s0 e (AddStmtToKs s ks)).
  simpl.
  auto.
  rewrite <- H in H0.
  apply addstmts_same_remove in H0.
  subst; auto.
  simpl in Hcall.
  inverts Hcall.
Qed.

Lemma callcont_some_addcont : forall ks ks1 k ,  
                                callcont ks = Some k -> callcont (AddKsToTail ks1 ks) 
                                                        = Some  (AddKsToTail ks1 k) .
Proof.
  introv  H.
  inductions ks;
    try simpl in H;
    try simpl;
    try eapply IHks; eauto;  tryfalse.
  inverts H.
  simpl.
  auto.
Qed.

Lemma callcont_none_addstmts : forall s ks , callcont (AddStmtToKs s ks) = None -> callcont  ks = None.
Proof.
  introv Hcall.
  inductions ks;simpl; auto.
  simpl in Hcall.
  inverts Hcall.
Qed.

Lemma callcont_none_addstmts_rev : forall ks s, callcont ks = None -> callcont (AddStmtToKs s ks) = None.
Proof.
  induction ks;intros;simpl;auto.
  simpl in H.
  inversion H.
Qed.

Lemma callcont_none :
  forall ks f s E ks', 
    callcont (ks ## kcall f s E kstop) = None -> 
    callcont (ks ## kcall f s E ks') = None.
Proof.
  intros.
  gen ks ks' f s E.
  induction ks; induction ks'; intros; simpl in *; tryfalse || auto.
Qed.

Lemma callcont_stmts_exist : forall s ks f s0 le ks',
                               callcont (AddStmtToKs s ks) = Some (kcall f s0 le ks')->
                               exists ks'', kcall f s0 le ks' = AddStmtToKs s (kcall f s0 le ks'').
Proof.
  introv H.
  inductions ks ; 
    try (simpl in H;
         apply IHks in H;
         auto);
    try (simpl in H;inverts H).
  simpl.
  exists ks; auto.
Qed.

Lemma callcont_addkcall_imply_callcont_addkcall_exist :
  forall ks f s E ks' f' s' E' ks'' ks1,
    callcont (ks ## kcall f s E ks') = Some (kcall f' s' E' ks'') ->
    exists ks1' , callcont (ks ## kcall f s E ks1 ) = Some (kcall f' s' E' ks1').
Proof.
  intros.
  induction ks;
    simpl in *;
    try inverts H;
    try solve [do 4 eexists;eauto];
    try solve [apply IHks;eauto].
Qed.

Lemma callcont_addkcall_imply_addcont_exist :
  forall ks f s E ks' f' s' E' ks'',
    callcont ks <> None ->
    callcont (ks ## kcall f s E ks') = Some (kcall f' s' E' ks'') ->
    exists ks''', ks'' = ks''' ## kcall f s E ks'.
Proof.
  induction ks;intros;inverts H0;try solve [eapply IHks;eauto].
  simpl in H. false.
  eexists. auto.
Qed.

Lemma callcont_addkcall_imply_callcont_addkcall :
  forall ks f1 s1 E1 ks1 f2 s2 E2 ks2 f s E ks',
    callcont (ks ## kcall f1 s1 E1 ks1 ) = Some (kcall f s E (ks' ## kcall f1 s1 E1 ks1)) ->
    callcont (ks ## kcall f2 s2 E2 ks2 ) = Some (kcall f s E (ks' ## kcall f2 s2 E2 ks2)).
Proof.
  induction ks;intros;inverts H;try solve [eapply IHks;eauto].
  simpl. assert (len_stmtcont ks1 = len_stmtcont (ks' ## kcall f s E ks1)).
  rewrite H4 at 1;auto.
  simpl in H. rewrite length_addcont in H.
  simpl in H. omega.
  apply addcont_same_remove in H4.
  subst.
  simpl.
  auto.
Qed.

Lemma stmtcont_eq_length :
  forall (s1 s2 : stmtcont),
    s1 = s2 -> len_stmtcont s1 = len_stmtcont s2.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

Lemma  callcont_ks_kstop :
  forall ks f s E ks',
    callcont (ks ## kcall f s E ks') = Some (kcall f s E ks') ->
    callcont (ks ## kcall f s E kstop) = Some (kcall f s E kstop).
Proof.
  intros.
  gen ks'.
  induction ks; intros; simpl in *; tryfalse || eauto.
  inversion H; clear H.
  false.
  gen H4; clear; intros.
  apply stmtcont_eq_length in H4.
  assert (forall ks ks', len_stmtcont (ks ## ks') >= len_stmtcont ks') as H100. 
  clear; intros.
  induction ks; simpl; try omega.
  lets H200 : H100 ks (kcall f s E ks').
  rewrite H4 in H200; clear H100 H4.
  assert (forall ks, len_stmtcont (kcall f s E ks) = S (len_stmtcont ks)) as H100.
  clear; intros.
  induction ks; simpl; try omega.
  rewrite H100 in H200; clear H100.
  omega.
Qed.

Lemma  call_int_cont_none : 
  forall ks f s E ks1 ,
    callcont (ks ## kcall f s E ks1) <> None -> 
    callcont ks = None ->
    callcont (ks ## kcall f s E ks1) = Some (kcall f s E ks1).
Proof.
  induction ks; intros; simpl in *; tryfalse || eauto.
Qed.

Lemma callcont_kseq_kstop : 
  forall ks e s f s0 le' ks'0,
    callcont (ks ## kseq (swhile e s) kstop) = Some (kcall f s0 le' ks'0) ->
    exists ks',callcont ks = Some (kcall f s0 le' ks').
Proof.
  induction ks;intros;inverts H;try solve [eapply IHks;eauto].
  eexists;simpl;auto.
Qed.

Lemma callcont_addcont_none :   
  forall ks ks', 
    callcont (ks ## ks') = None -> 
    callcont ks = None.
Proof.
  intros.
  induction ks; simpl in *; tryfalse || auto.
Qed.

Lemma callcont_nont_addkseq_kstop : 
  forall ks s,
    callcont ks = None -> 
    callcont (ks ## kseq s kstop) = None.
Proof.
  intros.
  induction ks; simpl in *; tryfalse || auto.
Qed.

(* intcont *)
Lemma intcont_some_addcont : 
  forall ks ks1 k ,  
    intcont ks = Some k ->
    intcont (AddKsToTail ks1 ks)  = Some  (AddKsToTail ks1 k) .
Proof.
  introv  H.
  inductions ks;
    try simpl in H;
    try simpl;
    try eapply IHks; eauto;  tryfalse.
  inverts H.
  simpl.
  auto.
Qed.

Lemma intcont_some_addstmts : 
  forall ks s k ,  
    intcont ks = Some k ->
    intcont (AddStmtToKs s ks)  = Some  (AddStmtToKs s k) .
Proof.
  introv  H.
  inductions ks;
    try simpl in H;
    try simpl;
    try eapply IHks; eauto;  tryfalse.
  inverts H.
  simpl.
  auto.
Qed.

Lemma intcont_none_addstmts :
  forall s ks , 
    intcont (AddStmtToKs s ks) = None -> 
    intcont  ks = None.
Proof.
  introv Hint.
  inductions ks;simpl; auto.
  simpl in Hint.
  inverts Hint.
Qed.

Lemma intcont_none_addstmsts_rev : 
  forall s ks ,
    intcont  ks = None -> 
    intcont (AddStmtToKs s ks) = None.
Proof.
  introv Hint.
  inductions ks;simpl; auto.
  simpl in Hint.
  inverts Hint.
Qed.

Lemma intcont_none_addcont : 
  forall s ks , 
    intcont (ks##s) = None -> 
    intcont  ks = None.
Proof.
  introv Hcall.
  inductions ks;simpl; auto.
  simpl in Hcall.
  inverts Hcall.
Qed.

Lemma intcont_nont_addstmt_prev :
  forall ks s, 
    intcont ks = None ->
    intcont (ks ## kseq s kstop) = None.
Proof.
  intros.
  induction ks; simpl in *; tryfalse || auto.
Qed.

Lemma intcont_none : 
  forall ks f s E ks', 
    intcont (ks ## kcall f s E kstop) = None -> 
    intcont (ks ## kcall f s E ks') = None.
Proof.
  intros.
  gen ks ks' f s E.
  induction ks; induction ks'; intros; simpl in *; tryfalse || auto.
Qed.

Lemma intcont_some_kcall_none :  
  forall ks f s E ks1, 
    intcont (ks ## kcall f s E ks1) <> None -> 
    intcont ks <> None. 
Proof.
  induction ks; intros; simpl in *; tryfalse || eauto.
  intro;tryfalse.
Qed.

Lemma intcont_intcont_none: 
  forall ks f s E ks',
    intcont ks = None ->  
    intcont (ks ## kcall f s E ks') =  None.
Proof.
  induction ks; intros; simpl in *; tryfalse || auto.
Qed.

Lemma intcont_addkcall_exist : 
  forall ks f s E ks' c0 ke0 le0 ks'0 ,
    intcont (ks ## kcall f s E ks') = Some (kint c0 ke0 le0 ks'0) ->
    exists ks'', ks'0 = ks'' ## kcall f s E ks'.
Proof.
  induction ks;intros;inverts H;try apply IHks;eauto.
Qed.

Lemma intcont_addkcall_imply_intcont :
  forall ks f s E ks' c0 ke0 le0 ks1 ,
    intcont (ks ## kcall f s E ks1) = Some (kint c0 ke0 le0 (ks' ## kcall f s E ks1)) -> 
    intcont ks = Some (kint c0 ke0 le0 ks').
Proof.
  induction ks;intros;inverts H;try eapply IHks;eauto.
  apply addcont_same_remove in H4.
  rewrite H4;auto.
Qed.

Lemma intcont_addkcall_imply_intcont_addkcall_exist :
  forall ks f1 s1 E1 ks1 f2 s2 E2 ks2 c ke E ks',
    intcont (ks ## kcall f1 s1 E1 ks1 ) = Some (kint c ke E ks') ->
    exists ks'',intcont (ks ## kcall f2 s2 E2 ks2 ) = Some (kint c ke E ks'').
Proof.
  induction ks;intros;inverts H;try solve [eapply IHks;eauto].
  eexists;simpl;eauto.
Qed.

(* intcont & callcont *)
Lemma  callcont_none_intcont_some_imply_callcont_addcont_none :
  forall ks ks' ,
    callcont ks = None ->
    intcont ks <> None ->  callcont (ks ## ks') = None.
Proof.
  inductions ks;introv Hcal Hint ; simpl; auto.
  simpl in Hint; tryfalse.
  simpl in Hint; tryfalse.
Qed.

Lemma callcont_some :
  forall ks0 f s E', 
    callcont ks0 = None ->
    intcont ks0 = None ->
    callcont (ks0 ## kcall f s E' kstop) = Some (kcall f s E' kstop).
Proof.
  inductions ks0;introv Hcall Hint;simpl in *; tryfalse; try eauto.
Qed.

Lemma callcont_kcall_neqnone : 
  forall ks f s E , ~(callcont (ks ## kcall f s E kstop) = None /\ intcont (ks ## kcall f s E kstop) = None).
Proof.
  inductions ks; introv Hfalse; simpl in Hfalse; destruct Hfalse; tryfalse; try (eapply IHks; eauto).
Qed.

Lemma callcont_not_none : 
  forall ks f  s E ks', 
    intcont (ks ## kcall f  s E ks') = None-> 
    callcont (ks ## kcall f  s E ks') <> None. 
Proof.
  intros.
  induction ks; simpl in  *; try discriminate || auto.
Qed.

Lemma callcont_not_none' :  
  forall ks f  s E ks' ks0 , 
    ks ## kcall f s E ks' = kret ks0 -> 
    intcont ks0 = None -> 
    callcont ks0 <> None.
Proof.
  intros.
  gen f s E ks' ks0.
  induction ks; intros; simpl in *; try discriminate || auto.
  inverts H.
  eapply  callcont_not_none; eauto.
Qed.

Lemma  call_int_none_call:
  forall ks f s E ks',
    callcont ks =None -> intcont ks = None ->
    callcont (ks ## kcall f s E ks') = Some (kcall f s E ks').
Proof.
  inductions ks; intros; simpl in *; tryfalse; try auto.
Qed.

Lemma callcont_some_eq : 
  forall ks1 f s E ks ,
    callcont ks1 = None -> 
    intcont ks1 = None -> 
    callcont (ks1 ## kcall f s E ks) =  Some (kcall f s E ks) .
Proof.  
  induction ks1; induction ks; intros; simpl in *; tryfalse || auto.
Qed.

Lemma  callcont_intcont_kcall_none :
  forall ks f s E , 
    callcont ks = None ->
    intcont (ks ## kcall f s E kstop) = None ->
    intcont ks = None.
Proof.
  inductions ks; tryfalse; simpl; auto.
  introv _ Hf; tryfalse.
Qed.

Lemma intcont_calcont_not_none: 
  forall ks f s E ks',
    intcont ks = None -> 
    callcont (ks ## kcall f s E ks') <>  None.
Proof.
  induction ks; intros; simpl in *; tryfalse || auto.
  intro;tryfalse.
  intro;tryfalse.
Qed.

(* others *)
Lemma ks_puls_kcall_neq :
  forall ks ks' f s E, ks ## kcall f s E ks' <> kstop.
Proof.
  intros.
  induction ks;simpl;try discriminate.
Qed.

Lemma add_stmt_not_kstop : 
  forall s ks, AddStmtToKs s ks <> kstop.
Proof.
  intros.
  induction ks;simpl;try discriminate.
Qed.

Lemma addstmt_kret_exist : 
  forall s ks ks' ,  
    AddStmtToKs s ks = kret ks' -> 
    exists ks'', ks = kret ks''.
Proof.
  intros.
  destruct ks;inverts H.
  eexists;eauto.
Qed. 

Lemma kseq_not_kstop :
  forall ks e s, ks ## kseq (swhile e s) kstop <> kstop.
Proof.
  intros.
  destruct ks;simpl;discriminate.
Qed.

Lemma kseq_eq_addstmt:
  forall ks s , ks ## kseq s kstop  = AddStmtToKs s ks.
Proof.
  intros.
  rewrite addstmts_eq_addcont.
  auto.
Qed.

(* addcont *)
Lemma kseq_addcont :
  forall ks ks' ks'',
    kseq ks (ks' ## ks'') = (kseq ks ks') ## ks''.
Proof.
  intros. simpl. auto.
Qed.

Lemma kcall_addcont : 
  forall f s E ks ks',
    kcall f s E (ks ## ks') = (kcall f s E ks) ## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kint_addcont :
  forall c ke le ks ks',
    kint c ke le (ks ## ks') = (kint c ke le ks) ## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kassignr_addcont : 
  forall e t ks ks',
    kassignr e t (ks ## ks') = (kassignr e t ks )## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kassignl_addcont : 
  forall v t ks ks',
    kassignl v t (ks ## ks') = (kassignl v t ks )## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kfuneval_addcont : 
  forall f vl tl el ks ks',
    kfuneval f vl tl el (ks ## ks') = (kfuneval f vl tl el ks) ## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kif_addcont : 
  forall s1 s2 ks ks',
    kif s1 s2 (ks ## ks') = (kif s1 s2 ks) ## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kwhile_addcont :
  forall e s ks ks',
    kwhile e s (ks ## ks') = (kwhile e s ks) ## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kret_addcont :
  forall ks ks',
    kret (ks ## ks') = (kret ks) ## ks'.
Proof.
  intros. simpl. auto.
Qed.

Ltac rewrite_addcont :=
  try rewrite kseq_addcont;
  try rewrite kcall_addcont;
  try rewrite kint_addcont;
  try rewrite kassignr_addcont;
  try rewrite kassignl_addcont;
  try rewrite kfuneval_addcont;
  try rewrite kif_addcont; 
  try rewrite kwhile_addcont;
  try rewrite kret_addcont.


Fixpoint length_dl (dl : decllist) : nat :=
  match dl with
    | dnil => O
    | dcons _ _ dl' => S (length_dl dl')
  end.

Definition  isallocate (C : code) := 
  exists vl dl ks , C = (curs (salloc  vl dl), (kenil, ks)) /\ 
                    dl <> dnil /\  length vl <=  length_dl dl.

Definition joinenvmem (o: taskst) (E : env) (M : mem) (o':taskst) :  Prop :=
  exists G E0 E1 M0 M1 ir aux, 
    o = ((G, E0, M0), ir, aux) /\ 
    o' = ((G,E1,M1), ir, aux)
    /\ join E0 E E1 /\ join M0 M M1.


Definition  allocstep  (C : code) (o o' : taskst) :=  
  exists vl dl ks x t , C = (curs (salloc  vl (dcons x t dl)), (kenil, ks)) /\ 
                        length vl <= S (length_dl dl) /\ 
                        (vl = nil -> exists b v M , mapstoval (b,0%Z) t true v M 
                                                    /\ joinenvmem o (EnvMod.sig x (b,t)) M o') /\
                        (vl <> nil -> exists b v vl' M , vl = v :: vl'/\
                                                         mapstoval (b,0%Z) t true v M 
                                                         /\joinenvmem o (EnvMod.sig x (b,t)) M o').

Definition losallocstep (p:progunit)(C: code) (o: taskst) (C' : code)(o':taskst) :=
  loststep p C o C' o' /\  allocstep C o o'.


Inductive losallocstepstar :  progunit -> code -> taskst -> code -> taskst -> Prop :=
| losallocstepstar_0 : forall p C o, losallocstepstar  p C o C o
| losallocstepstar_n : forall  p C o C'' o'' C' o', losallocstep  p C o C'' o'' ->
                                                    losallocstepstar  p C'' o'' C' o'  ->
                                                    losallocstepstar  p C o C' o'. 

Inductive losallocstepn : nat -> progunit -> code -> taskst -> code -> taskst -> Prop :=
| losallocstep_0 : forall p C o, losallocstepn O p C o C o
| losallocstep_n : forall n p C o C'' o'' C' o', losallocstep  p C o C'' o'' ->
                                                 losallocstepn n  p C'' o'' C' o'  ->
                                                 losallocstepn (S n) p C o C' o'.


Tactic Notation "invertstep" tactic (t) :=
  repeat progress
         match goal with
           | H : (_, _) = (_, _) |- _ => inverts H; tryfalse
           | H : estep _ _ _ _ _ _ |- _ => inverts H
           | H : loststep _ _ _ _ _ |- _ => inverts H
           | H : cstep _ _ _ _ _ |- _ => inverts H
           | H : sstep _ _ _ _ _ _ _ |- _ => inverts H
           | _ => t
         end.


Lemma alloc_locality_pre1 :
  forall x l t v E  E' M1 M2 M3 M4 M5 M6 M'', 
    join M1 M2 M3 -> 
    join M3 M4 M5 ->
    mapstoval l t true v M'' ->
    join M5 M'' M6 ->
    alloc x t E M5 E' M6 ->
    exists M1', alloc x t E M1 E' M1' /\ 
                join M1 M'' M1'.
Proof.
  intros.
  unfold alloc in *; mytac.
  lets H100 : join_assoc_l H H0; mytac.
  assert (fresh M1 x0) as H100 by (eapply fresh_mono; eauto).
  eexists; mytac.
  eexists; mytac.
  4 : auto.
  3 : auto.
  auto.
  auto.
  remember (typelen t) as n.
  gen H2 H3 H100; clear; intros.
  eapply join_allocb'; eauto.
Qed.

Lemma alloc_locality_pre2 :
  forall x l t v b  E  E' M1 M2 M3 M4 M5 M6 M7 M'', 
    join M1 M2 M3 -> 
    join M3 M4 M5 ->
    mapstoval l t true v M'' ->
    join M5 M'' M7 ->
    alloc x t E M5 E' M6 ->
    EnvMod.get E' x = Some (b, t) ->
    store t M6 (b, BinNums.Z0) v = Some M7 -> 
    exists M1' M1'', alloc x t E M1 E' M1' /\
                     store t M1' (b, BinNums.Z0) v = Some M1'' /\
                     join M1 M'' M1''.
Proof.
  intros.
  unfold alloc in *; mytac.
  lets H100 : join_assoc_l H H0; mytac.
  assert (fresh M1 x0) as H100 by (eapply fresh_mono; eauto).
  lets He : allocb_store_mem_ex t M1 b v.
  destruct He as (M1' & He).
  eexists; mytac.
  eexists; mytac.
  eexists; mytac.
  4 : auto.
  3 : auto.
  auto.
  auto.
  unfold set in H4; simpl in H4.
  rewrite EnvMod.set_a_get_a in H4; inverts H4.
  eauto.
  apply identspec.eq_beq_true; auto.
  unfold set in H4; simpl in H4.
  EnvMod.rewrite_get.
  inverts H4.
  eapply join_store_allocb;eauto.
Qed.

Lemma rulesoundlib_map1 :
  forall (A B T : Type) (MC : PermMap A B T) x7 M1 x1 M2 M x M'',
    join x7 M1 x1 ->
    join x1 M2 M ->
    join M x M'' ->
    join x7 x (merge x7 x) ->
    disjoint M1 (merge x7 x).
  hy.
Qed.

Lemma rulesoundlib_map2 :
  forall (A B T : Type) (MC : PermMap A B T) x7 M1 x1 M2 M x M',
    join x7 M1 x1 ->
    join x1 M2 M ->
    join M x M' ->
    join x7 x (merge x7 x) ->
    disjoint (merge x7 x) M1.
  hy.
Qed.

Lemma alloc_locality :
  forall p  vl dl ks o  o2 C' o2' M1 M2, 
    length vl <= length_dl dl ->
    dl <> dnil ->
    joinm2 o M1 M2 o2 ->
    loststep p (curs (salloc  vl dl), (kenil, ks)) o2 C' o2'->
    exists o', 
      losallocstep p  (curs (salloc  vl dl), (kenil, ks))  o C' o' /\  joinm2 o' M1 M2 o2'.
Proof.
  intros.
  unfold joinm2 in H1; simpljoin.
  rename H3 into Hx; rename H2 into H3; rename Hx into H2.
  rename x into o1.
  unfold joinmem in *; simpljoin.
  invertstep tryfalse.
  lets H100 : alloc_store_exist_mem_env H8 H10 H16; simpljoin.

  lets H100 : alloc_locality_pre2 H7 H5 H1 H3 H8.
  lets H200 : H100 H10 H16; clear H100; simpljoin.

  lets H100 : mem_join_disjoint_eq_merge H9; mytac.
  lets H100 : EnvMod.join_disj_meq H4; mytac.
  apply EnvMod.meq_eq in H13; substs.
  eexists; mytac.
  unfold losallocstep; mytac.
  eapply ostc_step.
  eapply stmt_step; eauto.
  econstructor; eauto.
  unfolds.
  do 5 eexists; mytac; eauto.
  introv Hz; tryfalse.
  introv Hz. do 4 eexists; splits; mytac; eauto.
  unfold joinenvmem.
  do 7 eexists; mytac; eauto.

  unfolds; unfold joinmem.
  eexists.
  split.

  do 6 eexists; mytac; eauto.
  apply join_merge_disj.
  (* ** ac: Check disj_sym. *)
  apply disj_sym.
  (* ** ac: Check disj_merge_intro_r. *)

  eapply rulesoundlib_map1; eauto.
  (* apply disj_sym; apply disj_merge_intro_r; split. *)
  (* apply join_comm in H7. *)
  (* lets H100 : mem_join_disjoint_eq_merge H7; mytac; auto. *)
  (* apply join_comm in H7. *)
  (* lets H100 : join_assoc_l H7 H5; mytac. *)
  (* apply join_comm in H14. *)
  (* lets H100 : join_assoc_l H14 H3; mytac. *)
  (* unfolds; eauto. *)
  
  do 6 eexists; mytac; eauto.
  apply join_comm in H5.
  lets H100 : join_assoc_l H5 H3; mytac.
  apply join_comm in H7.
  lets H100 : join_assoc_l H7 H13; mytac.
  lets H100 : mem_join_disjoint_eq_merge H15; mytac.
  apply join_comm in H17.
  lets H100 : mem_join_disjoint_eq_merge H17; mytac.

  
  lets H100 : alloc_exist_mem_env H14; mytac.
  lets H100 : alloc_locality_pre1 H7 H5 H1 H3 H14; mytac.
  lets H100 : mem_join_disjoint_eq_merge H6; mytac.
  lets H100 : EnvMod.join_disj_meq H4; mytac.
  apply EnvMod.meq_eq in H10; substs.
  eexists; mytac.
  unfold losallocstep; mytac.
  eapply ostc_step.
  eapply stmt_step; eauto.
  econstructor; eauto.
  unfolds.
  do 5 eexists; mytac; eauto.
  introv Hz; tryfalse.
  do 3 eexists; splits; eauto.
  unfold joinenvmem.
  do 7 eexists; mytac; eauto.
  intros; tryfalse.

  unfolds; unfold joinmem.
  eexists.
  split.
  
  do 6 eexists; splits; mytac; eauto.
  apply join_merge_disj.
  eapply rulesoundlib_map2; eauto.
  (* apply disj_sym; apply disj_merge_intro_r; split. *)
  (* apply join_comm in H7. *)
  (* lets H100 : mem_join_disjoint_eq_merge H7; mytac; auto. *)
  (* apply join_comm in H7. *)
  (* lets H100 : join_assoc_l H7 H5; mytac. *)
  (* apply join_comm in H11. *)
  (* lets H100 : join_assoc_l H11 H3; mytac. *)
  (* unfolds; eauto. *)
  
  do 6 eexists; mytac; eauto.
  apply join_comm in H5.
  lets H100 : join_assoc_l H5 H3; mytac.
  apply join_comm in H7.
  lets H100 : join_assoc_l H7 H10; mytac.
  lets H100 : mem_join_disjoint_eq_merge H12; mytac.
  apply join_comm in H13.
  lets H100 : mem_join_disjoint_eq_merge H13; mytac.
Qed.


Lemma good_inv_prop :
  forall p, GoodInvAsrt p ->
            forall ge le M ir ie is cs abst op,
              (ge, le, M ,ir, (ie ,is,cs), abst, op) |= p ->
              forall le' op' ie' cs',
                (ge,le', M, ir, (ie',is,cs') ,abst, op') |= p.
Proof.
  introv.
  inductions p; introv Hgood; introv Hsat; introv; simpl in *;  tryfalse; auto.
  destruct Hsat as [Hsat1 Hsat2].
  destruct Hgood as [Hgp Hgq].
  lets Hgpp : IHp1 Hgp Hsat1.
  lets Hgqq : IHp2 Hgq Hsat2.
  splits.
  eapply Hgpp; eauto.
  eapply Hgqq; eauto.
  destruct Hgood as [Hgp Hgq].
  destruct Hsat as [Hsat1 | Hsat2].
  lets Hgpp : IHp1 Hgp Hsat1.
  left.
  eapply Hgpp; eauto.
  lets Hgqq : IHp2 Hgq Hsat2.
  right.
  eapply Hgqq; eauto.
  simpl in Hgood.
  destruct Hgood as [Hgp Hgq].
  destruct Hsat.
  repeat destruct H.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H2.
  subst.
  do 6 eexists.
  splits; eauto.
  destruct Hsat as [x Hsatx].
  lets Hp : H (Hgood x) Hsatx.
  exists x.
  eapply Hp; eauto.
Qed.


Lemma  inv_isr_irrev_prop :
  forall n low I ge le M ir aux abst op, 
    (ge, le, M ,ir, aux, abst, op) |= starinv_isr I low n -> 
    forall le' op',
      (ge, le', M ,ir, aux, abst, op') |= starinv_isr I low n.   
Proof.
  inductions n.
  simpl starinv_isr.
  introv Hsat.
  introv.
  simpl.
  simpl in Hsat.
  destruct Hsat.
  exists x.
  destruct H.
  left; auto.
  right.
  repeat destruct H.
  destruct H0 as (Hm & Hx & Hdj & Hf & Hsa).
  do 6 eexists; splits; eauto.
  destruct aux as [[]].
  eapply  good_inv_prop.
  eapply (invp  (I low)).
  eauto.
  introv Hsat.
  introv.
  simpl starinv_isr.
  simpl starinv_isr in Hsat.
  unfold sat in Hsat.
  fold sat in Hsat.
  simpl substmo in Hsat.
  unfold sat.
  fold sat.
  simpl in *.
  mytac.
  do 6 eexists; splits; eauto.
  destruct H3.
  exists x5.
  left.
  auto.
  mytac.
  exists x5.
  right.
  exists empmem.
  exists x.
  exists x.
  exists empabst.
  exists x2.
  exists x2.
  splits; mytac; eauto.
  destruct aux as [[]].
  eapply   good_inv_prop.
  eapply (invp  (I low)).
  eauto.
Qed.


Lemma INV_irrev_prop :
  forall  I ge le M ir aux abst op, 
    (ge, le, M ,ir, aux, abst, op) |= INV I -> 
    forall le' op',
      (ge, le', M ,ir, aux, abst, op') |= INV I.
Proof.
  introv Hsat.
  introv.
  unfold INV in *.
  unfold inv_ieon in *.
  unfold inv_ieoff in *.
  unfold invlth_isr in *.
  unfold sat in *.
  fold sat in *.
  simpl getabst in *.
  simpl substmo in *.
  simpl empst in *.
  simpl getmem in *.
  simpl gettaskst in *.
  destruct aux as [[ie is] cs].
  simpl getis in *.
  destruct Hsat as (M1 & M2 & M0 & o1 & o2 & o & Hsat).
  destruct Hsat as (Hm0 & Hmj & Hoa & Hjoin & Hst & Hsat).
  exists M1 M2 M0 o1 o2 o; splits; eauto.
  eapply   good_inv_prop.
  eapply (invp  (I (S INUM))).
  eauto.
  simpl getie in *.
  destruct Hsat as [Hsat1 | Hsat2].
  left.
  destruct Hsat1 as (M1' & M3' & M' & o1' & O3' & o' & Heq & Hmjj & Hoo & Habs & Hie & Hsat).
  do 6 eexists; splits; eauto.
  eapply inv_isr_irrev_prop ; eauto.
  right.
  destruct Hsat2 as (M1' & M3' & M' & o1' & O3' & o' & Heq & Hmjj & Hoo & Habs & Hie & Hsat).
  do 6  eexists; splits; eauto.
  do 7 eexists; splits; mytac; eauto.
  mytac;eauto.
  mytac; eauto.
  destruct H4.
  left.
  destruct H;mytac.
  do 6 eexists; splits; mytac; eauto.
  mytac.
  eauto.
  mytac.
  eauto.
  omega.
  assert (gettopis is + 0 + 1 =gettopis is + 1)%nat by omega.
  rewrite H.
  eapply inv_isr_irrev_prop ; eauto.
  right.
  splits;mytac; eauto.
  replace ((gettopis is)) with (gettopis is + 0)%nat in H  by omega.
  auto.
Qed.


Lemma alloc_inv_prev : forall p  vl dl o C o' ks Ms Os ab I,  
                         losallocstep p (curs (salloc  vl dl), (kenil, ks)) o C o' -> 
                         (substaskst o Ms, Os, ab) |= INV I -> 
                         (substaskst o' Ms, Os, ab) |= INV I.
Proof.
  introv Hstep Hsat.
  destruct o as [[[[G E] M ]isr]aux].
  destruct o' as [[[[G' E'] M' ]isr']aux'].
  simpl substaskst in *.
  unfolds in Hstep.
  destruct Hstep as (Hstep &_).
  inverts Hstep; tryfalse.
  inverts H5; tryfalse.
  inverts H; inverts H0;tryfalse.
  inverts H; inverts H0; tryfalse.
  inverts H2.
  inverts H3.
  eapply INV_irrev_prop.
  eauto.
  inverts H2;  inverts H4; eapply INV_irrev_prop; eauto.
  eapply INV_irrev_prop; eauto.
Qed.

Lemma GoodLInvAsrt_change_lenv :
  forall p ge le le' m i l o aop,
    GoodLocalInvAsrt p ->
    (ge, le, m, i, l, o, aop) |= p ->
    (ge, le', m, i, l, o, aop) |= p.
Proof.
  inductions p; intros; simpl in H; tryfalse;
  try solve [simpl in H0; simpl; simpljoin; eauto].
  destruct H.
  destruct H0.
  left.
  eapply IHp1; eauto.
  right.
  eapply IHp2; eauto.
  destruct H.
  simpl in H0; simpljoin.
  simpl.
  do 6 eexists; splits; eauto.
  destruct H1.
  exists x.
  eapply H; eauto.
Qed.

Lemma local_inv_E_irev:
  forall G E M  isr aux li t E' O,
    satp (G, E, M, isr, aux) O (CurLINV li t) ->
    satp (G, E',  M , isr, aux) O (CurLINV li t).
Proof.
  intros.
  unfold satp in *.
  intros.
  pose proof H aop.
  unfold CurLINV in *.
  destruct H0.
  exists x.
  unfold sat in *; fold sat in *.
  simpl assertion.getmem in *.
  simpl getabst in *.
  simpl substmo in *.
  simpljoin.
  do 6 eexists.
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  clear - H9.
  unfold LINV in *.

  sep split in H9.
  sep split; auto.
  eapply GoodLInvAsrt_change_lenv; eauto.
  unfolds in H.
  apply H.
Qed.


Lemma alloc_local_inv_prev : 
  forall p  o  O C o' C' li t ,  
    losallocstep p C o C' o' -> 
    satp o O (CurLINV li t) ->
    satp o' O (CurLINV li t). 
Proof.
  intros.
  unfolds in H.
  destruct H.
  unfolds in H1.
  simp join.
  assert (x= nil \/ x <> nil) by tauto.
  destruct H1.
  apply H3 in H1.
  simp join.
  inverts H; tryfalse.
  inverts H6; tryfalse.
  inverts H; inverts H7; tryfalse.
  inverts H; inverts H7; tryfalse.

  (*zhanghui begin*)
  assert(satp (ge, le', M, i, au) O (CurLINV li t)).
  eapply local_inv_E_irev; eauto.
  
  unfolds in H5; simpljoin.
  eapply join_satp_local_inv; eauto.
  unfolds; eauto.
  do 6 eexists; splits; eauto.
  join auto.

  assert(satp (ge, le', M, i, au) O (CurLINV li t)).
  eapply local_inv_E_irev; eauto.
  
  unfolds in H5; simpljoin.
  eapply join_satp_local_inv; eauto.
  unfolds; eauto.
  do 6 eexists; splits; eauto.
  join auto.
  (**)
  
  apply H4 in H1.
  simp join.
  inverts H; tryfalse.
  inverts H1; inverts H7; tryfalse.
  inverts H.

  (*zhanghui begin*)
  assert(v :: vl <> nil).
  intro; tryfalse.
  apply H4 in H; simpljoin.
  unfolds in H7; simpljoin.
  
  assert (satp (x5, x8, x9, x11, x12) O (CurLINV li t)).
  eapply local_inv_E_irev; eauto.

  eapply join_satp_local_inv; eauto.
  unfolds; eauto.
  do 6 eexists; splits; eauto.
  join auto.
Qed.
  
Lemma joinm2_ex_join : 
  forall o  M1 M2 o', 
    joinm2 o M1 M2 o'
    -> exists M3, join M1 M2 M3 /\  joinmem o M3 o'.
Proof.
  intros.
  unfolds in H; simpljoin.
  unfold joinmem in *; simpljoin.
  exists (merge M1 M2).
  split.
  eapply map_join_merge.
  join auto.
  do 6 eexists; splits; eauto.  
  eapply mem_join_join_merge23_join; eauto.
Qed.

  
Lemma loadbytes_mono: 
  forall m M m' l n v ,  
    join m M m' -> 
    loadbytes m l n = Some v ->
    loadbytes m' l n = loadbytes m l n.
Proof.
  intros.
  generalize dependent l.
  generalize dependent v.
  induction n.
  intros.
  simpl. auto.
  intros.
  destruct l. 
  simpl. simpl in H0.

  unfold get in *; simpl in *.
  remember (HalfPermMap.get m (b, o)) as bb.
  destruct bb;tryfalse.
  destruct b0.

  symmetry in Heqbb.
  lets Hx: mem_join_get_get_l H Heqbb; simpljoin.
  unfolds in H1; simpl in H1.
  rewrite H1.
  
  remember (loadbytes m (b, (o+1)%Z) n) as v1.
  destruct v1;tryfalse.
  erewrite IHn;rewrite<-Heqv1;eauto.
Qed.


Lemma evaltype_irrev_mem : 
  forall  e G E M  M', evaltype e (G,E,M) = evaltype e (G,E,M').
Proof.
  inductions e;intros; simpl; auto;
  try   rewrite IHe with (M:=M)(M':= M'); auto;  tryfalse. 
  rewrite IHe1 with (M:=M)(M':= M'); auto;
  rewrite IHe2 with (M:=M)(M':= M'); auto.
  destruct e; simpl in IHe; tryfalse; auto.
  lets Ihe : IHe G E M M'.
  remember (evaltype e (G, E, M)) as t1.
  remember(evaltype e (G, E, M')) as t2.
  destruct t1; destruct t2; tryfalse; auto.
  destruct t; destruct t0; tryfalse; auto.
  inverts Ihe; auto.
  destruct t; tryfalse; auto.
  destruct t; tryfalse; auto.
  rewrite IHe1 with (M:=M)(M':= M'); auto;
  rewrite IHe2 with (M:=M)(M':= M'); auto.
Qed.


Lemma evaltype_mono: 
  forall e ge le m M m' ,  
    join m M m' -> 
    evaltype e (ge, le, m') = evaltype e (ge, le, m).
Proof.
  intros.
  apply evaltype_irrev_mem; eauto.
Qed.

Lemma match_loadbytes :
  forall t m M m' b v, 
    join m M m' ->
    match loadbytes m (b, 0%Z) (typelen t) with
      | Some bls => Some (decode_val t bls)
      | None => None
    end = Some v ->
    match loadbytes m' (b, 0%Z) (typelen t) with
      | Some bls => Some (decode_val t bls)
      | None => None
    end =
    match loadbytes m (b, 0%Z) (typelen t) with
      | Some bls => Some (decode_val t bls)
      | None => None
    end.
Proof.
  intros.
  remember (loadbytes m (b, 0%Z) (typelen t)) as v1.
  destruct v1;tryfalse.
  symmetry in Heqv1.
  erewrite loadbytes_mono;eauto.
  rewrite Heqv1;auto.
Qed.

Lemma loadm_mono: 
  forall m M m' t l v, 
    join m M m' ->
    loadm t m l = Some v -> 
    loadm t m' l = loadm t m l .
Proof.
  intros.
  destruct l. simpl in *.
  remember (loadbytes m (b, o) (typelen t)) as bb.
  destruct bb.
  symmetry in Heqbb.
  assert (loadbytes m' (b, o) (typelen t) = Some l).
  erewrite loadbytes_mono;eauto.
  rewrite H1. auto.
  inversion H0.
Qed.

Lemma load_mono: 
  forall m M m' t l v, 
    join m M m' ->
    load t m l = Some v ->
    load t m' l = load t m l .
Proof.
  unfold load;intros;destruct t;try eapply loadm_mono;eauto.
Qed.

Lemma getoff_mono: 
  forall ge le m M m' b o i e, 
    join m M m' ->
    getoff b o i e (le, ge, m') = getoff b o i e (le, ge, m).
Proof.
  intros.
  unfold getoff.
  erewrite evaltype_mono;eauto.
Qed.



Lemma evalvaladdr_mono: 
  forall ge le e m M m' v ,
    ( 
      join m M m' -> 
      evalval e (ge, le, m) = Some v -> 
      evalval e (ge, le, m') = evalval e (ge, le, m)
    ) /\
    ( 
      join m M m' ->
      evaladdr e (ge, le, m) = Some v -> 
      evaladdr e (ge, le, m') = evaladdr e (ge, le, m)
    ).
Proof.
  inductions e;introv;intros;split;auto;intros;eauto.
  unfold evalval;simpl;unfold evalval in H0;simpl in H0;eauto.
  destruct (get le v),(get ge v);tryfalse.
  destruct p;tryfalse. 
  destruct t;tryfalse;try (eapply match_loadbytes;eauto).
  auto.
  destruct p;tryfalse. 
  destruct t;tryfalse;try (eapply match_loadbytes;eauto).
  auto.
  destruct p;tryfalse. 
  destruct t;tryfalse;try (eapply match_loadbytes;eauto).
  auto.
  simpl. simpl in H0. erewrite evaltype_mono;eauto.
  destruct (evaltype e (ge, le, m)) as [];eauto.
  destruct (uop_type t u) as [];eauto.  
  remember (evalval e (ge, le, m)) as v1.
  destruct v1;tryfalse.
  generalize (IHe m M m' v0).
  intros. destruct H1. 
  rewrite H1;auto.
  rewrite<-Heqv1. auto.

  simpl. simpl in H0.
  erewrite evaltype_mono;eauto.
  destruct (evaltype e1 (ge, le, m)) as [];eauto.
  erewrite evaltype_mono;eauto.
  destruct (evaltype e2 (ge, le, m)) as [];eauto.
  destruct (bop_type t t0 b) as [];eauto.
  remember (evalval e1 (ge, le, m)) as v1.
  destruct v1;tryfalse.
  remember (evalval e2 (ge, le, m)) as v2.
  destruct v2;tryfalse.
  symmetry in Heqv1,Heqv2.
  generalize (IHe1 m M m' v0).
  intros. destruct H1. erewrite H1;auto.
  generalize (IHe2 m M m' v1).
  intros. destruct H3. erewrite H3;auto.
  rewrite Heqv1,Heqv2;eauto.

  simpl. simpl in H0.
  erewrite evaltype_mono;eauto.
  destruct (evaltype e (ge, le, m)) as [];eauto.
  destruct t as [];eauto.
  remember (evalval e (ge, le, m)) as v1.
  destruct v1;tryfalse.
  destruct v0;tryfalse.
  generalize (IHe m M m' (Vptr a)).
  intros. destruct H1. 
  rewrite H1;auto.
  rewrite<-Heqv1.
  eapply load_mono;eauto.

  simpl in *.
  generalize (IHe m M m' v).
  intros. destruct H1.
  apply H1;eauto. 

  simpl. simpl in H0.
  destruct e as [];eauto.
  erewrite evaltype_mono;eauto.
  destruct (evaltype e (ge, le, m)) as [];eauto.
  destruct t; tryfalse; auto.
  simpl in IHe.
  eapply IHe;eauto.
  erewrite evaltype_mono;eauto.
  destruct (evaltype (efield e i) (ge, le, m)) as [];eauto.
  generalize (IHe m M m' v).
  intros. destruct H1.
  rewrite H2;auto.
  erewrite evaltype_mono;eauto.
  destruct (evaltype (earrayelem e1 e2) (ge, le, m)) as [];eauto.
  generalize (IHe m M m' v).
  intros. destruct H1.
  rewrite H2;auto.

  simpl. simpl in H0.
  erewrite evaltype_mono;eauto.
  destruct (evaltype e (ge, le, m)) as [];eauto.  
  destruct t as [];eauto.
  destruct (memory.ftype i d) as [];eauto.
  remember (evaladdr e (ge, le, m)) as addr.
  destruct addr as [];tryfalse.
  generalize (IHe m M m' v0).
  intros. destruct H1.
  rewrite H2;auto.
  rewrite<-Heqaddr.
  destruct v0;tryfalse.
  destruct a;tryfalse.
  erewrite getoff_mono;eauto.
  destruct (getoff b (Int.unsigned i1) i e (ge, le, m));tryfalse.
  eapply load_mono;eauto.
  
  simpl. simpl in H0.
  remember (evaladdr e (ge, le, m)) as addr.
  destruct addr as [];tryfalse.
  generalize (IHe m M m' v0).
  intros. destruct H1.
  rewrite H2;auto.
  rewrite<-Heqaddr.
  destruct v0;tryfalse.
  destruct a;tryfalse.
  erewrite getoff_mono;eauto.

  
  simpl. simpl in H0.
  erewrite evaltype_mono;eauto.
  destruct (evaltype e (ge, le, m)) as [];eauto.
  destruct t0;tryfalse.
  destruct t ;tryfalse;simpl in *.
  remember (evalval e (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe m M m' v0).
  intros.
  destruct H1.
  symmetry in Heqaddr.
  lets Hx:H1 H Heqaddr.
  rewrite Hx;auto.
  
  
  destruct t;tryfalse;simpl in *.
  remember (evalval e (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe m M m' v0).
  intros.
  destruct H1.
  symmetry in Heqaddr.
  lets Hx:H1 H Heqaddr.
  rewrite Hx;auto.
  rewrite Heqaddr.
  auto.
  remember (evalval e (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe m M m' v0).
  intros.
  destruct H1.
  symmetry in Heqaddr.
  lets Hx:H1 H Heqaddr.
  rewrite Hx;auto.
  rewrite Heqaddr.
  auto.
  remember (evalval e (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe m M m' v0).
  intros.
  destruct H1.
  symmetry in Heqaddr.
  lets Hx:H1 H Heqaddr.
  rewrite Hx;auto.
  rewrite Heqaddr.
  auto.
  destruct t;tryfalse;simpl in *.
  remember (evalval e (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe m M m' v0).
  intros.
  destruct H1.
  symmetry in Heqaddr.
  lets Hx:H1 H Heqaddr.
  rewrite Hx;auto.
  rewrite Heqaddr.
  auto.
  remember (evalval e (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe m M m' v0).
  intros.
  destruct H1.
  symmetry in Heqaddr.
  lets Hx:H1 H Heqaddr.
  rewrite Hx;auto.
  rewrite Heqaddr.
  auto.
  remember (evalval e (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe m M m' v0).
  intros.
  destruct H1.
  symmetry in Heqaddr.
  lets Hx:H1 H Heqaddr.
  rewrite Hx;auto.
  rewrite Heqaddr.
  auto.
  destruct t;tryfalse;simpl in *.
  remember (evalval e (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe m M m' v0).
  intros.
  destruct H1.
  symmetry in Heqaddr.
  lets Hx:H1 H Heqaddr.
  rewrite Hx;auto.
  rewrite Heqaddr.
  auto.
  remember (evalval e (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe m M m' v0).
  intros.
  destruct H1.
  symmetry in Heqaddr.
  lets Hx:H1 H Heqaddr.
  rewrite Hx;auto.
  rewrite Heqaddr.
  auto.
  remember (evalval e (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe m M m' v0).
  intros.
  destruct H1.
  symmetry in Heqaddr.
  lets Hx:H1 H Heqaddr.
  rewrite Hx;auto.
  rewrite Heqaddr.
  auto.

  destruct t;simpl in *;tryfalse.
  remember (evalval e (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe m M m' v0).
  intros.
  destruct H1.
  symmetry in Heqaddr.
  lets Hx:H1 H Heqaddr.
  rewrite Hx;auto.

  destruct t;simpl in *;tryfalse.
  remember (evalval e (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe m M m' v0).
  intros.
  destruct H1.
  symmetry in Heqaddr.
  lets Hx:H1 H Heqaddr.
  rewrite Hx;auto.
  
  simpl. simpl in H0.
  erewrite evaltype_mono;eauto.
  destruct (evaltype e1 (ge, le, m)) as [];eauto.
  destruct t ;tryfalse.
  erewrite evaltype_mono;eauto.
  destruct (evaltype e2 (ge, le, m)) as [];eauto.
  destruct t0;tryfalse.
  remember (evalval e1 (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe1 m M m' v0).
  intros.
  destruct H1.
  rewrite H1;auto.
  rewrite<-Heqaddr.
  destruct v0;tryfalse.
  destruct a ;tryfalse.
  remember (evalval e2 (ge, le, m)) as v2.
  destruct v2;tryfalse.
  generalize (IHe2 m M m' v0).
  intros; destruct H3.
  rewrite H3;auto.
  rewrite<-Heqv2.
  destruct (vtoZ v0);tryfalse.
  destruct v0;tryfalse.
  eapply load_mono;eauto.
  destruct v0;tryfalse.
  eapply load_mono;eauto.
  

  remember (evalval e1 (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe1 m M m' v0).
  intros; destruct H1.
  rewrite H1;auto.
  rewrite<-Heqaddr.
  destruct v0;tryfalse.
  destruct a ;tryfalse.
  remember (evalval e2 (ge, le, m)) as v2.
  destruct v2;tryfalse.
  generalize (IHe2 m M m' v0).
  intros; destruct H3.
  rewrite H3;auto.
  rewrite<-Heqv2.
  destruct (vtoZ v0);tryfalse.
  destruct v0;tryfalse.
  eapply load_mono;eauto.
  destruct v0;tryfalse.
  eapply load_mono;eauto.

  
  remember (evalval e1 (ge, le, m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe1 m M m' v0).
  intros; destruct H1.
  rewrite H1;auto.
  rewrite<-Heqaddr.
  destruct v0;tryfalse.
  destruct a ;tryfalse.
  remember (evalval e2 (ge, le, m)) as v2.
  destruct v2;tryfalse.
  generalize (IHe2 m M m' v0).
  intros; destruct H3.
  rewrite H3;auto.
  rewrite<-Heqv2.
  destruct (vtoZ v0);tryfalse.
  destruct v0;tryfalse.
  eapply load_mono;eauto.
  destruct v0;tryfalse.
  eapply load_mono;eauto.

  simpl;simpl in H0. 
  erewrite evaltype_mono;eauto.
  destruct (evaltype e2 (ge,le,m));tryfalse.
  destruct t0;tryfalse.
  remember (evalval e1 (ge,le,m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe1 m M m' v0).
  intros. destruct H1.
  rewrite H1;auto.
  rewrite<-Heqaddr.
  remember (evalval e2 (ge,le,m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe2 m M m' v1).
  intros. destruct H3.
  rewrite H3;auto.
  rewrite<-Heqaddr0.
  destruct v0;tryfalse;destruct a ;tryfalse.
  destruct v1;tryfalse.
  eapply load_mono;eauto.
  destruct v0;tryfalse.
  destruct a;tryfalse.
  
  remember (evalval e1 (ge,le,m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe1 m M m' v0).
  intros. destruct H1.
  rewrite H1;auto.
  rewrite<-Heqaddr.
  remember (evalval e2 (ge,le,m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe2 m M m' v1).
  intros. destruct H3.
  rewrite H3;auto.
  rewrite<-Heqaddr0.
  destruct v0;tryfalse;destruct a ;tryfalse.
  destruct v1;tryfalse.
  eapply load_mono;eauto.
  destruct v0;tryfalse.
  destruct a;tryfalse.

  remember (evalval e1 (ge,le,m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe1 m M m' v0).
  intros. destruct H1.
  rewrite H1;auto.
  rewrite<-Heqaddr.
  remember (evalval e2 (ge,le,m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe2 m M m' v1).
  intros. destruct H3.
  rewrite H3;auto.
  rewrite<-Heqaddr0.
  destruct v0;tryfalse;destruct a ;tryfalse.
  destruct v1;tryfalse.
  eapply load_mono;eauto.
  destruct v0;tryfalse.
  destruct a;tryfalse.

  simpl;simpl in H0. 
  erewrite evaltype_mono;eauto.
  destruct (evaltype e1 (ge,le,m));tryfalse.
  destruct t;tryfalse.
  remember (evalval e1 (ge,le,m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe1 m M m' v0).
  intros. destruct H1.
  rewrite H1;auto.
  rewrite<-Heqaddr.
  remember (evalval e2 (ge,le,m)) as addr.
  destruct addr;tryfalse.
  generalize (IHe2 m M m' v1).
  intros. destruct H3.
  rewrite H3;auto.
  rewrite<-Heqaddr0.
  destruct v0;tryfalse;destruct a ;tryfalse.
  destruct v1;tryfalse.
  auto.
  destruct v0;tryfalse.
  destruct a;tryfalse.
  
  remember (evalval e1 (ge,le,m)) as addr.
  destruct addr;tryfalse. 
  generalize (IHe1 m M m' v0).
  intros. destruct H1.
  rewrite H1;auto.
  rewrite<-Heqaddr.
  destruct v0;tryfalse.
  destruct a ;tryfalse.
  remember (evalval e2 (ge, le, m)) as v2.
  destruct v2;tryfalse.
  generalize (IHe2 m M m' v0).
  intros. destruct H3.
  rewrite H3;auto.
  rewrite<-Heqv2.
  destruct (vtoZ v0);auto.
Qed.


Lemma evalval_mono: 
  forall ge le e m M m' v ,
    (
      join m M m' -> 
      evalval e (ge, le, m) = Some v -> 
      evalval e (ge, le, m') = evalval e (ge, le, m)
    ). 
Proof.
  intros.
  generalize (evalvaladdr_mono ge le e m M m' v).
  intros. destruct H1.
  apply H1;eauto.
Qed.

Lemma fresh_exist : 
  forall m, (exists b,fresh m b).
Proof.
  intros.
  generalize MemoryNotFull.
  intros.
  generalize (H m).
  intros.
  unfold FullMemory in H0.
  apply not_all_ex_not in H0.
  destruct H0. exists x.
  unfold fresh.
  intros.
  red. intros. apply H0.
  exists i. subst. eauto.
Qed.

Lemma storebytes_mono: 
  forall m M m' m0 l vl,  
    join m M m' ->
    storebytes m l vl = Some m0 ->
    (exists m0',storebytes m' l vl = Some m0').
Proof.
  introv. intro.
  generalize l.
  generalize m0.
  induction vl.
  intros. eexists.
  simpl. auto.
  intros.
  simpl. simpl in H0.
  destruct l0;tryfalse.
  unfold get in *; simpl in *.
  remember (HalfPermMap.get m (b, o)) as v.
  destruct v;tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  assert (get m' (b, o) = Some (true, c)).

  eapply mem_join_get_get_l_true; eauto.
  unfold get in H1; simpl in H1.
  rewrite H1.
  remember (storebytes m (b, (o+1)%Z) vl) as mm0.
  destruct mm0;tryfalse. 
  generalize (IHvl m2 (b, (o+1)%Z)).
  intros. symmetry in Heqmm0. 
  apply H2 in Heqmm0.
  destruct Heqmm0.
  rewrite H3. 
  eauto.
Qed.

Lemma store_mono: 
  forall m M m' m0 a t v, 
    join m M m' ->
    store t m a v = Some m0 -> 
    (exists m0',store t m' a v = Some m0').
Proof.
  intros. 
  subst. simpl in H0. simpl.
  unfold store.
  unfold store in H0.
  destruct a;tryfalse.
  destruct (encode_val t v);tryfalse.
  eapply storebytes_mono;eauto.
  eapply storebytes_mono;eauto.
Qed.

Lemma allocb_get_some :
  forall m b n i off,
    (off<n)%nat->
    exists v,
      get (allocb m b i n) (b, (i + Z_of_nat off)%Z) = Some (true,v).
Proof.
  intros.
  gen m i off.
  induction n.
  intros.
  omega.
  intros.
  destruct off.
  simpl.
  exists Undef.
  rewrite Z.add_0_r.
  rewrite set_a_get_a; auto.
  
  rewrite Nat2Z.inj_succ.
  assert (Z.succ (Z.of_nat off) = 1 + (Z.of_nat off))%Z.
  omega.
  rewrite H0.
  rewrite Z.add_assoc.
  simpl.
  rewrite set_a_get_a'.
  apply IHn.
  omega.

  intro; inverts H1.
  assert (Z.of_nat off >=0)%Z.
  omega.
  assert (i + 1 + Z.of_nat off >i)%Z.
  omega.
  rewrite<-H3 in H2.
  omega.
Qed.
  
Lemma allocb_storebytes_mem_ex :
  forall vl n m b i,
    ((length vl) + i = n)%nat -> 
    (exists m', storebytes (allocb m b 0%Z n) (b, Z_of_nat i) vl = Some m').
Proof.
  intros.
  gen i.
  induction vl.
  simpl.
  eexists;eauto.
  simpl. 
  intros.
  generalize allocb_get_some.
  intros.
  generalize (H0 m b n 0 i)%Z.
  intros.
  assert (i<n)%nat.
  omega.
  apply H1 in H2.
  destruct H2.
  simpl in H2.

  change (
      (fun x =>
         exists m',
           match x with
             | Some (true, _) =>
               match storebytes (allocb m b 0%Z n) (b, Z.of_nat i + 1)%Z vl with
                 | Some m'0 => Some (set m'0 (b, Z.of_nat i) (true, a))
                 | None => None
               end
             | Some (false, _) => None
             | None => None
           end = Some m') (get (allocb m b 0%Z n) (b, Z.of_nat i))).
  rewrite H2.

  generalize (IHvl (i+1)%nat).
  intros.
  assert ((length vl + (i + 1))%nat = n).
  omega.
  apply H3 in H4.
  destruct H4.
  rewrite Nat2Z.inj_add in H4.
  simpl in H4.
  rewrite H4.
  eexists;eauto.
Qed.

Lemma allocb_store_mem_ex : 
  forall t m b v, 
    (exists m', store t (allocb m b 0%Z (typelen t)) (b, BinNums.Z0) v = Some m').
Proof.
  intros.
  unfold store.
  generalize encode_val_length.
  intros.
  generalize (H t v).
  intros.
  remember (typelen t) as n.
  remember (encode_val t v) as vl.
  assert (0 = Z_of_nat 0)%Z.
  auto.
  rewrite H1.
  eapply allocb_storebytes_mem_ex.
  omega.
Qed.


Lemma freeb_mono: 
  forall m M m' m0 b i n, 
    join m M m' ->
    freeb m b i n = Some m0 -> 
    (exists m0',freeb m' b i n = Some m0').
Proof.
  introv. intro. 
  generalize i m0.
  unfold free.
  induction n.
  intros.
  simpl. eexists. auto.
  intros.
  simpl.
  simpl in H0.

  unfold get in *; simpl in *.
  destruct (HalfPermMap.get m (b, i0)) eqn : eq1; tryfalse.
  destruct b0.
  destruct b0; tryfalse.

  erewrite mem_join_get_get_l_true; eauto.
  remember (freeb m b (i0 + 1) n) as mm0.
  destruct mm0;tryfalse.
  generalize (IHn (i0+1)%Z m2).
  intros. symmetry in Heqmm0. apply H1 in Heqmm0.
  destruct Heqmm0. rewrite H2.
  eexists;auto.
Qed.


Lemma free_mono: 
  forall m M m' m0 b t,  
    join m M m' ->
    free t b m = Some m0 ->
    (exists m0',free t b m' = Some m0').
Proof.
  intros.
  unfold free.
  unfold free in H0.
  eapply freeb_mono;eauto.
Qed.



Lemma cstep_safe_mono: 
  forall p C m M m', 
    ~(cstepabt p C m) ->
    SysmemJoinM m M m' -> 
    ~(cstepabt p C m'). 
Proof.
  intros.
  red. intros.
  apply H. clear H.
  unfold cstepabt.
  red. intros.
  apply H1.
  destruct H0 as (G & E & M0 & M0' & H0).
  destructs H0.
  subst.
  destruct H as [C'].
  destruct H as [m0].
  destruct H as [ev].
  destruct H.
  inversion H;subst.
  inversion H2;subst;do 3 eexists;left;eapply expr_step;
  try solve [ constructors;erewrite evalval_mono;eauto
             |constructors;eauto;erewrite evaltype_mono;eauto
             |constructors;eauto].
  eapply eaelemaddr_step.
  erewrite evaltype_mono;
    eauto.
  
  eapply eaelem_step.
  erewrite evaltype_mono;
    eauto.
  
  eapply ecast_step;eauto.
  erewrite evaltype_mono;eauto.

  
  eapply ecastnull_step;eauto.
  erewrite evaltype_mono;eauto.

  
  eapply ecastcomptr_step;eauto.
  erewrite evaltype_mono;eauto.

  inverts H0.
  assert (load t M0' (addrval_to_addr a) = load t M1 (addrval_to_addr a)). eapply load_mono;eauto.
  rewrite H4 in H0.
  constructors;eauto. 
  (* cstepev *)
  Focus 2.
  inversion H;subst. do 3 eexists. right. constructors. auto. auto. auto.
  inversion H2;subst;constructors. auto. erewrite evalval_mono;eauto.
  (* sstep *)
  generalize (fresh_exist M0').
  intros. destruct H0.
  inverts H2;
    try solve [do 3 eexists;left;eapply stmt_step;eauto;constructors;eauto|
               do 3 eexists;left;eapply stmt_step;eauto;constructors;eauto;
               try erewrite evalval_mono;try erewrite evaltype_mono;try erewrite<-typematch_mono;eauto].
  (* kassign *)
  inverts H4.
  eapply store_mono in H6;eauto. destruct H6. simpl in *. 
  do 3 eexists;left;eapply stmt_step;eauto;constructors;eauto.
  (* sclloc f v::vl *)
  inverts H4.
  generalize (allocb_store_mem_ex t M0' x v).
  intros. destruct H2.
  do 3 eexists;left;eapply stmt_step;eauto.
  eapply sallocp_step.
  auto. auto. 
  unfold alloc. exists x. 
  split;eauto. split;eauto. split;eauto.
  destruct H6. apply H4.
  eapply EnvMod.set_a_get_a. eapply identspec.eq_beq_true;auto.
  eauto.
  (* salloc f nil *)
  inverts H4.
  do 3 eexists;left;eapply stmt_step;eauto;constructors;eauto.
  unfold alloc. exists x.
  split;eauto. split;eauto. split;eauto.
  destruct H6. apply H2.
  (* sfree *)
  inverts H4.
  eapply free_mono in H6;eauto. destruct H6.
  do 3 eexists;left;eapply stmt_step;eauto;constructors;eauto.
  (*
(* kif false *)
  do 3 eexists;left;eapply stmt_step;eauto;eapply sviff_step;auto.
(* kwhile false *)
  do 3 eexists;left;eapply stmt_step;eauto;eapply svwhilef_step;auto.
   *)
  Grab Existential Variables.
  trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. 
  trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. 
  trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. 
  trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. 
  trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial.
  trivial.
  trivial. trivial.
Qed.

Lemma notabt_frame :
  forall p C o M o1, 
    joinmem o M o1-> 
    ~ loststepabt p C o ->
    ~ loststepabt p C o1.
Proof. 
  intros.
  apply Classical_Prop.NNPP in H0.
  destruct H0 as (o' & C' & Hlo).
  unfold loststepabt.
  red.
  intro.
  apply H0.
  clear H0.
  inverts Hlo;
    destruct H as ( X & XX & M1 & M2 & ir0 & ls & H);
    destructs H;
    inverts H;
    subst.
  assert (~ cstepabt p C (X, XX, M2)).
  eapply cstep_safe_mono.
  red.
  intro.
  apply H.
  do 2 eexists;exists Vundef;eauto.
  unfold SysmemJoinM;do 4 eexists;eauto.
  apply Classical_Prop.NNPP in H.
  do 4 destruct H.
  do 2 eexists.
  eapply ostc_step;eauto.
  inverts H0;
    inverts H;
    inverts H0;
    inverts H1;
    inverts H3.
  do 2 eexists;eapply exint_step;eauto. 
  do 2 eexists;eapply eoi_step;eauto.
  do 2 eexists;eapply cli_step;eauto.
  do 2 eexists;eapply sti_step;eauto.
  do 2 eexists;eapply encrit_step;eauto.
  do 2 eexists;eapply excrit_step;eauto.
  lets Hx:store_mono H1 H3.
  destruct Hx.
  do 2 eexists;eapply checkis_step;eauto.
Qed.

Lemma alloc_irev_prog :
  forall p  vl dl ks o,  
    ~ loststepabt p (curs (salloc  vl dl), (kenil, ks)) o -> 
    forall p',  ~ loststepabt p' (curs (salloc  vl dl), (kenil, ks)) o .
Proof.
  intros.
  red. intros. apply H.
  unfold loststepabt in *.
  red. intros. apply H0.
  clear H H0.
  destruct H1 as (C' & tst' & H1).
  exists C' tst'.
  inverts H1;tryfalse.
  inverts H;tryfalse.
  inverts H0;inverts H1;tryfalse.
  inverts H0;inverts H1;tryfalse;
  constructors;eauto;
  eapply stmt_step;eauto;
  constructors;eauto.
Qed.


Lemma alloc_step_msim_hold :
  forall p FSpec sd C o  gamma O I r ri q li t, 
    isallocate C -> 
    satp o O (CurLINV li t) ->
    ~ loststepabt p C o ->
    (forall p o' C', losallocstep p C o C' o' -> MethSimMod FSpec sd C' o'  gamma O li I r ri q t) ->
    MethSimMod FSpec sd C o gamma O li I r ri q t .
Proof.
  introv Hisa Hsat Hnotabt  Hforall.
  unfolds in Hisa.
  destruct Hisa as ( vl & dl & ks & Hc & Hnil & Hlen).
  subst.
  constructors;introv Hfalse;tryfalse.
  introv Hsat1  Hjm2 Hj Hlst.
  lets Hre :  alloc_locality  Hjm2 Hlst; eauto.
  destruct Hre as (o'  & Hlastep & Hjm).
  lets Hf : Hforall Hlastep. 
  exists gamma OO. 
  exists o' Ms O Os.  
  splits; auto. 
  constructors.
  unfold satp in *.
  intros.
  eapply alloc_inv_prev; eauto.
  unfold satp.
  intros.
  eapply alloc_local_inv_prev; eauto.
  introv Hsat1  Hj2 Hdisj.
  lets Hjj : joinm2_ex_join  Hj2.
  destruct Hjj as (M''&Hjmm & Hjmm').
  eapply notabt_frame; eauto.
  eapply  alloc_irev_prog; eauto.
Qed.


Lemma allocstep_imply_isalloc :
  forall C o o',allocstep C o o' -> isallocate C.
Proof.
  introv His.
  unfolds.
  unfolds in His.
  destruct His as (vl&dl&ks&x&t&Hc&Hle& Hv1& Hv2).
  do 3 eexists; splits; eauto.
  intro;tryfalse.
Qed.

Lemma losallocstep_irev_prog :
  forall p C o C' o',   losallocstep p C o C' o' -> 
                        forall p',  losallocstep p' C o C' o' .
Proof.
  intros.
  inverts H.
  unfold allocstep in H1.
  destruct H1 as (vl & dl & ks & x & t & H1).
  destructs H1.
  inverts H.
  clear H4.
  inverts H0;tryfalse.
  inverts H;tryfalse.
  inverts H0;inverts H4;tryfalse.
  inverts H0;inverts H4;tryfalse.
  constructors.
  constructors;eauto.
  eapply stmt_step;eauto.
  constructors;eauto.
  unfold allocstep.
  do 5 eexists;split;eauto.
  constructors.
  constructors;eauto.
  eapply stmt_step;eauto.
  constructors;eauto.
  unfold allocstep.
  do 5 eexists;split;eauto.
Qed.

Lemma alloc_code_eq : 
  forall p p' C o C' o' C'' o'',   
    losallocstep p C o C' o' -> 
    losallocstep p' C o C'' o'' -> C' = C''.
Proof.
  introv Hlos Hlos'.
  unfolds in Hlos.
  unfolds in Hlos'.
  destruct Hlos as (Hstep1 & Hisa).
  destruct Hlos' as(Hstep2 & _).
  unfolds in Hisa.
  destruct Hisa as (vl & dl & ks & x & t & Hc & Hlen & Hnil & Hnnil).
  subst.
  inverts Hstep1; inverts Hstep2; tryfalse.
  inverts H;inverts H7; tryfalse.
  inverts H0;inverts H; inverts H1; inverts H2; tryfalse.
  apply eq_sym in H0.
  apply eq_sym in H.
  inversion H0.
  inversion H.
  subst.
  inverts H1; tryfalse.
  inversion H; subst.
  inverts H2; tryfalse.
  inversion H0; inversion H; subst.
  inverts H.
  inverts H1; inverts H2;tryfalse; auto.
Qed.


Definition env_domain_eq x y := forall a, EnvMod.indom x a <-> EnvMod.indom y a. 

Lemma env_domain_eq_imply_alloc_exist : 
  forall le le1 le' x t M M' M1,
    env_domain_eq le le1 ->
      alloc x t le M le' M' ->
        exists le1' M1', alloc x t le1 M1 le1' M1'.
Proof.
  intros.
  destruct H0.
  destructs H0.
  generalize (fresh_exist M1).
  intros.
  destruct H4.
  exists (EnvMod.set le1 x (x1, t)).
  exists (allocb M1 x1 0%Z (typelen t)).
  unfold alloc.
  exists x1.
  split;eauto.
  split;eauto.
  split;eauto.
  red.
  intros.
  apply H2.
  apply H.
  auto.
Qed.

Lemma allocstep_exist : 
  forall p C C' o o' o1 ,
    losallocstep p C o C' o'->
    env_domain_eq (get_lenv (fst (fst o))) (get_lenv (fst (fst o1))) ->
    exists o1', losallocstep p C o1 C' o1'.
Proof.
  introv Hlo Henv.
  inverts Hlo.
  destruct H0.
  destruct H0 as (dl & ks & x0 & t & Halloc).
  destructs Halloc.
  subst.
  inverts H;tryfalse.
  inverts H0;tryfalse.
  inverts H.
  inverts H4;tryfalse.
  inverts H.
  inverts H4;tryfalse.
(* case 2 *)
  destruct o1 as [[[[ge1 le1] M1] i1] au1].
  simpl in Henv.
  lets H5 : env_domain_eq_imply_alloc_exist M1 Henv H15.
  destruct H5 as (le1' & M1' & H5).
  destruct H5 as (b1 & H5).
  destructs H5.
  lets Hstore : allocb_store_mem_ex t M1 b1 v.
  destruct Hstore as (m' & Hstore).
  eexists.
  constructors.
  eapply ostc_step.
  eapply stmt_step;eauto.
  constructors;auto.
  3:apply Hstore.
  unfold alloc.
  exists b1.
  split;eauto.
  rewrite H5.
  EnvMod.rewrite_get.
  eauto.
  rewrite set_a_get_a; auto.
  
  unfold allocstep.
  do 5 eexists;split;eauto.
  split;eauto.
  split.
  intros.
  false.
  intros.
  apply H3 in H6.
  destruct H6 as (l & v0 & vl' & M0 & H6).
  destructs H6.
  unfold joinenvmem in *.
  do 7 destruct H8.
  destructs H8.
  inverts H6.
  inverts H8.
  inverts H9.
  lets Hmaps: mapstoval_exist (b1,0%Z) t v0 true.
  destruct Hmaps as (M2 & Hmaps).
  do 4 eexists.
  split;eauto.
  split;eauto.
  do 7 eexists;split;eauto.
  split;eauto.
  split. rewrite H5.
  assert (EnvMod.get (EnvMod.sig x0 (b1,t)) x0 = Some (b1,t)).
  apply EnvMod.get_a_sig_a. eapply identspec.eq_beq_true;eauto.
  apply EnvMod.join_sig_set.
  auto.
  eapply join_mapstoval_store_allocb;eauto.
(* case 1 *)
  destruct o1 as [[[[ge1 le1] M1] i1] au1].
  simpl in Henv.
  lets H5 : env_domain_eq_imply_alloc_exist M1 Henv H15.
  destruct H5 as (le1' & M1' & H5).
  eexists.
  constructors.
  eapply ostc_step.
  eapply stmt_step;eauto.
  constructors;eauto.
  unfold allocstep.
  do 5 eexists;split;eauto.
  destruct H5 as (b & H5).
  destructs H5.
  destruct H15 as (b1 & H6).
  destructs H6.
  subst.
  split;auto.
  split.
  intros.
  apply H2 in H0.
  destruct H0 as (l & v & M0 & H0).
  destruct H0.
  unfold joinenvmem in *.
  do 7 destruct H5.
  destructs H5.
  inverts H5.
  inverts H7.
  lets Hmaps: mapstoval_exist (b,0%Z) t Vundef true.
  destruct Hmaps as (M2 & Hmaps). 
  do 3 eexists.
  split;eauto.
  do 7 eexists;split;eauto.
  split;eauto.
  split.
  apply EnvMod.join_sig_set.
  eauto.
  eapply join_mapstoval_allocb;eauto.
  intros. false.
Qed.

Lemma env_domain_set_eq : 
  forall le le' x v v' ,
    env_domain_eq le le' ->
    env_domain_eq (EnvMod.set le x v) (EnvMod.set le' x v').
Proof.
  intros.
  unfold env_domain_eq in *.
  intros.
  split.
  intros.
  EnvMod.beq_case_tac a x.
  eapply EnvMod.get_indom.
  EnvMod.rewrite_get.
  eexists;eauto.
  eapply EnvMod.get_indom.
  apply EnvMod.indom_get in H0.
  destruct H0.
  EnvMod.rewrite_get.
  apply EnvMod.indom_get.
  apply H.
  apply EnvMod.get_indom.
  eexists;eauto.
  intros.
  EnvMod.beq_case_tac a x.
  eapply EnvMod.get_indom.
  EnvMod.rewrite_get.
  eexists;eauto.
  eapply EnvMod.get_indom.
  apply EnvMod.indom_get in H0.
  destruct H0.
  EnvMod.rewrite_get.
  apply EnvMod.indom_get.
  apply H.
  apply EnvMod.get_indom.
  eexists;eauto.
Qed.

Lemma allocstepn_exist : 
  forall n p C C' o o' o1 ,
    losallocstepn n p C o C' o'->
    env_domain_eq (get_lenv (fst (fst o))) (get_lenv (fst (fst o1))) ->
    exists o1', losallocstepn n p C o1 C' o1'.
Proof.
  induction n.
  introv Hlo Henv.
  inverts Hlo.
  eexists.
  constructors.
  introv Hlo Henv.
  inverts Hlo.
  lets Ho1 : allocstep_exist H0 Henv.
  destruct Ho1 as (o1' & Ho1').
  assert (exists o1'', losallocstepn n p C'' o1' C' o1'').
  eapply IHn;eauto.
  destructs H0.
  destruct H0 as (l & v & x & t& M0 & H0).
  destructs H0.
  inverts H0.
  inverts H;tryfalse.
  inverts H0;tryfalse.
  inverts H.
  inverts H6;tryfalse.
  inverts H.
  inverts H6;tryfalse.
  destruct o1 as [[[[ge1 le1] M1] i1] au1].
  simpl in *.
  inverts Ho1'.
  inverts H;tryfalse.
  inverts H13;tryfalse.
  inverts H12.
  inverts H14;tryfalse.
  inverts H10.
  inverts H12.
  simpl.
  inverts H11.
  destruct H17,H21.
  destructs H. 
  destructs H6.
  subst.
  apply env_domain_set_eq;eauto.
  destruct o1 as [[[[ge1 le1] M1] i1] au1].
  simpl in *.
  inverts H5.
  inverts Ho1'.
  inverts H;tryfalse.
  inverts H12;tryfalse.
  inverts H11.
  inverts H13;tryfalse.
  inverts H9.
  inverts H11.
  simpl.
  inverts H8.
  destruct H17,H15.
  destructs H. 
  destructs H5.
  subst.
  apply env_domain_set_eq;eauto.
  destruct H.
  eexists.
  constructors;eauto.
Qed.


Lemma  alloc_exist : 
  forall n p C C' C'' o o' o'' , 
    losallocstepn (S (S n)) p C o C'' o''->
    losallocstep p C o C' o' -> 
    exists o''', losallocstepn (S n) p  C' o' C'' o'''.
Proof.
  intros.
  inverts H.
  lets Hcode : alloc_code_eq H0 H2.
  subst.
  eapply allocstepn_exist;eauto.
  inverts H2;inverts H0.
  unfold allocstep in H1.
  destruct H1 as (vl & dl & ks & x & t & H0).
  destructs H0.
  subst C.
  inverts H;inverts H2;tryfalse.
  inverts H0;inverts H13;tryfalse.
  inverts H;inverts H2.
  inverts H;inverts H2.
  inverts H14;inverts H15.
  inverts H;inverts H11.
  inverts H14;inverts H2.
  inverts H11;simpl.
  destruct H18,H17.
  destructs H.
  destructs H0.
  subst.
  apply env_domain_set_eq.
  unfold env_domain_eq.
  intros;split;eauto.
  inverts H9;simpl.
  destruct H15,H18.
  destructs H.
  destructs H0.
  subst.
  apply env_domain_set_eq.
  unfold env_domain_eq.
  intros;split;eauto.
Qed.


Lemma alloc_not_abort : 
  forall p C o C' o' o'' C'' o1,
    losallocstep p C o C' o' -> 
    losallocstep p C o C' o'' -> 
    losallocstep p C' o' C'' o1 -> 
    ~ loststepabt p C' o''.
Proof.
  intros.
  assert (losallocstepn 2 p C o C'' o1).
  constructors. apply H.
  constructors;eauto.
  constructors.
  lets Halloc : alloc_exist H2 H0.
  destruct Halloc as (o''' & Halloc).
  inverts Halloc.
  inverts H4.
  unfold loststepabt.
  red. intros. apply H4.
  do 2 eexists;eauto.
Qed.


Lemma alloc_stepn_msim_hold :
  forall n p  FSpec sd  C o  gamma O I r ri q li t, 
    satp o O (CurLINV li t) ->
    (exists  C'' o'', losallocstepn n  p C o C'' o'') -> 
    (forall C' o', losallocstepn n  p C o C' o' ->
                   MethSimMod FSpec sd C' o'  gamma O li I r ri q t ) ->
    MethSimMod FSpec sd C o  gamma O li I r ri q t .
Proof.
  introv Hsat  Hls.
  inductions n.
  assert  (losallocstepn 0 p C o C o) as H.
  constructors.
  introv Hlos.
  simpl.
  eapply Hlos; eauto.
  simpl.
  introv Hlos.
  eapply  alloc_step_msim_hold; eauto.
  destruct Hls as ( C'' & o'' & Hstep).
  inverts Hstep.
  unfolds in H0.
  destruct H0 as (Hs & Hisa ).
  eapply allocstep_imply_isalloc; eauto.
  destruct Hls as ( C'' & o'' & Hstep).
  inverts Hstep.
  unfolds in H0.
  destruct H0 as (Hs & Hisa & _).
  eauto.
  clear IHn.
  inductions n.
  simpl.
  introv Hlosp.
  eapply Hlos.
  constructors;eauto.
  eapply  losallocstep_irev_prog; eauto.
  constructors.
  introv Hlosp.
  simpl.
  eapply  alloc_step_msim_hold; eauto.
  destruct Hls as ( C'' & o'' & Hstep).
  inverts Hstep.
  lets  Heq :  alloc_code_eq Hlosp H0.
  subst.
  inverts H1.
  destruct H2 as (Htep & Hisa ). 
  eapply allocstep_imply_isalloc; eauto.
  eapply alloc_local_inv_prev; eauto.
  destruct Hls as ( C'' & o'' & Hstep).
  inverts Hstep.
  inverts H1.
  lets  Heq :  alloc_code_eq Hlosp H0.
  subst.
  assert (losallocstep p C o C''0 o') as Hasrt.
  eapply losallocstep_irev_prog; eauto.
  lets Hre :  alloc_not_abort H0 Hasrt H2.
  eauto.
  eapply IHn.
  eapply alloc_local_inv_prev; eauto.
  destruct Hls as ( C'' & o'' & Hstep).
  exists  C''.
  eapply alloc_exist;eauto.
  eapply losallocstep_irev_prog; eauto.
  introv Hlso.
  eapply Hlos.
  constructors; eauto.
  eapply losallocstep_irev_prog; eauto.
Qed.

Definition frp (C : code) := 
  (exists v ks, C = (curs (sfree nil v),(kenil,ks))/\
                callcont ks = None/\intcont ks = None).

Tactic Notation "invertstep" tactic (t) :=
  repeat progress
         match goal with
           | H : (_, _) = (_, _) |- _ => inverts H; tryfalse
           | H : estep _ _ _ _ _ _ |- _ => inverts H
           | H : loststep _ _ _ _ _ |- _ => inverts H
           | H : cstep _ _ _ _ _ |- _ => inverts H
           | H : sstep _ _ _ _ _ _ _ |- _ => inverts H
           | _ => t
         end.

Lemma IsFcall_kstop : 
  forall v ks  f s E,
    ~ IsFcall (curs (sfree nil v), (kenil, ks ## kcall f s E kstop)).
Proof. 
  introv Hf.     
  unfolds in Hf.
  destruct Hf as (f1 & V1 & t1 & Hss & Heq); inverts Heq.
Qed.

Lemma join_frame_dis :  
  forall o1 M  Ms  Mf o  o', 
    joinm2  o Ms  Mf o'  ->  
    joinmem o1 M o ->
    exists M', joinm2 o1 Ms M' o' /\  join M Mf M'.  
Proof.
  intros.
  exists (merge M Mf).
  unfold joinm2 in *.
  unfold joinmem in *.
  simpljoin.
  split.
  eexists; splits.
  do 6 eexists; splits; eauto.
  instantiate (1:= merge x1 Ms).
  assert(disjoint x1 Ms).

  eapply mem_join_join_disjoint; eauto.
  eapply join_merge_disj; eauto.

  do 6 eexists; splits; eauto.
  eapply mem_join_merge_rearange; eauto.

  apply join_comm in H2.
  eapply mem_join_join_join_merge; eauto.
Qed.

Lemma   joinmem_satp_mono:
  forall o1 M o1' Ms Os I,
    joinmem o1 M o1' ->
    satp (substaskst o1' Ms) Os (INV I) ->
    satp (substaskst o1 Ms) Os (INV I).
Proof.
  intros.
  unfolds in H; simpljoin.
  simpl in *.
  auto.
Qed.

Lemma joinm2_join_ex1 :
  forall oo Mss MM o M Mf,
    joinm2 oo Mss MM o ->
    join M Mf MM ->
    exists  o', joinm2 o' Mss Mf o /\ joinmem oo M o'.
Proof.
  intros.
  unfolds in H.
  simp join.
  unfolds in H.
  unfolds in H1.
  simp join.
  unfold joinmem.
  unfold joinm2.
  unfold joinmem.
  join auto.
Qed. 

Lemma   joinmem_satp_mono_rev:
  forall o1 M o1' Ms Os I,
    joinmem o1 M o1' ->
    satp (substaskst o1 Ms) Os (INV I) ->
    satp (substaskst o1' Ms) Os (INV I).
Proof.
  intros.
  unfolds in H; simpl in H.
  simpljoin.
  simpl in *.
  auto.
Qed.


Lemma  join_satp_local_inv:
  forall o M o' O Of O' t li,
    joinmem o M o' ->
    join O Of O' ->
    satp o O (CurLINV li t) ->
    satp o' O' (CurLINV li t).
Proof.
  intros.
  eapply join_satp_local_inv; eauto.
Qed.

Lemma  joinm2_disj : 
  forall o M1 M2 o',
    joinm2 o M1 M2  o' ->
    disjoint (getmem o)  M1.
Proof.
  unfold joinm2, disjoint in *.
  intros.
  unfold getmem in *.
  destruct o as  [[[[]]]].
  simpl.
  unfold joinmem in *.
  simp join.
  join auto.
Qed.

Lemma joinm2_getenv_eq:
  forall o1 Ms Mss  MM ge le Mf  M0 i ol  au E G,  
    G = get_genv (get_smem o1) ->
    joinm2 o1 Ms MM (ge, le, M0, i, au) -> 
    joinm2 ol Mss Mf (ge, E, M0, i, au) ->
    G = get_genv (get_smem ol) /\  E = get_lenv (get_smem ol).
Proof.
  intros.
  unfold joinm2 in *.
  unfold joinmem in *.
  simpljoin.
  simpl; auto.
Qed.

Lemma callcont_addkcall_nonone_imply_callcont_addkcall:
  forall (ks : stmtcont) (f : fid) (s : stmts) 
         (ks' : stmtcont)  
         (E : env) ( ks1 : stmtcont),
    callcont (ks ## kcall f s E ks') <> None ->
    callcont (ks ## kcall f s E ks1) <> None.
Proof.
  intros.
  induction ks;simpl;auto.
  intro;tryfalse.
  intro;tryfalse.
Qed.

Lemma loststep_keepG : 
  forall p C o C' o', 
    loststep p C o C' o'  ->  
    get_genv (get_smem o) =  get_genv (get_smem o').
Proof.
  intros.
  destruct o as [ [ [ [ ] ] ] ]; simpl.
  destruct o' as [ [ [ [ ] ] ] ]; simpl.
  invertstep auto.
Qed.


Lemma not_free_cont_loc : 
  forall p c ke ks o o' f  s E ks' C, 
    ~ frp (c, (ke, ks)) -> 
    loststep p (c, (ke, ks ## kcall f  s E ks')) o C o'->
    ~ loststepabt p (c, (ke, ks ## kcall f  s E kstop)) o ->
    exists c' ke' ks'',  
      loststep p (c, (ke, ks ## kcall f  s E kstop)) o
               (c',(ke',ks''## kcall f  s E kstop)) o' /\ 
      C =  (c',(ke',ks''## kcall f  s E ks')).
Proof.
  intros.
  apply Classical_Prop.NNPP in H1.
  destruct H1 as (C' & tst' & H1).
  inverts H0.
  inverts H2.
  inverts H0;inverts H3;
  try solve [
        do 3 eexists;
        split;eauto;constructors;eauto;
        constructors;eauto;
        try solve [eapply ecastnull_step;eauto];constructors;eauto].
  do 3 eexists;
    split;eauto;constructors;eauto;
    constructors;eauto;
    try solve [eapply ecastnull_step;eauto];eapply eaelemaddr_step;eauto.
  do 3 eexists;
    split;eauto;constructors;eauto;
    constructors;eauto;
    try solve [eapply ecastnull_step;eauto];eapply eaelem_step;eauto.
  
  inverts H0.
  inverts H3;(inverts H1 as Hlo;tryfalse); try solve [
                                                 try (destruct ks ;inverts H0);
                                                 try (destruct ks ;inverts H5);
                                                 rewrite_addcont;
                                                 do 3 eexists;
                                                 split;eauto;constructors;eauto;
                                                 eapply stmt_step;eauto; 
                                                 constructors;eauto].
  rewrite H5.
  destruct ks;inverts H5;
  do 3 eexists;
  split;eauto;constructors;eauto;
  eapply stmt_step;eauto; 
  constructors;eauto.
  lets Hcall : callcont_addkcall_imply_callcont_addkcall_exist H2.
  destruct Hcall as (ks1 & Hcall).
  do 3 eexists;
    split;eauto;constructors;eauto;
    eapply stmt_step;eauto; 
    constructors;eauto.
  destruct ks;inverts H0.
  
  lets Hcall : callcont_addkcall_nonone_imply_callcont_addkcall H4.
  do 3 eexists;
    split;eauto;constructors;eauto;
    eapply stmt_step;eauto; 
    constructors;eauto.
  unfold frp in H.
  lets Hfrp: Classical_Pred_Type.not_ex_all_not H v.
  lets Hfrp': Classical_Pred_Type.not_ex_all_not Hfrp ks.
  apply Classical_Prop.not_and_or in Hfrp'.
  destruct Hfrp'.
  false. 
  apply Classical_Prop.not_and_or in H0.
  destruct H0.
  lets Hcall : callcont_addkcall_imply_addcont_exist H0 H4.
  destruct Hcall as (ks''' & Hcall). subst ks'0.
  lets Hcall :  callcont_addkcall_imply_callcont_addkcall H4.
  do 3 eexists;split;eauto;constructors;eauto; eapply stmt_step;eauto;constructors;eauto.
  assert (callcont ks = None \/ callcont ks <> None ).
  apply Classical_Prop.classic.
  destruct H1.
  lets Hcall : callcont_none_intcont_some_imply_callcont_addcont_none  (kcall f s E ks') H1 H0.
  rewrite H4 in Hcall.
  inverts Hcall.
  lets Hcall : callcont_addkcall_imply_addcont_exist H1 H4.
  destruct Hcall as (ks''' & Hcall). subst ks'0.
  lets Hcall :  callcont_addkcall_imply_callcont_addkcall H4.
  do 3 eexists;split;eauto;constructors;eauto; eapply stmt_step;eauto;constructors;eauto.
  inverts H2.
  lets Hint : intcont_addkcall_exist H3.
  destruct Hint as (ks'' & Hint).
  subst ks'0.
  do 3 eexists;
    split;eauto;constructors;eauto.
  rewrite_addcont.
  apply intcont_some_addcont.
  eapply intcont_addkcall_imply_intcont;eauto.
  inverts H2.
  do 3 eexists;
    split;eauto;constructors;eauto.
  inverts H2.
  do 3 eexists;
    split;eauto;constructors;eauto.
  inverts H2.
  do 3 eexists;
    split;eauto;constructors;eauto.
  inverts H2.
  do 3 eexists;
    split;eauto;constructors;eauto.
  inverts H2.
  do 3 eexists.
  split;eauto.
  constructors;eauto.
  inverts H2.
  do 3 eexists.
  split;eauto.
  eapply checkis_step;eauto.
Qed.

Lemma get_genv_join3_eq:
  forall o2 o2' o1 M o1' Ms   oo ol  Mss Mf  G,
    get_genv (get_smem o2) = get_genv (get_smem o2') ->
    G = get_genv (get_smem o1) ->
    joinmem o1 M o1' -> 
    joinm2 o1' Ms Mf o2 ->
    joinmem oo M ol -> 
    joinm2 ol Mss Mf o2' ->
    G = get_genv (get_smem oo).
Proof.
  intros.
  unfold joinm2 in *.
  unfold joinmem in *.
  simpljoin.
  simpl in *; auto.
Qed.

Ltac  casenot H :=  
  apply Classical_Prop.not_and_or in H;
  let Hc := fresh "Cs" in ( destruct H as [Hc | H];
                            [apply Classical_Prop.NNPP in Hc| ]).


Lemma loststepabt_cont_loststepabt : 
  forall p c ke ks ks' f  s E o2, 
    ~ loststepabt p (c, (ke, ks ## kcall f s E kstop)) o2 ->
    ~ loststepabt p (c, (ke, ks ## kcall f s E ks')) o2.
Proof.
  intros.
  red. intro.
  apply H.
  unfold loststepabt in *.
  red. intro.
  apply H0.
  clear H H0.
  destruct H1 as (C' & tst' & H).
  inverts H;
    inverts H0.
  inverts H;inverts H1;try solve [
                             do 2 eexists; constructors;eauto;constructors;eauto;try solve [constructors;eauto]].
  do 2 eexists; constructors;eauto;constructors;eauto;try solve [eapply eaelemaddr_step;eauto].
  do 2 eexists; constructors;eauto;constructors;eauto;try solve [eapply eaelem_step;eauto].
  do 2 eexists; constructors;eauto;constructors;eauto;
  eapply ecast_step;eauto.
  do 2 eexists; constructors;eauto;constructors;eauto;
  eapply ecastnull_step;eauto.
  do 2 eexists; constructors;eauto;constructors;eauto;
  eapply ecastcomptr_step;eauto.
  inverts H;inverts H1; 
  try solve [do 2 eexists; constructors;eauto; eapply stmt_step;eauto;constructors;eauto |
             destruct ks;simpl in H ;inverts H ;do 2 eexists;constructors;eauto;eapply stmt_step;eauto;constructors;eauto |
             destruct ks;simpl in H3;inverts H3;do 2 eexists;constructors;eauto;eapply stmt_step;eauto;constructors;eauto    ].
  lets Hcall : callcont_addkcall_imply_callcont_addkcall_exist H0.
  destruct Hcall as (ks1 & Hcall).
  do 2 eexists; constructors;eauto; eapply stmt_step;eauto;constructors;eauto.
  destruct ks;inverts H.
  lets Hcall : callcont_addkcall_nonone_imply_callcont_addkcall H2.
  do 2 eexists; constructors;eauto; eapply stmt_step;eauto;constructors;eauto.
  lets Hcall : callcont_addkcall_imply_callcont_addkcall_exist H2.
  destruct Hcall as (ks1 & Hcall).
  do 2 eexists; constructors;eauto; eapply stmt_step;eauto;constructors;eauto.

  lets Hint : intcont_addkcall_imply_intcont_addkcall_exist H1.
  destruct Hint.
  do 2 eexists;eapply exint_step;eauto.
  do 2 eexists;eapply eoi_step;eauto.
  do 2 eexists;eapply cli_step;eauto.
  do 2 eexists;eapply sti_step;eauto.
  do 2 eexists;eapply encrit_step;eauto. 
  do 2 eexists;eapply excrit_step;eauto.
  do 2 eexists;eapply checkis_step;eauto.
Qed.


Lemma joinmem_disj_disj : 
  forall o1 M o1' Ms,
    joinmem o1 M o1' ->
    disjoint (getmem o1') Ms ->
    disjoint (getmem o1) Ms.
Proof.
  intros.
  unfold joinmem in H; simpljoin.
  unfold getmem in *; simpl in *.
  eapply mem_join_disjoint_disjoint; eauto.
Qed.
  

Lemma get_genv_jeq:
  forall G o1 M o1' o' oo,
    G = get_genv (get_smem o1) ->
    joinmem o1 M o1' ->
    eqenv o1' o' ->
    joinmem oo M o' ->
    G = get_genv (get_smem oo) /\  eqenv o1 oo.
Proof.
  intros.
  unfold joinmem in *; simpljoin.
  simpl.
  unfolds in H1.
  simpljoin; auto.
Qed.


Lemma fcall_kstop :
  forall c ke ks f  s E ks',   
    ~ IsFcall (c, (ke, ks ## kcall f  s E ks')) -> 
    ~ IsFcall (c, (ke, ks ## kcall f  s E kstop)). 
Proof.
  intros.
  red; intros H100; apply H; clear H; rename H100 into H.
  unfold IsFcall in *; mytac.
  eauto.
Qed. 


Lemma joinmem_ex_intro:
  forall om MM o1 M o1',
    joinmem om MM o1 ->
    joinmem o1 M o1' ->
    exists Mb, joinmem om Mb o1' /\ join MM M Mb.
Proof.
  intros.
  unfold joinmem in *.
  join auto.
Qed.

Lemma joinmem_ex_elim:
  forall o0 Mb o' MM  M,
    joinmem o0 Mb o'->
    join MM M Mb ->
    exists oo, joinmem oo M o' /\ joinmem o0 MM oo.
Proof.
  intros.
  unfold joinmem in *.
  join auto.
Qed.

Lemma joinmem2_ex_intro:
  forall oo Mc o1 M o1',
    joinmem oo Mc o1 ->
    joinmem o1 M o1' ->
    exists ok, joinmem ok Mc o1'
               /\ joinmem oo M ok.
Proof.
  intros.
  unfold joinmem in *; simpljoin.
  eexists.
  split.
  do 6 eexists; eauto.
  splits; eauto.
  instantiate (1:=(merge x7 M)).
  apply join_comm.
  apply join_comm in H4.
  eapply mem_join_join_merge23_join; eauto.

  do 6 eexists; splits; eauto.
  eapply map_join_merge.
  eapply mem_join_join_disjoint; eauto.
Qed.

Lemma  join3_satp_swinv:
  forall  o1 M o1' Mc I t Oc sd pa,
    GoodI I sd pa->
    joinmem o1 M o1'->
    satp (substaskst o1 Mc) Oc (SWINVt I t)  ->
    satp (substaskst o1' Mc) Oc (SWINVt I t).
Proof.
  intros.
  unfolds in H0; simpljoin.
  simpl in *.
  auto.
Qed.

Lemma local_inv_satp_hold:
   forall  oo M ok Oll Of Ot t li,
     joinmem oo M ok ->
     join Oll Of Ot -> 
     satp oo Oll (EX lg' : list logicvar, LINV li t lg' ** Atrue) ->
     satp ok Ot (EX lg' : list logicvar, LINV li t lg' ** Atrue).
Proof.
  intros.
  unfold satp in *.
  intros.
  pose proof H1 aop.
  destruct H2.
  exists x.
  destruct oo; destruct p; destruct s; destruct p.
  unfold joinmem in H; simpljoin.
  unfold sat in H2; fold sat in H2.
  unfold sat; fold sat.
  simpl assertion.getmem in *.
  simpl getabst in *.
  simpl substmo in *.
  simpljoin.
  exists x6 (merge x7 M) x3.
  exists x9 (merge x10 Of) Ot.
  splits; auto.
  clear - H4 H2.
  eapply mem_join_join_merge23_join; eauto.
  clear - H0 H5.
  
  eapply join_merge23_join; eauto.
Qed.

Lemma  joinmem_ex_intro2:
forall oo M ok Mc o',
  joinmem oo M ok ->
  joinmem ok Mc o' ->
  exists ol, joinmem ol M o'/\ joinmem oo Mc ol.
Proof.
  unfold joinmem; intros.
  simpljoin.
  eexists.
  split; do 6 eexists; splits; eauto.
  instantiate (1:= merge x7 Mc).
  apply join_comm.
  apply join_comm in H4.
  eapply mem_join_join_merge23_join; eauto.
  eapply map_join_merge.
  eapply mem_join_join_disjoint; eauto.
Qed.


Lemma get_genv_joinmem_eq:
  forall o1 M o1' ok Mc  oo Mc' oo1 G,
    G = get_genv (get_smem o1) ->
    joinmem o1 M o1' ->
    joinmem ok Mc o1' ->
    joinmem oo M ok ->
    joinmem oo Mc' oo1 ->
    G = get_genv (get_smem oo1).
Proof.
  unfold joinmem; intros.
  simpljoin.
  simpl; auto.
Qed.
  
Lemma  join3_satp_swinv_rev:
    forall  o1 M o1' Mc I t Oc sd pa,
      GoodI I sd pa->
      joinmem o1 M o1'->
      satp (substaskst o1' Mc) Oc (SWINVt I t)  ->
      satp (substaskst o1 Mc) Oc (SWINVt I t).
Proof.
  intros.
  unfold joinmem in *.
  simpljoin.
  simpl in *.
  auto.
Qed.
  
Lemma abs_crt_locality :
  forall O O' t t' p O1 Of,
    abs_crt_step O O' t t' p ->
    join Of O O1 ->
    exists O1', abs_crt_step O1 O1'  t t' p /\ join Of O' O1'.
Proof.
  intros.
  exists (merge Of O').
  unfolds in H; simpljoin.
  unfold abs_crt_step.
  split.
  split; auto.
  exists x x0.
  splits; auto.
  eapply join_get_r; eauto.
  eapply join_get_r; eauto.
  
  eapply OSAbstMod.extensionality; intros.
  rewrite OSAbstMod.merge_sem.
  destruct (absdataidspec.beq abstcblsid a) eqn : eq1.
  lets Hx: absdataidspec.beq_true_eq eq1; substs.
  rewrite OSAbstMod.set_a_get_a; auto.
  rewrite OSAbstMod.set_a_get_a; auto.
  pose proof H0 abstcblsid.
  unfold get in H2; simpl in H2.
  rewrite H2 in H4.
  destruct (OSAbstMod.get Of abstcblsid); tryfalse; auto.

  
  rewrite OSAbstMod.set_a_get_a'; auto.
  rewrite OSAbstMod.set_a_get_a'; auto.
  pose proof H0 a.
  destruct (OSAbstMod.get Of a);
    destruct (OSAbstMod.get O a);
    destruct (OSAbstMod.get O1 a); tryfalse; substs; eauto.

  rewrite map_merge_comm.
  rewrite merge_set_eq_1; eauto.
  eapply join_set_r; eauto.
  rewrite map_merge_comm; jeat.
  eapply join_merge_disj.
  unfolds; jeat.
  unfolds; eauto.
  exists (set O1 abstcblsid (abstcblist x0)).
  eapply join_set_r; eauto.
  unfolds; jeat.
Qed.

Lemma abs_delself_locality :
  forall O O' t t' p O1 Of,
    abs_delself_step O O' t t' p ->
    join Of O O1 ->
    exists O1', abs_delself_step O1 O1'  t t' p /\ join Of O' O1'.
Proof.
  intros.
  exists (merge Of O').
  unfolds in H; simpljoin.
  unfold abs_delself_step.
  split.
  splits; eauto.
  eapply join_get_r; eauto.
  unfolds in H2; simpljoin.
  unfolds.
  exists x x0 x1 x2.
  splits; auto.
  eapply join_get_r; eauto.
  
  eapply OSAbstMod.extensionality; intros.
  rewrite OSAbstMod.merge_sem.
  destruct (absdataidspec.beq abstcblsid a) eqn : eq1.
  lets Hx: absdataidspec.beq_true_eq eq1; substs.
  rewrite OSAbstMod.set_a_get_a; auto.
  rewrite OSAbstMod.set_a_get_a; auto.
  pose proof H0 abstcblsid.
  unfold get in H; simpl in H.
  rewrite H in H3.
  destruct (OSAbstMod.get Of abstcblsid); tryfalse; auto.

  rewrite OSAbstMod.set_a_get_a'; auto.
  rewrite OSAbstMod.set_a_get_a'; auto.
  pose proof H0 a.
  destruct (OSAbstMod.get Of a);
    destruct (OSAbstMod.get O a);
    destruct (OSAbstMod.get O1 a); tryfalse; substs; eauto.

  eapply join_merge_disj.
  unfolds in H2; simpljoin.
  unfold disjoint.
  exists (set O1 abstcblsid (abstcblist x0)).
  eapply join_set_r; eauto.
  unfolds; jeat.
Qed.


Lemma abs_delother_locality :
  forall O O' t t' p O1 Of,
    abs_delother_step O O' t t' p ->
    join Of O O1 ->
    exists O1', abs_delother_step O1 O1'  t t' p /\ join Of O' O1'.
Proof.
  intros.
  exists (merge Of O').
  unfolds in H; simpljoin.
  split.
  unfolds.
  splits; auto.
  eapply join_get_r; eauto.
  unfolds in H2; simpljoin.
  unfolds.
  exists x x0 x1 x2.
  splits; auto.
  eapply join_get_r; eauto.

  eapply OSAbstMod.extensionality; intros.
  rewrite OSAbstMod.merge_sem.
  destruct (absdataidspec.beq abstcblsid a) eqn : eq1.
  lets Hx: absdataidspec.beq_true_eq eq1; substs.
  rewrite OSAbstMod.set_a_get_a; auto.
  rewrite OSAbstMod.set_a_get_a; auto.
  pose proof H0 abstcblsid.
  unfold get in H2; simpl in H2.
  rewrite H2 in H4.
  destruct (OSAbstMod.get Of abstcblsid); tryfalse; auto.

  rewrite OSAbstMod.set_a_get_a'; auto.
  rewrite OSAbstMod.set_a_get_a'; auto.
  pose proof H0 a.
  destruct (OSAbstMod.get Of a);
    destruct (OSAbstMod.get O a);
    destruct (OSAbstMod.get O1 a); tryfalse; substs; eauto.

  eapply join_merge_disj.
  unfolds in H2; simpljoin.
  unfold disjoint.
  exists (set O1 abstcblsid (abstcblist x0)).
  eapply join_set_r; eauto.
  unfolds; jeat.
Qed.

Lemma evalval_mono_joinmem:
  forall o1 M o1' e0 v1,
    joinmem o1 M o1' ->
    evalval e0 (get_smem o1) = Some v1 ->
    evalval e0 (get_smem o1') = Some v1.
Proof.
  intros.
  destruct o1 as [[[[]]]].
  destruct o1' as [[[[]]]].
  unfold joinmem in *.
  simp join.
  simpl in *.
  lets Has : evalval_mono H2 H0.
  rewrite Has.
  auto.
Qed.


Lemma joinmem_satp_ocr:
  forall o1 M o1' ocr mcr li t',
    joinmem o1 M o1' -> 
    satp (substaskst o1 mcr) ocr (li t' init_lg ** [|GoodLInvAsrt li|]) ->
    satp (substaskst o1' mcr) ocr (li t' init_lg ** [|GoodLInvAsrt li|]).
Proof.
  intros.
  unfolds in H; simpljoin.
  simpl in *.
  auto.
Qed.

Lemma get_genv_joinmem3_eq:
  forall  o1 M   mcr o1' o11 ok G,
    G = get_genv (get_smem o1) ->
    joinmem o1 M o1' ->
    joinmem ok mcr o1' ->
    joinmem o11 M ok ->
    G = get_genv (get_smem o11) .
Proof.
  intros.
  unfold joinmem in *.
  simpljoin.
  simpl; auto.
Qed.
  
Lemma local_inv_satp_join_hold:
  forall  o1 M o1' Mdel Odel li t',
    joinmem o1 M o1'  ->
    satp (substaskst o1' Mdel) Odel
         (EX lg : list logicvar, LINV li t' lg) ->
    satp (substaskst o1  Mdel) Odel
         (EX lg : list logicvar, LINV li t' lg).
Proof.
  intros.
  unfolds in H; simpljoin.
  simpl in *.
  auto.
Qed.

Lemma get_genv_join2del_eq:
forall o1 M o1' oo1 Mdel G,
 G = get_genv (get_smem o1) ->
  joinmem o1 M o1' ->
 joinmem o1 Mdel oo1 ->
  G = get_genv (get_smem oo1) .
Proof.
  intros.
  unfold joinmem in *; simpljoin.
  simpl; auto.
Qed.
  
Lemma join_ex2:
forall (O1: OSAbstMod.map)  O2 O3 O4 O5,
    join O1 O2 O3 ->
  join O3  O4 O5 ->
  exists O,  join O1 O4 O /\  join O O2 O5.
Proof.
 intros.
 join auto.
Qed.

Lemma free_frame_prop : 
  forall tp b M M' M1 MM MM' Ms Mf, 
    free tp b M = Some M'->  
    free tp b MM = Some MM' -> 
    join M Ms M1 ->
    join M1 Mf MM -> exists M'', join M' Ms M'' /\ join M'' Mf MM'.
Proof.
  intros.
  exists (merge M' Ms).
  assert(join M (merge Ms Mf) MM).
  eapply mem_join_join_merge23_join; eauto.
  lets Hx: join_free H3 H H0.
  assert(disjoint Ms Mf).
  apply join_comm in H1.
  eapply mem_join_join_disjoint; eauto.

  split.
  apply map_join_merge.
  eapply mem_disjoint_merge_disjoint; eauto.

  eapply mem_join_merge_disjoint; eauto.
Qed.


Lemma free_locality_pre :
  forall b i n M' M Ms Mf M1 M2 , 
    freeb M b i n = Some M'->
    join M Ms M1 ->
    join M1 Mf M2 -> exists M'', freeb M2 b i n = Some M'' . 
Proof.
  intros.
  gen b i M'.
  induction n; intros; simpl in *.
  eauto.
  unfold get in *; simpl in *.

  remember (HalfPermMap.get M (b, i)) as v100; destruct v100; tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  lets H100 : join_assoc_l H0 H1; mytac.
  assert (HalfPermMap.get M2 (b, i) = Some (true, c)) as H100.
  eapply mem_join_get_get_l_true; eauto.
  rewrite H100; clear H100.
  remember (freeb M b (i + 1) n) as v200; destruct v200; tryfalse.
  symmetry in Heqv200.
  lets H100 : IHn Heqv200; mytac.
  rewrite H4.
  eauto.
Qed.


Lemma free_locality:
  forall tp b  M' M Ms Mf M1 M2 ,
    free tp b M = Some M'-> 
    join M Ms M1 ->
    join M1 Mf M2 ->
    exists M'', free tp b M2  = Some M'' . 
Proof.
  intros.
  unfold free in *.
  eapply free_locality_pre; eauto.
Qed.

Inductive freels :  freelist -> mem -> mem -> Prop :=
| freelist_0 : forall M, freels nil M M
| freelist_n : forall b t ls M M'' M', free t b M = Some M'' -> freels ls M'' M' ->
                                       freels (cons (b,t) ls) M M'.


Lemma get_ptomvallist_less_none :
  forall b i n ls M,
    (n > 0)%Z ->
    ptomvallist (b, (i + n)%Z) true ls M ->
    get M (b, i) = None.
Proof.
  intros.
  gen n b i M.
  induction ls; intros; simpl in *; mytac.
  apply emp_sem.  

  lets H00 : mem_join_disjoint_eq_merge H0; mytac.
  rewrite merge_semp.
  unfold ptomval in H1; subst x; rewrite get_sig_none.
  rewrite Zplus_assoc_reverse in H2.
  erewrite IHls; auto.
  2 : apply H2.
  omega.
  intro.
  inverts H1.
  assert (i + n > i)%Z as H100 by omega.
  rewrite H5 in H100.
  omega.
  unfold usePerm.
  simpl.
  unfold HalfPermMap.usePerm; auto.
Qed.

Lemma freeb_join :
  forall b i n M1 M12,
    freeb M12 b i n = Some M1 ->
    exists vl M2, length vl = n /\ ptomvallist (b, i) true vl M2 /\ join M1 M2 M12.
Proof.
  intros.
  gen M1 M12 b i.
  induction n; intros; simpl in *.
  inv H.
  exists (@nil memval) empmem; mytac; simpl; auto.

  remember (get M12 (b, i)) as v100; destruct v100; tryfalse.
  remember (freeb M12 b (i + 1) n) as m100; destruct m100; tryfalse.
  symmetry in Heqv100, Heqm100.
  lets H100 : IHn Heqm100; mytac.
  destruct p; destruct b0; tryfalse.
(*  lets H100 : H2 (b, i); rewrite Heqv100 in H100. *)
  assert (get x0 (b, i) = None) as H200.
  eapply get_ptomvallist_less_none.
  2 : eauto.
  omega.
  assert (get m (b, i) = Some (true, m0)).
  eapply mem_get_join_get; eauto.
  
  assert (join M1 (sig (b, i) (true, m0)) m) as H100.
  inverts H.
  apply join_comm.

  eapply mem_get_join_sig_del; eauto.
  lets h200 : join_assoc_l H100 H2; mytac.
  exists (m0 :: x); simpl.
  eexists; mytac; eauto.
  do 2 eexists; mytac; eauto.
  unfold ptomval; auto.
  destruct p; destruct b0; tryfalse.
Qed.

Lemma freeb_join_exist :
  forall n M M' b i,
    freeb M b i n = Some M' ->
    exists Mx, join M' Mx M.
Proof.
  inductions n; intros.
  simpl in H; inverts H.
  exists empmem.
  eapply join_comm.
  eapply join_emp; auto.

  unfold freeb in H; fold freeb in H.
  destruct(get M (b, i)) eqn : eq1; tryfalse.
  destruct p.
  destruct b0; tryfalse.
  destruct (freeb M b (i + 1) n) eqn : eq2; tryfalse.
  inverts H.
  eapply IHn in eq2; simpljoin.

  eapply mem_get_join_join_del_exists; eauto.
Qed.

Lemma free_join_exist :
  forall t b M M',
    free t b M = Some M' ->
    exists Mx, join M' Mx M.
Proof.
  intros.
  unfolds in H.
  eapply freeb_join_exist; eauto.
Qed.

Lemma freels_join :
  forall ls M1 M2,
    freels ls M1 M2 ->
    exists Mx, join M2 Mx M1.
Proof.
  inductions ls; intros.
  inverts H.
  exists empmem.
  eapply join_comm.
  eapply join_emp; auto.

  inverts H.
  eapply IHls in H5; simpljoin.

  lets Hx: free_join_exist H2.
  simpljoin.
  exists (merge x x0).
  eapply mem_join_join_merge23_join; eauto.
Qed.

Lemma freels_local_inv_hold:
  forall ls M'' M'  G E isr aux O li t,
    freels ls M'' M' ->
    satp (G, E, M', isr, aux) O (CurLINV li t) ->
    satp (G, E, M'', isr, aux) O (CurLINV li t).
Proof.
  intros.
    
  lets Hx: freels_join H; simpljoin.
  eapply join_satp_local_inv; eauto.
  unfolds.
  do 6 eexists; splits; eauto.
  eapply join_comm.
  eapply join_emp; auto.
Qed.

Lemma free_step_sim_hold :
  forall FSpec sd  I ri r post b tp ls ks  G E M M' isr aux O aop v t li,
    free tp b M = Some M' ->
    satp (G,E,M',isr,aux)  O (CurLINV li t) -> 
    MethSimMod FSpec sd   (curs (sfree ls v), (kenil, ks)) (G,E,M',isr,aux) aop O  li I r ri  (fun v => (post v)) t ->
    MethSimMod FSpec sd   (curs (sfree (cons (b, tp) ls) v), (kenil, ks)) (G,E,M,isr,aux) aop O  li I r ri  (fun v => (post v)) t.
Proof.
  introv  Hfree Hsat  Hsim.
  constructors; try(introv Hfalse; tryfalse).
  introv Hinv Hjm Hjon Hstep.
  invertstep idtac.
  unfold joinm2 in Hjm.
  unfold joinmem in Hjm.
  simp join.
  simpl in Hinv.
  lets Hex :  free_frame_prop Hfree H12 H4 H2.
  destruct Hex as (M'' & Hmmj1 & Hmmj2).
  exists aop OO (x0, x1, M', x4, x5) Ms O  Os. 
  splits; auto.
  constructors.
  unfolds;eexists.
  unfold joinmem.
  splits; do 6 eexists; eauto.
  introv   Hinv Hjm Hdisj Hstep. 
  unfold joinm2 in Hjm.
  unfold joinmem in Hjm.
  simp join.
  simpl in Hinv.
  unfolds in Hstep.
  apply Hstep.
  lets Hfe : free_locality Hfree H4 H2. 
  destruct Hfe as (M'' & Hffee).
  do 2 eexists.
  eapply ostc_step; eauto.
  eapply stmt_step;eauto.
  constructors;eauto.
Qed.


Lemma free_stepn_sim_hold :
  forall p sd  I ri r post ls ks G E M M' isr aux O aop v li t,
    freels ls M M' ->
    satp (G,E,M',isr,aux)  O (CurLINV li t) -> 
    MethSimMod p sd  (curs (sfree nil v), (kenil, ks)) (G,E,M',isr,aux) aop O  li I r ri  (fun v => (post v)) t ->
    MethSimMod p sd   (curs (sfree  ls v), (kenil, ks)) (G,E,M,isr,aux) aop O  li I r ri  (fun v => (post v)) t.
Proof.
  introv Hfree Hsat Hsim.
  inductions Hfree. 
  auto.
  eapply   free_step_sim_hold;  eauto.
  eapply  freels_local_inv_hold; eauto.
Qed.


Lemma free_intro_aux1 : forall  d a G E M isr aux O aop, 
                          Some a = buildq d -> 
                          (G, E, M, isr, aux, O, aop) |= a
                          -> O = empabst.
Proof.
  inductions d.
  introv Ha; simpl in Ha.
  inverts Ha.
  simpl.
  intros.
  destruct H.
  unfolds in H0; auto.
  introv Hsa.
  simpl in Hsa.
  remember (negb (in_decllist i d) && good_decllist d) as b100; destruct b100; tryfalse.
  remember (buildq d) as Hd; destruct Hd; tryfalse.
  inverts Hsa.
  introv Hsat.
  destruct Hsat;mytac.
  simpl substmo in *.
  lets Hss: IHd H4;eauto.
  mytac.
  simpl getmem in H0.
  simpl in H3;mytac.
Qed.

Inductive freels' : freelist -> mem -> mem -> Prop :=
| freelist'_0 : forall M, freels' nil M M
| freelist'_n : forall b t ls1 ls2 M1 M2 M3 M4, free t b M1 = Some M2 ->
                                                freels' ls1 M2 M3 ->
                                                freels' ls2 M3 M4 ->
                                                freels' (ls1 ++ ( (b, t)) ::ls2) M1 M4.

Lemma freeb_join_rev :
  forall b i n vl M1 M2 M12,
    join M1 M2 M12 ->
    ptomvallist (b, i) true vl M2 ->
    length vl = n ->
    freeb M12 b i n = Some M1.
Proof.
  intros.
  gen n b i M1 M2 M12.
  induction vl; induction n; intros; simpl in *.
  mytac; auto.
  mytac; tryfalse.
  tryfalse.

  clear IHn.
  inversion H1; clear H1.
  lets H100 : IHvl H3; clear IHvl; rename H100 into IHvl. 
  mytac.
  assert (get M12 (b, i) = Some (true, a)) as H100.

  eapply mem_join_get_get_r_true; eauto.
  eapply mem_join_get_get_l_true; eauto.
  unfold ptomval in *; subst x; apply get_sig_some.
  
  change Z with offset; rewrite H100; clear H100.
  lets H100 : join_assoc_r H0 H; mytac.
  erewrite IHvl; eauto.

  erewrite <- mem_join_true_del; eauto.
  unfold ptomval in H1; rewrite <- H1.
  jeat.
Qed.


Lemma free_exchange' :
  forall b i ls b' i' ls' M1 M2 M3,
    freeb M1 b i ls = Some M2 ->
    freeb M2 b' i' ls' = Some M3 ->
    exists M, freeb M1 b' i' ls' = Some M /\ freeb M b i ls = Some M3.
Proof.
  intros.
  lets H100 : freeb_join H; mytac.
  lets H100 : freeb_join H0; mytac.
  assert(join x2 M3 M2) as H5'.
  apply join_comm in H5; auto.
  lets H100 : join_assoc_l H5' H3; mytac.
  apply join_comm in H6.
  exists x3; mytac; eapply freeb_join_rev; eauto.  
Qed.


Lemma free_exchage :
  forall t b M1 t' b' M2 M3,
    free t b M1 = Some M2 ->
    free t' b' M2 = Some M3 ->
    exists M', free t' b' M1 = Some M' /\ free t b M' = Some M3.
Proof.
  intros.
  unfold free in *.
  eapply free_exchange'; eauto.
Qed.

Lemma freels_exchange1 : 
  forall ls1 t b M1 M2 t' b' M3 M4, 
    free t b M1 = Some M2 -> 
    free t' b' M2 = Some M3 ->
    freels ls1 M3 M4 -> 
    exists M'' M''',
      free t' b' M1 = Some M'' /\ 
      freels ls1 M'' M'''/\ 
      free t b M''' = Some M4.
Proof.
  inductions ls1.
  intros.  
  inverts H1.
  lets Hds : free_exchage H H0.
  destruct Hds as (Ms & Hfr & Hfr').
  exists Ms.  
  exists Ms.
  splits;eauto.
  constructors.
  intros.
  inverts H1.
  lets Hds :  free_exchage H H0.
  destruct Hds as (Ms & Hfr & Hfr').
  exists Ms.
  lets Hrs :  IHls1 Hfr' H4 H7.
  destruct Hrs as (Ms2 & Ms3 & Hfr1 & Hfr2 & Hfr3).
  exists Ms3.
  splits; eauto.
  constructors; eauto.
Qed.


Lemma freels_exchage2 :
  forall  ls1 t b ls2 M1 M2 M3 M4,
    free t b M1 = Some M2 ->
    freels ls1 M2 M3 -> freels ls2 M3 M4 ->
    exists M', freels ls1 M1 M' /\ freels  ((b, t) :: ls2)  M' M4. 
Proof. 
  inductions ls1.                      
  intros.
  inverts H0.
  exists M1.
  splits; constructors;eauto.
  intros.
  inverts H0.
  lets Hds : freels_exchange1 H H4 H7.
  destruct Hds as (Ms1 & Ms2 & Hfre1 & Hfe & Hfss).
  exists Ms2.
  splits; eauto.
  constructors; eauto.
  constructors;eauto.
Qed.

Lemma freels_merge : forall ls1 ls2 M1 M2 M3, freels ls1 M1 M2 -> freels ls2 M2 M3 -> 
                                              freels (ls1 ++ ls2) M1 M3.
Proof.
  inductions ls1.
  intros.
  inverts H.
  simpl.
  auto.
  intros.
  simpl.
  inverts H.
  constructors; eauto.
Qed.

Lemma freels_imply_freels' : forall ls  M1 M2, freels' ls M1 M2 -> 
                                               freels ls M1 M2.  
Proof.
  introv Hfr.
  inductions Hfr. 
  constructors.
  lets Hds: freels_exchage2  H IHHfr1 IHHfr2.
  destruct Hds as (Ms & Hf1 & Hf2).
  eapply freels_merge; eauto.
Qed.

Lemma eqdomenv_nil_enil : forall E , eq_dom_env E nil -> E = empenv.
Proof.
  intros.
  unfold eq_dom_env in *; simpl in *.
  apply EnvMod.extensionality; intros.
  rewrite EnvMod.emp_sem.
  lets H100 : H a.
  assert (EnvMod.get E a = None \/ EnvMod.get E a <> None) as H200.
  destruct (EnvMod.get E a); tauto.
  destruct H200.
  auto.
  assert (forall t, ~ exists l, EnvMod.get E a = Some (l, t)) as H200.
  intros.
  lets H200 : H100 t; destruct H200; auto.
  clear H100; rename H200 into H100.
  assert (forall t l, ~ EnvMod.get E a = Some (l, t)) as H200.
  intros.
  lets H200 : H100 t.
  intro; apply H200; eauto.
  clear H100; rename H200 into H100.
  assert (forall b, EnvMod.get E a <> Some b) as H200.
  intros.
  destruct b.
  apply H100; auto.
  clear H100; rename H200 into H100.
  destruct (EnvMod.get E a); tryfalse.
Qed.

Lemma lb_sub_l :
  forall l1 l2 x,
    EnvMod.lb x (l1 ++ l2) ->
    EnvMod.lb x l1.
Proof.
  induction l1, l2; intros; simpl in *; auto.
  destruct a; mytac; auto.
  rewrite app_nil_r in H0; auto.
  destruct a; mytac; auto.
  eapply IHl1; eauto.
Qed.

Lemma is_orderset_sub_r :
  forall l1 l2,
    EnvMod.is_orderset (l1 ++ l2) ->
    EnvMod.is_orderset l2.
Proof.
  induction l1; induction l2; intros; simpl in *; mytac.
  destruct a; mytac; auto.
  destruct a, a0; mytac; auto.
  gen H0; clear; intros.
  induction l1; simpl in *; mytac; auto.
  destruct a; mytac; auto.
  cut (EnvMod.is_orderset ((a0,b0)::l2)).
  intros.
  simpl in H1; mytac; auto.
  auto.
Qed.

Lemma is_orderset_sub_l :
  forall l1 l2,
    EnvMod.is_orderset (l1 ++ l2) ->
    EnvMod.is_orderset l1.
Proof.
  induction l1; induction l2; intros; simpl in *; mytac.
  destruct a; mytac.
  rewrite app_nil_r in H; auto.
  rewrite app_nil_r in H0; auto.
  destruct a; mytac.
  eapply lb_sub_l; eauto.
  eauto.
Qed.

Lemma lb_blt_mid :
  forall l1 l2 x a b,
    EnvMod.lb x (l1 ++ (a,b)::l2) ->
    identspec.blt x a = true.
Proof.
  induction l1, l2; intros; simpl in *; mytac; auto.
  destruct a; mytac.
  eapply IHl1; eauto.
  destruct a; mytac.
  eapply IHl1; eauto.
Qed.

Lemma lb_sub_r :
  forall l1 l2 x,
    EnvMod.lb x (l1 ++ l2) ->
    EnvMod.lb x l2.
Proof.
  induction l1, l2; intros; simpl in *; auto.
  destruct a, p; mytac.
  eapply lb_blt_mid; eauto.
  cut (EnvMod.lb x ((a0,b0)::l2)).
  intros.
  simpl in H1; mytac; auto.
  apply IHl1; auto.
Qed.

Lemma lb_remove_mid :
  forall l1 l2 l3 x,
    EnvMod.lb x (l1 ++ l2 ++ l3) ->
    EnvMod.lb x (l1 ++ l3).
Proof.
  intros.
  gen l1 l3 l2.
  induction l1, l3, l2; intros; simpl in *; auto.
  destruct p0, p; mytac.
  eapply lb_blt_mid; eauto.
  replace (l2 ++ (a0, b0)::l3) with ((l2 ++ (a0,b0)::nil) ++ l3) in H0.
  eapply lb_sub_r; eauto.
  rewrite app_assoc_reverse; simpl; auto.
  destruct a; mytac; auto.  
  rewrite app_nil_r in H0; rewrite app_nil_r.
  eapply lb_sub_l; eauto.
  destruct a; mytac; auto.
  replace (l1 ++ p0 :: l2 ++ p :: l3) with (l1 ++ (p0::l2) ++ p::l3) in H0.
  eapply IHl1; eauto.
  simpl; auto.
Qed.

Lemma is_orderset_remove_mid :
  forall l1 l2 l3,
    EnvMod.is_orderset (l1 ++ l2 ++ l3) ->
    EnvMod.is_orderset (l1 ++ l3).
Proof.
  intros.
  gen l1 l3 l2.
  induction l1, l3, l2; intros; simpl in *; auto.
  destruct p0, p; mytac.
  gen H0; clear; intros.
  induction l2; simpl in *; mytac; auto.
  destruct a; mytac; auto.
  replace (l2 ++ (a0,b0)::l3) with ((l2 ++ (a0,b0)::nil) ++ l3) in H0.
  eapply is_orderset_sub_r; eauto.
  rewrite app_assoc_reverse; simpl; auto.
  destruct a; mytac.
  rewrite app_nil_r in H; rewrite app_nil_r.
  eapply lb_sub_l; eauto.
  replace (l1 ++ p::l2 ++ nil) with (l1 ++ (p::l2) ++ nil) in H0.
  eapply IHl1; eauto.
  simpl; auto.
  destruct a; mytac.
  replace (l1 ++ p0::l2 ++ p::l3) with (l1 ++ (p0::l2) ++ p::l3) in H.
  eapply lb_remove_mid; eauto.
  simpl; auto.
  replace (l1 ++ p0::l2 ++ p::l3) with (l1 ++ (p0::l2) ++ p::l3) in H0.
  eapply IHl1; eauto.
  simpl; auto.
Qed.

Lemma eqdomenv_conse_pre' :
  forall ls x v,
    EnvMod.is_orderset ls ->
    EnvMod.get' ls x = Some v ->
    exists ls1 ls2 ls',
      ls = ls1 ++ (x,v)::ls2 /\
      ls' = ls1 ++ ls2 /\
      EnvMod.is_orderset ls1 /\
      EnvMod.is_orderset ls2 /\
      EnvMod.is_orderset ls'.
Proof.
  induction ls; intros; simpl in *.
  tryfalse.
  destruct a; mytac.
  remember (identspec.beq x a) as b100; destruct b100.
  
  symmetry in Heqb100; apply identspec.beq_true_eq in Heqb100; subst a.
  inverts H0.
  exists (@nil (identspec.A * blocktypespec.B)) ls ls;
    mytac; simpl; auto.

  lets H100 : IHls H1 H0; mytac. 
  exists ((a,b)::x0) x1 ((a,b)::x0 ++ x1);
    mytac; simpl; auto.
  split.
  eapply lb_sub_l; eauto.
  eapply is_orderset_sub_l; eauto.
  change (x0 ++ (x, v)::x1) with (x0 ++ ((x,v)::nil) ++ x1) in H, H1.
  split.
  eapply lb_remove_mid; eauto.
  eapply is_orderset_remove_mid; eauto.
Qed.

Lemma EnvMod_lb_neq :
  forall l1 l2 a x v,
    EnvMod.lb a (l1 ++ (x, v)::l2) -> identspec.beq x a = false.
Proof.
  induction l1; induction l2; intros; simpl in *; mytac.
  apply EnvMod.bgt_t_beq_f in H; auto.
  destruct a; mytac.
  apply IHl2; auto.
  destruct a; mytac.
  eapply IHl1; eauto.
  destruct a; mytac.
  eapply IHl1; eauto.
Qed.

Lemma is_orderset_get'_none :
  forall l1 l2 x v,
    EnvMod.is_orderset (l1 ++ (x, v)::l2) ->
    EnvMod.get' (l1 ++ l2) x = None.
Proof.
  induction l1; induction l2; intros; simpl in *.
  auto.

  destruct a; mytac.
  apply EnvMod.blt_t_beq_f in H.
  rewrite H.
  apply IHl2; auto.

  destruct a; mytac.
  cut (identspec.beq x a = false).
  intros H100; rewrite H100.
  eapply IHl1; eauto.
  eapply EnvMod_lb_neq; eauto.

  destruct a; mytac.
  cut (identspec.beq x a = false).
  intros H100; rewrite H100.
  eapply IHl1; eauto.
  eapply EnvMod_lb_neq; eauto.
Qed.

Lemma envmod_get'_remove_mid :
  forall l1 l2 l3 x,
    EnvMod.is_orderset (l1 ++ l2 ++ l3) ->
    EnvMod.get' l2 x = None ->
    EnvMod.get' (l1 ++ l2 ++ l3) x = EnvMod.get' (l1 ++ l3) x.
Proof.
  intros.
  gen l1 l3 l2.
  induction l1; induction l3; induction l2;
  intros; simpl in *; auto.

  destruct a; mytac.
  rewrite app_nil_r; auto.
  
  destruct a0, a; mytac.
  rewrite <- IHl2; auto.
  destruct (identspec.beq x a0); tryfalse || auto.
  destruct (identspec.beq x a0); tryfalse || auto.
  
  destruct a, a0; mytac.
  rewrite<- IHl2; auto.
  destruct (identspec.beq x a); tryfalse || auto.
  rewrite app_nil_r in H, H1.
  rewrite app_nil_r.
  replace (l1 ++ (a0, b0)::l2) with (l1 ++ ((a0,b0)::nil) ++ l2).
  eapply IHl1; simpl; auto. 
  destruct (identspec.beq x a0); tryfalse || auto.
  simpl; auto.
  rewrite app_nil_r in H, H1.
  rewrite app_nil_r.
  split.
  replace (l1 ++ (a0, b0)::l2) with (l1 ++ ((a0,b0)::nil) ++ l2) in H.
  eapply lb_remove_mid; eauto.
  simpl; auto.
  replace (l1 ++ (a0, b0)::l2) with (l1 ++ ((a0,b0)::nil) ++ l2) in H1.
  eapply is_orderset_remove_mid; eauto.
  simpl; auto.
  destruct (identspec.beq x a0); tryfalse || auto.

  destruct a, a1; mytac.
  rewrite <- IHl2.
  destruct (identspec.beq x a); tryfalse || auto.
  replace (l1 ++ (a1, b0) :: l2 ++ a0 :: l3) with (l1 ++ ((a1, b0)::nil) ++ (l2 ++ a0 :: l3)).

  apply IHl1; simpl; auto.
  destruct (identspec.beq x a1); tryfalse || auto.
  simpl; auto.
  split.
  replace (l1 ++ (a1, b0)::l2 ++ a0::l3) with (l1 ++ ((a1,b0)::nil) ++ (l2 ++ a0::l3)) in H.
  eapply lb_remove_mid; eauto.
  simpl; auto.
  replace (l1 ++ (a1, b0)::l2 ++ a0::l3) with (l1 ++ ((a1,b0)::nil) ++ (l2 ++ a0::l3)) in H1.
  eapply is_orderset_remove_mid; eauto.
  simpl; auto.
  destruct (identspec.beq x a1); tryfalse || auto.
Qed.


Lemma eqdomenv_conse_pre :
  forall E x v,
    EnvMod.get E x = Some v ->
    exists E1 E2 E',
      EnvMod.join E' (EnvMod.sig x v) E /\
      getaddr E = getaddr E1 ++ v::getaddr E2 /\
      getaddr E' = getaddr E1 ++ getaddr E2.
Proof.
  intros.
  destruct E.
  unfold EnvMod.get in H; simpl in H.
  lets H100 : eqdomenv_conse_pre' i H; mytac.
  exists (EnvMod.listset_con H2) (EnvMod.listset_con H3) (EnvMod.listset_con H4);
    mytac; simpl.
  unfold EnvMod.join; intros.
  unfold EnvMod.get; simpl.
  remember (EnvMod.get' (x0 ++ x1) a) as b100;
    remember (identspec.beq a x) as b200;
    remember (EnvMod.get' (x0 ++ (x, v) :: x1) a) as b300.
  destruct b100; destruct b200.
  
  lets H100 : is_orderset_get'_none i.
  symmetry in Heqb200; apply identspec.beq_true_eq in Heqb200; subst.
  rewrite H100 in Heqb100; tryfalse.

  assert (EnvMod.get' ((x,v)::nil) a = None).
  simpl.
  rewrite <- Heqb200; auto.
  replace (x0 ++ (x, v) :: x1) with ((x0 ++ ((x, v)::nil) ++ x1)) in i, Heqb300.
  lets H100 : envmod_get'_remove_mid i H0.
  rewrite H100 in Heqb300.
  rewrite <- Heqb300 in Heqb100.
  subst b300; auto.
  simpl; auto.

  symmetry in Heqb200; apply identspec.beq_true_eq in Heqb200; subst a.
  rewrite H in Heqb300.  
  subst b300; auto.
  
  assert (EnvMod.get' ((x,v)::nil) a = None).
  simpl.
  rewrite <- Heqb200; auto.
  replace (x0 ++ (x, v) :: x1) with ((x0 ++ ((x, v)::nil) ++ x1)) in i, Heqb300.
  lets H100 : envmod_get'_remove_mid i H0.
  rewrite H100 in Heqb300.
  rewrite <- Heqb300 in Heqb100.
  subst b300; auto.
  simpl; auto.

  clear.
  destruct v.
  gen x0 x1 x b t.
  induction x0, x1; intros; simpl in *; auto.
  destruct a.
  destruct b0.
  simpl.
  rewrite IHx0; simpl; auto.
  destruct a.
  destruct b0.
  simpl.
  rewrite IHx0.
  simpl; auto.
  clear.

  gen x0 x1.
  induction x0, x1; intros; simpl in *; auto.
  destruct a.
  destruct b.
  simpl.
  repeat rewrite app_nil_r; auto.
  destruct a.
  destruct b.
  destruct p.
  destruct b0.
  simpl.
  rewrite IHx0.
  simpl; auto.
Qed.

Lemma ListSet_setIn_in_decllist_true :
  forall x t d,
    ListSet.set_In (x, t) (getlenvdom d) -> in_decllist x d = true.
Proof.
  intros.
  gen x t.
  induction d; intros; simpl in *.
  tryfalse.
  destruct H.
  inverts H.
  apply orb_true_intro; left.
  apply Zeq_is_eq_bool; auto.
  apply IHd in H.
  apply orb_true_intro; right.
  auto.
Qed.

Lemma  eqdomenv_conse:
  forall x t E d,
    in_decllist x d  = false ->
    eq_dom_env E (getlenvdom (dcons x t d)) ->
    exists l E1 E2 E',        
      getaddr E' = getaddr E1 ++ getaddr E2 /\
      EnvMod.sub E' E /\
      EnvMod.get E x = Some (l,t) /\ 
      getaddr E = (getaddr E1) ++ (l,t) :: getaddr E2 /\ 
      eq_dom_env E' (getlenvdom d).
Proof.
  intros.
  unfold eq_dom_env in *; simpl in *.
  assert (exists l, EnvMod.get E x = Some (l, t)) as H100.
  apply H0; auto.
  destruct H100.
  rewrite H1.
  exists x0.
  

  lets H100 : eqdomenv_conse_pre H1; mytac.
  exists x1 x2 x3; mytac; auto.
  eapply EnvMod.join_sub_l; eauto.
  clear H3 H4.
  split; intros.

  lets H100 : H0 x4 t0; destruct H100.
  clear H5.
  assert (x4 = x \/ x4 <> x) as H100 by repeat decide equality; destruct H100.
  subst.
  apply ListSet_setIn_in_decllist_true in H3.
  tryfalse.
  assert (exists l, EnvMod.get E x4 = Some (l, t0)) as H100.
  apply H4; auto.
  mytac.
  lets H100 : EnvMod.join_disj_meq H2; mytac.
  apply EnvMod.meq_eq in H8; substs.
  rewrite EnvMod.merge_sem in H6.
  rewrite EnvMod.get_sig_none in H6; auto.
  destruct (EnvMod.get x3 x4) eqn : eq1; tryfalse.
  inverts H6.
  unfold get; simpl; eauto.
  
  lets H100 : H0 x4 t0; destruct H100.
  clear H4.
  mytac.
  assert (x4 = x \/ x4 <> x) as H100 by repeat decide equality; destruct H100.
  subst.
  unfold get in H3; simpl in H3.
  lets H100 : H2 x; rewrite H3 in H100.
  rewrite EnvMod.get_sig_some in H100; tryfalse.
  assert (EnvMod.get E x4 = Some (x5, t0)) as H100.
  unfold get in H3; simpl in H3.
  lets H100 : H2 x4; rewrite H3 in H100.
  rewrite EnvMod.get_sig_none in H100; auto.
  destruct (EnvMod.get E x4); tryfalse || subst; auto.
  assert (exists l, EnvMod.get E x4 = Some (l, t0)) as H200 by eauto.
  apply H5 in H200; destruct H200.
  inverts H6; tryfalse.
  auto.
Qed.

Lemma free_locality2' :
  forall M1 M2 M12 b i ls,
    join M1 M2 M12 ->
    ptomvallist (b, i) true ls M1 ->
    freeb M12 b i (length ls) = Some M2.
Proof.
  intros.
  gen M1 M2 M12 b i.
  induction ls; intros; simpl in *; mytac.
  auto.
  assert (get M12 (b, i) = Some (true, a)) as H100.
  eapply mem_join_get_get_l_true; eauto.
  eapply mem_join_get_get_l_true; eauto.
  unfold ptomval in *; subst x; apply get_sig_some.
  
  change Z with offset; rewrite H100; clear H100.
  apply join_comm in H0.
  lets H100 : join_assoc_l H0 H; mytac.
  erewrite IHls; eauto.
  apply join_comm in H3.
  erewrite <- mem_join_true_del; eauto.
  unfold ptomval in H1; rewrite <- H1.
  auto.
Qed.


Lemma  free_locality2 : forall  M1 M2 Mc M' M b t v,
                          join M M1 M2 -> join Mc M' M -> mapstoval (b, 0%Z) t true v Mc 
                          ->   exists MM, free t b M2 = Some MM /\ join M' M1 MM. 
Proof.
  intros.
  lets H100 : join_assoc_l H0 H; mytac.
  eexists; mytac; eauto.
  gen H1 H3; clear; intros.
  unfold mapstoval in *; mytac.
  unfold free in *.
  erewrite <- encode_val_length.
  eapply free_locality2'; eauto.
Qed.

Definition sub_dom_env (E:env)(d:edom) :=
  forall x t, ListSet.set_In (x,t) d -> 
              exists l, EnvMod.get E x = Some (l, t).

Lemma  sub_dom_exists : forall  x t d E,
                          sub_dom_env  E (getlenvdom (dcons x t d)) ->
                          exists l,  EnvMod.get E x = Some (l, t).
Proof.
  intros.
  unfold sub_dom_env in *; simpl in *.
  lets H100 : H x t.
  apply H100; auto.
Qed.

Lemma  subdomenv_conse:
  forall x t E d,
    sub_dom_env E (getlenvdom (dcons x t d)) ->
    sub_dom_env E (getlenvdom d) /\
    exists l, EnvMod.get E x = Some (l,t).

Proof.
  intros.
  lets H100 : sub_dom_exists H; mytac.
  unfold sub_dom_env in *; simpl in *.
  intros.
  lets H100 : H x1 t0.
  apply H100; auto.
  eauto.
Qed.

Lemma envsub_get : 
  forall E' E x l t,
    EnvMod.sub E' E ->  EnvMod.get E' x= Some (l, t) ->  
    EnvMod.get E x  = Some (l, t).
Proof.
  intros.
  eapply EnvMod.get_sub_get; eauto.
Qed.

Lemma  buidq_intro_e : forall  d a  G E M isr aux O E' aop,
                         EnvMod.sub E' E ->
                         Some a = buildq d -> 
                         (G, E,  M, isr, aux, O, aop) |= a ->
                         sub_dom_env E' (getlenvdom d) -> 
                         (G, E',  M, isr, aux, O, aop) |= a.
Proof.
  inductions d.
  intros.
  simpl in *.
  inverts H0.
  simpl in H1; mytac.
  simpl; splits; mytac.
  introv Hsub Ha Hsat Heq.
  simpl in Ha.
  remember (buildq d) as Hbu.
  remember (negb (in_decllist i d) && (good_decllist d)) as b100; destruct b100; tryfalse.  
  destruct Hbu; tryfalse.
  inverts Ha.
  destruct Hsat; mytac.
  simpl substmo in *.
  destruct H3; mytac.
  simpl in H;mytac.
  simpl in H0.
  lets Hdss : subdomenv_conse Heq.
  destruct Hdss as (Hget & (b & Head)).
  lets Hssd : sub_dom_exists  Heq.
  destruct Hssd as (ll & Heqq).
  lets Hee : envsub_get Hsub Heqq.
  rewrite Head in Heqq.
  inverts Heqq.
  unfold get in H6; simpl in H6.
  rewrite Hee in H6.
  inverts H6.
  exists  x x0 M empabst O O.
  splits; mytac; eauto.
  exists x1.
  simpl.
  do 7 eexists; splits; mytac; eauto.
  mytac.
  mytac.
  eexists; splits; eauto.
  unfolds; auto.
  simpl.
  eauto.
Qed.

Lemma freels'_imply_freels : forall ls  M1 M2, freels ls M1 M2 -> 
                                               freels' ls M1 M2.  
Proof.
  intro ls.
  replace ls with (nil++ls) by auto.
  introv Hfr.
  simpl in Hfr.
  inductions Hfr. 
  constructors.
  inverts Hfr.
  constructors;eauto.
  simpl in IHHfr.
  constructors;eauto.
  constructors.
Qed.

Lemma freels'_split : forall ls2 ls1 ls  M' M , ls = ls1++ ls2 -> freels' ls M M' -> 
                                                exists M1, freels' ls1 M M1 /\ freels' ls2 M1 M'.

Proof.
  intros.
  inductions ls1.
  simpl in H.
  subst.
  exists M.
  splits; eauto.
  constructors.
  subst ls.
  apply  freels_imply_freels'  in H0.
  inverts H0.
  apply  freels'_imply_freels in H5.
  lets Hds : IHls1 H5.
  eauto.
  destruct Hds as (Ms1 & Hfr1 & Hfr2).
  apply  freels_imply_freels' in Hfr1.
  exists Ms1.
  splits.
  eapply  freels'_imply_freels. 
  constructors; eauto.
  auto.
Qed.


Lemma free_intro_aux2:  forall  d a G E  M M1 M2  isr aux O aop, 
                          Some a = buildq d -> 
                          (G, E,  M, isr, aux, O, aop) |= a ->
                          eq_dom_env E (getlenvdom d) ->  
                          join M M1 M2 ->
                          freels' (getaddr E) M2 M1. 
Proof.
  inductions d.
  simpl.
  introv Hsa Hsat Heq Hmj.
  inverts Hsa.
  simpl in Hsat; mytac.
  apply  eqdomenv_nil_enil in Heq.
  subst E.
  simpl.
  constructors.
  introv Heq Hsat Heqdom Hmj.
  simpl in Heq.
  remember (negb (in_decllist i d) && good_decllist d) as b100; destruct b100; tryfalse.
  remember (buildq  d) as Hbd; destruct Hbd; tryfalse.
  inverts Heq.
  symmetry in Heqb100; apply andb_true_iff in Heqb100; destruct Heqb100 as [ H100 H200 ].
  apply negb_true_iff in H100.
  lets Hs :   eqdomenv_conse H100 Heqdom.
  destruct Hs as (l &E1&E2&E' &Hje& Hsub &Henv & Hget & Heqs).
  rewrite Hget.
  destruct Hsat; mytac.
  simpl substmo in *.
  destruct H3; mytac.
  simpl in H; mytac.
  unfold get in H6; simpl in H6.
  rewrite H6 in Henv.
  inverts Henv.
  simpl in H0.
  lets Hrs :   free_locality2 Hmj H0 H7.
  destruct Hrs as (MM & Hfm & Hmmj).
  lets Hds : IHd  Heqs Hmmj.
  eauto.
  eapply buidq_intro_e; eauto.
  unfolds.
  unfolds in Heqs.
  intros.
  apply Heqs in H.
  eauto.
  lets Hres : freels'_split Hje Hds. 
  destruct Hres as (Mms & Hfas & Hfass).
  constructors;eauto.
Qed.


Lemma  free_intro: 
  forall  a d0 d G  E M1 isr aux o1 M2 M3 aop,
    Some a = buildq (revlcons d0 d)  ->  
    (G, E, M1, isr, aux, o1, aop) |= a ->
    eq_dom_env E (getlenvdom (revlcons d0 d)) -> 
    join M1 M2 M3 ->
    o1 = empabst /\ freels (getaddr E) M3 M2. 
Proof.
  introv Hsat Ha Heq Hmj.
  split.
  eapply  free_intro_aux1; eauto.
  eapply  freels_imply_freels'. 
  eapply  free_intro_aux2; eauto.
Qed.


Definition post_imp_linv (post:fpost) (li :LocalInv)   (vl:vallist)  logicl t  :=
  forall o O aop v,
    (o, O, aop) |= POST [post,  rev vl, v, logicl, t] ->
    satp o O (CurLINV li t).

Lemma good_fun_asrt_absop:
  forall p, GoodFunAsrt p ->
            forall ge le M ir aux abst op,
              (ge,le,M , ir, aux,abst, op) |= p -> 
              forall  le',
                (ge,le',M ,ir, aux,abst, op) |= p. 
Proof.
  introv.
  inductions p; introv Hgood; introv Hsat; introv; simpl in *;  tryfalse; auto.
  destruct Hgood as [Hgp Hgq].
  destruct Hsat as [Hsat1 Hsat2].
  lets Hgpp : IHp1 Hgp Hsat1.
  lets Hgqq : IHp2 Hgq Hsat2.
  splits.
  eapply Hgpp; eauto.
  eapply Hgqq; eauto.
  destruct Hgood as [Hgp Hgq].
  destruct Hsat as [Hsat1 | Hsat2].
  lets Hgpp : IHp1 Hgp Hsat1.
  left.
  eapply Hgpp;  eauto.
  lets Hgqq : IHp2 Hgq Hsat2.
  right.
  eapply Hgqq;  eauto.
  destruct Hsat as [x Hsatx].
  destruct Hgood as [Hgp Hgq].
  destruct Hsatx.
  repeat destruct H.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H2.
  subst.
  do 6 eexists.
  splits; eauto.
  destruct Hsat as [x Hsatx].
  lets Hp : H (Hgood x) Hsatx.
  exists x.
  eapply Hp;simpl; eauto.
Qed.


Lemma cont_frame_mono : forall p c ke ks o C' o' ks', 
                       ~ loststepabt p (c, (ke, ks)) o ->
                       loststep p (c, (ke, ks ## ks')) o C' o' -> 
                       exists c' ke' ks'',  loststep p (c, (ke, ks)) o (c', (ke',ks'')) o' 
                         /\ C' = (c',(ke',ks'' ## ks')).
Proof.
  intros.
  apply Classical_Prop.NNPP in H.
  destruct H as (C0 & tst0 & H).
  inverts H0.
  inverts H1.
  inverts H0;inverts H2;
  try solve [
  do 3 eexists;
  split;eauto;constructors;eauto;
  constructors;eauto;
  try solve [constructors;eauto]].
  
  do 3 eexists;
  split;eauto;constructors;eauto;
  constructors;eauto;
  try solve [eapply eaelemaddr_step;eauto].
  
  do 3 eexists;
  split;eauto;constructors;eauto;
  constructors;eauto;
  try solve [eapply eaelem_step;eauto].

  inverts H0.
  inverts H2;(inverts H as Hlo;tryfalse); try solve [
  try (destruct ks ;inverts H0);
  try (destruct ks ;inverts H5);
  rewrite_addcont;
  do 3 eexists;split;eauto;constructors;eauto;eapply stmt_step;eauto; constructors;eauto |
  destruct ks;simpl in *;tryfalse;
  [inverts Hlo;inverts H;inverts H1|idtac];
  inverts H0;rewrite_addcont;
  do 3 eexists;split;eauto;constructors;eauto;eapply stmt_step;eauto; constructors;eauto |
  destruct ks;simpl in *;tryfalse;
  [inverts Hlo;inverts H;inverts H0|idtac];
  inverts H4;rewrite_addcont;
  do 3 eexists;split;eauto;constructors;eauto;eapply stmt_step;eauto; constructors;eauto].
  inverts Hlo;inverts H;inverts H0.
  inverts H.
  do 3 eexists;split;eauto;constructors;eauto;eapply stmt_step;eauto; constructors;eauto.
  destruct ks;simpl in *;tryfalse.
  inverts Hlo;inverts H;inverts H1.
  inverts Hlo;inverts H;inverts H1.
  inverts H4;inverts H0;rewrite_addcont.
  do 3 eexists;split;eauto;constructors;eauto;eapply stmt_step;eauto; constructors;eauto.
  inverts Hlo;inverts H;inverts H0.
  inverts H1.
  lets Hcall: callcont_some_addcont ks' H5.
  rewrite Hcall in H3. inverts H3.
  do 3 eexists;split;eauto;constructors;eauto;eapply stmt_step;eauto; constructors;eauto.
  inverts H1. 
  inverts H;tryfalse.
  inverts H8;tryfalse. inverts H;inverts H0.
  inverts H;inverts H0.
  inverts H13.
  lets Hint: intcont_some_addcont ks' H14.
  rewrite Hint in H2.
  inverts H2.
  do 3 eexists;split;eauto;eapply exint_step;eauto.
  inverts H1;do 3 eexists;split;eauto;eapply eoi_step;eauto.
  inverts H1;do 3 eexists;split;eauto;eapply cli_step;eauto.
  inverts H1;do 3 eexists;split;eauto;eapply sti_step;eauto.
  inverts H1;do 3 eexists;split;eauto;eapply encrit_step;eauto. 
  inverts H1;do 3 eexists;split;eauto;eapply excrit_step;eauto.
  inverts H1;do 3 eexists;split;eauto;eapply checkis_step;eauto.
Qed.

Lemma fcall_not : 
  forall c ke ks ks', 
    ~ IsFcall (c, (ke, ks ## ks')) -> 
    ~ IsFcall (c, (ke, ks )).
Proof.
  introv Hfa.
  introv Hisf.
  apply Hfa.
  unfold IsFcall in *.
  destruct Hisf as (f&vl&tl&ks0& Hea).
  inverts Hea.
  do 4 eexists; eauto.
Qed.


Lemma callcont_nonone_addcont: 
  forall ks ks1,
    callcont ks <> None -> callcont (ks ## ks1) <> None.
Proof.
  intros.
  assert (exists x, callcont ks = Some x).
  destruct (callcont ks).
  eexists;auto.
  tryfalse.
  destruct H0.
  assert (callcont (ks ## ks1)= Some (x ## ks1)).
  apply callcont_some_addcont;auto.
  intro;tryfalse.
Qed.


Lemma  loststepabt_cont_loststepabt' :
      forall (p : progunit) (c : cureval) (ke : exprcont)
         (ks ks' : stmtcont) (o2 : taskst),
       ~ loststepabt p (c, (ke, ks )) o2 ->
       ~ loststepabt p (c, (ke, ks ## ks')) o2.
Proof.
  intros.
  red. intro.
  apply H.
  unfold loststepabt in *.
  red. intro.
  apply H0.
  clear H H0.
  destruct H1 as (C' & tst' & H).
  inverts H;
  inverts H0.
  inverts H;inverts H1;
  try solve [
  do 2 eexists; constructors;eauto; constructors;eauto;try solve [constructors;eauto]].

  do 2 eexists; constructors;eauto; constructors;eauto;try solve [eapply eaelemaddr_step;eauto].
  
  do 2 eexists; constructors;eauto; constructors;eauto;try solve [eapply eaelem_step;eauto].
    
  do 2 eexists; constructors;eauto; constructors;eauto;
  eapply ecast_step;eauto.
  do 2 eexists; constructors;eauto; constructors;eauto;
  eapply ecastnull_step;eauto.
  do 2 eexists; constructors;eauto; constructors;eauto;
  eapply ecastcomptr_step;eauto.
  inverts H;inverts H1;
  try solve [try (lets Hcall : callcont_some_addcont H0);
             try (lets Hcall : callcont_some_addcont H2);
  do 2 eexists; constructors;eauto; eapply stmt_step;eauto;constructors;eauto |
  destruct ks;simpl in H ;inverts H ;do 2 eexists;constructors;eauto;eapply stmt_step;eauto;constructors;eauto |
  destruct ks;simpl in H3;inverts H3;do 2 eexists;constructors;eauto;eapply stmt_step;eauto;constructors;eauto ].
  apply callcont_nonone_addcont with (ks1:=ks') in H0.
  do 2 eexists;constructors;eauto;eapply stmt_step;eauto;eapply sretv_step;eauto.
  lets Hcall : intcont_some_addcont H1;
  do 2 eexists;eapply exint_step;eauto.
  do 2 eexists;eapply eoi_step;eauto.
  do 2 eexists;eapply cli_step;eauto.
  do 2 eexists;eapply sti_step;eauto.
  do 2 eexists;eapply encrit_step;eauto. 
  do 2 eexists;eapply excrit_step;eauto.
  do 2 eexists;eapply checkis_step;eauto.
Qed.


Lemma getaddr_exist : forall ls, exists al, getaddrlist ls = al.
Proof.
  introv.
  inductions ls.
  simpl.
  eexists; eauto.
  simpl.
  destruct a.
  destruct p.
  destruct IHls.
  exists ((b,t) :: x); rewrite H. eauto.
Qed. 


Lemma get_env_addrlist_ex : forall E, exists al, getaddr E = al.
Proof.
  introv. destruct E.
  simpl.
  eapply getaddr_exist.
Qed.

Lemma eval_length_tlmatch :
  forall tl dl,
    tlmatch tl dl -> length tl = length_dl dl.
Proof.
  induction tl; induction dl; simpl; intros;
  tryfalse || auto.
  cut (length tl = length_dl dl).
  intros H100; rewrite H100; auto.
  apply IHtl; intuition.
Qed.

Lemma length_prop : 
  forall (vl:vallist) tl d1 d2, 
    length vl = length tl -> tlmatch (rev tl) d1 -> 
    length vl <= length_dl (revlcons d1 d2).
Proof.
  intros.
  apply eval_length_tlmatch in H0.
  rewrite rev_length in H0.
  rewrite H.
  rewrite H0.
  clear.
  cut (length_dl (revlcons d1 d2) = length_dl d1 + length_dl d2).
  intros.
  rewrite H; omega.
  gen d2.
  induction d1; induction d2; simpl in *; auto.
  rewrite IHd1; simpl; omega.
  rewrite IHd1; simpl; omega.
Qed.

Lemma tl_vl_match_leneq:
  forall tl vl,  tl_vl_match tl vl = true -> length vl =length tl.
Proof.
  intros.
  generalize dependent vl.
  induction tl;intros.
  destruct vl;simpl in H;tryfalse.
  simpl;auto.
  destruct vl.
  simpl in H.
  false.
  simpl in H.
  simpl.
  destruct (type_val_match a v);tryfalse.
  apply IHtl in H.
  auto.
Qed.


Lemma alloc_code_eq' : forall p C o1 C' o1' o2  C'' o2',   
                         losallocstep p C o1 C' o1' ->  losallocstep p C o2 C'' o2' -> C' = C''.
Proof.
  introv Hlos Hlos'.
  unfolds in Hlos.
  unfolds in Hlos'.
  destruct Hlos as (Hstep1 & Hisa).
  destruct Hlos' as(Hstep2 & _).
  unfolds in Hisa.
  destruct Hisa as (vl & dl & ks & x & t & Hc & Hlen & Hnil & Hnnil).
  subst.
  inverts Hstep1; inverts Hstep2; tryfalse.
  inverts H;inverts H0; tryfalse.
  inverts H1;inverts H; inverts H2; inverts H3; tryfalse.
  inverts H1;inverts H; inverts H2; inverts H3; tryfalse.
  inverts H1;inverts H; inverts H2; inverts H3; tryfalse.
  inverts H1;inverts H; inverts H2; inverts H3; tryfalse.
  auto.
  auto.
Qed.

Lemma alloc_stepn_code_eq :
  forall n p C o C' o',
    losallocstepn n p C o C' o' -> 
    forall  C'' o  o'', losallocstepn n p C o C'' o'' ->  C' =  C''.
Proof.
  introv Hos.
  inductions Hos.
  introv H.
  inverts H; auto.
  introv H'.
  inverts H'.
  lets Hre : alloc_code_eq' H H1.
  subst.
  eapply IHHos; eauto.
Qed.

Fixpoint good_env_decllist le dl :=
  match dl with 
    | dnil => True
    | dcons x _ dl' => (~EnvMod.indom le x) /\ (good_env_decllist le dl')
  end.

Lemma set_env_good_env_decllist:
  forall le dl i b t, 
    good_env_decllist le dl ->
    ~ EnvMod.indom le i ->
    good_decllist dl = true ->
    in_decllist i dl = false ->
    good_env_decllist (EnvMod.set le i (b, t)) dl.
Proof.
  intros.
  gen le.
  induction dl.
  intros.
  simpl;auto.
  intros.
  simpl in *.
  lets Hor : orb_false_elim H2.
  destruct Hor.
  split.
  destruct H.
  red.
  intros.
  apply H.
  lets H7: EnvMod.indom_get H6.
  destruct H7.
  EnvMod.rewrite_get.
  rewrite identspec.neq_beq_false in H7.
  apply EnvMod.get_indom.
  eexists;eauto.
  apply Zeq_bool_neq;eauto.
  apply IHdl;eauto.
  lets Hand: andb_prop H1.
  apply Hand.
  apply H.
Qed.

Lemma alloc_exist_mem_env: 
  forall x t le M le' M',
    alloc x t le M le' M' ->
    exists M'' le'' b v,  mapstoval (b,0)%Z t true v M'' /\ 
                          le'' = sig x (b,t)/\ join M M'' M'/\
                          join le le'' le'.
Proof.
  intros.
  destruct H as [b].
  destructs H.
  exists (allocb emp b 0%Z (typelen t)).
  exists (EnvMod.sig x (b, t)).
  exists b.
  exists Vundef.
  split.
  apply alloc_empmem_mapstoval.
  split.
  auto.
  split.
  apply join_comm.
  rewrite H0.
  eapply join_allocb;eauto.
  apply join_emp;eauto.
  rewrite H2.
  apply EnvMod.join_comm.
  assert (EnvMod.sig x (b, t) = EnvMod.set EnvMod.emp x (b, t)).
  apply EnvMod.extensionality.
  intros.
  EnvMod.rewrite_get.
  rewrite H3.
  eapply EnvMod.join_set_nindom_l;eauto.
  apply EnvMod.join_emp;eauto.
Qed.

(*lemmas and definitions for lemma alloc_store_exist_mem_env*)
Lemma set_empmem_sig_eq : forall a val, set empmem a val = sig a val.
Proof.
  intros.
  join auto.
Qed.

Lemma beq_Z_Zeqb_ident : forall a b : Z, beq_Z a b = Z.eqb a b.
  induction a; induction b; intros; simpl; auto.
Qed.

Fixpoint init_mem (b:block) (i:offset) (vl:mvallist) {struct vl} : mem :=
  match vl with
    | nil => empmem
    | u :: vl' => set (init_mem b (i+1)%Z vl') (b, i)%Z (true, u)
  end.

Definition fresh_index (M : mem) (b : block) (i : offset): Prop := 
  forall offset, (offset >= 0)%Z -> get M (b, i + offset)%Z = None.

Lemma init_mem_not_in_dom : forall b i vl n,
                              (n > 0)%Z -> get (init_mem b (i + n)%Z vl) (b, i) = None.
Proof.
  intros.
  generalize dependent n.
  generalize dependent i.
  induction vl.
  intros.
  simpl.
  apply emp_sem.

  intros.
  simpl.
  rewrite set_a_get_a'.
  replace (i + n + 1)%Z with (i + (n + 1))%Z.
  apply IHvl.
  omega.
  omega.
  simpl.
  assert (beq_Z (i + n) i = false).

  assert (i + n <> i)%Z.
  omega.
  apply Z.eqb_neq in H0.
  rewrite <- H0.

  apply beq_Z_Zeqb_ident.
  intro.
  inverts H1.
  rewrite H3 in H0.
  rewrite Z.eqb_refl in H0; tryfalse.
Qed.

(* key lemma *)
Lemma ptomvallist_init_mem : forall b i vl, ptomvallist (b, i) true vl (init_mem b i vl).
Proof.
  intros.
  generalize dependent i.
  inductions vl.
  intro.
  simpl.
  auto.
  intro.
  simpl.
  exists (sig (b, i) (true, a)).
  exists (init_mem b (i+1)%Z vl).
  split.
  apply join_comm.
  
  apply join_sig_set'.
  lets Hx: init_mem_not_in_dom b i vl 1%Z.
  cut (1>0)%Z.
  intros.
  apply Hx in H.
  unfold get in *; simpl in *.
  remember (init_mem b (i + 1)%Z vl) as X.
  unfold HalfPermMap.get in *.
  auto.

  omega.
  split.
  unfold ptomval.
  auto.
  apply IHvl.
Qed.
  
Lemma init_mem_get_some : forall b i vl b1 ba ia,
  get (init_mem b i vl) (ba, ia) = Some b1 ->
  b = ba /\ exists off, (off >= 0)%Z /\ ia = (i + off)%Z.
Proof.
  intros.
  generalize dependent i.
  inductions vl.
  intros.
  simpl in H.
  unfold get in H.
  simpl in H.
  tryfalse.
  intros.

  pose proof addr_eq_dec (b, i) (ba, ia) as eq1.
  destruct eq1 as [eq1 | eq1].
  inversion eq1.
  subst.
  split; auto.
  exists 0%Z.
  split.
  omega.
  destruct ia.
  auto.
  auto.
  auto.
  
  simpl in H.
  rewrite set_a_get_a' in H; auto.
  apply IHvl in H.
  destruct H.
  split.
  auto.
  destruct H0.
  destruct H0.
  exists (1 + x)%Z.
  split.
  omega.
  rewrite Zplus_assoc.
  auto.
Qed.

(* key lemma *)
Lemma mem_set_a_set_a : forall (M:mem) a val1 val2, set (set M a val1) a val2 = set M a val2.
Proof.
  intros.
  eapply extensionality.
  intro.
  pose proof addr_eq_dec a a0.
  destruct H as [eq1 | eq1].
  substs.
  rewrite set_a_get_a.
  rewrite set_a_get_a.
  auto.
  
  rewrite set_a_get_a'.
  rewrite set_a_get_a'.
  rewrite set_a_get_a'.
  auto.
  auto.
  auto.
  auto.
Qed.


(* key lemma *)
Lemma mem_set_a_set_a' : forall (M:mem) a v a' v', a <> a' ->
  set (set M a v) a' v' = set (set M a' v') a v.
Proof.
  intros.
  eapply extensionality.
  intro.
  pose proof addr_eq_dec a a0 as eq1; destruct eq1 as [eq1|eq1];
    pose proof addr_eq_dec a' a0 as eq2; destruct eq2 as [eq2|eq2].
  subst.
  tryfalse.
  
  rewrite set_a_get_a'.
  substs.
  rewrite set_a_get_a.
  rewrite set_a_get_a.
  auto.
  auto.
  auto.
  auto.
  substs.
  rewrite set_a_get_a.
  rewrite set_a_get_a'.
  rewrite set_a_get_a.
  auto.
  auto.
  rewrite set_a_get_a'.
  rewrite set_a_get_a'.
  rewrite set_a_get_a'.
  rewrite set_a_get_a'.
  auto.
  auto.
  auto.
  auto.
  auto.
Qed.

Lemma memset_allocb_comm :
  forall M b i n len,
    (n > 0)%Z -> ((set (allocb M b (i + n)%Z len) (b, i) (true, Undef))
                  = ((allocb (set M (b, i) (true, Undef)) b (i + n)%Z len))).
Proof.
  intros.
  generalize dependent n.
  inductions len.
  intros.
  simpl.
  auto.
  intros.
  simpl.
  
  rewrite mem_set_a_set_a'.
  assert (n + 1 > 0)%Z.
  omega.
  pose proof IHlen (n + 1)%Z H0.
  rewrite <- Zplus_assoc.

  unfold set in *; simpl in *.
  rewrite H1.
  auto.
  unfold not.
  intro.
  inversion H0.
  assert ((i + n) > (i + 0))%Z.
  apply Zplus_gt_compat_l.
  auto.
  rewrite H2 in H1.
  omega.
Qed.


(* key lemma *)
Lemma allocb_storebytes_memjoin : forall M b i len val M',
   fresh_index M b i -> storebytes (allocb M b i len) (b, i) (list_repeat len val) = Some M' ->
   join M (init_mem b i (list_repeat len val)) M'.
Proof.
  intros.
  generalize dependent i.
  generalize dependent M.
  inductions len.
  simpl.
  intros.
  apply join_comm.
  apply join_emp.
  inversion H0.
  auto.

  intros.
  simpl in H0.
  rewrite set_a_get_a in H0.
  destruct (storebytes (set (allocb M b (i + 1)%Z len) (b, i) (true, Undef)) (b, i+1)%Z (list_repeat len val)) eqn:eq1.
  inversion H0. clear H0.

(*  
  unfold MemMod.join.
  intro.
*)

  assert (fresh_index (set M (b, i) (true, Undef)) b (i + 1)%Z).
  unfold fresh_index.
  intros.
  unfold fresh_index in H.
  pose proof H (1 + offset)%Z.
  assert (1 + offset >= 0)%Z.
  omega.
  apply H1 in H3.
  rewrite set_a_get_a'.
  rewrite <- Zplus_assoc.
  auto.
  simpl.

  assert (beq_Z i (i + 1 + offset) = false).
(*  rewrite beq_Z_Zeqb_ident.*)
  rewrite Z.eqb_neq.
  omega.
  intro; inverts H5; substs.
  rewrite <- H7 in H4.
  rewrite Z.eqb_refl in H4; tryfalse.

  
  unfold list_repeat; fold (list_repeat (A:=memval)).
  unfold init_mem; fold init_mem.
  rewrite memset_allocb_comm in eq1.
  lets Hx: IHlen H0 eq1.
  remember (init_mem b (i + 1)%Z (list_repeat len val)) as X.

  assert(join M (set X (b, i) (true, Undef)) m).
  eapply mem_join_set_true_comm; eauto.
  pose proof H 0%Z.
  rewrite Z.add_0_r in H1.
  eapply H1.
  omega.

  rewrite HeqX.
  eapply init_mem_not_in_dom.
  omega.

  assert((set X (b, i) (true, val)) = (set (set X (b, i) (true, Undef)) (b, i) (true, val))).
  symmetry.
  eapply mem_set_a_set_a.
 
  apply join_comm in H1.
  apply join_comm.
  rewrite H3.
  eapply map_join_set_none in H1; eauto.
  pose proof H 0%Z.
  rewrite Z.add_0_r in H4.
  eapply H4.
  omega.
  omega.

  tryfalse.
Qed.

(* key lemma *)
Lemma fresh_implies_fresh_index : forall M b i, fresh M b -> fresh_index M b i.
Proof.
  intros.
  unfold fresh_index.
  intros.
  destruct (get M (b, (i + offset)%Z)) eqn:eq1.
  false.
  unfold fresh in H.
  pose proof H (b, (i + offset)%Z) (i + offset)%Z.
  unfold not in H1.
  apply H1.
  auto.
  unfold indom.
  exists p.
  auto.
  auto.
Qed.

(* key lemma *)
Lemma mem_join_sig_r : forall (M:mem) a v, ~indom M a -> join M (sig a v) (set M a v).
Proof.
  intros.
  eapply mem_sig_set.
  unfolds in H.
  unfold indom in H.
  destruct (get M a) eqn : eq1; auto.
  false; apply H.
  eauto.
Qed.


(* key lemma, same as above, should be generalized in to MapLib.v? *)
Lemma env_join_sig_r : forall M a v, ~EnvMod.indom M a -> EnvMod.join M (EnvMod.sig a v) (EnvMod.set M a v).
Proof.
  intros.
  unfold EnvMod.join.
  intro.
  rewrite EnvMod.sig_sem.
  destruct (identspec.beq a a0) eqn:eq1.
  rewrite EnvMod.set_a_get_a.
  destruct (EnvMod.get M a0) eqn:eq2.
  apply identspec.beq_true_eq in eq1.
  subst.
  unfold not in H.
  apply H.
  unfold EnvMod.indom.
  exists b.
  auto.
  auto.
  auto.
  rewrite EnvMod.set_a_get_a'.
  destruct (EnvMod.get M a0) eqn:eq2.
  auto.
  auto.
  auto.
Qed.

Lemma fresh_get_none :
  forall (m:mem) b i,
    fresh m b ->
    get m (b, i) = None.
Proof.
  intros.
  unfolds in H.
  unfold indom in H.
  pose proof H (b, i) i.
  assert ((b, i) = (b, i)).
  auto.
  apply H0 in H1.
  destruct (get m (b, i)) eqn :eq1; auto.
  unfold not in H1.
  false; apply H1; eauto.
Qed.

(*end of lemmas and definitions*)
Lemma alloc_store_exist_mem_env: 
  forall x v b  t le M le' M' M'',
    alloc x t le M le' M' -> 
    get le' x = Some (b, t) ->
    store t M' (b, BinNums.Z0) v = Some M''->
    exists M1 le'',  mapstoval (b,BinNums.Z0) t true v M1 /\ 
                     le'' = sig x (b,t)/\ join M M1 M''/\
                     join le le'' le'.
Proof.
  intros.
  destruct H as [b0].
  destruct H.
  destruct H2.
  destruct H3.
  rewrite H4 in H0.
  rewrite EnvMod.set_a_get_a in H0.
  inversion H0. clear H0.
  subst.
  exists (init_mem b 0%Z (encode_val t v)).
  eexists.
  split.
  unfold mapstoval.
  eexists.
  split.
  auto.
  apply ptomvallist_init_mem.
  split.
  eexists.
  split.
  unfold store in H1.
  destruct v;
    try (simpl; simpl in H1; apply allocb_storebytes_memjoin; [apply fresh_implies_fresh_index; auto | auto]);
    try (destruct t; try (unfold encode_val; try (destruct a); unfold encode_val in H1; apply allocb_storebytes_memjoin;
                          [apply fresh_implies_fresh_index; auto | auto])).

(* 5 cases remain *)
(* 1 Tint8 *)
  simpl; simpl in H1.
  rewrite set_a_get_a in H1.
  inversion H1.
  rewrite set_empmem_sig_eq.
  rewrite mem_set_a_set_a.
  apply mem_join_sig_r.
  intro.
  unfold fresh in H.
  unfold not in H.
  apply (H (b, 0%Z) 0%Z).
  auto.
  auto.

(* 2 Tint16*)
  simpl.
  rewrite mem_set_a_set_a'.
  simpl in H1.
  rewrite set_a_get_a in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a in H1.
  rewrite mem_set_a_set_a' in H1.
  rewrite mem_set_a_set_a in H1.
  rewrite mem_set_a_set_a' in H1.
  rewrite mem_set_a_set_a in H1.
  rewrite mem_set_a_set_a' in H1.
  inverts H1.
  apply join_comm.
  apply map_join_set_none.
  apply map_join_set_none.
  apply join_emp; auto.

  eapply fresh_get_none; auto.
  eapply fresh_get_none; auto.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.

(* 3  Tint32 *)
  simpl; simpl in H1.
  rewrite set_a_get_a in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a in H1.

  rewrite mem_set_a_set_a' in H1.
  change ((fun x =>
             Some
               (set x (b, 1%Z) (true, Byte (Byte.repr (Int.unsigned i / 256)))) = Some M'')
((set
               (set
                  (set
                     (set
                        (set
                           (set (set M (b, 3%Z) (true, Undef)) 
                              (b, 2%Z) (true, Undef)) 
                           (b, 1%Z) (true, Undef)) 
                        (b, 0%Z) (true, Undef)) (b, 3%Z)
                     (true,
                     Byte (Byte.repr (Int.unsigned i / 256 / 256 / 256))))
                  (b, 2%Z)
                  (true, Byte (Byte.repr (Int.unsigned i / 256 / 256))))
               (b, 0%Z) (true, Byte (Byte.repr (Int.unsigned i)))))) in H1.
  rewrite mem_set_a_set_a' in H1.

  change ((fun x => (Some
         (set
            (set x
               
               (b, 2%Z) (true, Byte (Byte.repr (Int.unsigned i / 256 / 256))))
            (b, 1%Z) (true, Byte (Byte.repr (Int.unsigned i / 256)))) =
       Some M'')) ((set
                  (set
                     (set
                        (set
                           (set (set M (b, 3%Z) (true, Undef)) 
                              (b, 2%Z) (true, Undef)) 
                           (b, 1%Z) (true, Undef)) 
                        (b, 0%Z) (true, Undef)) (b, 3%Z)
                     (true,
                     Byte (Byte.repr (Int.unsigned i / 256 / 256 / 256))))
                  (b, 0%Z) (true, Byte (Byte.repr (Int.unsigned i)))))) in H1.
  rewrite mem_set_a_set_a' in H1.
  rewrite mem_set_a_set_a in H1.

  rewrite mem_set_a_set_a' in H1.
  change ((fun x => (Some
         (set
            x
            (b, 2%Z) (true, Byte (Byte.repr (Int.unsigned i / 256 / 256)))) =
       Some M'')) ((set
               (set
                  (set
                     (set
                        (set (set M (b, 3%Z) (true, Undef)) 
                           (b, 2%Z) (true, Undef)) 
                        (b, 1%Z) (true, Undef)) (b, 0%Z)
                     (true, Byte (Byte.repr (Int.unsigned i)))) 
                  (b, 3%Z)
                  (true, Byte (Byte.repr (Int.unsigned i / 256 / 256 / 256))))
               (b, 1%Z) (true, Byte (Byte.repr (Int.unsigned i / 256)))))) in H1.

  rewrite mem_set_a_set_a' in H1.
  change ((fun x => (Some
         (set
            (set x
               (b, 3%Z)
               (true, Byte (Byte.repr (Int.unsigned i / 256 / 256 / 256))))
            (b, 2%Z) (true, Byte (Byte.repr (Int.unsigned i / 256 / 256)))) =
       Some M''))(
               (set
                  (set
                     (set
                        (set (set M (b, 3%Z) (true, Undef)) 
                           (b, 2%Z) (true, Undef)) 
                        (b, 1%Z) (true, Undef)) (b, 0%Z)
                     (true, Byte (Byte.repr (Int.unsigned i)))) 
                  (b, 1%Z) (true, Byte (Byte.repr (Int.unsigned i / 256)))))) in H1.
  rewrite mem_set_a_set_a' in H1.
  rewrite mem_set_a_set_a in H1.

  rewrite mem_set_a_set_a' in H1.
  
  change ((fun x => (Some
         (set x
            (b, 3%Z)
            (true, Byte (Byte.repr (Int.unsigned i / 256 / 256 / 256)))) =
       Some M'')) (
            (set
               (set
                  (set
                     (set (set M (b, 3%Z) (true, Undef)) 
                        (b, 2%Z) (true, Undef)) (b, 1%Z)
                     (true, Byte (Byte.repr (Int.unsigned i / 256))))
                  (b, 0%Z) (true, Byte (Byte.repr (Int.unsigned i))))
               (b, 2%Z) (true, Byte (Byte.repr (Int.unsigned i / 256 / 256)))))) in H1.
  rewrite mem_set_a_set_a' in H1.
  change ((fun x => (Some
         (set
            (set x
               (b, 0%Z) (true, Byte (Byte.repr (Int.unsigned i)))) 
            (b, 3%Z)
            (true, Byte (Byte.repr (Int.unsigned i / 256 / 256 / 256)))) =
       Some M'')) (
               (set
                  (set
                     (set (set M (b, 3%Z) (true, Undef)) 
                        (b, 2%Z) (true, Undef)) (b, 1%Z)
                     (true, Byte (Byte.repr (Int.unsigned i / 256))))
                  (b, 2%Z)
                  (true, Byte (Byte.repr (Int.unsigned i / 256 / 256)))))) in H1.
  rewrite mem_set_a_set_a' in H1.
  rewrite mem_set_a_set_a in H1.

  rewrite mem_set_a_set_a' in H1.
  change ((fun x => ( Some
         (set
            x
            (b, 0%Z) (true, Byte (Byte.repr (Int.unsigned i)))) = 
       Some M''))((set
               (set
                  (set (set M (b, 3%Z) (true, Undef)) 
                     (b, 2%Z)
                     (true, Byte (Byte.repr (Int.unsigned i / 256 / 256))))
                  (b, 1%Z) (true, Byte (Byte.repr (Int.unsigned i / 256))))
               (b, 3%Z)
               (true, Byte (Byte.repr (Int.unsigned i / 256 / 256 / 256)))))) in H1.
  rewrite mem_set_a_set_a' in H1.
  change ((fun x => (Some
         (set
            (set
               x
               (b, 1%Z) (true, Byte (Byte.repr (Int.unsigned i / 256))))
            (b, 0%Z) (true, Byte (Byte.repr (Int.unsigned i)))) = 
       Some M''))((set
                  (set (set M (b, 3%Z) (true, Undef)) 
                     (b, 2%Z)
                     (true, Byte (Byte.repr (Int.unsigned i / 256 / 256))))
                  (b, 3%Z)
                  (true, Byte (Byte.repr (Int.unsigned i / 256 / 256 / 256)))))) in H1.
  rewrite mem_set_a_set_a' in H1.
  rewrite mem_set_a_set_a in H1.
  inverts H1.
  apply join_comm.
  apply map_join_set_none.
  apply map_join_set_none.
  apply map_join_set_none.
  apply map_join_set_none.
  apply join_emp; auto.
  eapply fresh_get_none; auto.
  eapply fresh_get_none; auto.
  eapply fresh_get_none; auto.
  eapply fresh_get_none; auto.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.

  
  (* 4, same as 3, except the 'destruct a' in the 4th line below *)
  simpl; destruct a as [ba ia]; simpl; simpl in H1.
  rewrite set_a_get_a in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a in H1.

  rewrite mem_set_a_set_a' in H1.
  change ((fun x => (Some
         (set
            x  (b, 1%Z) (true, Pointer ba ia 2)) =
       Some M''))((set
               (set
                  (set
                     (set
                        (set
                           (set (set M (b, 3%Z) (true, Undef)) 
                              (b, 2%Z) (true, Undef)) 
                           (b, 1%Z) (true, Undef)) 
                        (b, 0%Z) (true, Undef)) (b, 3%Z)
                     (true, Pointer ba ia 0)) (b, 2%Z)
                  (true, Pointer ba ia 1)) (b, 0%Z) 
               (true, Pointer ba ia 3)))) in H1.
  rewrite mem_set_a_set_a' in H1.

  change ((fun x => (Some
         (set
            (set
               x (b, 2%Z) 
               (true, Pointer ba ia 1)) (b, 1%Z) (true, Pointer ba ia 2)) =
       Some M''))((set
                  (set
                     (set
                        (set
                           (set (set M (b, 3%Z) (true, Undef)) 
                              (b, 2%Z) (true, Undef)) 
                           (b, 1%Z) (true, Undef)) 
                        (b, 0%Z) (true, Undef)) (b, 3%Z)
                     (true, Pointer ba ia 0)) (b, 0%Z)
                  (true, Pointer ba ia 3)))) in H1.
  rewrite mem_set_a_set_a' in H1.
  rewrite mem_set_a_set_a in H1.

  rewrite mem_set_a_set_a' in H1.
  change ((fun x => (Some
         (set
            x (b, 2%Z) (true, Pointer ba ia 1)) =
       Some M''))((set
               (set
                  (set
                     (set
                        (set (set M (b, 3%Z) (true, Undef)) 
                           (b, 2%Z) (true, Undef)) 
                        (b, 1%Z) (true, Undef)) (b, 0%Z)
                     (true, Pointer ba ia 3)) (b, 3%Z)
                  (true, Pointer ba ia 0)) (b, 1%Z) 
               (true, Pointer ba ia 2)))) in H1.
  rewrite mem_set_a_set_a' in H1.
  
  change ((fun x => (Some
         (set
            (set x (b, 3%Z) 
               (true, Pointer ba ia 0)) (b, 2%Z) (true, Pointer ba ia 1)) =
       Some M''))(
               (set
                  (set
                     (set
                        (set (set M (b, 3%Z) (true, Undef)) 
                           (b, 2%Z) (true, Undef)) 
                        (b, 1%Z) (true, Undef)) (b, 0%Z)
                     (true, Pointer ba ia 3)) (b, 1%Z)
                  (true, Pointer ba ia 2)))) in H1.
  rewrite mem_set_a_set_a' in H1.
  rewrite mem_set_a_set_a in H1.

  rewrite mem_set_a_set_a' in H1.
  change ((fun x => (Some
         (set x (b, 3%Z) (true, Pointer ba ia 0)) =
       Some M''))(
            (set
               (set
                  (set
                     (set (set M (b, 3%Z) (true, Undef)) 
                        (b, 2%Z) (true, Undef)) (b, 1%Z)
                     (true, Pointer ba ia 2)) (b, 0%Z)
                  (true, Pointer ba ia 3)) (b, 2%Z) 
               (true, Pointer ba ia 1)))) in H1.
  rewrite mem_set_a_set_a' in H1.
  
  change ((fun x => (Some
         (set
            (set x (b, 0%Z) 
               (true, Pointer ba ia 3)) (b, 3%Z) (true, Pointer ba ia 0)) =
       Some M''))(
               (set
                  (set
                     (set (set M (b, 3%Z) (true, Undef)) 
                        (b, 2%Z) (true, Undef)) (b, 1%Z)
                     (true, Pointer ba ia 2)) (b, 2%Z)
                  (true, Pointer ba ia 1)))) in H1.
   rewrite mem_set_a_set_a' in H1.
   rewrite mem_set_a_set_a in H1.
   
   rewrite mem_set_a_set_a' in H1.
   change ((fun x => (Some
         (set x (b, 0%Z)
            (true, Pointer ba ia 3)) = Some M''))(
            (set
               (set
                  (set (set M (b, 3%Z) (true, Undef)) 
                     (b, 2%Z) (true, Pointer ba ia 1)) 
                  (b, 1%Z) (true, Pointer ba ia 2)) 
               (b, 3%Z) (true, Pointer ba ia 0)))) in H1.
   rewrite mem_set_a_set_a' in H1.
   change ((fun x => (Some
         (set
            (set
               x 
               (b, 1%Z) (true, Pointer ba ia 2)) (b, 0%Z)
            (true, Pointer ba ia 3)) = Some M''))((set
                  (set (set M (b, 3%Z) (true, Undef)) 
                     (b, 2%Z) (true, Pointer ba ia 1)) 
                  (b, 3%Z) (true, Pointer ba ia 0)))) in H1.
   rewrite mem_set_a_set_a' in H1.
   rewrite mem_set_a_set_a in H1.

  inverts H1.
  apply join_comm.
  apply map_join_set_none.
  apply map_join_set_none.
  apply map_join_set_none.
  apply map_join_set_none.
  apply join_emp; auto.
  eapply fresh_get_none; auto.
  eapply fresh_get_none; auto.
  eapply fresh_get_none; auto.
  eapply fresh_get_none; auto.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.

  (* 4, same as 3, except the 'destruct a' in the 4th line below *)
  simpl. destruct a as [ba ia]. simpl. simpl in H1.
  rewrite set_a_get_a in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a' in H1.
  rewrite set_a_get_a in H1.

  rewrite mem_set_a_set_a' in H1.
  change ((fun x => (Some
         (set
            x  (b, 1%Z) (true, Pointer ba ia 2)) =
       Some M''))((set
               (set
                  (set
                     (set
                        (set
                           (set (set M (b, 3%Z) (true, Undef)) 
                              (b, 2%Z) (true, Undef)) 
                           (b, 1%Z) (true, Undef)) 
                        (b, 0%Z) (true, Undef)) (b, 3%Z)
                     (true, Pointer ba ia 0)) (b, 2%Z)
                  (true, Pointer ba ia 1)) (b, 0%Z) 
               (true, Pointer ba ia 3)))) in H1.
  rewrite mem_set_a_set_a' in H1.

  change ((fun x => (Some
         (set
            (set
               x (b, 2%Z) 
               (true, Pointer ba ia 1)) (b, 1%Z) (true, Pointer ba ia 2)) =
       Some M''))((set
                  (set
                     (set
                        (set
                           (set (set M (b, 3%Z) (true, Undef)) 
                              (b, 2%Z) (true, Undef)) 
                           (b, 1%Z) (true, Undef)) 
                        (b, 0%Z) (true, Undef)) (b, 3%Z)
                     (true, Pointer ba ia 0)) (b, 0%Z)
                  (true, Pointer ba ia 3)))) in H1.
  rewrite mem_set_a_set_a' in H1.
  rewrite mem_set_a_set_a in H1.

  rewrite mem_set_a_set_a' in H1.
  change ((fun x => (Some
         (set
            x (b, 2%Z) (true, Pointer ba ia 1)) =
       Some M''))((set
               (set
                  (set
                     (set
                        (set (set M (b, 3%Z) (true, Undef)) 
                           (b, 2%Z) (true, Undef)) 
                        (b, 1%Z) (true, Undef)) (b, 0%Z)
                     (true, Pointer ba ia 3)) (b, 3%Z)
                  (true, Pointer ba ia 0)) (b, 1%Z) 
               (true, Pointer ba ia 2)))) in H1.
  rewrite mem_set_a_set_a' in H1.
  
  change ((fun x => (Some
         (set
            (set x (b, 3%Z) 
               (true, Pointer ba ia 0)) (b, 2%Z) (true, Pointer ba ia 1)) =
       Some M''))(
               (set
                  (set
                     (set
                        (set (set M (b, 3%Z) (true, Undef)) 
                           (b, 2%Z) (true, Undef)) 
                        (b, 1%Z) (true, Undef)) (b, 0%Z)
                     (true, Pointer ba ia 3)) (b, 1%Z)
                  (true, Pointer ba ia 2)))) in H1.
  rewrite mem_set_a_set_a' in H1.
  rewrite mem_set_a_set_a in H1.

  rewrite mem_set_a_set_a' in H1.
  change ((fun x => (Some
         (set x (b, 3%Z) (true, Pointer ba ia 0)) =
       Some M''))(
            (set
               (set
                  (set
                     (set (set M (b, 3%Z) (true, Undef)) 
                        (b, 2%Z) (true, Undef)) (b, 1%Z)
                     (true, Pointer ba ia 2)) (b, 0%Z)
                  (true, Pointer ba ia 3)) (b, 2%Z) 
               (true, Pointer ba ia 1)))) in H1.
  rewrite mem_set_a_set_a' in H1.
  
  change ((fun x => (Some
         (set
            (set x (b, 0%Z) 
               (true, Pointer ba ia 3)) (b, 3%Z) (true, Pointer ba ia 0)) =
       Some M''))(
               (set
                  (set
                     (set (set M (b, 3%Z) (true, Undef)) 
                        (b, 2%Z) (true, Undef)) (b, 1%Z)
                     (true, Pointer ba ia 2)) (b, 2%Z)
                  (true, Pointer ba ia 1)))) in H1.
   rewrite mem_set_a_set_a' in H1.
   rewrite mem_set_a_set_a in H1.
   
   rewrite mem_set_a_set_a' in H1.
   change ((fun x => (Some
         (set x (b, 0%Z)
            (true, Pointer ba ia 3)) = Some M''))(
            (set
               (set
                  (set (set M (b, 3%Z) (true, Undef)) 
                     (b, 2%Z) (true, Pointer ba ia 1)) 
                  (b, 1%Z) (true, Pointer ba ia 2)) 
               (b, 3%Z) (true, Pointer ba ia 0)))) in H1.
   rewrite mem_set_a_set_a' in H1.
   change ((fun x => (Some
         (set
            (set
               x 
               (b, 1%Z) (true, Pointer ba ia 2)) (b, 0%Z)
            (true, Pointer ba ia 3)) = Some M''))((set
                  (set (set M (b, 3%Z) (true, Undef)) 
                     (b, 2%Z) (true, Pointer ba ia 1)) 
                  (b, 3%Z) (true, Pointer ba ia 0)))) in H1.
   rewrite mem_set_a_set_a' in H1.
   rewrite mem_set_a_set_a in H1.

  inverts H1.
  apply join_comm.
  apply map_join_set_none.
  apply map_join_set_none.
  apply map_join_set_none.
  apply map_join_set_none.
  apply join_emp; auto.
  eapply fresh_get_none; auto.
  eapply fresh_get_none; auto.
  eapply fresh_get_none; auto.
  eapply fresh_get_none; auto.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  
  (* finised the 5 remaining cases *)
  apply env_join_sig_r.
  auto.
  apply identspec.eq_beq_true.
  auto.
Qed.

Lemma alloc_star_exist' : forall  p vl dl ks ge le  M ir aux, 
                            length vl <= length_dl dl -> 
                            good_decllist dl = true ->
                            good_env_decllist le dl ->
                            exists le' M',  
                              losallocstepstar p (curs (salloc vl dl), (kenil, ks))
                                               (ge, le , M, ir, aux) (curs (salloc nil dnil), (kenil, ks))
                                               (ge, le', M', ir, aux).
Proof.
  intros.
  gen le M dl.
  induction vl.
  introv.
  gen le M.
  induction dl.
  (* base *)
  intros.
  do 2 eexists.
  constructors.
  (* induction *)
  intros.
  simpl in *.
  destruct H1.
  lets Hb : fresh_exist M.
  destruct Hb as (b & Hb).
  simpl in IHdl,H.
  assert (0 <= (length_dl dl)).
  omega.
  lets H4 : andb_prop H0.
  destruct H4.
  assert (in_decllist i dl = false).
  apply negb_true_iff.
  auto.
  lets Hlos : IHdl (EnvMod.set le i (b, t)) (allocb M b 0%Z (typelen t)).
  apply Hlos in H3;eauto.
  destruct H3 as (le' & M' & H3).
  do 2 eexists.
  eapply losallocstepstar_n;eauto.
  constructors.
  constructors.
  eapply stmt_step.
  eauto.
  constructors.
  eauto.
  eauto.
  unfold alloc.
  exists b.
  split;eauto.
  unfold allocstep.
  do 5 eexists.
  split;eauto.
  split;eauto.
  assert (alloc i t le M (EnvMod.set le i (b, t)) (allocb M b 0%Z (typelen t))).
  unfold alloc.
  exists b;eauto.

  lets H8: alloc_exist_mem_env H7.
  destruct H8 as (M'' & le'' & l & v & H8).
  destructs H8.
  split.
  intros.
  do 3 eexists.
  split;eauto.
  unfold joinenvmem.
  do 7 eexists;split;eauto;split;eauto;split;eauto.
  rewrite H9 in H11.
  eauto.
  intros.
  false.
  eapply set_env_good_env_decllist;eauto.
  intros.
  destruct dl.
  simpl in H.
  omega.
  assert (length vl <= length_dl (dcons i t dl)).
  simpl in H.
  simpl.
  omega.
  lets Hb : fresh_exist M.
  destruct Hb as (b & Hb).
  lets Hmem : allocb_store_mem_ex t M b a.
  destruct Hmem as (M' & Hmem).
  assert (length vl <= length_dl dl).
  simpl in H. omega.
  simpl in H0. lets Hand : andb_prop H0.
  destruct Hand.
  assert (good_env_decllist (EnvMod.set le i (b, t)) dl).
  simpl in *.
  eapply set_env_good_env_decllist;eauto.
  apply H1.
  apply H1.
  eapply negb_true_iff;eauto.
  lets Hlos : IHvl (EnvMod.set le i (b, t)) M' dl H3 H5.  
  apply Hlos in H6.
  destruct H6 as (le' & M'0 & H6).
  do 2 eexists.
  eapply losallocstepstar_n.
  constructors.
  constructors.
  eapply stmt_step.
  eauto.
  constructors.
  eauto.
  eauto.
  unfold alloc.
  exists b.
  split;eauto.
  split;eauto.
  split;eauto.
  simpl in H1.
  apply H1.
  eapply map_get_set;eauto.
  eauto.
  unfold allocstep.
  do 5 eexists.
  split;eauto.
  split;eauto.
  assert (alloc i t le M (set le i (b, t)) (allocb M b 0%Z (typelen t))).
  unfold alloc.
  exists b;split;eauto;split;eauto;split;eauto.
  apply H1.
  lets Hmem' : alloc_store_exist_mem_env H7 Hmem.
  eapply map_get_set.
  eauto.
  destruct Hmem' as (M1 & le'' & l & Hmem').
  split.
  intros.
  inverts H8.
  intros.
  do 4 eexists.
  split;eauto.
  split;eauto.
  unfold joinenvmem.
  do 7 eexists;split;eauto.
  split;eauto.
  split. destructs Hmem'.
  rewrite H9 in H11.
  apply H11.
  apply Hmem'.
  apply H6.
Qed.

Lemma alloc_star_exist : forall  p vl dl ks ge  M ir aux, 
                           length vl <= length_dl dl -> good_decllist dl = true ->
                           exists le' M',  
                             losallocstepstar p (curs (salloc vl dl), (kenil, ks))
                                              (ge, empenv , M, ir, aux) (curs (salloc nil dnil), (kenil, ks))
                                              (ge, le', M', ir, aux).
Proof.
  intros.
  eapply alloc_star_exist';eauto.
  clear.
  induction dl.
  simpl;auto.
  simpl.
  split;eauto.
  red.
  intros.
  lets Hget: EnvMod.indom_get H.
  destruct Hget.
  inverts H0.
Qed.

Inductive losidstepn : nat ->  progunit -> code -> taskst -> code -> taskst -> Prop :=
|  losidstep_0 : forall p C o,  losidstepn O p C o C o
|  losidstep_n  : forall n p C o C' C'', loststep p C o C'' o -> 
                                         losidstepn n p C'' o C' o -> losidstepn (S n) p C o C' o.

Inductive lostidstepstar :  progunit -> code -> taskst -> code -> taskst -> Prop :=
| lostidstepstar0 : forall pu C o, lostidstepstar pu C o C o
| lostidstepstarn : forall pu C o C' C'', loststep pu C o C' o -> 
                                          lostidstepstar pu C' o C'' o -> lostidstepstar pu C o C'' o.


Lemma losidstepstar_imply_losidstepn : forall p C o C' o', 
                                         lostidstepstar p C o C' o' -> exists n, losidstepn n p C o C' o'.
Proof.
  introv Hlos.
  inductions Hlos.
  exists O.
  constructors.
  destruct IHHlos as (n & HH).
  exists (S n).
  constructors; eauto.
Qed.

Lemma losidstepstar_imply_losallocstepn : forall p C o C' o', 
                                            losallocstepstar p C o C' o' -> exists n, losallocstepn n p C o C' o'.
Proof.
  introv Hlos.
  inductions Hlos.
  exists O.
  constructors.
  destruct IHHlos as (n & HH).
  exists (S n).
  constructors; eauto.
Qed.

Lemma list_cs_noteq : 
  forall   (T:Type)( i : T) (l: list T), ~(l = i :: l).
Proof.
  inductions l; introv H.
  inverts H.
  inverts H.
  apply IHl.
  auto.
Qed.


Lemma estep_mem_same :
  forall c ke m c' ke' m', estep c ke m c' ke' m' ->  m = m'.
Proof.
  introv Hestep.
  inductions Hestep; eauto.
Qed.

Ltac Some_eq :=
  match goal with
    | |- ?x = ?y =>
    cut (Some x = Some y); [ let H := fresh in intros H; inversion H; auto | idtac ]
    end.

Ltac Tptr_eq := 
  match goal with
    | |- ?x = ?y =>
    cut (Tptr x = Tptr y); [ let H := fresh in intros H; inversion H; auto | idtac ]
    end.

Lemma storebytes_mono' :
  forall M1 M1' M M2 M2' a l,
    storebytes M1 a l = Some M1' ->
    join M1 M M2 ->
    join M1' M M2' ->
    storebytes M2 a l = Some M2'.
Proof.
  intros.
  gen H H0 H1.
  gen M1 M1' M M2 M2' a.
  induction l; intros; simpl in *.

  inv H.
  lets H100 : join_unique H1 H0.
  rewrite H100; auto.

  destruct a0.

  unfold get in *; simpl in *.
  remember (HalfPermMap.get M1 (b, o)) as v1; destruct v1.
  2 : tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  symmetry in Heqv1.
  lets H100 : mem_join_get_get_l_true H0 Heqv1.
  unfold get in H100; simpl in H100.
  rewrite H100.
  clear H100.
  
  remember (storebytes M1 (b, o + 1)%Z l) as v2; destruct v2.
  2 : tryfalse.
  symmetry in Heqv2.
  inversion H; clear H.

  cut (exists m', join m M m' /\ set m' (b, o) (true, a) = M2'); intros.
  do 2 destruct H.
  eapply IHl in Heqv2; eauto.
  rewrite Heqv2.
  rewrite <- H2; auto.
  
  gen H1 H3; clear; intros.
  rewrite <- H3 in H1; clear H3.

  lets H100 : mem_join_set_l_rev H1.
  auto.
  destruct H100; eexists; intuition eauto.
Qed.


Lemma store_mono' :
  forall t M1 M1' M M2 M2' a v,
    store t M1 a v = Some M1' ->
    join M1 M M2 ->
    join M1' M M2' ->
    store t M2 a v = Some M2'.
Proof.
  intros.
  unfold store in *.
  destruct a.
  
  destruct v; simpl in *.

  eapply storebytes_mono'; eauto.
  eapply storebytes_mono'; eauto.
  
  destruct t; eapply storebytes_mono'; eauto.
  destruct a; destruct t; eapply storebytes_mono'; eauto.
Qed.

Lemma store_same_mono :
  forall t M M1 M2 a v,
    join M M1 M2 ->
    store t M a v = Some M ->
    store t M2 a v = Some M2.
Proof.
  intros; eapply store_mono'; eauto.
Qed.

Lemma free_false : forall t b M,(typelen t <> 0)%nat -> ~free t b M = Some M.
Proof.
  intros.
  remember (typelen t) as tlen.
  red.
  intros.
  destruct tlen.
  apply  H.
  auto.
  unfold free in H0.
  rewrite<-Heqtlen in H0.
  simpl in H0.
  remember (get M (b, BinNums.Z0)) as v.
  destruct v;tryfalse.
  destruct p.
  remember (freeb M b 1 tlen) as M'.
  destruct M';tryfalse.
  destruct b0; tryfalse.
  injection H0;intros.
  subst M.

  rewrite mem_del_get in Heqv; tryfalse.
  destruct b0; tryfalse.
Qed.


Lemma alloc_false : forall x t le M M', ~alloc x t le M le M'.
Proof.
  intros.
  red.
  intros.
  unfold alloc in H.
  destruct H.
  destruct H.
  destruct H0.
  destruct H1.
  apply H1.
  apply EnvMod.get_indom.
  rewrite H2.
  rewrite EnvMod.set_a_get_a;eauto.
  eapply identspec.eq_beq_true;eauto.
Qed.



Lemma cstep_idmove_frame :
  forall G E M1 M M2 m' p C C' C'',
    join M1 M M2 ->
    cstep p C (G, E, M1) C' (G, E, M1) ->
    cstep p C (G, E, M2) C'' m' ->
    C'' = C' /\ m' = (G, E, M2).
Proof.
  intros.
  inverts H0.
  inverts H1.
  inverts H0.
  lets He : estep_mem_same H2.
  subst m'.
  inverts H3;inverts H2;auto;
  split;auto;do 6 decEq.
  Some_eq;rewrite<-H0;rewrite<-H3;
  eapply evalval_mono;eauto;unfold SysmemJoinM;do 4 eexists;eauto.
  
  Some_eq;rewrite<-H0;rewrite<-H3;
  eapply evalval_mono;eauto;unfold SysmemJoinM;do 4 eexists;eauto.

  Tptr_eq;Some_eq;rewrite<-H0;rewrite<-H3;
  eapply evaltype_mono;eauto;unfold SysmemJoinM;do 4 eexists;eauto.

  Some_eq;rewrite<-H1;rewrite<-H10;decEq.
  assert (evaltype e (G, E, M2) = evaltype e (G, E, M1)). 
  eapply evaltype_mono;unfold SysmemJoinM;eauto.
  rewrite H0,H5 in H2;injection H2;eauto.

  assert (evaltype e1 (G, E, M2) = evaltype e1 (G, E, M1)). 
  eapply evaltype_mono;unfold SysmemJoinM;eauto.
  rewrite H0,H8 in H1;injection H1;eauto.
  rewrite evaltype_irrev_mem with (M':=M2) in H0.
  assert (evaltype e1 (G, E, M2) = Some (Tptr t));auto.
  rewrite H1 in H8;tryfalse.
  rewrite evaltype_irrev_mem with (M':=M2) in H0.
  assert (evaltype e1 (G, E, M2) = Some (Tarray t n));auto.
  rewrite H1 in H8;tryfalse.
  
  rewrite evaltype_irrev_mem with (M':=M2) in H0.
  assert (evaltype e1 (G, E, M2) = Some (Tarray t n));auto.
  rewrite H1 in H8;tryfalse.
  inverts H8;auto.
  
  Some_eq;rewrite<-H1;rewrite<-H10;decEq.
  assert (evaltype e (G, E, M2) = evaltype e (G, E, M1)). 
  eapply evaltype_mono;unfold SysmemJoinM;eauto.
  rewrite H0,H5 in H2;injection H2;eauto.
  assert (evaltype e1 (G, E, M2) = evaltype e1 (G, E, M1)). 
  eapply evaltype_mono;unfold SysmemJoinM;eauto.
  rewrite H0,H8 in H1;injection H1;eauto.
  rewrite evaltype_irrev_mem with (M':=M2) in H0.
  assert (evaltype e1 (G, E, M2) = Some (Tarray t n));auto.
  rewrite H1 in H8;tryfalse.
  rewrite evaltype_irrev_mem with (M':=M2) in H0.
  assert (evaltype e1 (G, E, M2) = Some (Tptr t));auto.
  rewrite H1 in H8;tryfalse.
  rewrite evaltype_irrev_mem with (M':=M2) in H0.
  assert (evaltype e1 (G, E, M2) = Some (Tptr t));auto.
  rewrite H1 in H8;tryfalse.
  inverts H8;auto.
  assert (evaltype e (G, E, M2) = evaltype e (G, E, M1)). 
  eapply evaltype_mono;unfold SysmemJoinM;eauto.
  rewrite H0,H8 in H1;injection H1;eauto.
  assert (evaltype e1 (G, E, M2) = evaltype e1 (G, E, M1)). 
  eapply evaltype_mono;unfold SysmemJoinM;eauto.
  rewrite H0,H10 in H2;injection H2;eauto.
  assert (evaltype e2 (G, E, M2) = evaltype e2 (G, E, M1)). 
  eapply evaltype_mono;unfold SysmemJoinM;eauto.
  rewrite H1,H11 in H2;injection H2;eauto.
  simpl in *;tryfalse.
  simpl in *;tryfalse.
  simpl in *;tryfalse.
  simpl in *;tryfalse.
  simpl in *;tryfalse.
  simpl in *;tryfalse.
  Some_eq.
  rewrite <-H0,<-H6.
  eapply evaltype_mono;unfold SysmemJoinM;eauto.
  rewrite H0 in H9;inverts H9.
  auto.
  Some_eq. 
  rewrite<-H1,<-H10.
  inverts H0.
  inverts H6.
  eapply load_mono;eauto.
  inverts H9;auto.  
  rewrite H0 in H9;inverts H9;auto.
  rewrite H0 in H11;inverts H11;auto.
  inverts H0.
  inverts H3;inverts H2.
  inverts H1.
  inverts H0.
  inverts H2;inverts H3.
  inverts H0.
  inverts H2;inverts H3;auto;tryfalse.
  split;auto;do 6 decEq. 
  Some_eq;rewrite<-H0,<-H6.
  eapply evaltype_mono;unfold SysmemJoinM;eauto.
  split;auto.
  inverts H0;inverts H8;inverts H13.
  do 2 decEq. Some_eq.
  rewrite<-H4.
  eapply store_same_mono;eauto.
  split;auto;do 6 decEq. 
  Some_eq;rewrite<-H0,<-H10.
  eapply evaltype_mono;unfold SysmemJoinM;eauto.
  split;auto;do 6 decEq. 
  Some_eq;rewrite<-H0,<-H10.
  eapply evaltype_mono;unfold SysmemJoinM;eauto.
  split;auto;do 6 decEq. 
  Some_eq;rewrite<-H0,<-H13.
  eapply evaltype_mono;unfold SysmemJoinM;eauto.
  inverts H0;inverts H8;inverts H9.
  rewrite H4 in H11;inverts H11;eauto.
  inverts H0;inverts H11;inverts H17.
  false; eapply alloc_false; eauto.
  
  inverts H0;inverts H7;inverts H13.
  false; eapply alloc_false; eauto.
  
  inverts H0;inverts H2.
  rewrite H1 in H4;inverts H4;eauto.
  
  inverts H0;inverts H5. eauto.
  
  inverts H0;inverts H13;inverts H14.
  split;auto.
  assert (typelen t = 0 \/ typelen t <>0).
  omega.
  destruct H0.
  unfold free in *.
  rewrite H0 in *.
  simpl in *.
  inverts H4.
  auto.
  false;eapply free_false;eauto.
  inverts H0;inverts H2;inverts H5;rewrite H4 in H7;inverts H7;auto.
  Grab Existential Variables.
Qed.

Lemma store_mono_join_eq:
  forall M0 v b t M M1 M',
    store t M0 (b, 0%Z) v = Some M0 -> 
    join M0 M M1 -> 
    store t M1 (b, 0%Z) v = Some M' -> M1=M'.
Proof.
  introv Hst Hj Hsts.
  lets Hds : store_same_mono  Hj Hst.
  rewrite Hsts in Hds.
  inverts Hds; auto.
Qed.

Lemma losstep_idmove_frame : 
  forall p  C C' C'' o  o' o''  M, 
    loststep p C o C' o -> 
    joinmem o M o' -> 
    loststep p C o' C'' o'' ->
    C' = C'' /\ o' = o''.
Proof.
  introv Hstep Hjoin Hstep'.
  unfolds in Hjoin.
  destruct Hjoin as (G & E & M1 & M2 & ir &  ls & Ho1 & Ho2 & Hmj).
  subst.
  inverts Hstep;try solve [false;eapply list_cs_noteq;eauto].
  (* cstep *)
  inverts Hstep';
    try solve [
          inverts H5;
          inverts H;
          inverts H0].
  lets Hcstep: cstep_idmove_frame Hmj H5 H7.
  split.
  symmetry.
  apply Hcstep.
  decEq.
  decEq.
  symmetry.
  apply Hcstep.
  (* prim *)
  inverts Hstep';
    try solve [
          inverts H7;
          inverts H;
          inverts H0;
          inverts H;
          inverts H0].
  inverts H10.
  inverts H5.
  auto.
  inverts H2.
  inverts Hstep';try inverts H8.
  inverts H6.
  inverts H;inverts H0.
  inverts H;inverts H0.
  inverts H10.
  inverts H4.
  auto.
  inverts H6.
  inverts Hstep';try inverts H8.
  inverts H6.
  inverts H;inverts H0.
  inverts H;inverts H0.
  inverts H10.
  inverts H4.
  auto.
  inverts H6.
  inverts H6.
  inverts Hstep';tryfalse.
  inverts H6;tryfalse.
  inverts H0;tryfalse.
  inverts H0;tryfalse.
  inverts H6.
  inverts H12.
  inverts H10.
  split;auto.
  rewrite H13 in H8;inverts H8.
  assert (M1=M'0).
  eapply store_mono_join_eq;eauto.
  subst;auto.
Qed.

Lemma losalloc_local_inv_hold:
  forall n P C C'   O li t o o',
    satp o O (CurLINV li t) ->
    losallocstepn  n P C o  C' o'  -> 
    satp o' O (CurLINV li t).
Proof.
  intros.
  gen O li t H.
  inductions H0; intros.
  auto.

  eapply IHlosallocstepn.
  eapply alloc_local_inv_prev; eauto.
Qed.


 Lemma loststep_join_notabt: 
   forall p C o  o1 o2 M1 M2,
     joinmem o M1 o1 -> 
     joinmem o1 M2 o2 ->
  (exists o' C', loststep p C o C' o')  -> ~ loststepabt p C o2.
Proof.
  intros.
  eapply notabt_frame.
  apply H0.
  eapply notabt_frame.
  apply H.
  red.
  intros.
  apply H2.
  do 2 destruct H1.
  do 2 eexists.
  eauto.
Qed.

Definition empprogunit : progunit := fun _ => None.

Lemma identity_step_msim_hold :
  forall  C C'  o ,
    notabortm C ->
    (forall p,  loststep p C o C' o)  -> 
    forall   FSpec sd gamma O  I r ri q li t,
      satp o O (CurLINV li t) ->
      MethSimMod FSpec sd C' o  gamma O  li I r ri q  t ->
      MethSimMod FSpec  sd C o gamma O  li I r ri q   t.
Proof.
  introv Hnot Hlos.
  introv Hmsim.
  constructors.
  introv Hfcal Hinv Hjm1  Hjon Hlostep.
  exists gamma OO  o Ms O Os .
  assert ( exists M, joinmem o M o2 /\ join Ms Mf M) as Hast.
  unfolds in Hjm1.
  unfold joinmem in *.
  clear - Hjm1.
  join auto.
  destruct Hast as (Ml & Hjmk & Hjk ).
  lets Htm : losstep_idmove_frame Hlos Hjmk  Hlostep.
  simp join.
  splits; auto.
  constructors. 
  introv Hfalse.
  subst C.
  lets Hff : Hlos empprogunit.
  invertstep idtac.
  introv Hc; subst.
  lets Hff : Hlos empprogunit.
  invertstep idtac.
  introv Hc; subst.
  lets Hff : Hlos empprogunit.
  invertstep idtac.
  introv Hc; subst.
  lets Hff : Hlos empprogunit.
  invertstep idtac.
  unfolds in Hnot.
  destruct Hnot as (_& _ &  Hf & _).  
  introv Hcal Hint.
  false.
  introv Hc Hcal Hint.
  unfolds in Hnot.
  subst C.
  destruct Hnot as (_& _ & _ & _ & hf &_).  
  false. apply hf.  unfolds. do 2 eexists; splits;  eauto. 
  introv Hc Hcal Hint.
  unfolds in Hnot.
  subst C.
  destruct Hnot as (_& _ & _ & _ & _  &hf & _).  
  false. apply hf.  unfolds. do 1 eexists; splits;  eauto. 
  introv Hnotm Hts Hts' Hdisj.
  unfolds in Hts'.
  simp join.
  apply loststep_join_notabt with (o2 := o2) (o1:=x)(M1:=Ms) (M2:=Mf) (o:=o) (C:=C); auto.
  do 2 eexists; eauto.
  introv Hc; subst.
  lets Hff : Hlos empprogunit.
  invertstep idtac.
  introv Hc; subst.
  lets Hff : Hlos empprogunit.
  invertstep idtac.
Qed.


Lemma alloc_notabortm : 
  forall v d ks,notabortm (curs (salloc v d), (kenil, ks)).  
Proof.
  introv. 
  unfolds.
  splits.  
  introv Hfa; unfolds in Hfa; simp join; tryfalse.
  splits;
    introv Hfa; unfolds in Hfa; simp join; tryfalse.
Qed.

Lemma vl_app_v_h_t : 
  forall {T} vl v, exists (h:T) t, vl ++ v :: nil = h :: t.
Proof.  
  intros.
  gen v.
  inductions vl; intros.
  simpl.
  eauto.
  simpl.
  pose proof IHvl a.
  do 2 destruct H.
  unfold "++".
  eauto.
Qed.

Lemma tl_vl_match_true_append : 
  forall tl vl t v,
    tl_vl_match tl vl = true ->
    tl_vl_match (tl ++ t :: nil) (vl ++ v :: nil) = tl_vl_match (t :: nil) (v :: nil).
Proof.
  intro.
  inductions tl; intros.
  destruct vl; simpl in H; tryfalse.
  simpl; auto.
  destruct vl; simpl in H; tryfalse.
  destruct (type_val_match a v0) eqn : eq1; simpl in H; tryfalse.
  simpl tl_vl_match at 1.
  rewrite eq1.
  eapply IHtl.
  auto.
Qed.

Lemma tl_vl_match_false_append :
  forall tl vl t v,
    tl_vl_match tl vl = false ->
    tl_vl_match (tl ++ t :: nil) (vl ++ v :: nil) = false.
Proof.
  intro.
  inductions tl; intros.
  destruct vl; simpl in H; tryfalse.
  simpl.
  pose proof vl_app_v_h_t vl v.
  do 2 destruct H0.
  rewrite H0.
  destruct (type_val_match t v0); auto.
  destruct vl.
  simpl in H.
  simpl.
  destruct (type_val_match a v) eqn :eq1.
  pose proof vl_app_v_h_t tl t.
  do 2 destruct H0.
  rewrite H0.
  simpl; auto.
  auto.
  simpl.
  simpl in H.
  destruct (type_val_match a v0).
  eapply IHtl.
  auto.
  auto.
Qed.

Lemma tl_vl_rev_match:
  forall tl vl, tl_vl_match tl vl = tl_vl_match (rev tl) (rev vl).
Proof.
  intro.
  inductions tl; intros.
  destruct vl.
  simpl; auto.
  simpl.
  pose proof vl_app_v_h_t (rev vl) v.
  do 2 destruct H.
  rewrite H.
  auto.
  simpl.
  destruct vl.
  simpl.
  pose proof vl_app_v_h_t (rev tl) a.
  do 2 destruct H.
  rewrite H.
  simpl.
  auto.
  simpl.
  pose proof IHtl vl.
  destruct (type_val_match a v) eqn : eq1.
  destruct (tl_vl_match tl vl) eqn : eq2.
  symmetry in H.
  pose proof tl_vl_match_true_append (rev tl) (rev vl) a v H.
  rewrite H0.
  simpl.
  rewrite eq1.
  auto.
  symmetry in H.
  pose proof tl_vl_match_false_append (rev tl) (rev vl) a v H.
  symmetry in H0.
  auto.
  destruct (tl_vl_match (rev tl) (rev vl)) eqn : eq2.
  pose proof tl_vl_match_true_append (rev tl) (rev vl) a v eq2.
  rewrite H0.
  simpl.
  rewrite eq1.
  auto.
  pose proof tl_vl_match_false_append (rev tl) (rev vl) a v eq2.
  rewrite H0.
  auto.
Qed.

Lemma rev_tl_vl: 
  forall tl vl,
    tl_vl_match (rev tl) vl =true -> 
    tl_vl_match tl (rev vl) = true.
Proof. 
  intros.
  pose proof tl_vl_rev_match (rev tl) vl.
  rewrite H in H0.
  rewrite rev_involutive in H0.
  auto. 
Qed.

Lemma tl_vl_dl: 
  forall tl vl dl, 
    tl_vl_match tl vl = true ->  
    tlmatch  tl dl -> 
    dl_vl_match dl vl =true.
Proof.
  intros.
  generalize dependent tl. 
  generalize dependent vl.
  induction dl.
  intros.
  destruct tl;
    simpl in H0.
  simpl in H.
  destruct vl;tryfalse.
  simpl;auto.
  false.
  intros.
  destruct tl.
  simpl in H0.
  false.
  simpl in H0.
  destruct H0.
  destruct vl;
    simpl in H.
  inversion H.
  remember (type_val_match t0 v) as X.
  destruct X;tryfalse.
  simpl.
  subst t0.
  rewrite <- HeqX.
  eapply IHdl;eauto.
Qed.


Lemma tl_vl_dl': 
  forall tl vl dl, 
    tl_vl_match (rev tl) vl = true -> 
    tlmatch  tl dl -> 
dl_vl_match dl (rev vl) =true.
Proof.
  intros.
  apply rev_tl_vl in H.
  eapply tl_vl_dl;eauto.
Qed.

Lemma eval_length_rev :
  forall  (tl:typelist) (vl:vallist) , 
    length vl = length tl ->  length (rev vl) = length (rev tl).
Proof.
  induction tl; induction vl; simpl; intros;
  tryfalse || auto.
  do 2 rewrite app_length; simpl.
  do 2 rewrite NPeano.Nat.add_1_r.
  cut (length (rev vl) = length (rev tl)).
  intros H100; rewrite H100; auto.
  apply IHtl.
  intuition.
Qed.

Lemma tl_vl_match_leneq': 
  forall tl vl,  tl_vl_match (rev tl) vl = true -> length vl =length tl.
Proof.
  intros.
  apply tl_vl_match_leneq in H.
  rewrite rev_length in H.
  auto.
Qed.

Lemma build_pre_ret_exist :  
  forall   f tl tp Spec pre post  vl d1 d2  s p0 ll t, 
    tl_vl_match (rev tl) vl = true ->  tlmatch  tl d1 -> 
    good_decllist (revlcons d1 d2) = true ->
    p0 f = Some (tp, d1, d2, s) -> 
    Spec f = Some (pre, post, (tp,  tl)) ->
    (exists p , Some p = BuildPreI p0 f  vl ll pre t) /\ 
    (exists r , Some r = BuildRetI p0 f vl ll post t).
Proof.
  intros.
  unfold BuildPreI; unfold BuildRetI.
  rewrite H2.
  cut ((exists p, buildp (revlcons d1 d2) vl = Some p) /\ (exists p, buildq (revlcons d1 d2) = Some p)); intros.
  destruct H4.
  destruct H4; destruct H5.
  rewrite H4; rewrite H5.
  lets Hd:tl_vl_dl' H H0.
  rewrite Hd.
  split; eexists; eauto.
  split.
  apply eval_length_tlmatch in H0.
  assert (length_dl d1 <= length_dl (revlcons d1 d2))%nat as H100.
  assert (length_dl (revlcons d1 d2) = (length_dl d1) + (length_dl d2))%nat as H200.
  clear.
  gen d1 d2.
  induction d1; simpl; intros; auto.
  rewrite IHd1.
  cut (length_dl (dcons i t d2) = S (length_dl d2)).
  intros H100; rewrite H100; omega.
  clear.
  gen d2 i t.
  induction d2; simpl; intros; auto.
  rewrite H200; omega.
  rewrite <- H0 in H100.
  assert (length tl = length vl) as H200.
  cut (length (rev tl) = length (rev vl)).
  intros H300; do 2 rewrite rev_length in H300; auto.
  symmetry; eapply eval_length_rev; eauto.
  apply tl_vl_match_leneq';auto.
  rewrite H200 in H100; clear H200.
  remember (revlcons d1 d2) as d.
  gen H1 H100.
  clear.
  gen d vl.
  induction d; induction vl; simpl; intros.
  eexists; eauto.
  omega.
  rewrite H1.
  lets H200 : IHd (@nil val); clear IHd; rename H200 into IHd; simpl in IHd.
  apply andb_prop in H1; destruct H1.
  apply IHd in H0; clear IHd.
  2 : omega.
  destruct H0.
  rewrite H0.
  eexists; eauto.
  rewrite H1.
  lets H200 : IHd vl; clear IHd; rename H200 into IHd.
  apply andb_prop in H1; destruct H1.
  apply IHd in H0; clear IHd.
  2 : omega.
  destruct H0.
  rewrite H0.
  eexists; eauto.
  remember (revlcons d1 d2) as d.
  gen H1; clear; intros.
  induction d; simpl.
  eexists; eauto.
  simpl in H1.
  rewrite H1.
  apply andb_true_iff in H1; destruct H1.
  apply IHd in H0.
  destruct H0.
  rewrite H0.
  eexists; eauto.
Qed.


Lemma join_mjoin_intro_intro: forall G E M1 isr aux M2 M3 M o,
                        joinmem (G,E,M1,isr,aux) M o -> 
                        join M2 M3 M
                    -> exists M',  joinmem (G,E,M',isr,aux) M2 o /\ join M1 M3 M'.
Proof.
  intros.
  unfold joinmem in *; mytac.
  assert(join M3 M2 M) as H0'.
  apply join_comm; auto.
  lets H100 : join_assoc_r H0' H2; mytac.
  eexists; mytac; eauto.
  do 6 eexists; mytac; eauto.
Qed.

Lemma alloc_lemma_aux: 
  forall d1  asrt vl a  M1 M2 M ir aux Os p n aop  o G E0  ks s f E, 
    GoodFunAsrt asrt ->
    buildp d1 vl = (Some a) ->
    join M1 M2 M -> 
    (G, E, M1, ir, aux, Os, aop) |= asrt -> 
    losallocstepn n p
                  (curs (salloc vl d1),
                   (kenil, kcall f  s E ks)) (G, E0, M, ir, aux)
                                        (curs (salloc nil dnil), (kenil, kcall f  s E ks)) o -> 
    exists E1 E2 M',
      join E0 E1 E2 /\ 
      joinmem (G, E2, M', ir, aux) M2 o /\
      (G, E2, M', ir, aux, Os, aop) |= (a **asrt**  <||aop||>)  /\ 
      (G, E1, empmem, ir, aux, empabst, aop) |= A_dom_lenv (getlenvdom d1)
 /\ exists Mx, join M1 Mx M'.
Proof.
  inductions d1.
(*base*)
  introv Hasrt H1.      
  simpl in H1.
  destruct vl; tryfalse.
  inverts H1.
  introv Hmj Hpre Hstep.
  inverts Hstep.
  
  Focus 2.
  unfolds in H.
  destruct H.
  unfolds in H1.
  destruct H1 as (v1 & d1& ks1 & x& t& Heq & Hneq & Hll).
  inverts Heq.
  exists (emp:env) E0 M1.
  splits; eauto.
  mytac.
  unfolds; do 6 eexists; splits;eauto.
  exists empmem M1 M1 empabst Os Os.
  splits; simpl; mytac.
  do 6 eexists; splits; eauto.
  apply join_comm.
  eapply join_emp; eauto.
  eapply join_comm.
  eapply join_emp; eauto.   
  eapply good_fun_asrt_absop; eauto.
  unfolds.
  split.
  simpl.
  unfold eq_dom_env.
  intros.
  splits; eauto.
  split.
  introv Hli.
  unfolds in Hli.
  unfold In in Hli.
  tryfalse.
  introv Hin.
  unfold EnvMod.indom in Hin.
  destruct Hin.
  unfold get in H; simpl in H.
  unfold EnvMod.get in H.
  unfold empenv in H.
  simpl in H.
  tryfalse.
  unfolds; auto.

  exists empmem; apply join_comm; apply join_emp; auto.
(*ind*) 
  introv Hasrt Heq.
  simpl in Heq.
  remember (negb (in_decllist i d1) && good_decllist d1) as Hb.
  destruct Hb; tryfalse.
  destruct vl; tryfalse.
  remember ( buildp d1 nil) as a1.
  destruct a1; tryfalse.
  apply eq_sym in Heqa1.
  inverts Heq.
  introv Hjm Hpre Hstep.
  inverts Hstep.
  unfolds in H.
  destruct H.
  invertstep idtac.
  unfolds in H1.
  destruct H1 as (vv & dd &kss & x & tp & Heq & Hlen & Hvnil & Hvn).
  inverts Heq.
  assert (nil = (nil:vallist)) by auto.
  apply Hvnil in H.
  destruct H as  (l&v&Ma &Hmap&Hjj).
  unfolds in Hjj.
  mytac.
  
  lets Hrs : join_assoc_l Hjm H3.
  destruct Hrs as (M2'& Hmj1 & Hmj2).
  lets Hrs : IHd1 Heqa1 Hmj2 Hpre H0;eauto. 
  destruct Hrs as (E1 & E2 & M'' & Hej & Hjj& Hsat1&Hsat2 & H_new).
  lets Hdes : EnvMod.join_assoc_l H2 Hej.
  destruct Hdes as (E1'& He1 & He2).
  lets Hadaa: join_mjoin_intro_intro Hjj Hmj1.
  destruct Hadaa as (Mm& Hmmj1 & Hmmj2).
  exists E1' E2 Mm.
  splits; eauto.

  apply StarAssocI.
  apply join_comm in Hmmj2.
  exists Ma M'' Mm empabst Os Os.
  split; mytac; auto.
  exists v.
  simpl.
  destruct Hsat2.
  simpl in H.
  do 7 eexists; splits; mytac; eauto.
  mytac;eauto.
  mytac.
  exists l; splits; eauto.
  unfold get; simpl.
  eapply env_join_get; eauto.
  unfolds; auto.
  split.
  
  eapply join_eq_dom_env; eauto.
  destruct Hsat2.
  simpl in H; auto.

  unfolds; simpl.
  unfold emposabst; auto.

  destruct H_new.
  clear - H Hmmj2.
  join auto.
  
  remember ( buildp d1 vl) as a1.
  destruct a1; tryfalse.
  apply eq_sym in Heqa1.
  inverts Heq.
  introv Hjm Hpre Hstep.
  inverts Hstep.
  unfolds in H.
  destruct H.
  invertstep idtac.
  unfolds in H1.
  destruct H1 as (vv & dd &kss & x & tp & Heq & Hlen & Hvnil & Hvn).
  inverts Heq.
  assert (v :: vl <> (nil:vallist)).
  intro; tryfalse.
  
  apply Hvn in H.
  destruct H as  (l&v0 &vl' &Ma &Heqv &Hmap&Hjj).
  apply eq_sym in Heqv; inverts Heqv.
  unfolds in Hjj.
  mytac.
  lets Hrs : join_assoc_l Hjm H3.
  destruct Hrs as (M2'& Hmj1 & Hmj2).
  lets Hrs : IHd1 Heqa1 Hmj2 Hpre H0;eauto. 
  destruct Hrs as (E1 & E2 & M'' & Hej & Hjj& Hsat1&Hsat2 & H_new).
  lets Hdes : EnvMod.join_assoc_l H2 Hej.
  destruct Hdes as (E1'& He1 & He2).
  lets Hadaa: join_mjoin_intro_intro Hjj Hmj1.
  destruct Hadaa as (Mm& Hmmj1 & Hmmj2).
  exists E1' E2 Mm.
  splits; eauto.
  apply StarAssocI.
  apply join_comm in Hmmj2.
  exists Ma M'' Mm empabst Os Os.
  split; mytac; auto.
  simpl.
  
  do 7 eexists; splits; mytac; eauto.
  mytac;eauto.
  mytac.
  exists l; splits; eauto.
  eapply env_join_get; eauto.
  unfolds; auto.
  
  destruct Hsat2.
  simpl; unfold emposabst; split; auto.
  simpl in H.
  eapply join_eq_dom_env; eauto.
  clear - H_new Hmmj2.
  join auto.
Qed.

Lemma GoodLocalInvAsrt_irrel :
  forall p G E E' M isr isr' aux aux' O aop aop',
    GoodLocalInvAsrt p ->
    (G, E, M, isr, aux, O, aop) |= p ->
    (G, E', M, isr', aux', O, aop') |= p.
Proof.
  inductions p; intros;
  try solve [simpl in *; simpljoin; auto];
  try solve [simpl in H; tryfalse].
  
  simpl in H0; simpl in H; simpljoin; simpl; split;
  [eapply IHp1; eauto | eapply IHp2; eauto].
  destruct H.
  destruct H0.
  left.
  eapply IHp1; eauto.
  right.
  eapply IHp2; eauto.

  simpl in H; simpl in H0; simpljoin.
  simpl.
  do 6 eexists; splits; eauto.

  destruct H1.
  exists x.
  eapply H; eauto.

  simpl in H0; simpljoin.
  simpl.
  eexists.
  splits; eauto.
Qed.

Lemma GoodLInvAsrt_irrel :
  forall li G E E' M isr isr' aux aux' O aop aop' t ll,
    GoodLInvAsrt li ->
    (G, E, M, isr, aux, O, aop) |= li t ll ->
    (G, E', M, isr', aux', O, aop') |= li t ll.
Proof.
  intros.
  pose proof H t ll.
  eapply GoodLocalInvAsrt_irrel; eauto.
  destruct H1;auto.
Qed.


Lemma Linv_igore:
  forall G E E' M isr isr' aux O  aux'  li t, 
    satp (G, E, M, isr, aux) O (CurLINV li t) ->
    satp (G,E', M,isr',aux') O (CurLINV li t).
Proof.
  intros.
  unfold CurLINV in *.
  unfold satp in *.
  intro.
  pose proof H aop.
  destruct H0.
  exists x.
  simpl in *; simpljoin.
  do 6 eexists; splits; eauto.
  do 8 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  eapply GoodLInvAsrt_irrel; eauto.
Qed.

Lemma  alloc_lemma : 
  forall  prespec s ks  n p f vl d1 d2 E G M1 M2 M ir aux o Os aop pre tp stmt ll t li, 
    Some prespec  = BuildPreI p f  vl ll pre t ->
    p f = Some (tp ,d1, d2, stmt) ->
    dl_vl_match d1 (rev vl) =true->
    join M1 M2 M -> 
    (G, E, M1, ir, aux, Os, aop) |= PRE  [pre, rev vl, ll, t] -> 
    satp  (G, E, M1, ir, aux)  Os  (CurLINV li t) -> 
    losallocstepn n p
                  (curs (salloc vl (revlcons d1 d2)),
                   (kenil, kcall f  s E ks)) (G, empenv, M, ir, aux)
                  (curs (salloc nil dnil), (kenil, kcall f  s E ks)) o -> 
    exists E' M' , joinmem  (G, E',M', ir ,aux )  M2 o /\
                   ((G, E',M', ir ,aux ), Os, aop) |= prespec /\
                   satp (G, E',M', ir ,aux )  Os  (CurLINV li t) . 
Proof.
  intros.
  unfold BuildPreI in *.
  rewrite H0 in H.
  remember (buildp (revlcons d1 d2) vl) as assn; destruct assn.
  Focus 2.
  rewrite H1 in H.
  tryfalse.
  
  inv H.
  lets Hrs : alloc_lemma_aux (eq_sym Heqassn) H2 H3 H5.
  eapply (getprop (pre (rev vl) ll t)).
  
  destruct Hrs as (E1 & E2 & MM & Hej & Hjmm & Hsat1 & Hsat2 & H_new).
  rewrite H1 in H7.
  inverts H7.
  exists E2 MM.
  splits;eauto.
  sep split in Hsat1.
  simpl in Hsat2.
  sep split.
  auto.
  simp join.
  assert (E1=E2) by join auto.
  subst E1.
  simpl. 
  auto.
  
  (*satp*)
  assert(satp (G, E2, M1, ir, aux) Os (CurLINV li t)).
  eapply Linv_igore; eauto.  
  clear - H H_new.
  destruct H_new.
  eapply join_satp_local_inv; eauto.
  unfold joinmem.
  do 6 eexists; splits; eauto.
  eapply join_comm; eapply join_emp; auto.
Qed.


Lemma tl_vl_dl'': 
  forall tl vl dl,  tl_vl_match tl vl = true ->  
                    tlmatch  (rev tl) dl ->
                    dl_vl_match dl (rev vl) =true.
Proof.
  intros.
  rewrite  tl_vl_rev_match in H.
  eapply tl_vl_dl;eauto.
Qed.

Lemma notabort_rete:
  forall e ,notabortm (nilcont (srete e)).
Proof.
  intros.
  unfold notabortm.
  splits.
  introv Hf.
  match goal with
    | H : ?P _ |- _ => unfold P in H; simp join; tryfalse
  end.
  unfold notabort.
  splits; introv Hf;
  match goal with
    | H : ?P _ |- _ => unfold P in H; simp join; tryfalse
  end.
Qed.

Lemma  estep_lstep_deter :
  forall c  G E M isr aux M1 M2 c' ke' m' p ke ks   o2 C o2',
    estep c ke (G, E, M) c' ke' m' ->
    joinm2 (G,E,M,isr,aux) M1 M2 o2 ->
    loststep p (c, (ke, ks)) o2 C o2' ->
    o2 = o2' /\ C = (c',(ke', ks )).
Proof.
  unfold joinm2.
  intros.
  unfold joinmem in *. 
  Definition cjy_and := and.
  fold cjy_and; simpljoin.
  rename x0 into x; rename x1 into x0; rename x2 into x1; rename x3 into x2;
  rename x4 into x3; rename x5 into x4; rename x8 into x7.
  rename H1 into H2.
  
  lets H100 : join_assoc_l H6 H4; simpljoin.
  apply join_sub_l in H1.
  clear H6 H4 H0; unfold cjy_and.

  inverts H2.
  inverts H9.
  inverts H0.
  invertstep (try solve [intuition auto]).
  
  cut (v = v0); [ intros; subst; auto | eapply evalval_deter; eauto ].
  cut (v = v0); [ intros; subst; auto | eapply evalval_deter; eauto ].
  cut (Tptr t = Tptr t0); [ intros H100; inv H100; auto | eapply evaltype_deter; eauto ].
  cut (Tstruct id' dl = Tstruct id'0 dl0); [ intros H100; inv H100; auto | eapply evaltype_deter; eauto ].
  rewrite H11 in H3; inv H3; auto.
  cut (Tptr t = Tptr t0); [ intros H100; inv H100; auto | eapply evaltype_deter; eauto ].
  erewrite evaltype_irrev_mem with (M':=x2) in H0;eauto.
  rewrite H9 in H0.
  inverts H0.
  erewrite evaltype_irrev_mem with (M':=x2) in H0;eauto.
  rewrite H9 in H0.
  inverts H0.
  cut (Tarray t n = Tarray t0 n0); [ intros H100; inv H100; auto | eapply evaltype_deter; eauto ].
  cut (Tstruct id' dl = Tstruct id'0 dl0); [ intros H100; inv H100; auto | eapply evaltype_deter; eauto ].
  rewrite H11 in H3; inv H3; auto.
  cut (Tarray t n = Tarray t0 n0); [ intros H100; inv H100; auto | eapply evaltype_deter; eauto ].
  cut (t = t0); [ intros; subst; auto | eapply evaltype_deter; eauto ].
   erewrite evaltype_irrev_mem with (M':=x2) in H0;eauto.
  rewrite H9 in H0.
  inverts H0.
  erewrite evaltype_irrev_mem with (M':=x2) in H0;eauto.
  rewrite H9 in H0.
  inverts H0.
   erewrite evaltype_irrev_mem with (M':=x2) in H0;eauto.
  rewrite H9 in H0.
  inverts H0.
  erewrite evaltype_irrev_mem with (M':=x2) in H0;eauto.
  rewrite H9 in H0.
  inverts H0.
  splits;auto.
  splits;auto.
  cut (t = t0); [ intros; subst; auto | eapply evaltype_deter; eauto ].
  splits;auto.
  cut (t0 = t1 /\ t3 = t2); [ intros H100; destruct H100; subst; auto | split; eapply evaltype_deter; eauto ].
  simpl in *;tryfalse.
  simpl in *;tryfalse.
  simpl in *;tryfalse.
  simpl in *;tryfalse.
  simpl in *;tryfalse.
  simpl in *;tryfalse.
  cut (t' = t'0); [ intros; subst; auto | eapply evaltype_deter; eauto ].
  rewrite H0 in H10;inverts H10;split;auto.
  
  cut (v = v0); [ intros; subst; auto | eapply load_mem_deter; eauto ].

  inverts H10;auto.
  rewrite H0 in H10; inv H10; auto.
  rewrite H0 in H12; inv H12; auto.
  inverts H0;
  intuition auto.
  inverts H2;inverts H;tryfalse;auto;intuition auto.
  inverts H2;inverts H;tryfalse;auto;intuition auto.
  inverts H11;inverts H;tryfalse.
  inverts H7;inverts H;tryfalse.
  inverts H9;inverts H;tryfalse.
  inverts H9;inverts H;tryfalse.
  inverts H9;inverts H;tryfalse.
  inverts H9;inverts H;tryfalse.
  inverts H9;inverts H;tryfalse.

  Grab Existential Variables.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
Qed.


Lemma estep_frame_loststep :
  forall p Mf c ke m c' ke' m' ks isr aux Ms  o2, 
    estep c ke m c' ke' m' -> 
    joinm2 (m, isr, aux) Ms  Mf o2 -> 
    loststep p (c, (ke, ks)) o2 (c', (ke', ks)) o2.
Proof.
  unfold joinm2.
  intros.
  unfold joinmem in *; mytac.

  rename x0 into x; rename x1 into x0; rename x2 into x1; rename x3 into x2;
  rename x4 into x3; rename x5 into x4; rename x8 into x7.
  
  constructor.
  econstructor.
  eauto.

  inv H; try solve [econstructor; eauto;
   eapply evaltype_eq_prop; eauto ].
  econstructor;eauto.
  eapply evalval_eq_prop; eauto.
  apply join_sub_l in H3.
  apply join_sub_l in H5.
  eapply sub_trans; eauto.
  
  econstructor;eauto.
  inv H0.
  eapply load_mem_mono; eauto.
  apply join_sub_l in H3.
  apply join_sub_l in H5.
  eapply sub_trans; eauto.
Qed.

Lemma estep_msim_hold :
  forall c ke  m c' ke' m' li t,
    estep c ke m c' ke' m'  -> 
    forall  ks Fspec sd  gamma O  I r ri q isr aux,
      satp (m, isr, aux) O (CurLINV li t) ->
      MethSimMod Fspec sd (c',(ke',ks)) (m',isr,aux)  gamma O li  I r ri q t ->
      MethSimMod Fspec sd (c,(ke,ks)) (m,isr,aux)  gamma O  li I r ri q t.
Proof.
  introv Hestep Hsim.
  constructors; introv Hfalse; tryfalse.
  introv Hinv Hjm1 Hjm2 Hlstep.
  destruct m as [[G E] M].
  lets Hex : estep_lstep_deter  Hestep Hjm1  Hlstep. 
  destruct Hex.
  subst o2'.
  subst C'.
  exists  gamma  OO (G, E,M , isr, aux)  Ms O Os.
  splits; eauto.
  constructors.
  lets Heqm : estep_mem_same Hestep.
  subst m'.
  auto.
  inverts Hfalse.
  invertstep tryfalse.
  inverts Hfalse.
  invertstep tryfalse.
  inverts Hfalse.
  invertstep tryfalse.
  inverts Hfalse.
  invertstep tryfalse.
  inverts Hfalse.
  invertstep tryfalse.
  inverts Hfalse.
  invertstep tryfalse.
  introv  Hjj2 Hinv Hdisj Hff.
  apply Hff.
  exists (c',(ke',ks)) o2.         
  eapply estep_frame_loststep; eauto.
  inverts Hfalse.
  invertstep tryfalse.
  inverts Hfalse.
  invertstep tryfalse.
Qed.


Lemma estepstar_msim_hold :
  forall c ke  m c' ke' m' ,
    estepstar c ke m c' ke' m'  -> 
    forall  ks Fspec sd  gamma O  I r ri q isr aux li t,
      satp (m, isr, aux) O (CurLINV li t) ->
      MethSimMod Fspec sd (c',(ke',ks)) (m',isr,aux)   gamma O  li I r ri q t ->
      MethSimMod Fspec sd (c,(ke,ks)) (m,isr,aux)   gamma O  li I r ri q  t.
Proof.
  introv Hestar.
  inductions Hestar; auto.
  introv Hsat Hsim.
  eapply  estep_msim_hold.  eauto.
  auto.
  eapply IHHestar.
  lets Heqm : estep_mem_same H.
  subst.
  eauto.
  auto.
Qed.

Lemma estepstar_estep_trans : 
  forall c ke m c' ke' m' c'' ke'' m'',
    estepstar c ke m c' ke' m' ->
    estep  c' ke' m' c'' ke'' m'' ->  estepstar c ke m c'' ke'' m''.
Proof.
  induction 1.
  introv Hs. 
  constructors.
  eauto.
  constructors.
  intros.
  apply IHestepstar in H1.
  constructors.
  eauto.
  eauto.
Qed.


Lemma estepstar_estepstar_trans : 
  forall c ke m c' ke' m' c'' ke'' m'',
    estepstar c ke m c' ke' m' -> estepstar  c' ke' m' c'' ke'' m'' ->  
    estepstar c ke m c'' ke'' m''.
Proof.
  induction 1.
  introv Hs. 
  eauto.
  intros.
  apply IHestepstar in H1.
  constructors.
  eauto.
  eauto.
Qed.


Lemma field_offset_plus :
  forall i d  n  z1 z2,  
    field_offsetfld i d z1 = Some n -> 
    field_offsetfld i d  (Int.add z1 z2) = Some (Int.add n z2). 
Proof.
  introv H1.
  gen z2.
  inductions  d.
  simpl in H1.
  inverts H1.
  simpl in H1.
  simpl. 
  remember (Zbool.Zeq_bool i i0) as Zeq.
  destruct Zeq; tryfalse.
  inverts H1.
  auto.
  simpl in H1.
  intros.
  apply IHd with (z1:= (Int.add (Int.repr (Z.of_nat (typelen t))) z1)) (z2:=z2) 
    in H1.
  rewrite  Int.add_assoc in H1.
  auto. 
Qed. 

Lemma structtype_imply_fieldoffset :  
  forall i d t, memory.ftype i d = Some t ->
                exists n, field_offset i d = Some n.
Proof.
  introv Hem.
  gen i t Hem.
  inductions d.
  introv Hem.
  simpl in Hem. 
  inverts Hem.
  introv Hem.
  simpl in Hem.
  unfold field_offset.
  simpl.
  remember ( Zbool.Zeq_bool i0 i) as Heq.
  destruct Heq; tryfalse.
  exists (Int.zero). 
  auto.
  apply IHd in Hem. 
  destruct Hem.
  unfold field_offset in H.
  exists (Int.add x  (Int.repr (Z.of_nat (typelen t))) ).
  rewrite Int.add_commut.
  apply  field_offset_plus  with (z2:=  Int.repr (Z.of_nat (typelen t))) in H.
  auto.
Qed.

Lemma evalval_imply_evaltype : 
  forall (e : expr) (m : smem) v , 
    evalval e m = Some v ->
    exists t, evaltype e m = Some t.
Proof.
  introv He.
  remember (evaltype e m) as Hee.
  unfold evalval in He;  destruct e; destruct Hee; try  rewrite <- HeqHee  in He; tryfalse
  ; exists t; auto.
  simpl evaltype in HeqHee.
  destruct m in HeqHee.
  destruct p in HeqHee.
  destruct  (evaltype e (e0,e1,m)); tryfalse.
  destruct t1; tryfalse.
  destruct t; tryfalse.
  auto.
  destruct t;tryfalse;auto.
  destruct t;tryfalse;auto.

  destruct t;tryfalse;auto.
  destruct t;tryfalse;auto.
  destruct t;tryfalse;auto.
Qed.


Lemma evalval_evaladdr_imply_estepstar : forall (e:expr) (m : smem),
(forall v ke,  evalval e m = Some v -> 
  estepstar (cure e) ke  m [v]ke m) /\
    (forall v ke, evaladdr e m = Some v ->
          estepstar (cure (eaddrof e)) ke  m [v] ke m).
Proof.
inductions e.
+split.
 -introv Heval.
  constructors.
  constructors.
  unfold evalval in Heval.
  simpl in Heval.
  destruct m as [[ge le] M].
  inverts Heval.
  constructors.
 -introv Haddr.
  destruct m as [[ge le] M].
  simpl in Haddr.
  inverts Haddr.
+split.
 -introv Heval.
  constructors.
  constructors.
  eauto.
  constructors.
 -introv Haddr.
  constructors.
  constructors.
  destruct m as [[ge le] M].
  simpl.
  simpl in Haddr.
  rewrite Haddr.
  destruct (get le v); destruct ( get ge v). 
  destruct p; tryfalse.
  eauto.
  destruct p; eauto; tryfalse.
  destruct p; eauto; tryfalse.
  auto.
  constructors.
+split.
 -introv Heval.
  constructors.
  constructors.
  destruct m as [[ge le] M].
  simpl in Heval.
  inverts Heval.
  constructors.
 -introv Heval.
  simpl in Heval.
  inverts Heval.
+split. 
 -introv Heval.
  destruct m as [[ge le] M]. 
  simpl in Heval.
  remember (evaltype e (ge,le,M)) as Het.
  remember (evalval e (ge,le,M)) as Hem.
  destruct Het; destruct Hem; tryfalse.
  assert (evalval e (ge,le,M) = Some v0) as Hee ; auto.
  assert (evaltype  e  (ge,le,M) = Some t) as Htt; auto.
  destruct (IHe (ge,le,M)  ) as [IHe1 IHe2].
  apply IHe1 with (ke:= (keop1 u t ke))  in Hee.
  constructors.
  constructors.
  eauto.
  assert (estep (curs (sskip (Some v0))) (keop1 u t ke) (ge,le,M) [v] ke (ge,le,M) ).
  constructors.
  destruct (uop_type t u); tryfalse.
  eauto.
  eapply estepstar_estep_trans; eauto.
  destruct (uop_type t u); tryfalse.
 -introv Haddr.
  simpl in Haddr.
  inverts Haddr.
+split.
 -introv Heval.
  simpl in Heval.
  remember (evaltype e1 m) as Het1.
  remember (evalval e1 m) as Hem1.
  remember (evaltype e2 m) as Het2.
  remember (evalval e2 m) as Hem2.
  destruct m as [[ge le] M];  destruct Het1;
   destruct Hem1; destruct Het2; destruct Hem2; tryfalse.
  apply eq_sym in HeqHet1. 
  apply eq_sym in HeqHet2.
  apply eq_sym in HeqHem1.
  apply eq_sym in HeqHem2.
  destruct (IHe1 (ge,le,M)) as [IHe11 IHe12].
  destruct (IHe2 (ge,le,M)) as [IHe21 IHe22].
  apply IHe11  with (ke:= (keop2r b e2 t t0 ke) ) in HeqHem1. 
  apply IHe21  with (ke:= (keop2l b v0 t t0 ke) ) in HeqHem2. 
  assert( estepstar (cure e1) (keop2r b e2 t t0 ke) (ge,le,M)
          (cure e2) (keop2l b v0 t t0 ke)(ge,le,M)).
  eapply estepstar_estep_trans; eauto.
  constructors.
  constructors.
  constructors.
  eauto.
  eauto.
  eapply estepstar_estepstar_trans; eauto.
  eapply estepstar_estep_trans;eauto.
  constructors.
  destruct (bop_type t t0 b) ; tryfalse.
  auto.
  destruct (bop_type t t0 b) ; tryfalse.
  destruct (bop_type t t0 b) ; tryfalse.
  destruct (bop_type t t0 b) ; tryfalse.
 -introv Haddr.
  simpl in Haddr.
  inverts Haddr.
+split.
 -introv Heval.
  simpl in Heval.
  remember (evaltype e m) as Het.
  remember (evalval e m) as Hem.
  destruct m as [[ge le] M];    destruct Het; destruct Hem;  tryfalse.
  destruct t;  destruct v0;  tryfalse.
  apply eq_sym in HeqHet.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M)) as [IHe1 IHe2].
  apply IHe1 with (ke := kederef t ke) in HeqHem.
  constructors.
  constructors.
  eauto.
  eapply estepstar_estep_trans.
  eauto.
  constructors.
  eauto.
  eauto.
  destruct t;  tryfalse.
 -introv Haddr.
  constructors.
  constructors.
  eapply IHe.
  simpl in Haddr. 
  auto.
+split.
 -introv Heval.
  simpl in Heval.
  remember (evaltype e m) as Het. 
  remember (evaladdr e m) as Hea.
  destruct m as [[ge le] M];   destruct Het; destruct Hea; tryfalse.
  destruct (IHe (ge,le,M)) as [IHe1 IHe2].
  apply eq_sym in HeqHet.
  apply eq_sym in HeqHea.
  apply IHe2 with (ke:=ke) in HeqHea .
  destruct e;  inverts Heval; eauto;  tryfalse.
  constructors.
  constructors. rewrite H0. 
  remember (evaltype e (ge, le, M)) as Het.
  destruct Het; tryfalse. destruct t0; tryfalse.
  simpl in IHe2.
  apply IHe2  with (ke := ke)in H0.
  inverts H0; tryfalse.
  inverts H. eauto.
  destruct e;  inverts Heval; eauto;  tryfalse.
constructors.
  constructors. rewrite H0. 
  remember (evaltype e (ge, le, M)) as Het.
  destruct Het; tryfalse. destruct t0; tryfalse.
  simpl in IHe.
  eapply IHe  with (ke := ke)in H0.
  inverts H0; tryfalse.
  inverts H. eauto.
  destruct e;  inverts Heval; eauto;  tryfalse.
constructors.
  constructors. rewrite H0. 
  remember (evaltype e (ge, le, M)) as Het.
  destruct Het; tryfalse. destruct t; tryfalse.
  simpl in IHe.
  eapply IHe  with (ke := ke)in H0.
  inverts H0; tryfalse.
  inverts H. eauto.
  destruct e;  inverts Heval; eauto;  tryfalse.
constructors.
  constructors. rewrite H0. 
  remember (evaltype e (ge, le, M)) as Het.
  destruct Het; tryfalse. destruct t; tryfalse.
  simpl in IHe.
  eapply IHe  with (ke := ke)in H0.
  inverts H0; tryfalse.
  inverts H. eauto.
 - introv Haddr.
   simpl in Haddr. inverts Haddr.
+ split.
 -introv Heval.
  simpl in Heval.
  remember (evaltype e m) as Het. 
  remember (evaladdr e m) as Hea.
  destruct m as [[ge le] M];   destruct Het; destruct Hea; tryfalse.
  destruct (IHe (ge,le,M)) as [IHe1 IHe2].
  apply eq_sym in HeqHet.
  apply eq_sym in HeqHea.
  destruct t; tryfalse.
  remember (memory.ftype i d) as Hft.
  destruct Hft; destruct v0; tryfalse.
  destruct a; tryfalse.
  simpl in Heval.
  assert (evaladdr e (ge,le,M)=
           Some (Vptr (b, i1))) as Headdr; auto.
  apply eq_sym in HeqHft.
  assert (memory.ftype i d = Some t) as Hmf; auto.
  apply structtype_imply_fieldoffset in Hmf.
  destruct Hmf as [n Hfo]. 
  constructors.
  constructors.
  eauto.
  eauto.
  constructors.
  constructors.
  eauto.
  eauto.
  apply IHe2 with (ke:=(keoffset n (kederef t ke))) in HeqHea .
  eapply estepstar_estepstar_trans.
  eauto.
  constructors.
  constructors.
  constructors.
  constructors.
  eauto.
  remember (getoff b  (Int.unsigned i1)  i e (ge,le,M)) as Hget.
  destruct Hget .
  unfold getoff in HeqHget.
  rewrite HeqHet in HeqHget.
  rewrite Hfo in HeqHget.
  inverts HeqHget.
  rewrite Int.repr_unsigned in Heval.
  eauto.
  inverts Heval.
  constructors.
  destruct t; tryfalse.
  destruct (memory.ftype i d); tryfalse.
 -introv Haddr.
  simpl in Haddr.
  remember (evaladdr e m) as Hea.
   destruct Hea; tryfalse.
  destruct v0; tryfalse.
  destruct a.
  destruct (IHe m) as [IHe1 IHe2].
 remember (getoff b (Int.unsigned i0) i e  m) as Hget.
 destruct Hget; tryfalse.
 unfold getoff in HeqHget.
 remember ( evaltype e m) as Het.
 destruct Het; tryfalse.
 destruct t; tryfalse.
 remember (field_offset i d) as Hft.
 destruct Hft; tryfalse.
 apply  eq_sym in HeqHea.
 constructors.
 constructors.
 eauto.
 eauto.
 inverts HeqHget.
 apply IHe2 with (ke := keoffset i2 ke ) in  HeqHea.
 eapply estepstar_estepstar_trans.
 eauto.
 constructors.
 constructors.
 inverts Haddr.
 rewrite Int.repr_unsigned.
 constructors.
 
+split.
 -introv Heval.
  simpl in Heval.
  remember (evalval e m) as Hem.
  remember (evaltype e m) as Het. 
  destruct m as [[ge le] M ]; destruct Hem; destruct Het;  tryfalse.
  destruct t0;destruct t; tryfalse.
  simpl in *.
  inverts Heval.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M) ) as [IHe1 IHe2].
  apply IHe1 with (ke := ke) in HeqHem.
  constructors.
  eapply ecastnull_step;eauto.
  auto.
  simpl in *.
  inverts Heval.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M) ) as [IHe1 IHe2].
  apply IHe1 with (ke := (kecast Tint8 Tint8 ke) ) in HeqHem.
  constructors.
  eapply ecastint_step;eauto.
  eapply estepstar_estep_trans;eauto.
  destruct v0;tryfalse.
  eapply evcastint_step;eauto.

  simpl in *.
  inverts Heval.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M) ) as [IHe1 IHe2].
  apply IHe1 with (ke := (kecast Tint8 Tint16 ke) ) in HeqHem.
  constructors.
  eapply ecastint_step;eauto.
  eapply estepstar_estep_trans;eauto.
  destruct v0;tryfalse.
  eapply evcastint_step;eauto.

  
  simpl in *.
  inverts Heval.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M) ) as [IHe1 IHe2].
  apply IHe1 with (ke := (kecast Tint8 Tint32 ke) ) in HeqHem.
  constructors.
  eapply ecastint_step;eauto.
  eapply estepstar_estep_trans;eauto.
  destruct v0;tryfalse.
  eapply evcastint_step;eauto.

  simpl in *.
  inverts Heval.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M) ) as [IHe1 IHe2].
  apply IHe1 with (ke := (kecast Tint16 Tint8 ke) ) in HeqHem.
  constructors.
  eapply ecastint_step;eauto.
  eapply estepstar_estep_trans;eauto.
  destruct v0;tryfalse.
  eapply evcastint_step;eauto.
  
  simpl in *.
  inverts Heval.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M) ) as [IHe1 IHe2].
  apply IHe1 with (ke := (kecast Tint16 Tint16 ke) ) in HeqHem.
  constructors.
  eapply ecastint_step;eauto.
  eapply estepstar_estep_trans;eauto.
  destruct v0;tryfalse.
  eapply evcastint_step;eauto.

  simpl in *.
  inverts Heval.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M) ) as [IHe1 IHe2].
  apply IHe1 with (ke := (kecast Tint16 Tint32 ke) ) in HeqHem.
  constructors.
  eapply ecastint_step;eauto.
  eapply estepstar_estep_trans;eauto.
  destruct v0;tryfalse.
  eapply evcastint_step;eauto.

  simpl in *.
  inverts Heval.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M) ) as [IHe1 IHe2].
  apply IHe1 with (ke := (kecast Tint32 Tint8 ke) ) in HeqHem.
  constructors.
  eapply ecastint_step;eauto.
  eapply estepstar_estep_trans;eauto.
  destruct v0;tryfalse.
  eapply evcastint_step;eauto.

  simpl in *.
  inverts Heval.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M) ) as [IHe1 IHe2].
  apply IHe1 with (ke := (kecast Tint32 Tint16 ke) ) in HeqHem.
  constructors.
  eapply ecastint_step;eauto.
  eapply estepstar_estep_trans;eauto.
  destruct v0;tryfalse.
  eapply evcastint_step;eauto.

  simpl in *.
  inverts Heval.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M) ) as [IHe1 IHe2].
  apply IHe1 with (ke := (kecast Tint32 Tint32 ke) ) in HeqHem.
  constructors.
  eapply ecastint_step;eauto.
  eapply estepstar_estep_trans;eauto.
  destruct v0;tryfalse.
  eapply evcastint_step;eauto.

  simpl in *.
  inverts Heval.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M) ) as [IHe1 IHe2].
  apply IHe1 with (ke := ke) in HeqHem.
  constructors.
  eapply ecast_step;eauto.
  auto.

  
  simpl in *.
  inverts Heval.
  apply eq_sym in HeqHem.
  destruct (IHe (ge,le,M) ) as [IHe1 IHe2].
  apply IHe1 with (ke := ke) in HeqHem.
  constructors.
  eapply ecastcomptr_step;eauto.
  auto.
  

  destruct t0; destruct t; tryfalse.
 -introv Haddr. 
  simpl in Haddr.
  inverts Haddr.

(*******************)
+split.
 -introv Heval.
  simpl in Heval.
  remember ( evaltype e1 m) as Het1.
  remember ( evaltype e2 m) as Het2.
  remember (evalval e2 m) as Hem.
  remember (evalval e1 m) as Hea.
  destruct (IHe1 m) as [IHe11 IHe12].
  destruct (IHe2 m) as [IHe21 IHe22].
  apply eq_sym in HeqHea.
  apply eq_sym in HeqHem.
  destruct m as [[ge le] M];  destruct Het1;  destruct Het2; tryfalse.
  destruct t; destruct t0; destruct Hea ; tryfalse.
  destruct v0; tryfalse.
  destruct a;  destruct Hem; tryfalse.
  constructors.
  eapply eaptrelem_step.
  eauto.
  constructors.
  eapply eaptrelemaddr_step.
  eauto.
  apply IHe11 with (ke :=  (kearrbase e2 t (kederef t ke))) in HeqHea.
  eapply estepstar_estepstar_trans.
  eauto.
  constructors.
  constructors.
  destruct v0; tryfalse.
  apply IHe21 with (ke:=  (kearrindex (Vptr (b, i)) t (kederef t ke)) ) in HeqHem.
  eapply estepstar_estepstar_trans.
  eauto.
  constructors.
  constructors;eauto.
  constructors.
  constructors.
  eauto.
  simpl get_mem in Heval.
  eauto. 
  constructors.

  destruct v0; tryfalse.
  destruct a;  destruct Hem; tryfalse.
  destruct v0; tryfalse.
  constructors.
  eapply eaptrelem_step.
  eauto.
  constructors.
  eapply eaptrelemaddr_step;eauto.

  apply IHe11 with (ke :=  (kearrbase e2 t (kederef t ke))) in HeqHea.
  eapply estepstar_estepstar_trans.
  eauto.
  constructors.
  constructors.
  eauto.
  eapply estepstar_estepstar_trans.
  eapply IHe21; eauto.
  constructors.
  constructors;eauto.
  constructors; eauto.
  constructors;eauto.
  constructors.
  destruct v0; tryfalse.
  destruct a;  destruct Hem; tryfalse.
  destruct v0; tryfalse.
  constructors.
  eapply eaptrelem_step.
  eauto.
  constructors.
  eapply eaptrelemaddr_step.
  eauto.
  apply IHe11 with (ke :=  (kearrbase e2 t (kederef t ke))) in HeqHea.
  eapply estepstar_estepstar_trans.
  eauto.
  constructors.
  constructors.
  eauto.
  eapply estepstar_estepstar_trans.
  eapply IHe21; eauto.
  constructors.
  constructors;eauto.
  constructors; eauto.
  constructors;eauto.
  constructors.

  destruct v0; tryfalse.
  destruct a;  destruct Hem; tryfalse.
  destruct v0; tryfalse.
  constructors.
  eapply eaelem_step.
  eauto.
  constructors.
  eapply eaelemaddr_step.
  eauto.
  apply IHe11 with (ke :=  (kearrbase e2 t (kederef t ke))) in HeqHea.
  eapply estepstar_estepstar_trans.
  eauto.
  constructors.
  constructors.
  eauto.
  eapply estepstar_estepstar_trans.
  eapply IHe21; eauto.
  constructors.
  constructors;eauto.
  constructors; eauto.
  constructors;eauto.
  constructors.

    destruct v0; tryfalse.
  destruct a;  destruct Hem; tryfalse.
  destruct v0; tryfalse.
  constructors.
  eapply eaelem_step.
  eauto.
  constructors.
  eapply eaelemaddr_step.
  eauto.
  apply IHe11 with (ke :=  (kearrbase e2 t (kederef t ke))) in HeqHea.
  eapply estepstar_estepstar_trans.
  eauto.
  constructors.
  constructors.
  eauto.
  eapply estepstar_estepstar_trans.
  eapply IHe21; eauto.
  constructors.
  constructors;eauto.
  constructors; eauto.
  constructors;eauto.
  constructors.

    destruct v0; tryfalse.
  destruct a;  destruct Hem; tryfalse.
  destruct v0; tryfalse.
  constructors.
  eapply eaelem_step.
  eauto.
  constructors.
  eapply eaelemaddr_step.
  eauto.
  apply IHe11 with (ke :=  (kearrbase e2 t (kederef t ke))) in HeqHea.
  eapply estepstar_estepstar_trans.
  eauto.
  constructors.
  constructors.
  eauto.
  eapply estepstar_estepstar_trans.
  eapply IHe21; eauto.
  constructors.
  constructors;eauto.
  constructors; eauto.
  constructors;eauto.
  constructors.

  destruct t; tryfalse.

 -introv Heval.
  simpl in Heval.
  remember ( evaltype e1 m) as Het1.
  remember ( evaltype e2 m) as Het2.
  remember (evalval e2 m) as Hem.
  remember (evalval e1 m) as Hea.
  destruct (IHe1 m) as [IHe11 IHe12].
  destruct (IHe2 m) as [IHe21 IHe22].
  apply eq_sym in HeqHea.
  apply eq_sym in HeqHem.
  destruct m as [[ge le] M];  destruct Het1;  destruct Het2; tryfalse.
  destruct t; destruct Hea ; tryfalse.
  destruct v0; tryfalse.
  destruct a;  destruct Hem; tryfalse.
  destruct v0;tryfalse.
  constructors.
  eapply eaptrelemaddr_step;eauto.
  apply IHe11 with (ke :=  (kearrbase e2 t ke)) in HeqHea.
  eapply estepstar_estepstar_trans.
  eauto.
  constructors.
  constructors.
  eapply estepstar_estepstar_trans.
  eapply IHe21; eauto.
  constructors.
  constructors.
  eauto.
  eauto.
  inverts Heval;constructors.
  

  destruct v0; tryfalse.
  destruct a;  destruct Hem; tryfalse.
  destruct v0;tryfalse.
  constructors.
  eapply eaelemaddr_step;eauto.
  apply IHe11 with (ke :=  (kearrbase e2 t ke)) in HeqHea.
  eapply estepstar_estepstar_trans.
  eauto.
  constructors.
  constructors.
  eapply estepstar_estepstar_trans.
  eapply IHe21; eauto.
  constructors.
  constructors.
  eauto.
  eauto.
  inverts Heval;constructors.
  destruct t;tryfalse.
  destruct Hem;tryfalse.
  apply evalval_imply_evaltype in HeqHem ;destruct HeqHem ;tryfalse.
  destruct Hea;tryfalse.
  destruct v0;tryfalse.
  destruct a;tryfalse.
    destruct Hem;tryfalse.
  apply evalval_imply_evaltype in HeqHem ;destruct HeqHem ;tryfalse.
  destruct Hea;tryfalse.
  destruct v0;tryfalse.
  destruct a;tryfalse.
Qed.



Lemma  evalval_imply_estepstar  :  
  forall (e:expr) (m : smem)  v ke,  
    evalval e m = Some v -> 
    estepstar (cure e) ke  m [v] ke m.
Proof.
  introv Heval .
  generalize (evalval_evaladdr_imply_estepstar e m).
  introv H.
  destruct H as [H1 H2].
  apply H1.
  auto.
Qed.

Lemma  evaladdr_imply_estepstar  : 
  forall (e:expr) (m : smem)  v ke, 
    evaladdr e m = Some v -> 
    estepstar (cure (eaddrof e)) ke  m [v] ke m.
Proof.
  introv Heval .
  generalize (evalval_evaladdr_imply_estepstar e m).
  introv H.
  destruct H as [H1 H2].
  apply H2.
  auto.
Qed.


Lemma skip_expr_eval_msim_hold :
  forall (e:expr) (m : smem)  v ke, 
    evalval e m = Some v ->
    forall ks isr  aux C C' o,
      C =  (cure e, (ke,ks)) -> 
      C' = ((curs (sskip (Some v))), (ke, ks)) ->
      o =  (m , isr, aux) ->
      forall FSpec  sd gamma O  I r ri q li t, 
        satp o O (CurLINV li t) ->
        MethSimMod FSpec sd C' o  gamma O li  I r ri q t ->
        MethSimMod FSpec sd C o  gamma O li  I r ri q t.
Proof.
  introv Hevl.
  introv Hc Hc' Ho Hsim.
  subst C C'.
  lets Hlo : evalval_imply_estepstar ke Hevl.
  destruct o as [[]].
  inverts Ho.
  eapply  estepstar_msim_hold ; eauto.
Qed.


Lemma evaladdr_val_eq : 
  forall e m v t, 
    evaltype e m = Some t -> 
    evaladdr e m = Some v -> 
    evalval (eaddrof e) m = Some v.
Proof.
  intros. 
  destruct e; destruct m as [[]];simpl in *; tryfalse; try rewrite H; auto.
  destruct (evaltype e (e0, e1, m) ) ; tryfalse.
  destruct t0; tryfalse.
  inverts H. auto.
Qed.

Lemma evaltype_GE_eq : 
  forall G E M1 M2 e t1 t2, 
    evaltype e (G, E, M1) = Some t1 -> 
    evaltype e (G,E,M2) = Some t2 ->
    t1 = t2.
Proof.
  intros.
  cut (Some t1 = Some t2).
  intros;inverts H1;eauto.
  rewrite<-H,<-H0.
  clear.
  induction e;intros;
  try solve [
        unfold evaltype;auto |
        simpl in *;erewrite IHe;eauto |
        simpl in *;erewrite IHe1;erewrite IHe2;eauto | simpl in *;erewrite IHe;eauto  ].
  simpl in *. rewrite IHe.
  destruct e; auto.
  erewrite evaltype_irrev_mem.
  eauto.
Qed.

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
                                       simpl starinv_isr in *).

Lemma store_mapstoval_mono_rev2 :
  forall M1 M2 M12 M3 M123 M123' l t v1 v2,
    mapstoval l t true v1 M1 ->
    join M1 M2 M12 ->
    join M12 M3 M123 ->
    store t M123 l v2 = Some M123' ->
    exists M12', store t M12 l v2 = Some M12' /\ join M12' M3 M123'.
Proof.
  intros.
  lets H200 : join_assoc_l H0 H1; mytac.
  lets H100 : store_mapstoval_frame H H4 H2; mytac.
  lets H100 : store_mono H0 H5; mytac.
  lets H100 : join_store H0 H5 H7.
  lets H200 : join_assoc_r H3 H6; mytac.
  lets H200 : join_unique H100 H8; subst.
  eauto.
Qed.


Lemma assign_loststep_exists' : 
  forall p v l t o1  o3 C o3' Mf Ms aop O P v1, 
    loststep p (curs (sskip  (Some (Vptr l))), 
                (kenil,kassignl v t kstop)) o3 C o3' -> 
    joinm2 o1 Ms Mf o3 ->
    (o1, O, aop) |= P ** ( (addrval_to_addr l) # t |-> v1) ->
    exists o1', 
      loststep p (curs (sskip  (Some (Vptr l))), (kenil,kassignl v t kstop)) o1 C o1'/\ joinm2 o1' Ms Mf o3'.
Proof.
  unfold joinm2.
  intros.
  unfold joinmem in *; mytac.
  rename x0 into x; rename x1 into x0; rename x2 into x1; rename x3 into x2;
  rename x4 into x3; rename x5 into x4.
  rename x1 into x1'; rename x8 into x1.
  rename x2 into x8.
  rename x1' into x2.
  rename H4 into H4'; rename H6 into H4; rename H4' into H6.
  rename H1 into H2.

  invertstep idtac.
  unfold sat in H2; fold sat in H2; mytac.
  trysimplsall; mytac.
  unfold substmo in *.
  cut (exists M1 M2, store t x1  (addrval_to_addr l) v = Some M1 /\ join M1 Ms M2 /\ join M2 Mf M').
  intros; mytac.
  do 2 eexists; mytac.
  apply ostc_step.
  eapply stmt_step; eauto.
  econstructor; eauto.
  do 6 eexists; mytac; eauto.
  lets H100 : join_assoc_l H4 H6; mytac.

  apply join_comm in H0.
  lets H100 : store_mapstoval_mono_rev2 H5 H0 H1 H14; mytac. 
  lets H100 : join_assoc_r H H7; mytac.
  eauto.
Qed.

Lemma  store_asrt_hold : 
  forall G E M M' e l v isr aux O aop p tp1 tp2 ,
    assign_type_match tp1 tp2 ->
    (G,E,M, isr,aux,O,aop) |= Rv  e@tp2 == v  ->
    (G,E,M, isr,aux,O,aop) |=  p ** (EX v1 : val, l # tp1 |-> v1) ->
    store tp1 M l v = Some M' ->  
    (G,E,M', isr,aux,O,aop) |=  p ** l # tp1 |-> v.
Proof.
  intros.
  simpl in *; mytac.
  apply join_comm in H3.
  lets H200 : store_mapstoval_frame1 H7 H3 H2; mytac.
  apply join_comm in H5.
  do 6 eexists; mytac; eauto.
Qed.


(*-------------------*)
Lemma  store_asrt_hold' : 
  forall G E M M' e l v isr aux O aop p tp1 tp2 v1,
    assign_type_match tp1 tp2 ->
    (G,E,M, isr,aux,O,aop) |= Rv  e@tp2 == v  ->
    (G,E,M, isr,aux,O,aop) |=  p ** ( l # tp1 |-> v1) ->
    store tp1 M l v = Some M' ->  
    (G,E,M', isr,aux,O,aop) |=  p ** l # tp1 |-> v.
Proof.
  intros.
  simpl in *; mytac.
  apply join_comm in H3.
  lets H200 : store_mapstoval_frame1 H7 H3 H2; mytac.
  apply join_comm in H5.
  do 6 eexists; mytac; eauto.
Qed.


Lemma ptomvallist_eqlen_storebytes_exists :
  forall b o l1 l2 M ,
    ptomvallist (b, o) true l1 M ->
    length l1 = length l2 ->
    exists M', storebytes M (b, o) l2 = Some M'.
Proof.
  intros.
  gen l1 l2 b o M.
  induction l1, l2; intros; simpl in *.
  eauto.
  tryfalse.
  tryfalse.
  inv H0.
  mytac.
  lets H100 : IHl1 H2 H1; clear IHl1 H2 H1; mytac.
  unfold ptomval in H0; subst.
  assert (get M (b, o) = Some (true, a)) as H200.
  eapply mem_join_get_get_l_true; eauto.
  apply get_sig_some.

  unfold get in *; simpl in *.
  rewrite H200; clear H200.
  apply join_comm in H.
  lets H100 : storebytes_mono H H1; clear H H1; mytac.
  change Z with offset.
  rewrite H.
  eauto.
Qed.


Lemma store_exist_join': 
  forall l tp x y M1 M2 M3, 
    mapstoval l tp true x M1 ->
    join M1 M2 M3 ->
    exists M', store tp M3 l y = Some M'.
Proof.
  intros.
  cut (exists M', store tp M1 l y = Some M').
  intros; simp join.
  eapply store_mono; eauto.
  clear H0.
  unfold mapstoval in *; simp join.
  unfold store in *.
  destruct l.
  eapply ptomvallist_eqlen_storebytes_exists; eauto.
  do 2 rewrite encode_val_length; auto.
Qed.  


Lemma store_exist_join: 
  forall l tp x y M1 M3 M2 M4 M5 M6 M7, 
    mapstoval l tp true  x M1 -> join M1 M3 M2 -> join M4 M2 M5 ->
    join M5 M6 M7  ->
    exists M', store tp M7 l y = Some M'.
Proof.
  intros.
  apply join_comm in H0.
  lets H100 : join_assoc_r H0 H1; mytac.
  apply join_comm in H4.
  lets H100 : join_assoc_l H4 H2; mytac.
  eapply store_exist_join'; eauto.
Qed.


Lemma evaltype_eq_prop : 
  forall G E M1 M2 e t,
    evaltype e (G,E, M1) = Some t ->
    evaltype e (G,E,M2) = Some t.
Proof.
  intros.
  erewrite evaltype_irrev_mem;eauto.
Qed.


Lemma  store_join_map_join :
  forall  Mf x4 x10 Ms x3  b v v' M' x0 x1,
    join x3 Mf x4 ->
    join x10 Ms x3->
    join x0 x1 x10 ->
    mapstoval (b, Int.unsigned Int.zero) Tint32 true v x0 ->
    store Tint32 x4 (b, 0%Z) v' = Some M'->
    exists M1 M2  MM, 
      join M2 Mf M' /\
      join MM Ms M2 /\
      join M1 x1 MM /\
      mapstoval  (b, Int.unsigned Int.zero) Tint32 true v' M1.
Proof.   
    introv Hj1 Hj2 Hj3 Hmp Hs.
    lets Hsd : join_assoc_l Hj3 Hj2.
    mytac.
    lets Hsd : join_assoc_l H0 Hj1.
    mytac.
    assert(join x0 (merge (merge x1 Ms) Mf) x4).

    apply join_comm.
    apply join_comm in H2.
    eapply mem_join_merge_merge; eauto.

    lets Has : store_mapstoval_frame1 Hmp H3 Hs. 
    mytac. 
    exists x5 (merge (merge x5 x1) Ms) (merge x5 x1).
    splits; auto.

    apply join_comm.
    eapply mem_merge_assoc2.
    eauto.
    apply join_comm in H0.
    eapply H0.
    eauto.
    auto.

    eapply mem_merge_join.
    eauto.
    apply join_comm in H0.
    eapply H0; eauto.
    eauto.
    eauto.
    apply join_merge_disj.
    apply disj_sym.
    eapply join_merge_disjoint.
    eauto.
    apply join_comm in H0; eapply H0.
    eauto.
    eauto.
Qed.

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
  lets Hrs : IHj Hsat.
  sep cancel 1%nat 1%nat.
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
  trysimplsall.
  assert (S i = S (i+0)) by omega.
  rewrite <- H in Hsat.
  auto.
  introv Hsat.
  trysimplsall.
  assert (S (i + S j) = S (S i + j)) by omega.
  sep cancel 1%nat 1%nat.
  rewrite H in *.
  lets Hrs : IHj Hsat.
  sep auto.
Qed.



Lemma starinv_prop2:
  forall  i j I,
    (starinv_isr I 0 i)%nat **(starinv_isr I (S i) (S j)) ==>
                       (starinv_isr I 0 (S i))%nat ** (starinv_isr I (S (S i)) j).
Proof.
  destruct  i.
  introv Hj.
  trysimplsall.
  sep auto.
  introv Hsat.
  trysimplsall.
  sep cancel 1%nat 1%nat.
  sep cancel 3%nat 3%nat.
  assert (S (S i) = S (1 + i)) by omega.
  rewrite H in Hsat.
  apply  starinv_prop1_rev in Hsat.
  auto.
Qed.


Lemma starinv_prop : 
  forall I i j, i <= j ->  
                starinv_isr I 0 (S j) ==>  
                            starinv_isr I 0 i ** starinv_isr I (S i) (S j - S i).
Proof.
  introv Hij.
  inductions i.
  introv Hsat.
  trysimplsall.
  assert (j-0 = j) by omega.
  rewrite H.
  sep auto.
  assert (i <= j) by omega.
  introv Hsat.
  lets Hres : IHi H Hsat.
  assert (exists m, S j - S i = S m).
  destruct j.
  inverts Hij.
  exists (j - i). omega.
  destruct H0 as (k & Heqk).
  rewrite Heqk in Hres.
  assert ((S j - S (S i) =k)) by omega.
  rewrite H0.
  eapply starinv_prop2;eauto.
Qed.

Lemma inv_destr :
  forall i n I, i < n ->  
                invlth_isr I 0 n ==>
                           ((invlth_isr I 0 i) ** (invlth_isr I (S i) n)).
Proof.
  introv Hn.
  introv Hsat.
  unfold invlth_isr in *.
  assert (exists j, n =  S j).
  destruct n.
  inverts Hn.
  eexists; eauto.
  destruct H as (j & Hj).
  assert (n - 0 = n) by omega.
  rewrite H in Hsat.
  rewrite Hj in Hsat.
  rewrite Hj.
  assert (i -0 = i) by omega.
  rewrite H0.
  eapply starinv_prop;eauto.
  omega.
Qed.

Lemma inv_isr_prop : 
  forall j i G E M isr ie is cs O aop  I ,
    (G,E,M,isr,(ie,is,cs),O,aop) |= starinv_isr I i j -> 
    forall E' ie' cs' aop',    
      (G,E',M,isr,(ie',is,cs'),O,aop') |=starinv_isr I i j.
Proof.
  inductions j.
  introv  Hsat.
  introv.
  simpl  starinv_isr  in *;mytac.
  destruct Hsat;mytac.
  destruct H; mytac.
  exists isr.
  left.
  destruct H;mytac.
  simpl in H;mytac.
  simpl in H0;mytac.
  split; simpl; mytac; auto.
  destruct H; mytac.
  trysimplsall.
  destruct H3; mytac.
  simpl in H; mytac.
  simpl in H1; mytac.
  exists x.
  right.
  exists empmem M M empabst O O.
  splits;mytac.
  simpl; auto.
  simpl; auto.
  trysimplsall.
  splits; mytac. auto.
  unfolds; auto.
  splits; unfolds; auto.
  trysimplsall; auto.
  unfolds; auto.
  splits; unfolds; auto.
  simpl.
  eapply good_inv_prop; eauto.
  eapply (invp (I i)).
  introv Hsat.
  introv.
  simpl starinv_isr in *; mytac.
  destruct Hsat; mytac.
  trysimplsall.
  destruct H3; mytac.
  destruct H; mytac.
  destruct H; mytac.
  simpl in H1; mytac.
  simpl in H; mytac.
  exists empmem M M empabst O O.
  trysimplsall.
  splits; mytac; auto.
  exists x1.
  left.
  splits; mytac; simpl; try unfolds; auto.
  splits; auto.
  unfolds ; auto.
  splits; auto.
  unfolds; auto.
  eapply IHj; eauto.
  destruct H; mytac.
  trysimplsall.
  destruct H6; mytac.
  simpl in H3; mytac.
  simpl in H; mytac.
  exists x x0 M x2 x3 O.
  splits; mytac; trysimplsall; try auto.
  exists x1.
  right.
  exists empmem x x empabst x2 x2.
  trysimplsall; splits; mytac; auto.
  splits; simpl; auto.
  splits; auto.
  unfolds; auto.
  splits; auto.
  unfolds; auto.
  eapply good_inv_prop; eauto.
  eapply (invp (I i)).
  eapply IHj; eauto.
Qed.

Lemma starinv_isr_elim1 : forall  j i  I, 
                            ((starinv_isr I 0 i)%nat ** (starinv_isr I (S i) j))
                              ==>  (starinv_isr I 0 (S( i + j)))%nat.
Proof.                                            
  inductions j.  
  introv Hsat.
  apply  starinv_prop1_rev in Hsat.
  replace (S (i+0)) with (S i) by omega.
  auto.
  introv Hsat.
  replace ((S (i + S j))) with (S (S i +  j)) by omega.
  apply IHj.
  apply starinv_prop2.
  auto.
Qed.

Lemma nat_exists : 
  forall (i j:nat), (i < j)%nat -> exists k, j = S k.
Proof.
  introv Hij.
  destruct j.
  inverts Hij.
  exists j; auto.
Qed.


Lemma Zle_imply_natle :  
  forall n i,(0  <= Int.intval i)%Z ->  (Int.intval i  < Z.of_nat n)%Z -> (Z.to_nat (Int.intval i)  < n)%nat.
Proof.
  intros.
  replace n with (Z.to_nat (Z.of_nat n)).
  2 : apply Nat2Z.id.
  apply Z2Nat.inj_lt; auto.
  apply Zle_0_nat.
Qed.



Lemma beq_nat_false : forall i, beq_nat i (S i) = false.
Proof.
  induction i; intros; simpl in *; auto.
Qed.

Lemma beq_nat_false2 : forall i j , beq_nat i (S (S (i+j))) = false.
Proof.
  intros.
  replace (S (S (i + j))) with (i + S (S j))%nat.
  2 : omega.
  induction i; simpl; auto.
Qed.


Lemma starinv_isr_prop4 :
  forall j i G E M isr aux O aop  I, 
    (G,E,M,isr,aux,O,aop) |=  starinv_isr I (S i) j -> 
    (G,E,M,(isrupd isr i false),aux,O,aop) |=  starinv_isr I (S i) j.
Proof.
  inductions j.
  simpl   starinv_isr in *.
  introv Hdat.
  destruct Hdat;mytac.  
  destruct H;mytac.
  destruct H;mytac.
  simpl in H;simpl in H0;mytac.
  exists ( isrupd x i false).
  left.  
  splits; simpl;mytac.
  unfolds.
  rewrite   beq_nat_false. 
  auto.
  destruct H;mytac.
  trysimplsall.
  destruct H3;mytac.
  simpl in H; simpl in H1;mytac.
  exists ( isrupd x i false).  
  right.
  exists (empmem:mem) M M (empabst:osabst) O O.
  trysimplsall.
  splits; mytac;eauto.
  splits;simpl;mytac;eauto.
  unfolds.
  rewrite  beq_nat_false;auto.
  destruct (prec (I (S i))) as [Hi Hj].
  destruct Hj as [Hj _].

  lets Hrs : Hj H4.
  simpl set_isr_s in Hrs.
  apply Hrs. 
  introv Hsat.
  eapply starinv_prop1_rev.
  apply starinv_prop1 in Hsat.
  destruct Hsat;mytac.
  trysimplsall.  
  destruct H4;mytac.
  destruct H;mytac.
  exists x x0 M x2 x3 O.
  trysimplsall.
  splits; mytac;eauto.
  destruct H;mytac.
  simpl in H;simpl in H1; mytac.
  exists (isrupd x1 i false).
  left.
  simpl;splits;mytac.  
  unfolds.
  rewrite   beq_nat_false2. 
  auto.
  exists x x0 M x2 x3 O.
  trysimplsall.
  splits; mytac;eauto.
  destruct H;mytac.
  trysimplsall.
  destruct H6;mytac.
  simpl in H;simpl in H4; mytac.
  lets Hs : IHj  H3.
  exists (isrupd x1 i false).
  right.  
  exists (empmem:mem) x0 x0 (empabst:osabst) x3 x3. 
  trysimplsall; splits; mytac; eauto.
  splits; simpl; mytac; eauto.
  unfolds.
  rewrite   beq_nat_false2. 
  auto.
  destruct (prec (I (S (S (i + j))))) as [Hi Hj].
  destruct Hj as [Hj _].
  
  lets Hrs : Hj H7.
  simpl set_isr_s in Hrs.
  apply Hrs. 
Qed.

Lemma beq_nat_false3 : forall i j,  beq_nat (S (S (i + j))) (S i) = false.
Proof.
  intros.
  replace (S (S (i + j))) with ((S i) + (S j))%nat.
  2 : omega.
  remember (S i) as i'; clear.
  induction i'; simpl; auto.
Qed.



Lemma starinv_isr_prop5 :
  (forall  i j G E M isr aux O aop  I, 
     (G,E,M,isr,aux,O,aop) |=  starinv_isr I 0 i -> 
     (G,E,M,(isrupd isr (S (i + j)) false),aux,O,aop) |=  starinv_isr I 0 i)%nat.
Proof.
  inductions i.
  simpl   starinv_isr in *.
  introv Hdat.
  destruct Hdat;mytac.  
  destruct H;mytac.
  destruct H;mytac.
  simpl in H;simpl in H0;mytac.
  exists ( isrupd x (S (0 + j)) false)%nat.
  left.  
  splits; simpl;mytac.
  unfolds.
  simpl.
  auto.
  destruct H;mytac.
  trysimplsall.
  destruct H3;mytac.
  simpl in H; simpl in H1;mytac.
  exists ( isrupd x (S (0 + j)) false)%nat.  
  right.
  exists (empmem:mem) M M (empabst:osabst) O O.
  trysimplsall.
  splits; mytac;eauto.
  splits;simpl;mytac;eauto.
  destruct (prec (I 0%nat)) as [Hi Hj].
  destruct Hj as [Hj _].
  lets Hrs : Hj H4.
  simpl set_isr_s in Hrs.
  apply Hrs. 
  introv Hsat.
  eapply starinv_prop1_rev.
  apply starinv_prop1 in Hsat.
  destruct Hsat;mytac.
  trysimplsall.  
  destruct H4;mytac.
  destruct H;mytac.
  exists x x0 M x2 x3 O.
  trysimplsall.
  splits; mytac;eauto.
  destruct H;mytac.
  simpl in H;simpl in H1; mytac.
  replace ((S (S (i + j)))) with (S (i + S j)) by omega.
  eapply IHi;eauto.
  destruct H; mytac.
  simpl in H; simpl in H1; mytac.
  exists ( isrupd x1 (S (S (i + j))) false).
  left.
  simpl;splits;mytac.  
  unfolds.
  rewrite   beq_nat_false3. 
  auto.
  exists x x0 M x2 x3 O.
  trysimplsall.
  splits; mytac;eauto.
  destruct H;mytac.
  trysimplsall.
  destruct H6;mytac.
  simpl in H;simpl in H4; mytac.
  replace ((S (S (i + j)))) with (S (i + S j)) by omega.
  eapply IHi; eauto.
  exists ( isrupd isr (S (S (i + j))) false).
  right.
  destruct H; mytac.  
  simpl in H6;mytac.
  exists (empmem:mem) x0 x0 (empabst:osabst) x3 x3. 
  trysimplsall; splits; mytac; eauto.
  splits; simpl; mytac; eauto.
  unfolds.
  rewrite   beq_nat_false3. 
  auto.
  destruct (prec (I (S i))) as [Hi Hj].
  destruct Hj as [Hj _].
  lets Hrs : Hj H7.
  simpl set_isr_s in Hrs.
  apply Hrs. 
Qed.

Lemma starinv_prop2_rev:
  forall  i j I,
    (starinv_isr I 0 (S i))%nat ** (starinv_isr I (S (S i)) j)==>
                           (starinv_isr I 0 i)%nat **(starinv_isr I (S i) (S j)).
Proof.
  destruct  i.
  introv Hj.
  trysimplsall.
  sep auto.
  introv Hsat.
  trysimplsall.
  sep cancel 1%nat 1%nat.
  assert (S (S i) = S (1 + i)) by omega.
  sep cancel 3%nat 3%nat.
  rewrite H . 
  apply  starinv_prop1 in Hsat.
  auto.
Qed.



Lemma  starinv_isr_prop_intro2 : forall I i j,   
                                   starinv_isr I 0%nat (S j + S i)%nat ==> 
                                               starinv_isr I 0%nat (S j) ** starinv_isr I (S (S j)) i.
  inductions i.
  introv Hsat.
  trysimplsall.
  sep cancel 1%nat 1%nat.
  replace (j+1)%nat with (S j) in Hsat by omega.
  apply starinv_prop1 in Hsat.
  sep auto.
  introv Hsat.
  replace (S j + S (S i))%nat with (S (S j) +  (S i))%nat in Hsat by omega.
  apply IHi in Hsat.
  apply starinv_prop2_rev in Hsat.
  auto.
Qed.



Lemma  starinv_isr_prop_intro3 :
  forall I i j, (starinv_isr I 0 (S j + S i))%nat ==>  (starinv_isr I 0 j)%nat ** 
                                             (starinv_isr I (S j) 0)%nat ** (starinv_isr I (S (S j)) i).
Proof.
  introv Hsat.
  apply  starinv_isr_prop_intro2  in Hsat.
  sep cancel 2%nat 3%nat.
  apply starinv_prop1.
  auto.
Qed.



Lemma sm_nat_exist: forall (i j:nat), (S i < j)%nat -> exists k, j = S (S k).
Proof.
  introv Hji.
  destruct j.
  inverts Hji.
  destruct j.
  inverts Hji.
  inverts H0.
  exists j.
  auto.
Qed.


Lemma  starinv_isr_prop_rev :(forall I i j,    
                                starinv_isr I 0 (S j) ** starinv_isr I (S (S j)) i ==> starinv_isr I 0 (S j + S i))%nat.
  inductions i.
  introv Hsat.
  trysimplsall.
  sep cancel 1%nat 1%nat.
  replace (j+1)%nat with (S j)  by omega.
  apply starinv_prop1_rev.
  sep auto.
  introv Hsat.
  replace (S j + S (S i))%nat with (S (S j) +  (S i))%nat  by omega.
  apply IHi.
  apply starinv_prop2 in Hsat.
  auto.
Qed.


Lemma  starinv_isr_prop_elim :
  forall I i j, (starinv_isr I 0 j)%nat ** 
                                   (starinv_isr I (S j) 0)%nat ** (starinv_isr I (S (S j)) i) ==>   (starinv_isr I 0 (S j + S i))%nat.
Proof.
  introv Hsat.
  apply  starinv_isr_prop_rev.
  sep auto.
  apply starinv_prop1_rev.
  auto.
Qed.


Lemma list_rev_prop :  
  forall (A:Type)(t : A) (tl: list A), t :: tl = rev (rev tl ++ t :: nil).
Proof.
  intros.
  rewrite rev_app_distr.
  simpl.
  rewrite rev_involutive.
  auto.
Qed.

Inductive evalexprlist' : exprlist -> typelist -> vallist -> smem ->  Prop :=
|  evalexprlist_b :  forall m,  evalexprlist' nil nil nil m
|  evalexprlist_i : forall e el t tl v vl  m, 
                      v <> Vundef -> 
                      evalval e m = Some v -> 
                      evaltype e m = Some t ->  
                      evalexprlist' el tl vl m -> 
                      evalexprlist' (cons e  el) (cons t  tl) (cons v  vl) m . 

Lemma evalexprlist_imply_evalexprlist' : 
  forall el tl vl m ,
    evalexprlist el tl vl m -> 
    evalexprlist' el tl vl m.
Proof.
  inductions el; introv Heval; destruct tl ; destruct vl; tryfalse.
  constructors.
  simpl in Heval.
  destruct Heval as (Hev & Het &  Hexpr & Hnv).
  constructors; eauto.
Qed.

Lemma evalexprlist'_imply_evalexprlist :
  forall el tl vl m ,
    evalexprlist' el tl vl m -> 
    evalexprlist el tl vl m.
Proof.
  inductions el; introv Heval; destruct tl ; destruct vl; 
  auto; inverts Heval;  tryfalse.
  simpl ; auto.
  simpl.
  splits; auto.
Qed.

Lemma aux_for_tl_vl_match_rev: 
  forall tl vl tl' vl', 
    tl_vl_match tl vl =true -> 
    tl_vl_match tl'  vl' =true -> 
    tl_vl_match (tl++tl') (vl++vl')=true. 
Proof.
  inductions tl;intros.
  simpl in H.
  destruct vl;tryfalse.
  simpl.
  auto.
  destruct vl;tryfalse.
  simpl in H.
  remember (type_val_match a v )as X.
  destruct X;tryfalse.
  simpl.
  rewrite <- HeqX.
  apply IHtl;auto.
Qed.



Lemma tl_vl_match_rev:
  forall vl tl,tl_vl_match tl vl =true -> tl_vl_match (rev tl) (rev vl) =true.
Proof.
  intros.
  generalize dependent vl.
  induction tl;intros.
  simpl in H.
  destruct vl;simpl in H;tryfalse.
  simpl;auto.
  simpl in H.
  destruct vl;simpl in H;tryfalse.
  simpl.
  remember (type_val_match a v) as X;destruct X;tryfalse.
  apply IHtl in H.

  apply aux_for_tl_vl_match_rev;auto.
  simpl.
  rewrite <-HeqX;auto.
Qed.

Lemma  evaladdr_mono:  
  forall e M1 M2 M v ge le,
    join M1 M2 M -> 
    evaladdr e (ge, le, M1) = Some v ->
    evaladdr e (ge,le,M)= Some v.
Proof.
  intros.
  generalize (evalvaladdr_mono ge le e M1 M2 M v).
  intros. destruct H1.
  erewrite H2;eauto.
Qed.


Lemma store_exists_fcall:
  forall tp M0 l v0 M' M11 M31 M2 Mm1 Mm ge le isr aux  O'' aop  p 
         (vl : vallist) Ms1  Md Mf0 (post:fpost) x O (logicl:list logicvar) tt,
    store tp M0 l v0 = Some M' ->  
    mapstoval l tp true x M11 -> 
    join M11 M31 M2 -> 
    join Mm1 M2 Mm -> 
    (ge, le, Mm1, isr, aux, O'', aop) |= POST  [post, rev vl, Some v0, logicl,tt] -> 
    join Mm Ms1 Md -> 
    join Md Mf0 M0 -> 
    (ge, le, M31, isr, aux, O, aop) |= p -> 
    exists M11' M2' Mm' Md',  
      mapstoval l tp true v0 M11' /\ 
      join M11' M31 M2'/\  
      join Mm1 M2' Mm' /\ 
      join Mm' Ms1 Md' /\  
      join Md' Mf0  M'.
Proof.
  intros.
  gen H H0 H1 H2 H4 H5; clear; intros.
  apply join_comm in H1.
  lets H100 : join_assoc_r H1 H2; mytac.
  apply join_comm in H6.
  lets H100 : join_assoc_l H6 H4; mytac.
  lets H100 : join_assoc_l H8 H5; mytac.
  lets H100 : store_mapstoval_frame1 H0 H10 H; mytac.
  lets H100 : join_assoc_r H9 H13; mytac.
  lets H100 : join_assoc_r H7 H14; mytac.
  apply join_comm in H3.
  lets H100 : join_assoc_r H3 H16; mytac.
  do 4 eexists; mytac; eauto.
  apply join_comm; auto.
Qed.


Definition n_dym_com_s (s:stmts):=
  match s with
    | sif e s1 s2 => GoodStmt' s1 /\ GoodStmt' s2
    | sifthen e s => GoodStmt' s
    | sseq s1 s2 => GoodStmt' s1 /\ GoodStmt' s2
    | swhile e s =>GoodStmt' s
    | hapi_code _ => False
    | _ => True
  end.   

Definition n_dym_com_ceval (c:cureval):=
  match c with
    | cure e => True
    | curs s => n_dym_com_s s
  end.

Fixpoint n_dym_com_int_scont (ks:stmtcont):=
  match ks with
    | kstop => True
    | kseq s ks' => GoodStmt' s/\ n_dym_com_int_scont ks'
    | kcall f s le ks' => GoodStmt' s /\ n_dym_com_int_scont ks'
    | kint _ _ _ _ => False
    | kassignr _ _ ks' => n_dym_com_int_scont ks'
    | kassignl _ _ ks' => n_dym_com_int_scont ks'
    | kfuneval _ _ _ _ ks' => n_dym_com_int_scont ks'
    | kif s1 s2 ks' => GoodStmt' s1 /\ GoodStmt' s2 /\ n_dym_com_int_scont ks'
    | kwhile e s ks' =>  GoodStmt' s /\ n_dym_com_int_scont ks'
    | kret ks' =>  n_dym_com_int_scont ks'
    | kevent _ _ _ => False
  end.

Definition n_dym_com_int_cd (C:code):=
  match C with
    | (c,(ke,ks)) => n_dym_com_ceval c/\ n_dym_com_int_scont ks
  end.


Definition isfree (C:code)  := 
  exists ls v ks, C = (curs (sfree ls v), (kenil,ks)).

Definition isalloc (C:code)  :=
  exists vl dl ks, C = (curs (salloc vl dl), (kenil, ks)) .

Definition nci (C:code) := 
  exists s ke ks, C = (s, (ke,ks)) /\ callcont ks = None /\ intcont ks = None.

Lemma  n_dym_com_int_scont_callcont :
  forall ks ks' f s le',
    callcont ks = Some (kcall f s le' ks') -> n_dym_com_int_scont ks ->
    n_dym_com_int_scont ks'.
Proof.
  intros.
  induction ks;
    try solve [apply IHks; auto];
    try solve [simpl in H; inv H];
    try solve [simpl in H; simpl in H0; destruct H0; apply (IHks H H1)];
    try solve [simpl in H; inverts H; simpl in H0; destruct H0; auto].
  apply IHks.
  simpl in H.
  auto.
  simpl in H0.
  destruct H0.
  destruct H1.
  auto.
Qed.

Lemma n_dym_com_int_scont_intcont_n_dym_com_int_cd :
  forall ks (ks':stmtcont) ke ks' le' c,
    n_dym_com_int_scont ks -> intcont ks = Some (kint c ke le' ks') -> n_dym_com_int_cd (c, (ke, ks')).
Proof.
  inductions ks; intros; simpl in H0; tryfalse;
  try solve [simpl in H; destruct H; eapply IHks; eauto];
  try solve [simpl in H; eapply IHks; eauto].
  simpl in H.
  destruct H.
  destruct H1.
  eapply IHks; eauto.
Qed.



Lemma loststep_good_code_prop :
  forall p C o C' o', loststep p C o C' o' ->
                      ~ IsFcall C  ->   n_dym_com_int_cd C ->  n_dym_com_int_cd C'.
Proof.
  intros.
  inverts H; auto.
  inverts H2.
  inverts H3; auto.
  inverts H3; simpl in H1; simpl; auto;
  try solve [destruct H1; destruct H1; destruct s; simpl; auto];
  try solve [destruct H1; destruct H; destruct s1; simpl; auto].
  false.
  apply H0.
  unfold IsFcall.
  eauto.
  split; auto.
  destruct H1; clear H.
  eapply n_dym_com_int_scont_callcont.
  apply H4.
  auto.
  destruct H1.
  auto.
  destruct H1.
  destruct H2.
  destruct H3.
  split; auto.
  destruct s1; simpl; auto.
  split; auto.
  destruct H.
  destruct H1.
  destruct H1.
  destruct H2.
  destruct s2; simpl; auto.
  destruct H.
  destruct H1.
  destruct H1.
  destruct H2.
  destruct s2; simpl; auto.
  split; auto.
  destruct H.
  destruct H1.
  destruct H1.
  destruct s; simpl; auto.
  split; auto.
  destruct H1.
  destruct H2.
  destruct s; simpl; auto.
  destruct H1.
  destruct H2.
  auto.
  split;auto.
  destruct H1.
  destruct H2.
  auto.
  simpl in H1.
  destruct H1.
  eapply n_dym_com_int_scont_intcont_n_dym_com_int_cd; eauto.
Qed.

Lemma loststep_code_prop: forall p C o C' o' , 
                            loststep p C o C' o' -> ~ IsFcall C /\
                                                    ~ isalloc C /\ ~ isfree C /\ nci C /\  n_dym_com_int_cd C ->  
                            ~ isalloc C' /\ ~ isfree C' /\ nci C' /\  n_dym_com_int_cd C'.
Proof.
  intros.
  splits.
  destruct H0.
  destruct H1.
  destruct H2.
  destruct H3.
  introv Hf.
  unfolds in Hf.
  destruct Hf as (vl & dl & ks & Hc).
  subst C'.
  invertstep idtac.
  apply H0.
  do 3 eexists; eauto.
  apply H1.
  do 3 eexists; eauto.
  apply H1.
  do 3 eexists; eauto.
  unfolds in H3.
  destruct H3 as (ss & ke&ks&Hse & Hcal).
  inverts Hse.
  simpl in Hcal.  destruct Hcal. tryfalse.
  simpl in H4.
  destruct H4.
  destruct H; tryfalse.
  simpl in H4; destruct H4.   destruct H4; tryfalse.
  simpl in H4; destruct H4.   destruct H4; tryfalse.
  simpl in H4; destruct H4.   destruct H4; tryfalse.
  simpl in H4; destruct H4.   destruct H4; tryfalse.
  destruct H5; tryfalse.
  simpl in H4; destruct H4.   destruct H4; tryfalse.
  unfolds in H3.   destruct  H3 as (H31 & H32 & H33 & H34 & H35 & H36).
  inverts H34.
  tryfalse.
  introv Hf.
  unfolds in Hf.
  destruct Hf as (ls & v& ks & Hc).
  subst C'.
  simp join.
  invertstep idtac.
  destruct  H3 as (H31 & H32 & H33 & H34 & H35 & H36).
  inverts H34. 
  simpl in H35; tryfalse.
  destruct  H3 as (H31 & H32 & H33 & H34 & H35 & H36).
  inverts H34. 
  simpl in H35; tryfalse.
  destruct  H3 as (H31 & H32 & H33 & H34 & H35 & H36).
  inverts H34. 
  simpl in H35; tryfalse.
  apply H2; do 3 eexists; eauto.
  simpl in H4.
  simp join; tryfalse.
  simpl  in H4; simp join; tryfalse.
  simpl in H4; simp join; tryfalse.
  simpl  in H4; simp join; tryfalse.
  simpl in H4; simp join; tryfalse.
  simpl  in H4; simp join; tryfalse.
  simpl in H4; simp join; tryfalse.
  destruct  H3 as (H31 & H32 & H33 & H34 & H35 & H36).
  inverts H34. 
  simpl in H35; tryfalse.
  simp join.
  destruct H3 as (s&ke&ks& He1 & He2 & He3).
  subst C.
  invertstep idtac; try (do 3 eexists; splits; eauto); tryfalse.
  false. apply H0.
  do 4 eexists;   eauto.
  eapply  loststep_good_code_prop ; intuition eauto.
Qed.

Lemma  loststep_eqenv : 
  forall p C o C' o' , 
    loststep p C o C' o' -> ~ IsFcall C ->
    ~ isalloc C /\ ~ isfree C /\ nci C /\  n_dym_com_int_cd C ->  eqenv o o'.
Proof.
  intros.
  simp join.
  destruct o as [[[[]]]].
  destruct o' as [[[[]]]].
  unfolds.
  invertstep auto; split; auto.
  false.
  apply H0.
  do 4 eexists; eauto.
  false.
  apply H1.
  do 4 eexists; eauto.
  false.
  apply H1.
  do 4 eexists; eauto.
  false.
  apply H2.
  do 3 eexists; eauto.
  destruct H3 as (s&kee&kss&He1 & He2&He3).
  inverts He1.
  tryfalse.
Qed.

Lemma goodfrm_prop : 
  forall p m isr aux O aop ,  
    GoodFrm p -> 
    sat ((m,isr,aux),O,aop) p -> 
    forall isr' aux' aop',  sat ((m,isr',aux'),O,aop') p.
Proof.
  inductions p; intros; intuition eauto; tryfalse.
  destruct H.
  destruct H0.
  split.  
  lets Hres :  IHp1 H H0.
  auto.
  lets Hres :  IHp2 H1 H2.
  auto.
  simpl in H.
  destruct H.
  destruct H0.
  left.
  lets Hres : IHp1 H H0.
  auto.
  right.
  lets Hres : IHp2 H1 H0. auto.
  simpl in H.
  destruct H.
  destruct H0.
  simp join.
  destruct m as [[G E] M].
  simpl substmo  in *.
  simpl getabst in  *.
  simpl getmem in *.
  exists x x0 M x2 x3 O.
  simpl.
  splits; eauto.
  destruct H1.
  simpl in H0.
  lets Hres : H0 x .
  lets Hss : H x  Hres H1.
  eexists.   
  auto.
Qed.


Lemma eqenv_goodg_sat :
  forall o O gamma M Of frm oo O'' gam ,
    eqenv oo o -> 
    GoodFrm frm -> 
    substmo (o, O, gamma) M Of |= frm ->  substmo (oo, O'', gam) M Of |= frm.
Proof.
  intros.
  destruct o as [[[[]]]].
  destruct oo as [[[[]]]].
  simpl substmo in  *.  
  destruct H.
  subst.
  eapply  goodfrm_prop; eauto.
Qed.

Lemma eqenv_trans : 
  forall o o' o'', eqenv o o' -> eqenv o' o'' -> eqenv o o''.
Proof.
  intros.
  destruct o as [ [ [ [ ] ] ] ]; simpl.
  destruct o' as [ [ [ [ ] ] ] ]; simpl.
  destruct o'' as [ [ [ [ ] ] ] ]; simpl.
  unfold eqenv in *; join auto.
Qed.

Lemma eqenv_comm: forall o o', eqenv o o' -> eqenv o' o.
  intros.
  destruct o as [ [ [ [ ] ] ] ]; simpl.
  destruct o' as [ [ [ [ ] ] ] ]; simpl.
  unfold eqenv in *; join auto.
Qed.


Lemma GoodStmt_ndym:
  forall s , GoodStmt' s -> n_dym_com_s s. 
Proof.
  inductions s;intros; eauto; try simpl in *; tryfalse.
Qed.

Lemma local_inv_irev_prop:
  forall G E M isr aux O aop li t,
    (G,E,M,isr,aux, O, aop) |= CurLINV li t ->
    forall E' aop',  (G,E',M,isr,aux, O, aop') |= CurLINV li t.
Proof.
  intros.
  unfold CurLINV in *.
  destruct H.
  exists x.
  simpl sat in H; simpljoin.
  simpl sat.
  do 6 eexists.
  splits; eauto.
  do 8 eexists.
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  clear - H13 H14.
  eapply GoodLInvAsrt_irrel; eauto.
Qed.

Lemma  joinmem_frm_asrt_hold:
  forall  M o' Ol' Of Ok gam q frm gamma o O,
    GoodFrm frm ->
    joinmem o M o' ->
    join Ol' Of Ok ->
    substmo (o, O, gamma) M Of |= frm ->
    (o, Ol', gam) |= q ->
    (o', Ok, gam) |= q ** frm.
Proof.
  intros.
  destruct o as [[[[]]]].
  simpl in *.
  unfold joinmem in *.
  simp join.
  simpl.
  exists x1 M x2 Ol' Of Ok.
  splits; auto.
  eapply  goodfrm_prop; eauto.
Qed.

Lemma notabortm_if : 
  forall e s1 s2,    notabortm (curs (sif e s1 s2), (kenil, kstop)).
Proof.
  intros.
  unfold notabortm.
  split.
  introv Hf; 
    match goal with
      | H : ?P _ |- _ => unfold P in H; simp join; tryfalse
    end.
  unfold notabort.
  splits;
    introv Hf; 
    match goal with
      | H : ?P _ |- _ => unfold P in H; simp join; tryfalse
    end.
Qed.


Lemma notabortm_if_v :  
  forall v s1 s2,    notabortm (curs(sskip (Some v)),(kenil, kif s1 s2 kstop)).
Proof.
  intros.
  unfold notabortm.
  split.
  introv Hf; 
    match goal with
      | H : ?P _ |- _ => unfold P in H; simp join; tryfalse
    end.
  unfold notabort.
  splits;
    introv Hf; 
    match goal with
      | H : ?P _ |- _ => unfold P in H; simp join; tryfalse
    end.
Qed.



Lemma addstmts_not_eqkstop : 
  forall s ks,  AddStmtToKs s ks <> kstop.
Proof.
  intros.
  destruct ks; simpl; try discriminate.
Qed.

Lemma notabort_sseq:
  forall s1 s2, notabortm (curs (sseq s1 s2), (kenil, kstop)). 
Proof.
  intros.
  unfold notabortm.
  split. 
  introv Hf.
  match goal with
    | H : ?P _ |- _ => unfold P in H; simp join; tryfalse
  end.
  splits; 
    introv Hf;
    match goal with
      | H : ?P _ |- _ => unfold P in H; simp join; tryfalse
    end.
Qed.

Lemma get_env_eq : 
  forall G o M1  M2 o2 o' M1'  M2' o2',
    G = get_genv (get_smem o) -> 
    joinm2  o M1  M2 o2 -> 
    get_genv (get_smem o2)  =  get_genv (get_smem o2') ->
    joinm2  o' M1'  M2' o2' ->
    G = get_genv (get_smem o').
Proof.           
  intros.
  unfold joinm2 in *.
  unfold joinmem in *.
  join auto.
Qed.

Lemma swinv_aop_irev:
  forall o O aop t I,
    (o, O, aop) |= SWINVt I t ->
    satp o O (SWINVt I t).
Proof.
  intros.
  unfold satp; intro.
  unfold SWINVt in *.
  destruct o; destruct p; destruct s; destruct p.
  simpl in H; simpljoin.
  destruct l.
  destruct p.
  simpl.
  do 6 eexists.
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.

  eexists.
  splits; eauto. 
  do 7 eexists; splits; eauto.
  eapply inv_isr_irrev_prop.
  rewrite Nat.sub_0_r.
  rewrite Nat.add_0_r.
  unfold invlth_isr in H23; rewrite Nat.sub_0_r in H23; eauto.

  do 8 eexists; splits; eauto.
Qed.


Lemma swpre_aop_irev:
  forall o O aop t  sd  x,
    (o, O, aop) |= SWPRE sd x t  ->
    satp o O ( SWPRE sd x t ).
Proof.
  intros.
  unfold satp; intros.
  unfold SWPRE in *.
  destruct H.
  exists x0.
  destruct o as [[[[]]]].
  simpl in H; simpljoin.
  simpl.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  eexists; splits; eauto.

  do 6 eexists; splits; eauto.
  do 8 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  do 8 eexists; splits; eauto.
Qed.


Lemma linv_aop_irev:
  forall o O aop aop' li t lg,
    (o,O,aop) |= LINV li t lg ** Atrue ->
    (o,O,aop') |= LINV li t lg ** Atrue.
Proof.
  intros.
  destruct o as [[[[]]]].
  simpl in H; simpljoin.
  simpl.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  pose proof H9 t lg.
  eapply GoodLocalInvAsrt_aop_irev; eauto.
  destruct H;auto.
Qed.


Lemma joinmem_swinv_linv:
  forall e e0 x1 i l Mc' o' x4  O'' aop t li lg Oc' I,
    joinmem (e, e0, x1, i, l) Mc' o' ->
    join x4 Oc' O'' -> 
    satp (e, e0, Mc', i, l) Oc' (SWINVt I t) ->
    (e, e0, x1, i, l, x4, aop) |= LINV li t lg ** Atrue ->
    satp o' O'' (CurLINV li t) .
Proof.
  intros.
  unfolds in H; simpljoin.

  unfold satp; unfold CurLINV; intros.
  exists lg.
  pose proof H1 aop0.
  eapply linv_aop_irev with (aop':=aop0) in H2.
  unfold SWINVt in H.
  remember (SWINV I) as xx.
  remember (LINV li t lg) as yy.
  clear Heqxx Heqyy.
  simpl in H2; simpljoin.
  sep lift 2%nat.
  remember (CurTid t ** Atrue).
  simpl.
  exists x1 (merge x7 Mc') x3.
  exists x9 (merge x10 Oc') O''.
  splits; eauto.
  eapply mem_join_join_merge23_join; eauto.

  clear - H0 H6.
  eapply join_merge23; eauto.

  substs.
  unfold CurTid.
  sep lift 2%nat in H.
  simpl in H; simpljoin.
  simpl.
  exists x8 (merge x7 x11); eexists.
  exists x13 (merge x10 x14); eexists.
  splits; eauto.

  eapply join_merge_merge1; eauto.
  apply join_comm in H3; eauto.
  
  eapply join_merge_merge1; eauto.
  apply join_comm in H6; eauto.  
  do 8 eexists; splits; eauto.
Qed.
  
Lemma swdead_aop_irev:
  forall o O aop t  x sd,
    (o, O, aop) |= SWPRE_DEAD sd x  t  ->
    satp o O ( SWPRE_DEAD  sd x t ).
Proof.
  intros.
  unfold SWPRE_DEAD in *.
  destruct H.
  split.
  eapply swpre_aop_irev; eauto.
  destruct o as [[[[]]]].
  destruct H0.
  exists x0.
  auto.
Qed.

Lemma joinsig_idom_neq:
  forall t1 x (tls: TcbMod.map) tls'  t,
    joinsig t1 x  tls tls' ->
    indom tls t -> t <> t1.
Proof.
  intros.
  unfold joinsig in H.
  unfold indom in H0.
  destruct H0.
  intro; substs.
  assert (get tls t1 = None).
  jeat.
  rewrite H0 in H1; tryfalse.
Qed.
    
  
Lemma joinsig_join2_get2:
  forall tls t x9 x2 (x1:osabst) x8 O Os OO,
    join (sig abstcblsid (abstcblist tls)) (sig curtid (oscurt t)) x9 ->
    join x2 x9 x1 ->
    join x1 x8 O ->
    join O Os OO ->
    get OO curtid = Some (oscurt t)  /\   get OO abstcblsid = Some (abstcblist tls).
Proof.
  intros.
  split.
  assert(get x9 curtid = Some (oscurt t)).
  jeat.
  assert(get x1 curtid = Some (oscurt t)).
  jeat.
  assert (get O curtid = Some (oscurt t)).
  jeat.
  jeat.

  assert(get x9 abstcblsid = Some (abstcblist tls)).
  jeat.
  assert(get x1 abstcblsid = Some (abstcblist tls)).
  jeat.
  assert(get O abstcblsid = Some (abstcblist tls)).
  jeat.
  jeat.
Qed.
  

Lemma get_join_set_set:
  forall  tls (O:osabst) Os OO tls',
    get O abstcblsid = Some (abstcblist tls) ->
    join O Os OO ->
    join (set O abstcblsid (abstcblist tls')) Os
         (set OO abstcblsid (abstcblist tls')).
Proof.
  intros.
  apply map_join_set_none; auto.
  jeat.
Qed.

Lemma joinsig_join2_get2':
  forall tls t x9 x2 (x1:osabst) x8 O,
    join (sig abstcblsid (abstcblist tls)) (sig curtid (oscurt t)) x9 ->
    join x2 x9 x1 ->
    join x1 x8 O ->
    get O curtid = Some (oscurt t)  /\   get O abstcblsid = Some (abstcblist tls).
Proof.
  intros.
  split.
  assert(get x9 curtid = Some (oscurt t)).
  jeat.
  assert(get x1 curtid = Some (oscurt t)).
  jeat.
  jeat.

  assert(get x9 abstcblsid = Some (abstcblist tls)).
  jeat.
  assert(get x1 abstcblsid = Some (abstcblist tls)).
  jeat.
  jeat.  
Qed.

Lemma joinsig_join2_get2'':
  forall tls t x9 x2 (x1:osabst) ,
    join (sig abstcblsid (abstcblist tls)) (sig curtid (oscurt t)) x9 ->
    join x2 x9 x1 ->
    get x1 curtid = Some (oscurt t)  /\   get x1 abstcblsid = Some (abstcblist tls).
Proof.
  intros.
  split.
  assert(get x9 curtid = Some (oscurt t)).
  jeat.
  jeat.
  assert(get x9 abstcblsid = Some (abstcblist tls)).
  jeat.
  jeat.
Qed.

Lemma set_join3_join:
  forall OK O tls' x2 b x9 x8 t tls,
    OK = set O abstcblsid (abstcblist tls') -> 
    join x2 b O ->
    join x9 x8 b -> 
    join (sig abstcblsid (abstcblist tls)) (sig curtid (oscurt t)) x9 ->
    join x2 (set b abstcblsid (abstcblist tls')) OK.
Proof.
  intros.
  substs.
  apply join_comm.
  apply map_join_set_none.
  apply join_comm; auto.
  assert (get b abstcblsid = Some (abstcblist tls)).
  assert (get x9 abstcblsid = Some (abstcblist tls)).
  jeat.
  jeat.
  jeat.
Qed.


Lemma good_linvasrt_aop_irev:
  forall o O aop aop' t lg pa,
    GoodLInvAsrt pa ->
    (o,O,aop) |= pa t lg ->
    (o,O,aop') |= pa t lg.
Proof.
  intros.
  pose proof H t lg.
  destruct o as [[[[]]]].
  eapply GoodLocalInvAsrt_aop_irev; eauto.
  destruct H1;auto.
Qed.

Lemma set_join2_join:
  forall OK  tls' x1  x9  t tls x2,
    OK = set x1 abstcblsid (abstcblist tls') -> 
    join x2 x9 x1 ->
    join (sig abstcblsid (abstcblist tls)) (sig curtid (oscurt t)) x9 ->
    join x2 (set x9 abstcblsid (abstcblist tls')) OK.
Proof.
  intros.
  substs.
  apply join_comm.
  apply map_join_set_none.
  apply join_comm; auto.

  assert (get x9 abstcblsid = Some (abstcblist tls)).
  jeat.
  jeat.
Qed.

Lemma join2_sig_join:
  forall x2 x9 x1 tls t tls',
    join x2 x9 x1 ->
    join (sig abstcblsid (abstcblist tls)) (sig curtid (oscurt t)) x9 -> 
    join x2 (set x9 abstcblsid (abstcblist tls'))
         (set x1 abstcblsid (abstcblist tls')) /\   
    join (sig abstcblsid (abstcblist tls')) (sig curtid (oscurt t))
         (set x9 abstcblsid (abstcblist tls')).
Proof.
  intros.
  split.
  apply join_comm.
  apply map_join_set_none.
  apply join_comm; auto.
  
  assert (get x9 abstcblsid = Some (abstcblist tls)).
  jeat.
  jeat.

  eapply joinsig_set; eauto.
Qed.

Lemma join3_ex2:
  forall  tls' Odel O'' tls t x3 x2 O,
    join (set O abstcblsid (abstcblist tls')) Odel O'' ->
    join (sig abstcblsid (abstcblist tls)) (sig curtid (oscurt t)) x3 -> 
    join x2 x3 O -> 
    exists k,  join x2 k O'' /\ join (set x3 abstcblsid (abstcblist tls')) Odel k.
Proof.
  intros.
  assert (get x3 abstcblsid = Some (abstcblist tls)).
  jeat.
  assert (join x2 (set x3 abstcblsid (abstcblist tls')) (set O abstcblsid (abstcblist tls'))).
  apply join_comm.
  eapply join_set_set; eauto.
  apply join_comm; auto.

  exists (merge (set x3 abstcblsid (abstcblist tls')) Odel).
  split.
  assert(join x2 (set x3 abstcblsid (abstcblist tls')) (set O abstcblsid (abstcblist tls'))).
  eapply join_set_r; eauto.
  unfolds; eauto.
  eapply join_merge23; eauto.

  assert(join x2 (set x3 abstcblsid (abstcblist tls')) (set O abstcblsid (abstcblist tls'))).
  eapply join_set_r; eauto.
  unfolds; eauto.
  
  eapply join_join_merge; eauto.
Qed.

  
Lemma join3_get2:
  forall x2 x3  tls t O Os OO,
    join x2 x3 O -> 
    join (sig abstcblsid (abstcblist tls)) (sig curtid (oscurt t)) x3 ->
    join O Os OO ->
    get OO curtid = Some (oscurt t) /\ get OO abstcblsid = Some (abstcblist tls) /\ 
    get O abstcblsid = Some (abstcblist tls).
Proof.
  intros.
  split.
  assert (get x3 curtid = Some (oscurt t)).
  jeat.
  assert (get O curtid = Some (oscurt t)).
  jeat.
  jeat.

  assert (get x3 abstcblsid = Some (abstcblist tls)).
  jeat.
  split.
  assert (get O abstcblsid = Some (abstcblist tls)).
  jeat.
  jeat.
  jeat.
Qed.

Lemma  estepv_notabortm : 
  forall  m v c ke  , 
    estepstar c ke m [v] kenil m ->
    ~ IsFcall (c,(ke,kstop)) /\
    ~ IsSwitch  (c,(ke,kstop)) /\ 
    ~ IsRet  (c,(ke,kstop)) /\ 
    ~ IsRetE  (c,(ke,kstop)) /\ 
    ~ IsIRet (c,(ke,kstop))  /\
    ~IsStkInit(c,(ke,kstop)) /\
    ~IsStkFree(c,(ke,kstop)).
Proof.
  introv He1.
  inductions He1; try solve [
                        splits;introv H; unfolds in H; simp join; tryfalse].
  lets Heq : estep_mem_same H.
  subst m'.
  assert (m = m) as Hasrt; auto.
  lets Hres : IHHe1 Hasrt.
  destruct Hres as (Hf & Hsw & Hisret & Hisre & Hiret).
  splits;
    introv Hfl; unfolds in Hfl; simp join; tryfalse;inverts H.
Qed.

Lemma callcont_kseq_kstop_nonone:
  forall (ks : stmtcont) (e : expr) (s : stmts),
    callcont (ks ## kseq (swhile e s) kstop) <> None ->
    callcont ks <> None.
Proof.
  intros.
  induction ks;auto.
  intro;tryfalse.
Qed.    


Lemma loststep_keq_while_mono :  
forall p c ke ks e s o C o' ,
     loststep p (c, (ke, ks ## kseq (swhile e s) kstop)) o C o' ->
     ~ loststepabt p (c, (ke, ks)) o ->
     exists c' ke' ks' , loststep p (c, (ke, ks)) o (c',(ke',ks')) o' /\
     C = (c',(ke',ks'## kseq (swhile e s) kstop)).
Proof.
  intros.
  unfold loststepabt in H0.
  apply Classical_Prop.NNPP in H0; simp join.
  inverts H.
  inverts H1.
  inverts H.
  do 3 eexists;split;eauto.
  eapply ostc_step; eapply expr_step; eauto; econstructor; eauto.
  inverts H.
  inverts H2;(inverts H0 as Hlo;tryfalse); try solve [
  try (destruct ks ;inverts H);
  try (destruct ks ;inverts H4);
  rewrite_addcont;
  do 3 eexists;split;eauto;constructors;eauto;eapply stmt_step;eauto; constructors;eauto |
  destruct ks;simpl in *;tryfalse;
  [inverts Hlo;inverts H;inverts H1|idtac];
  inverts H0;rewrite_addcont;
  do 3 eexists;split;eauto;constructors;eauto;eapply stmt_step;eauto; constructors;eauto |
  destruct ks;simpl in *;tryfalse;
  [inverts Hlo;inverts H;inverts H0|idtac];
  inverts H4;rewrite_addcont;
  do 3 eexists;split;eauto;constructors;eauto;eapply stmt_step;eauto; constructors;eauto].
  inverts Hlo;inverts H;inverts H0.
  inverts H.
  do 3 eexists;split;eauto;constructors;eauto;eapply stmt_step;eauto; constructors;eauto.
  destruct ks;simpl in *;tryfalse.
  inverts H.
  lets Hcall: callcont_kseq_kstop_nonone H3.
  do 3 eexists;split;eauto;constructors;eauto;eapply stmt_step;eauto; constructors;eauto.
  inverts Hlo;inverts H;inverts H0.
  inverts H1;rewrite_addcont.
  lets Hcall: callcont_some_addcont (kseq (swhile e s) kstop) H5.
  rewrite Hcall in H3. inverts H3.
  do 3 eexists;split;eauto;constructors;eauto;eapply stmt_step;eauto; constructors;eauto.
  inverts H1. 
  inverts H0;tryfalse.
  inverts H8;tryfalse. inverts H;inverts H0.
  inverts H;inverts H0.
  inverts H13.
  lets Hint: intcont_some_addcont (kseq (swhile e s) kstop) H14.
  rewrite Hint in H2.
  inverts H2.
  do 3 eexists;split;eauto;eapply exint_step;eauto.
  inverts H1;do 3 eexists;split;eauto;eapply eoi_step;eauto.
  inverts H1;do 3 eexists;split;eauto;eapply cli_step;eauto.
  inverts H1;do 3 eexists;split;eauto;eapply sti_step;eauto.
  inverts H1;do 3 eexists;split;eauto;eapply encrit_step;eauto. 
  inverts H1;do 3 eexists;split;eauto;eapply excrit_step;eauto.
  inverts H1;do 3 eexists;split;eauto;eapply checkis_step;eauto.
Qed.


Lemma  estep_deter : forall c ke m c' ke' m' c'' ke'' m'',
                       estep c ke m c' ke' m' -> estep c ke m c'' ke'' m'' ->
                       c' = c'' /\ m' = m''/\ ke'=ke''.
Proof.
  introv Hes Hes'.
  inverts Hes as Hp Hq Hr;  inverts Hes' as Hp' Hq' Hr';
  try rewrite Hp in Hp'; 
  try inverts keep Hp'; try rewrite Hq in Hq'; try inverts keep Hq'; 
  try rewrite Hr in Hr'; try inverts keep Hp'; splits; auto.
  simpl in *;tryfalse.
  simpl in *;tryfalse.
  simpl in *;tryfalse.
  rewrite Hp in Hq'; inverts Hq'; auto.
  rewrite H0;auto.
Qed.


Lemma estepstar_imply_star :  forall c  c' ke ke' m v , 
        estepstar c ke m c' ke' m ->  estepstar c ke  m [v] kenil m ->
        estepstar c' ke' m [v] kenil m. 
Proof.
introv  Hes.
inductions Hes.
auto.
introv Hss.
lets Heqm : estep_mem_same H.
subst.
eapply IHHes; eauto.
inverts Hss.
inverts H.
lets Hre : estep_deter H H0.
destruct Hre as (Hcc & Hmm & Hke).
subst.
auto.
Qed.

Lemma notvundef_true_false: 
  forall v,  v <> Vundef ->  
             istrue v = Some true  \/ istrue v = Some false. 
Proof.
  intros.
  destruct v; simpl in *; tryfalse || auto.
  destruct (Int.eq i Int.zero); auto.
Qed.


Lemma estep_join_lstep: 
  forall p c ke m c' ke' m' isr aux Ms  Mf o2, 
    estep c ke m c' ke' m' ->  
    joinm2 (m, isr, aux) Ms Mf o2 ->
    exists o2' C,  loststep p (c, (ke, kstop)) o2 C o2' /\ o2 = o2' /\ C = (c',(ke',kstop)).
Proof.
  unfold joinm2; intros.
  simpljoin.
  rename x into o1.

  lets Hestep : estep_mem_same H.
  subst.
  unfold joinmem in *.
  do 6 destruct H1.
  destructs H1.
  subst.
  do 6 destruct H0.
  destructs H0.
  inverts H0;inverts H1.  
  
  inverts H;
  try solve[
  do 2 eexists;
  try solve [(
  split;[
  (eapply ostc_step;eauto;eapply expr_step;eauto;eapply ecastint_step;eauto)|eauto]);
  try solve [lets Hjoin: join_assoc_l H2 H3;
  destruct Hjoin as (M'' & Hjoin);destruct Hjoin;
  try erewrite evalval_mono;eauto;
  try erewrite evaltype_mono;eauto;
  unfold SysmemJoinM;
  do 4 eexists;split;eauto;split;eauto]];
  (
  split;[
  (eapply ostc_step;eauto;eapply expr_step;eauto;econstructor;eauto)|eauto]);
  try solve [lets Hjoin: join_assoc_l H2 H3;
  destruct Hjoin as (M'' & Hjoin);destruct Hjoin;
  try erewrite evalval_mono;eauto;
  try erewrite evaltype_mono;eauto;
  unfold SysmemJoinM;
  do 4 eexists;split;eauto;split;eauto]].
  
  do 2 eexists;
  try solve [(
  split;[
  (eapply ostc_step;eauto;eapply expr_step;eauto;eapply ecastnull_step;eauto;eapply ecastcomptr_step;eauto)|eauto]);
  try solve [lets Hjoin: join_assoc_l H2 H3;
  destruct Hjoin as (M'' & Hjoin);destruct Hjoin;
  try erewrite evalval_mono;eauto;
  try erewrite evaltype_mono;eauto;
  unfold SysmemJoinM;
  do 4 eexists;split;eauto;split;eauto]];
  (
  split;[
  (eapply ostc_step;eauto;eapply expr_step;eauto;constructors;eauto)|eauto]);
  try solve [lets Hjoin: join_assoc_l H2 H3;
  destruct Hjoin as (M'' & Hjoin);destruct Hjoin;
  try erewrite evalval_mono;eauto;
  try erewrite evaltype_mono;eauto;
  unfold SysmemJoinM;
  do 4 eexists;split;eauto;split;eauto].
  inverts H0.
  assert (load t x8 (addrval_to_addr a) = Some v).
  erewrite load_mono;eauto.
  erewrite load_mono;eauto.
Qed.

Lemma inv_precise_imply_eqm' :
  forall p G E  M Ms Ms'  isr aux Os Os'   M' M'', 
    satp  (G, E, Ms, isr, aux) Os  p ->
    satp  (G, E, Ms', isr, aux) Os' p ->
    precise p ->
    join M Ms M'' ->
    join M' Ms' M'' ->
    M = M' /\ Ms = Ms'.
Proof.
  intros.
  unfold satp in *.
  unfold precise in H1.
  pose proof H sched.
  pose proof H0 sched.
  pose proof H1 (G, E, Ms, isr, aux, Os, sched) Ms Ms' Os Os'.
  simpl in H6.
  pose proof H6 H4 H5; clear H6.
  destruct H7.
  pose proof H6 M''.
  assert (Ms = Ms').
  apply H8.
  clear - H2.
  eapply join_sub_r; eauto.
  clear - H3.
  eapply join_sub_r; eauto.

  split; auto.
  clear - H2 H3 H9; substs.
  jeat.
Qed.


Lemma starinv_isr_precise :
  forall n low I s M1 M2 o1 o2,
    substmo s M1 o1 |= starinv_isr I low n ->
    substmo s M2 o2 |= starinv_isr I low n ->
    (forall M : mem, Maps.sub M1 M -> Maps.sub M2 M -> M1 = M2) /\
    (forall o : osabst, Maps.sub o1 o -> Maps.sub o2 o -> o1 = o2).
Proof.
  inductions n; intros.
  destruct s as [[[[[[]]]]]].
  simpl substmo in *.

  simpl starinv_isr in H, H0.
  destruct H, H0.
  destruct H, H0.
  simpl in H, H0; mytac; intros; auto.
  simpl in H, H0; simpljoin; tryfalse.
  simpl in H, H0; simpljoin; tryfalse.

  remember (I low) as X.
  destruct X.
  destruct prec.
  simpl assertion.getinv in H, H0.
  simpl in H, H0; mytac.
  unfold precise in p.
  pose proof p (e, e0, M1, x0, l, o1, a) M1 M2 o1 o2.
  simpl substmo in H.
  pose proof H H15 H5.
  destruct H0.
  intros.
  eapply H0; eauto.

  pose proof p (e, e0, M1, x0, l, o1, a) M1 M2 o1 o2.
  simpl substmo in H.
  pose proof H H15 H5.
  destruct H0.
  intros.
  eapply H1; eauto.

  unfold starinv_isr in H, H0; fold starinv_isr in H, H0.
  destruct s as [[[[[[]]]]]].
  simpl substmo in *.
  unfold sat in H, H0; fold sat in H,H0.
  simpl substmo in *.
  simpl assertion.getmem in *.
  simpl getabst in *.
  simpl gettaskst in *.
  simpl getisr in *.
  simpl empst in *.
  unfold emposabst in *.
  simpljoin.
  destruct H9, H4; mytac; tryfalse.

  pose proof IHn (S low) I (e, e0, M1, x11, l, o1, a) M1 M2 o1 o2.
  simpl substmo in H1.
  pose proof H1 H10 H5; destruct H2.
  intros; eapply H2; eauto.
  
  pose proof IHn (S low) I (e, e0, M1, x11, l, o1, a) M1 M2 o1 o2.
  simpl substmo in H1.
  pose proof H1 H10 H5; destruct H2.
  intros; eapply H1; eauto.

  remember (I low) as X; destruct X; destruct prec.
  simpl assertion.getinv in H11, H21.
  unfold precise in p.
  pose proof p (e, e0, x5, x11, l, x8, a) x5 x x8 x2.
  simpl substmo in H.
  pose proof H H21 H11.
  destruct H0.
  intros.
  assert(x5 = x).
  eapply H0.
  instantiate (1:=M).
  clear - H6 H4.
  unfold Maps.sub in H4; simpljoin.
  assert (Maps.sub x5 M1).
  eapply join_sub_l; eauto.
  assert (Maps.sub M1 M).
  eapply join_sub_l; eauto.
  eapply sub_trans; eauto.
  assert (Maps.sub x M2).
  eapply join_sub_l; eauto.
  eapply sub_trans; eauto.
  substs.
  pose proof IHn (S low) I (e, e0, x6, x11, l, x9, a) x6 x0 x9 x3 H10 H5.
  destruct H12.
  assert (x6 = x0).
  eapply H12.
  instantiate (1:=M).
  assert(Maps.sub x6 M1).
  eapply join_sub_r; eauto.
  eapply sub_trans; eauto.
  assert(Maps.sub x0 M2).
  eapply join_sub_r; eauto.
  eapply sub_trans; eauto.
  substs.
  clear - H1 H6.
  jeat.

  remember (I low) as X; destruct X; destruct prec.
  simpl assertion.getinv in H11, H21.
  unfold precise in p.
  pose proof p (e, e0, x5, x11, l, x8, a) x5 x x8 x2.
  simpl substmo in H.
  pose proof H H21 H11.
  destruct H0.
  intros.
  assert(x8 = x2).
  eapply H2.
  instantiate (1:=o0).
  assert (Maps.sub x8 o1).
  eapply join_sub_l; eauto.
  eapply sub_trans; eauto.
  assert (Maps.sub x2 o2).
  eapply join_sub_l; eauto.
  eapply sub_trans; eauto.
  substs.
  pose proof IHn (S low) I (e, e0, x6, x11, l, x9, a) x6 x0 x9 x3 H10 H5.
  destruct H12.
  assert (x9 = x3).
  eapply H13.
  instantiate (1:=o0).
  assert(Maps.sub x9 o1).
  eapply join_sub_r; eauto.
  eapply sub_trans; eauto.
  assert(Maps.sub x3 o2).
  eapply join_sub_r; eauto.
  eapply sub_trans; eauto.
  substs.
  clear - H3 H8.
  jeat.
Qed.


Lemma inv_ieon_precise :
  forall I s M1 M2 o1 o2,
    substmo s M1 o1 |= inv_ieon I ->
    substmo s M2 o2 |= inv_ieon I ->
    (forall M : mem, Maps.sub M1 M -> Maps.sub M2 M -> M1 = M2) /\
    (forall o : osabst, Maps.sub o1 o -> Maps.sub o2 o -> o1 = o2).
Proof.
  intros.
  destruct s as [[[[[[]]]]]].
  simpl substmo in *.
  unfold inv_ieon in *.
  unfold sat in H; fold sat in H.
  unfold sat in H0; fold sat in H0.
  simpl assertion.getmem in *.
  simpl gettaskst in *.
  simpl getabst in *.
  simpl getie in *.
  destruct l; destruct p.
  simpl substmo in *.
  simpljoin.
  unfold empst in *.
  unfold emptaskst in *.
  simpljoin.
  
  unfold invlth_isr in *.
  rewrite Nat.sub_0_r in *.
  pose proof starinv_isr_precise INUM 0 I (e, e0, x6, i, (true, i1, c), x9, a) x6 x0 x9 x3.
  simpl substmo in H.
  pose proof H H11 H5.
  assert (x0 = M2).
  mytac.
  assert (x6 = M1).
  mytac.
  substs.
  unfold emposabst in *.
  substs.
  assert (x3 = o2 /\ x9 = o1).
  mytac.
  simpljoin.
  auto.
Qed.

Lemma inv_ieoff_precise :
  forall I s M1 M2 o1 o2,
    substmo s M1 o1 |= inv_ieoff I ->
    substmo s M2 o2 |= inv_ieoff I ->
    (forall M : mem, Maps.sub M1 M -> Maps.sub M2 M -> M1 = M2) /\
    (forall o : osabst, Maps.sub o1 o -> Maps.sub o2 o -> o1 = o2).
Proof.
  intros.
  unfold inv_ieoff in *.
  destruct s as [[[[[[]]]]]].
  simpl substmo in *.
  unfold sat in H, H0; fold sat in H, H0.
  simpl assertion.getmem in *.
  simpl substmo in *.
  simpl gettaskst in *.
  simpl getabst in *.
  simpl getie in *.
  destruct l; destruct p.
  simpl gettopis in *.
  simpl empst in *.
  mytac.
  destruct H24, H10; mytac; tryfalse.
  unfold invlth_isr in *.
  pose proof starinv_isr_precise (INUM - (gettopis i1 + 1)) (gettopis i1 + 1) I
       (e, e0, M1, i, (false, i1, c), o1, a) M1 M2 o1 o2 H12 H5.
  destruct H.
  intros; eapply H; eauto.

  rewrite H0 in H6.
  clear - H6.
  apply Nat.lt_irrefl in H6; false.

  rewrite H in H4.
  apply Nat.lt_irrefl in H4; false.

  intros; auto.

  destruct H24, H10; mytac; tryfalse.
  unfold invlth_isr in *.
  pose proof starinv_isr_precise (INUM - (gettopis i1 + 1)) (gettopis i1 + 1) I
       (e, e0, M1, i, (false, i1, c), o1, a) M1 M2 o1 o2 H12 H5.
  destruct H.
  intros; eapply H0; eauto.

  rewrite H0 in H6.
  clear - H6.
  apply Nat.lt_irrefl in H6; false.

  rewrite H in H4.
  apply Nat.lt_irrefl in H4; false.

  intros; auto.
Qed.


Lemma inv_ieon_inv_ieoff_precise :
  forall I,
    precise (inv_ieon I \\// inv_ieoff I).
Proof.
  unfold precise; intros.
  destruct H, H0.


  eapply inv_ieon_precise; eauto.

  unfold inv_ieon in H.
  unfold inv_ieoff in H0.
  destruct_s s; mytac; tryfalse.

  
  unfold inv_ieon in H0.
  unfold inv_ieoff in H.
  destruct_s s; mytac; tryfalse.

  eapply inv_ieoff_precise; eauto.
Qed.


Lemma inv_precise :
  forall I,
    precise (INV I).
Proof.
  intros.
  unfold INV.
  remember (I (S INUM)) as x.
  destruct x.
  simpl.
  destruct prec.

  unfold precise; intros.
  destruct s as [[[[[[]]]]]].
  simpl substmo in *.
  remember (inv_ieon I \\// inv_ieoff I) as X.
  unfold sat in H, H0; fold sat in H, H0; simpljoin.
  simpl substmo in *.
  simpl assertion.getmem in *.
  simpl getabst in *.

  unfold precise in p.
  pose proof p (e, e0, x5, i0, l, x8, a) x5 x x8 x2 H9 H4.
  pose proof inv_ieon_inv_ieoff_precise I.
  unfold precise in H0.
  pose proof H0 (e, e0, x6, i0, l, x9, a) x6 x0 x9 x3 H10 H5.
  mytac; intros.
  assert (x5 = x).
  mytac; eapply H.
  instantiate (1:=M).
  assert(Maps.sub x5 M1).
  eapply join_sub_l; eauto.
  eapply sub_trans; eauto.
  assert(Maps.sub x M2).
  eapply join_sub_l; eauto.
  eapply sub_trans; eauto.
  substs.

  assert (x6 = x0).
  eapply H2.
  instantiate (1:=M).
  assert(Maps.sub x6 M1).
  eapply join_sub_r; eauto.
  eapply sub_trans; eauto.
  assert(Maps.sub x0 M2).
  eapply join_sub_r; eauto.
  eapply sub_trans; eauto.
  substs.
  clear - H1 H6.
  jeat.

  assert (x8 = x2).
  mytac; eapply H11.
  instantiate (1:=o0).
  assert(Maps.sub x8 o1).
  eapply join_sub_l; eauto.
  eapply sub_trans; eauto.
  assert(Maps.sub x2 o2).
  eapply join_sub_l; eauto.
  eapply sub_trans; eauto.
  substs.
  
  assert (x9 = x3).
  eapply H7.
  instantiate (1:=o0).
  assert(Maps.sub x9 o1).
  eapply join_sub_r; eauto.
  eapply sub_trans; eauto.
  assert(Maps.sub x3 o2).
  eapply join_sub_r; eauto.
  eapply sub_trans; eauto.
  substs.
  clear - H3 H8.
  jeat.
Qed.

Lemma inv_precise_imply_eqm :
  forall G E  M Ms Ms' I  isr aux Os Os'   M' M'', 
    satp  (G, E, Ms, isr, aux) Os  (INV I) ->
   satp  (G, E, Ms', isr, aux) Os' (INV I) ->
    join M Ms M'' ->
    join M' Ms' M'' ->
    M = M' /\ Ms = Ms'.
Proof.
  intros.
  eapply inv_precise_imply_eqm'; eauto.
  eapply inv_precise.
Qed.
