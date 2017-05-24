Require Import Coqlib.
Require Import memory.
Require Import Integers.
Require Import List.
Require Import ZArith.
Require Import language.
Require Import opsem.
Require Import LibTactics.
Require Import assertion.

(*Continuation Properties*)

Lemma addstmts_eq_addcont : forall s ks ,
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

Open Local Scope nat_scope.
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

 Lemma  call_int_cont_none : forall ks f s E ks1 ,callcont (ks ## kcall f s E ks1) <> None -> callcont ks = None -> callcont (ks ## kcall f s E ks1) = Some (kcall f s E ks1).
 Proof.
   induction ks; intros; simpl in *; tryfalse || eauto.
Qed.

Lemma callcont_kseq_kstop : forall ks e s f s0 le' ks'0,
  callcont (ks ## kseq (swhile e s) kstop) = Some (kcall f s0 le' ks'0) ->
    exists ks',callcont ks = Some (kcall f s0 le' ks').
Proof.
  induction ks;intros;inverts H;try solve [eapply IHks;eauto].
  eexists;simpl;auto.
Qed.

Lemma callcont_addcont_none :   forall ks ks', callcont (ks ## ks') = None -> 
                                  callcont ks = None.
Proof.
  intros.
  induction ks; simpl in *; tryfalse || auto.
Qed.

Lemma callcont_nont_addkseq_kstop : forall ks s, callcont ks = None -> callcont (ks ## kseq s kstop) = None.
Proof.
  intros.
  induction ks; simpl in *; tryfalse || auto.
Qed.

(* intcont *)
Lemma intcont_some_addcont : forall ks ks1 k ,  
      intcont ks = Some k -> intcont (AddKsToTail ks1 ks) 
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

Lemma intcont_some_addstmts : forall ks s k ,  
      intcont ks = Some k -> intcont (AddStmtToKs s ks) 
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

Lemma intcont_none_addstmts : forall s ks , intcont (AddStmtToKs s ks) = None -> intcont  ks = None.
Proof.
introv Hint.
inductions ks;simpl; auto.
simpl in Hint.
inverts Hint.
Qed.

Lemma intcont_none_addstmsts_rev : forall s ks , intcont  ks = None ->  intcont (AddStmtToKs s ks) = None.
Proof.
introv Hint.
inductions ks;simpl; auto.
simpl in Hint.
inverts Hint.
Qed.

Lemma intcont_none_addcont : forall s ks , intcont (ks##s) = None -> intcont  ks = None.
Proof.
introv Hcall.
inductions ks;simpl; auto.
simpl in Hcall.
inverts Hcall.
Qed.

Lemma intcont_nont_addstmt_prev : forall ks s, intcont ks = None -> intcont (ks ## kseq s kstop) = None.
Proof.
  intros.
  induction ks; simpl in *; tryfalse || auto.
Qed.

Lemma intcont_none : forall ks f s E ks', 
           intcont (ks ## kcall f s E kstop) = None -> 
            intcont (ks ## kcall f s E ks') = None.
Proof.
  intros.
  gen ks ks' f s E.
  induction ks; induction ks'; intros; simpl in *; tryfalse || auto.
Qed.

Lemma intcont_some_kcall_none :  forall ks f s E ks1, 
                  intcont (ks ## kcall f s E ks1) <> None -> 
                                     intcont ks <> None. 
Proof.
  induction ks; intros; simpl in *; tryfalse || eauto.
  intro;tryfalse.
Qed.

Lemma intcont_intcont_none: forall ks f s E ks',
              intcont ks = None ->  intcont (ks ## kcall f s E ks') =  None.
Proof.
  induction ks; intros; simpl in *; tryfalse || auto.
Qed.

Lemma intcont_addkcall_exist : forall ks f s E ks' c0 ke0 le0 ks'0 ,
  intcont (ks ## kcall f s E ks') = Some (kint c0 ke0 le0 ks'0) ->
      exists ks'', ks'0 = ks'' ## kcall f s E ks'.
Proof.
  induction ks;intros;inverts H;try apply IHks;eauto.
Qed.

Lemma intcont_addkcall_imply_intcont : forall ks f s E ks' c0 ke0 le0 ks1 ,
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
Lemma  callcont_none_intcont_some_imply_callcont_addcont_none : forall ks ks' , callcont ks = None -> intcont ks <> None ->  callcont (ks ## ks') = None.
Proof.
 inductions ks;introv Hcal Hint ; simpl; auto.
 simpl in Hint; tryfalse.
 simpl in Hint; tryfalse.
Qed.

Lemma callcont_some : forall ks0 f s E', callcont ks0 = None -> intcont ks0 = None -> callcont (ks0 ## kcall f s E' kstop) = Some
  (kcall f s E' kstop).
Proof.
inductions ks0;introv Hcall Hint;simpl in *; tryfalse; try eauto.
Qed.

Lemma callcont_kcall_neqnone : forall ks f s E , ~(callcont (ks ## kcall f s E kstop) = None /\ intcont (ks ## kcall f s E kstop) = None).
Proof.
inductions ks; introv Hfalse; simpl in Hfalse; destruct Hfalse; tryfalse; try (eapply IHks; eauto).
Qed.

Lemma callcont_not_none : forall ks f  s E ks',  intcont (ks ## kcall f  s E ks') = None-> callcont (ks ## kcall f  s E ks') <> None. 
Proof.
  intros.
  induction ks; simpl in  *; try discriminate || auto.
Qed.

Lemma callcont_not_none' :  forall ks f  s E ks' ks0 , ks ## kcall f s E ks' = kret ks0 -> intcont ks0 = None ->  callcont ks0 <> None.
Proof.
  intros.
  gen f s E ks' ks0.
  induction ks; intros; simpl in *; try discriminate || auto.
  inverts H.
  eapply  callcont_not_none; eauto.
Qed.

Lemma  call_int_none_call: forall ks f s E ks',
                             callcont ks =None -> intcont ks = None ->
                             callcont (ks ## kcall f s E ks') = Some (kcall f s E ks').
Proof.
  inductions ks; intros; simpl in *; tryfalse; try auto.
Qed.

Lemma callcont_some_eq :  forall ks1 f s E ks ,
                  callcont ks1 = None -> 
                  intcont ks1 = None -> 
               callcont (ks1 ## kcall f s E ks) =  Some (kcall f s E ks) .
Proof.  
  induction ks1; induction ks; intros; simpl in *; tryfalse || auto.
Qed.

 Lemma  callcont_intcont_kcall_none : forall ks f s E , 
              callcont ks = None ->  intcont (ks ## kcall f s E kstop) = None -> intcont ks = None.
Proof.
inductions ks; tryfalse; simpl; auto.
 introv _ Hf; tryfalse.
Qed.

Lemma intcont_calcont_not_none: forall ks f s E ks',
              intcont ks = None ->  callcont (ks ## kcall f s E ks') <>  None.
Proof.
  induction ks; intros; simpl in *; tryfalse || auto.
  intro;tryfalse.
  intro;tryfalse.
Qed.

(* others *)
Lemma ks_puls_kcall_neq : forall ks ks' f s E, ks ## kcall f s E ks' <> kstop.
Proof.
  intros.
  induction ks;simpl;try discriminate.
Qed.

Lemma add_stmt_not_kstop :  forall s ks, AddStmtToKs s ks <> kstop.
Proof.
  intros.
  induction ks;simpl;try discriminate.
Qed.

Lemma addstmt_kret_exist : forall s ks ks' ,  AddStmtToKs s ks = kret ks' ->
                   exists ks'', ks = kret ks''.
Proof.
  intros.
  destruct ks;inverts H.
  eexists;eauto.
Qed. 

Lemma kseq_not_kstop : forall ks e s, ks ## kseq (swhile e s) kstop <> kstop.
Proof.
  intros.
  destruct ks;simpl;discriminate.
Qed.

Lemma kseq_eq_addstmt: forall ks s , ks ## kseq s kstop  = AddStmtToKs s ks.
Proof.
  intros.
  rewrite addstmts_eq_addcont.
  auto.
Qed.
  
(* addcont *)
Lemma kseq_addcont : forall ks ks' ks'',
  kseq ks (ks' ## ks'') = (kseq ks ks') ## ks''.
Proof.
  intros. simpl. auto.
Qed.

Lemma kcall_addcont : forall f s E ks ks',
  kcall f s E (ks ## ks') = (kcall f s E ks) ## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kint_addcont : forall c ke le ks ks',
  kint c ke le (ks ## ks') = (kint c ke le ks) ## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kassignr_addcont : forall e t ks ks',
  kassignr e t (ks ## ks') = (kassignr e t ks )## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kassignl_addcont : forall v t ks ks',
  kassignl v t (ks ## ks') = (kassignl v t ks )## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kfuneval_addcont : forall f vl tl el ks ks',
  kfuneval f vl tl el (ks ## ks') = (kfuneval f vl tl el ks) ## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kif_addcont : forall s1 s2 ks ks',
  kif s1 s2 (ks ## ks') = (kif s1 s2 ks) ## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kwhile_addcont : forall e s ks ks',
  kwhile e s (ks ## ks') = (kwhile e s ks) ## ks'.
Proof.
  intros. simpl. auto.
Qed.

Lemma kret_addcont : forall ks ks',
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



