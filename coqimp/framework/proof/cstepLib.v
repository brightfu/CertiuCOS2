Require Import include_frm.
Require Import memory_prop.
Require Import lmachLib.
Require Import contLib.
Require Import code_notations.

Open Scope nat_scope.

(* eval property *)
Lemma evaladdr_val_eq : forall e m v t, evaltype e m = Some t -> evaladdr e m = Some v -> evalval (eaddrof e) m = Some v.
Proof.
  intros. 
  destruct e; destruct m as [[]];simpl in *; tryfalse; try rewrite H; auto.
  destruct (evaltype e (e0, e1, m) ) ; tryfalse.
  destruct t0; tryfalse.
  inverts H. auto.
Qed.

Lemma evaltype_GE_eq : forall G E M1 M2 e t1 t2, evaltype e (G, E, M1) = Some t1 -> evaltype e (G,E,M2) = Some t2 -> t1 = t2.
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
 

(*Expression Evaluation Properties *)
Lemma estepstar_estep_trans : forall c ke m c' ke' m' c'' ke'' m'',
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


Lemma estepstar_estepstar_trans : forall c ke m c' ke' m' c'' ke'' m'',
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

Lemma sstep_idmove_deter : forall p c c' c'' ks ks' ks'' m m' , 
                     sstep p c ks m c' ks' m 
              -> sstep p  c ks m c'' ks'' m' ->  c' =c''/\ ks' = ks''  /\ m =m'.
Proof.
introv H1 H2.
inverts keep H1; inverts keep H2; 
try (tryfalse; splits; eauto).
rewrite H6 in H;inverts H;eauto.
inverts H0;inverts H8. 
rewrite H14 in H3;inverts H3;eauto.
rewrite H12 in H;inverts H;eauto.
auto.
rewrite H12 in H;inverts H;eauto.
rewrite H15 in H;inverts H;eauto.
rewrite H3 in H11;inverts H11;eauto.
rewrite H3 in H11;inverts H11;inverts H0;inverts H8;eauto.
inverts H0;inverts H8;eauto.
inverts H0;inverts H11;eauto.
apply alloc_false in H3;inverts H3.
inverts H0;inverts H7;eauto.
apply alloc_false in H3;inverts H3.
inverts H10;inverts H;eauto.
inverts H4;eauto.
inverts H0;inverts H13;eauto.
assert (typelen t = 0 \/ typelen t <> 0).
omega.
destruct H.
unfold free in H15.
rewrite H in H15.
simpl in H15.
inverts H15;eauto.
apply free_false in H3.
inverts H3.
auto.
rewrite H3 in H7;inverts H7;eauto.
inverts H0;inverts H4;rewrite H3 in H7;inverts H7;eauto.
Qed.


Lemma estepstar_deter: forall c ke m v v'  m' m'',
                         estepstar c ke m [v] kenil  m' ->
                         estepstar c ke m [v'] kenil  m'' -> v = v'/\ m' = m''.
Proof.
  introv Hestep Hestep'.
  gen Hestep'.
  inductions Hestep.
  introv Hestep'.
  inverts keep Hestep'.
  splits.
  auto.
  auto.
  inverts H.
  introv Hestep'.
  inverts Hestep'.
  inverts H.
  eapply IHHestep.
  apply estep_deter with (c :=c)( ke:=ke)(m:=m)( c':=c')(ke':=ke')( m':=m')( c'':=c'0)
                                (ke'':= ke'0)( m'':=m'0) in H; auto.
  destruct H as  [Hc [Hm Hk]].
  subst.
  auto.
Qed.


Lemma cstep_idmove_deter : forall p C C' C'' m m' ,
                             cstep p C m C' m -> cstep p C m C'' m'
                             ->  C' = C'' /\ m = m'.
Proof.
  introv H1 H2.
  inverts H1; inverts H2; tryfalse.
  inverts H. 
  lets Hres : estep_deter H0 H1.
  do 2 (inverts Hres as Hres _) ; subst.
  splits; eauto.
  inverts H;
    try ( inverts H1 as H0; inverts H0; splits; eauto).
  inverts H; 
    try ( inverts H1 as H0; inverts H0; splits; eauto).
  inverts H.
  lets Hres :sstep_idmove_deter H0 H1.
  do 2 (inverts Hres as Hres _) ; subst.
  splits; auto.
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
(*
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
  constructors.
  constructors.
  destruct m as [[ge le] M].
  simpl in Heval.
  inverts Heval.
  constructors.
 -introv Heval.
  simpl in Heval.
  inverts Heval.
*)
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

Lemma  evalval_imply_estepstar  :  forall (e:expr) (m : smem)  v ke,  evalval e m = Some v -> 
                                                                      estepstar (cure e) ke  m [v] ke m.
Proof.
  introv Heval .
  generalize (evalval_evaladdr_imply_estepstar e m).
  introv H.
  destruct H as [H1 H2].
  apply H1.
  auto.
Qed.

Lemma  evaladdr_imply_estepstar  :  forall (e:expr) (m : smem)  v ke,  evaladdr e m = Some v -> 
estepstar (cure (eaddrof e)) ke  m [v] ke m.
Proof.
introv Heval .
generalize (evalval_evaladdr_imply_estepstar e m).
introv H.
destruct H as [H1 H2].
apply H2.
auto.
Qed.

Lemma estep_mem_same : forall c ke m c' ke' m', estep c ke m c' ke' m' ->  m = m'.
Proof.
introv Hestep.
inductions Hestep; eauto.
Qed.

Lemma estepstar_mem_same : forall c ke m c' ke' m', estepstar c ke m c' ke' m' ->  m = m'.
Proof.
introv H.
inductions H. 
eauto.
eapply estep_mem_same in H.
subst.
auto.
Qed.

Lemma cstep_safe_mono: forall p C m M m', ~(cstepabt p C m) -> SysmemJoinM m M m' -> ~(cstepabt p C m'). 
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

Lemma cstep_frame : forall p C m M m' m'' C', ~(cstepabt p C m) -> SysmemJoinM m M m' -> cstep p C m' C' m'' ->
                                              (exists m1'', SysmemJoinM m1'' M m'' /\ cstep p C m C' m1'').
Proof.
  intros.
  destruct H0 as (G & E & M0 & M0' & H0).
  destructs H0.
  subst.
  inverts H1. 
  invert keep H2;intros;subst; 
  eexists;split;eauto;constructors;
  try solve [constructors;erewrite evalval_mono;eauto|constructors;eauto;erewrite evaltype_mono;eauto|constructors;eauto];
  try solve [constructors;erewrite<-evalval_mono;eauto|constructors;eauto;erewrite<-evaltype_mono;eauto|constructors;eauto].
  constructors.
  unfold cstepabt in H.
  apply Classical_Prop.NNPP in H.
  destruct H. destruct H. destruct H. destruct H.
  inverts H;
  inverts H1;inverts H4.
  rewrite<-H0. symmetry. eapply evalval_mono;eauto.
  inverts H. inverts H1;inverts H4.
  eapply eaelemaddr_step.
  erewrite <- evaltype_mono;
  eauto.
  
  eapply eaelem_step.
  erewrite <- evaltype_mono;
  eauto.

  (*
  eapply ecastnull_step;eauto.
  erewrite <-evaltype_mono;eauto.

  eapply ecastcomptr_step;eauto.
  erewrite <-evaltype_mono;eauto.
   *)
  inverts H0.
  constructors;eauto.
  unfold cstepabt in H.
  apply Classical_Prop.NNPP in H.
  destruct H. destruct H. destruct H. destruct H.
  inverts H;inverts H0;inverts H4.
  inverts H6. rewrite<-H1. symmetry. eapply load_mono;eauto.
  inverts H;inverts H0;inverts H4.
(* sstep *)
  unfold cstepabt in H.
  apply Classical_Prop.NNPP in H.
  destruct H. destruct H. destruct H. destruct H. 
  Focus 2. inverts H;inverts H0;inverts H1.
  inverts H2.
  inverts H2;
  try solve [eexists;split;eauto;try eapply stmt_step;eauto;constructors;eauto;try (do 3 eexists;eauto);
             try erewrite<-evaltype_mono;eauto;try erewrite<-evaltype_mono;eauto].
(* kassign *)
  inverts H0.
  inverts H;inverts H0;inverts H1.
  inverts H7.
  eexists;split;eauto.
  unfold SysmemJoinM.
  do 4 eexists;split;eauto;split;eauto.
  2:eapply stmt_step;eauto;constructors;eauto.
  eapply join_store;eauto.
(* fexec *)
  inverts H0.
  eexists.
  split.
  unfold SysmemJoinM. 
  do 4 eexists;split;eauto.
  eapply stmt_step;eauto. 
  constructors;eauto.
(* alloc2 *)
  inverts H0.
  lets Hx: (allocb_store_mem_ex t M0 b v).
  destruct Hx. destruct H4. destructs H1.
  rewrite H7 in H5.
  rewrite EnvMod.set_a_get_a in H5.
  inverts H5.
  rewrite H2 in H6.
  exists (ge, le', x3).
  split.
  unfold SysmemJoinM.
  do 4 eexists;split;eauto.
  split;eauto.
  eapply join_store.
  2:eauto. 2:eauto.
  eapply join_allocb;eauto.
  eapply stmt_step;eauto. 
  constructors;eauto.
  unfold alloc.
  exists b.
  split.
  eapply fresh_mono;eauto.
  split;eauto.
  rewrite H7.
  apply EnvMod.set_a_get_a.
  apply identspec.eq_beq_true;auto.
  apply identspec.eq_beq_true;auto.
(* alloc *)
  inverts H0.
  destruct H4. destructs H0.
  exists (ge, le', (allocb M0 x3 0%Z (typelen t))).
  split.
  unfold SysmemJoinM.
  do 4 eexists;split;eauto;split;eauto.
  eapply join_allocb;eauto.
  eapply stmt_step;eauto. 
  constructors;eauto.
  unfold alloc.
  exists x3.
  split;eauto.
  eapply fresh_mono.
  apply H3.
  eauto.
(* ret *)
  inverts H0.
  inverts H;inverts H0;inverts H2.
  inverts H.
  rewrite H0 in H1;inverts H1.
  eexists.
  split.
  unfold SysmemJoinM.
  do 4 eexists;split;eauto.
  eapply stmt_step;eauto.
  constructors;eauto.
(* kret *)
  eexists;split;eauto;try eapply stmt_step;eauto;constructors;eauto.
  inverts H0.
  do 3 eexists;split;eauto.
  inverts H0;auto.
(* free *)
  inverts H0.
  inverts H;inverts H0;inverts H1.
  inverts H12.
  eexists.
  split.
  unfold SysmemJoinM.
  do 4 eexists;split;eauto;split;auto.
  eapply join_free;eauto.
  eapply stmt_step;eauto.
  constructors;eauto.
(* free nil *)
  inverts H0.
  eexists.
  split.
  unfold SysmemJoinM.
  do 4 eexists;split;eauto.
  eapply stmt_step;auto.
  constructors;eauto.
Qed.
(*
Lemma cstep_cont_locality : forall p c ke ks ks1 m m' c' ke' ks', 
                        cstep p (c, (ke, ks)) m (c', (ke', ks')) m'->
                        cstep p (c, (ke, (AddKsToTail ks1 ks))) m 
                        (c', (ke', (AddKsToTail ks1 ks'))) m'.
Proof.
introv H.
inductions H.
eapply expr_step; eauto.
eapply stmt_step; eauto.
inductions H0; constructors; eauto.
simpl.
lets Haux: callcont_some_prev_rev H0.
eauto.
lets Haux: callcont_some_prev_rev H0.
simpl in Haux.
eauto.
lets Haux: callcont_some_prev_rev H0.
simpl in Haux.
eauto.
lets Haux: callcont_some_prev_rev  H0.
simpl in Haux.
eauto.
Qed.

Lemma cstep_cont_stmts_locality : forall p c ke ks s m m' c' ke' ks', 
                        cstep p (c, (ke, ks)) m (c', (ke', ks')) m'->
                        cstep p (c, (ke, (AddStmtToKs s  ks))) m 
                        (c', (ke', (AddStmtToKs s ks'))) m'.
Proof.
introv H.
rewrite_all  addstmts_eq_addcont.
eapply cstep_cont_locality; eauto.
Qed.

Lemma cstepstar_cont_locality: forall p c ke ks ks1 m m' c' ke' ks', 
                        cstepstar  p (c, (ke, ks)) m (c', (ke', ks')) m'->
                        cstepstar p (c, (ke, (AddKsToTail ks1 ks))) m 
                        (c', (ke', (AddKsToTail ks1 ks'))) m'.
Proof.
introv H.
inductions H.
constructors.
destruct C'.  
destruct c1. 
constructors; [| eapply IHcstepstar; eauto].
 eauto.
eauto.
simpl in *.
lets Hstep :  cstep_cont_locality  H.
eauto.
Qed.
*)
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

Ltac  destru m :=   (let H := fresh  in  destruct m  as ( H & m)). 

Lemma  estepv_notabortm : forall  m v c ke  , 
                         estepstar c ke m [v] kenil m ->
 ~ IsFcall (c,(ke,kstop)) /\
~ IsSwitch  (c,(ke,kstop)) /\ ~ IsRet  (c,(ke,kstop)) /\ ~ IsRetE  (c,(ke,kstop)) /\ ~ IsIRet (c,(ke,kstop)) .
Proof.
introv He1.
inductions He1.
splits;introv H.
do 4 destru H; inverts H.
do 2 destru H; inverts H.
do 2 destru H; inverts H.
inverts H1.
do 3 destru H; inverts H.
inverts H2.
do 2 destru H; inverts H.
inverts H1.
lets Heq : estep_mem_same H.
subst m'.
assert (m = m) as Hasrt; auto.
lets Hres : IHHe1 Hasrt.
destruct Hres as (Hf & Hsw & Hisret & Hisre & Hiret).
splits; introv Hfl.
do 4 destru Hfl; inverts Hfl.
inverts H.
do 2 destru Hfl; inverts Hfl.
inverts H.
do 2 destru Hfl; inverts Hfl.
inverts H1.
inverts H.
do 3 destru Hfl; inverts Hfl.
inverts H2.
do 2 destru Hfl; inverts Hfl.
inverts H1.
inverts H.
Qed.

Close Scope nat_scope.
