Require Import include_frm.
Require Import base_tac.
Require Import sep_auto.
Require Import memory_prop.
Require Import aux_map_lib.
Open Scope Z_scope.
 

Import DeprecatedTactic.

Lemma evalval_imply_evaltype : forall (e : expr) (m : smem) v , 
 evalval e m = Some v -> exists t, 
 evaltype e m = Some t.
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

Lemma field_offset_plus : forall i d  n  z1 z2,  field_offsetfld i d z1 = Some n -> 
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

Lemma structtype_imply_fieldoffset :  forall i d t, memory.ftype i d = Some t ->
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


Lemma eval_addr_prop : forall e m v,  evaladdr e m = Some v ->
(exists e', e = ederef e')\/
( exists x, e = evar x) \/
(exists e' id, e = efield e' id) \/(exists e1 e2,  e = earrayelem e1 e2).
Proof.
introv He.
destruct e; simpl in He; tryfalse.
branch 2.
exists v0.
auto.
branch 1.
eexists;eauto.
branch 3.
exists e i.
auto.
branch 4.
exists e1 e2.
auto.
Qed.

Lemma evaltype_irrev_mem : forall  e G E M  M', evaltype e (G,E,M) = evaltype e (G,E,M').
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

Lemma evaltype_mono: forall e ge le m M m' ,  
                       join m M m' -> evaltype e (ge, le, m') = evaltype e (ge, le, m).
Proof.
   intros.
   apply evaltype_irrev_mem; eauto.
Qed.

Lemma map_get_join_val :
  forall  (x y z: mem) t b v, 
    join x y z ->
    HalfPermMap.get x t = Some (b, v) ->
    exists b, HalfPermMap.get z t = Some (b, v).
Proof.
  intros.
  unfold join in H.
  unfold memMap in H.
  unfold HalfPermMap.join in H.
  unfold HalfPermMap.disjoint in H.
  unfold HalfPermMap.merge in H.
  destruct H.
  rewrite H1.
  unfold HalfPermMap.get in *.
  lets aa: H t.
  rewrite H0 in *.
  destruct b.
  destruct (y t).
  inversion aa.
  eauto.
  destruct (y t).
  destruct b.
  destruct b.
  inversion aa.
  inverts aa.
  unfold HalfPermMap.rjoin.
  2:eauto.
  destruct (HalfPermMap.dec_C c c ).
  eauto.
  eauto.
Qed.

Lemma loadbytes_mono: forall m M m' l n v ,  
  join m M m' -> 
  loadbytes m l n = Some v -> loadbytes m' l n = loadbytes m l n.
Proof.
  intros.
  generalize dependent l.
  generalize dependent v.
  induction n.
  intros.
  simpl.
  auto.
  intros.
  destruct l.
  simpl.
  simpl in H0.
  change (match get m (b, o) with
               | Some (_, u) =>
                 match loadbytes m (b, (o + 1)%Z) n with
                   | Some bl => Some (u :: bl)
                   | None => None
                 end
               | None => None
             end
         ) with ((fun x =>    match x with
                                | Some (_, u) =>
                                  match loadbytes m (b, (o + 1)%Z) n with
                                    | Some bl => Some (u :: bl)
                                    | None => None
                                  end
                                | None => None
                              end
                 ) (get m (b,o))) in *.

  remember (get m ( b, o)) as bb.
  unfold get in Heqbb.
  simpl in Heqbb.
  assert (HalfPermMap.get m (b,o) = bb).
  auto.
  destruct bb.
  destruct p.
  lets ff: map_get_join_val H.
  apply ff in H1.
  unfold HalfPermMap.get in Heqbb.
  mytac.
  unfold get.
  simpl.
  rewrite H1.
  remember (   loadbytes m (b, (o + 1)%Z) ).
  rewrite Heqo0.
  remember (o0 n).
  assert ((exists bl, o1 = Some bl) \/ o1 = None).
  destruct o1.
  left; eauto.
  right; auto.
  destruct H2; intros.
  destruct H2.
  erewrite IHn.
  auto.
  rewrite <- Heqo0.
  rewrite <- Heqo1.
  eauto.
  rewrite H2 in H0.
  inversion H0.
  inversion H0.
Qed.

Lemma loadm_mono: forall m M m' t l v,  join m M m' ->
  loadm t m l = Some v -> loadm t m' l = loadm t m l .
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

Lemma load_mono: forall m M m' t l v,  join m M m' ->
  load t m l = Some v -> load t m' l = load t m l .
Proof.
  unfold load;intros;destruct t;try eapply loadm_mono;eauto.
Qed.
 

Lemma getoff_mono: forall ge le m M m' b o i e, join m M m' ->
   getoff b o i e (le, ge, m') = getoff b o i e (le, ge, m).
Proof.
  intros.
  unfold getoff.
  erewrite evaltype_mono;eauto.
Qed.

Lemma evalvaladdr_mono: 
  forall ge le e m M m' v ,
    ( join m M m' -> evalval e (ge, le, m) = Some v -> evalval e (ge, le, m') = evalval e (ge, le, m)) /\
    ( join m M m' -> evaladdr e (ge, le, m) = Some v -> evaladdr e (ge, le, m') = evaladdr e (ge, le, m)).
Proof.
  inductions e;introv;intros;split;auto;intros;eauto.

  unfold evalval;simpl;unfold evalval in H0;simpl in H0;eauto.
  destruct (get le v),(get ge v);tryfalse.
  destruct p;tryfalse. 
  Lemma match_loadbytes :
    forall t m M m' b v, join m M m' ->
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
  forall ge le e m M m' v , (join m M m' -> evalval e (ge, le, m) = Some v -> evalval e (ge, le, m') = evalval e (ge, le, m)). 
Proof.
  intros.
  generalize (evalvaladdr_mono ge le e m M m' v).
  intros. destruct H1.
  apply H1;eauto.
Qed.

Lemma  evaladdr_mono:forall e M1 M2 M v ge le, join M1 M2 M -> evaladdr e (ge, le, M1) = Some v ->  evaladdr e (ge,le,M)= Some v.
Proof.
  intros.
  generalize (evalvaladdr_mono ge le e M1 M2 M v).
  intros. destruct H1.
  erewrite H2;eauto.
Qed.

Lemma typematch_mono:
  forall ge le m M m' el dl,  join m M m' -> (typematch el dl (ge, le, m) <-> typematch el dl (ge, le, m')).
Proof.
  intros. 
  generalize dependent dl.
  induction el. 
  intros. split;intros; 
  simpl;simpl in H0;auto.
  intros. split;intros;
  simpl;simpl in H0;destruct dl;auto.
  split. erewrite evaltype_mono;eauto. apply H0.
  apply IHel. apply H0.
  split. erewrite<-evaltype_mono;eauto. apply H0.
  apply IHel. apply H0.
Qed.

Require Import mem_join_lemmas.
Lemma storebytes_mono: forall m M m' m0 l vl,  join m M m' ->
  storebytes m l vl = Some m0 -> (exists m0',storebytes m' l vl = Some m0').
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


Lemma store_mono: forall m M m' m0 a t v,  join m M m' ->
  store t m a v = Some m0 -> (exists m0',store t m' a v = Some m0').
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


Lemma freeb_mono: forall m M m' m0 b i n,  join m M m' ->
  freeb m b i n = Some m0 -> (exists m0',freeb m' b i n = Some m0').
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

Lemma free_mono: forall m M m' m0 b t,  join m M m' ->
  free t b m = Some m0 -> (exists m0',free t b m' = Some m0').
Proof.
  intros.
  unfold free.
  unfold free in H0.
  eapply freeb_mono;eauto.
Qed.


Lemma allocb_emp_get_none : forall b i l x, (x > 0)%Z ->
                                            get (allocb empmem b (i + x) l) (b, i) = None.
Proof.
  intros.
  gen i.
  gen x.
  induction l; intros.
  simpl.
  apply emp_sem.
  simpl.
  rewrite set_a_get_a'.
  rewrite <- Zplus_assoc.
  apply (IHl (x+1)%Z).
  omega.
  intro.
  inversion H0.
  assert ((i + x)%Z <> i).
  omega.
  apply H1.
  apply H2.
Qed.

Lemma alloc_exist_ptomvallist :
  forall b i l,
    ptomvallist (b, i) true (list_repeat l Undef)
                (allocb empmem b i l).
Proof.
  introv. gen i.
  induction l.
  intros.
  simpl. auto.
  intros.
  simpl.
  do 2 eexists.
  split.
  2:split.
  3:apply IHl.
  2:unfold ptomval;auto.

  remember (allocb empenv b (i+1) l).
  assert (get m (b, i) = None).
  substs.
  eapply allocb_emp_get_none.
  omega.

  eapply get_none_join_sig_set; eauto.
Qed.


Lemma alloc_empmem_mapstoval:
  forall b t, 
    mapstoval (b, 0)%Z t true Vundef (allocb empmem b 0%Z (typelen t)).
Proof.
  intros.
  unfold mapstoval.
  unfold encode_val.
  eexists;split;eauto. 
  apply alloc_exist_ptomvallist.
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

(* Definitions and lemmas for the proof of 'alloc_store_exist_mem_env',
   lemmas marked as 'key lemma' are directly used in the proof *)
(* proofed by zhanghui *)
(* ----------------------------------------------------------------------*)
Lemma set_empmem_sig_eq : forall {A B T : Type} {X:PermMap A B T} a val, set emp a val = sig a val.
Proof.
  intros.
  join auto.
Qed.


Notation beq_Z := Z.eqb.

(*
Lemma beq_Z_Zeqb_ident : forall a b : Z, beq_Z a b = Z.eqb a b.
  induction a; induction b; intros; simpl; auto.

  Goal forall a b : positive, beq_pos a b = Pos.eqb a b.
    induction a; induction b; intros; simpl; auto.
  Qed.

  apply Unnamed_thm.
  apply Unnamed_thm.
Qed.
*)

Fixpoint init_mem (b:block) (i:offset) (vl:mvallist) {struct vl} : mem :=
  match vl with
    | nil => empmem
    | u :: vl' => set (init_mem b (i+1)%Z vl') (b, i)%Z (true,u)
  end.


Definition fresh_index (M : mem) (b : block) (i : offset): Prop := 
  forall offset, (offset >= 0)%Z -> get M (b, i + offset)%Z = None.


Lemma beq_Z_Zeqb_ident : forall a b : Z, beq_Z a b = Z.eqb a b.
  induction a; induction b; intros; simpl; auto.
Qed.

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
Lemma ptomvallist_init_mem : forall b i vl, ptomvallist (b, i) true  vl (init_mem b i vl).
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
  (* ** ac: Check join_sig_set. *)


  apply join_sig_set'.
  (* intro. *)
  (* unfolds in H; simpljoin. *)
  lets Hx: init_mem_not_in_dom b i vl 1%Z.
  cut (1>0)%Z.
  intros.
  apply Hx in H.
  auto.
  
  (* unfold get in *; simpl in *. *)
  (* remember (init_mem b (i + 1)%Z vl) as X. *)
  (* unfold HalfPermMap.get in *. *)
  (* change ((fun x => x = None) (X (b,i))) in H0. *)
  (* rewrite H in H0; tryfalse. *)

  omega.
  split.
  unfold ptomval.
  auto.
  apply IHvl.
Qed.

Lemma init_mem_get_some :
  forall b i vl b1 ba ia,
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


(* key lemma *)
Lemma memset_allocb_comm :
  forall M b i n len,
    (n > 0)%Z ->
    ((set (allocb M b (i + n) len) (b, i) (true,Undef)) = ((allocb (set M (b, i) (true,Undef)) b (i + n) len))).
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
  eapply mem_join_set_true_comm'; eauto.
  pose proof H 0%Z.
  rewrite Z.add_0_r in H1.
  eapply H1.
  omega.

  rewrite HeqX.

  assert((set X (b, i) (true, val)) = (set (set X (b, i) (true, Undef)) (b, i) (true, val))).
  symmetry.
  eapply mem_set_a_set_a.
  
  apply join_comm in H1.
  apply join_comm.
  substs.
  rewrite H3.
  eapply map_join_set_none in H1; eauto.
  pose proof H 0%Z.
  rewrite Z.add_0_r in H2.
  eapply H2.
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
Lemma mem_join_sig_r : forall {A B T : Type} {X:PermMap A B T} M a v, ~ indom M a -> join M (sig a v) (set M a v).
Proof.
  intros.
  apply join_comm.
  eapply get_none_join_sig_set.
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


(*-------------------------------------------------------------------------------*)
Fixpoint length_dl (dl : decllist) : nat :=
 match dl with
 | dnil => O
 | dcons _ _ dl' => S (length_dl dl')
end.

Lemma eval_type_match: forall el tl vl dl m, 
                 evalexprlist el tl vl m -> tlmatch tl dl -> 
                 typematch el dl m.
Proof.
inductions el.
intros.
destruct tl, vl, dl;
tryfalse;
try trivial.
intros.
destruct tl, vl, dl;
tryfalse.
simpl in H.
destruct H.
destruct H1.
simpl in H0.
destruct H0.
simpl.
subst.
split.
exists t.
split.
auto.
destruct t.
constructor.
right;auto.
constructor.
apply eq_int.
auto.
apply eq_int.
auto.
apply eq_int.
auto.
apply eq_vptr.
exists t.
exists t;auto.
apply eq_vcomptr.
split.
right.
exists i0;auto.
left.
exists i0;auto.
apply eq_array.
exists t n.
auto.
apply eq_struct.
exists i0 d.
auto.
apply (IHel tl vl dl m).
apply H2.
auto.
Qed.


Lemma revlcons_nil : forall d d', revlcons d d' = dnil -> d = dnil /\ d' = dnil.
Proof.
intro.
induction d.
intro.
destruct d'.
intro.
auto.
intro.
simpl in H.
inversion H.
intros.
false.
simpl in H.
pose proof IHd (dcons i t d').
apply H0 in H.
destruct H.
inversion H1.
Qed.

Lemma evalexprlist_len_eq : forall el tl vl m,
evalexprlist el tl vl m -> length el = length tl /\ length tl = length vl.
Proof.
inductions el.
intros.
destruct tl,vl;
tryfalse.
auto.
intros.
destruct tl, vl;
tryfalse.
simpl in H.
destruct H.
destruct H0.
destruct H1.
apply IHel in H1.
destruct H1.
simpl.
rewrite H1, H3.
auto.
Qed.

Lemma tlmatch_len_eq : forall tl dl, tlmatch tl dl -> length tl = length_dl dl.
Proof.
inductions tl.
intros.
destruct dl.
simpl.
reflexivity.
simpl in H.
inversion H.
intros.
destruct dl.
simpl in H.
inversion H.
simpl in H.
destruct H.
apply IHtl in H.
simpl.
destruct H.
auto.
Qed.


Lemma revlcons_len_plus : forall d d', length_dl (revlcons d d') = (length_dl d + length_dl d')%nat.
Proof.
inductions d.
intros.
simpl.
reflexivity.
intros.
simpl.
pose proof IHd (dcons i t d').
simpl in H.
rewrite H.
omega.
Qed.

Lemma evallist_length_leb :
  forall (vl:vallist) d d' tl el m, 
    evalexprlist el tl vl m ->
    tlmatch tl d -> 
    (length vl <= length_dl (revlcons d d'))%nat.
Proof.
  intros.
  apply tlmatch_len_eq in H0.
  apply evalexprlist_len_eq in H.
  destruct H.
  rewrite revlcons_len_plus.
  rewrite <- H1.
  rewrite H0.
  omega.
Qed.

Lemma rev_len_eq : forall vl : vallist, length (rev vl) = length vl.
Proof.
  inductions vl.
  simpl.
  reflexivity.
  simpl.
  rewrite app_length.
  simpl.
  omega.
Qed.

Lemma evallist_length_leb_rev : forall (vl:vallist) d d' tl el m, 
        evalexprlist el tl vl m ->
        tlmatch tl d -> 
        (length (List.rev vl) <= length_dl (revlcons d d'))%nat.
Proof.
  intros.
  rewrite rev_len_eq.
  apply evalexprlist_len_eq in H.
  destruct H.
  apply tlmatch_len_eq in H0.
  rewrite <- H1.
  rewrite H0.
  rewrite revlcons_len_plus.
  omega.
Qed.

Inductive evalexprlist' : exprlist -> typelist -> vallist -> smem ->  Prop :=
     |  evalexprlist_b :  forall m,  evalexprlist' nil nil nil m
     |  evalexprlist_i : forall e el t tl v vl  m, evalval e m = Some v -> 
                             evaltype e m = Some t -> v<>Vundef -> evalexprlist' el tl vl m -> 
                             evalexprlist' (cons e  el) (cons t  tl) (cons v  vl) m . 

Lemma evalexprlist_imply_evalexprlist' : forall el tl vl m , evalexprlist el tl vl m -> 
                                                             evalexprlist' el tl vl m.
Proof.

  inductions el; introv Heval; destruct tl ; destruct vl; tryfalse.
  constructors.
  simpl in Heval.
  destruct Heval as (Hev & Het &  Hexpr).
  constructors; eauto.
  apply Hexpr.
  apply IHel;eauto.
  apply Hexpr.
Qed.

Lemma evalexprlist'_imply_evalexprlist : forall el tl vl m , evalexprlist' el tl vl m -> 
                                                             evalexprlist el tl vl m.
Proof.
  inductions el; introv Heval; destruct tl ; destruct vl; 
  auto; inverts Heval;  tryfalse.
  simpl ; auto.
  simpl.
  splits; auto.
Qed.

Lemma mapstoval_exist :
  forall l t v b, exists m, mapstoval l t b v m.
Proof.
  intros.
  unfold mapstoval.
  cut (exists vl, encode_val t v = vl).
  intros.
  destruct H.
  cut (exists m, ptomvallist l b x m).
  intros.
  destruct H0.
  eauto.
  clear.
  gen l.
  induction x; intros; simpl.
  eauto.
  destruct l.
  lets H100 : IHx (b0, (o + 1)%Z); destruct H100.
  unfold ptomval.
  do 3 eexists; mytac; eauto.
  apply join_merge_disj.

  Lemma ptomvallist_get_none' :
    forall b0 b o i vl M,
      (i >= 1)%Z ->
      ptomvallist (b0, (o + i)%Z) b vl M ->
      get M (b0, o) = None.
  Proof.
    intros.
    gen b b0 o i M.
    induction vl; intros; simpl in *.
    subst.
    apply emp_sem.
    mytac.
    lets H100 : mem_join_disjoint_eq_merge H0; mytac.
    (* unfold ptomval in H1; subst x. *)
    (* Lemma lmachlib_map1 : *)
    (*   forall (A B T : Type) (MC : PermMap A B T) x x0, *)
    (*     disjoint (sig a b) x0 -> *)
    (*     join (sig a b) x0 (merge (sig a b) x0) -> *)
    (*     get (merge (sig a b) x0)  *)
    
    rewrite merge_semp; auto.
    unfold ptomval in H1; subst x.
    rewrite get_sig_none.
    rewrite IHvl with (i := (i + 1)%Z) (b := b).
    auto.
    omega.
    rewrite <- Zplus_assoc_reverse; auto.
    intro.
    inverts H1.
    gen H H5; clear; intros.
    rewrite <- Z.add_0_r in H5.
    apply Z.add_cancel_l in H5.
    omega.
  Qed.

  lets Hx: ptomvallist_get_none' H.
  omega.
  
  eapply get_none_disjoint_sig; auto.
  eexists. auto.
Qed.


Lemma allocb_nindom :
  forall m b i1 i2 n,
    fresh m b -> (i1 < i2)%Z -> ~ indom (allocb m b i2 n) (b, i1).
Proof.
  intros.
  gen i1 i2.
  inductions n; intros.
  simpl.
  intro.
  unfold fresh in H.
  unfold not in H.
  eapply H.
  auto.
  apply H1.
  simpl.
  pose proof (IHn H). clear IHn H.
  pose proof (H1 i1 (i2 + 1)%Z).
  assert (i1 < (i2 + 1))%Z.
  omega.
  pose proof (H H2).
  clear H1 H H2.
  intro.
  apply H3. clear H3.
  unfold indom in *.
  destruct H.
  rewrite set_a_get_a' in H.
  eauto.
  intro; inverts H1.
  omega.
Qed.


Lemma join_mapstoval_allocb' :
  forall m b t M i,
    fresh m b ->
    mapstoval (b, i) t true Vundef M ->
    join m M (allocb m b i (typelen t)).
Proof.
  intros.
  unfold mapstoval in H0.
  destruct H0.
  destruct H0.
  simpl in H0.
  subst.
  gen m b M i. 

  induction (typelen t); intros.
  simpl in H1.
  subst.
  simpl.
  apply join_comm.
  apply join_emp.
  auto.

  simpl in H1.
  destruct H1.
  do 2 destruct H0.
  destruct H1.
  pose proof (IHn m b H x0 (i+1)%Z H2). clear IHn.
  simpl.
  unfold ptomval in H1.
  subst. clear H2. clears.
  assert (M = set x0 (b, i) (true, Undef)).
  eapply extensionality.
  intros.

  assert (a = (b, i) \/ a <> (b, i)) by tauto.
  destruct H1.
  substs.
  rewrite set_a_get_a.

  eapply mem_join_sig_true_get_l; eauto.
  rewrite set_a_get_a'; auto.

  eapply mem_join_sig_true_get_eq; eauto.

  subst.
  assert (~indom (allocb m b (i+1) n) (b, i)).
  eapply allocb_nindom.
  auto.
  omega.

  eapply join_set_nindom_r.
  apply H3.
  auto.
  auto.
  auto.
Qed.


Lemma join_mapstoval_allocb :
  forall m b t M,
    fresh m b ->
    mapstoval (b,0%Z) t true Vundef M ->
    join m M (allocb m b 0 (typelen t)).
Proof.
  intros.
  eapply join_mapstoval_allocb'.
  auto.
  auto.
Qed.

Lemma length_list_repeat : forall (A : Type) len (v : A), length (list_repeat len v) = len.
Proof.
  intros.
  induction len.
  simpl.
  auto.
  simpl.
  eauto.
Qed.


Lemma storebytes_memjoin :
  forall vl m M m' b len i,
    fresh_index m b i -> storebytes (allocb m b i len) (b, i%Z) vl = Some m' ->
    length vl = len -> ptomvallist (b, i%Z) true vl M -> join m M m'.
Proof.
  intro.
  inductions vl; intros.

  simpl in H0.
  simpl in H1.
  subst.
  simpl in H0.
  inversion H0.
  simpl in H2.
  subst.
  apply join_comm.
  apply join_emp.
  auto.

  simpl in H1.
  destruct len.
  false.
  inversion H1. clear H1.
  simpl in H0.
  rewrite set_a_get_a in H0.
  destruct (storebytes (set (allocb m b (i + 1) len) (b, i) (true, Undef))
                       (b, (i + 1)%Z) vl) eqn : eq1; tryfalse.
  change offset with Z in eq1.

  rewrite memset_allocb_comm in eq1.
  assert (fresh_index (set m (b, i) (true, Undef)) b (i + 1)%Z).
  unfold fresh_index.
  intros.
  rewrite set_a_get_a'.
  unfold fresh_index in H.
  rewrite <- Zplus_assoc.
  apply H.
  omega.
  intro.
  inversion H3.
  assert (i < (i + 1 + offset))%Z.
  omega.
  rewrite <- H6 in H5.
  omega.
  
  simpl in H2.
  do 3 destruct H2.
  destruct H3.
  
  pose proof (IHvl (set m (b, i) (true, Undef)) x0 m0 b len (i + 1)%Z H1 eq1 H4 H5).
  clear IHvl.

  assert (join m (set x0 (b, i) (true, Undef)) m0).
  assert (get m (b, i) = None).
  clear - H.
  unfolds in H.
  pose proof H 0%Z.
  assert (0 >= 0)%Z.
  omega.
  apply H0 in H1.
  replace (i + 0)%Z with i in H1.
  auto.
  rewrite Z.add_0_r; auto.

  eapply mem_join_set_true_comm; eauto.

  inversion H0.
  subst.
  unfold ptomval in H3.
  subst.

  apply join_comm in H2.
  assert (M = set x0 (b, i) (true, a)).
  eapply extensionality.
  intro.
  assert ((b, i) = a0 \/ (b, i) <> a0) by tauto.
  destruct H3.
  substs.
  rewrite set_a_get_a.
  eapply mem_join_get_get_r_true; eauto.
  rewrite get_sig_some; auto.

  rewrite set_a_get_a'; auto.
  eapply join_comm in H2.
  eapply mem_join_sig_true_get_eq; eauto.

  apply join_comm in H2.
  eapply mem_join_get_none'; eauto.

  inverts H0.
  unfolds in H3.
  substs.
  assert (M = set x0 (b, i) (true, a)).
  eapply mem_sig_true_set_eq; eauto.
  substs.
  
  assert (set x0 (b, i) (true, a) = set (set x0 (b, i) (true, Undef)) (b, i) (true, a)).
  rewrite mem_set_a_set_a; auto.
  rewrite H0.
  apply join_comm.
  eapply mem_join_set_true_join.
  apply join_comm in H7; auto.
  rewrite set_a_get_a; auto.
  omega.
Qed.


Lemma join_mapstoval_store_allocb :
  forall m b t v M m',
    fresh m b ->
    mapstoval (b,0%Z) t true v M ->
    store t (allocb m b 0 (typelen t)) (b, 0%Z) v = Some m'->
    join m M m'.
Proof.
  intros.
  unfold mapstoval in H0.
  destruct H0.
  destruct H0.
  unfold store in H1.
  pose proof storebytes_memjoin.
  assert (fresh_index m b 0%Z).
  apply fresh_implies_fresh_index.
  auto.
  eapply H3; eauto.
  apply encode_val_length.
  subst.
  auto.
Qed.


Lemma allocb_storebytes_some :
  forall vl m b i len,
    fresh_index m b i -> 
    length vl = len ->
    exists m', storebytes (allocb m b i len) (b, i) vl = Some m'.
Proof.
  intro.
  induction vl; intros.
  simpl in H0.
  subst.
  simpl.
  exists m.
  auto.

  simpl in H0.
  destruct len.
  false.
  inversion H0.
  simpl.
  rewrite set_a_get_a.
  rewrite memset_allocb_comm.
  pose proof (IHvl (set m (b, i) (true, Undef)) b (i + 1)%Z len).
  assert (fresh_index (set m (b, i) (true, Undef)) b (i + 1)%Z).
  unfold fresh_index.
  intros.
  rewrite set_a_get_a'.
  rewrite <- Zplus_assoc.
  eapply H.
  omega.
  intro.
  inversion H4.
  rewrite<-Z.add_assoc in H6.
  assert (1 + offset > 0)%Z.
  omega.
  assert (i < (i + (1 + offset)))%Z.
  omega.
  rewrite <- H6 in H7.
  omega.

  pose proof (H1 H3 H2).
  subst.
  destruct H4.
  change offset with Z in H2.
  rewrite H2.
  eexists.
  auto.
  omega.
Qed.

Lemma storebytes_indom :
  forall M l vl M' l',
    storebytes M l vl = Some M' ->
    indom M l'->
    indom M' l'.
Proof.
  intros.
  gen M l M' l'.
  induction vl.
  intros.
  simpl in H.
  inverts H.
  auto.
  intros.
  destruct l.
  simpl in H.
  unfold get in H; simpl in H.
  destruct (HalfPermMap.get M (b, o));tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  remember (storebytes M (b, (o + 1)%Z) vl) as M1.
  destruct M1;tryfalse.
  symmetry in HeqM1.
  lets HH: IHvl HeqM1 l'.
  inverts H.
  apply HH in H0.
  eapply get_indom.
  assert ((b, o) = l' \/ (b, o) <> l') by tauto.
  destruct H.
  substs.
  rewrite set_a_get_a; eauto.
  rewrite set_a_get_a'; eauto.
Qed.

Lemma storebytes_indom_true :
  forall M l vl M' l',
    storebytes M l vl = Some M' ->
    (exists x, get M l' = Some (true, x)) ->
    (exists x, get M' l' = Some (true, x)).
Proof.
  intros.
  gen M l M' l'.
  induction vl.
  intros.
  simpl in H.
  inverts H.
  auto.
  intros.
  destruct l.
  simpl in H.
  unfold get in H; simpl in H.
  destruct (HalfPermMap.get M (b, o));tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  remember (storebytes M (b, (o + 1)%Z) vl) as M1.
  destruct M1;tryfalse.
  symmetry in HeqM1.
  lets HH: IHvl HeqM1 l'.
  inverts H.
  apply HH in H0.

  assert ((b, o) = l' \/ (b, o) <> l') by tauto.
  destruct H.
  substs.
  rewrite set_a_get_a; eauto.
  rewrite set_a_get_a'; eauto.
Qed.


Lemma storebytes_ptomvallist_frame :
  forall b o vl1 vl2 M1 M2 M12 M12',
    ptomvallist (b,o) true vl1 M1 ->
    join M1 M2 M12 ->
    storebytes M12 (b,o) vl2 = Some M12' ->
    length vl1 = length vl2 ->
    exists M1',storebytes M1 (b,o) vl2 = Some M1' /\ join M1' M2 M12'.
Proof.
  intros.
  gen o vl1 M12' M1 M2 M12.
  induction vl2.
  intros.
  eexists. 
  simpl in *;split;eauto.
  inverts H1;eauto.

  intros.
  simpl in *.
  unfold get in H1; simpl in H1.
  remember (HalfPermMap.get M12 (b, o)) as v12.
  destruct v12;tryfalse.
  destruct b0.
  destruct b0; tryfalse.
  destruct vl1.
  inverts H2.

  simpl in H.
  do 2 destruct H.
  destructs H.
  unfold get; simpl.
  remember (HalfPermMap.get M1 (b,o)) as v1.
  unfold ptomval in H3.
  rewrite H3 in H.
  assert (get M1 (b, o) = Some (true, m)) as Hget.
  eapply mem_join_get_get_l_true; eauto.
  rewrite get_sig_some; auto.

  unfold get in Hget; simpl in Hget.
  rewrite Hget in Heqv1;eauto.
  rewrite Heqv1.
  
  remember (storebytes M12 (b, (o + 1)%Z) vl2 ) as M12''.
  destruct M12''; tryfalse.
  symmetry in HeqM12''.
  simpl in H2.
  injection H2.
  intros.

  apply join_comm in H.
  lets Hjoin' : join_assoc_l H H0.
  destruct Hjoin'.
  destruct H6.

  lets Hs : IHvl2  HeqM12''.
  2:eauto.
  2:eauto.
  auto.
  destruct Hs.
  destruct H8.
  lets Hs : storebytes_mono H8.
  eapply H.
  destruct Hs.
  change Z with offset.
  rewrite H10.

  eexists; splits; eauto.
  inverts H1.
  
  eapply mem_join_set_true_join'.
  eapply join_storebytes.
  2:apply H10.
  2:apply HeqM12''.
  auto.
  
  eapply storebytes_indom_true;eauto.
Qed.



Lemma store_mapstoval_frame :  
  forall M1 M2 M12 M12' l t v1 v2,    
    mapstoval l t true v1 M1 ->    
    join M1 M2 M12 ->  
    store t M12 l v2 = Some M12' ->    
    exists M1', store t M1 l v2 = Some M1' /\ join M1' M2 M12'.
Proof.
  intros.
  destruct l.
  unfold store in *.
  unfold mapstoval in H. 
  mytac.
  eapply storebytes_ptomvallist_frame;eauto.
  repeat erewrite encode_val_length.
  auto.
Qed.


Lemma ptomvallist_get_none :
  forall l b i1 i2 m,
    (i2 < i1)%Z ->
    ptomvallist (b, i1) true l m ->
    get m (b, i2) = None.
Proof.
  intro.
  inductions l; intros.
  simpl in H0.
  subst.
  apply emp_sem.

  simpl in H0.
  do 3 destruct H0.
  destruct H1.
  assert (i2 < i1 + 1)%Z.
  omega.
  pose proof (IHl b (i1 + 1)%Z i2 x0 H3 H2).
  unfolds in H1.
  assert (get x (b, i2) = None).
  subst.
  apply get_sig_none.
  intro.
  inversion H1.
  substs.
  omega.
  lets Hx: mem_join_get_none H5 H4 H0; auto.
Qed.


Lemma storebytes_ptomvallist_eqlen_infer :
  forall M1 M2 b o l1 l2,
    ptomvallist (b, o) true l1 M1 ->
    length l1 = length l2 ->
    storebytes M1 (b, o) l2 = Some M2 ->
    ptomvallist (b, o) true l2 M2.
Proof.
  intros.
  gen l1 l2 M1 M2 b o.
  induction l1, l2; intros; simpl in *; mytac; tryfalse.
  inverts H1; auto.
  inverts H0.
  assert (get M1 (b, o) = Some (true, a)) as H100.
  eapply mem_join_get_get_l_true; eauto.
  unfold ptomval in H2; subst x; apply get_sig_some.
  unfold get in H100, H1; simpl in H100, H1.
  rewrite H100 in H1; clear H100.
  remember (storebytes M1 (b, (o + 1)%Z) l2) as m100; destruct m100; tryfalse.
  symmetry in Heqm100.
  inversion H1; clear H1.
  lets H100 : IHl1 H5; clear IHl1; rename H100 into IHl1.

  apply join_comm in H.
  lets H100 : storebytes_ptomvallist_frame H3 H H5.
  eauto.
  mytac.
  lets H100 : IHl1 H3 H0.
  do 2 eexists; mytac.
  3 : eauto.
  2 : unfold ptomval; auto.
  gen H1 H2 H100; clear; intros.

  unfolds in H2; substs.
  apply join_comm in H1.
  assert (sig (b, o) (true, m) = set (sig (b, o) (true, a)) (b, o) (true, m)).

  symmetry.
  eapply set_sig_eq.
  unfold sig in *; simpl in *.
  rewrite H.
  eapply mem_join_set_true_join; eauto.
  rewrite get_sig_some; eauto.
Qed.


Lemma store_mapstoval_frame1 :  
  forall M1 M2 M12 M12' l t v1 v2,    
    mapstoval l t true  v1 M1 ->    
    join M1 M2 M12 ->  
    store t M12 l v2 = Some M12' ->    
    exists M1', mapstoval l t true v2 M1' /\ store t M1 l v2 = Some M1' /\ join M1' M2 M12'.
Proof.
  intros.
  lets H100 : store_mapstoval_frame H H0 H1; mytac.
  cut (mapstoval l t true v2 x).
  intros; eexists; mytac; eauto.
  gen H H2; clear; intros.
  unfold mapstoval in *; mytac.
  unfold store in *.
  destruct l.
  eexists; mytac; auto.
  eapply storebytes_ptomvallist_eqlen_infer; eauto.
  repeat rewrite encode_val_length; auto.
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

Open Local Scope nat_scope.
Lemma length_prop : forall (vl:vallist) tl d1 d2, length vl = length tl -> tlmatch (rev tl) d1 -> 
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

Lemma eval_length_rev : forall  (tl:typelist) (vl:vallist)  ,  length vl = length tl ->  length (rev vl) = length (rev tl).
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

Lemma len_rev: forall (vl:vallist)( tl:typelist) , length vl = length tl  -> length vl = length (rev tl).
Proof.
  inductions vl ; inductions tl; auto || tryfalse.
  introv Hf.
  simpl in Hf.
  tryfalse.
  introv Hf.
  simpl. 
  simpl in Hf.
  assert (length vl = length tl); intuition.
  lets Hre : IHvl H.
  rewrite app_length.
  simpl.
  omega.
Qed.

Lemma evaltype_eq_prop : forall G E M1 M2 e t, evaltype e (G,E, M1) = Some t ->
               evaltype e (G,E,M2) = Some t.
Proof.
  intros.
  erewrite evaltype_irrev_mem;eauto.
Qed.


Lemma load_mem_mono :
  forall t M M' a v,
    load t M a = Some v ->
    Maps.sub M M' ->
    load t M' a = Some v.
Proof.
  intros.
  rewrite <- H.
  lets Hj :join_sub_minus M' M.
  apply Hj in H0.
  eapply load_mono;eauto.
Qed.


Lemma evalval_eq_prop :
  forall e G E M M' v,
    evalval e (G, E, M) = Some v ->
    Maps.sub M M' ->
    evalval e (G, E, M') = Some v.
Proof.
  intros.
  rewrite<-H.
  lets Hj :join_sub_minus M' M.
  apply Hj in H0.
  eapply evalval_mono;eauto.
Qed.


Lemma evaltype_deter :
  forall G E M1 M2 e t1 t2,
    evaltype e (G, E, M1) = Some t1 ->
    evaltype e (G, E, M2) = Some t2 ->
    t1 = t2.
Proof.
  intros.
  eapply evaltype_eq_prop in H.
  rewrite H in H0.
  inv H0.
  auto.
Qed.

Lemma evalval_deter :
  forall G E M1 M2 e v1 v2,
    evalval e (G, E, M1) = Some v1 ->
    evalval e (G, E, M2) = Some v2 ->
    Maps.sub M1 M2 ->
    v1 = v2.
Proof.
  intros.
  eapply evalval_eq_prop in H.
  rewrite H in H0.
  inv H0.
  auto.
  auto.
Qed.

Lemma load_mem_deter :
  forall t M1 M2 a v1 v2,
    load t M1 a = Some v1 ->
    load t M2 a = Some v2 ->
    Maps.sub M1 M2 ->
    v1 = v2.
Proof.
  intros.
  eapply load_mem_mono in H.
  rewrite H in H0.
  inv H0.
  auto.
  auto.
Qed.

Close Scope nat_scope.
Close Scope Z_scope.


