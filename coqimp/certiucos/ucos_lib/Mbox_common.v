Require Import include_frm.
Require Import math_auto.
Require Import ucos_include.
Require Import os_ucos_h.
Require Import OSTimeDlyPure.

Require Import OSQPostPure.
Local Open Scope code_scope.

Import DeprecatedTactic.

(* Local Ltac mytac := simpljoin;
 *     match goal with
 *       | |- _ /\ _ =>splits
 *       | _ => idtac
 *     end; subst. *)

(* TODO: move to mathlib *)
Lemma val_inj_eq
     : forall i0 a: int32,
       val_inj
         (notint
            (val_inj
               (if Int.eq i0  a
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
       val_inj
         (notint
            (val_inj
               (if Int.eq i0  a
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) = Vnull ->
       i0 = a.
Proof.
  intros.
  destruct H; intros.
  int auto.
  apply unsigned_inj; auto.
  int auto.
Qed.

(* TODO: move to mathlib *)
Lemma ecbjoin_sig_join'
     : forall (x x1 v'35 x0 : EcbMod.map) (v'61 : block) 
         v3,
       EcbMod.join x x1 v'35 ->
       EcbMod.join x0 (EcbMod.sig (v'61, Int.zero) (v3, nil)) x1 ->
       exists y,
       EcbMod.join x0 x y /\
       EcbMod.join y (EcbMod.sig (v'61, Int.zero) (v3, nil)) v'35.
Proof.
  intros.

  set ( EcbMod.join_assoc_r H0 H).
  mytac.
  exists x2.
  split; auto.
  apply EcbMod.join_comm in H1.
  auto.
Qed.

Lemma joinsig_join_ex_my:
  forall x1 v1 ma mb mab m,
    EcbMod.joinsig x1 v1 mab m ->
    EcbMod.join ma mb mab ->
    exists mm, EcbMod.joinsig x1 v1 ma mm /\ EcbMod.join mm mb m.
Proof.
  intros x1 v1 ma mb mab m.
  unfold EcbMod.joinsig.
  intros F1 F2.
  apply EcbMod.join_assoc_spec_1 with (mab:=mab); trivial.
Qed.

Lemma joinsig_join_ex:
  forall x0 x x1 t x4 x5,
    EcbMod.joinsig x0 x x1 t ->
    EcbMod.join x4 x5 x1 ->
    exists y,  EcbMod.joinsig x0 x x4 y /\  EcbMod.join y x5 t.
Proof.
  intros x0 x x1 t x4 x5.
  apply joinsig_join_ex_my with (mab:=x1).
Qed.  


Lemma get_last_prop:
  forall (l : list EventCtr)  x v y,
    l <> nil -> 
    (get_last_ptr ((x, v) :: l)  =   y <->
     get_last_ptr  l =  y).
Proof.
  destruct l.
  intros.
  tryfalse.
  intros.
  unfolds get_last_ptr.
  simpl.
  destruct l; splits;auto.
Qed.


Lemma ecblist_p_decompose :
  forall  y1 z1  x y2 z2 t z ,
    length y1 = length y2 ->
    ECBList_P x Vnull (y1++z1) (y2++z2) t z ->
    exists x1 t1 t2,
      ECBList_P x x1 y1 y2 t1 z /\ ECBList_P x1 Vnull z1 z2 t2 z /\
      EcbMod.join t1 t2 t /\  (get_last_ptr y1 = None \/ get_last_ptr y1  = Some x1).
Proof.
  inductions y1; inductions y2.
  simpl.
  intros.
  do 3 eexists; splits; eauto.
  eapply EcbMod.join_emp; eauto.
  intros.
  simpl in H.
  tryfalse.
  intros.
  simpl in H; tryfalse.
  intros.
  simpl in H.
  inverts H.
  simpl in H0.
  mytac.
  destruct a.
  mytac.
  lets Hx : IHy1 H2 H4.
  mytac.
  lets Hex : joinsig_join_ex H1 H7.
  mytac.
  do 3 eexists.
  splits.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits.
  eauto.
  2: eauto.
  3: eauto.
  2 : eauto.
  eauto.
  eauto.
  assert (y1 = nil \/ y1 <> nil) by tauto.
  destruct H11.
  subst y1.  
  right.
  simpl in H2.
  apply eq_sym in H2.
  apply length_zero_nil in H2.
  subst y2.
  simpl in H5.
  mytac.
  unfolds.
  simpl.
  auto.
  destruct H8.
  left.
  eapply  get_last_prop in H11.
  eapply H11; eauto.
  eapply  get_last_prop in H11.
  right.
  eapply H11; eauto.
Qed.  


Lemma  ecb_joinsig_ex_split:
  forall x x0 x1 ecbls x3 x4,
    EcbMod.joinsig x x0 x1 ecbls ->
    EcbMod.join x3 x4 x1 ->
    exists y, EcbMod.joinsig x x0 x3 y /\ EcbMod.join y x4 ecbls.
Proof.
  intros.
  exists (EcbMod.minus ecbls x4).
  split.
  unfolds; intro.
  pose proof H a.
  pose proof H0 a.
  destruct(tidspec.beq x a) eqn:eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some.
  rewrite EcbMod.get_sig_some in H1.
  rewrite EcbMod.minus_sem.
  destruct( EcbMod.get x3 a);
  destruct( EcbMod.get x4 a);
  destruct( EcbMod.get x1 a);
  destruct( EcbMod.get ecbls a);
  tryfalse; substs; auto.
  apply tidspec.beq_false_neq in eq1.
  rewrite EcbMod.get_sig_none; auto.
  rewrite EcbMod.get_sig_none in H1; auto.
  rewrite EcbMod.minus_sem.
  destruct( EcbMod.get x3 a);
  destruct( EcbMod.get x4 a);
  destruct( EcbMod.get x1 a);
  destruct( EcbMod.get ecbls a);
  tryfalse; substs; auto.

  intro.
  pose proof H a.
  pose proof H0 a.
  rewrite EcbMod.minus_sem.
  destruct(tidspec.beq x a) eqn:eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H1.
  destruct( EcbMod.get x3 a);
  destruct( EcbMod.get x4 a);
  destruct( EcbMod.get x1 a);
  destruct( EcbMod.get ecbls a);
  tryfalse; substs; auto.
  
  apply tidspec.beq_false_neq in eq1.
  rewrite EcbMod.get_sig_none in H1; auto.
  destruct( EcbMod.get x3 a);
  destruct( EcbMod.get x4 a);
  destruct( EcbMod.get x1 a);
  destruct( EcbMod.get ecbls a);
  tryfalse; substs; auto.
Qed.

Lemma ecblist_p_decompose':
  forall l1 ll1 l2 ll2 head ecbls tcbls,
    length l1 = length ll1 ->
    ECBList_P head Vnull
              (l1++
                 l2) (ll1 ++ ll2) ecbls tcbls ->
    exists ecbls1 ecbls2 x,
      ECBList_P head x l1 ll1 ecbls1 tcbls /\
      ECBList_P x Vnull l2 ll2 ecbls2 tcbls /\
      EcbMod.join ecbls1 ecbls2 ecbls.
Proof.
  inductions l1.
  simpl.
  intros.
  destruct ll1.
  simpl in H0.
  do 3 eexists;splits; eauto.
  eapply EcbMod.join_emp; auto.
  simpl in H.
  tryfalse.
  intros.
  destruct ll1.
  simpl in H.
  tryfalse.
  simpl in H.
  assert (length l1 = length ll1) by omega.
  simpl in H0.
  mytac.
  destruct a.
  mytac.
  lets Hxs : IHl1 H1 H5.
  mytac.
  lets Hsx :     ecb_joinsig_ex_split H3 H8.
  mytac.
  exists x6 x4 x5.
  simpl.
  splits.
  eexists.
  splits; eauto.
  do 3 eexists.
  splits; eauto.
  auto.
  auto.
Qed.

(* similar to eventtype_neq_q in common.v *)
Local Open Scope list_scope.
Local Open Scope int_scope.
Lemma eventtype_neq_mbox:
  forall v'38 v'21 i1 i0 i2 x2 x3 v'42 v'40 v'22 v'23 v'41 v'24 v'34 v'35 v'49 s P v'43 v'45 v'44 v'46,
    length v'21 = length v'23-> 
    ECBList_P v'38 Vnull
              (v'21 ++
                    ((Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil,
                      v'40) :: nil) ++ v'22) (v'23 ++ (v'41 :: nil) ++ v'24) v'34 v'35 ->
    ECBList_P v'38 (Vptr (v'49, Int.zero)) v'21 v'23 v'43 v'35 ->
    EcbMod.join v'43 v'45 v'34 ->
    EcbMod.joinsig (v'49, Int.zero) v'46 v'44 v'45 ->
    false = Int.eq i1 ($  OS_EVENT_TYPE_MBOX) ->
    s|= AEventData
     (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil) v'41 ** P ->
    s |= AEventData
      (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil) v'41 **
      [|~ exists x z, EcbMod.get v'34 (v'49,Int.zero) = Some (absmbox x, z) |] ** P.
Proof.
  intros.

  apply ecblist_p_decompose' in H0;auto.
  mytac.
 
  assert (x1 = Vptr (v'49, Int.zero) /\ x = v'43).
  eapply ecblist_p_eqh;eauto.
  instantiate (1:=v'34).
  eapply EcbMod.join_sub_l;eauto.
  eapply EcbMod.join_sub_l;eauto.
  destruct H8;subst.
  destruct v'41.
  Focus 3.
  unfold AEventData in *.
  sep normal in H5.
  sep split in H5.
  unfolds in H8;simpl in H8.
  inverts H8.
  rewrite Int.eq_true in H4;tryfalse.
  sep auto.
  simpl in H6.
  simpljoin.
  destruct x1.
  destruct e;tryfalse.
  simpljoin.
  intro.
  simpljoin.
  inverts H6.
  lets Hx:EcbMod.join_joinsig_get H7 H10.
  rewrite H16 in Hx.
  tryfalse.
  sep auto.
  simpl in H6.
  mytac.
  destruct x1.
  destruct e;tryfalse.
  mytac.
  intro.
  mytac.
  inverts H6.
  lets Hx:EcbMod.join_joinsig_get H7 H10.
  rewrite H11 in Hx.
  tryfalse.
  sep auto.
  simpl in H6.
  mytac.
  destruct x1.
  destruct e;tryfalse.

  mytac.
  intro.
  mytac.
  inverts H6.
  lets Hx:EcbMod.join_joinsig_get H7 H10.
  rewrite H14 in Hx.
  tryfalse.
Qed.


Lemma eventtype_neq_mbox':
  forall v'38 v'21 i1 i0 i2 x2 x3 v'42 v'40 v'22 v'23 v'41 v'24 v'34 v'35 v'49 s P v'43 v'45 v'44 v'46,
    length v'21 = length v'23-> 
    ECBList_P v'38 Vnull
              (v'21 ++
                    ((Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil,
                      v'40) :: nil) ++ v'22) (v'23 ++ (v'41 :: nil) ++ v'24) v'34 v'35 ->
    ECBList_P v'38 (Vptr (v'49, Int.zero)) v'21 v'23 v'43 v'35 ->
    EcbMod.join v'43 v'45 v'34 ->
    EcbMod.joinsig (v'49, Int.zero) v'46 v'44 v'45 ->
    false = Int.eq i1 ($  OS_EVENT_TYPE_MBOX) ->
    s|= AEventData
     (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil) v'41 ** P ->
    s |= AEventData
      (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'42 :: nil) v'41 **
      [| exists d, EcbMod.get v'34 (v'49,Int.zero) = Some d /\ (~exists x z, d= (absmbox x, z)) |] ** P.
  intros.
  lets aaa : eventtype_neq_mbox H5; eauto.
  clear H5.
  sep auto.
  eexists.
  assert ( EcbMod.get v'34 (v'49, Int.zero) = Some v'46).
  eapply EcbMod.join_get_get_r.
  eauto.
  eapply EcbMod.join_get_get_l.
  eauto.
  eapply EcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
  split.
  eauto.
  intro.
  rewrite H6 in H5.
  apply H5.
  inversion H7.
  inversion H8.
  exists x x0.
  rewrite H9.
  auto.
Qed.  
Lemma length8_ex:
  forall v'40 :vallist,
    length v'40 = ∘OS_EVENT_TBL_SIZE ->
    exists v1 v2 v3 v4 v5 v6 v7 v8,
      v'40 = v1::v2::v3::v4::v5::v6::v7::v8::nil.
Proof.
  introv Hlen.
  try do 8  (destruct v'40; simpl in Hlen; tryfalse).
  do 8 eexists; eauto.
  assert (length v'40 = 0)%nat.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  inverts Hlen.
  auto.
  assert (v'40 = nil).
  destruct v'40.
  auto.
  simpl in H; tryfalse.
  subst.
  eauto.
Qed.

Lemma ecblist_ecbmod_get_aux_mbox :
  forall v'61 i6  x4 x8 v'58 v'42  
         v'63 x20 v'37 v'35 v'36 v'38,
    array_type_vallist_match Int8u v'58->
    RH_CurTCB v'38 v'36 ->
    length v'58 = ∘OS_EVENT_TBL_SIZE ->
    RH_TCBList_ECBList_P v'35 v'36 v'38 ->
    RL_Tbl_Grp_P v'58 (V$0) ->
    ECBList_P (Vptr (v'61, Int.zero)) Vnull
              (
                   ((V$OS_EVENT_TYPE_MBOX
                      :: V$0 :: Vint32 i6 :: v'63 :: x4 :: x8 :: nil,
                     v'58) :: nil) ++ v'42)
                                       ((DMbox x20 :: nil) ++ v'37) v'35 v'36 ->
    exists msgls,
      EcbMod.get v'35 (v'61, Int.zero) = Some (absmbox msgls , nil)
    /\ exists vv,  EcbMod.join vv  (EcbMod.sig (v'61, Int.zero) (absmbox msgls, nil)) v'35 /\ECBList_P x8 Vnull v'42 v'37  vv  v'36.
Proof.
  introv  Harr Hcur Hrl Htcb Hre Hep.
  unfolds in Hre.
  assert (forall n, (0 <= n < 8)%nat  ->  nth_val n v'58 = Some (Vint32 ($ 0))).
  intros.
  lets Hex : n07_arr_len_ex H  Harr Hrl.
  destruct Hex as (vh & Hnth & Hneq).
  assert (V$0 = V$0) as Hasrt by auto.
  lets Hres : Hre H Hnth Hasrt.
  destruct Hres as (Hrs1 & Hrs2).
  destruct Hrs1 as (Hrs11 & Hrs22).
  rewrite Int.and_zero_l in Hrs11.
  assert (vh = $ 0) .
  apply Hrs11.
  auto.
  subst vh.
  auto.
  simpl in Hep.
  destruct Hep as (qid & Heq & Heb & Hex).
  destruct Hex as (absmq & mqls' & v' & Hv & Hej & Hmt & Hlp).
  destruct absmq.
  destruct e; tryfalse.
  usimpl Hv.
  inverts Heq.
  destruct Hmt as (Hm1 & Hm2 ). (* & Hm3 & Hm4). *)
  mytac.
  exists m.
  assert (w = nil \/ w <> nil) by tauto.
  destruct H0 as [Hnil | Hnnil].
  Focus 2.
  unfolds in Hcur.
  unfolds in Htcb.
  destruct Htcb as (Htcb1&Htcb2&Htcb3&Htcb4).
  lets Hj : ecbmod_joinsig_get Hej.
  lets Hea : qwaitset_notnil_ex Hnnil.
  destruct Hea as (tid & Hin).
  assert ( EcbMod.get v'35 (v'61, Int.zero) = Some (absmbox m, w) /\ In tid w) by (split; auto).
  destruct Htcb3 as (Htb & Htb2).
  lets Hjj : Htb H0.
  destruct Hjj as (prio & m0 & n & Htcg).
  unfolds in Heb.
  destruct Heb as (Heb1 & Heb2 & _).
  unfolds  in Heb2.
  destruct Heb2 as (Heba & Hebb & Hebc & Hebd).
  lets Hebs : Hebc Htcg.
  lets Hbb : prioinq_exists Hebs.
  destruct Hbb as (n0 & Hnn & Hnth).
  lets Hfs : H Hnn.
  tryfalse.
  subst w.
  split.
 
  eapply ecbmod_joinsig_get; eauto.
  eexists; splits; eauto.
 
  eapply  ecbmod_joinsig_sig; eauto.
Qed.


Lemma ecblist_ecbmod_get_mbox :
  forall v'61 i6  x4 x8 v'58 v'42 v'21 v'63 x20 v'37 v'35 v'36 v'38,
    length v'21 = O  ->
    array_type_vallist_match Int8u v'58->
    RH_CurTCB v'38 v'36 ->
    length v'58 = ∘OS_EVENT_TBL_SIZE ->
    RH_TCBList_ECBList_P v'35 v'36 v'38 ->
    RL_Tbl_Grp_P v'58 (V$0) ->
    ECBList_P (Vptr (v'61, Int.zero)) Vnull
              (nil ++
                   ((V$OS_EVENT_TYPE_MBOX
                      :: V$0 :: Vint32 i6 :: v'63 :: x4 :: x8 :: nil,
                     v'58) :: nil) ++ v'42)
              (v'21 ++
                    (DMbox x20 :: nil) ++ v'37) v'35 v'36 ->
    exists msgls,
      EcbMod.get v'35 (v'61, Int.zero) = Some (absmbox msgls, nil)
      /\ exists vv,  EcbMod.join vv  (EcbMod.sig (v'61, Int.zero) (absmbox msgls , nil)) v'35 /\ECBList_P x8 Vnull v'42 v'37  vv  v'36.
Proof.
  introv Hlen Harr Hcur Hrl Htcb Hre Hep.
  destruct v'21.
  2 : simpl in Hlen; tryfalse.
  rewrite app_nil_l in Hep.
  rewrite app_nil_l in Hep.
  eapply ecblist_ecbmod_get_aux_mbox;eauto.
Qed.

(* the following two lemmas are in OSQDelPure.v *)

(* in common.v there's a lemma have the same name. but they have small differences *)
Lemma ecblist_p_decompose'' :
  forall  y1 z1  x y2 z2 t z ,
    length y1 = length y2 ->
    ECBList_P x Vnull (y1++z1) (y2++z2) t z ->
    exists x1 t1 t2,
      ECBList_P x x1 y1 y2 t1 z /\ ECBList_P x1 Vnull z1 z2 t2 z /\
      EcbMod.join t1 t2 t /\  (get_last_ptr y1 = None \/ get_last_ptr y1  = Some x1).
Proof.
  inductions y1; inductions y2.
  simpl.
  intros.
  do 3 eexists; splits; eauto.
  eapply EcbMod.join_emp; eauto.
  intros.
  simpl in H.
  tryfalse.
  intros.
  simpl in H; tryfalse.
  intros.
  simpl in H.
  inverts H.
  simpl in H0.
  mytac.
  destruct a.
  mytac.
  lets Hx : IHy1 H2 H4.
  mytac.
  lets Hex : joinsig_join_ex H1 H7.
  mytac.
  do 3 eexists.
  splits.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits.
  eauto.
  2: eauto.
  3: eauto.
  2 : eauto.
  eauto.
  eauto.
  assert (y1 = nil \/ y1 <> nil) by tauto.
  destruct H11.
  subst y1.  
  right.
  simpl in H2.
  apply eq_sym in H2.
  apply length_zero_nil in H2.
  subst y2.
  simpl in H5.
  mytac.
  unfolds.
  simpl.
  auto.
  destruct H8.
  left.
  eapply  get_last_prop in H11.
  eapply H11; eauto.
  eapply  get_last_prop in H11.
  right.
  eapply H11; eauto.
Qed.

Local Open Scope Z_scope.

Lemma ecblist_ecbmod_get_mbox' :
  forall v'40 v'52 v'61 i6  x4 x8 v'58 v'42 v'21 xx
         v'63 x20 i5 v'37 v'35 v'36 v'38,
    Some (Vptr (v'61, Int.zero)) = get_last_ptr v'40 ->
    length v'40 = length v'21 ->
    Int.unsigned i5 <= 65535 -> 
    array_type_vallist_match Int8u v'58->
    RH_CurTCB v'38 v'36 ->
    length v'58 = ∘OS_EVENT_TBL_SIZE ->
    RH_TCBList_ECBList_P v'35 v'36 v'38 ->
    RL_Tbl_Grp_P v'58 (V$0) ->
    ECBList_P v'52 Vnull
              (v'40 ++
                    ((V$OS_EVENT_TYPE_MBOX
                       :: xx :: Vint32 i6 :: v'63 :: x4 :: x8 :: nil,
                      v'58) :: nil) ++ v'42)
              (v'21 ++
                                              (DMbox x20 :: nil) ++ v'37) v'35 v'36 ->
 
     exists msgls,
      EcbMod.get v'35 (v'61, Int.zero) = Some (absmbox msgls , nil)
    /\ exists vg vv vx,
         ECBList_P v'52 (Vptr (v'61, Int.zero)) v'40 v'21 vg v'36 /\
         EcbMod.join vg vx v'35/\
         EcbMod.join vv  (EcbMod.sig (v'61, Int.zero) (absmbox msgls, nil)) vx/\
         ECBList_P x8 Vnull v'42 v'37  vv  v'36.
  introv Hsom Hlen Hi Harr Hcur Hrl Htcb Hre Hep.
  lets Hex : ecblist_p_decompose'' Hlen Hep.


  mytac.
  destruct H2.
  rewrite H2 in Hsom; tryfalse.
  rewrite H2 in Hsom ; inverts Hsom.
  unfolds in Hre.
  assert (forall n, (0 <= n < 8)%nat  ->  nth_val n v'58 = Some (Vint32 ($ 0))).
  intros.
  lets Hex : n07_arr_len_ex H3  Harr Hrl.
  destruct Hex as (vh & Hnth & Hneq).
  assert (V$0 = V$0) as Hasrt by auto.
  lets Hres : Hre H3 Hnth Hasrt.
  destruct Hres as (Hrs1 & Hrs2).
  destruct Hrs1 as (Hrs11 & Hrs22).
  rewrite Int.and_zero_l in Hrs11.
  assert (vh = $ 0) .
  apply Hrs11.
  auto.
  subst vh.
  auto.
  simpl in H0.
  destruct H0 as (qid & Heq & Heb & Hex).
  destruct Hex as (absmq & mqls' & v' & Hv & Hej & Hmt & Hlp).
  destruct absmq.
  destruct e; tryfalse.
  usimpl Hv.
  inverts Heq.
  destruct Hmt as (Hm1 & Hm2). (* & Hm3 & Hm4). *)
  assert (w = nil \/ w <> nil) by tauto.
  destruct H0 as [Hnil | Hnnil].
  Focus 2.
  unfolds in Hcur.
  unfolds in Htcb.
  destruct Htcb as (Htcb1&Htcb2&Htcb3&Htcb4).
  lets Hj : ecbmod_joinsig_get Hej.
  lets Hea : qwaitset_notnil_ex Hnnil.
  destruct Hea as (tid & Hin).
  assert ( EcbMod.get x1 (v'61, Int.zero) = Some (absmbox m, w) /\ In tid w) by (split; auto).
  lets Has : EcbMod.join_get_get_r H1 H0.
  assert ( EcbMod.get v'35 (v'61, Int.zero) = Some (absmbox m, w) /\ In tid w) by (split; auto).
  destruct Htcb3 as (Htc & Htc').
  lets Hjj : Htc H4.
  destruct Hjj as (prio & m0 & n & Htcg).
  unfolds in Heb.
  destruct Heb as (Heb1 & Heb2 &  Heb3).
  unfolds  in Heb1.
  unfolds in Heb2.
  destruct Heb2 as (Hebbb & Heb2 & Hebb & Heb4).
  lets Hebs : Hebb Htcg.
  lets Hbb : prioinq_exists Hebs.
  destruct Hbb as (n0 & Hnn & Hnth).
  lets Hfs : H3 Hnn.
  tryfalse.
  subst w.
  exists m.
  split.
  assert (EcbMod.get x1 (v'61, Int.zero) = Some (absmbox m, nil)).
  eapply ecbmod_joinsig_get; eauto.
  eapply EcbMod.join_get_get_r;eauto.
  do 3 eexists; splits; eauto.
  eapply ecbmod_joinsig_sig.
  eauto.
Qed. 

Lemma  ecb_wt_ex_prop_mbox :
  forall
    v'43  v'34 v'38 x v'21 tid
    v'23 v'35 i i3 x2 x3 v'42 v'40,
    Int.eq i ($ 0) = false ->
    Int.unsigned i <= 255 ->
    array_type_vallist_match Int8u v'40 ->
    length v'40 = ∘OS_EVENT_TBL_SIZE ->
    RL_Tbl_Grp_P v'40 (Vint32 i) -> 
    ECBList_P v'38 (Vptr x)  v'21 v'23 v'43 v'35->
    R_ECB_ETbl_P x
                 (V$OS_EVENT_TYPE_MBOX
                   :: Vint32 i
                   :: Vint32 i3 :: x2 :: x3 :: v'42 :: nil,
                  v'40) v'35 ->
    RH_TCBList_ECBList_P v'34 v'35 tid ->
    exists z t' tl,
      EcbMod.get v'34 x = Some (absmbox z, t' :: tl).
Proof.
  introv Hinteq Hiu Harr Hlen  Hrl Hep Hrp Hz.
  unfolds in Hrp.
  unfolds in Hrl.
  lets Hex : int8_neq0_ex Hiu Hinteq.
  destruct Hex as (n & Hn1 & Hn2).
  lets Heu :  n07_arr_len_ex Hn1 Harr Hlen.
  destruct Heu as (vv & Hnth & Hint).
  assert ( Vint32 i = Vint32 i) by auto.
  lets Hed : Hrl Hn1 Hnth H.
  destruct Hed as (Hed1 & Hed2).
  destruct Hed2.
  lets Hed22 : H0 Hn2.
  destruct Hrp as (Hrp1 & Hrp2).
  unfold PrioWaitInQ in Hrp1.
  lets Hexx : prio_inq Hn1 Hed22 Hint Hnth.
  destruct Hexx as (prio & Hpro).
  unfolds in Hrp1.
  destruct Hrp1 as (Hrpa & Hrpb & Hrp1 & Hrpc).
  lets Hxq : Hrp1 Hpro.
  destruct Hxq as (tid' & n0 & m & Hte).
  unfolds; simpl; auto.
  unfolds in Hz.
  destruct Hz as (Hz1 & Hz2 & Hz3 & Hz4).
  destruct Hz3.
  lets Hea : H3 Hte.
  mytac.
  apply  inlist_ex in H5.
  mytac.
  do 3 eexists.
  eauto.
Qed.

  Lemma  Mutex_owner_set: forall x y z t, (~exists aa bb cc, t = (absmutexsem aa bb, cc))->   RH_TCBList_ECBList_MUTEX_OWNER x y ->  RH_TCBList_ECBList_MUTEX_OWNER (EcbMod.set x z t) y.
  Proof.
    intros.
    unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
    intros.
    assert ( eid = z \/ eid <> z).
    tauto.
    elim H2; intros.
    subst eid.
    rewrite EcbMod.set_a_get_a in H1.
    inverts H1.
    false.
    apply H.
    eauto.
    go.

    rewrite EcbMod.set_a_get_a' in H1.
    eapply H0; eauto.
    go.
  Qed.
  

Lemma upd_last_prop:
  forall v g x vl z ,
    V_OSEventListPtr v = Some x ->
    vl = upd_last_ectrls ((v, g) :: nil) z ->
    exists v', vl = ((v', g) ::nil) /\ V_OSEventListPtr v' = Some z.
Proof.
  intros.
  unfolds in H.
  destruct v;simpl in H; tryfalse.
  destruct v0; simpl in H; tryfalse.
  destruct v1; simpl in H; tryfalse.
  destruct v2; simpl in H; tryfalse.
  destruct v3; simpl in H; tryfalse.
  destruct v4; simpl in H; tryfalse.
  inverts H.
  unfold upd_last_ectrls in H0.
  simpl in H0.
  eexists; splits; eauto.
Qed.

(* there's some lemma which has the same name with fixpoint update_nth *)

Local Open Scope list_scope.

Lemma nth_val_upd_prop:
  forall vl n m v x,
    (n<>m)%nat ->
    (nth_val n (ifun_spec.update_nth val m vl v) = Some x  <->
     nth_val n vl  = Some x).
Proof.
  inductions vl.
  intros.
  simpl.
  split;
    intros; tryfalse.
  intros.
  simpl.
  destruct n.
  destruct m.
  tryfalse.
  simpl.
  intros; split; auto.
  destruct m.
  simpl.
  split; auto.
  assert (n <> m) by omega.
  simpl.
  eapply IHvl.
  eauto.
Qed.

Lemma R_ECB_upd_hold :
  forall x1 v v0 v'36 x8,
    R_ECB_ETbl_P x1 (v, v0) v'36 ->
    R_ECB_ETbl_P x1 (ifun_spec.update_nth val 5 v x8, v0) v'36.
Proof.
  introv Hr.
  unfolds in Hr.
  destruct Hr.
  unfolds.
  splits.
  destruct H as (Hr1 & Hr2 & Hr3 & Hr4).
  unfolds in Hr1.
  splits.
  unfolds.
  intros.
  unfolds in H1.
  eapply Hr1; eauto.
  unfolds.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  unfolds in Hr2.
  unfolds.
  intros.
  eapply Hr2; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  unfolds in Hr3.
  unfolds.
  intros.
  eapply Hr3; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  unfolds in Hr4.
  unfolds.
  intros.
  eapply Hr4; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  destruct H0 as (H0 & _).
  destruct H0 as (Hr1 & Hr2 & Hr3 & Hr4).
  unfolds.
  splits.
  unfolds in Hr1.
  unfolds.
  intros.
  apply Hr1 in H0.
  destruct H0.
  split; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  unfolds in Hr2.
  unfolds.
  intros.
  apply Hr2 in H0.
  destruct H0.
  split; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  unfolds in Hr3.
  unfolds.
  intros.
  apply Hr3 in H0.
  destruct H0.
  split; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  unfolds in Hr4.
  unfolds.
  intros.
  apply Hr4 in H0.
  destruct H0.
  split; eauto.
  assert (0<>5)%nat by omega.
  eapply nth_val_upd_prop; eauto.
  destruct H0.
  unfolds in H1.
  unfolds.
  simpl in *.
  unfold V_OSEventType in *.
  destruct H1.
  left.
  eapply nth_val_upd_prop; eauto.
  destruct H1.
  branch 2.
  eapply nth_val_upd_prop; eauto.
  destruct H1.
  branch 3.
  eapply nth_val_upd_prop; eauto.
  branch 4.
  eapply nth_val_upd_prop; eauto.
Qed.


    
Lemma ecb_list_join_join :
  forall v'40  v'52 v'61 v'21 x x2  v'36 x8 v'42 v'37 x0 v'51,
     v'40 <> nil ->
     ECBList_P v'52 (Vptr (v'61, Int.zero)) v'40 v'21 x v'36 ->
     ECBList_P x8 Vnull v'42 v'37 x0 v'36 ->
     v'51 = upd_last_ectrls v'40 x8 -> 
     EcbMod.join x0 x x2 -> 
     ECBList_P v'52 Vnull (v'51 ++ v'42) (v'21 ++ v'37) x2 v'36.
Proof.
  inductions v'40.
  simpl.
  intros.
  mytac.
  unfold upd_last_ectrls in H.
  simpl in H.
  tryfalse.
  introv Hneq Hep Hepp Hsom Hj.
  assert (v'40 = nil \/ v'40 <> nil) by tauto.
  destruct H.
  subst v'40.
  destruct v'21.
  simpl in Hep.
  mytac; tryfalse.
  simpl in Hep.
  mytac.
  destruct a.
  mytac.
  remember (upd_last_ectrls ((v, v0) :: nil) x8) as vl.
  lets Hx : upd_last_prop  H Heqvl.
  mytac.
  unfolds in H3.
  simpl in H3.
  inverts H3.
  unfolds upd_last_ectrls.
  simpl.
  eexists; splits; eauto.
(* ** ac:   Check R_ECB_upd_hold. *)
  eapply R_ECB_upd_hold; eauto.
  do 2 eexists.
  exists x8.
  split; auto.
  split.
  eapply ecbmod_join_sigg; eauto.
  split; eauto.
  destruct a.
  lets Hzz :  upd_last_prop' Hsom;auto.
  destruct Hzz as (vll & Hv1 & Hv2).
  rewrite Hv1.
  destruct v'21.
  simpl in Hep; mytac; tryfalse.
  simpl.
  simpl in Hep.
  destruct Hep as (qid & Heq & Hr &Hex).
  destruct Hex as (abs & mqls & vv & Heaq & Hjoin & Hrl & Hepc ).
  lets Hxz : joinsig_join_sig2 Hjoin Hj.
  destruct Hxz as (x6 & Hj1 & Hj2).
  subst v'52.
  eexists.
  split; eauto.
  split; auto.
  do 2 eexists.
  exists vv.
  splits; eauto.
Qed.

Lemma RH_TCBList_ECBList_MUTEX_OWNER_subset_hold : forall x y z t,  RH_TCBList_ECBList_MUTEX_OWNER z t -> EcbMod.join x y z ->   RH_TCBList_ECBList_MUTEX_OWNER x t.
Proof.
  intros.
  unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
  intros.
  unfold get in *; simpl in *.
  assert ( EcbMod.get z eid = Some (absmutexsem pr (Some (tid, opr)), wls)) by go.
  eapply H; eauto.
Qed.

Lemma ecb_del_prop_RHhold:
  forall v'35 v'36 v'38 x y absmg,
    RH_TCBList_ECBList_P v'35 v'36 v'38 ->
    EcbMod.join x (EcbMod.sig y (absmg, nil))
                v'35 ->  RH_TCBList_ECBList_P x v'36 v'38 .
Proof.
  introv Hrh Hjo.
  unfolds in Hrh.
  destruct Hrh as (Hrh1&Hrh2&Hrh3&Hrh4).
  unfolds.
  splits.
  destruct Hrh1.
  splits.
  intros.
  mytac.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  mytac.
  destruct H2.
  subst y.
  apply EcbMod.join_comm in Hjo.
  eapply EcbMod.join_sig_get in Hjo.
  unfold get in *; simpl in *.
  rewrite H1 in Hjo.
  inverts Hjo.
  simpl in H3.
  tryfalse.
  do 3 eexists; split; try eapply ecbmod_get_join_get; eauto.
  destruct Hrh2.
  splits.
  intros.
  mytac.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  mytac.
  destruct H2.
  subst y.
  apply EcbMod.join_comm in Hjo.
  eapply EcbMod.join_sig_get in Hjo.
  unfold get in *; simpl in *.

  rewrite H1 in Hjo.
  inverts Hjo.
  simpl in H3.
  tryfalse.
  do 2 eexists; split; try eapply ecbmod_get_join_get; eauto.
  destruct Hrh3.
  splits.
  intros.
  mytac.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  mytac.
  destruct H2.
  subst y.
  apply EcbMod.join_comm in Hjo.
  eapply EcbMod.join_sig_get in Hjo.
  unfold get in *; simpl in *.
  rewrite H1 in Hjo.
  inverts Hjo.
  simpl in H3.
  tryfalse.
  do 2 eexists; split; try eapply ecbmod_get_join_get; eauto.
  destruct Hrh4.
  splits.
  intros.
  mytac.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  mytac.
  destruct H2.
  subst y.
  apply EcbMod.join_comm in Hjo.
  eapply EcbMod.join_sig_get in Hjo.
  unfold get in *; simpl in *.
  rewrite H1 in Hjo.
  inverts Hjo.
  simpl in H3.
  tryfalse.
  do 3 eexists; split; try eapply ecbmod_get_join_get; eauto.


  eapply  RH_TCBList_ECBList_MUTEX_OWNER_subset_hold; eauto.
  tauto.
Qed.  

Lemma  Mutex_owner_hold_for_set_tcb: forall x y pcur a b c,  RH_TCBList_ECBList_MUTEX_OWNER x y ->  RH_TCBList_ECBList_MUTEX_OWNER x (TcbMod.set y pcur (a, b, c)).
Proof.
  intros.
  unfold   RH_TCBList_ECBList_MUTEX_OWNER  in *.
  intros.
  assert ( pcur = tid  \/ pcur <> tid ) by tauto.
  elim H1; intros.
  subst pcur.
  rewrite TcbMod.set_a_get_a; auto.
  eauto.
  go.
  rewrite TcbMod.set_a_get_a'; auto.
  eapply H; eauto.
  go.
Qed.

(* infer step rule *)
(* Lemma absinfer_mbox_acc_err_return :
 *   forall P x , 
 *     can_change_aop P ->
 *     isptr x ->
 *     absinfer (<|| mbox_acc (x :: nil) ||>  **  P) ( <|| END (Some Vnull) ||>  **  P).
 * Proof.
 *   infer_solver 0%nat.
 * Qed.
 * 
 * 
 * Lemma  absinfer_mbox_acc_succ_return:
 *   forall P mqls x wl v v1 v3 v4 a,
 *     can_change_aop P ->  
 *     v = Vptr a -> 
 *     EcbMod.get mqls x = Some (absmbox v, wl) -> 
 *     absinfer
 *       ( <|| mbox_acc (Vptr x :: nil) ||>  ** 
 *             HECBList mqls **  HTCBList v1 **
 *       HTime v3 **
 *       HCurTCB v4 **
 *        P) 
 *       (<|| END (Some v) ||>  ** HECBList (EcbMod.set mqls x (absmbox Vnull, nil)) **  HTCBList v1 **
 *       HTime v3 **
 *       HCurTCB v4 **
 *                     P).
 * Proof.
 *   infer_solver 1%nat.
 * Qed. *)


Lemma absmbox_ptr_wt_nil: forall a w, RH_ECB_P  (absmbox (Vptr a), w) -> w = nil.
  intros.
  unfolds in H; try inversion H.
  clear H1.
  mytac.
  assert (w=nil \/ w<>nil) by tauto.
  elim H2; intros.
  auto.
  apply H.
  intro; tryfalse.
  
Qed.    


Lemma ecb_sig_join_sig'_set : forall a b c d b', EcbMod.joinsig a b c d -> EcbMod.joinsig a b' c (EcbMod.set d a b').
  intros.
  unfolds.
  unfolds in H.
  unfolds.
  intros.
  unfolds in H.
  lets aaa : H a0.
  assert (a = a0 \/ a<> a0) by tauto.
  elim H0; intros.
  subst.
  rewrite EcbMod.get_a_sig_a.
  rewrite EcbMod.get_a_sig_a in aaa.
  rewrite EcbMod.set_a_get_a.
  destruct (EcbMod.get c a0).
  inversion aaa.
  auto.
  apply CltEnvMod.beq_refl.
  apply CltEnvMod.beq_refl.
  apply CltEnvMod.beq_refl.
  
  rewrite EcbMod.get_a_sig_a'.
  rewrite EcbMod.get_a_sig_a' in aaa.
  rewrite EcbMod.set_a_get_a'.
  destruct (EcbMod.get c a0).
  destruct (EcbMod.get d a0).
  auto.
  auto.
  auto.
  apply tidspec.neq_beq_false; auto.
  apply tidspec.neq_beq_false; auto.
  apply tidspec.neq_beq_false; auto.
Qed.


Lemma R_ECB_ETbl_P_high_ecb_mbox_acpt_hold :
  forall x2 i i1 a  x3 v'42 v'40 v'35,
 R_ECB_ETbl_P x2
          (V$OS_EVENT_TYPE_MBOX
           :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: v'42 :: nil, v'40) v'35
->
 R_ECB_ETbl_P x2
     (V$OS_EVENT_TYPE_MBOX
      :: Vint32 i :: Vint32 i1 :: Vnull :: x3 :: v'42 :: nil, v'40) v'35
.
  intros.
  splits.
  unfolds in H.
  mytac.
  unfolds in H.
  mytac.
  unfolds .
  splits;  unfolds; auto.
  unfolds in H.
  mytac.
  clear -H0.
  unfolds in H0.
  mytac.
  unfolds.
  splits; unfolds; auto.
  unfolds in H.
  mytac.
  clear -H1.
  unfolds in H1.
  unfolds.
  auto.
Qed.

Lemma mbox_acpt_rh_tcblist_ecblist_p_hold: forall v'34 v'35 v'37 v w m, EcbMod.get v'34 v = Some (absmbox m, w) ->RH_TCBList_ECBList_P v'34 v'35 v'37 ->
RH_TCBList_ECBList_P
     (EcbMod.set v'34 v (absmbox Vnull, w)) v'35 v'37.
Proof.
  intros.
  unfolds in H0.
  mytac.
  unfolds.
  mytac; [clear -H H0| clear -H H1; rename H1 into H0|clear -H H2; rename H2 into H0| clear -H H3; rename H3 into H0]; unfolds; unfolds in H0; mytac; intros; unfold get in *; simpl in *; 
  try solve [eapply H0;
              mytac; eauto;
              assert ( eid = v \/ eid <> v)  as aa by tauto; destruct aa;[subst;
                                                                           rewrite EcbMod.set_a_get_a in e;[
                                                                             inversion e|
                                                                             apply CltEnvMod.beq_refl] 
                                                                         |
                                                                         rewrite EcbMod.set_a_get_a' in e;[
                                                                             eauto|
                                                                             apply tidspec.neq_beq_false];
                                                                         auto]]
  ;
  try solve[
         lets aaa : H1 H2;
         mytac;
         assert ( eid = v \/ eid <> v)  as aa by tauto; destruct aa;[subst eid;rewrite H in H3;inversion H3|
                                                                     rewrite EcbMod.set_a_get_a';[
                                                                         rewrite H3;
                                                                         eauto|
                                                                         apply tidspec.neq_beq_false;
                                                                           auto]]
       ]
  .

  assert (eid = v \/ eid <> v) as aa by tauto; destruct aa;[subst eid; rewrite EcbMod.set_a_get_a in H2|idtac].
  elim H2; intros.

  inversion H3.
  subst.
  eapply H0.
  splits; eauto.
  apply CltEnvMod.beq_refl.
  eapply H0.
  rewrite EcbMod.set_a_get_a' in H2.
  eauto.
  apply tidspec.neq_beq_false; auto.

  assert (eid = v \/ eid <> v) as aa by tauto; destruct aa. 
  subst.
  rewrite EcbMod.set_a_get_a.
  repeat eexists.
  lets aaa : H1 H2.
  mytac; auto.
  rewrite H in H3.
  inversion H3.
  subst.
  auto.
  apply CltEnvMod.beq_refl.

  rewrite EcbMod.set_a_get_a'.
  eapply H1.
  eauto.
  apply tidspec.neq_beq_false; auto.
  assert ( v = eid \/ v <> eid) by tauto.
  elim H4; intros.
  apply H1 in H3.
  simpljoin.
  rewrite H3 in H.
  inversion H.
  rewrite EcbMod.set_a_get_a' .
  eapply H1; eauto.
  go.
  eapply Mutex_owner_set.
  intro.
  mytac.
  auto.
Qed.

Lemma RLH_ECBData_p_high_mbox_acpt_hold:
  forall a e w,
 RLH_ECBData_P (DMbox (Vptr a)) (e, w) ->  RLH_ECBData_P (DMbox Vnull) (absmbox Vnull, w).
Proof.
  intros.
  unfolds in H.
  destruct e; tryfalse.
  unfolds.
  mytac.
  auto.
  unfolds in H0.
  assert (w = nil).
  mytac.
  assert (w = nil \/ w <> nil) by tauto.
  elim H1; auto.
(*  intro.
  apply H0 in H2.
  inverts H2. *)

  unfolds.
  mytac; auto.
Qed.


(* absinfer lemmas *)
(* Lemma absinfer_mbox_del_null_return : forall P , 
 * can_change_aop P ->
 * absinfer (<|| mbox_del (Vnull :: nil) ||> ** P) ( <|| END (Some (Vint32 (Int.repr MBOX_DEL_NULL_ERR))) ||> ** P).
 * Proof.
 *   infer_solver 0%nat.
 * Qed.
 * 
 * Lemma absinfer_mbox_del_p_not_legal_return : forall x a P tcbls tm curtid, 
 *                                   can_change_aop P ->
 *                                   ~ (exists x0 wls, EcbMod.get x a = Some (absmbox x0, wls)) ->
 * absinfer (<|| mbox_del (Vptr a :: nil) ||> ** HECBList x **   HTCBList tcbls ** HTime tm **  HCurTCB curtid **
 *             P) ( <|| END (Some  (V$ MBOX_DEL_P_NOT_LEGAL_ERR)) ||> ** HECBList x **   HTCBList tcbls ** HTime tm **  HCurTCB curtid  ** P).
 * Proof.
 *   infer_solver 1%nat.
 * Qed.
 * 
 * Lemma absinfer_mbox_del_wrong_type_return : forall x a P tcbls tm curtid ,
 *                                   can_change_aop P ->
 *  (exists d,
 *   EcbMod.get x a = Some d /\ ~ (exists x wls, d = (absmbox x, wls))) ->
 * absinfer (<||mbox_del (Vptr a :: nil) ||>  ** HECBList x **   HTCBList tcbls ** HTime tm **  HCurTCB curtid **  P) ( <|| END (Some  (V$ OS_ERR_EVENT_TYPE)) ||> ** HECBList x **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
 * Proof.
 *   infer_solver 2%nat.
 * Qed.
 * 
 * 
 * Lemma absinfer_mbox_del_task_wt_return : forall x a P tcbls tm curtid, 
 *                                   can_change_aop P ->
 *  (exists y t tl,
 *   EcbMod.get x a = Some (absmbox y, t::tl)) ->
 * absinfer (<|| mbox_del (Vptr a :: nil) ||>  ** HECBList x **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P) ( <|| END (Some  (V$ MBOX_DEL_TASK_WAITING_ERR)) ||>   ** HECBList x **   HTCBList tcbls ** HTime tm **  HCurTCB curtid ** P).
 * Proof.
 *   infer_solver 3%nat.
 * Qed.
 * 
 * Lemma absinfer_mbox_del_succ_return :
 *   forall ecbls ecbls' x a P tid tcbls t, 
 *     can_change_aop P ->
 *     EcbMod.get ecbls a = Some (absmbox x, nil) ->
 *     EcbMod.join ecbls' (EcbMod.sig a (absmbox x, nil)) ecbls -> 
 *     absinfer (<|| mbox_del (Vptr a :: nil) ||> ** HECBList ecbls **
 *               HTCBList tcbls ** HTime t **  HCurTCB tid **  P) ( <||  END (Some  (V$NO_ERR)) ||> **
 *                          HECBList ecbls' ** HTCBList tcbls ** HTime t **  HCurTCB tid  ** P).
 * Proof.
 *   infer_solver 4%nat.
 * Qed. *)

Lemma RH_TCBList_ECBList_P_high_get_msg_hold_mbox :
  forall ecbls tcbls pcur qid m  wl prio  m',
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    EcbMod.get ecbls qid = Some (absmbox (Vptr m), wl) ->
    TcbMod.get tcbls pcur = Some (prio, rdy, m') ->
    RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absmbox Vnull, wl)) (TcbMod.set tcbls pcur (prio, rdy, (Vptr m))) pcur. 
Proof.
  introv Hr Ht He.
  unfolds in Hr.
  destruct Hr as (Hr3 & Hr2 & Hr1 & Hr4).
  unfolds.
  splits.
  Focus 3.
  splits.  
  intros.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  inverts H0.
  assert ( EcbMod.get ecbls eid = Some (absmbox (Vptr m), wls) /\ In tid wls).
  splits; auto.
  apply Hr1 in H.
  mytac.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  unfold get in *; simpl in *.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr1 in H.
  mytac.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr1 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 2 eexists; splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
Focus 2.
{
  splits.  
  intros.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  inverts H0.
  destruct H as (Ha & Hb).
  rewrite EcbMod.set_sem in Ha.
  rewrite tidspec.neq_beq_false in Ha; auto.
  assert ( EcbMod.get ecbls eid = Some (abssem n, wls)/\ In tid wls).
  splits; auto.
  apply Hr2 in H.
  mytac.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr2 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
}
  Unfocus.
{
  splits.
  intros.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  inverts H0.
  destruct H as (Ha & Hb).
  rewrite EcbMod.set_sem in Ha.
  rewrite tidspec.neq_beq_false in Ha; auto.
  assert ( EcbMod.get ecbls eid =Some (absmsgq x y, qwaitset)/\ In tid qwaitset).
  splits; auto.
  apply Hr3 in H.
  mytac.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr3 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; splits; eauto.
}
{
  splits.  
  intros.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  inverts H0.
  destruct H as (Ha & Hb).
  rewrite EcbMod.set_sem in Ha.
  rewrite tidspec.neq_beq_false in Ha; auto.
  assert ( EcbMod.get ecbls eid =Some (absmutexsem n1 n2, wls)/\ In tid wls).
  splits; auto.
  apply Hr4 in H.
  mytac.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.
  rewrite He in H; inverts H.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; eauto.
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr4 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; splits; eauto.

  unfolds in Hr4.
  mytac.

  eapply Mutex_owner_hold_for_set_tcb.
  eapply Mutex_owner_set.
  intro; mytac.
  auto.
}
Qed.  

Lemma TCBListP_head_in_tcb:
  forall v'51 v'52 v'22 x9 x8 i9 i8 i6 i5 i4 i3 v'33 v'34 v'50 xx,
    TCBList_P (Vptr v'52)
              ((v'51
                  :: v'22
                  :: x9
                  :: x8
                  :: Vint32 i9
                  :: Vint32 i8
                  :: Vint32 xx
                  :: Vint32 i6
                  :: Vint32 i5
                  :: Vint32 i4 :: Vint32 i3 :: nil) :: v'33)
              v'34 v'50 ->
    exists st, TcbMod.get v'50 v'52 = Some ( xx, st, x8).
Proof.
  intros.
  unfolds in H.
  fold TCBList_P in H.
  mytac.
  unfolds in H2.
  destruct x2; destruct p.
  mytac.
  unfolds in H2.
  unfolds in H4.
  simpl in H2.
  simpl in H4.
  inverts H2.
  inverts H4.
  inverts H.
  unfolds in H0; simpl in H0.
  inverts H0.
  unfolds in H6.
  eexists.
  eapply TcbMod.join_get_l.
  exact H1.
  eapply TcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
Qed.


Lemma tcblist_p_node_rl_mbox:
  forall v'47 v'39 v'19 x15 x10 i10 i9 i8 i7 i6 i5 i1 v'31 v'32 v'36 i,
    TCBList_P (Vptr (v'47, Int.zero))
              ((v'39
                  :: v'19
                  :: x15
                  :: x10
                  :: Vint32 i10
                  :: Vint32 i9
                  :: Vint32 i8
                  :: Vint32 i7
                  :: Vint32 i6
                  :: Vint32 i5 :: Vint32 i1 :: nil) :: v'31)
              v'32 v'36 ->
    RL_TCBblk_P
      (v'39
         :: v'19
         :: x15
         :: Vnull
         :: Vint32 i
         :: V$OS_STAT_MBOX
         :: Vint32 i8
         :: Vint32 i7
         :: Vint32 i6 :: Vint32 i5 :: Vint32 i1 :: nil).
Proof.
  introv Ht.
  simpl in Ht.
  mytac;simpl_hyp.
  inverts H.
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
  unfolds.
  do 6 eexists;splits; try unfolds; simpl;  eauto.
  splits; auto.
  eexists.
  splits.
  unfolds.
  simpl; eauto.
  introv Hf.
  inverts Hf.
 Qed. 


(* absinfer lemmas *)
(* Lemma absinfer_mbox_pend_null_return : forall P x, 
 *                                        can_change_aop P ->
 *                                        tl_vl_match  (Tint16 :: nil) x = true ->
 *                                        absinfer (<|| mbox_pend (Vnull :: x) ||> ** P) ( <|| END (Some (Vint32 (Int.repr MBOX_PEND_NULL_ERR))) ||> ** P).
 * Proof.
 *   infer_solver 0%nat.
 * Qed.
 * 
 * Open Scope code_scope.
 * 
 * 
 * Lemma absinfer_mbox_pend_p_not_legal_return : forall x a P b v'33 v'16 v'35, 
 *                                               can_change_aop P ->
 *                                               Int.unsigned b<=65535 ->
 *                                               EcbMod.get x a = None ->
 *                                               absinfer (<|| mbox_pend (Vptr a ::Vint32 b:: nil) ||> ** HECBList x **
 *     HTCBList v'33 **
 *     HTime v'16 **
 *     HCurTCB v'35 **
 *                                                           P) ( <|| END (Some  (V$ MBOX_PEND_P_NOT_LEGAL_ERR)) ||> ** HECBList x **
 *     HTCBList v'33 **
 *     HTime v'16 **
 *     HCurTCB v'35 ** P).
 * Proof.
 *   infer_solver 1%nat.
 * Qed.
 * 
 * 
 * Lemma absinfer_mbox_pend_wrong_type_return : forall x a b P v'33 v'16 v'35, 
 *                                              can_change_aop P ->
 *                                              Int.unsigned b <= 65535 ->
 *                                              (exists d,
 *                                                 EcbMod.get x a = Some d /\ ~ (exists x wls, d = (absmbox x, wls))) ->
 *                                              absinfer (<|| mbox_pend (Vptr a :: Vint32 b :: nil) ||> ** HECBList x **
 *     HTCBList v'33 **
 *     HTime v'16 **
 *     HCurTCB v'35 **
 *                                                          P) ( <|| END (Some  (V$MBOX_PEND_WRONG_TYPE_ERR)) ||> ** HECBList x **
 *     HTCBList v'33 **
 *     HTime v'16 **
 *     HCurTCB v'35 ** P).
 * Proof.
 *   intros.
 *   mytac.
 *   destruct x0.
 *   infer_solver 2%nat.
 *   repeat tri_exists_and_solver1.
 *   intro.
 *   apply H2.
 *   mytac.
 *   eauto.
 * Qed.
 * 
 * Lemma absinfer_mbox_pend_from_idle_return : forall x a b P y t ct, 
 *                                              can_change_aop P ->
 *                                              Int.unsigned b <= 65535 ->
 *                                              (exists st msg, TcbMod.get y ct = Some (Int.repr OS_IDLE_PRIO, st, msg)) ->
 *                                              absinfer (<|| mbox_pend (Vptr a :: Vint32 b :: nil) ||> ** HECBList x ** HTCBList y ** HTime t ** HCurTCB ct **
 *                                                          P) ( <|| END (Some  (V$MBOX_PEND_FROM_IDLE_ERR)) ||> ** HECBList x ** HTCBList y ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   infer_solver 3%nat.
 * Qed.
 * Lemma absinfer_mbox_pend_not_ready_return :
 *   forall P ecbls tcbls t ct st msg v x prio,
 *     Int.unsigned v <= 65535 ->
 *     TcbMod.get tcbls ct = Some (prio, st, msg) ->
 *     ~ st = rdy ->
 *     can_change_aop P ->
 *     absinfer (<|| mbox_pend (Vptr x :: Vint32 v :: nil) ||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P)
 *            (<|| END (Some (Vint32 (Int.repr MBOX_PEND_NOT_READY_ERR)))||> ** HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   infer_solver 4%nat.
 * Qed.
 * 
 * 
 * Lemma  absinfer_mbox_pend_inst_get_return:
 *   forall P mqls x wl v v1 v3 v4 a v00 msg p,
 *     can_change_aop P ->  
 *     v = Vptr a -> 
 *     Int.unsigned v00 <= 65535 ->
 *     EcbMod.get mqls x = Some (absmbox v, wl) -> 
 *     TcbMod.get v1 v4 = Some (p, rdy, msg) ->
 *     absinfer
 *       ( <|| mbox_pend (Vptr x ::Vint32 v00 :: nil) ||>  ** 
 *             HECBList mqls **  HTCBList v1 **
 *       HTime v3 **
 *       HCurTCB v4 **
 *        P) 
 *       (<|| END (Some (Vint32 (Int.repr MBOX_PEND_SUCC))) ||>  ** HECBList (EcbMod.set mqls x (absmbox Vnull, nil)) **  HTCBList (TcbMod.set v1 v4 (p, rdy, v)) **
 *       HTime v3 **
 *       HCurTCB v4 **
 *                     P).
 * Proof.
 *   infer_solver 5%nat.
 * Qed.
 * 
 * Lemma absinfer_mbox_pend_block:
 *   forall P mqls qid v wl p m t ct tls,
 *     Int.unsigned v <= 65535 ->
 *     can_change_aop P ->
 *     EcbMod.get mqls qid = Some (absmbox Vnull, wl) ->
 *     TcbMod.get tls ct = Some (p,rdy,m) ->
 *     absinfer
 *       ( <|| mbox_pend (Vptr qid :: Vint32 v :: nil) ||>  ** 
 *            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
 *       (<|| isched;; (mbox_pend_timeout_err (|Vptr qid :: Vint32 v :: nil|) ?? mbox_pend_block_get_succ (|Vptr qid :: Vint32 v :: nil|))||>  ** HECBList (EcbMod.set mqls qid (absmbox Vnull,ct::wl)) ** HTCBList (TcbMod.set tls ct (p,wait (os_stat_mbox qid) v, Vnull) ) ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   
 *   unfold mbox_pend; intros.
 *   infer_branch 6%nat.
 *   eapply absinfer_trans.
 *   Focus 2.
 *   eapply absinfer_seq_end.
 *   3:sep auto.
 *   can_change_aop_solver.
 *   can_change_aop_solver.
 *   instantiate (1:= None).
 *   eapply absinfer_seq.
 *   can_change_aop_solver.
 *   can_change_aop_solver.
 *   tri_infer_prim.
 *   infer_part2.
 * Qed. *)


Lemma low_stat_q_impl_high_stat_q
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) (msg : val),
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     V_OSTCBMsg tcurl = Some msg ->
     exists prio st,
       TcbMod.get tcbls tcur = Some (prio, st, msg).
Proof.
  introv Ht Hv.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  mytac.
  unfolds in H.
  rewrite H in H4.
  inverts H4.
  apply tcbjoin_get_a in H1.
  do 2 eexists; eauto.
Qed.


Lemma low_stat_nordy_imp_high:
  forall a b c d e f g h i j st rtbl p t m,
    R_TCB_Status_P
      (a
         :: b
         :: c
         :: d
         :: Vint32 e
         :: Vint32 st
         :: f
         :: g
         :: h :: i :: j :: nil)
      rtbl (p, t, m) -> (Int.eq st ($ OS_STAT_RDY) = false \/ Int.eq e ($ 0) = false) ->
    ~(t = rdy ).
Proof.
  introv Hr Heq.
  unfolds in Hr.
  mytac.
  introv Hf.
  clear H H1.
  subst t.
  assert ( (p, rdy, m) = (p, rdy, m)) by auto.
  apply H0 in H.
  mytac.
  unfolds in H1.
  simpl in H1.
  inverts H1.
  simpl_hyp.
  repeat rewrite Int.eq_true in Heq.
  destruct Heq; tryfalse.
Qed.


Lemma r_tcb_status_p_nrdy:
  forall v'39 v'19 x15 x10 i10 i9 i8 i7 i6 i5 i1 p t m v'32,
    R_TCB_Status_P
      (v'39
         :: v'19
         :: x15
         :: x10
         :: Vint32 i10
         :: Vint32 i9
         :: Vint32 i8
         :: Vint32 i7
         :: Vint32 i6 :: Vint32 i5 :: Vint32 i1 :: nil)
      v'32 (p, t, m) ->
    Int.eq i9 ($ OS_STAT_RDY) = false \/ Int.eq i10 ($ 0) = false ->
    ~ t =rdy.
Proof.
  intros.
  eapply low_stat_nordy_imp_high; eauto.
Qed.


Lemma TCBList_P_impl_high_tcbcur_Some :  
  forall tcbls tcur tcurl tcblist rtbl,
    TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
    exists prio st m, TcbMod.get tcbls tcur = Some (prio, st, m).
Proof.
  introv Htcb.
  simpl in Htcb.
  mytac.
  inverts H.
  apply tcbjoin_get_a in H1.
  destruct x2.
  destruct p.
  eauto.
Qed.

Lemma TCBList_P_impl_high_tcbcur_rdy:
  forall (tcbls : TcbMod.map) (tcur : addrval) 
         (tcurl : vallist) (tcblist : list vallist)
         (rtbl : vallist) v'39 v'19 x15 x10 i10 i9 i8 i7 i6 i5 i1,
    Int.eq i9 ($ OS_STAT_RDY) = true ->
    Int.eq i10 ($ 0) = true ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    TCBList_P (Vptr tcur) ((v'39
                              :: v'19
                              :: x15
                              :: x10
                              :: Vint32 i10
                              :: Vint32 i9
                              :: Vint32 i8
                              :: Vint32 i7
                              :: Vint32 i6
                              :: Vint32 i5 :: Vint32 i1 :: nil) :: tcblist) rtbl tcbls ->
    exists prio m, TcbMod.get tcbls tcur = Some (prio, rdy, m).
Proof.
  introv Heq1 Heq2 Harr Hlen Htc Htsp.
  lets Hs : TCBList_P_impl_high_tcbcur_Some  Htsp.
  mytac.
  unfolds in Htsp.
  fold TCBList_P in Htsp.
  mytac.
  simpl_hyp.
  unfolds in H3.
  destruct x5.
  destruct p.
  mytac.
  simpl_hyp.
  

  lets Hsd : low_stat_rdy_imp_high H5 H6 Heq2 Harr; eauto.
  subst.
  inverts H0.
  apply tcbjoin_get_a in H2.
  rewrite H2 in H.
  inverts H.
  do 2 eexists; eauto.
Qed.




Lemma  ecb_etbl_set_hold:
  forall x y tcbls prio st m ptcb m',
    TcbMod.get tcbls ptcb = Some (prio, st, m) ->
    R_ECB_ETbl_P x y tcbls  ->
    R_ECB_ETbl_P x y  (TcbMod.set tcbls ptcb (prio, st, m')).
Proof.
  introv Htc Hr.
  unfolds in Hr.
  destruct Hr as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra1 & Hra2 & Hra3 & Hra4).
  destruct Hr2 as (Hrb1 & Hrb2 & Hrb3 & Hrb4).
  unfolds.
  splits.
  unfolds.
  splits.
  unfolds.
  destruct y.
  intros.
  eapply Hra1 in H0; eauto.
  mytac.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.

  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m'.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  unfolds.
  destruct y.
  intros.
  eapply Hra2 in H0; eauto.
  mytac.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m'.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  unfolds.
  destruct y.
  intros.
  eapply Hra3 in H0; eauto.
  mytac.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m'.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  unfolds.
  destruct y.
  intros.
  eapply Hra4 in H0; eauto.
  mytac.
  assert (ptcb = x0 \/ ptcb <> x0) by tauto.
  destruct H1.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in Htc.
  inverts Htc.
  exists x0.
  exists x1 m'.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  exists x0.
  exists x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  unfolds.
  splits.
  unfolds.
  destruct y.
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb1; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  unfolds.
  destruct y.
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb2; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  unfolds.
  destruct y.
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb3; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  unfolds.
  destruct y.
  intros.
  assert (ptcb = tid \/ ptcb <> tid) by tauto. 
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrb4; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  auto.
Qed.


Lemma ECBList_P_high_tcb_get_msg_hold:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio st m m',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m) ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, st, m')).
Proof.
  inductions ectrl.
  intros.
  simpl in H.
  mytac.
  simpl; splits; auto.
  intros.
  simpl in H.
  mytac.
  destruct msgql; tryfalse.
  destruct a.
  mytac.
  simpl.
  eexists.
  splits; eauto.


  eapply ecb_etbl_set_hold; eauto.
  do 3 eexists; splits; eauto.
Qed.


Lemma TCBList_P_tcb_get_msg_hold :
    forall ptcb v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 rtbl vl
           tcbls prio st m m',
    TCBList_P (Vptr ptcb) ((v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m) ->
    TCBList_P (Vptr ptcb) ((v1::v2::v3::m'::v5::v6::v7::v8::v9::v10::v11::nil)::vl) rtbl (TcbMod.set tcbls ptcb (prio, st, m')).
Proof.
  introv Htc Hget.
  unfolds in Htc.
  mytac.
  simpl_hyp.
  inverts H.
  fold TCBList_P in H3.
  unfolds.
  fold TCBList_P.
  do 4 eexists; splits; eauto.
  unfolds; simpl; auto.
  instantiate (1:=(prio,st,m')).
  eapply tcbjoin_set; eauto.
  funfold H2.
  destruct x2.
  destruct p.
   lets Heq : tcbjoin_get H1 Hget.
  inverts Heq.
  mytac.
  simpl_hyp.
  unfolds.
  splits; try unfolds; simpl; auto.
  splits.
  funfold H4.
  clear - H.
  funfold H.
  unfolds.
  intros.
   assert (RdyTCBblk
        (x0
         :: v2
            :: v3
               :: m
                  :: v5 :: v6 :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
        rtbl prio0).
  unfolds.
  funfold H0; simpl; auto.
  apply H in H1.
  destruct H1 as (Ha & Hb & Hc).
  splits; try unfolds;simpl; eauto.
  destruct Hc.
  inverts H1.
  eexists; eauto.
  destruct H4 as (_ & Hhl & _).
  unfolds in Hhl.
  unfolds.
  intros.
  inverts H.
  assert ( (prio0, rdy, m) = (prio0, rdy, m)) by auto. 
  apply Hhl in H.
  mytac; try unfolds;simpl; auto.
  destruct H4 as (_ & _ & Hhl & _).
  unfolds in Hhl.
  unfolds.
  mytac; try unfolds;simpl; auto.
  intros.
  simpl_hyp.
  unfolds in H.
  assert (WaitTCBblk
         (x0
          :: v2
             :: v3
                :: m
                   :: v5
                      :: V$OS_STAT_RDY
                         :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
         rtbl prio0 t).
  funfold H7.
  unfolds; simpl; auto.
  apply H in H8.
  destruct H8.
  splits; eauto.
  mytac; eexists; eauto.
  unfolds; simpl; auto.
  intros.
  simpl_hyp.
  assert ( WaitTCBblk
         (x0
          :: v2
             :: Vptr eid
                :: m
                   :: v5
                      :: V$OS_STAT_SEM
                         :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
         rtbl prio0 t).
  funfold H7.
  unfolds; simpl; eauto.
  eapply H0 in H8.
  unfold V_OSTCBStat in H8.
  unfold  V_OSTCBEventPtr in H8.
  simpl in H8; eauto.
  assert (exists m0, (prio, st, m) = (prio0, wait (os_stat_sem eid) t, m0)).
  eapply H8;eauto.
  mytac.
  eexists; eauto.
  intros.
  simpl_hyp.
  assert ( WaitTCBblk
         (x0
          :: v2
             :: Vptr eid
                :: m
                   :: v5
                      :: V$OS_STAT_Q
                         :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
         rtbl prio0 t).
  funfold H7; unfolds; simpl;eauto.
  eapply H4 in H8.
   unfold V_OSTCBStat in H8.
  unfold  V_OSTCBEventPtr in H8.
  simpl in H8; eauto.
  assert ( exists m0, (prio, st, m) = (prio0, wait (os_stat_q eid) t, m0)).
  eapply H8; eauto.
  mytac.
  eexists; eauto.
 intros.
  simpl_hyp.
  assert ( WaitTCBblk
         (x0
          :: v2
             :: Vptr eid
                :: m
                   :: v5
                      :: V$OS_STAT_MBOX
                         :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
         rtbl prio0 t).
  funfold H7; unfolds; simpl;eauto.
  eapply H5 in H8.
   unfold V_OSTCBStat in H8.
  unfold  V_OSTCBEventPtr in H8.
  simpl in H8; eauto.
  assert ( exists m0, (prio, st, m) = (prio0, wait (os_stat_mbox eid) t, m0)).
  eapply H8; eauto.
  mytac.
  eexists; eauto.
   intros.
  simpl_hyp.
  assert ( WaitTCBblk
         (x0
          :: v2
             :: Vptr eid
                :: m
                   :: v5
                      ::V$OS_STAT_MUTEX
                         :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
         rtbl prio0 t).
  funfold H7; unfolds; simpl;eauto.
  eapply H6 in H8.
   unfold V_OSTCBStat in H8.
  unfold  V_OSTCBEventPtr in H8.
  simpl in H8; eauto.
  assert ( exists m0, (prio, st, m) = (prio0, wait (os_stat_mutexsem eid) t, m0)).
  eapply H8; eauto.
  mytac.
  eexists; eauto.
  unfolds.
  splits;
  unfolds;
  intros;
  inverts H;
  eapply H4; eauto.
Qed.



Lemma RH_CurTCB_high_get_msg_hold :
  forall ptcb tcbls prio st m m',
    RH_CurTCB ptcb tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m) ->
    RH_CurTCB ptcb (TcbMod.set tcbls ptcb (prio, st, m')).
Proof.
  introv Hrh Htc.
  unfolds in Hrh.
  mytac.
  unfolds.
  unfold get in *; simpl in *.
  rewrite H in Htc.
  inverts Htc.
  exists prio st m'.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
Qed.


(* absinfer lemmas *)
(* Lemma absinfer_mbox_pend_block_get_return
 *      : forall (P : asrt) (mqls : EcbMod.map) (qid : addrval) 
 *          (v : int32) (p : priority) (t : ostime) (ct : tidspec.A)
 *          (tls : TcbMod.map) (m : msg) (st : taskstatus),
 *        Int.unsigned v <= 65535 ->
 *        can_change_aop P ->
 *        TcbMod.get tls ct = Some (p, st, m) ->
 *        m <> Vnull ->
 *        ⊢  <|| mbox_pend_timeout_err (|Vptr qid :: Vint32 v :: nil|)
 *     ?? mbox_pend_block_get_succ (|Vptr qid :: Vint32 v :: nil|)
 *     ||>
 *   **
 *         HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P
 *        ⇒  <|| END (Some (V$ MBOX_PEND_SUCC)) ||>  **
 *          HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P
 * .
 * Proof.
 *   infer_part1 1%nat.
 *   infer_part2.
 * Qed.
 * 
 * 
 * Lemma absinfer_mbox_pend_to_return :
 *    forall P mqls qid v t ct tls st prio,
 *     Int.unsigned v <= 65535 ->
 *     TcbMod.get tls ct = Some (prio, st, Vnull) ->
 *     can_change_aop P ->
 *     absinfer
 *       ( <||
 *     mbox_pend_timeout_err (|Vptr qid :: Vint32 v :: nil|)
 *     ?? mbox_pend_block_get_succ (|Vptr qid :: Vint32 v :: nil|)
 *     ||>  ** 
 *            HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
 *       (<||  END (Some (Vint32 (Int.repr MBOX_PEND_TIMEOUT_ERR)))||>  ** HECBList mqls  ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   infer_part1 0%nat.
 *   infer_part2.
 * Qed. *)



Lemma ECBList_P_high_tcb_block_hold_mbox:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time m' ,
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, rdy, m) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, wait (os_stat_mbox qid) time, m')).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  mytac; auto.
  intros.
  simpl in H.
  mytac.
  destruct msgql; tryfalse.
  destruct a.
  mytac.
  simpl.
  exists x.
  splits; auto.
  unfolds.
  destruct H2 as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra3 & Hra2 & Hra1 & Hra4).
  destruct Hr2 as (Hrb3 & Hrb2 & Hrb1 & Hrb4).
  simpl in Hr3.
  splits.
  unfolds.
  splits.
Focus 3.
{
  unfolds.
  intros.
  eapply Hra1 in H6;eauto.
  mytac.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
}
Unfocus.
Focus 2.
{
  unfolds.
  intros.
  eapply Hra2 in H6;eauto.
  mytac.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
}
Unfocus.
{
  unfolds.
  intros.
  eapply Hra3 in H6;eauto.
  mytac.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
}
{
  unfolds.
  intros.
  eapply Hra4 in H6;eauto.
  mytac.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H7.
  subst.
  unfold get in *; simpl in *.
  rewrite H0 in H6.
  inverts H6.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
}
  unfolds.
  splits.
Focus 3.
{
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  apply ecbmod_joinsig_get in H3.
  rewrite H3 in H1.
  tryfalse.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
}
Unfocus.

  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
   unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H6.
  subst.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  rewrite TcbMod.set_sem in H2.
  rewrite tidspec.neq_beq_false in H2; eauto.
  simpl; auto.
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma ejoin_get_none_r : forall ma mb mc x a, EcbMod.get ma x = Some a -> EcbMod.join ma mb mc -> EcbMod.get mb x = None.
Proof.
  intros.
  unfolds in H0.
  lets adf : H0 x.
  destruct (EcbMod.get ma x).
  destruct (EcbMod.get mb x).
  tryfalse.
  auto.
  destruct (EcbMod.get mb x).
  tryfalse.
  auto.
Qed.

Lemma ejoin_get_none_l : forall ma mb mc x a, EcbMod.get mb x = Some a -> EcbMod.join ma mb mc -> EcbMod.get ma x = None.
Proof.
  intros.
  apply EcbMod.join_comm in H0.
  eapply ejoin_get_none_r; eauto.
Qed.


Lemma R_ECB_ETbl_P_high_tcb_block_hold:
  forall (l : addrval) (vl : vallist) (egrp : int32) 
    (v2 v3 v4 v5 : val) (etbl : vallist) (tcbls : TcbMod.map)
    (ptcb : tidspec.A) (prio : int32) (st : taskstatus) 
    (m m' : msg) (y bity bitx ey time : int32) (av : addrval),
  Int.unsigned prio < 64 ->
  R_PrioTbl_P vl tcbls av ->
  R_ECB_ETbl_P l
    (V$OS_EVENT_TYPE_MBOX :: Vint32 egrp :: v2 :: v3 :: v4 :: v5 :: nil, etbl)
    tcbls ->
  TcbMod.get tcbls ptcb = Some (prio, st, m) ->
  y = Int.shru prio ($ 3) ->
  bity = Int.shl ($ 1) y ->
  bitx = Int.shl ($ 1) (prio&ᵢ$ 7) ->
  nth_val ∘(Int.unsigned y) etbl = Some (Vint32 ey) ->
  R_ECB_ETbl_P l
    (V$OS_EVENT_TYPE_MBOX
     :: Vint32 (Int.or egrp bity) :: v2 :: v3 :: v4 :: v5 :: nil,
    update_nth_val ∘(Int.unsigned y) etbl (Vint32 (Int.or ey bitx)))
    (TcbMod.set tcbls ptcb (prio, wait (os_stat_mbox l) time, m'))
.
Proof.
  introv Hran Hrs  Hre Htc Hy Hb1 Hb2 Hnth.
  subst.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 & Het).
  unfolds.
  splits.
  unfolds.
  splits.
  Focus 3.
{
  unfolds.
  intros.
  destruct Hre1 as (_ & _ &Hre1 & _).
  destruct Hre2 as (_ & _ & Hre2 & _).
  unfolds in Hre1.
  unfolds in Hre2.
  assert (prio = $ prio0 \/ prio <> $ prio0) by tauto.
  destruct H1.
  subst.
  exists ptcb time m'.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  lets Hres : prio_wt_inq_keep Hran H1 Hnth .
  destruct Hres.
  apply H2 in H.
  apply Hre1 in H.
  mytac.
  exists x x0 x1.
  assert (x = ptcb \/ x <> ptcb) by tauto.
  destruct H4.
  subst.
  unfold get in *; simpl in *.
  rewrite Htc in H.
  inverts H.
  tryfalse.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  unfolds. 
  simpl; auto.
}
Unfocus.
Focus 2.
{
  unfolds.
  intros.
  usimpl H0.
}
Unfocus.
{
  unfolds.
  intros.
  usimpl H0.
}
{
   unfolds.
  intros.
  usimpl H0.
}
  unfolds.
  splits.
Focus 3.
{
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  splits.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  unfolds.
  rewrite Int.repr_unsigned.
  exists ( prio0&ᵢ$ 7).
  exists (Int.shru prio0 ($3)).
  exists ((Int.or ey ($ 1<<ᵢ(prio0&ᵢ$ 7)))).
  splits; eauto.
  clear - Hran.
  int auto.
  eapply update_nth; eauto.
  rewrite Int.and_commut.
  rewrite Int.or_commut.
  unfold Int.one.
  rewrite Int.and_or_absorb.
  auto.
  unfolds; simpl; auto.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  unfolds in Hre2.
  destruct Hre2 as (_ & _ & Hre2 & _).
  lets Hasd : Hre2  H.
   destruct Hasd as (Has1 & Has2).
  splits.
  eapply prio_wt_inq_keep; eauto.
  rewrite Int.repr_unsigned.
  unfolds  in Hrs.
  destruct Hrs.
  destruct H2.
  unfolds in H3.
  lets Hdd : H3 H0 H Htc.
  eauto.
  unfolds; simpl; auto.
}
Unfocus.
Focus 2.
{
   unfolds.

  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (_&Hre2&_).
  apply Hre2 in H.
  destruct H.
  usimpl H1.
}
Unfocus.
{
   unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (Hre2&_).
  apply Hre2 in H.
  destruct H.
  usimpl H1.
}
   unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.  
  destruct H0.
  subst.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  erewrite tidspec.neq_beq_false in H; eauto.
  destruct Hre2 as (_&_& _ &Hre2).
  apply Hre2 in H.
  destruct H.
  usimpl H1.
  simpl.
  unfolds.
  branch 3.
  unfolds; simpl; auto.
Qed.



(**)
(* TODO *)
Lemma TCBList_P_tcb_block_hold :
    forall ptcb v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 rtbl vl
           tcbls prio st m qid time ry,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::v4::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m) ->
    prio_neq_cur tcbls ptcb ( prio) ->
    st = rdy \/ (exists n, st = wait os_stat_time n) -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    TCBList_P (Vptr ptcb) ((v1::v2::(Vptr qid)::Vnull::(Vint32 time)::(Vint32 ($ OS_STAT_MBOX))::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) 
(update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10)))) 
 (TcbMod.set tcbls ptcb ( prio, wait (os_stat_mbox qid) ( time), Vnull)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth.
  unfolds in Htcb;fold TCBList_P in Htcb.
  mytac.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_mbox qid) time,Vnull).
  splits; eauto.
  eapply tcbjoin_set; eauto.
{
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds in H;simpl in H; inverts H.
  unfolds.
  split.  
  unfolds.
  simpl.
  auto.
  funfold H2.
  splits.
  auto.
  unfolds.
  do 6 eexists; splits; try unfolds; simpl; eauto.
  splits; eauto.
  eexists.
  splits.
  unfolds;simpl; eauto.
  introv Hf.
  inverts Hf.
  lets Hexa : tcbjoin_get H1 Htm.
  inverts Hexa.
  unfolds in H4.
  split.
  unfolds.
  intros.
  simpl_hyp.
  unfolds in H.
  destruct H.
  simpl_hyp.
  unfolds in H0.
  assert (prio&ᵢ$ 7 = prio&ᵢ$ 7) by auto.
  assert (Int.shru ( prio) ($ 3) =Int.shru (prio) ($ 3)) by auto.
  assert ( nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3)))
         (update_nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3))) rtbl
            (Vint32 (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
           Some (Vint32  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth; eauto.
  lets Hr: H0 H H2 H5.
  rewrite Int.and_assoc in Hr.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut.
  rewrite Int.and_not_self.
  auto.
  rewrite H6  in Hr.
  rewrite Int.and_zero in Hr.
  assert ( $ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply  math_prop_neq_zero2; try omega).
  unfold Int.zero in Hr.
  tryfalse.
  split.
  unfolds.
  intros.
  inverts H.
  split.
  unfolds.
  split.
  unfolds.
  intros.
  inverts H0.
  split.
  unfolds.
  intros.
  inverts H0.

  split.
  unfolds.
  intros.
  inverts H0.
  split.
  unfolds.
  intros.


  unfolds in H.
  mytac.
  simpl_hyp.
  eexists.
  eauto.
  unfolds.
  

  intros.
  inverts H0.

  unfolds.
  split.
  unfolds.
  intros.
  inverts H.
  split.
  unfolds.
  intros.
  inverts H.
  split.
  unfolds.
  intros.
  inverts H.
  splits; try unfolds ; simpl ; auto.
  split.
  inverts H.
  unfolds; simpl ; auto.
  splits; try unfolds; simpl ; auto.

  intros.
  subst.
  apply nth_upd_eq in H2.
  inverts H2.
  rewrite Int.and_assoc.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut.
  rewrite Int.and_not_self.
  auto.
  rewrite H.
  rewrite  Int.and_zero.
  auto.
  split.
  unfolds.
  intros.
  inverts H.
  split.
  inverts H.
  unfolds; simpl; auto.
  intros.
  inverts H.
}
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
  eapply update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.

Lemma RH_CurTCB_high_block_hold_mbox :
  forall ptcb tcbls prio st m qid time m',
    RH_CurTCB ptcb tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m) ->
    RH_CurTCB ptcb (TcbMod.set tcbls ptcb
        (prio, wait (os_stat_mbox qid) time, m')).
Proof.
  introv Hr Ht.
  unfolds in Hr.
  mytac.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  unfolds.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
Qed.

Lemma RH_TCBList_ECBList_P_high_block_hold_mbox :
  forall ecbls tcbls pcur qid m ml wl prio  time m',
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    EcbMod.get ecbls qid = Some (absmbox ml, wl) ->
    TcbMod.get tcbls pcur = Some (prio, rdy, m) ->
    RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absmbox ml, pcur::wl)) (TcbMod.set tcbls pcur (prio, wait (os_stat_mbox qid) time, m')) pcur. 
Proof.
  introv Hr Ht He.
  unfolds in Hr.
  destruct Hr as (Hr3 & Hr2 & Hr1 & Hr4).
  unfolds.
  splits.
  Focus 3.
{
  unfolds.
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  simpl in H0.
  destruct H0.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
  assert (EcbMod.get ecbls eid = Some (absmbox n, wl) /\ In tid wl) by eauto.
  apply Hr1 in H0.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H1.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmbox n, wls) /\ In tid wls) by eauto.
  apply Hr1 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  exists ml.
  exists (tid::wl).
  splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
  simpl; left; auto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr1 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 2 eexists; splits; eauto.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  simpl.
  right; auto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
}
  Unfocus.
  Focus 2.
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid =Some (abssem n, wls) /\ In tid wls) by eauto.
  apply Hr2 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr2 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
}
  Unfocus.
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmsgq x y, qwaitset) /\ In tid qwaitset) by eauto.
  apply Hr3 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr3 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; splits; eauto.
}
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmutexsem n1 n2, wls) /\ In tid wls) by eauto.
  apply Hr4 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr4 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; splits; eauto.
  apply Mutex_owner_hold_for_set_tcb; eauto.
  eapply Mutex_owner_set; eauto.
  intro; mytac.
  unfolds in Hr4.
  mytac.
  auto.
}
Qed.


Lemma TcbMod_set_R_PrioTbl_P_hold :
  (*OSQPendPure*)
  forall ptbl tcbls ptcb pr st m st' m' av,
    R_PrioTbl_P ptbl tcbls av ->
    TcbMod.get tcbls ptcb = Some (pr, st, m) ->
    R_PrioTbl_P ptbl (TcbMod.set tcbls ptcb (pr,st',m')) av.
Proof.
  intros.
  unfold R_PrioTbl_P in *.
  mytac.
  intros.
  lets H100 : H H3 H4 H5.
  mytac.
  rewrite TcbMod.set_sem.
  unfold get in *; simpl in *.
  rewrite H6.
  remember (tidspec.beq ptcb tcbid) as bool; destruct bool.
  symmetry in Heqbool; apply tidspec.beq_true_eq in Heqbool.
  subst.
  rewrite H0 in H6.  
  inverts H6.
  eauto.
  eauto.
  intros.
  rewrite TcbMod.set_sem in H3.
  remember (tidspec.beq ptcb tcbid) as bool; destruct bool.
  inverts H3.
  symmetry in Heqbool; apply tidspec.beq_true_eq in Heqbool.
  subst.
  eapply H1; eauto.
  eapply H1; eauto.
  eapply  R_Prio_NoChange_Prio_hold; eauto.
Qed.



Lemma TCBList_P_tcb_block_hold'' :
  (*OSQPendPure*)
  forall v ptcb rtbl vl y bitx
         tcbls prio ry x1 tcs tcs' t m,
    0 <= Int.unsigned prio < 64 ->
    TcbMod.join (TcbMod.sig ptcb (prio, t, m)) x1 tcs ->
    TcbMod.join tcbls tcs tcs' -> 
    TCBList_P v vl rtbl tcbls ->
    y = Int.shru prio ($ 3) ->
    bitx = ($ 1) <<ᵢ (Int.and prio ($ 7)) ->
    prio_neq_cur tcbls ptcb  prio ->
    nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 ry) ->
    TCBList_P v vl (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (Int.and ry (Int.not bitx)))) tcbls.
Proof.
  introv Hran Htc Hy Hb Hpro Hnth.
  eapply TCBList_P_tcb_dly_hold'; eauto.
Qed.


Lemma TCBList_P_tcb_block_hold':
  (*OSQPendPure*)
  forall v ptcb rtbl vl y bitx
         tcbls prio ry tcs tcs' t m,
    0 <= Int.unsigned prio < 64 ->
    TcbMod.get  tcs ptcb = Some (prio, t, m)->
    TcbMod.join tcbls tcs tcs' -> 
    TCBList_P v vl rtbl tcbls ->
    y = Int.shru prio ($ 3) ->
    bitx = ($ 1) <<ᵢ (Int.and prio ($ 7)) ->
    prio_neq_cur tcbls ptcb  prio ->
    nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 ry) ->
    TCBList_P v vl (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (Int.and ry (Int.not bitx)))) tcbls.
Proof.
  intros.
  lets Hx:tcb_get_join H0.
  mytac.
  eapply TCBList_P_tcb_block_hold'';eauto.
Qed.



(* absinfer lemma *)
(* Lemma absinfer_mbox_post_exwt_succ: 
 *   forall P mqls x v wl tls t ct p st m m'  t' , 
 *     can_change_aop P ->  
 *     EcbMod.get mqls x = Some (absmbox m ,wl) ->
 *     ~ wl=nil ->
 *     GetHWait tls wl t' ->
 *     TcbMod.get tls t' = Some (p,st, m') ->
 *     absinfer
 *       ( <|| mbox_post (Vptr x :: Vptr v :: nil) ||>  ** 
 *             HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
 *       (<|| isched;;END (Some (Vint32 (Int.repr NO_ERR))) ||>  ** HECBList (EcbMod.set mqls x (absmbox m, (remove_tid t' wl))) ** HTCBList (TcbMod.set tls t' (p,rdy , (Vptr v)) ) ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   unfold mbox_post; intros.
 *   infer_branch 5%nat.
 *   eapply absinfer_trans.
 *   Focus 2.
 *   eapply absinfer_seq_end.
 *   3:sep auto.
 *   can_change_aop_solver.
 *   can_change_aop_solver.
 *   instantiate (1:= (Some (V$NO_ERR))).
 *   eapply absinfer_seq.
 *   can_change_aop_solver.
 *   can_change_aop_solver.
 *   tri_infer_prim.
 * 
 *   infer_part2.
 * Qed. *)

Lemma mbox_rh_tcblist_ecblist_p_hold: forall v'34 v'35 v'37 v w m m2, EcbMod.get v'34 v = Some (absmbox m, w) ->RH_TCBList_ECBList_P v'34 v'35 v'37 ->
                                                                      RH_TCBList_ECBList_P
                                                                        (EcbMod.set v'34 v (absmbox m2, w)) v'35 v'37.
Proof.
  intros.
  unfolds in H0.
  mytac.
  unfolds.
  mytac; [clear -H H0| clear -H H1; rename H1 into H0|clear -H H2; rename H2 into H0| clear -H H3; rename H3 into H0]; unfolds; unfolds in H0; mytac; intros; unfold get in *; simpl in *;

  try solve [eapply H0;
              mytac; eauto;
              assert ( eid = v \/ eid <> v)  as aa by tauto; destruct aa;[subst;
                                                                           rewrite EcbMod.set_a_get_a in e;[
                                                                             inversion e|
                                                                             apply CltEnvMod.beq_refl] 
                                                                         |
                                                                         rewrite EcbMod.set_a_get_a' in e;[
                                                                             eauto|
                                                                             apply tidspec.neq_beq_false];
                                                                         auto]]
  ;try solve[
         lets aaa : H1 H2;
         mytac;
         assert ( eid = v \/ eid <> v)  as aa by tauto; destruct aa;[subst eid;rewrite H in H3;inversion H3|
                                                                     rewrite EcbMod.set_a_get_a';[
                                                                         rewrite H3;
                                                                         eauto|
                                                                         apply tidspec.neq_beq_false;
                                                                           auto]]
       ]
  .

  assert (eid = v \/ eid <> v) as aa by tauto; destruct aa;[subst eid; rewrite EcbMod.set_a_get_a in H2|idtac].
  elim H2; intros.

  inversion H3.
  subst.
  eapply H0.
  splits; eauto.
  apply CltEnvMod.beq_refl.
  eapply H0.
  rewrite EcbMod.set_a_get_a' in H2.
  eauto.
  apply tidspec.neq_beq_false; auto.

  assert (eid = v \/ eid <> v) as aa by tauto; destruct aa. 
  subst.
  rewrite EcbMod.set_a_get_a.
  repeat eexists.
  lets aaa : H1 H2.
  mytac; auto.
  rewrite H in H3.
  inversion H3.
  subst.
  auto.
  apply CltEnvMod.beq_refl.

  rewrite EcbMod.set_a_get_a'.
  eapply H1.
  eauto.
  apply tidspec.neq_beq_false; auto.
  
  assert ( v= eid \/ v<> eid) by tauto.
  elim H4; intros.
  subst eid.

  lets aaa : H1 H3.
  simpljoin.
  rewrite H5 in H.
  inverts H.
 
  rewrite EcbMod.set_a_get_a' .
  eapply H1; eauto.
  go.
  eapply Mutex_owner_set.
  intro; mytac.
  auto.

Qed.


Lemma post_exwt_succ_pre_mbox
     : forall (v'36 v'13 : vallist) (v'12 : int32) 
         (v'32 : block) (v'15 : int32) (v'24 : block) 
         (v'35 v'0 : val) (v'8 : tid) (v'9 v'11 : EcbMod.map)
         (x : val) (x0 : maxlen) (x1 : waitset)
         (v'6 v'10 : EcbMod.map) (v'38 v'69 v'39 : int32) 
         (v'58 : block) (a : priority) (b : taskstatus) 
         (c :msg) (v'62 v'7 : TcbMod.map) 
         (vhold : addrval),
       v'12 <> Int.zero ->
       R_PrioTbl_P v'36 v'7 vhold ->
       RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
       R_ECB_ETbl_P (v'32, Int.zero)
         (V$OS_EVENT_TYPE_MBOX
          :: Vint32 v'12
             :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
         v'13) v'7 ->
       RH_TCBList_ECBList_P v'11 v'7 v'8 ->
       EcbMod.join v'9 v'10 v'11 ->
       EcbMod.joinsig (v'32, Int.zero) (absmbox x , x1) v'6 v'10 ->
       Int.unsigned v'12 <= 255 ->
       array_type_vallist_match Int8u v'13 ->
       length v'13 = ∘OS_EVENT_TBL_SIZE ->
       nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
       Int.unsigned v'38 <= 7 ->
       nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
       Int.unsigned v'69 <= 255 ->
       nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
       Int.unsigned v'39 <= 7 ->
       nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
       Vptr (v'58, Int.zero) ->
       TcbJoin (v'58, Int.zero) (a, b, c) v'62 v'7 ->
       a = (v'38<<ᵢ$ 3)+ᵢv'39/\ b<> rdy /\
       x1 <> nil /\
       GetHWait v'7 x1 (v'58, Int.zero) /\
       TcbMod.get v'7 (v'58, Int.zero) = Some (a, b, c)
.
Proof.
  intros.
  lets Hs :  tcbjoin_get_a  H16.
  unfolds in H3.
  unfolds in H1.
  unfolds in H0.
  unfolds in H2.
  destruct H2.
  destruct H17 as (H17&Htype).
  unfolds in H2.
  unfolds in H17.
  lets Hg : EcbMod.join_joinsig_get H4 H5.
  clear H4 H5.
  clear H16.
  assert ( Int.unsigned v'38 < 8) as Hx by omega.
  assert (Int.unsigned v'39 < 8) as Hy by omega.
  clear H10 H12.
  lets Hrs : math_xy_prio_cons Hx Hy.
  unfold nat_of_Z in H0.
  destruct H0 as (Hpr1 & Hpr2).
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  destruct Hpr2.
  apply H0 in Hs.
  destruct Hs;auto.
  lets Hnth : nth_val'_imp_nth_val_vptr H15.
  lets Hsd : Hpr1 Hrs Hnth.
  destruct Hsd as (st & m & Hst);auto.
  unfold get in *; simpl in *.

  rewrite Hs in Hst.
  inverts Hst.
  assert (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3)= v'38).
  eapply math_shrl_3_eq; eauto.
  eapply nat_8_range_conver; eauto.
  assert ( (Z.to_nat (Int.unsigned v'38))  < length v'13)%nat.
  rewrite H8.
  simpl.
  unfold Pos.to_nat; simpl.
  clear - Hx.
  mauto.
  lets Has : array_int8u_nth_lt_len H7 H4.
  destruct Has as (i & Hnthz & Hinsa).
  rewrite H11 in Hnthz.
  inverts Hnthz.
  assert ((((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7) = v'39).
  eapply math_8range_eqy; eauto.
  eapply  nat_8_range_conver; eauto.
  apply nth_val'_imp_nth_val_int in H11.
  assert ( Vint32 v'12 = Vint32 v'12) by auto.
  lets Hzs : H1 H11 H10.
  eapply  nat_8_range_conver; eauto.
  destruct Hzs.
  lets Has : math_8_255_eq H6 H9 H.
  assert (i <> $ 0).
  assert ($ 1<<ᵢ$ Z.of_nat ∘(Int.unsigned v'38) = $ 1<<ᵢv'38).
  clear -Hx.
  mauto.
  rewrite H18 in H16.
  apply H16 in Has.
  apply ltu_eq_false in Has.
  pose (Int.eq_spec i ($0)).
  rewrite Has in y.
  auto.
  assert (PrioWaitInQ (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39)) v'13).
  unfolds.
  rewrite Int.repr_unsigned in *.
  exists ( ((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7 ).
  exists (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3) ).
  rewrite H0 in *.
  exists i.
  splits; eauto.
  rewrite H5.
  eapply math_8_255_eq; eauto.
  destruct H2 as (H2'&H2''&H2&Hres).
  lets Hes : H2 H19.
  unfold V_OSEventType in Hes.
  simpl nth_val in Hes.
  assert (Some (V$OS_EVENT_TYPE_MBOX) = Some (V$OS_EVENT_TYPE_MBOX)) by auto.
  apply Hes in H20.
  clear Hes.
  rename H20 into Hes.
  destruct Hes as (td & nn &mm & Hge).
  destruct Hpr2 as (Hpr2 & Hpr3).
  unfolds in Hpr3.
  assert (td = (v'58, Int.zero)  \/ td <> (v'58, Int.zero) ) by tauto.
  destruct H20.
  Focus 2.
  lets Hass : Hpr3 H20 Hge Hs.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  rewrite Int.repr_unsigned in *.
  subst td.
  unfold get in *; simpl in *.
  rewrite Hs in Hge.
  inverts Hge.
  destruct H3 as (H3'&H3''&H3&Hres').
  destruct H3 as (Heg1 & Heg2).
  lets Hrgs : Heg2 Hs.
  destruct Hrgs as (xz &  qw & Hem & Hin).
  unfold get in *; simpl in *.
  rewrite Hg in Hem.
  inverts Hem.
  split.
  auto.
  split.
  intro; tryfalse.



  assert (qw = nil \/ qw <> nil) by tauto.
  destruct H3.
  subst qw.
  simpl in Hin; tryfalse.
  splits; auto.
  unfolds.
  splits; auto.
  do 3 eexists; splits; eauto.
  intros.
  assert (EcbMod.get v'11 (v'32, Int.zero) = Some (absmbox xz, qw) /\ In t' qw) .
  splits; auto.
  lets Habs : Heg1 H22.
  destruct Habs as (prio' & m' & n' & Hbs).
  do 3 eexists; splits; eauto.
  destruct H17 as (H17'&H17''&H17&Hres'').
  lets Hpro : H17 Hbs.
  destruct Hpro as (Hpro&Hss).
  clear Hss.
  unfolds in Hpro.
  destruct Hpro as (xa & xb & zz & Hran & Hxx & Hyy & Hnths & Hzz).
  subst xa xb.
  rewrite Int.repr_unsigned in *.
  lets Hat : math_highest_prio_select H13 H9 H11 Hnths  Hzz;
    try eapply int_usigned_tcb_range; try omega;
    eauto.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hzs : H1 Hnths H23.
  eapply nat_8_range_conver; eauto.
  try eapply int_usigned_tcb_range; eauto.  
  destruct Hzs.
  assert (zz = $ 0 \/ zz <> $ 0) by tauto.
  destruct H26.
  subst zz.
  rewrite Int.and_commut in Hzz.
  rewrite Int.and_zero in Hzz.
  unfold Int.one in *.
  unfold Int.zero in *.
  assert ($ 1<<ᵢ(prio'&ᵢ$ 7) <> $ 0 ).
  eapply math_prop_neq_zero2; eauto.
  tryfalse.
  assert (Int.ltu ($ 0) zz = true).
  clear - H26.
  int auto.
  assert (0<=Int.unsigned zz ).
  int auto.
  assert (Int.unsigned zz = 0).
  omega.
  rewrite <- H0 in H26.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  apply H25 in H27.
  assert ($ Z.of_nat ∘(Int.unsigned (Int.shru prio' ($ 3))) = (Int.shru prio' ($ 3))).
  clear -Hran.
  mauto.
  rewrite H28 in *.
  auto.
  lets Hasss : Hpr3 H20 Hs Hbs; eauto.
  unfolds.
  rewrite zlt_true; auto.
  assert (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < Int.unsigned prio' \/
          Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) = Int.unsigned prio').
  omega.
  destruct H23; auto; tryfalse.
  false.
  apply Hasss.
  apply unsigned_inj; eauto.
Qed.

Lemma get_tcb_stat_mbox
: forall (p : int32) (etbl : vallist) (ptbl : list val) 
         (tid : addrval) (tcbls : TcbMod.map) (abstcb : abstcb.B)
         (tcbls' : TcbMod.map) (vl rtbl : vallist) 
         (qid : addrval) (vle : list val) (vhold : addrval),
    0 <= Int.unsigned p < 64 ->
    array_type_vallist_match Int8u etbl ->
    length etbl = ∘OS_EVENT_TBL_SIZE ->
    prio_in_tbl p etbl ->
    nth_val' (Z.to_nat (Int.unsigned p)) ptbl = Vptr tid ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbJoin tid abstcb tcbls' tcbls ->
    TCBNode_P vl rtbl abstcb ->
    R_ECB_ETbl_P qid (V$OS_EVENT_TYPE_MBOX :: vle, etbl) tcbls ->
    V_OSTCBStat vl = Some (V$OS_STAT_MBOX).
Proof.
  introv Hran Harr Hlen Hpri Hnth Hr Htj Htn Hre.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 & Hre3).
  unfolds in Hre2.
  destruct Hre1 as (Hre1'&Hre1''&Hre1& _).
  unfolds in Hre1.
  unfolds in Htn.
  destruct abstcb.
  destruct p0.
  destruct Htn as (Hv1 & Hv2 &  Hrl & Hrc).
  funfold Hrl.
  rewrite H8 in H4.
  inverts H4.
  unfolds in Hrc.
  destruct Hrc as (_&_&_&Hrc).
  unfolds in Hrc.
  destruct Hrc as (_&_&_&Hrc&_).
  unfolds in Hrc.
  unfolds in Hpri.
  lets Hges : tcbjoin_get_a Htj.
  unfolds in Hr.
  destruct Hr.
  apply nth_val'_imp_nth_val_vptr in Hnth.
  lets Hs : H Hnth; eauto.
  assert (tid <> vhold) as Hnvhold.
  apply H4 in Hges;destruct Hges;auto.
  destruct Hs as (st & mm & Hgs);auto.
  unfold get in *; simpl in *.
  rewrite Hges in Hgs.
  inverts Hgs.
  assert (PrioWaitInQ (Int.unsigned p) etbl).
  unfolds.
  rewrite Int.repr_unsigned.
  remember (Int.shru p ($3)) as py.
  remember ( p&ᵢ$ 7) as px.
  lets Hrs : n07_arr_len_ex ∘(Int.unsigned py)  Harr Hlen.
  subst py.
  clear - H17.
  mauto.
  destruct Hrs as (vx & Hntht & Hin).
  do 3 eexists; splits; eauto.
  assert ( V_OSEventType (V$OS_EVENT_TYPE_MBOX :: vle) = Some (V$OS_EVENT_TYPE_MBOX)).
  unfolds.
  simpl; auto.
  lets Hsd : Hre1 H15 H20.
  mytac.
  rewrite Int.repr_unsigned in H21.
  assert (x = tid \/ x <> tid) by tauto.
  destruct H23.
  subst x.
  rewrite Hges in H21.
  inverts H21.
  eapply Hrc; eauto.
  unfolds in H22.
  lets Hfs : H22 H23 H21 Hges.
  tryfalse.
Qed.

Lemma msglist_p_compose_mbox
: forall (p : val) (qid : addrval) (mqls : EcbMod.map)
         (qptrl1 qptrl2 : list EventCtr) (i i1 : int32) 
         (a : val) (x3 p' : val) (v'41 : vallist)
         (msgqls1 msgqls2 : list EventData) (msgq : EventData)
         (mqls1 mqls2 : EcbMod.map) (mq : absecb.B) 
         (mqls' : EcbMod.map) (tcbls : TcbMod.map),
    R_ECB_ETbl_P qid
                 (V$OS_EVENT_TYPE_MBOX
                   :: Vint32 i :: Vint32 i1 ::  a :: x3 :: p' :: nil, v'41) tcbls ->
    ECBList_P p (Vptr qid) qptrl1 msgqls1 mqls1 tcbls ->
    ECBList_P p' Vnull qptrl2 msgqls2 mqls2 tcbls ->
    RLH_ECBData_P msgq mq ->
    EcbMod.joinsig qid mq mqls2 mqls' ->
    EcbMod.join mqls1 mqls' mqls ->
    ECBList_P p Vnull
              (qptrl1 ++
                      ((V$OS_EVENT_TYPE_MBOX
                         :: Vint32 i :: Vint32 i1 ::  a :: x3 :: p' :: nil, v'41)
                         :: nil) ++ qptrl2) (msgqls1 ++ (msgq :: nil) ++ msgqls2) mqls
              tcbls.
Proof.
  intros.
  simpl.
  eapply ecblist_p_compose; eauto.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits; eauto.
  unfolds; simpl; auto.
Qed.


Lemma TCBList_P_post_mbox
: forall (v'42 : val) (v'48 : list vallist) (v'47 : TcbMod.map)
         (v'60 : val) (v'50 : list vallist) (v'37 : vallist)
         (v'59 v'49 v'44 : TcbMod.map) (v'63 v'64 v'65 : val)
         (v'51 v'52 v'53 v'54 v'55 v'56 : int32) (x00 : addrval)
         (v'58 : block) (v'40 v'38 : int32) (prio : priority)
         (st : taskstatus) (msg0 :msg)
         (v'7 v'62 v'43 : TcbMod.map) (v'36 : vallist) 
         (v'39 : int32) (v'13 : vallist) (vhold : addrval),
    Int.unsigned v'38 <= 7 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    prio_in_tbl ((v'38<<ᵢ$ 3)+ᵢv'39) v'13 ->
    RL_RTbl_PrioTbl_P v'13 v'36 vhold ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
    Vptr (v'58, Int.zero) ->
    R_PrioTbl_P v'36 v'7 vhold ->
    array_type_vallist_match Int8u v'37 ->
    length v'37 = ∘OS_RDY_TBL_SIZE ->
    TcbMod.join v'44 v'43 v'7 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg0) v'62 v'7 ->
    get_last_tcb_ptr v'48 v'42 = Some (Vptr (v'58, Int.zero)) ->
    TCBList_P v'42 v'48 v'37 v'47 ->
    TCBList_P v'60 v'50 v'37 v'59 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg0) v'59 v'49 ->
    TcbMod.join v'47 v'49 v'44 ->
    TCBNode_P
      (v'60
         :: v'63
         :: v'64
         :: v'65
         :: Vint32 v'51
         :: V$OS_STAT_MBOX
         :: Vint32 v'52
         :: Vint32 v'53
         :: Vint32 v'54
         :: Vint32 v'55 :: Vint32 v'56 :: nil) v'37
      (prio, st, msg0) ->
    TCBList_P v'42
              (v'48 ++
                    (v'60
                       :: v'63
                       :: Vnull
                       :: Vptr x00
                       :: V$0
                       :: V$0
                       :: Vint32 v'52
                       :: Vint32 v'53
                       :: Vint32 v'54
                       :: Vint32 v'55 :: Vint32 v'56 :: nil)
                    :: v'50)
              (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                              (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37)
                                     (Vint32 v'40))))
              (TcbMod.set v'44 (v'58, Int.zero) (prio, rdy, Vptr x00)).
Proof.
  intros.
  unfolds in H5.
  destruct H5 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H H0.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H4.
  lets Hps : Ha1 H5 H4.
  
  lets Hgs : tcbjoin_get_a H9.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in Hgs.
  destruct Hgs;auto.
  apply Hps in Hnvhold.
  clear Hps.
  mytac.
  unfold get in *; simpl in *.
  rewrite H16 in Hgs.
  inverts Hgs.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  lets Hps : tcbjoin_set_ex (prio,st,msg0) (prio,rdy,Vptr x00)  H14;eauto.
  destruct Hps as (b&Htx & Hty).
  remember (val_inj
              (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))) as Hv.
  assert (0<= Z.to_nat (Int.unsigned v'38) <8)%nat.
  clear -H.
  mauto.
  lets Hsx : n07_arr_len_ex H6 H7; eauto.
  destruct Hsx as (vx & Hnth & Hi).
  lets Hns :  nth_val_nth_val'_some_eq  Hnth.
  rewrite Hns in HeqHv.
  simpl in HeqHv.
  subst Hv.
  assert (v'38 = Int.shru prio ($ 3)).
  subst.
  clear - H H0.
  mauto.
  rewrite H19.
  assert (v'40 = ($ 1<<ᵢ(prio &ᵢ$ 7))).  
  rewrite Heqprio.
  rewrite Heqpx.
  assert ((((v'38<<ᵢ$ 3)+ᵢpy)&ᵢ$ 7) = py).
  clear -H H0.
  mauto.
  rewrite H20.
  clear -H0 H1.
  mautoext.
  rewrite H20.
  eapply TCBList_P_Combine; eauto.
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
  rewrite <-H19.
  auto.
  intros.
  unfolds in Ha3.
  lets Hsx : tcbjoin_join_get_neq H13 H14 H21.
  destruct Hsx.
  eapply Ha3; eauto.
  lets Hacb  :  TcbMod.join_get_l H8 H23; eauto.
  simpl.
  do 4 eexists; splits; eauto.
  unfolds; simpl; eauto.
  exact Htx.
  unfolds.
  auto.
  fsimpl.
  usimpl H15.
  usimpl H22.
  splits.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  funfold H23.
  unfolds.
  do 6 eexists; splits; try solve [unfolds; simpl;auto].
  omega.
  splits; eauto.
  eexists.
  split.
  unfolds;simpl; eauto.
  auto.
  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  splits; try solve [unfolds; simpl;auto].
  eexists; eauto.
  unfolds.
  intros.
  inverts H15.
  splits; try solve [unfolds; simpl;auto].
  unfolds.
  splits; try solve [unfolds; simpl;auto].
  apply prio_in_tbl_orself ; auto.
  unfolds.
  splits.
  unfolds.
  intros.
  usimpl H22.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  usimpl H25.
  false.
  rewrite H26 in H19.
  rewrite H19 in Hnth.
  rewrite H26 in H17.
  rewrite H26 in H22.
  lets Hfs :  prio_notin_tbl_orself  H17 Hnth.
  tryfalse.

  unfolds.
  intros.
  usimpl H22.
  unfolds.
  intros.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  usimpl H25.

  unfolds.
  intros.
  usimpl H22.
  unfolds.
  intros.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  usimpl H25.
  
  unfolds.
  splits; try solve [
                unfolds;
                introv Hf; inverts Hf].
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
  rewrite <-H19.
  auto.
  intros.
  lets Hnas : tcbjoin_tid_neq H13 H21.
  unfolds in Ha3.
  eapply Ha3; eauto.
  lets Haxc  : TcbMod.join_get_r H13 H21.
  lets Haa : TcbMod.join_get_r H14 Haxc.
  lets Ad :  TcbMod.join_get_l H8 Haa; eauto.
Qed.

  Lemma ECBList_P_Set_Rdy_hold_mbox
  : forall (a : list EventCtr) (tcbls : TcbMod.map) 
           (tid : tidspec.A) (prio : priority) (msg0 msg' : msg) 
           (x y : val) (b : list EventData) (c : EcbMod.map) 
           (eid : ecbid) (nl : int32),
      TcbMod.get tcbls tid = Some (prio, wait (os_stat_mbox eid) nl, msg0) ->
      EcbMod.get c eid = None ->
      ECBList_P x y a b c tcbls ->
      ECBList_P x y a b c (TcbMod.set tcbls tid (prio, rdy, msg')).
Proof.
  inductions a; intros.
  simpl in *; auto.
  simpl in H1.
  mytac.
  destruct b; tryfalse.
  destruct a.
  mytac.
  simpl.
  eexists.
  splits; eauto.
  unfolds.
  unfolds in H2.

  splits.
  
  destructs H2.
  unfolds in H2.
  mytac.
  unfolds.
  splits; unfolds;intros.

  apply H2 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  
  apply H8 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H9 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H10 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.



  
  unfolds.
  destructs H2;unfolds in H6;destructs H6.
  splits;intros prio' mg ng x3 Hti;
  assert (tid = x3
          \/ tid <> x3) by tauto.
  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H6; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H8; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H9; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti;  auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H10; eauto.

  mytac;auto.


  do 3 eexists; splits; eauto.
  eapply IHa; eauto.
  eapply ecbmod_joinsig_get_none; eauto.
Qed.

Lemma ecblist_p_post_exwt_hold_mbox
: forall (v'36 : vallist) (v'12 : int32) (v'13 : vallist)
         (v'38 v'69 v'39 : int32) (v'58 : block) (v'40 : int32)
         (v'32 : block) (v'15 : int32) (v'24 : val)
         (v'35 v'16 v'18 v'19 v'20 v'34 : val) (v'21 v'22 : int32)
         (v'23 : block) (v'25 v'26 : val) (v'27 : vallist)
         (x : list msg) (x0 : maxlen) (x1 : waitset) 
         (v'0 : val) (v'1 : list EventCtr) (v'5 : list EventData)
         (v'6 : EcbMod.map) (v'7 : TcbMod.map) (x00 : addrval)
         (v'11 : EcbMod.map) (v'31 : list EventData) 
         (v'30 : list EventCtr) (v'29 : val) (v'10 v'9 : EcbMod.map)
         (prio : priority) (v'62 : TcbMod.map) (st : taskstatus)
         (msg0 : msg) (y : int32) (vhold : addrval),
    (* RL_RTbl_PrioTbl_P v'13 v'36 vhold -> *)
    True ->
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
    Vptr (v'58, Int.zero) ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_MBOX
                   :: Vint32 v'12
                   :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil,
                  v'13) v'7 ->
    RLH_ECBData_P
      (DMbox v'24) (absmbox v'24, x1) ->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr (v'32, Int.zero)) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig (v'32, Int.zero) (absmbox v'24, x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg0) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold ->
    x1 <> nil ->
    ECBList_P v'29 Vnull
              (v'30 ++
                    ((V$OS_EVENT_TYPE_MBOX
                       :: Vint32 y
                       :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil,
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                                     (Vint32 (v'69&ᵢInt.not v'40))) :: nil) ++ v'1)
              (v'31 ++
                    (DMbox v'24 ::nil)
                    ++ v'5)
              (EcbMod.set v'11 (v'32, Int.zero)
                          (absmbox v'24, remove_tid (v'58, Int.zero) x1))
              (TcbMod.set v'7 (v'58, Int.zero) (prio, rdy, Vptr x00))
.
Proof.
  intros.
  unfolds in H21.
  destruct H21 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H5 H9.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H10.
  lets Hps : Ha1 H21 H10.
  apply tcbjoin_get_a in H20.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in H20.
  destruct H20;auto.
  destruct Hps as (sts & mg & Hget);auto.
  unfold get in *; simpl in *.
  rewrite Hget in H20.
  inverts H20.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  unfolds in H14.
  destruct H14 as (Ha & Hb & Hc).
  destruct Ha as (Ha''&Ha'&Ha&Ha''').
  destruct Hb as (Hb''&Hb'&Hb&Hb''').
  lets Hz : math_unmap_get_y H1 H4.
  lets Heq1 :  math_mapval_core_prop H11; eauto.
  omega.
  subst v'40.
  assert (v'38 = Int.shru prio ($3)).
  subst.
  clear -Hz H9.
  mauto.
  assert (py = prio &ᵢ $ 7).
  subst prio. 
  rewrite Heqpx.
  clear -Hz H9.
  mauto.
  rewrite H14 in H6.
  assert (PrioWaitInQ (Int.unsigned prio) v'13) as Hcp.
  unfolds.
  do 3 eexists; splits; eauto.
  rewrite Int.repr_unsigned.
  eapply nth_val'_imp_nth_val_int; eauto.
  rewrite Int.repr_unsigned.
  rewrite <- H20.
  unfold Int.one.
  eapply math_8_255_eq; eauto.
  
  unfold Int.zero in H0.
  rewrite <-H14 in *.
  lets Hneq :  rl_tbl_grp_neq_zero H1 H0  H4 H6 H13.
  omega.
  auto.
  lets Hecp : Ha Hcp.
  unfold V_OSEventType in Hecp.
  simpl nth_val in Hecp.
  assert (Some (V$OS_EVENT_TYPE_MBOX) = Some (V$OS_EVENT_TYPE_MBOX)) by auto.
  apply Hecp in H23.
  clear Hecp.
  rename H23 into Hecp.
  destruct Hecp as (ct & nl & mg & Hcg).
  assert (ct = tid) as Hed.
  assert (ct = tid \/ ct <> tid)  by tauto.
  destruct H23; auto.
  lets Heqs : Ha3 H23 Hcg Hget.
  rewrite Int.repr_unsigned in Heqs.
  tryfalse.
  subst ct.
  unfold get in *; simpl in *.
  rewrite Hget in Hcg.
  inversion Hcg.
  subst mg st .
  clear Hcg.
  
  lets Hsds : ecb_set_join_join  (absmbox v'24, remove_tid tid x1)  H18  H19.
  destruct Hsds as ( vv & Hsj1 & Hsj2).

  eapply msglist_p_compose_mbox.
  instantiate (1:= (v'32, Int.zero)).
  unfolds.
  splits.
  unfolds.
  splits;unfolds.
  Focus 3.
  
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).
  rewrite H14 in Hprs1.
  rewrite H20 in Hprs1.
  lets Hrs : prio_wt_inq_tid_neq  H6 H21 .
  destruct Hrs as (Hrs & _).
  apply Hrs in Hprs1.
  destruct Hprs1 as (Hpq & Hneq).
  lets Hxs : Ha Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  unfold get in *; simpl in *.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  intros.
  unfolds in H25;simpl in H25;tryfalse.
  intros.
  unfolds in H25;simpl in H25;tryfalse.
  intros.
  unfolds in H25;simpl in H25;tryfalse.
  


  unfolds.
  splits;
    intros prio' mm nn tid'.
  Focus 3.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.

  lets Hrs : prio_wt_inq_tid_neq  H6 H21 .
  destruct Hrs as (_ & Hrs).
  apply Hrs in H25.
  rewrite H20.
  rewrite H14.
  auto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H23.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H23 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  simpl fst in Hc;simpl;auto.
  
  instantiate (1:=v'9).


  
  eapply ECBList_P_Set_Rdy_hold_mbox;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply joinsig_join_getnone; eauto.
  instantiate (1:=v'6).
  eapply ECBList_P_Set_Rdy_hold_mbox;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply  joinsig_get_none; eauto.
  3:eauto.
  2:eauto.
  unfolds.
  splits; auto.
  unfolds.
    destruct H15; intros.
   destruct H23; intros.
  splits; intros; auto; tryfalse.
  apply H23 in H26.
  subst x1.
  simpl.
  auto.
Qed.



Lemma rh_tcblist_ecblist_p_post_exwt_mbox
: forall (v'8 tid : tid) (v'11 : EcbMod.map) 
         (v'7 : TcbMod.map) (v'9 v'10 : EcbMod.map) 
         (eid : tidspec.A) (x : val) 
         (x0 : maxlen) (x1 : waitset) (v'6 : EcbMod.map) 
         (prio : priority) (msg0 : msg) 
         (x00 : addrval) (xl : int32),
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig eid (absmbox x , x1) v'6 v'10 ->
    In tid x1 ->
    TcbMod.get v'7 tid = Some (prio, wait (os_stat_mbox eid) xl, msg0) ->
    RH_TCBList_ECBList_P
      (EcbMod.set v'11 eid (absmbox x, remove_tid tid x1))
      (TcbMod.set v'7 tid (prio, rdy, Vptr x00)) v'8
.
Proof.
  intros.
  unfolds.
  splits.
  Focus 3.
  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hy&Hx&H&Hz).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H7.
  subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert (EcbMod.get v'11 eid = Some (absmbox x, x1)/\ In tid0 x1 ).
  splits; auto.
  lets Hsa : H H7.
  mytac.
  unfold get in *; simpl in *.

  rewrite H3 in H8.
  inverts H8.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8.
  subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  apply  in_wtset_rm_notin in H9.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmbox n, wls) /\ In tid0 wls ).

  splits; auto.
  lets Hsc : H H10.
  mytac.
  rewrite H3 in H11.
  inverts H11.
  tryfalse.
  rewrite TcbMod.set_sem .
  rewrite tidspec.neq_beq_false; auto.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8.
  subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  lets Hbss :tidneq_inwt_in  x1 H7.
  destruct Hbss as (Hbss & _).
  lets Hbssc : Hbss H5.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert ( EcbMod.get v'11 eid0 = Some (absmbox n, x1) /\ In tid0 x1 ).
  splits; auto.
  apply H in H4.
  mytac.
  do 3 eexists; eauto.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert ( EcbMod.get v'11 eid0 = Some (absmbox n, wls)/\ In tid0 wls ).
  splits; auto.
  apply H in H9.
  mytac.
  do 3 eexists; eauto .
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H5.
  subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  
  unfolds in H.
  destruct H as (H6 & H7 & H & H8).
  destruct H.
  apply H9 in H4.
  mytac.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H11.
  subst.
  unfold get in *; simpl in *.
  rewrite H4 in Hget.
  inverts Hget.
  lets Hbss :tidneq_inwt_in  x1 H5.
  destruct Hbss as (_ & Hbss).
  lets Hbssc : Hbss H10.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 2 eexists; splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.


  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (H&_).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmsgq x2 y, qwaitset) /\ In tid0 qwaitset).
  split;auto.
  apply H in H8.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H9;subst.
  unfold get in *; simpl in *.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (H&_).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  mytac.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in *; simpl in *.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists;split;eauto.

  
  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&H&_).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (abssem n, wls) /\ In tid0 wls).
  split;auto.
  apply H in H8.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H9;subst.
  unfold get in *; simpl in *.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&H&_).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  mytac.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in *; simpl in *.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists;split;eauto.

  
  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&Hhh&Hx&H).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmutexsem n1 n2, wls) /\ In tid0 wls).
  split;auto.
  apply H in H8.
  destruct H6 as (H6 & HHHHH).
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H9;subst.
  unfold get in *; simpl in *.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&Hx&Hhh&H).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  destruct H5 as (H5 & HHHHH).
  mytac.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in *; simpl in *.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists;split;eauto.

  apply Mutex_owner_hold_for_set_tcb.
  eapply Mutex_owner_set; eauto.
  intro; mytac.
  unfolds in H.
  mytac.
  unfolds in H6; mytac.
  auto.
Qed.

Lemma rh_tcblist_ecblist_p_post_exwt_aux_mbox
: forall (v'8 tid0 : tid) (v'11 : EcbMod.map) 
         (v'7 : TcbMod.map) (v'9 v'10 : EcbMod.map) 
         (eid : tidspec.A) (x : val) 
         (x0 : maxlen) (x1 : waitset) (v'6 : EcbMod.map) 
         (prio : priority) (msg0 : msg) 
         (st : taskstatus),
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig eid (absmbox x, x1) v'6 v'10 ->
    In tid0 x1 ->
    TcbMod.get v'7 tid0 = Some (prio, st, msg0) ->
    exists xl, st = wait (os_stat_mbox eid) xl
.
  intros.
  unfolds in H.
  destruct H as (Hexaa & Hexa & Hex & Hexaaa).
  lets Hget : EcbMod.join_joinsig_get H0 H1.
  assert (EcbMod.get v'11 eid = Some (absmbox x, x1) /\ In tid0 x1).
  split; auto.
  apply Hex in H.
  mytac.
  unfold get in *; simpl in *.
  rewrite H3 in H.
  inverts H.
  eauto.
Qed.


Lemma TCBList_P_post_msg_mbox
: forall (v'42 : val) (v'48 : list vallist) (v'47 : TcbMod.map)
         (v'60 : val) (v'50 : list vallist) (v'37 : vallist)
         (v'59 v'49 v'44 : TcbMod.map) (v'63 v'64 v'65 : val)
         (v'51 v'52 v'53 v'54 v'55 v'56 : int32) (x00 : addrval)
         (v'58 : block) (v'40 v'38 : int32) (prio : priority)
         (st : taskstatus) (msg : msg)
         (v'7 v'62 v'43 : TcbMod.map) (v'36 : vallist) 
         (v'39 : int32) (v'13 : vallist) (vhold : addrval),
    Int.unsigned v'38 <= 7 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    prio_in_tbl ((v'38<<ᵢ$ 3)+ᵢv'39) v'13 ->
    RL_RTbl_PrioTbl_P v'13 v'36 vhold ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
    Vptr (v'58, Int.zero) ->
    R_PrioTbl_P v'36 v'7 vhold ->
    array_type_vallist_match Int8u v'37 ->
    length v'37 = ∘OS_RDY_TBL_SIZE ->
    TcbMod.join v'44 v'43 v'7 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg) v'62 v'7 ->
    get_last_tcb_ptr v'48 v'42 = Some (Vptr (v'58, Int.zero)) ->
    TCBList_P v'42 v'48 v'37 v'47 ->
    TCBList_P v'60 v'50 v'37 v'59 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg) v'59 v'49 ->
    TcbMod.join v'47 v'49 v'44 ->
    TCBNode_P
      (v'60
         :: v'63
         :: v'64
         :: v'65
         :: Vint32 v'51
         :: V$OS_STAT_MBOX
         :: Vint32 v'52
         :: Vint32 v'53
         :: Vint32 v'54
         :: Vint32 v'55 :: Vint32 v'56 :: nil) v'37
      (prio, st, msg) ->
    TCBList_P v'42
              (v'48 ++
                    (v'60
                       :: v'63
                       :: Vnull
                       :: Vptr x00
                       :: V$0
                       :: Vint32 ($ OS_STAT_MBOX&ᵢInt.not ($ OS_STAT_MBOX))
                       :: Vint32 v'52
                       :: Vint32 v'53
                       :: Vint32 v'54
                       :: Vint32 v'55 :: Vint32 v'56 :: nil)
                    :: v'50)
              (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                              (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37)
                                     (Vint32 v'40))))
              (TcbMod.set v'44 (v'58, Int.zero) (prio, rdy, Vptr x00)).
Proof.
  intros.
  unfolds in H5.
  destruct H5 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H H0.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H4.
  lets Hps : Ha1 H5 H4.
  
  lets Hgs : tcbjoin_get_a H9.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in Hgs.
  destruct Hgs;auto.
  apply Hps in Hnvhold.
  clear Hps.
  mytac.
  unfold get in *; simpl in *.
  rewrite H16 in Hgs.
  inverts Hgs.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  lets Hps : tcbjoin_set_ex (prio,st,msg) (prio,rdy,Vptr x00)  H14;eauto.
  destruct Hps as (b&Htx & Hty).
  remember (val_inj
              (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))) as Hv.
  assert (0<= Z.to_nat (Int.unsigned v'38) <8)%nat.
  clear -H.
  mauto.
  lets Hsx : n07_arr_len_ex H6 H7; eauto.
  destruct Hsx as (vx & Hnth & Hi).
  lets Hns :  nth_val_nth_val'_some_eq  Hnth.
  rewrite Hns in HeqHv.
  simpl in HeqHv.
  subst Hv.
  assert (v'38 = Int.shru prio ($ 3)).
  subst.
  clear - H H0.
  mauto.
  rewrite H19.
  assert (v'40 = ($ 1<<ᵢ(prio &ᵢ$ 7))).  
  rewrite Heqprio.
  rewrite Heqpx.
  assert ((((v'38<<ᵢ$ 3)+ᵢpy)&ᵢ$ 7) = py).
  clear -H H0.
  mauto.
  rewrite H20.
  clear -H0 H1.
  mautoext.
  rewrite H20.
  eapply TCBList_P_Combine; eauto.
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
  rewrite <-H19.
  auto.
  intros.
  unfolds in Ha3.
  lets Hsx : tcbjoin_join_get_neq H13 H14 H21.
  destruct Hsx.
  eapply Ha3; eauto.
  lets Hacb  :  TcbMod.join_get_l H8 H23; eauto.
  simpl.
  do 4 eexists; splits; eauto.
  unfolds; simpl; eauto.
  exact Htx.
  unfolds.
  fsimpl.
  usimpl H15.
  usimpl H22.
  splits.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  funfold H23.
  unfolds.
  do 6 eexists; splits; try solve [unfolds; simpl;auto].
  omega.
  splits; eauto.
  eexists.
  split.
  unfolds;simpl; eauto.
  auto.
  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  splits; try solve [unfolds; simpl;auto].
  eexists; eauto.
  unfolds.
  intros.
  inverts H15.
  splits; try solve [unfolds; simpl;auto].
  unfolds.
  splits; try solve [unfolds; simpl;auto].
  apply prio_in_tbl_orself ; auto.
  unfolds.
  splits.
  unfolds.
  intros.
  usimpl H22.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  usimpl H25.
  false.
  rewrite H26 in H19.
  rewrite H19 in Hnth.
  rewrite H26 in H17.
  rewrite H26 in H22.
  lets Hfs :  prio_notin_tbl_orself  H17 Hnth.
  tryfalse.

  unfolds.
  intros.
  usimpl H22.
  unfolds.
  intros.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  usimpl H25.

  unfolds.
  intros.
  usimpl H22.
  unfolds.
  intros.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  usimpl H25.
  
  unfolds.
  splits; try solve [
                unfolds;
                introv Hf; inverts Hf].
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
  rewrite <-H19.
  auto.
  intros.
  lets Hnas : tcbjoin_tid_neq H13 H21.
  unfolds in Ha3.
  eapply Ha3; eauto.
  lets Haxc  : TcbMod.join_get_r H13 H21.
  lets Haa : TcbMod.join_get_r H14 Haxc.
  lets Ad :  TcbMod.join_get_l H8 Haa; eauto.
Qed.

Lemma statmbox_and_not_statmbox_eq_rdy : Int.eq ($ OS_STAT_MBOX&ᵢInt.not ($ OS_STAT_MBOX)) ($ OS_STAT_RDY) = true.
Proof.
  unfold OS_STAT_MBOX, OS_STAT_RDY.
  unfold Int.not.
  unfold Int.xor.
  unfold Z.lxor.
  int auto.
  compute.
  split; intros; tryfalse.
  int auto.
  compute.
  intro; tryfalse.
  compute.
  intro; tryfalse.
  compute.
  split; intros; tryfalse.
Qed.

Lemma tcb_inrtbl_not_vhold: forall v'42 v'62 v'93 v'57 v'81, RL_RTbl_PrioTbl_P v'42 v'62 v'93 ->  prio_in_tbl ((v'57)) v'42 -> nth_val' (Z.to_nat (Int.unsigned ((v'57)))) v'62 =  Vptr (v'81, Int.zero) ->   0 <= Int.unsigned v'57 < 64 -> (v'81, Int.zero) <> v'93.
Proof.
  introv H H0 H1 asdfasfd.
  unfolds in H.
  lets adaf: H H0.
  auto.
  mytac.
  apply nth_val_nth_val'_some_eq in H2.
  rewrite H1 in H2.
  inverts H2.
  auto.
Qed.

Lemma le7_le7_range64:  forall v'57 v'59, Int.unsigned v'57 <= 7 -> Int.unsigned v'59 <= 7 ->  0 <= Int.unsigned ((v'57<<ᵢ$ 3)+ᵢv'59) < 64.
  intros.
  mauto.
Qed.



(* absinfer lemma *)
(* Lemma absinfer_mbox_post_put_mail_return : forall P x m mqls tcbls t ct,
 *                                            can_change_aop P ->
 *                                            EcbMod.get mqls x = Some (absmbox Vnull, nil) ->
 *                                            absinfer (<|| mbox_post (Vptr x :: Vptr m ::nil) ||> **HECBList mqls** HTCBList tcbls ** HTime t ** HCurTCB ct ** P) (<|| END (Some (Vint32 (Int.repr MBOX_POST_SUCC))) ||> **HECBList (EcbMod.set mqls x (absmbox (Vptr m),nil))** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   infer_solver 6%nat.
 * Qed.
 * 
 * 
 * Lemma absinfer_mbox_post_null_return : forall P x, 
 *                                        can_change_aop P ->
 *                                        tl_vl_match  ((Void) ∗ :: nil) x = true ->
 *                                        absinfer (<|| mbox_post (Vnull :: x) ||> ** P) ( <|| END (Some (Vint32 (Int.repr MBOX_POST_NULL_ERR))) ||> ** P).
 * Proof.
 *   infer_solver 0%nat.
 * Qed.
 * 
 * Lemma absinfer_mbox_post_msg_null_return:
 *   forall P v, 
 *     can_change_aop P -> 
 *     absinfer
 *       ( <|| mbox_post (Vptr v :: Vnull ::nil) ||>  **
 *             P) (<|| END (Some (Vint32 (Int.repr  OS_ERR_POST_NULL_PTR))) ||>  **
 *                     P).
 * Proof.
 *   infer_solver 1%nat.
 * Qed.
 * 
 * Lemma absinfer_mbox_post_p_not_legal_return : forall x a P b tcbls t ct, 
 *                                               can_change_aop P ->
 *                                               EcbMod.get x a = None ->
 *                                               absinfer (<|| mbox_post (Vptr a ::Vptr b:: nil) ||> ** HECBList x** HTCBList tcbls ** HTime t ** HCurTCB ct  **
 *                                                           P) ( <|| END (Some  (V$ MBOX_POST_P_NOT_LEGAL_ERR)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct  ** P).
 * Proof.
 *   infer_solver 2%nat.
 * Qed.
 * 
 * Lemma absinfer_mbox_post_wrong_type_return : forall x a b P tcbls t ct, 
 *                                              can_change_aop P ->
 *                                              (exists d,
 *                                                 EcbMod.get x a = Some d /\ ~ (exists x wls, d = (absmbox x, wls))) ->
 *                                              absinfer (<|| mbox_post (Vptr a :: Vptr b :: nil) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct **
 *                                                          P) ( <|| END (Some  (V$MBOX_POST_WRONG_TYPE_ERR)) ||> ** HECBList x ** HTCBList tcbls ** HTime t ** HCurTCB ct ** P).
 * Proof.
 *   infer_solver 3%nat.
 *   destruct x0.
 *   repeat tri_exists_and_solver1.
 *   intro.
 *   apply H2.
 *   mytac.
 *   eauto.
 * Qed. *)

(* Lemma absinfer_mbox_post_full_return :   forall P mqls x a wl y tcbls t ct, 
 *                                          can_change_aop P ->  
 *                                          EcbMod.get mqls x = Some (absmbox a,wl) ->
 *                                          (exists b, a= Vptr b) ->
 *                                          absinfer
 *                                            ( <|| mbox_post (Vptr x :: Vptr y :: nil) ||>  **HECBList mqls ** 
 *                                                  HTCBList tcbls ** HTime t ** HCurTCB ct ** P) 
 *                                            (<|| END (Some (Vint32 (Int.repr MBOX_POST_FULL_ERR))) ||> **HECBList mqls ** HTCBList tcbls ** HTime t ** HCurTCB ct  ** P).
 * Proof.
 *   infer_solver 4%nat.
 * Qed. *)

Lemma something_in_not_nil : forall (T:Type) (y: @list T), y<>nil -> exists x, In x y.
Proof.
  intros T y.
  elim y.
  intro; tryfalse.
  intros.
  exists a.
  simpl.
  left; auto.
Qed.

Lemma rg1 :  forall x2 x6 ,  0 <= Int.unsigned x2 < 64->
                             x6 = $ Int.unsigned x2&ᵢ$ 7 ->
                             0<= Int.unsigned x6 < 8.
Proof.
  intros.
  subst x6.

  mauto.
Qed.

Lemma rg2 :  forall x2 x7 ,  0 <= Int.unsigned x2 < 64->
                             x7 = Int.shru ($ Int.unsigned x2) ($ 3) ->
                             0<= Int.unsigned x7 < 8.
Proof.
  intros.
  subst x7.
  mauto.
Qed.

Lemma post_exwt_succ_pre_mbox'
: forall (v'36 v'13 : vallist) (v'12 : int32) 
         (v'32 : block) (v'15 : int32) (v'24 : val) 
         (v'35 v'0 : val) (v'8 : tid) (v'9 v'11 : EcbMod.map)
         (x : val) (x1 : waitset)
         (v'6 v'10 : EcbMod.map) (v'38 v'69 v'39 : int32) 
         (v'58 : block) (a : priority)
         (c : msg) (v'62 v'7 : TcbMod.map) 
         (vhold : addrval),
    v'12 = Int.zero ->
    R_PrioTbl_P v'36 v'7 vhold ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_MBOX
                   :: Vint32 v'12
                   :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil,
                  v'13) v'7 ->
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig (v'32, Int.zero) (absmbox x , x1) v'6 v'10 ->
    x1 = nil
.
Proof.
  intros.
  unfolds in H2.
  destruct H2 as (H2 & H2' & _).
  destruct H2 as (_ & _ & H2 & _).
  destruct H2' as (_ & _ & H2' & _).
  unfolds in H2.
  unfolds in H2'.
  

  unfolds in H3.
  unfolds in H1.
  unfolds in H0.
  destruct H3 as (_ & _ & H3 & _).
  unfolds in H3.
  destruct H3 as (H3 & H3').

  lets Hg : EcbMod.join_joinsig_get H4 H5.
  clear H4 H5.
  assert ( x1 = nil \/ x1 <> nil) by tauto.
  destruct H4; intros; auto.

  idtac.
  apply something_in_not_nil in H4.
  inversion H4.
  assert (EcbMod.get v'11 (v'32, Int.zero) = Some (absmbox x, x1) /\ In x0 x1) by tauto.
  lets aadf : H3 H6.
  mytac.
  lets bbdf : H2' H7.
  destruct bbdf.
  unfolds in H.
  do 3 destruct H.
  destruct H as (Ha & Hb & Hc & Hd& He).
  cut ( 0<=(∘(Int.unsigned x7)) <8)%nat.
  intro.
  assert (V$0 = V$0) by auto.
  lets adfafd : H1 H Hd H12.
  destruct adfafd.
  destruct H13.
  destruct H14.
  cut ( $ 0&ᵢ($ 1<<ᵢ$ Z.of_nat ∘(Int.unsigned x7)) = $ 0).
  intro.
  apply H13 in H17.
  subst x8.

  lets rg : rg1 Ha Hb.
  clear -He rg.
  false.
  gen He.
  mauto.

  lets rg : rg2 Ha Hc.
  clear -rg.
  mauto.

  lets rg : rg2 Ha Hc.
  clear -rg.
  mauto.
Qed.

Lemma val_inj_lemma: forall m0 a,  val_inj (notint (val_inj (val_eq m0 a))) = Vint32 Int.zero \/
                                   val_inj (notint (val_inj (val_eq m0 a))) = Vnull -> m0 = a.
  intros.

  destruct H; intros; int auto.
  destruct m0; destruct a; try destruct a0; try destruct m0; simpl in *; int auto.
  destruct a; int auto.
  apply unsigned_inj in e.
  subst.
  auto.

  destruct a.
  int auto.
  destruct (peq b b0).
  apply unsigned_inj in e;subst;auto.

  int auto.
  destruct (peq b b0); int auto.
  destruct (val_eq m0 a).
  destruct v; int auto.
  int auto.
Qed.


Lemma AOSTCBPrioTbl_high_tcblist_get_msg :
  forall tcbls p prio st m vl rtbl m' s P av,
    TcbMod.get tcbls p = Some (prio, st, m) ->
    s|= AOSTCBPrioTbl vl rtbl tcbls av ** P ->
    s|= AOSTCBPrioTbl vl rtbl (TcbMod.set tcbls p (prio, st, m')) av ** P.
Proof.
  introv Htcb Hs.
  sep cancel 2%nat 2%nat.
  unfold AOSTCBPrioTbl  in Hs.
  unfold AOSTCBPrioTbl.
  sep cancel 1%nat 1%nat.
  sep split in Hs.
  sep split; eauto.
  unfolds.
  unfolds  in H1.
  unfolds in   H0.
  splits.
  intros.
  destruct H1.
  lets Hrs : H1 H2 H3 H4.
  mytac.
  assert (tcbid = p \/ tcbid <> p) by tauto.
  destruct H10.
  subst.
  unfold get in *; simpl in *.

  rewrite Htcb in H6.
  inverts H6.
  exists  x m'.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  exists x x0.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (tcbid = p \/ tcbid <> p) by tauto.
  destruct H3.
  subst.
  rewrite TcbMod.set_sem in H2.
  erewrite tidspec.eq_beq_true in H2; eauto.
  inverts H2.
  destruct H1.
  eapply H2; eauto.
  rewrite TcbMod.set_sem in H2.
  erewrite tidspec.neq_beq_false in H2; eauto.
  destruct H1.
  eapply H4; eauto.
  destruct H1.
  destruct H2.
  eapply R_Prio_NoChange_Prio_hold; eauto.
Qed.

