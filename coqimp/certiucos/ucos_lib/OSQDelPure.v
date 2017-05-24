Require Import ucos_include.

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

(**Pure Lemmas for OSQDel**)
Lemma  ecb_wt_ex_prop :
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
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 i
                   :: Vint32 i3 :: x2 :: x3 :: v'42 :: nil,
                  v'40) v'35 ->
    RH_TCBList_ECBList_P v'34 v'35 tid ->
    exists t' tl z y,
      EcbMod.get v'34 x = Some (absmsgq z y, t' :: tl).
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
  destruct Hrp1 as (Hrp1 & _).
  lets Hxq : Hrp1 Hpro.
  destruct Hxq as (tid' & n0 & m & Hte).
  unfolds; simpl; auto.
  unfolds in Hz.
  destruct Hz as (Hz1 & Hz2).
  destruct Hz1.
  lets Hea : H3 Hte.
  simp join.
  apply  inlist_ex in H5.
  simp join.
  do 4 eexists.
  eauto.
Qed.

Lemma ecblist_pin :
  forall v1 x y  v1' v2 v3 v4 z,
    ECBList_P x y v1  v2 v3 v4 -> In y (get_eidls x (v1 ++  z :: v1')).
Proof.
  introv Hecb.
  eapply in_get_eidls .
  clear v1'.
  unfold get_eidls.
  rewrite get_remove_exchange.
  erewrite removelast_app.
  simpl removelast.
  rewrite app_nil_r.
  inductions v1.
  simpl in Hecb.
  simp join.
  simpl.
  left; auto.
  simpl in Hecb.
  simp join.
  destruct v2; tryfalse.
  destruct a.
  simp join.
  unfold get_eid_ecbls; fold get_eid_ecbls.
  simpl.
  lets Hx : IHv1 z H3.
  unfolds in H.
  simpl in Hx.
  destruct v.
  simpl in H.
  tryfalse.
  destruct v5.
  simpl in H; tryfalse.
  destruct v6.
  simpl in H; tryfalse.
  destruct v7; simpl in H; tryfalse.
  destruct v8; simpl in H; tryfalse.
  destruct v9;simpl in H; tryfalse.
  inverts H.
  destruct Hx.
  subst.
  branch 2; auto.
  branch 3; auto.
  intro Hf.
  tryfalse.
Qed.


Lemma ecblist_ecbmod_get_aux :
  forall v'61 i6  x4 x8 v'58 v'42  
         v'63 x20 x19 x9 x10 x15 i5 i4 v'65 x21 x22 v3 v'37 v'35 v'36 v'38,
    Int.unsigned i5 <= 65535 -> 
    array_type_vallist_match Int8u v'58->
    RH_CurTCB v'38 v'36 ->
    length v'58 = ∘OS_EVENT_TBL_SIZE ->
    RH_TCBList_ECBList_P v'35 v'36 v'38 ->
    RL_Tbl_Grp_P v'58 (V$0) ->
    ECBList_P (Vptr (v'61, Int.zero)) Vnull
              (
                   ((V$OS_EVENT_TYPE_Q
                      :: V$0 :: Vint32 i6 :: Vptr (v'63, Int.zero) :: x4 :: x8 :: nil,
                     v'58) :: nil) ++ v'42)
                                       (
                                             (DMsgQ (Vptr (v'63, Int.zero))
                                                    (x20
                                                       :: x19
                                                       :: x9
                                                       :: x10
                                                       :: x15
                                                       :: Vint32 i5
                                                       :: Vint32 i4 :: Vptr (v'65, Int.zero) :: nil)
                                                    (x21 :: x22 :: nil) v3 :: nil) ++ v'37) v'35 v'36 ->
    exists msgls,
      EcbMod.get v'35 (v'61, Int.zero) = Some (absmsgq msgls  i5, nil)
    /\ exists vv,  EcbMod.join vv  (EcbMod.sig (v'61, Int.zero) (absmsgq msgls  i5, nil)) v'35 /\ECBList_P x8 Vnull v'42 v'37  vv  v'36.
Proof.
  introv  Hi Harr Hcur Hrl Htcb Hre Hep.
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
  destruct Hmt as (Hm1 & Hm2 & Hm3 & Hm4).
  unfolds in Hm1.
  unfolds in Hm2.
  unfolds in Hm3.
  simp join.
  exists l.
  unfolds in H1.
  simpl in H1.
  usimpl H2.
  usimpl H7.
  usimpl H8.
  usimpl H9.
  usimpl H0.
  assert (w = nil \/ w <> nil) by tauto.
  destruct H0 as [Hnil | Hnnil].
  Focus 2.
  unfolds in Hcur.
  unfolds in Htcb.
  destruct Htcb as (Htcb1&Htcb2).
  lets Hj : ecbmod_joinsig_get Hej.
  lets Hea : qwaitset_notnil_ex Hnnil.
  destruct Hea as (tid & Hin).
  assert ( EcbMod.get v'35 (v'61, Int.zero) = Some (absmsgq l m, w) /\ In tid w) by (split; auto).
  destruct Htcb1 as (Htb & Htb2).
  lets Hjj : Htb H0.
  destruct Hjj as (prio & m0 & n & Htcg).
  unfolds in Heb.
  destruct Heb as (Heb1 & Heb2 & _).
  unfolds  in Heb2.
  destruct Heb2 as (Heba & Hebb).
  lets Hebs : Heba Htcg.
  lets Hbb : prioinq_exists Hebs.
  destruct Hbb as (n0 & Hnn & Hnth).
  lets Hfs : H Hnn.
  tryfalse.
  subst w.
  (*lets Heq : int_usign_eq H4 H5. *)
  split.
  rewrite Int.repr_unsigned.
  eapply ecbmod_joinsig_get; eauto.
  eexists; splits; eauto.
  rewrite Int.repr_unsigned.
  eapply  ecbmod_joinsig_sig; eauto.
Qed.



Lemma ecblist_ecbmod_get :
  forall v'61 i6  x4 x8 v'58 v'42 v'21 
         v'63 x20 x19 x9 x10 x15 i5 i4 v'65 x21 x22 v3 v'37 v'35 v'36 v'38,
    length v'21 = O  ->
    Int.unsigned i5 <= 65535 -> 
    array_type_vallist_match Int8u v'58->
    RH_CurTCB v'38 v'36 ->
    length v'58 = ∘OS_EVENT_TBL_SIZE ->
    RH_TCBList_ECBList_P v'35 v'36 v'38 ->
    RL_Tbl_Grp_P v'58 (V$0) ->
    ECBList_P (Vptr (v'61, Int.zero)) Vnull
              (nil ++
                   ((V$OS_EVENT_TYPE_Q
                      :: V$0 :: Vint32 i6 :: Vptr (v'63, Int.zero) :: x4 :: x8 :: nil,
                     v'58) :: nil) ++ v'42)
              (v'21 ++
                    (DMsgQ (Vptr (v'63, Int.zero))
                           (x20
                              :: x19
                              :: x9
                              :: x10
                              :: x15
                              :: Vint32 i5
                              :: Vint32 i4 :: Vptr (v'65, Int.zero) :: nil)
                           (x21 :: x22 :: nil) v3 :: nil) ++ v'37) v'35 v'36 ->
    exists msgls,
      EcbMod.get v'35 (v'61, Int.zero) = Some (absmsgq msgls  i5, nil)
      /\ exists vv,  EcbMod.join vv  (EcbMod.sig (v'61, Int.zero) (absmsgq msgls i5, nil)) v'35 /\ECBList_P x8 Vnull v'42 v'37  vv  v'36.
Proof.
  introv Hlen Hi Harr Hcur Hrl Htcb Hre Hep.
  destruct v'21.
  2 : simpl in Hlen; tryfalse.
  rewrite app_nil_l in Hep.
  rewrite app_nil_l in Hep.
  eapply ecblist_ecbmod_get_aux;eauto.
Qed.
  

  Lemma RH_TCBList_ECBList_MUTEX_OWNER_subset_hold : 
    forall x y z t,  
      RH_TCBList_ECBList_MUTEX_OWNER z t -> 
      EcbMod.join x y z ->   
      RH_TCBList_ECBList_MUTEX_OWNER x t.
  Proof.
    intros.
    unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
    intros.
    assert ( EcbMod.get z eid = Some (absmutexsem pr (Some (tid, opr)), wls)). 
    unfold get in H1.
    simpl in H1.
    go.
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
  simp join.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  simp join.
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
  simp join.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  simp join.
  destruct H2.
  subst y.
  apply EcbMod.join_comm in Hjo.
  eapply EcbMod.join_sig_get in Hjo.
  unfold get in H1; simpl in H1.
  rewrite H1 in Hjo.
  inverts Hjo.
  simpl in H3.
  tryfalse.
  do 2 eexists; split; try eapply ecbmod_get_join_get; eauto.
  destruct Hrh3.
  splits.
  intros.
  simp join.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  simp join.
  destruct H2.
  subst y.
  apply EcbMod.join_comm in Hjo.
  eapply EcbMod.join_sig_get in Hjo.
  unfold get in H1; simpl in H1.
  rewrite H1 in Hjo.
  inverts Hjo.
  simpl in H3.
  tryfalse.
  do 2 eexists; split; try eapply ecbmod_get_join_get; eauto.
  destruct Hrh4.
  splits.
  intros.
  simp join.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  simp join.
  destruct H2.
  subst y.
  apply EcbMod.join_comm in Hjo.
  eapply EcbMod.join_sig_get in Hjo.
  unfold get in H1; simpl in H1.
  rewrite H1 in Hjo.
  inverts Hjo.
  simpl in H3.
  tryfalse.
  do 3 eexists; split; try eapply ecbmod_get_join_get; eauto.
  destruct H0.
  eapply RH_TCBList_ECBList_MUTEX_OWNER_subset_hold; eauto.
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
  simp join.
  destruct a.
  simp join.
  lets Hx : IHy1 H2 H4.
  simp join.
  lets Hex : joinsig_join_ex H1 H7.
  simp join.
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
  simp join.
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



Lemma ecblist_ecbmod_get' :
  forall v'40 v'52 v'61 i6  x4 x8 v'58 v'42 v'21
         v'63 x20 x19 x9 x10 x15 i5 i4 v'65 x21 x22 v3 v'37 v'35 v'36 v'38,
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
                    ((V$OS_EVENT_TYPE_Q
                       :: V$0 :: Vint32 i6 :: Vptr (v'63, Int.zero) :: x4 :: x8 :: nil,
                      v'58) :: nil) ++ v'42)
              (v'21 ++
                                              (DMsgQ (Vptr (v'63, Int.zero))
                                                     (x20
                                                        :: x19
                                                        :: x9
                                                        :: x10
                                                        :: x15
                                                        :: Vint32 i5
                                                        :: Vint32 i4 :: Vptr (v'65, Int.zero) :: nil)
                                                     (x21 :: x22 :: nil) v3 :: nil) ++ v'37) v'35 v'36 ->
 
     exists msgls,
      EcbMod.get v'35 (v'61, Int.zero) = Some (absmsgq msgls  i5, nil)
    /\ exists vg vv vx,
         ECBList_P v'52 (Vptr (v'61, Int.zero)) v'40 v'21 vg v'36 /\
         EcbMod.join vg vx v'35/\
         EcbMod.join vv  (EcbMod.sig (v'61, Int.zero) (absmsgq msgls i5, nil)) vx/\
         ECBList_P x8 Vnull v'42 v'37  vv  v'36.
Proof.
  introv Hsom Hlen Hi Harr Hcur Hrl Htcb Hre Hep.
  lets Hex : ecblist_p_decompose Hlen Hep.
  simp join.
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
  destruct Hmt as (Hm1 & Hm2 & Hm3 & Hm4).
  unfolds in Hm1.
  unfolds in Hm2.
  unfolds in Hm3.
  simp join.
  exists l.
  unfolds in H0.
  simpl in H0.
  inverts H0.
  usimpl H5.
  usimpl H10.
  usimpl H11.
  usimpl H12.
  usimpl H4.
  assert (w = nil \/ w <> nil) by tauto.
  destruct H0 as [Hnil | Hnnil].
  Focus 2.
  unfolds in Hcur.
  unfolds in Htcb.
  destruct Htcb as (Htcb1&Htcb2).
  lets Hj : ecbmod_joinsig_get Hej.
  lets Hea : qwaitset_notnil_ex Hnnil.
  destruct Hea as (tid & Hin).
  assert ( EcbMod.get x1 (v'61, Int.zero) = Some (absmsgq l m, w) /\ In tid w) by (split; auto).
  lets Has : EcbMod.join_get_get_r H1 H0.
  assert ( EcbMod.get v'35 (v'61, Int.zero) = Some (absmsgq l m, w) /\ In tid w) by (split; auto).
  destruct Htcb1 as (Htc & Htc').
  lets Hjj : Htc H4.
  destruct Hjj as (prio & m0 & n & Htcg).
  unfolds in Heb.
  destruct Heb as (Heb1 & Heb2 & _).
  unfolds  in Heb1.
  unfolds in Heb2.
  destruct Heb2 as (Hebb & Heb2).
  lets Hebs : Hebb Htcg.
  lets Hbb : prioinq_exists Hebs.
  destruct Hbb as (n0 & Hnn & Hnth).
  lets Hfs : H3 Hnn.
  tryfalse.
  subst w.
  lets Heq : int_usign_eq H7 H8.
  split.
  rewrite Int.repr_unsigned.
  assert (EcbMod.get x1 (v'61, Int.zero) = Some (absmsgq l m, nil)).
  eapply ecbmod_joinsig_get; eauto.
  eapply EcbMod.join_get_get_r;eauto.
  do 3 eexists; splits; eauto.
  eapply ecbmod_joinsig_sig.
  rewrite Int.repr_unsigned.
  eauto.
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
  simp join.
  unfold upd_last_ectrls in H.
  simpl in H.
  tryfalse.
  introv Hneq Hep Hepp Hsom Hj.
  assert (v'40 = nil \/ v'40 <> nil) by tauto.
  destruct H.
  subst v'40.
  destruct v'21.
  simpl in Hep.
  simp join; tryfalse.
  simpl in Hep.
  simp join.
  destruct a.
  simp join.
  remember (upd_last_ectrls ((v, v0) :: nil) x8) as vl.
  lets Hx : upd_last_prop  H Heqvl.
  simp join.
  unfolds in H3.
  simpl in H3.
  inverts H3.
  unfolds upd_last_ectrls.
  simpl.
  eexists; splits; eauto.
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
  simpl in Hep; simp join; tryfalse.
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

Close Scope code_scope.
Close Scope  int_scope.
Close Scope  Z_scope.
