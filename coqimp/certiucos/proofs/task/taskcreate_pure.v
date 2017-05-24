Require Import ucos_include.
Require Import os_ucos_h.
Require Import sep_lemmas_ext.
Require Import linv_solver.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma absimp_taskcre_prio_invalid:
  forall P v1 v2 v3 sch,
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true ->
    absinfer sch ( <|| taskcrecode (v1 :: v2 :: (Vint32 v3) :: nil) ||> ** P)
             ( <|| END (Some (Vint32 (Int.repr PRIO_ERR))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absimp_taskcre_prio_already_exists:
  forall P v1 v2 v3 sch mqls tls t ct,
    can_change_aop P ->
    absinfer sch ( <|| taskcrecode (v1 :: v2 :: (Vint32 v3) :: nil) ||> ** 
                       HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) 
             ( <|| END (Some (Vint32 (Int.repr  OS_PRIO_EXIST))) ||> ** 
                   HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) .
Proof.
  infer_solver 1%nat.
Qed.


Lemma absimp_taskcre_no_more_tcb:
  forall P v1 v2 v3 sch,
    can_change_aop P ->
    absinfer sch ( <|| taskcrecode (v1 :: v2 :: (Vint32 v3) :: nil) ||> ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_NO_MORE_TCB))) ||> ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma absimp_taskcre_succ:
  forall P v1 v2 v3 sch t tls mqls ct ,
    can_change_aop P ->
    (* Int.lt ($ 63) v3 = false ->
     * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
     * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
     * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
    absinfer sch ( <|| taskcrecode (v1 :: v2 :: (Vint32 v3) :: nil) ||> **
                       HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
             ( <|| scrt (v1 :: v2 :: (Vint32 v3) :: nil);;(* taskcre_succ  (|(v1 :: v2 :: (Vint32 v3) :: nil)|) ;;  *)isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||> **  HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).

Proof.
  intros.
  unfold taskcrecode.
  infer_branch 3%nat.
  eapply absinfer_eq.
Qed.

Lemma retpost_tcbinitpost: 
  retpost OS_TCBInitPost.
Proof.
  unfolds.
  intros.
  unfold getasrt in H.
  unfold  OS_TCBInitPost in H.
  unfold  OS_TCBInitPost' in H.
  sep lift 6%nat in H.
  disj_asrt_destruct H.
  sep split in H.
  intro.
  subst .
  inverts H5.
  intro.
  subst.
  sep split in H.
  inverts H0.
Qed.


Local Ltac smartunfold3 :=
  match goal with
    | |- ?e _ _ _ => unfold e in *
  end.


Lemma struct_pv_overlap:
  forall p v1 v2 s P,
    s |= Astruct p OS_TCB_flag v1 **
      PV p @ Int8u |-> v2 **
      P ->
    False.
Proof.
  intros.
  unfold Astruct in H.
  unfold OS_TCB_flag in H.
  unfold Astruct' in H.
  destruct v1.
  sep destroy H.
  simpl in H0; tryfalse.
  destruct p.
  sep normal in H.
  Set Printing Depth 999.
(* ** ac:   Show. *)
  remember (        match v1 with
                      | nil => Afalse
                      | v :: vl' =>
                        PV (b, i +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) @
                           STRUCT os_tcb ⋆ |-> v **
                           match vl' with
                             | nil => Afalse
                             | v0 :: vl'0 =>
                               PV (b,
                                   (i +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                   $ Z.of_nat (typelen STRUCT os_tcb ⋆)) @ 
                                  OS_EVENT ∗ |-> v0 **
                                  match vl'0 with
                                    | nil => Afalse
                                    | v1 :: vl'1 =>
                                      PV (b,
                                          ((i +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                           $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                                                                    $ Z.of_nat (typelen OS_EVENT ∗)) @ 
                                         (Void) ∗ |-> v1 **
                                         match vl'1 with
                                           | nil => Afalse
                                           | v2 :: vl'2 =>
                                             PV (b,
                                                 (((i +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆))
                                                   +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                                $ Z.of_nat (typelen OS_EVENT ∗)) +ᵢ
                                                                                                                                    $ Z.of_nat (typelen (Void) ∗)) @ 
                                                Int16u |-> v2 **
                                                match vl'2 with
                                                  | nil => Afalse
                                                  | v3 :: vl'3 =>
                                                    PV (b,
                                                        ((((i +ᵢ
                                                                 $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                                          $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                                                                                   $ Z.of_nat (typelen OS_EVENT ∗)) +ᵢ
                                                                                                                                                                                       $ Z.of_nat (typelen (Void) ∗)) +ᵢ
                                                                                                                                                                                                                         $ Z.of_nat (typelen Int16u)) @ 
                                                       Int8u |-> v3 **
                                                       match vl'3 with
                                                         | nil => Afalse
                                                         | v4 :: vl'4 =>
                                                           PV (b,
                                                               (((((i +ᵢ
                                                                         $ Z.of_nat (typelen STRUCT os_tcb ⋆))
                                                                   +ᵢ
                                                                      $ Z.of_nat (typelen STRUCT os_tcb ⋆))
                                                                  +ᵢ  $ Z.of_nat (typelen OS_EVENT ∗))
                                                                 +ᵢ  $ Z.of_nat (typelen (Void) ∗)) +ᵢ
                                                                                                       $ Z.of_nat (typelen Int16u)) +ᵢ
                                                                                                                                       $ Z.of_nat (typelen Int8u)) @ 
                                                              Int8u |-> v4 **
                                                              match vl'4 with
                                                                | nil => Afalse
                                                                | v5 :: vl'5 =>
                                                                  PV (b,
                                                                      ((((((i +ᵢ
                                                                                 $
                                                                                 Z.of_nat
                                                                                 (typelen STRUCT os_tcb ⋆))
                                                                           +ᵢ
                                                                              $
                                                                              Z.of_nat
                                                                              (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                                            $ Z.of_nat (typelen OS_EVENT ∗))
                                                                         +ᵢ  $ Z.of_nat (typelen (Void) ∗))
                                                                        +ᵢ  $ Z.of_nat (typelen Int16u))
                                                                       +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
                                                                                                          $ Z.of_nat (typelen Int8u)) @ 
                                                                     Int8u |-> v5 **
                                                                     match vl'5 with
                                                                       | nil => Afalse
                                                                       | v6 :: vl'6 =>
                                                                         PV (b,
                                                                             (((((((i +ᵢ
                                                                                         $
                                                                                         Z.of_nat
                                                                                         (typelen STRUCT os_tcb ⋆))
                                                                                   +ᵢ
                                                                                      $
                                                                                      Z.of_nat
                                                                                      (typelen STRUCT os_tcb ⋆))
                                                                                  +ᵢ
                                                                                     $
                                                                                     Z.of_nat
                                                                                     (typelen OS_EVENT ∗)) +ᵢ
                                                                                                              $ Z.of_nat (typelen (Void) ∗))
                                                                                +ᵢ
                                                                                   $ Z.of_nat (typelen Int16u))
                                                                               +ᵢ  
                                                                                  $ Z.of_nat (typelen Int8u)) +ᵢ
                                                                                                                 $ Z.of_nat (typelen Int8u)) +ᵢ
                                                                                                                                                $ Z.of_nat (typelen Int8u)) @
                                                                            Int8u |-> v6 **
                                                                            match vl'6 with
                                                                              | nil => Afalse
                                                                              | v7 :: vl'7 =>
                                                                                PV (b,
                                                                                    ((((((((i +ᵢ
                                                                                                 $
                                                                                                 Z.of_nat
                                                                                                 (typelen STRUCT os_tcb ⋆))
                                                                                           +ᵢ
                                                                                              $
                                                                                              Z.of_nat
                                                                                              (typelen STRUCT os_tcb ⋆))
                                                                                          +ᵢ
                                                                                             $
                                                                                             Z.of_nat
                                                                                             (typelen OS_EVENT ∗)) +ᵢ
                                                                                                                      $
                                                                                                                      Z.of_nat (typelen (Void) ∗))
                                                                                        +ᵢ
                                                                                           $ Z.of_nat (typelen Int16u))
                                                                                       +ᵢ
                                                                                          $ Z.of_nat (typelen Int8u))
                                                                                      +ᵢ
                                                                                         $ Z.of_nat (typelen Int8u))
                                                                                     +ᵢ
                                                                                        $ Z.of_nat (typelen Int8u))
                                                                                    +ᵢ
                                                                                       $ Z.of_nat (typelen Int8u)) @
                                                                                   Int8u |-> v7 **
                                                                                   match vl'7 with
                                                                                     | nil => Afalse
                                                                                     | v8 :: vl'8 =>
                                                                                       PV 
                                                                                         (b,
                                                                                          (((((((((i +ᵢ
                                                                                                        $
                                                                                                        Z.of_nat
                                                                                                        (typelen STRUCT os_tcb ⋆))
                                                                                                  +ᵢ
                                                                                                     $
                                                                                                     Z.of_nat
                                                                                                     (typelen STRUCT os_tcb ⋆))
                                                                                                 +ᵢ
                                                                                                    $
                                                                                                    Z.of_nat
                                                                                                    (typelen OS_EVENT ∗)) +ᵢ
                                                                                                                             $
                                                                                                                             Z.of_nat (typelen (Void) ∗))
                                                                                               +ᵢ
                                                                                                  $ Z.of_nat (typelen Int16u))
                                                                                              +ᵢ
                                                                                                 $ Z.of_nat (typelen Int8u))
                                                                                             +ᵢ
                                                                                                $ Z.of_nat (typelen Int8u))
                                                                                            +ᵢ
                                                                                               $ Z.of_nat (typelen Int8u))
                                                                                           +ᵢ
                                                                                              $ Z.of_nat (typelen Int8u))
                                                                                          +ᵢ
                                                                                             $ Z.of_nat (typelen Int8u)) @
                                                                                         Int8u |-> v8 **
                                                                                         match vl'8 with
                                                                                           | nil => Aemp
                                                                                           | _ :: _ => Afalse
                                                                                         end
                                                                                   end
                                                                            end
                                                                     end
                                                              end
                                                       end
                                                end
                                         end
                                  end
                           end
                    end ).
  clear Heqa.
  assert ( (b,i) <> (b,i)).
  eapply pv_false.
  Focus 3.
  instantiate (6:= s).
  sep auto.
  intro.
  unfolds in H0.
  destruct H0; simpljoin; tryfalse.
  destruct H0; simpljoin; tryfalse.
  intro.
  unfolds in H0.
  destruct H0; simpljoin; tryfalse.
  destruct H0; simpljoin; tryfalse.
  apply H0; auto.
Qed.



Lemma R_ECB_ETbl_P_hold_for_add_tcb:
  forall x0 p v'14 v'42 v'5 v'34, 
    R_ECB_ETbl_P x0 p v'14 ->
    TcbJoin v'34 (v'42, rdy, Vnull) v'14 v'5 ->
    R_ECB_ETbl_P x0 p v'5.
Proof.
  intros.
  destruct p.
  unfold R_ECB_ETbl_P in *.
  splits.
  simpljoin.
  clear H1 H2.

  smartunfold3.
  simpljoin.
  splits.
  {
    smartunfold3.
    intros .
    lets bb: H prio H4 H5.
    simpljoin.
    exists x.
    unfold get in *; simpl in *.
    erewrite TcbMod.join_get_r.
    eauto.
    eauto.
    eauto.
  }

  {
    smartunfold3.
    intros .
    lets bb: H1 prio H4 H5.
    simpljoin.
    exists x.
    unfold get in *; simpl in *.
    erewrite TcbMod.join_get_r.
    eauto.
    eauto.
    eauto.
  }

  {
    smartunfold3.
    intros .
    lets bb: H2 prio H4 H5.
    simpljoin.
    exists x.
    unfold get in *; simpl in *.
    erewrite TcbMod.join_get_r.
    eauto.
    eauto.
    eauto.
  }

  {
    smartunfold3.
    intros .
    lets bb: H3 prio H4 H5.
    simpljoin.
    exists x.
    unfold get in *; simpl in *.
    erewrite TcbMod.join_get_r.
    eauto.
    eauto.
    eauto.
  }

  simpljoin.
  clear H H2.

  smartunfold3.
  simpljoin.
  splits.

  {
    smartunfold3.
    intros.
    unfold TcbJoin in H0.
    unfold get, join, sig in *; simpl in *.
    assert (TcbMod.get v'14 tid = Some (prio, wait (os_stat_q x0) n, m)).
    eapply TcbMod.join_get_or in H4.
    2:eauto.
    destruct H4; intros.
    assert ( v'34 = tid \/ v'34 <> tid).
    tauto.
    destruct H5.
    subst.
    rewrite TcbMod.get_a_sig_a in H4.
    inverts H4.
    go.

    rewrite TcbMod.get_a_sig_a' in H4.
    inverts H4.
    go.
    auto.

    eapply H.
    eauto.
  }
  
  {
    smartunfold3.
    intros.
    unfold TcbJoin in H0.
    unfold get, join, sig in *; simpl in *.
    assert (TcbMod.get v'14 tid = Some (prio, wait (os_stat_sem x0) n, m)).
    eapply TcbMod.join_get_or in H4.
    2:eauto.
    destruct H4; intros.
    assert ( v'34 = tid \/ v'34 <> tid).
    tauto.
    destruct H5.
    subst.
    rewrite TcbMod.get_a_sig_a in H4.
    inverts H4.
    go.

    rewrite TcbMod.get_a_sig_a' in H4.
    inverts H4.
    go.
    auto.

    eapply H1.
    eauto.
  }
  
  {
    smartunfold3.
    intros.
    unfold TcbJoin in H0.
    unfold get, join, sig in *; simpl in *.
    assert (TcbMod.get v'14 tid = Some (prio, wait (os_stat_mbox x0) n, m)).
    eapply TcbMod.join_get_or in H4.
    2:eauto.
    destruct H4; intros.
    assert ( v'34 = tid \/ v'34 <> tid).
    tauto.
    destruct H5.
    subst.
    rewrite TcbMod.get_a_sig_a in H4.
    inverts H4.
    go.

    rewrite TcbMod.get_a_sig_a' in H4.
    inverts H4.
    go.
    auto.

    eapply H2.
    eauto.
  }

  {
    smartunfold3.
    intros.
    unfold TcbJoin in H0.
    unfold get, join, sig in *; simpl in *.
    assert (TcbMod.get v'14 tid = Some (prio, wait (os_stat_mutexsem x0) n, m)).
    eapply TcbMod.join_get_or in H4.
    2:eauto.
    destruct H4; intros.
    assert ( v'34 = tid \/ v'34 <> tid).
    tauto.
    destruct H5.
    subst.
    rewrite TcbMod.get_a_sig_a in H4.
    inverts H4.
    go.

    rewrite TcbMod.get_a_sig_a' in H4.
    inverts H4.
    go.
    auto.

    eapply H3.
    eauto.
  }

  simpljoin; auto.
Qed.


Lemma ecblist_hold_for_add_tcb :
  forall v'4 x v'3 v'13 v'14 v'5 v'42 v'34,
    ECBList_P x Vnull v'4 v'3 v'13 v'14 ->
    TcbJoin v'34 (v'42, rdy, Vnull) v'14 v'5 ->
    ECBList_P x Vnull v'4 v'3 v'13 v'5.
Proof.
  induction v'4.
  intros.
  simpl.
  simpl in H.
  auto.
  intros.
  unfold1 ECBList_P in *.
  simpljoin.
  destruct v'3; tryfalse.
  destruct a.
  simpljoin.
  eexists.
  splits; eauto.
  eapply R_ECB_ETbl_P_hold_for_add_tcb; eauto.

  repeat tri_exists_and_solver1.
  
Qed.
Lemma nv'2nv:
  forall vl n x,
    nth_val' n vl = x ->
    x <> Vundef ->
    nth_val n vl = Some x.
Proof.
  induction vl.
  induction n.
  intros.
  simpl in H.
  tryfalse.
  intros.
  simpl in H.
  tryfalse.

  induction n.
  intros.
  simpl in H.
  simpl.
  inverts H.
  auto.
  intros.
  simpl.
  simpl in H.
  apply IHvl.
  auto.
  auto.
Qed.


Lemma r_priotbl_p_hold_for_add_tcb :
  forall v'14 v'5 v'42 v'34 v'43 v'28,
    (* Int.unsigned v'42 < 64 -> *)
    v'43 <> v'34 ->
    nth_val' (Z.to_nat (Int.unsigned v'42)) v'28 = Vnull ->
    R_PrioTbl_P v'28 v'14 v'43 ->
    TcbJoin v'34 (v'42, rdy, Vnull) v'14 v'5 ->
    R_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned v'42)) v'28 (Vptr v'34)) v'5
      v'43.
Proof.
  introv HHHH.
  intros.
  smartunfold3.
  simpljoin.
  assert ( R_Prio_No_Dup v'5) as special.
  {
    unfold R_Prio_No_Dup in *.
    intros.
    assert (tid = v'34 \/ tid <> v'34) by tauto.
    assert (tid' = v'34 \/ tid' <> v'34) by tauto.

    destruct H7; destruct H8.
    subst.
    tryfalse.

    {
      subst v'34.
      unfold get, join, sig in *; simpl in *.
      erewrite TcbMod.join_get_l in H5.
      2:eauto.
      2:go.
      Focus 2.
      assert (tidspec.beq tid tid = true).
      go.
      rewrite H7.
      eauto.
      inverts H5.
      eapply TcbMod.join_get_or in H6.
      2: eauto.

      destruct H6.
      
      unfold get, join, sig in *; simpl in *.
      rewrite TcbMod.get_a_sig_a' in H5.
      inverts H5.
      go.
      
      lets bbb: H2 H5.
      intro.
      subst.
      simpljoin.
      eapply nv'2nv in H.
      unfold nat_of_Z in *.
      rewrite H in H6.
      inverts H6.
      intro; tryfalse.
    }

    {
      subst v'34.
      unfold get, join, sig in *; simpl in *.
      erewrite TcbMod.join_get_l in H6.
      2:eauto.
      2:go.
      Focus 2.
      assert (tidspec.beq tid' tid' = true).
      go.
      rewrite H8.
      eauto.
      inverts H6.
      eapply TcbMod.join_get_or in H1.
      2: eauto.

      destruct H1.
      
      unfold get, join, sig in *; simpl in *.
      rewrite TcbMod.get_a_sig_a' in H1.
      inverts H1.
      go.
      
      lets bbb: H2 H1.
      intro.
      subst.
      simpljoin.
      eapply nv'2nv in H.
      unfold nat_of_Z in *.
      rewrite H in H6.
      inverts H6.
      intro; tryfalse.
    }

    {
      unfold get, sig, join in *; simpl in *.
      eapply TcbMod.join_get_or in H5; eauto.
      eapply TcbMod.join_get_or in H6; eauto.

      destruct H5.
      unfold get, sig, join in *; simpl in *.
      rewrite TcbMod.get_a_sig_a' in H5.
      inverts H5.
      go.

      destruct H6.
      unfold get, sig, join in *; simpl in *.
      rewrite TcbMod.get_a_sig_a' in H6.
      inverts H6.
      go.

      eapply H3.
      2:eauto.
      2:eauto.
      eauto.
    }
    
  }
  splits; auto.
  intros.
  assert ( prio =  v'42 \/  prio <>  v'42).
  tauto.
  destruct H7.
  rewrite H7 in *.
  unfold nat_of_Z in *.
  erewrite hoare_assign.update_nth in H5.
  inverts H5.
  
  unfold TcbJoin in *.
  unfold get, join, sig in *; simpl in *.
  do 2 eexists.
  eapply TcbMod.join_get_l.
  eauto.
  inverts H7.
  eapply TcbMod.get_a_sig_a.
  go.
(* ** ac:   SearchAbout nth_val. *)
(* ** ac:   Print nth_val'. *)
(* ** ac:   Show. *)
  eapply nv'2nv; eauto.
  (* intro; tryfalse. *)
  unfold nat_of_Z in *.
(* ** ac:   SearchAbout nth_val. *)

  assert (exists st m, get v'14 tcbid = Some (prio, st, m)).
  eapply H0; eauto.
  eapply nth_upd_neq.
  2:eauto.
  intro.
(* ** ac:   SearchAbout Z.to_nat. *)
  apply Z2Nat.inj in H8.
(* ** ac:   SearchAbout (Int.unsigned _ = Int.unsigned _). *)

  apply unsigned_inj in H8.
  tryfalse.
  clear; int auto.
  clear; int auto.

  simpljoin.
  unfold TcbJoin in H1.
  unfold get, join, sig in *; simpl in *.
  do 2 eexists.
  go.


  intros.
  unfold nat_of_Z in *.


  eapply TcbMod.join_get_or in H4; eauto.
  2:exact H1.
  destruct H4.
  assert (tcbid = v'34 \/ tcbid <> v'34).
  tauto.
  destruct H5.
  subst.
  erewrite TcbMod.get_a_sig_a in H4.
  inverts H4.
  erewrite hoare_assign.update_nth.
  splits; auto.
  eapply nv'2nv.
  eauto.
  intro; tryfalse.
  go.

  erewrite TcbMod.get_a_sig_a' in H4.
  inverts H4.
  go.

  lets bb: H2 H4.

  assert (prio = v'42 \/ prio <> v'42) by tauto.
  destruct H5.
  subst.
  apply nv'2nv in H.
  rewrite H in bb.
  destruct bb.
  tryfalse.
  intro; tryfalse.

  simpljoin.
  splits; auto.
  erewrite nth_upd_neqrev.
  eauto.
  intro.
  2:eauto.
  
  apply Z2Nat.inj in H8.
  apply unsigned_inj in H8.
  tryfalse.
  clear; int auto.
  clear; int auto.
Qed.

Lemma nth_upd_neqeq:
  forall (vl : vallist) (n m : nat) (x : val),
    n <> m ->
    nth_val n (update_nth_val m vl x) = nth_val n vl.
Proof.
  intros.
  simpl.
  auto.
  intros.
  remember (nth_val n vl).
  destruct o.
  erewrite nth_upd_neqrev.
  eauto.
  auto.
  auto.
  gen n.
  gen m.
  induction vl.
  simpl.
  auto.
  intros.
  gen m.
  induction n.

  simpl in Heqo.
  inverts Heqo.
  induction m.
  intros.
  simpl.
  simpl in Heqo.
  auto.
  intros.
  simpl.
  simpl in Heqo.
  apply IHvl.
  auto.
  auto.
Qed.

Lemma tcblist_p_hold_for_upd_1 :
  forall a b ls c d e,
    TCBList_P a (b::ls) c d ->
    TCBList_P a (update_nth_val 1 b e :: ls) c d. 
Proof.
  intros.
  unfold1 TCBList_P in *.
  simpljoin.
  repeat tri_exists_and_solver1.
  unfolds.
(* ** ac:   SearchAbout nth_val. *)
  eapply nth_upd_neqrev.
  omega.
  auto.

  unfold TCBNode_P in *.
  destruct x2; destruct p.
  simpljoin.
  splits ; try (eapply nth_upd_neqrev; [omega| auto]).

  unfold RL_TCBblk_P in *.
  simpljoin.
  unfold V_OSTCBPrio, V_OSTCBX, V_OSTCBY, V_OSTCBBitX, V_OSTCBBitY, V_OSTCBStat,  V_OSTCBEventPtr  .
  repeat (erewrite nth_upd_neqrev; [idtac| try omega| eauto 1]).
  repeat tri_exists_and_solver1.

  unfold R_TCB_Status_P in *.
  unfold RLH_RdyI_P, RHL_RdyI_P, RLH_TCB_Status_Wait_P, RHL_TCB_Status_Wait_P in *.
  unfold RLH_Wait_P, RLH_WaitS_P, RLH_WaitQ_P, RLH_WaitMB_P, RLH_WaitMS_P,
  RHL_Wait_P, RHL_WaitS_P, RHL_WaitQ_P, RHL_WaitMB_P, RHL_WaitMS_P
    in *.
  unfold WaitTCBblk in *.
  unfold RdyTCBblk in *.
  unfold V_OSTCBPrio, V_OSTCBX, V_OSTCBY, V_OSTCBBitX, V_OSTCBBitY, V_OSTCBStat,  V_OSTCBEventPtr, V_OSTCBDly in *.
  simpljoin.
  repeat (erewrite nth_upd_neqeq; [idtac| try omega]).
  splits; auto.
Qed.

Lemma tcblist_p_hold_for_add_tcb_lemma :
  forall v l v'26 v'23 v'42 ,
    0 <= Int.unsigned v'42 < 64 ->
    array_type_vallist_match Int8u v'26 ->
    length v'26 = ∘ OS_RDY_TBL_SIZE ->
    TCBList_P v l v'26 v'23 ->
    (~ exists id t m, get v'23 id = Some (v'42, t, m) )->
    TCBList_P v l
              (update_nth_val (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26
                              (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26)
                                     (nth_val' (Z.to_nat (Int.unsigned (v'42&ᵢ$ 7))) OSMapVallist))))
              v'23.
Proof.
  introv HHH.
  Require Import protect.
  protect HHH.
  intros HHH2 HHH3.
  gen v.
  gen v'23.
  gen l.
  induction l.
  intros.
  simpl.
  simpl in H.
  auto.
  intros.
  unfold1 TCBList_P.
  unfold1 TCBList_P in H.
  simpljoin.
  repeat tri_exists_and_solver1.
  Focus 2.
  eapply IHl.
  auto.
  intro.
  simpljoin.
  eapply H0.
  do 3 eexists.
  unfold get,sig,join in *; simpl in *.
  unfold get,sig,join in *; simpl in *.
  eapply TcbMod.join_get_r.
  eauto.
  exact H.
  auto.
  Require Import OSQPostPure.
(* ** ac:   Check   prio_in_tbl_orself . *)
(* ** ac:   SearchAbout TCBNode_P. *)
  cut (exists grp, nth_val ∘ (Int.unsigned (v'42 >>ᵢ $ 3)) v'26 = Some (Vint32 grp) ).
  intro.
  simpljoin.
  lets bbb: H.
  unfold nat_of_Z in bbb.
(* ** ac:   SearchAbout nth_val. *)
  eapply new_inv.nth_val_nth_val'_some_eq in bbb.
  rewrite bbb.
(* ** ac:   Check TCBNode_P_rtbl_add. *)
  cut ((nth_val' (Z.to_nat (Int.unsigned (v'42&ᵢ$ 7))) OSMapVallist) = Vint32 ($ 1<<ᵢ(v'42&ᵢ$ 7)) ).
  intro.
  rewrite H5.
  simpl.
  destruct x2.
  destruct p.
  eapply TCBNode_P_rtbl_add; eauto.
  Focus 3.
  unfolds in H3.
  simpljoin.
  auto.
  Focus 2.
  intro.
  apply H0.
  subst v'42.
  do 3 eexists.
  unfold get,sig,join in *; simpl in *.
  unfold get,sig,join in *; simpl in *.
  eapply TcbMod.join_get_l.
  eauto.
  eapply TcbMod.get_a_sig_a.
  go.
  unfolds in H3.
  simpljoin.
  unfolds in H7.
  simpljoin.
  rewrite H6 in H7.
  inverts H7.
  auto.
(* ** ac:   SearchAbout OSMapVallist. *)
  assert ((Int.unsigned (v'42&ᵢ$ 7)) <= 7).
  clear -HHH.
  unprotect HHH.
  mauto.
  clear -H5.
  remember (v'42&ᵢ$ 7) .
  mauto.
  eapply new_rtbl.prio_set_rdy_in_tbl_lemma_1; auto.
Qed.


Lemma tcblist_p_hold_for_add_tcb :
  forall tid v'9 v'10 v'26 v'23 v'42 v'34,
    0 <= Int.unsigned v'42 < 64 ->
    array_type_vallist_match Int8u v'26 ->
    length v'26 = ∘ OS_RDY_TBL_SIZE ->
    TCBList_P (Vptr tid) (v'9 :: v'10) v'26 v'23 ->
    (~ exists id t m, get v'23 id = Some (v'42, t, m) )->
    TCBList_P (Vptr tid) (update_nth_val 1 v'9 (v'34) :: v'10)
              (update_nth_val (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26
                              (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26)
                                     (nth_val' (Z.to_nat (Int.unsigned (v'42&ᵢ$ 7))) OSMapVallist))))
              v'23.
Proof.
  introv HHH.
  protect HHH.
  intros HHH2 HHH3.
  intros.
  eapply tcblist_p_hold_for_upd_1.
  remember (v'9 :: v'10).
  clear Heql.
  remember (Vptr tid).
  clear Heqv.
  gen v.
  gen v'23.
  gen l.
  induction l.
  intros.
  simpl.
  simpl in H.
  auto.
  intros.
  unfold1 TCBList_P.
  unfold1 TCBList_P in H.
  simpljoin.
  repeat tri_exists_and_solver1.
  Focus 2.
  eapply IHl.
  auto.
  intro.
  simpljoin.
  eapply H0.
  do 3 eexists.
  unfold get,sig,join in *; simpl in *.
  unfold get,sig,join in *; simpl in *.
  eapply TcbMod.join_get_r.
  eauto.
  exact H.
  auto.
  Require Import OSQPostPure.
(* ** ac:   Check   prio_in_tbl_orself . *)
(* ** ac:   SearchAbout TCBNode_P. *)
  cut (exists grp, nth_val ∘ (Int.unsigned (v'42 >>ᵢ $ 3)) v'26 = Some (Vint32 grp) ).
  intro.
  simpljoin.
  lets bbb: H.
  unfold nat_of_Z in bbb.
(* ** ac:   SearchAbout nth_val. *)
  eapply new_inv.nth_val_nth_val'_some_eq in bbb.
  rewrite bbb.
(* ** ac:   Check TCBNode_P_rtbl_add. *)
  cut ((nth_val' (Z.to_nat (Int.unsigned (v'42&ᵢ$ 7))) OSMapVallist) = Vint32 ($ 1<<ᵢ(v'42&ᵢ$ 7)) ).
  intro.
  rewrite H5.
  simpl.
  destruct x2.
  destruct p.
  eapply TCBNode_P_rtbl_add; eauto.
  Focus 3.
  unfolds in H3.
  simpljoin.
  auto.
  Focus 2.
  intro.
  apply H0.
  subst v'42.
  do 3 eexists.
  unfold get,sig,join in *; simpl in *.
  unfold get,sig,join in *; simpl in *.
  eapply TcbMod.join_get_l.
  eauto.
  eapply TcbMod.get_a_sig_a.
  go.
  unfolds in H3.
  simpljoin.
  unfolds in H7.
  simpljoin.
  rewrite H6 in H7.
  inverts H7.
  auto.
  assert ((Int.unsigned (v'42&ᵢ$ 7)) <= 7).
  clear -HHH.
  unprotect HHH.
  mauto.
  clear -H5.
  remember (v'42&ᵢ$ 7) .
  mauto.
  eapply new_rtbl.prio_set_rdy_in_tbl_lemma_1; auto.
  
Qed.

(* Lemma tcblist_p_hold_for_add_tcb' :
 *   forall v'26 v'42 v'34 v'39 v'30,
 *     (* TCBList_P v'30 nil v'26 v'22 -> *)
 *     new_tcb_node_p v'42 Vnull v'30 v'39 ->
 *     TCBList_P (Vptr v'34) ((v'39 :: nil) ++ nil)
 *               (update_nth_val (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26
 *                               (val_inj
 *                                  (or (nth_val' (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26)
 *                                      (nth_val' (Z.to_nat (Int.unsigned (v'42&ᵢ$ 7))) OSMapVallist))))
 *               (sig v'34 (v'42, rdy, Vnull)).
 *           Admitted. *)

Lemma TCBList_P_nil_empty:
  forall v'30 v'26 v'22,
    TCBList_P v'30 nil v'26 v'22 ->
    v'22 = empenv.
Proof.
  intros.
  simpl in H.
  auto.
Qed.


Lemma rh_t_e_p_hold_for_add_tcb:
  forall v'13 v'14 tid v'34 v'42 v'5,
    RH_TCBList_ECBList_P v'13 v'14 tid ->
    TcbJoin v'34 (v'42, rdy, Vnull) v'14 v'5 ->
    RH_TCBList_ECBList_P v'13 v'5 tid.
Proof.
  intros.
  smartunfold3.
  simpljoin.
  splits.
  {
    smartunfold3.
    simpljoin.
    splits.
    {
      intros.
      lets bb: H H5.
      simpljoin.
      do 3 eexists.
      unfold get, sig, join in *; simpl in *.
      go.
    }
    {
      intros.
      unfold get, sig, join in *; simpl in *.
      eapply TcbMod.join_get_or in H5.
      2: exact H0.
      destruct H5.
      assert (tid0 = v'34 \/ tid0 <> v'34).
      tauto.
      destruct H6.
      subst.
      rewrite TcbMod.get_a_sig_a in H5.
      inverts H5.
      go.
      
      rewrite TcbMod.get_a_sig_a' in H5.
      inverts H5.
      go.

      eapply H4.
      eauto.
    }
  }
  {
    Local Ltac swapname H H' :=
      let HH := fresh in
      rename H into HH; rename H' into H; rename HH into H'.
      swapname H H1.
      smartunfold3.
      simpljoin.
      splits.
      {
        intros.
        lets bb: H H5.
        simpljoin.
        do 3 eexists.
        unfold get, sig, join in *; simpl in *.
        go.
      }
      {
        intros.
        unfold get, sig, join in *; simpl in *.
        eapply TcbMod.join_get_or in H5.
        2: exact H0.
        destruct H5.
        assert (tid0 = v'34 \/ tid0 <> v'34).
        tauto.
        destruct H6.
        subst.
        rewrite TcbMod.get_a_sig_a in H5.
        inverts H5.
        go.
        
        rewrite TcbMod.get_a_sig_a' in H5.
        inverts H5.
        go.

        eapply H4.
        eauto.
      }
  }

  {
    swapname H H2.
    smartunfold3.
    simpljoin.
    splits.
    {
      intros.
      lets bb: H H5.
      simpljoin.
      do 3 eexists.
      unfold get, sig, join in *; simpl in *.
      go.
    }
    {
      intros.
      unfold get, sig, join in *; simpl in *.
      eapply TcbMod.join_get_or in H5.
      2: exact H0.
      destruct H5.
      assert (tid0 = v'34 \/ tid0 <> v'34).
      tauto.
      destruct H6.
      subst.
      rewrite TcbMod.get_a_sig_a in H5.
      inverts H5.
      go.
      
      rewrite TcbMod.get_a_sig_a' in H5.
      inverts H5.
      go.

      eapply H4.
      eauto.
    }
  }

  {
    swapname H H3.
    smartunfold3.
    simpljoin.
    splits.
    {
      intros.
      lets bb: H H6.
      simpljoin.
      do 3 eexists.
      unfold get, sig, join in *; simpl in *.
      go.
    }
    {
      intros.
      unfold get, sig, join in *; simpl in *.
      eapply TcbMod.join_get_or in H6.
      2: exact H0.
      destruct H6.
      assert (tid0 = v'34 \/ tid0 <> v'34).
      tauto.
      destruct H7.
      subst.
      rewrite TcbMod.get_a_sig_a in H6.
      inverts H6.
      go.
      
      rewrite TcbMod.get_a_sig_a' in H6.
      inverts H6.
      go.

      eapply H4.
      eauto.
    }

    unfolds.
    intros.
    unfolds in H5.
    lets bb: H5 H6.
    simpljoin.
    do 3 eexists.
    unfold get, sig, join in *; simpl in *.
    go.
  }

  
Qed.

Lemma update_eq :
  forall ls n c,
    nth_val n ls= Some c ->
    ls = update_nth_val n ls c.
Proof.
  induction ls.
  intros.
  simpl in H.
  inversion H.
  induction n.
  intros.
  simpl in H.
  simpl.
  inverts H.
  auto.
  intros.
  simpl.
  assert (ls = update_nth_val n ls c).
  apply IHls.
  simpl in H.
  auto.
  rewrite <- H0.
  auto.
Qed.


Lemma tcblist_p_hold_for_add_tcb'' :
  forall v'26 v'42 v'34 v'39 v'30 vleft x v'22,
    0 <= Int.unsigned v'42 < 64 ->
    array_type_vallist_match Int8u v'26 ->
    length v'26 = ∘ OS_RDY_TBL_SIZE ->
    ~ (exists id t m, get v'22 id = Some (v'42, t, m)) ->
    TCBList_P v'30 vleft v'26 v'22 ->
    new_tcb_node_p v'42 Vnull v'30 v'39 ->
    join (sig v'34 (v'42, rdy, Vnull)) v'22 x -> 
    TCBList_P (Vptr v'34) ((v'39 :: nil) ++ vleft)
              (update_nth_val (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26
                              (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26)
                                     (nth_val' (Z.to_nat (Int.unsigned (v'42&ᵢ$ 7))) OSMapVallist))))
              x.
Proof.
  intros.
  change ((v'39::nil) ++ vleft) with (v'39 :: vleft).
  unfold1 TCBList_P.
  repeat tri_exists_and_solver1.
  Focus 3.
  eapply tcblist_p_hold_for_add_tcb_lemma; eauto.
  unfolds in H4.
  simpljoin; auto.
(* ** ac:   SearchAbout TCBNode_P. *)

  assert ((nth_val' (Z.to_nat (Int.unsigned (v'42&ᵢ$ 7))) OSMapVallist) = Vint32 ($ 1<<ᵢ(v'42&ᵢ$ 7)) ) as HH1.
  assert ((Int.unsigned (v'42&ᵢ$ 7)) <= 7).
  clear -H.
  mauto.
  clear -H6.
  remember (v'42&ᵢ$ 7) .
  mauto.

  assert (exists grp, nth_val ∘ (Int.unsigned (v'42 >>ᵢ $ 3)) v'26 = Some (Vint32 grp) ) as HH2.
  eapply new_rtbl.prio_set_rdy_in_tbl_lemma_1; auto.
  destruct HH2 as (group & HH2).
  unfold nat_of_Z in HH2.
  lets HH2': (nth_val_nth_val'_some_eq _ _ HH2).

  rewrite HH1, HH2'.


  unfolds.
  unfolds in H4.
  splits; simpljoin; auto.
  unfolds.
  repeat tri_exists_and_solver1.
  Focus 3.
(* ** ac:   SearchAbout R_TCB_Status_P. *)
  unfolds.
  splits.
  {
    unfolds.
    intros.
    unfolds in H18.
    simpljoin.
    rewrite H6 in H18.
    inverts H18.
    repeat tri_exists_and_solver1.
  }

  {
    unfolds.
    intros.
    inverts H18.
    repeat tri_exists_and_solver1.
    unfolds.
    splits.
    auto.
(* ** ac:     Check prio_in_tbl_orself. *)
    simpl.
    eapply prio_in_tbl_orself.
  }

  {
    unfolds.
    splits.
    {
      unfolds.
      intros.
      unfolds in H18.
      simpljoin.
      rewrite H6 in H18.
      inverts H18.
      lets bb: prio_notin_tbl_orself H17 HH2.

      simpl in H20.
      tryfalse.
    }
    {
      unfolds.
      intros.
      unfolds in H18.
      simpljoin.
      rewrite H6 in H18.
      inverts H18.
      lets bb: prio_notin_tbl_orself H17 HH2.

      simpl in H20.
      tryfalse.
    }

    {
      unfolds.
      intros.
      unfolds in H18.
      simpljoin.
      rewrite H6 in H18.
      inverts H18.
      lets bb: prio_notin_tbl_orself H17 HH2.

      simpl in H20.
      tryfalse.
    }

    {
      unfolds.
      intros.
      unfolds in H18.
      simpljoin.
      rewrite H6 in H18.
      inverts H18.
      lets bb: prio_notin_tbl_orself H17 HH2.

      simpl in H20.
      tryfalse.
    }
    {
      unfolds.
      intros.
      unfolds in H18.
      simpljoin.
      rewrite H6 in H18.
      inverts H18.
      lets bb: prio_notin_tbl_orself H17 HH2.

      simpl in H20.
      tryfalse.
    }
    
  }

  {
    unfolds.
    splits.
    {
      unfolds.
      intros.
      inverts H18.
    }
    {
      unfolds.
      intros.
      inverts H18.
    }

    {
      unfolds.
      intros.
      inverts H18.
    }

    {
      unfolds.
      intros.
      inverts H18.
    }

    {
      unfolds.
      intros.
      inverts H18.
    }
  }
  Unfocus.
  rewrite HH1 in H12.
  auto.

  assert ((Int.unsigned (v'42>>ᵢ$ 3)) <= 7).
  clear -H17.
  mauto.
  assert ((nth_val' (Z.to_nat (Int.unsigned (v'42>>ᵢ$ 3))) OSMapVallist) = Vint32 ($ 1<<ᵢ(v'42>>ᵢ$ 3)) ) as HH3.
  clear -H18.
  remember (v'42>>ᵢ$ 3) .
  mauto.

  rewrite HH3 in H10.
  auto.


  
Qed.


Lemma mem_overlap_PV:
  forall s p v0 v P,
    s |= PV p @ STRUCT os_tcb ⋆ |-> v0 **
      PV p @ STRUCT os_tcb ⋆ |-> v  ** P ->
    False.
Proof.
  intros.
  assert (p <> p).
(* ** ac:   Check pv_false. *)
  eapply pv_false.
  3: eauto.
  unfold array_struct.
  intro.
  destruct H0; simpljoin; tryfalse.
  destruct H0; simpljoin; tryfalse.

  unfold array_struct.
  intro.
  destruct H0; simpljoin; tryfalse.
  destruct H0; simpljoin; tryfalse.
  apply H0; auto.
Qed.


Lemma mem_overlap_struct:
  forall s v1 v2 p P,
    s |= Astruct p OS_TCB_flag v1 ** Astruct p OS_TCB_flag v2 ** P ->
    False.
Proof.
  intros.
  unfold Astruct in H.
  unfold OS_TCB_flag in H.
  unfold Astruct' in H.
  destruct v1.
  sep destroy H.
  simpl in H0; tryfalse.
  destruct p.
  destruct v2.
  sep destroy H.
  simpl in H1; tryfalse.
  sep normal in H.
  sep lift 3%nat in H.
  Set Printing Depth 999.
(* ** ac:   Show. *)
  remember (match v1 with
              | nil => Afalse
              | v :: vl' =>
                PV (b, i +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) @
                   STRUCT os_tcb ⋆ |-> v **
                   match vl' with
                     | nil => Afalse
                     | v0 :: vl'0 =>
                       PV (b,
                           (i +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                           $ Z.of_nat (typelen STRUCT os_tcb ⋆)) @ 
                          OS_EVENT ∗ |-> v0 **
                          match vl'0 with
                            | nil => Afalse
                            | v1 :: vl'1 =>
                              PV (b,
                                  ((i +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                   $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                                                            $ Z.of_nat (typelen OS_EVENT ∗)) @ 
                                 (Void) ∗ |-> v1 **
                                 match vl'1 with
                                   | nil => Afalse
                                   | v2 :: vl'2 =>
                                     PV (b,
                                         (((i +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆))
                                           +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                        $ Z.of_nat (typelen OS_EVENT ∗)) +ᵢ
                                                                                                                            $ Z.of_nat (typelen (Void) ∗)) @ 
                                        Int16u |-> v2 **
                                        match vl'2 with
                                          | nil => Afalse
                                          | v3 :: vl'3 =>
                                            PV (b,
                                                ((((i +ᵢ
                                                         $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                                  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                                                                           $ Z.of_nat (typelen OS_EVENT ∗)) +ᵢ
                                                                                                                                                                               $ Z.of_nat (typelen (Void) ∗)) +ᵢ
                                                                                                                                                                                                                 $ Z.of_nat (typelen Int16u)) @ 
                                               Int8u |-> v3 **
                                               match vl'3 with
                                                 | nil => Afalse
                                                 | v4 :: vl'4 =>
                                                   PV (b,
                                                       (((((i +ᵢ
                                                                 $ Z.of_nat (typelen STRUCT os_tcb ⋆))
                                                           +ᵢ
                                                              $ Z.of_nat (typelen STRUCT os_tcb ⋆))
                                                          +ᵢ  $ Z.of_nat (typelen OS_EVENT ∗))
                                                         +ᵢ  $ Z.of_nat (typelen (Void) ∗)) +ᵢ
                                                                                               $ Z.of_nat (typelen Int16u)) +ᵢ
                                                                                                                               $ Z.of_nat (typelen Int8u)) @ 
                                                      Int8u |-> v4 **
                                                      match vl'4 with
                                                        | nil => Afalse
                                                        | v5 :: vl'5 =>
                                                          PV (b,
                                                              ((((((i +ᵢ
                                                                         $
                                                                         Z.of_nat
                                                                         (typelen STRUCT os_tcb ⋆))
                                                                   +ᵢ
                                                                      $
                                                                      Z.of_nat
                                                                      (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                                    $ Z.of_nat (typelen OS_EVENT ∗))
                                                                 +ᵢ  $ Z.of_nat (typelen (Void) ∗))
                                                                +ᵢ  $ Z.of_nat (typelen Int16u))
                                                               +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
                                                                                                  $ Z.of_nat (typelen Int8u)) @ 
                                                             Int8u |-> v5 **
                                                             match vl'5 with
                                                               | nil => Afalse
                                                               | v6 :: vl'6 =>
                                                                 PV (b,
                                                                     (((((((i +ᵢ
                                                                                 $
                                                                                 Z.of_nat
                                                                                 (typelen STRUCT os_tcb ⋆))
                                                                           +ᵢ
                                                                              $
                                                                              Z.of_nat
                                                                              (typelen STRUCT os_tcb ⋆))
                                                                          +ᵢ
                                                                             $
                                                                             Z.of_nat
                                                                             (typelen OS_EVENT ∗)) +ᵢ
                                                                                                      $ Z.of_nat (typelen (Void) ∗))
                                                                        +ᵢ
                                                                           $ Z.of_nat (typelen Int16u))
                                                                       +ᵢ  
                                                                          $ Z.of_nat (typelen Int8u)) +ᵢ
                                                                                                         $ Z.of_nat (typelen Int8u)) +ᵢ
                                                                                                                                        $ Z.of_nat (typelen Int8u)) @
                                                                    Int8u |-> v6 **
                                                                    match vl'6 with
                                                                      | nil => Afalse
                                                                      | v7 :: vl'7 =>
                                                                        PV (b,
                                                                            ((((((((i +ᵢ
                                                                                         $
                                                                                         Z.of_nat
                                                                                         (typelen STRUCT os_tcb ⋆))
                                                                                   +ᵢ
                                                                                      $
                                                                                      Z.of_nat
                                                                                      (typelen STRUCT os_tcb ⋆))
                                                                                  +ᵢ
                                                                                     $
                                                                                     Z.of_nat
                                                                                     (typelen OS_EVENT ∗)) +ᵢ
                                                                                                              $
                                                                                                              Z.of_nat (typelen (Void) ∗))
                                                                                +ᵢ
                                                                                   $ Z.of_nat (typelen Int16u))
                                                                               +ᵢ
                                                                                  $ Z.of_nat (typelen Int8u))
                                                                              +ᵢ
                                                                                 $ Z.of_nat (typelen Int8u))
                                                                             +ᵢ
                                                                                $ Z.of_nat (typelen Int8u))
                                                                            +ᵢ
                                                                               $ Z.of_nat (typelen Int8u)) @
                                                                           Int8u |-> v7 **
                                                                           match vl'7 with
                                                                             | nil => Afalse
                                                                             | v8 :: vl'8 =>
                                                                               PV 
                                                                                 (b,
                                                                                  (((((((((i +ᵢ
                                                                                                $
                                                                                                Z.of_nat
                                                                                                (typelen STRUCT os_tcb ⋆))
                                                                                          +ᵢ
                                                                                             $
                                                                                             Z.of_nat
                                                                                             (typelen STRUCT os_tcb ⋆))
                                                                                         +ᵢ
                                                                                            $
                                                                                            Z.of_nat
                                                                                            (typelen OS_EVENT ∗)) +ᵢ
                                                                                                                     $
                                                                                                                     Z.of_nat (typelen (Void) ∗))
                                                                                       +ᵢ
                                                                                          $ Z.of_nat (typelen Int16u))
                                                                                      +ᵢ
                                                                                         $ Z.of_nat (typelen Int8u))
                                                                                     +ᵢ
                                                                                        $ Z.of_nat (typelen Int8u))
                                                                                    +ᵢ
                                                                                       $ Z.of_nat (typelen Int8u))
                                                                                   +ᵢ
                                                                                      $ Z.of_nat (typelen Int8u))
                                                                                  +ᵢ
                                                                                     $ Z.of_nat (typelen Int8u)) @
                                                                                 Int8u |-> v8 **
                                                                                 match vl'8 with
                                                                                   | nil => Aemp
                                                                                   | _ :: _ => Afalse
                                                                                 end
                                                                           end
                                                                    end
                                                             end
                                                      end
                                               end
                                        end
                                 end
                          end
                   end
            end). 
  remember (
      match v2 with
        | nil => Afalse
        | v :: vl' =>
          PV (b, i +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) @
             STRUCT os_tcb ⋆ |-> v **
             match vl' with
               | nil => Afalse
               | v0 :: vl'0 =>
                 PV (b,
                     (i +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                     $ Z.of_nat (typelen STRUCT os_tcb ⋆)) @ 
                    OS_EVENT ∗ |-> v0 **
                    match vl'0 with
                      | nil => Afalse
                      | v1 :: vl'1 =>
                        PV (b,
                            ((i +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                             $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                                                      $ Z.of_nat (typelen OS_EVENT ∗)) @ 
                           (Void) ∗ |-> v1 **
                           match vl'1 with
                             | nil => Afalse
                             | v2 :: vl'2 =>
                               PV (b,
                                   (((i +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆))
                                     +ᵢ  $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                  $ Z.of_nat (typelen OS_EVENT ∗)) +ᵢ
                                                                                                                      $ Z.of_nat (typelen (Void) ∗)) @ 
                                  Int16u |-> v2 **
                                  match vl'2 with
                                    | nil => Afalse
                                    | v3 :: vl'3 =>
                                      PV (b,
                                          ((((i +ᵢ
                                                   $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                            $ Z.of_nat (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                                                                     $ Z.of_nat (typelen OS_EVENT ∗)) +ᵢ
                                                                                                                                                                         $ Z.of_nat (typelen (Void) ∗)) +ᵢ
                                                                                                                                                                                                           $ Z.of_nat (typelen Int16u)) @ 
                                         Int8u |-> v3 **
                                         match vl'3 with
                                           | nil => Afalse
                                           | v4 :: vl'4 =>
                                             PV (b,
                                                 (((((i +ᵢ
                                                           $ Z.of_nat (typelen STRUCT os_tcb ⋆))
                                                     +ᵢ
                                                        $ Z.of_nat (typelen STRUCT os_tcb ⋆))
                                                    +ᵢ  $ Z.of_nat (typelen OS_EVENT ∗))
                                                   +ᵢ  $ Z.of_nat (typelen (Void) ∗)) +ᵢ
                                                                                         $ Z.of_nat (typelen Int16u)) +ᵢ
                                                                                                                         $ Z.of_nat (typelen Int8u)) @ 
                                                Int8u |-> v4 **
                                                match vl'4 with
                                                  | nil => Afalse
                                                  | v5 :: vl'5 =>
                                                    PV (b,
                                                        ((((((i +ᵢ
                                                                   $
                                                                   Z.of_nat
                                                                   (typelen STRUCT os_tcb ⋆))
                                                             +ᵢ
                                                                $
                                                                Z.of_nat
                                                                (typelen STRUCT os_tcb ⋆)) +ᵢ
                                                                                              $ Z.of_nat (typelen OS_EVENT ∗))
                                                           +ᵢ  $ Z.of_nat (typelen (Void) ∗))
                                                          +ᵢ  $ Z.of_nat (typelen Int16u))
                                                         +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ
                                                                                            $ Z.of_nat (typelen Int8u)) @ 
                                                       Int8u |-> v5 **
                                                       match vl'5 with
                                                         | nil => Afalse
                                                         | v6 :: vl'6 =>
                                                           PV (b,
                                                               (((((((i +ᵢ
                                                                           $
                                                                           Z.of_nat
                                                                           (typelen STRUCT os_tcb ⋆))
                                                                     +ᵢ
                                                                        $
                                                                        Z.of_nat
                                                                        (typelen STRUCT os_tcb ⋆))
                                                                    +ᵢ
                                                                       $
                                                                       Z.of_nat
                                                                       (typelen OS_EVENT ∗)) +ᵢ
                                                                                                $ Z.of_nat (typelen (Void) ∗))
                                                                  +ᵢ
                                                                     $ Z.of_nat (typelen Int16u))
                                                                 +ᵢ  
                                                                    $ Z.of_nat (typelen Int8u)) +ᵢ
                                                                                                   $ Z.of_nat (typelen Int8u)) +ᵢ
                                                                                                                                  $ Z.of_nat (typelen Int8u)) @
                                                              Int8u |-> v6 **
                                                              match vl'6 with
                                                                | nil => Afalse
                                                                | v7 :: vl'7 =>
                                                                  PV (b,
                                                                      ((((((((i +ᵢ
                                                                                   $
                                                                                   Z.of_nat
                                                                                   (typelen STRUCT os_tcb ⋆))
                                                                             +ᵢ
                                                                                $
                                                                                Z.of_nat
                                                                                (typelen STRUCT os_tcb ⋆))
                                                                            +ᵢ
                                                                               $
                                                                               Z.of_nat
                                                                               (typelen OS_EVENT ∗)) +ᵢ
                                                                                                        $
                                                                                                        Z.of_nat (typelen (Void) ∗))
                                                                          +ᵢ
                                                                             $ Z.of_nat (typelen Int16u))
                                                                         +ᵢ
                                                                            $ Z.of_nat (typelen Int8u))
                                                                        +ᵢ
                                                                           $ Z.of_nat (typelen Int8u))
                                                                       +ᵢ
                                                                          $ Z.of_nat (typelen Int8u))
                                                                      +ᵢ
                                                                         $ Z.of_nat (typelen Int8u)) @
                                                                     Int8u |-> v7 **
                                                                     match vl'7 with
                                                                       | nil => Afalse
                                                                       | v8 :: vl'8 =>
                                                                         PV 
                                                                           (b,
                                                                            (((((((((i +ᵢ
                                                                                          $
                                                                                          Z.of_nat
                                                                                          (typelen STRUCT os_tcb ⋆))
                                                                                    +ᵢ
                                                                                       $
                                                                                       Z.of_nat
                                                                                       (typelen STRUCT os_tcb ⋆))
                                                                                   +ᵢ
                                                                                      $
                                                                                      Z.of_nat
                                                                                      (typelen OS_EVENT ∗)) +ᵢ
                                                                                                               $
                                                                                                               Z.of_nat (typelen (Void) ∗))
                                                                                 +ᵢ
                                                                                    $ Z.of_nat (typelen Int16u))
                                                                                +ᵢ
                                                                                   $ Z.of_nat (typelen Int8u))
                                                                               +ᵢ
                                                                                  $ Z.of_nat (typelen Int8u))
                                                                              +ᵢ
                                                                                 $ Z.of_nat (typelen Int8u))
                                                                             +ᵢ
                                                                                $ Z.of_nat (typelen Int8u))
                                                                            +ᵢ
                                                                               $ Z.of_nat (typelen Int8u)) @
                                                                           Int8u |-> v8 **
                                                                           match vl'8 with
                                                                             | nil => Aemp
                                                                             | _ :: _ => Afalse
                                                                           end
                                                                     end
                                                              end
                                                       end
                                                end
                                         end
                                  end
                           end
                    end
             end
      end ).
  clear -H.
  eapply mem_overlap_PV.
  instantiate (6:=s).
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  eauto.
Qed.

Lemma sometcblist_lemma:
  forall v v'22 s ptr vv a0 a2 a3 v'26 P a1, 
    s|= node (Vptr ptr) vv OS_TCB_flag ** tcbdllseg a0 a1 a2 a3 v ** P ->
    TCBList_P a0 v v'26 v'22 ->
    ~ TcbMod.indom v'22 ptr.
Proof.
  induction v.
  intros.
  simpl in H0.
  subst.
  intro.
  unfolds in H0.
  inverts H0.
  inverts H1.
  intros.
  lets back: H0.
  unfold1 TCBList_P in H0.
  simpljoin.
  unfold tcbdllseg in H.
  unfold1 dllseg in H.
  sep normal in  H.
  sep destruct H.
  sep split in H.
  assert (~ TcbMod.indom x1 ptr).
  eapply IHv.
  instantiate (7 := s).
  sep cancel 3%nat 1%nat.
  unfold tcbdllseg.
  sep cancel 2%nat 1%nat.
  eauto.
  rewrite H1 in H0.
  inverts H0.
  eauto.
  assert ( x <> ptr).
  intro.
  sep lift 3%nat in H.
  unfold node in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  subst x.
  simpljoin.
  inverts H10.
  inverts H8.
  
  eapply mem_overlap_struct.
  eauto.
  intro.
  unfolds in H9.
  simpljoin.
  unfolds in H2.
  
  eapply TcbMod.join_get_or in H9.
  2: exact H2.
  destruct H9.
  unfold sig in H9; simpl in H9.
  rewrite TcbMod.get_a_sig_a' in H9.
  inverts H9.
  go.
  apply H7.
  eexists.
  eauto.
Qed.
Lemma not_in_priotbl_no_priotcb:
  forall v'28 v'14 v'43 v'42,
    R_PrioTbl_P v'28 v'14 v'43 ->
    Int.unsigned v'42 < 64 ->
    nth_val' (Z.to_nat (Int.unsigned v'42)) v'28 = Vnull ->
    ~ (exists id t m, get v'14 id = Some (v'42, t, m)).
Proof.
  intros.
  unfolds in H.
  simpljoin.
  intro.
  simpljoin.
  lets bb: H2 H4. 
  simpljoin.
  apply nv'2nv in H1.
  unfold nat_of_Z in H5.
  rewrite H1 in H5.
  inverts H5.
  intro; tryfalse.
Qed.


