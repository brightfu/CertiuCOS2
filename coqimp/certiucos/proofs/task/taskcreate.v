Require Import ucos_include.
Require Import os_ucos_h.
Require Import sep_lemmas_ext.
Require Import linv_solver.
Require Import taskcreate_pure.
Require Import protect.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Theorem TaskCreateProof:
  forall  vl p r tid, 
    Some p =
    BuildPreA' os_api OSTaskCreate taskcreapi vl  OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api OSTaskCreate taskcreapi vl  OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSTaskCreate = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  hoare unfold.
  hoare forward.
  math simpls.
  destruct ( Int.ltu ($ OS_LOWEST_PRIO) i); simpl; intro; tryfalse.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskcre_prio_invalid.
  go.
  unfold OS_LOWEST_PRIO in *.
  int auto.
  
  hoare forward.
  hoare forward.
  hoare unfold.
  hoare forward prim.
  hoare normal pre.
  hoare unfold.
  assert (Int.unsigned i < 64).
  clear -H.

  unfold OS_LOWEST_PRIO in *.
  int auto.
  destruct H; simpl in H; tryfalse.
  clear H.
  assert (   rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned i)) v'5) = true).
  apply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match.
  rewrite H8.
  clear -H9; mauto.
  auto.

  hoare forward.
  math simpls.
  auto.
  unfolds in H.
  destruct ( nth_val' (Z.to_nat (Int.unsigned i)) v'5 ); tryfalse.
  simpl.
  intro; tryfalse.

  simpl.
  destruct a.
  intro; tryfalse.
  instantiate (1 := Afalse).
  Focus 2.
  (* error path *)
  hoare forward.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.

  eapply absimp_taskcre_prio_already_exists.
  go.
  hoare forward prim.
  unfold AOSTCBPrioTbl.
  sep pauto.
  go.
  hoare forward.

  (* right path *) 

  

  hoare unfold.
  hoare_assert_pure (   array_type_vallist_match Int8u v'11/\ length v'11 = ∘ OS_RDY_TBL_SIZE ) .
  unfold AOSRdyTblGrp in H13.
  unfold AOSRdyTbl in H13.
  sep normal in H13.
  sep split in H13.
  auto.
  hoare_split_pure_all.
  rename H13 into somehyp.
  protect somehyp.
  
  assert ((nth_val' (Z.to_nat (Int.unsigned i)) v'5) = Vnull).
  remember (nth_val' (Z.to_nat (Int.unsigned i)) v'5).

  destruct H.

  auto.
  simpljoin.
  rewrite H in *.
  simpl in *.
  destruct x; simpl in *.
  tryfalse.
  clear H10 H11 H12.
  hoare unfold.
  unfold AOSTCBList.
  hoare unfold.
  hoare forward.
  math simpls.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Aisr.
  sep cancel Acs.
  sep cancel AOSTCBFreeList.
  sep cancel Aop.
  sep cancel AOSRdyTblGrp.
  sep cancel 9%nat 1%nat.
  sep cancel 3%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  eauto.
  eauto.

  go.
  go.
  math simpl.
  clear -H9 l.
  unfold OS_LOWEST_PRIO in l.
  int auto.
  go.
  apply retpost_tcbinitpost.

  math simpl.
  clear -H1 H15.
  change Byte.max_unsigned with 255 in H15.
  omega.


  repeat intro.

  sep normal in H15.
  sep destruct H15.
  sep lift 6%nat in H15.

  disj_asrt_destruct H15.
  sep normal in H15.
  sep destruct H15.
  sep eexists.
  sep cancel p_local.
  simpl; auto.

  sep normal in H15.
  sep destruct H15.
  sep eexists.
  sep cancel p_local.
  simpl; auto.

  linv_solver.
  
  hoare unfold.
  hoare lift 6%nat pre.
  eapply backward_rule1.
  intro.
  intros.
  eapply disj_star_elim_disj in H15.
  eauto.
  hoare forward.
  hoare unfold.
  inverts H18.

  (* no more tcb *)
  hoare forward.
  hoare unfold.
  false.
  change (Int.eq ($ OS_NO_MORE_TCB) ($ OS_NO_ERR)) with false in *.
  simpl in *.
  apply H18; auto.
  hoare unfold.
  
  hoare abscsq.
  apply noabs_oslinv.

  eapply absimp_taskcre_no_more_tcb.
  go.
  
  
  instantiate (1 :=    <|| END Some (V$ OS_NO_MORE_TCB) ||>  **
                               Aisr empisr **
                               Aie true **
                               Ais nil ** Acs nil ** p_local OSLInv tid init_lg **
                               A_dom_lenv
                               ((prio, Int8u)
                                  :: (os_code_defs.pdata, (Void) ∗)
                                  :: (task, (Void) ∗) :: (err, Int8u) :: nil) **
                               LV err @ Int8u |-> (V$ OS_NO_MORE_TCB)  ** LV prio @ Int8u |-> Vint32 i **
                               LV os_code_defs.pdata @ (Void) ∗ |-> x0 ** LV task @ (Void) ∗ |-> x1
              ).
  
  hoare forward prim.
  sep cancel tcbdllflag.
  
  sep cancel A_dom_lenv.
  sep pauto.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  sep pauto.
  sep cancel 3%nat 1%nat.
  
  sep cancel 3%nat 1%nat.
  sep cancel 2%nat 1%nat.
  
  assumption.
  go.
  go.
  go.
  go.
  go.
  go.

  hoare forward.
  hoare_split_pure_all.
  false.
  clear -H18.
  simpljoin.
  change (Int.eq ($ OS_NO_MORE_TCB) ($ OS_NO_ERR)) with false in *.
  simpl in *.
  apply H; auto.

  (* right path *)
  hoare forward.

  hoare unfold.
  inverts H19.

  hoare forward.
  
  hoare unfold.
  Focus 2.
  hoare unfold.
  false.
  clear -H17.
  change (Int.eq ($ OS_NO_ERR) ($ OS_NO_ERR)) with true in H17.
  simpl in H17; destruct H17; tryfalse.

  
  

  hoare abscsq.
  apply noabs_oslinv.
  apply absimp_taskcre_succ.
  go.

  
  hoare_assert_pure (GoodLInvAsrt OSLInv).
  unfold p_local in H21.
  unfold LINV in H21.
  sep normal in H21.
  sep split in H21.
  auto.
  instantiate (1 :=
                 EX x, (
                   POST [OS_SchedPost, nil, x,
                         logic_code (END Some (V$ NO_ERR)) :: nil, tid] **
                        LV err @ Int8u |-> (V$ OS_NO_ERR) **
                        LV prio @ Int8u |-> Vint32 v'42 **
                        LV os_code_defs.pdata @ (Void) ∗ |-> x0 **
                        LV task @ (Void) ∗ |-> x1 **
                        A_dom_lenv
                        ((prio, Int8u)
                           :: (os_code_defs.pdata, (Void) ∗)
                           :: (task, (Void) ∗) :: (err, Int8u) :: nil)
                 )).


  hoare_assert_pure(exists new_tcbmod, TcbJoin v'34 (v'42, rdy, Vnull) v'14 new_tcbmod).
  
    unfold TcbJoin.
    eexists.
    eapply map_join_comm.
    
    unfold join; simpl.
    eapply TcbMod.join_sig_set.
    auto.
    intro.
    eapply (join_in_or H11) in H24.
    destruct H23.
    simpljoin.
    unfolds in H27.
    inverts H27.
    destruct H24.
    gen H23.
    eapply sometcblist_lemma.
    instantiate ( 8:= s0).
    sep cancel 13%nat 1%nat.
    sep cancel 14%nat 1%nat.
    eauto.
    eauto.

    gen H23.
    eapply sometcblist_lemma.
    instantiate ( 8:= s0).
    sep cancel 13%nat 1%nat.
    sep cancel 16%nat 1%nat.
    eauto.
    eapply  tcblist_p_hold_for_upd_1.
    eauto.



    simpljoin.
    unfolds in H26.
    inverts H26.

    destruct v'35.
    inverts H28.
    inverts H28.

    destruct H24.
    gen H24.
    eapply sometcblist_lemma.
    instantiate ( 8:= s0).
    sep cancel 13%nat 1%nat.
    sep cancel 14%nat 1%nat.
    eauto.
    eapply  tcblist_p_hold_for_upd_1.
    eauto.

    gen H24.
    eapply sometcblist_lemma.
    instantiate ( 8:= s0).
    sep cancel 13%nat 1%nat.
    sep cancel 16%nat 1%nat.
    eauto.
    eauto.
  hoare_split_pure_all.
  simpljoin.


  eapply backward_rule1.
  intro.
  Set Printing Depth 999.
  intros.
 
  instantiate (1 :=
    (<||
       scrt (x1 :: x0 :: Vint32 v'42 :: nil);;
       isched;; END Some (V$ NO_ERR) 
       ||>  ** 
       (
       HECBList v'13 **
       HTime v'15 **
       AOSTCBFreeList v'24 v'25 **
       AOSMapTbl **
       GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
       (update_nth_val (Z.to_nat (Int.unsigned v'42)) v'28 (Vptr v'34)) **
       G& OSPlaceHolder @ Int8u == v'43 **
       PV v'43 @ Int8u |-> v'45 **
       GV OSTCBList @ OS_TCB ∗ |-> Vptr v'34 **
       node (Vptr v'34) v'39 OS_TCB_flag **
       PV get_off_addr v'34 ($ 24) @ Int8u |-r-> (V$ 1) **
       tcbdllseg v'30 (Vptr v'34) v'32 (Vptr tid) v'36 **
       GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid **
       tcbdllseg (Vptr tid) v'32 v'33 Vnull v'38 **
       AOSRdyTblGrp
       (update_nth_val (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26
                       (val_inj
                          (or
                             (nth_val' (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26)
                             (nth_val' (Z.to_nat (Int.unsigned (v'42&ᵢ$ 7)))
                                       OSMapVallist)))) v'41 **
       p_local OSLInv tid init_lg **
       
       LV err @ Int8u |-> (V$ OS_NO_ERR) **
       AOSEventFreeList v'0 **
       AOSQFreeList v'1 **
       AOSQFreeBlk v'2 **
       AECBList v'4 v'3 v'13 v'14 **
       AOSUnMapTbl **
       AOSIntNesting **
       AOSTime (Vint32 v'15) **
       AGVars **
       tcbdllflag v'30 (v'35 ++ v'9 :: v'10) **
       atoy_inv' **
       LV prio @ Int8u |-> Vint32 v'42 **
       LV os_code_defs.pdata @ (Void) ∗ |-> x0 **
       LV task @ (Void) ∗ |-> x1 **
       A_dom_lenv
       ((prio, Int8u)
          :: (os_code_defs.pdata, (Void) ∗)
          :: (task, (Void) ∗) :: (err, Int8u) :: nil)
       ) **
       OSLInv v'34 init_lg **
       HTCBList v'14  **
       HCurTCB tid ** 
       OS [ empisr, false, nil, (true::nil)]  
    )).
  remember (
       HECBList v'13 **
       HTime v'15 **
       AOSTCBFreeList v'24 v'25 **
       AOSMapTbl **
       GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
         (update_nth_val (Z.to_nat (Int.unsigned v'42)) v'28 (Vptr v'34)) **
       G& OSPlaceHolder @ Int8u == v'43 **
       PV v'43 @ Int8u |-> v'45 **
       GV OSTCBList @ OS_TCB ∗ |-> Vptr v'34 **
       node (Vptr v'34) v'39 OS_TCB_flag **
       PV get_off_addr v'34 ($ 24) @ Int8u |-r-> (V$ 1) **
       tcbdllseg v'30 (Vptr v'34) v'32 (Vptr tid) v'36 **
       GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid **
       tcbdllseg (Vptr tid) v'32 v'33 Vnull v'38 **
       AOSRdyTblGrp
         (update_nth_val (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26
            (val_inj
               (or (nth_val' (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26)
                  (nth_val' (Z.to_nat (Int.unsigned (v'42&ᵢ$ 7)))
                     OSMapVallist)))) v'41 **
       p_local OSLInv tid init_lg **
       LV err @ Int8u |-> (V$ OS_NO_ERR) **
       AOSEventFreeList v'0 **
       AOSQFreeList v'1 **
       AOSQFreeBlk v'2 **
       AECBList v'4 v'3 v'13 v'14 **
       AOSUnMapTbl **
       AOSIntNesting **
       AOSTime (Vint32 v'15) **
       AGVars **
       tcbdllflag v'30 (v'35 ++ v'9 :: v'10) **
       atoy_inv' **
       LV prio @ Int8u |-> Vint32 v'42 **
       LV os_code_defs.pdata @ (Void) ∗ |-> x0 **
       LV task @ (Void) ∗ |-> x1 **
       A_dom_lenv
         ((prio, Int8u)
          :: (os_code_defs.pdata, (Void) ∗)
          :: (task, (Void) ∗) :: (err, Int8u) :: nil)).

  sep lifts (6::8:: nil)%nat.
  eapply elim_a_isr_is_prop.

  sep pauto.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel A_isr_is_prop.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  repeat sep cancel 2%nat 1%nat.
  repeat sep cancel 5%nat 3%nat.
  repeat sep cancel 4%nat 1%nat.
  unfold OSLInv.
  sep pauto.
  unfold init_lg.
  go.
  unfolds.
  left; auto.
  unfold scrt.
  
  eapply seq_rule.
  
  
   
  eapply cre_rule.
  assumption.
  go.
  unfold p_local.
  go.
  unfold CurTid.
  go.
  unfold LINV.
  go.
  unfold OSLInv.
  go.
  exact H21.
  clear -H4.
  unfolds in H4.
  simpljoin.
  unfolds.
  eauto.
  intro.
  intros.
  split.
  sep get rv.
  clear -H3.
  pauto.
  split.
  sep get rv.
  clear -H2.
  pauto.
  split.
  sep get rv.
  math simpls.
  apply len_lt_update_get_eq.
  rewrite H8.
  bsimplr.
  assumption.
  unfold CurLINV.
  unfold p_local in H26.
  sep pauto.
  sep cancel LINV.
  simpl; auto.
  eapply backward_rule1.
  intro; intros.
remember (
       HECBList v'13 **
       HTime v'15 **
       AOSTCBFreeList v'24 v'25 **
       AOSMapTbl **
       GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
         (update_nth_val (Z.to_nat (Int.unsigned v'42)) v'28 (Vptr v'34)) **
       G& OSPlaceHolder @ Int8u == v'43 **
       PV v'43 @ Int8u |-> v'45 **
       GV OSTCBList @ OS_TCB ∗ |-> Vptr v'34 **
       node (Vptr v'34) v'39 OS_TCB_flag **
       PV get_off_addr v'34 ($ 24) @ Int8u |-r-> (V$ 1) **
       tcbdllseg v'30 (Vptr v'34) v'32 (Vptr tid) v'36 **
       GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid **
       tcbdllseg (Vptr tid) v'32 v'33 Vnull v'38 **
       AOSRdyTblGrp
         (update_nth_val (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26
            (val_inj
               (or (nth_val' (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26)
                  (nth_val' (Z.to_nat (Int.unsigned (v'42&ᵢ$ 7)))
                     OSMapVallist)))) v'41 **
       p_local OSLInv tid init_lg **
       LV err @ Int8u |-> (V$ OS_NO_ERR) **
       AOSEventFreeList v'0 **
       AOSQFreeList v'1 **
       AOSQFreeBlk v'2 **
       AECBList v'4 v'3 v'13 v'14 **
       AOSUnMapTbl **
       AOSIntNesting **
       AOSTime (Vint32 v'15) **
       AGVars **
       tcbdllflag v'30 (v'35 ++ v'9 :: v'10) **
       atoy_inv' **
       LV prio @ Int8u |-> Vint32 v'42 **
       LV os_code_defs.pdata @ (Void) ∗ |-> x0 **
       LV task @ (Void) ∗ |-> x1 **
       A_dom_lenv
         ((prio, Int8u)
          :: (os_code_defs.pdata, (Void) ∗)
          :: (task, (Void) ∗) :: (err, Int8u) :: nil)).


  sep lifts (5::7::nil)%nat in H26.
  
  eapply add_a_isr_is_prop in H26.
  subst a.
  eauto.
  

  (***** two part ******)
    destruct H23.
      simpljoin.

      unfold tcbls_change_prev_ptr in H27.
      inverts H27.

      
      hoare forward prim.
      unfold AOSTCBPrioTbl.
      unfold AOSTCBList.
      sep pauto.
      sep cancel 1%nat 5%nat.
      sep cancel 1%nat 3%nat.
      instantiate (1 :=  (LV err @ Int8u |-> (V$ OS_NO_ERR) **
                                  LV prio @ Int8u |-> Vint32 v'42 **
                                  LV os_code_defs.pdata @ (Void) ∗ |-> x0 **
                                  LV task @ (Void) ∗ |-> x1 **
                                  A_dom_lenv
                                  ((prio, Int8u)
                                     :: (os_code_defs.pdata, (Void) ∗)
                                     :: (task, (Void) ∗) :: (err, Int8u) :: nil))).
      sep pauto.
      sep cancel A_dom_lenv.
      Focus 10.
      hoare forward.
      unfold init_lg in H23.
      sep cancel p_local.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Aop.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.
      
      unfold AECBList in *.
      sep pauto.
      sep cancel 1%nat 1%nat.
      sep cancel 4%nat 2%nat.
      instantiate (1 := (v'39 ::nil ) ++ nil).
      eapply inv_prop.tcbdllseg_compose.
      sep cancel 3%nat 2%nat.
      change (  (((v'39 :: nil) ++ nil) ++ update_nth_val 1 v'9 (Vptr v'34) :: v'10) ) with (v'39 :: update_nth_val 1 v'9 (Vptr v'34) :: v'10) .
      unfold tcbdllseg.
      unfold dllseg.
      sep pauto.
      unfold tcbdllflag.
      remember ( update_nth_val 1 v'9 (Vptr v'34) :: v'10).
      unfold1 dllsegflag.
      sep pauto.
      sep cancel 1%nat 1%nat.
      change (nil ++ v'9 :: v'10) with (v'9 :: v'10) in H23.
      unfold tcbdllflag in H23.
      unfold dllsegflag in *.
      sep destruct H23.
      
      sep pauto.
      unfolds.
      eapply nth_upd_neqrev.
      omega.
      auto.
      clear -H18.
      unfolds in H18.
      simpljoin; auto.
      

      clear -H18.
      unfolds in H18.
      simpljoin; auto.

      clear -H18.
      unfolds in H18.
      simpljoin; auto.
      eapply ecblist_hold_for_add_tcb; eauto.

      

      assert (v'43 <> v'34).
      
        unfold node in H23.
        sep normal in H23.
        sep destruct H23.
        sep split in H23.
        simpljoin.
        inverts H27.
        intro.
        eapply struct_pv_overlap.
(* ** ac:         Show. *)
(* ** ac:         Show. *)
        rewrite H27 in H23.
        sep lift 4%nat in H23.
        sep lift 2%nat in H23.
        exact H23.
          

        
      

      
      eapply r_priotbl_p_hold_for_add_tcb; eauto.
      assumption.
(* ** ac:       Print TCBList_P. *)
      instantiate (1:= v'23).
      eapply tcblist_p_hold_for_add_tcb.
      clear -H9.
      int auto.
      clear -somehyp.
      unprotect somehyp.
      tauto.

      clear -somehyp.
      unprotect somehyp.
      tauto.
      
      assumption.
      
      
        clear -H7 H13 H11.
        unfolds in H7.
        simpljoin.
        intro.
        simpljoin.
        assert (get v'14 x = Some (v'42, x0, x1)).
        unfold get,join in *; simpl in *.
        go.
        
        lets bb: H0 H3.
        simpljoin.
        eapply nth_val_nth_val'_some_eq in H4.
        unfold nat_of_Z in H4.
        rewrite H4 in H13.
        inverts H13.

      
     
      
    
   

      
  

      instantiate (1:= (sig v'34 (v'42, rdy, Vnull))).
      eapply tcblist_p_hold_for_add_tcb''.
      clear -H9.
      int auto.
      clear -somehyp .
      unprotect somehyp.
      tauto.
      clear -somehyp .
      unprotect somehyp.
      tauto.
        instantiate (1 := v'22).
        intro.
        simpljoin.
        assert (get v'14 x = Some (v'42, x2, x3)).
        unfold get,join,sig in *; simpl in *.
        go.
        eapply not_in_priotbl_no_priotcb; eauto.
      eauto.
      auto.

      eapply TCBList_P_nil_empty in H12.
      subst v'22.
      clear.
      join auto.
      simpl in H12.
      subst v'22.
      assert (v'23 = v'14).
      clear -H11.
      join auto.
      subst v'14.
      assumption.
      unfolds.
      unfolds in H4.
      simpljoin.
      clear -H4 H21.
      do 3 eexists.
      unfold get in *; simpl in *.
      eapply TcbMod.join_get_get_r.
      exact H21.
      eauto.

      eapply rh_t_e_p_hold_for_add_tcb.
      eauto.
      eauto.
      go.
      assert (exists t, join (sig v'34 (v'42, rdy, Vnull)) v'22 t ).
      clear -H21 H11.
      unfold TcbJoin in H21.
      join auto.
      simpljoin.

      unfold tcbls_change_prev_ptr in H27.
      destruct v'35.
      clear -H23; tryfalse.
      inverts H27.
      
      hoare forward prim.
      unfold AOSTCBPrioTbl.
      unfold AOSTCBList.
      sep pauto.
      sep cancel 1%nat 5%nat.
      sep cancel 1%nat 3%nat.
      instantiate (1 :=  (LV err @ Int8u |-> (V$ OS_NO_ERR) **
                                  LV prio @ Int8u |-> Vint32 v'42 **
                                  LV os_code_defs.pdata @ (Void) ∗ |-> x0 **
                                  LV task @ (Void) ∗ |-> x1 **
                                  A_dom_lenv
                                  ((prio, Int8u)
                                     :: (os_code_defs.pdata, (Void) ∗)
                                     :: (task, (Void) ∗) :: (err, Int8u) :: nil))).
      sep pauto.
      sep cancel A_dom_lenv.
      Focus 10.
      hoare forward.
      unfold init_lg in H27.
      sep cancel p_local.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Aop.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.
      
      unfold AECBList in *.
      sep pauto.
      sep cancel 1%nat 1%nat.
      sep cancel 4%nat 2%nat.
      instantiate (1 := (v'39 ::nil ) ++ ( (update_nth_val 1 v (Vptr v'34) :: v'35))).
      eapply inv_prop.tcbdllseg_compose.
      sep cancel 3%nat 2%nat.
      unfold tcbdllseg.
      unfold dllseg.
      sep pauto.
      unfold tcbdllflag.
      change ((v'39 :: nil) ++ update_nth_val 1 v (Vptr v'34) :: v'35) with (v'39 :: update_nth_val 1 v (Vptr v'34) :: v'35) .
      change (((v'39 :: update_nth_val 1 v (Vptr v'34) :: v'35) ++ v'9 :: v'10)) with (v'39 :: ((update_nth_val 1 v (Vptr v'34) :: v'35) ++ v'9 :: v'10)). 
      remember ((update_nth_val 1 v (Vptr v'34) :: v'35) ++ v'9 :: v'10).

      unfold1 dllsegflag.
      sep pauto.
      sep cancel 1%nat 1%nat.
      change  ((update_nth_val 1 v (Vptr v'34) :: v'35) ++ v'9 :: v'10) with  (update_nth_val 1 v (Vptr v'34) :: v'35 ++ v'9::v'10).
      change ((v :: v'35) ++ v'9 :: v'10) with (v :: v'35 ++ v'9 :: v'10) in H27.
      unfold tcbdllflag in H27.
      unfold dllsegflag in *.
      sep destruct H27.
      
      sep pauto.
      unfolds.
      eapply nth_upd_neqrev.
      omega.
      auto.
      clear -H18.
      unfolds in H18.
      simpljoin; auto.

      clear -H18.
      unfolds in H18.
      simpljoin; auto.

      clear -H18.
      unfolds in H18.
      simpljoin; auto.

      
      eapply ecblist_hold_for_add_tcb; eauto.
      
      eapply r_priotbl_p_hold_for_add_tcb; eauto.
        unfold node in H27.
        sep normal in H27.
        sep destruct H27.
        sep split in H27.
        simpljoin.
        inverts H29.
        intro.
        eapply struct_pv_overlap.
        rewrite H29 in H27.
        sep lift 4%nat in H27.
        sep lift 2%nat in H27.
        exact H27.
      assumption.
      instantiate (1:= v'23).
      
      assert (exists x, nth_val 1 v'9 = Some x).
      clear -H14.
      unfold1 TCBList_P in H14.
      simpljoin.
      unfolds in H2.
      destruct x2; destruct p.
      simpljoin.
      unfolds in H2.
      destruct v'9.
      inverts H2.
      destruct v'9.
      inverts H2.
      eexists.
      simpl.
      eauto.
      simpljoin.
      erewrite (update_eq v'9).
      
      eapply tcblist_p_hold_for_add_tcb.
      clear -H9.
      int auto.
      clear -somehyp.
      unprotect somehyp.
      tauto.
      clear -somehyp.
      unprotect somehyp.
      tauto.
      assumption.
        clear -H7 H13 H11.
        unfolds in H7.
        simpljoin.
        intro.
        simpljoin.
        assert (get v'14 x = Some (v'42, x0, x1)).
        unfold get,join in *; simpl in *.
        go.
        
        lets bb: H0 H3.
        simpljoin.
        eapply nth_val_nth_val'_some_eq in H4.
        unfold nat_of_Z in H4.
        rewrite H4 in H13.
        inverts H13.

      eauto.
      
      

      
      instantiate (1 := x). 
      eapply tcblist_p_hold_for_add_tcb''.
      clear -H9.
      int auto.
      clear -somehyp.
      unprotect somehyp.
      tauto.
      clear -somehyp.
      unprotect somehyp.
      tauto.
        instantiate (1 := v'22).
        intro.
        simpljoin.
        assert (get v'14 x2 = Some (v'42, x3, x4)).
        unfold get,join,sig in *; simpl in *.
        go.
        eapply not_in_priotbl_no_priotcb; eauto.
 
      eapply tcblist_p_hold_for_upd_1.
      eauto.
      eauto.
      go.
      clear -H21 H26 H11.
      unfold TcbJoin in H21.
      join auto.
      unfolds.
      unfolds in H4.
      simpljoin.
      clear -H4 H21.
      do 3 eexists.
      unfold get in *; simpl in *.
      eapply TcbMod.join_get_get_r.
      exact H21.
      eauto.


      

      eapply rh_t_e_p_hold_for_add_tcb.
      eauto.
      eauto.
      go.
      


  hoare forward.
  hoare unfold.
  unfold OS_SchedPost .
  unfold OS_SchedPost'.
  unfold getasrt.
  hoare unfold.
  hoare forward.
  inverts H21.
  reflexivity.
  hoare_split_pure_all.
  false.
  clear -H17.
  int auto.
  destruct H17; tryfalse.

  Grab Existential Variables.
  exact (Afalse).
  exact (Afalse).

Qed.
