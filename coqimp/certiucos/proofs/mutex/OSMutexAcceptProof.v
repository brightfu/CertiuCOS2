(**************************  uc/OS-II  ******************************) 
(*************************** OS_MUTEX.C *****************************) 
(****Proofs for API Fucntion:  void* OSMutexAccept(OS_EVENT* pevent**) 
(***************************** Code: ********************************) 
(***
Int8u ·OSMutexAccept·(⌞pevent @ OS_EVENT∗⌟)··{
        ⌞ 
          legal @ Int8u;
          pip @ Int8u
        ⌟; 
               
1         If(pevent′ ==ₑ NULL)
          {
2             RETURN ′0 
          };ₛ
3         ENTER_CRITICAL;ₛ
4         legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
5         If (legal′ ==ₑ ′0)
          {
6             EXIT_CRITICAL;ₛ
7             RETURN ′0 
          };ₛ
8         If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX)
          {
9           EXIT_CRITICAL;ₛ
10          RETURN ′0
          };ₛ
11        pip′  =ₑ 〈Int8u〉(pevent′→OSEventCnt ≫ ′8);ₛ
12        If ((OSTCBCur′→OSTCBPrio <ₑ pip′) ||ₑ (OSTCBCur′→OSTCBPrio ==ₑ pip′))
          {
13          EXIT_CRITICAL;ₛ
14          RETURN ′OS_ERR_MUTEX_PRIO
          };ₛ
15        If ((pevent′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8) ==ₑ ′OS_MUTEX_AVAILABLE)
          {
16          pevent′→OSEventCnt =ₑ pevent′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_UPPER_8;ₛ
17          pevent′→OSEventCnt =ₑ pevent′→OSEventCnt |ₑ OSTCBCur′→OSTCBPrio;ₛ
18          pevent′→OSEventPtr =ₑ ′OSTCBCur;ₛ
19          EXIT_CRITICAL;ₛ
20          RETURN ′1 
          };ₛ
21        EXIT_CRITICAL;ₛ
22        RETURN ′0  
*) 

Require Import ucos_include.
Require Import OSMutex_common.
Require Import os_ucos_h.
Require Import mutex_absop_rules.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Theorem OSMutexAccepteRight: 
  forall vl p r tid,
    Some p = BuildPreA' os_api OSMutexAccept mutexaccapi vl OSLInv tid init_lg->
    Some r = BuildRetA' os_api OSMutexAccept mutexaccapi vl OSLInv tid init_lg->
    exists t d1 d2 s,
      os_api OSMutexAccept = Some (t, d1, d2, s) /\ {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |- tid {{ p }} s {{ Afalse }}.
Proof.
  init_spec.
  destruct x.
  unfolds in H1;destruct H1; intros;  inversion H;
  try solve [inversion H;  inversion H0].
  Focus 2.
  unfolds in H1.
  elim H1; intros; inversion H.
  simpljoin.
  inversion H.

  hoare forward.
  (* intro; tryfalse. *)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply  mutexacc_null_absinfer.
  go.
  hoare forward.
  hoare forward.

  hoare unfold.
  false.
  elim H; intros; tryfalse.
  hoare forward.
  destruct a.
  intro; tryfalse.
  hoare unfold.
  instantiate (1:=Afalse).
  false.
  destruct a.
  simpl in H.
  apply H; auto.
  hoare forward.
  hoare unfold.

  hoare forward prim.
  hoare unfold.
  hoare forward.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel AECBList.
  sep cancel AOSTCBList.
  sep cancel tcbdllflag.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBPrioTbl.
  sep cancel 1%nat 1%nat.
  eauto 1.
  go.
  go.
  exact retpost_osev.
  intro.
  intros.
  {
    Require Import linv_solver.
    linv_solver.
  }
    linv_solver.
  hoare unfold.
  eapply backward_rule1.

  intros;eapply disj_star_elim.
  eauto.
  hoare forward. 
  Focus 2.
  hoare unfold.
  hoare forward.
  change (Int.eq ($ 0) ($ 0)) with true.
  simpl.
  (* intro; tryfalse. *)
  hoare_split_pure_all.
  inverts H7.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexacc_no_mutex_err_absinfer.
  go.
  intro.
  simpljoin.
  rewrite H8 in H6.
  tryfalse.
  hoare forward prim.
  sep cancel tcbdllflag.
  eauto.
  go.
  hoare forward.
  hoare forward .
  hoare unfold.
  false.
  clear -H5.
  elim H5; intros.
  int auto.
  int auto.
  hoare unfold.
  inverts H17.
  hoare forward.
  change ( Int.eq ($ 1) ($ 0)) with false.
  (* simpl; intro; tryfalse. *)
  hoare unfold.
  false.
  clear -H11 H12 H13.
  int auto.
  instantiate (1:=Afalse).
  hoare forward.
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)

  go.
  destruct (Int.eq i0 ($ OS_EVENT_TYPE_MUTEX)); simpl; intro; tryfalse.
  destruct (Int.eq i0 ($ OS_EVENT_TYPE_MUTEX)); simpl; intro; tryfalse.
  hoare unfold.
  assert (Int.eq i0 ($ OS_EVENT_TYPE_MUTEX) = false).
  clear -H12.
  pauto.


  destruct v'41;
    unfold AEventData;
    hoare_split_pure_all;
    inverts H29;
    unfolds in H6;
    destruct v'46;
    destruct e;
    try solve [inversion H6];
    simpljoin.
  assert (~exists x y w, EcbMod.get v'35 (v'26, Int.zero) = Some (absmutexsem x y, w))  by
          (  
        intro;
        assert (EcbMod.get v'35 (v'26, Int.zero) = Some (absmsgq l m, w)) by
            (
              eapply EcbMod.join_get_r; eauto;
              eapply EcbMod.join_get_l; eauto;
              apply EcbMod.get_a_sig_a;
              go);
        simpljoin;
        rewrite H29 in H6; inversion H6).



  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexacc_no_mutex_err_absinfer.
  go.
  auto.
  hoare forward prim.
  unfold AECBList.
  sep pauto.
  2:eauto.
  eapply evsllseg_merge.
  auto.
  simpl.
  sep lift 5%nat in H29.
  apply evsllseg_list_len_eq in H29.
  auto.
  do 2 rewrite l2.
  unfold1 evsllseg.
  sep pauto.
  unfold AEventNode.
  unfold AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel 2%nat 1%nat.
  sep cancel evsllseg.
  eauto.
  eauto.
  go.
  go.
  go.
  go.
  go.
  hoare forward.

  assert (~exists x y w, EcbMod.get v'35 (v'26, Int.zero) = Some (absmutexsem x y, w)).
  intro;
    assert (EcbMod.get v'35 (v'26, Int.zero) = Some (abssem i1, w)) by (
                                                                        eapply EcbMod.join_get_r; eauto;
                                                                        eapply EcbMod.join_get_l; eauto;
                                                                        apply EcbMod.get_a_sig_a;
                                                                        go);
    simpljoin.
  rewrite H29 in H6; inversion H6.



  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexacc_no_mutex_err_absinfer.
  go.
  auto.
  hoare forward prim.
  unfold AECBList.
  sep pauto.
  2:eauto.
  eapply evsllseg_merge.
  auto.
  simpl.
  sep lift 4%nat in H29.
  apply evsllseg_list_len_eq in H29.
  auto.

  do 2 rewrite l2.
  unfold1 evsllseg.
  sep pauto.
  unfold AEventNode.
  unfold AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel 2%nat 1%nat.
  sep cancel evsllseg.
  eauto.
  go.
  go.
  go.
  go.
  go.
  go.
  hoare forward.




  assert (~exists x y w, EcbMod.get v'35 (v'26, Int.zero) = Some (absmutexsem x y, w)).
  intro;
    assert (EcbMod.get v'35 (v'26, Int.zero) = Some (absmbox m0, w)) by (
                                                                         eapply EcbMod.join_get_r; eauto;
                                                                         eapply EcbMod.join_get_l; eauto;
                                                                         apply EcbMod.get_a_sig_a;
                                                                         go);
    simpljoin.
  rewrite H30 in H6; inversion H6.



  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexacc_no_mutex_err_absinfer.
  go.
  auto.
  hoare forward prim.
  unfold AECBList.
  sep pauto.
  2:eauto.
  eapply evsllseg_merge.
  auto.
  simpl.
  sep lift 4%nat in H30.
  apply evsllseg_list_len_eq in H30.
  auto.

  do 2 rewrite l2.
  unfold1 evsllseg.
  sep pauto.
  unfold AEventNode.
  unfold AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel 2%nat 1%nat.
  sep cancel evsllseg.
  eauto.
  eauto.
  go.
  go.
  go.
  go.
  go.
  hoare forward.
  false.
  inverts H28.

  clear -H27.
  int auto.
  hoare forward.

  hoare unfold.



  apply val_inj_eq in H12.
  subst i0.
  
  unfold AEventData.
  destruct v'41; hoare_split_pure_all. 
  inverts H15.
  inverts H12.
  inverts H12.
  inverts H15.
  inverts H17.
  clear H12.
  unfolds in H6.
  destruct v'46; destruct e; tryfalse.


  hoare forward.
  (* intro; tryfalse. *)
  go.
  change (Int.ltu ($ 8) Int.iwordsize ) with true.
  simpl.
  eauto.
  (* intro; tryfalse. *)

 (* skip. (* int32 = int 16 *)  *) 

  hoare unfold.
  hoare forward .
  go.

  Local Ltac if_invert := let HH := fresh in 
                    match goal with 
                      | |- (if ?e then true else false) = false => cut (e = false); [intro HH; rewrite HH; reflexivity| idtac]
                      | |- (if ?e then true else false) = true  => cut (e = true); [intro HH; rewrite HH; reflexivity| idtac]
                    end.
  if_invert.
  rewrite Z.leb_le.
  apply acpt_intlemma1.
  auto.
  clear.
  destruct (Int.ltu i6 (Int.modu (i1 >>ᵢ $ 8) ($ Byte.modulus))); simpl; intro; tryfalse. 
  go.
  
  if_invert.
  rewrite Z.leb_le.
  apply acpt_intlemma1.
  auto.
  destruct (Int.eq i6 (Int.modu (i1 >>ᵢ $ 8) ($ Byte.modulus))); simpl; intro; tryfalse. 
  destruct (Int.eq i6 (Int.modu (i1 >>ᵢ $ 8) ($ Byte.modulus))); destruct (Int.ltu i6 (Int.modu (i1 >>ᵢ $ 8) ($ Byte.modulus))); simpl; intro; tryfalse. 
  hoare unfold.
  


  apply or_true_ltrue_rtrue in H15.

  apply val_inj_or in H15.


  rewrite le65535shr8mod255self in H15.
  unfolds in H6.
  simpljoin.
  unfolds in H34.
  simpljoin.


  lets backup : H31.
  unfold1 TCBList_P in H31.
  simpljoin.
  unfolds in H44.
  destruct x4.
  destruct p.
  simpljoin.
  inverts H31.

  inverts H46.
  inverts H6.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexacc_prio_err_absinfer.
  go.


  joinsig_solver.
  unfold TcbJoin in H34.
  unfold TcbJoin in *.
  unfold join in *.
  simpl in H34.
  simpl in H29.
  eapply TcbMod.join_get_r.
  eauto.
  eapply TcbMod.join_get_l.
  eauto.
  eapply TcbMod.get_a_sig_a.
  go.

  inverts e.
  clear -H15.
  remember (Int.shru x ($ 8)).
  clear Heqi.
  destruct H15; intros.
  int auto.
  int auto.
  hoare forward prim.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold dllseg; fold dllseg.
  unfold node.
  sep pauto.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  instantiate (3:=
                 (v'22 ++
                       ((V$OS_EVENT_TYPE_MUTEX
                          :: Vint32 i :: Vint32 i1 :: v0 :: x3 :: v'42 :: nil, v'40) :: nil) ++
                       v'23)). 
  instantiate (2:=(v'24 ++ (DMutex (Vint32 i1) v0 :: nil) ++ v'25)).
  do 2 rewrite list_prop1.
  unfold AECBList.
  sep pauto.
  eapply evsllseg_merge.
  auto.
  simpl.
  sep lift 5%nat in H6.
  lets aaa : evsllseg_list_len_eq H6.
  auto.
  sep cancel 4%nat 1%nat.
  unfold1 evsllseg.
  unfold AEventNode.
  unfold AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel evsllseg.
  eauto.

  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  hoare forward.
  auto.

  hoare forward.
  hoare unfold.
  (**)  
  hoare forward.
  (* intro; tryfalse. *)
  go.
  (* intro; tryfalse. *)
  clear; destruct (Int.eq (i1&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ OS_MUTEX_AVAILABLE)); intro; tryfalse.
  instantiate (1:=Afalse).
  Focus 2.
  hoare forward.
  hoare unfold.

  assert ( (i1&ᵢ$ OS_MUTEX_KEEP_LOWER_8) <> ($ OS_MUTEX_AVAILABLE)).
  clear -H17.

  intro.
  assert (Int.eq  (i1&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ OS_MUTEX_AVAILABLE) = true).
  rewrite H; clear ; int auto.
  rewrite H0 in H17.
  simpl in H17;elim H17; intros; clear -H1.
  int auto.
  int auto.
  unfolds in H6.
  simpljoin.
  inverts H6.
  lets aaa: H48 H32.
  simpljoin.



  hoare abscsq.
  apply noabs_oslinv.
  eapply  mutexacc_no_available_absinfer.
  go.
  joinsig_solver.
  hoare forward prim.

  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  unfold dllseg; fold dllseg.
  unfold node.
  sep pauto.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.

  instantiate (3:=
                 (v'22 ++
                       ((V$OS_EVENT_TYPE_MUTEX
                          :: Vint32 i :: Vint32 x :: Vptr x0 :: x3 :: v'42 :: nil, v'40)
                          :: nil) ++ v'23)). 

  
  instantiate (2:= (v'24 ++ (DMutex (Vint32 x) (Vptr x0) :: nil) ++ v'25)).
  do 2 rewrite list_prop1.
  unfold AECBList.
  sep pauto.
  eapply evsllseg_merge.
  auto.
  simpl.
  sep lift 5%nat in H6.
  lets aaa : evsllseg_list_len_eq H6.
  auto.
  sep cancel 4%nat 1%nat.
  unfold1 evsllseg.
  unfold AEventNode.
  unfold AEventData.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  unfold1 evsllseg.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel evsllseg.
  eauto.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  hoare forward.


  (* succ *)  
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  (* intro; tryfalse. *)
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  assert (  Int.unsigned (i1&ᵢ$ OS_MUTEX_KEEP_UPPER_8) <= Int16.max_unsigned ).


  apply acpt_int_lemma0; auto.
  clear -H47 H48.
  omega.
  go.
  (* intro; tryfalse. *)
  hoare unfold.
  

  hoare forward.
  lets acopy : H10.

  unfolds in H6.
  simpljoin.
  apply acpt_intlemma2 in H17.
  inverts H6.
  lets aaa: H48 H17.
  simpljoin.
  unfolds in H10.
  simpljoin.
  
  hoare abscsq.
  apply noabs_oslinv.
  eapply  mutexacc_succ_absinfer.
  go.
  go.
  go.

  unfolds in H31.
  simpljoin.
  unfolds in H47.
  destruct x9; destruct p.
  simpljoin.
  inverts H51.
  inverts H10.
  assert (TcbMod.get v'36 (v'48, Int.zero) = Some (p, t, m)).
  eapply TcbMod.join_get_r.
  eauto.
  eapply TcbMod.join_get_l; eauto.
  exact H46.
  apply TcbMod.get_a_sig_a.
  go.
  unfold get in H6; simpl in H6.
  rewrite H10 in H6.
  inverts H6.

  rewrite  intlemma13 in H15.

  apply intlemma11; auto.
  change (Int.unsigned ($ Byte.modulus)) with 256.
  assert (Int.unsigned (Int.shru  x ($ 8)) <= 255).
  apply  acpt_intlemma10; auto.
  clear -H6; omega.

  apply intlemma11 in H15.
  rewrite intlemma13 in H15.
  Focus 2.
    change (Int.unsigned ($ Byte.modulus)) with 256.
    assert (Int.unsigned (Int.shru  x ($ 8)) <= 255).
    apply  acpt_intlemma10; auto.
    clear -H10; omega.


  lets backup_tcbp : H31.
  unfold1 TCBList_P in H31.
  simpljoin.
  unfold TCBNode_P in H47.
  inverts H31.
  destruct x9; destruct p.
  simpljoin.
  inverts H47; inverts H31; inverts H10.
  assert ( TcbMod.get v'36 (v'48, Int.zero) = Some (p, t, m)).
  eapply TcbMod.join_get_r.
  eauto.
  eapply TcbMod.join_get_l; eauto.
  exact H46.
  apply TcbMod.get_a_sig_a.
  go.
  unfold get in H6; simpl in H6.
  rewrite H6 in H10.
  inverts H10.
  lets backup_ecbp : H3.
  do 2 rewrite list_prop1 in H3.

  apply ecblist_p_decompose in H3.
  simpljoin.
  2:auto.

  unfold ECBList_P in H10; fold ECBList_P in H10.
  simpljoin.
  inverts H54.
  lets aaa: ecblist_p_eqh H5 H57.
  instantiate (1:=v'35).
  unfolds.
  unfold EcbMod.lookup.
  intros.
  go.
  unfolds.
  unfold EcbMod.lookup.
  unfold TcbJoin in H55.
  unfold join in H55.
  simpl in H55.
  unfolds in H57.
  intros.
  go.
  simpljoin.

  lets aaa: ecblist_p_eqh H3 H4.
  instantiate (1:=v'35).
  unfolds.
  unfold EcbMod.lookup.
  intros.
  go.
  unfolds.
  unfold EcbMod.lookup.
  intros.
  go.
  simpljoin.
  inverts H10.

  destruct x7.
(* ** ac:   Check mutex_no_owner_nil_wls. *)
  lets aa: mutex_no_owner_nil_wls H56.

  subst w0.
  lets aaa: mutex_no_owner_nil_wls' H34.
  subst w.


  hoare forward prim.
  instantiate (12:=(v'22 ++
                        ((V$OS_EVENT_TYPE_MUTEX
                           :: Vint32 i ::  Vint32 (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) p)
                           :: Vptr (v'48, Int.zero) :: x3 :: x10 :: nil, v'40)
                           :: nil) ++ v'23)).
  instantiate (11:=  (v'24 ++ (DMutex  (Vint32 (Int.or (x&ᵢ $ OS_MUTEX_KEEP_UPPER_8) p)) (Vptr (v'48, Int.zero)) :: nil) ++ v'25) ).
  unfold AECBList.
  unfold AOSTCBList.
  unfold tcbdllseg.
  sep pauto.
  sep cancel 5%nat 1%nat.
  unfold1 dllseg.
  unfold node.
  sep pauto.
  sep cancel 3%nat 1%nat.
  sep cancel 3%nat 1%nat.
  do 2 rewrite list_prop1.
  eapply evsllseg_merge.
  auto.
  sep lift 6%nat in H10.
  simpl.
  lets aaa:  evsllseg_list_len_eq H10.
  auto.
  
  sep cancel 5%nat 1%nat.
  unfold1 evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold node.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel evsllseg.
  eauto.

  go.
  go.
  go.
  go.
  go.

  assert ( Int.unsigned (Int.or (x&ᵢ$ OS_MUTEX_KEEP_UPPER_8) p) <= Int16.max_unsigned).

  apply acpt_intlemma6.
  lets aaa: tcbblk_prio_range H51.
  unfold V_OSTCBPrio in aaa.
  simpl in aaa.
  instantiate (1:=p) in aaa.
  lets bbb: aaa (eq_refl (Some (Vint32 p))).
  clear -bbb.
  omega.
  clear -H58 H59; omega.
  
  go.
  go.
  go.
  do 2 rewrite list_prop1.

  eapply ecblist_p_compose.
  2:exact H3.

  Focus 2.

  unfold1 ECBList_P.
  eexists; splits.
  eauto.


  apply R_ECB_ETbl_P_high_ecb_mutex_acpt_hold.
  auto.
  
  do 3 eexists; splits.
  go.
  3:go.
  instantiate (2:= (absmutexsem (Int.shru ( Int.or (x &ᵢ $ OS_MUTEX_KEEP_UPPER_8) p) ($ 8)) ( Some
                                                                                               (v'48, Int.zero, p)), nil)).




  eapply ecb_sig_join_sig'_set.
  eauto.



  eapply  RLH_ECBData_p_high_mbox_acpt_hold.
  
  lets aaa: tcbblk_prio_range H51.
  unfold V_OSTCBPrio in aaa.
  simpl in aaa.
  instantiate (1:=p) in aaa.
  lets bbb: aaa (eq_refl (Some (Vint32 p))).
  clear -bbb.
  omega.
  auto.

  eauto.
  rewrite acpt_intlemma4.
  2:auto.
  eapply EcbMod.join_set_r.
  auto.
  unfolds.
  eexists.
  go.
  lets aaa: tcbblk_prio_range H51.
  unfold V_OSTCBPrio in aaa.
  simpl in aaa.
  instantiate (1:=p) in aaa.
  lets bbb: aaa (eq_refl (Some (Vint32 p))).
  clear -bbb.
  omega.

  eauto.
  eauto.
  go.


  eapply mutex_acpt_rh_tcblist_ecblist_p_hold.
  go.
  go.
  go.
  go.
  hoare forward.

Qed.
