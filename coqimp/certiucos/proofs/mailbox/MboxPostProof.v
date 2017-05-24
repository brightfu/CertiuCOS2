(**************************  uc/OS-II  ******************************)
(*************************** OS_MBOX.C ******************************)
(*Proof of API Fucntion:  Int8u OSMboxPost(OS_EVENT* pevent, void* msg)*)
(***************************** Code: ********************************)
(***
 Int8u ·OSMboxPost·(⌞pevent @ OS_EVENT∗ ;  message @ Void∗⌟)··{
         ⌞ 
                 legal @ Int8u
         ⌟; 
1         If (pevent′ ==ₑ NULL)
          {
2                 RETURN  ′OS_ERR_PEVENT_NULL
          };ₛ
3         If (message′ ==ₑ NULL)
          {
4                RETURN  ′OS_ERR_POST_NULL_PTR
          };ₛ
5         ENTER_CRITICAL;ₛ
6         legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
7         If (legal′ ==ₑ ′0)
          {
8                EXIT_CRITICAL;ₛ
9                RETURN  ′MBOX_POST_P_NOT_LEGAL_ERR
          };ₛ
10        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MBOX)
          {
11               EXIT_CRITICAL;ₛ
12               RETURN  ′OS_ERR_EVENT_TYPE
          };ₛ
13        If (pevent′→OSEventGrp !=ₑ ′0)
          {
14               legal′ =ₑ ′OS_STAT_MBOX;ₛ 
15               OS_EventTaskRdy(­pevent′, message′, legal′ (* ′OS_STAT_MBOX *) ­);ₛ
16               EXIT_CRITICAL;ₛ
17               OS_Sched(­);ₛ
18               RETURN  ′OS_NO_ERR 
         };ₛ
19       If (pevent′→OSEventPtr !=ₑ  NULL)
         {
20               EXIT_CRITICAL;ₛ
21               RETURN  ′ MBOX_POST_FULL_ERR
         };ₛ
22       pevent′→OSEventPtr =ₑ  message′;ₛ
23       EXIT_CRITICAL;ₛ
24       RETURN  ′OS_NO_ERR 
 }· .
*)
Require Import ucos_include.
Require Import Mbox_common.
Require Import os_ucos_h.
Require Import mbox_absop_rules.
Require Import sep_lemmas_ext.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Lemma osmapvalle128:
  forall x y,
    nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 y ->
    Int.unsigned y <= 128.
Proof.
  intros.
  unfold OSMapVallist in H.
  assert (Int.unsigned x<8 \/ Int.unsigned x > 7).
  omega.
  elim H0; intros.
  mauto_dbg.
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  destruct H1; [rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega| ..].
  rewrite H1 in *; simpl in H; inverts H; ur_rewriter; omega.
  remember (Int.unsigned x).
(* ** ac:   SearchAbout (_ < _). *)
  assert ( 7 < z) by omega.
  apply Z2Nat.inj_lt in H2.
(* ** ac:   SearchAbout (nth_val' (Z.to_nat _) _ = _). *)
(* ** ac:   SearchAbout nat. *)
  remember (Z.to_nat z).
  change (Z.to_nat 7) with 7%nat in H2.
  destruct n; try omega.
  destruct n; try omega.
  destruct n; try omega.
  destruct n; try omega.
  destruct n; try omega.
  destruct n; try omega.
  destruct n; try omega.
  destruct n; try omega.
  induction n.
  simpl in H.
  inverts H.
  simpl in H.
  inverts H.
  omega.
  rewrite Heqz.
  int auto.
Qed.

(* ** ac: SearchAbout OSUnMapVallist. *)
(* ** ac: Search (Int.unsigned _ <= 7). *)

Lemma nth_val'_undef :
  forall ls x ,
    (x >= length ls)%nat ->
    nth_val' x ls =Vundef.
Proof.
  induction ls.
  intros.
  simpl in H.
  induction x.
  simpl.
  auto.
  simpl.
  auto.
  intro.
  induction x.
  intro.
  simpl in H.
  inversion H.
  simpl.
  intro.
  apply IHls.
  omega.
Qed.

Lemma OSUnMapVallistElementLe7:
  forall x y,
    nth_val' x OSUnMapVallist = Vint32 y ->
    Int.unsigned y <= 7.
Proof.
  intros.
  assert (x < 256 \/ x > 255)%nat.
  omega.
  destruct H0; intros.
  mauto_dbg.
  repeat (destruct H0;[subst x; unfold OSUnMapVallist in H; simpl in H; inverts H; ur_rewriter; omega| ..]).
  subst x; unfold OSUnMapVallist in H; simpl in H; inverts H; ur_rewriter; omega.
  assert ( 256 <= x)%nat by omega.
  clear H0.
  rewrite nth_val'_undef in H.
  inversion H.
  unfold OSUnMapVallist; simpl.
  omega.
Qed.
 

(**)
(*
Lemma mbox_post_part1: gen_mbox_post_part1.
Proof.
  unfolds.
  intros.
  unfold event_rdy_post1.
  pure intro.
  inverts H7.

  destruct v'84 as ((prio&st)&msg).
  assert ( w<>nil /\ GetHWait v'56 w (v'81,Int.zero) /\ TcbMod.get v'56 (v'81,Int.zero) = Some (prio,st,msg)).

  eapply post_exwt_succ_pre_mbox;eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  unfold Int.zero.
  rewrite H16 in Hx;auto.
  
  destructs H7.
  hoare_abscsq.
  eapply absinfer_mbox_post_exwt_succ.
  clear;can_change_aop_solver.

  eapply EcbMod.join_joinsig_get;eauto.
  auto.
  eauto.
  eauto.

  unfold AEventData.
  unfold_msg.
  pure intro.
  lets Hx:get_tcb_stat_mbox H58 H74 H53 H86 H39;eauto.

  apply le7_le7_range64; auto.
  unfolds in Hx;simpl in Hx;inverts Hx.
  hoare forward.
  unfold AOSMapTbl.
  unfold AOSUnMapTbl.
  unfold AOSTCBPrioTbl.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AECBList.
  sep pauto.
  sep cancel 10%nat 1%nat.
  sep cancel 9%nat 2%nat.
  eapply evsllseg_compose with
  (qptrl1:= v'22) (qptrl2:=v'23)
                  (l:= (V$OS_EVENT_TYPE_MBOX
                         ::  Vint32 (v'52&Int.not v'61)
                         :: Vint32 v'49
                         :: v'50 :: v'55 :: v'51 :: nil))
                  (msgqls1:=v'24) (msgqls2 := v'25) (tl:=(Vptr (v'53, Int.zero)))
                  (x:=
                     (update_nth_val (Z.to_nat (Int.unsigned v'57)) v'42
                                     (Vint32 (v'58&Int.not v'60))))
                  (msgq:=DMbox v'50);auto.
  unfolds; simpl; auto.
  unfold AEventNode.
  unfold AEventData.

  unfold_msg.
  sep pauto.
  subst.
  sep cancel 7%nat 1%nat.
  sep cancel 7%nat 1%nat.
  unfold AOSTCBList.
  sep normal.
  exists v'90 v'91.
  sep pauto.
  instantiate (2:=v'70).
  instantiate (2:=v'69).
  intros.
  sep pauto.
  eapply tcbdllseg_compose with (t1:=v'80) (tn1:=(Vptr (v'81, Int.zero)) ) (l1:=v'87)
                                           (l2:=  (v'82
                                                     :: v'80
                                                     :: Vnull
                                                     :: Vptr x
                                                     :: V$0
                                                     :: Vint32 (($ OS_STAT_MBOX)&Int.not ($ OS_STAT_MBOX))
                                                     :: Vint32 v'75
                                                     :: Vint32 v'76
                                                     :: Vint32 v'77
                                                     :: Vint32 v'78 :: Vint32 v'79 :: nil)::v'88).
  sep pauto.
  unfold tcbdllseg.
  unfold dllseg;fold dllseg.
  unfold node.
  sep pauto.
  split.
  auto.
  struct_type_match_solver.


  instantiate (1:=v'67).

  eapply TCBList_P_rtbl_add;eauto.

  assert (Vint32 ($ OS_STAT_MBOX & Int.not ($ OS_STAT_MBOX)) = V$0).
  clear -H55.
  unfold Int.eq in H55.
  destruct (zeq (Int.unsigned ($ OS_STAT_MBOX&Int.not ($ OS_STAT_MBOX)))
                (Int.unsigned ($ OS_STAT_RDY))).
  apply unsigned_inj in e.
  rewrite e.
  unfold OS_STAT_RDY.
  auto.
  inversion H55.


  rewrite H92.
  eapply TCBList_P_post_mbox with (v'49:=v'85) (v'59:=v'83) (v'44:=v'66);eauto.

  eapply  join_prop1 with  (v'49:=v'85); eauto.
  2:unfolds;simpl;auto.
  eapply rl_tbl_grp_p_set_hold;eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  unfold Int.zero.
  rewrite H16 in Hx;auto.

  auto.

  eapply array_type_vallist_match_int8u_update_hold;eauto.
  split;auto.
  struct_type_match_solver.

  split.
  eapply rl_tbl_grp_p_set_hold' with (v'12:=v'52) (v'69:=v'58) (v'36:=v'62);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  
  eapply idle_in_rtbl_hold';eauto.
  simpl.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  split.
  apply array_type_vallist_match_int8u_update_hold';auto.
  apply length_n_change;auto.
  eapply r_priotbl_p_set_hold;eauto.
  eapply rl_rtbl_priotbl_p_hold with (v'57:=v'64) (v'12:=v'52) (v'37:=v'63); eauto.
  eapply tcb_inrtbl_not_vhold; eauto.
  eapply le7_le7_range64; eauto.
  
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.


  idtac.
  eapply ecblist_p_post_exwt_hold_mbox with (v'12:=v'52) (v'39:=v'59) (v'69:=v'58) (v'38:=v'57);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  unfolds; split; auto.

  apply rh_curtcb_set_nct;auto.

  assert (exists xl,st = wait (os_stat_mbox (v'53, Int.zero)) xl).

  eapply rh_tcblist_ecblist_p_post_exwt_aux_mbox ;eauto.
  clear -H87.
  unfolds in H87;mytac;auto.
  destruct H96.
  subst.

  eapply rh_tcblist_ecblist_p_post_exwt_mbox ;eauto.
  clear -H87.
  unfolds in H87;mytac;auto.
  pauto.
  hoare forward.
  exact H89.
  pauto.
  hoare unfold.
  hoare forward.
  inverts H89;auto.
  Grab Existential Variables.
  exact Vundef.
  exact Vundef.
  exact v'53.
  exact (Int.repr 0).

Qed.


Lemma mbox_post_part2: gen_mbox_post_part2.
Proof.
  unfolds.
  intros.
  unfold event_rdy_post3.
  pure intro.
  inverts H7.

  destruct v'84 as ((prio&st)&msg).
  assert ( w<>nil /\ GetHWait v'56 w (v'81,Int.zero) /\ TcbMod.get v'56 (v'81,Int.zero) = Some (prio,st,msg)).
  Require Import OSQPostPure.
  eapply post_exwt_succ_pre_mbox;eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  unfold Int.zero.
  rewrite H16 in Hx;auto.
  
  destructs H7.
  hoare_abscsq.
  eapply absinfer_mbox_post_exwt_succ.

  unfold AEventData.
  clear;can_change_aop_solver.

  eapply EcbMod.join_joinsig_get;eauto.
  auto.
  eauto.
  eauto.




  unfold AEventData.
  unfold_msg.
  pure intro.
  lets Hx:get_tcb_stat_mbox H58 H74 H53 H86 H39;eauto.

  apply le7_le7_range64; auto.    
  unfolds in Hx;simpl in Hx;inverts Hx.
  hoare forward.
  unfold AOSMapTbl.
  unfold AOSUnMapTbl.
  unfold AOSTCBPrioTbl.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AECBList.
  sep pauto.
  sep cancel 10%nat 1%nat.
  sep cancel 9%nat 2%nat.
  eapply evsllseg_compose with
  (qptrl1:= v'22) (qptrl2:=v'23)
                  (l:= (V$OS_EVENT_TYPE_MBOX
                         ::  Vint32 (v'52&Int.not v'61)
                         :: Vint32 v'49
                         :: v'50 :: v'55 :: v'51 :: nil))
                  (msgqls1:=v'24) (msgqls2 := v'25) (tl:=(Vptr (v'53, Int.zero)))
                  (x:=
                     (update_nth_val (Z.to_nat (Int.unsigned v'57)) v'42
                                     (Vint32 (v'58&Int.not v'60))))
                  (msgq:=DMbox v'50);auto.
  unfolds; simpl; auto.
  unfold AEventNode.
  unfold AEventData.

  unfold_msg.
  sep pauto.
  subst.
  sep cancel 7%nat 1%nat.
  sep cancel 7%nat 1%nat.
  unfold AOSTCBList.
  sep normal.
  exists v'90 v'91.
  sep pauto.
  instantiate (4:=v'70).
  instantiate (3:=v'69).
  instantiate (2:=(v'87++(  (v'82
                               :: v'80
                               :: Vnull
                               :: Vptr x
                               :: V$0
                               ::  Vint32 ($ OS_STAT_MBOX&Int.not ($ OS_STAT_MBOX))
                               :: Vint32 v'75
                               :: Vint32 v'76
                               :: Vint32 v'77
                               :: Vint32 v'78 :: Vint32 v'79 :: nil)::v'88))).
  rewrite List.app_comm_cons.
  sep pauto.
  eapply tcbdllseg_compose with (t1:=v'80) (tn1:=(Vptr (v'81, Int.zero))).
  sep pauto.
  unfold tcbdllseg at 2.
  unfold dllseg;fold dllseg.
  unfold node.
  sep pauto.

  
  split;auto.
  simpl;splits;pauto.

  rewrite List.app_comm_cons.
  rewrite List.app_comm_cons in H85.
  
  apply TCBList_P_Split in H85;auto.
  
  mytac.
  apply TcbMod.join_comm in H60.

  eapply TCBList_P_post_msg_mbox with (v'48:=(v'69 :: v'87))  (v'44:=v'67) (v'7:=v'56) ;eauto.



  lets Hx: tcblist_p_sub_eq H63 H62 H92 H93.
  subst.
  auto.
  

  2:instantiate (1:=v'66).
  apply TcbMod.join_comm in H60.
  eapply TCBList_P_rtbl_add with (v'62:=v'89) (v'59:=v'83);eauto.
  eapply join_prop2 with (v'48:=v'85); eauto.
  eapply rl_tbl_grp_p_set_hold with (v'12:=v'52);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  unfold Int.zero.
  rewrite H16 in Hx;auto.
  auto.
  auto.
  eapply array_type_vallist_match_int8u_update_hold;eauto.

  
  split;auto.
  struct_type_match_solver.

  split.
  eapply rl_tbl_grp_p_set_hold' with (v'12:=v'52) (v'69:=v'58)  (v'36:=v'62);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  eapply idle_in_rtbl_hold';eauto.
  simpl.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  split.
  apply array_type_vallist_match_int8u_update_hold';auto.
  apply length_n_change;auto.
  eapply r_priotbl_p_set_hold;eauto. 
  eapply rl_rtbl_priotbl_p_hold with (v'57:=v'64) (v'12:=v'52) (v'37:=v'63);eauto.
  eapply tcb_inrtbl_not_vhold; eauto.
  eapply le7_le7_range64; eauto.

  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.

  eapply ecblist_p_post_exwt_hold_mbox with (v'12:=v'52) (v'39:=v'59) (v'69:=v'58) (v'38:=v'57);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  unfolds; split; auto.
  apply rh_curtcb_set_nct;auto.
  
  assert (exists xl,st = wait (os_stat_mbox (v'53, Int.zero)) xl).
  eapply rh_tcblist_ecblist_p_post_exwt_aux_mbox;eauto.
  clear -H87.
  unfolds in H87;mytac;auto.
  destruct H96.
  subst.
  eapply rh_tcblist_ecblist_p_post_exwt_mbox;eauto.
  clear -H87.
  unfolds in H87;mytac;auto.
  pauto.
  hoare forward.
  exact H89.
  pauto.
  hoare unfold.
  hoare forward.
  inverts H89;auto.
  Grab Existential Variables.
  exact (V$0).
  exact (V$0).
  eauto.
  exact ($0).
Qed.

Lemma mbox_post_part3: gen_mbox_post_part3.
Proof.
  unfolds.
  intros.
  unfold event_rdy_post5.
  pure intro.
  inverts H7.
  destruct v'79 as ((prio&st)&msg).
  apply TcbMod.join_comm in H60.
  lets Hx: tcbjoin_join_ex2_main H74 H60.
  destruct Hx as (tn&Hn1&Hn2).

  assert ( w<>nil /\ GetHWait v'56 w (v'80,Int.zero) /\ TcbMod.get v'56 (v'80,Int.zero) = Some (prio,st,msg)).

  eapply post_exwt_succ_pre_mbox;eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  unfold Int.zero.
  rewrite H16 in Hx;auto.
  
  destructs H7.
  hoare_abscsq.
  eapply absinfer_mbox_post_exwt_succ.

  unfold AEventData.
  clear;can_change_aop_solver.

  eapply EcbMod.join_joinsig_get;eauto.
  auto.
  eauto.
  eauto.

  unfold AEventData.
  unfold_msg.
  pure intro.
  lets Hx:get_tcb_stat_mbox H58 H72 H53 H76 H39;eauto.
  apply le7_le7_range64; auto.

  unfolds in Hx;simpl in Hx;inverts Hx.
  hoare forward.
  unfold AOSMapTbl.
  unfold AOSUnMapTbl.
  unfold AOSTCBPrioTbl.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AECBList.
  sep pauto.
  sep cancel 9%nat 1%nat.
  sep cancel 8%nat 2%nat.
  eapply evsllseg_compose with
  (qptrl1:= v'22) (qptrl2:=v'23)
                  (l:= (V$OS_EVENT_TYPE_MBOX
                         ::  Vint32 (v'52&Int.not v'61)
                         :: Vint32 v'49
                         :: v'50 :: v'55 :: v'51 :: nil))
                  (msgqls1:=v'24) (msgqls2 := v'25) (tl:=(Vptr (v'53, Int.zero)))
                  (x:=
                     (update_nth_val (Z.to_nat (Int.unsigned v'57)) v'42
                                     (Vint32 (v'58&Int.not v'60))))
                  (msgq:=DMbox v'50);auto.
  unfolds; simpl; auto.
  unfold AEventNode.
  unfold AEventData.

  unfold_msg.
  sep pauto.
  subst.
  
  sep cancel 6%nat 1%nat.
  sep cancel 6%nat 1%nat.
  unfold AOSTCBList.
  sep normal.
  exists v'81 v'82.
  sep pauto.
  sep cancel 3%nat 1%nat.
  instantiate (2:=v'85).
  instantiate (2:= (v'77
                      :: v'81
                      :: Vnull
                      :: Vptr x
                      :: V$0
                      :: Vint32 ($ OS_STAT_MBOX&Int.not ($ OS_STAT_MBOX))
                      :: Vint32 v'72
                      :: Vint32 v'73
                      :: Vint32 v'74
                      :: Vint32 v'75 :: Vint32 v'76 :: nil) ).
  
  unfold tcbdllseg.
  unfold dllseg;fold dllseg.
  unfold node.
  sep pauto.
  
  simpl;splits;pauto.

  instantiate(1:=  (TcbMod.set v'67 (v'80, Int.zero) (prio, rdy, Vptr x))).
  assert (TCBList_P (Vptr (v'80, Int.zero))
                    (nil++ (v'77
                              :: v'81
                              :: Vnull
                              :: Vptr x
                              :: V$0
                              :: Vint32 ($ OS_STAT_MBOX&Int.not ($ OS_STAT_MBOX))
                              :: Vint32 v'72
                              :: Vint32 v'73
                              :: Vint32 v'74
                              :: Vint32 v'75 :: Vint32 v'76 :: nil) :: v'85)
                    (update_nth_val (Z.to_nat (Int.unsigned v'57)) v'63
                                    (val_inj
                                       (or (nth_val' (Z.to_nat (Int.unsigned v'57)) v'63) (Vint32 v'60))))
                    (TcbMod.set v'67 (v'80, Int.zero) (prio, rdy, Vptr x))).
  eapply TCBList_P_post_mbox;eauto.
  instantiate (1:=TcbMod.emp).
  simpl.
  auto.
  apply TcbMod.join_emp;auto.
  simpl app in H87.
  exact H87.
  eapply TCBList_P_rtbl_add with (v'62:=tn) (v'59:=v'78) (v'49:=v'67) (v'37:=v'63) (v'43:=v'66);eauto.
  instantiate (1:=TcbMod.emp).
  apply TcbMod.join_emp;auto.
  apply TcbMod.join_comm in H60.
  eapply join_prop2 with (v'48:=v'67); eauto.
  eapply TcbMod.join_emp;auto.
  eapply rl_tbl_grp_p_set_hold with (v'12:=v'52);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  unfold Int.zero.
  rewrite H16 in Hx;auto.
  auto.
  auto.
  eapply array_type_vallist_match_int8u_update_hold;eauto.
  split; auto.
  struct_type_match_solver.
  
  split;auto.
  eapply rl_tbl_grp_p_set_hold' with (v'12:=v'52) (v'69:=v'58) (v'36:=v'62);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  
  eapply idle_in_rtbl_hold';eauto.
  simpl.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  split.
  apply array_type_vallist_match_int8u_update_hold';auto.
  apply length_n_change;auto.
  eapply r_priotbl_p_set_hold;eauto.
  eapply rl_rtbl_priotbl_p_hold with (v'57:=v'64) (v'12:=v'52) (v'37:=v'63);eauto.
  eapply tcb_inrtbl_not_vhold; eauto.
  eapply le7_le7_range64; eauto.

  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.

  eapply ecblist_p_post_exwt_hold_mbox with (v'12:=v'52) (v'39:=v'59) (v'69:=v'58) (v'38:=v'57);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  unfolds; split; auto.
  unfolds.
  exists prio rdy (Vptr x).
  apply TcbMod.set_a_get_a.
  apply TcbMod.beq_refl.
  assert (exists xl,st = wait (os_stat_mbox (v'53, Int.zero)) xl).
  eapply rh_tcblist_ecblist_p_post_exwt_aux_mbox;eauto.
  clear -H82.
  unfolds in H82;mytac;auto.
  destruct H91.
  subst.
  eapply rh_tcblist_ecblist_p_post_exwt_mbox;eauto.
  clear -H82.
  unfolds in H82;mytac;auto.
  pauto.
  hoare forward.
  exact H84.
  pauto.
  hoare unfold.
  hoare forward.
  inverts H84;auto.
  Grab Existential Variables.
  exact (V$0).
  exact (V$0).
  eauto.
  exact ($0).
Qed.

Lemma mbox_post_part4 :gen_mbox_post_part4.
Proof.
  unfolds.
  intros.
  unfold event_rdy_post1'.
  pure_intro.
  inverts H7.

  destruct v'84 as ((prio&st)&msg).
  assert ( w<>nil /\ GetHWait v'56 w (v'81,Int.zero) /\ TcbMod.get v'56 (v'81,Int.zero) = Some (prio,st,msg)).
  eapply post_exwt_succ_pre_mbox;eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  unfold Int.zero.
  rewrite H16 in Hx;auto.
  
  destructs H7.
  hoare_abscsq.
  eapply absinfer_mbox_post_exwt_succ.
  unfold AEventData.
  clear;can_change_aop_solver.
  simpl;auto.
  eapply EcbMod.join_joinsig_get;eauto.
  auto.
  eauto.
  eauto.
  unfold AEventData.
  unfold_msg.
  pure intro.

  
  lets Hx:get_tcb_stat_mbox H58 H74 H53 H86 H39;eauto.
  apply le7_le7_range64; auto.
  unfolds in Hx;simpl in Hx;inverts Hx.
  hoare forward.
  unfold AOSMapTbl.
  unfold AOSUnMapTbl.
  unfold AOSTCBPrioTbl.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AECBList.
  sep pauto.
  sep cancel Aptrmapsto.
  sep cancel Agvarenv'.
  eapply evsllseg_compose with
  (qptrl1:= v'22) (qptrl2:=v'23)
                  (l:= (V$OS_EVENT_TYPE_MBOX
                         ::  Vint32 (v'52)
                         :: Vint32 v'49
                         :: v'50 :: v'55 :: v'51 :: nil))
                  (msgqls1:=v'24) (msgqls2 := v'25) (tl:=(Vptr (v'53, Int.zero)))
                  (x:=
                     (update_nth_val (Z.to_nat (Int.unsigned v'57)) v'42
                                     (Vint32 (v'58&Int.not v'60))))
                  (msgq:=DMbox v'50);auto.


  unfold V_OSEventListPtr;simpl;auto.
  unfold AEventNode.
  unfold AEventData.
  unfold_msg.
  sep pauto.
  subst.
  sep cancel 8%nat 1%nat.
  sep cancel 7%nat 1%nat.
  unfold AOSTCBList.
  sep normal.
  exists v'90 v'91.
  sep pauto.
  instantiate (2:=v'70).
  instantiate (2:=v'69).
  sep pauto.
  eapply tcbdllseg_compose with (t1:=v'80) (tn1:=(Vptr (v'81, Int.zero)) ) (l1:=v'87)
                                           (l2:=  (v'82
                                                     :: v'80
                                                     :: Vnull
                                                     :: Vptr x
                                                     :: V$0
                                                     :: Vint32 (($ OS_STAT_MBOX)&Int.not ($ OS_STAT_MBOX))
                                                     :: Vint32 v'75
                                                     :: Vint32 v'76
                                                     :: Vint32 v'77
                                                     :: Vint32 v'78 :: Vint32 v'79 :: nil)::v'88).
  sep pauto.
  unfold tcbdllseg.
  unfold dllseg;fold dllseg.
  unfold node.
  sep pauto.
  split;auto.
  struct_type_match_solver.

  instantiate (1:=v'67).
  eapply TCBList_P_rtbl_add;eauto.
  eapply TCBList_P_post_mbox with (v'49:=v'85) (v'59:=v'83) (v'44:=v'66);eauto.

  eapply  join_prop1 with  (v'49:=v'85); eauto.
  2:unfolds;simpl;auto.
  eapply rl_tbl_grp_p_set_hold'';eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  unfold Int.zero.
  rewrite H16 in Hx;auto.
  auto.
  eapply array_type_vallist_match_int8u_update_hold;eauto.
  split;auto.
  struct_type_match_solver.

  split;auto.
  eapply rl_tbl_grp_p_set_hold' with (v'12:=v'52) (v'69:=v'58) (v'36:=v'62);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  
  eapply idle_in_rtbl_hold';eauto.
  simpl.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  split.
  apply array_type_vallist_match_int8u_update_hold';auto.
  apply length_n_change;auto.
  eapply r_priotbl_p_set_hold;eauto.
  eapply rl_rtbl_priotbl_p_hold with (v'57:=v'64) (v'12:=v'52) (v'37:=v'63);eauto.
  eapply tcb_inrtbl_not_vhold; eauto.
  eapply le7_le7_range64; eauto.

  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  eapply ecblist_p_post_exwt_hold_mbox with (v'12:=v'52) (v'39:=v'59) (v'69:=v'58) (v'38:=v'57);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  unfolds; split; auto.

  apply rh_curtcb_set_nct;auto.

  assert (exists xl,st = wait (os_stat_mbox (v'53, Int.zero)) xl).
  eapply rh_tcblist_ecblist_p_post_exwt_aux_mbox;eauto.
  clear -H87.
  unfolds in H87;mytac;auto.
  destruct H96.
  subst.
  eapply rh_tcblist_ecblist_p_post_exwt_mbox;eauto.
  clear -H87.
  unfolds in H87;mytac;auto.
  pauto.
  hoare forward.
  exact H89.
  pauto.
  hoare unfold.
  hoare forward.
  inverts H89;auto.
  Grab Existential Variables.
  exact (V$0).
  exact (V$0).
  eauto.
  exact ($0).
Qed.


Lemma mbox_post_part5: gen_mbox_post_part5.
Proof.
  unfolds.
  intros.
  unfold event_rdy_post3'.
  pure intro.
  inverts H7.

  destruct v'84 as ((prio&st)&msg).
  assert ( w<>nil /\ GetHWait v'56 w (v'81,Int.zero) /\ TcbMod.get v'56 (v'81,Int.zero) = Some (prio,st,msg)).
  
  eapply post_exwt_succ_pre_mbox;eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  unfold Int.zero.
  rewrite H16 in Hx;auto.
  
  destructs H7.
  hoare_abscsq.
  eapply absinfer_mbox_post_exwt_succ.
  
  unfold AEventData.
  clear;can_change_aop_solver.
  
  eapply EcbMod.join_joinsig_get;eauto.
  auto.
  eauto.
  eauto.




  unfold AEventData.
  unfold_msg.
  pure intro.
  lets Hx:get_tcb_stat_mbox H58 H74 H53 H86 H39;eauto.
  apply le7_le7_range64; auto.
  unfolds in Hx;simpl in Hx;inverts Hx.
  hoare forward.
  unfold AOSMapTbl.
  unfold AOSUnMapTbl.
  unfold AOSTCBPrioTbl.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AECBList.
  sep pauto.
  sep cancel Aptrmapsto.
  sep cancel Agvarenv'.
  eapply evsllseg_compose with
  (qptrl1:= v'22) (qptrl2:=v'23)
                  (l:= (V$OS_EVENT_TYPE_MBOX
                         :: Vint32 (v'52)
                         :: Vint32 v'49
                         :: v'50 :: v'55 :: v'51 :: nil))
                  (msgqls1:=v'24) (msgqls2 := v'25) (tl:=(Vptr (v'53, Int.zero)))
                  (x:=
                     (update_nth_val (Z.to_nat (Int.unsigned v'57)) v'42
                                     (Vint32 (v'58&Int.not v'60))))
                  (msgq:=DMbox v'50);auto.
  unfolds; simpl; auto.
  unfold AEventNode.
  unfold AEventData.
  
  unfold_msg.
  sep pauto.
  subst.
  sep cancel 8%nat 1%nat.
  sep cancel 7%nat 1%nat.
  unfold AOSTCBList.
  sep normal.
  exists v'90 v'91.
  sep pauto.
  instantiate (4:=v'70).
  instantiate (3:=v'69).
  instantiate (2:=(v'87++(  (v'82
                               :: v'80
                               :: Vnull
                               :: Vptr x
                               :: V$0
                               ::  Vint32 ($ OS_STAT_MBOX&Int.not ($ OS_STAT_MBOX))
                               :: Vint32 v'75
                               :: Vint32 v'76
                               :: Vint32 v'77
                               :: Vint32 v'78 :: Vint32 v'79 :: nil)::v'88))).
  rewrite List.app_comm_cons.
  sep pauto.
  eapply tcbdllseg_compose with (t1:=v'80) (tn1:=(Vptr (v'81, Int.zero))).
  sep pauto.
  unfold tcbdllseg at 2.
  unfold dllseg;fold dllseg.
  unfold node.
  sep pauto.
  
  split;auto.
  struct_type_match_solver.
  
  rewrite List.app_comm_cons.
  rewrite List.app_comm_cons in H85.
  
  apply TCBList_P_Split in H85;auto.
  
  mytac.
  apply TcbMod.join_comm in H60.

  eapply TCBList_P_post_msg_mbox with (v'48:=(v'69 :: v'87))  (v'44:=v'67) (v'7:=v'56) ;eauto.

  lets Hx: tcblist_p_sub_eq H63 H62 H92 H93.
  subst.
  auto.
  
  instantiate (1:=v'66).
  apply TcbMod.join_comm in H60.
  eapply TCBList_P_rtbl_add with (v'62:=v'89) (v'59:=v'83);eauto.
  eapply join_prop2 with (v'48:=v'85); eauto.

  eapply rl_tbl_grp_p_set_hold'' with (v'12:=v'52);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  unfold Int.zero.
  rewrite H16 in Hx;auto.
  auto.
  auto.
  eapply array_type_vallist_match_int8u_update_hold;eauto.

  split;auto.
  struct_type_match_solver.

  split.
  eapply rl_tbl_grp_p_set_hold' with (v'12:=v'52) (v'69:=v'58)  (v'36:=v'62);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  eapply idle_in_rtbl_hold';eauto.
  simpl.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  split.
  apply array_type_vallist_match_int8u_update_hold';auto.
  apply length_n_change;auto.
  eapply r_priotbl_p_set_hold;eauto. 
  eapply rl_rtbl_priotbl_p_hold with (v'57:=v'64) (v'12:=v'52) (v'37:=v'63);eauto.
  eapply tcb_inrtbl_not_vhold; eauto.
  eapply le7_le7_range64; eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.

  eapply ecblist_p_post_exwt_hold_mbox with (v'12:=v'52) (v'39:=v'59) (v'69:=v'58) (v'38:=v'57);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  unfolds; split; auto.
  apply rh_curtcb_set_nct;auto.
  
  assert (exists xl,st = wait (os_stat_mbox (v'53, Int.zero)) xl).
  eapply rh_tcblist_ecblist_p_post_exwt_aux_mbox;eauto.
  clear -H87.
  unfolds in H87;mytac;auto.
  destruct H96.
  subst.
  eapply rh_tcblist_ecblist_p_post_exwt_mbox;eauto.
  clear -H87.
  unfolds in H87;mytac;auto.
  pauto.
  hoare forward.
  exact H89.
  pauto.
  hoare unfold.
  hoare forward.

  inverts H89;auto.
  Grab Existential Variables.
  exact (V$0).
  exact (V$0).
  eauto.
  exact ($0).
Qed.

Lemma mbox_post_part6: gen_mbox_post_part6.
Proof.
  unfolds.
  intros.
  unfold event_rdy_post5'.
  pure intro.
  inverts H7.
  destruct v'79 as ((prio&st)&msg).
  apply TcbMod.join_comm in H60.
  lets Hx: tcbjoin_join_ex2_main H74 H60.
  destruct Hx as (tn&Hn1&Hn2).

  assert ( w<>nil /\ GetHWait v'56 w (v'80,Int.zero) /\ TcbMod.get v'56 (v'80,Int.zero) = Some (prio,st,msg)).

  eapply post_exwt_succ_pre_mbox;eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  unfold Int.zero.
  rewrite H16 in Hx;auto.
  
  destructs H7.
  hoare_abscsq.
  eapply absinfer_mbox_post_exwt_succ.

  unfold AEventData.
  clear;can_change_aop_solver.

  eapply EcbMod.join_joinsig_get;eauto.
  auto.
  eauto.
  eauto.

  unfold AEventData.
  unfold_msg.
  pure intro.
  lets Hx:get_tcb_stat_mbox H58 H72 H53 H76 H39;eauto.
  apply le7_le7_range64; auto.
  unfolds in Hx;simpl in Hx;inverts Hx.
  hoare forward.
  unfold AOSMapTbl.
  unfold AOSUnMapTbl.
  unfold AOSTCBPrioTbl.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AECBList.
  sep pauto.
  sep cancel Aptrmapsto.
  sep cancel Agvarenv'.
  eapply evsllseg_compose with
  (qptrl1:= v'22) (qptrl2:=v'23)
                  (l:= (V$OS_EVENT_TYPE_MBOX
                         ::  Vint32 (v'52)
                         :: Vint32 v'49
                         :: v'50 :: v'55 :: v'51 :: nil))
                  (msgqls1:=v'24) (msgqls2 := v'25) (tl:=(Vptr (v'53, Int.zero)))
                  (x:=
                     (update_nth_val (Z.to_nat (Int.unsigned v'57)) v'42
                                     (Vint32 (v'58&Int.not v'60))))
                  (msgq:=DMbox v'50);auto.
  unfolds; simpl; auto.
  unfold AEventNode.
  unfold AEventData.

  unfold_msg.
  sep pauto.
  subst.
  
  sep cancel 7%nat 1%nat.
  sep cancel 6%nat 1%nat.
  unfold AOSTCBList.
  sep normal.
  exists v'81 v'82.
  sep pauto.
  sep cancel 3%nat 1%nat.
  instantiate (2:=v'85).
  instantiate (2:= (v'77
                      :: v'81
                      :: Vnull
                      :: Vptr x
                      :: V$0
                      :: Vint32 ($ OS_STAT_MBOX&Int.not ($ OS_STAT_MBOX))
                      :: Vint32 v'72
                      :: Vint32 v'73
                      :: Vint32 v'74
                      :: Vint32 v'75 :: Vint32 v'76 :: nil) ).
  
  unfold tcbdllseg.
  unfold dllseg;fold dllseg.
  unfold node.
  sep pauto.
  
  simpl;splits;pauto.

  instantiate(1:=  (TcbMod.set v'67 (v'80, Int.zero) (prio, rdy, Vptr x))).
  assert (TCBList_P (Vptr (v'80, Int.zero))
                    (nil++ (v'77
                              :: v'81
                              :: Vnull
                              :: Vptr x
                              :: V$0
                              :: Vint32 ($ OS_STAT_MBOX&Int.not ($ OS_STAT_MBOX))
                              :: Vint32 v'72
                              :: Vint32 v'73
                              :: Vint32 v'74
                              :: Vint32 v'75 :: Vint32 v'76 :: nil) :: v'85)
                    (update_nth_val (Z.to_nat (Int.unsigned v'57)) v'63
                                    (val_inj
                                       (or (nth_val' (Z.to_nat (Int.unsigned v'57)) v'63) (Vint32 v'60))))
                    (TcbMod.set v'67 (v'80, Int.zero) (prio, rdy, Vptr x))).
  eapply TCBList_P_post_mbox;eauto.
  instantiate (1:=TcbMod.emp).
  simpl.
  auto.
  apply TcbMod.join_emp;auto.
  simpl app in H87.
  exact H87.
  eapply TCBList_P_rtbl_add with (v'62:=tn) (v'59:=v'78) (v'49:=v'67) (v'37:=v'63) (v'43:=v'66);eauto.
  instantiate (1:=TcbMod.emp).
  apply TcbMod.join_emp;auto.
  apply TcbMod.join_comm in H60.
  eapply join_prop2 with (v'48:=v'67); eauto.
  eapply TcbMod.join_emp;auto.
  eapply rl_tbl_grp_p_set_hold'' with (v'12:=v'52);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  unfold Int.zero.
  rewrite H16 in Hx;auto.
  auto.
  auto.
  eapply array_type_vallist_match_int8u_update_hold;eauto.
  split; auto.

  struct_type_match_solver.

  
  split;auto.
  eapply rl_tbl_grp_p_set_hold' with (v'12:=v'52) (v'69:=v'58) (v'36:=v'62);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  
  eapply idle_in_rtbl_hold';eauto.
  simpl.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  split.
  apply array_type_vallist_match_int8u_update_hold';auto.
  apply length_n_change;auto.
  eapply r_priotbl_p_set_hold;eauto.
  eapply rl_rtbl_priotbl_p_hold with (v'57:=v'64) (v'12:=v'52) (v'37:=v'63);eauto.
  eapply tcb_inrtbl_not_vhold; eauto.
  eapply le7_le7_range64; eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.

  eapply ecblist_p_post_exwt_hold_mbox with (v'12:=v'52) (v'39:=v'59) (v'69:=v'58) (v'38:=v'57);eauto.
  lets Hx: Int.eq_spec v'52 ($ 0).
  rewrite H16 in Hx.
  unfold Int.zero.
  auto.
  unfolds; split; auto.
  unfolds.
  exists prio rdy (Vptr x).
  apply TcbMod.set_a_get_a.
  apply TcbMod.beq_refl.
  assert (exists xl,st = wait (os_stat_mbox (v'53, Int.zero)) xl).
  eapply rh_tcblist_ecblist_p_post_exwt_aux_mbox;eauto.
  clear -H82.
  unfolds in H82;mytac;auto.
  destruct H91.
  subst.
  eapply rh_tcblist_ecblist_p_post_exwt_mbox;eauto.
  clear -H82.
  unfolds in H82;mytac;auto.
  pauto.
  hoare forward.
  exact H84.
  pauto.
  hoare unfold.
  hoare forward.
  inverts H84;auto.
  Grab Existential Variables.
  exact (V$0).
  exact (V$0).
  eauto.
  exact ($0).
Qed.

Lemma mbox_post_part0 : gen_mbox_post_part0.
Proof.
  unfolds.
  intros.
  hoare unfold.
  
  hoare forward.

  instantiate (3:= (DMbox m0)).
  unfold_msg.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  unfold AEventData.
  sep pauto.
  eauto.
  
  unfolds; simpl; auto.
  pauto.
  auto.
  split;[auto| struct_type_match_solver].

  1:split; [unfolds;simpl;auto| idtac].
  1:lets Hx: Int.eq_spec i Int.zero.
  1:unfold Int.zero in Hx.
  1:unfold Int.zero.
  1:rewrite H16 in Hx;auto.

  1:simpl; auto.
  1:auto.
  1:pauto.
  
  hoare unfold.
  unfold OS_EventTaskRdyPost_fold'.
  eapply backward_rule1.
  intros.
  eapply disj_star_elim'' in H7.
  exact H7.

  apply disj_rule.
  {
    eapply mbox_post_part1; eauto.
  }
  apply disj_rule.
  {
    unfold event_rdy_post2.
    pure intro.
    inverts H7.
    lets Hx:get_tcb_stat_mbox H58 H74 H53 H86 H39;eauto.
    apply le7_le7_range64; auto.
    unfolds in Hx;simpl in Hx;inverts Hx.

    rewrite statmbox_and_not_statmbox_eq_rdy in H55;tryfalse.
  }
  apply disj_rule.
  {
    eapply mbox_post_part2; eauto.
  }
  apply disj_rule.
  {
    unfold event_rdy_post4.
    pure intro.
    inverts H7.
    lets Hx:get_tcb_stat_mbox H58 H74 H53 H86 H39;eauto.
    apply le7_le7_range64; auto.
    unfolds in Hx;simpl in Hx;inverts Hx.
    rewrite statmbox_and_not_statmbox_eq_rdy in H55;tryfalse.
  }
  apply disj_rule.
  {
    eapply mbox_post_part3; eauto.
  }
  apply disj_rule.
  {
    unfold event_rdy_post6.
    pure intro.
    inverts H7.
    apply TcbMod.join_comm in H60.
    lets Hx: tcbjoin_join_ex2_main H74 H60.
    destruct Hx as (tn&Hn1&Hn2).
    lets Hx:get_tcb_stat_mbox H58 H72 H53 H76 H39;eauto.
    apply le7_le7_range64; auto.
    unfolds in Hx;simpl in Hx;inverts Hx.
    rewrite statmbox_and_not_statmbox_eq_rdy in H55;tryfalse.
  }
  apply disj_rule.
  {
    eapply mbox_post_part4; eauto.
  }
  apply disj_rule.
  {
    unfold event_rdy_post2'.
    pure intro.
    inverts H7.
    lets Hx:get_tcb_stat_mbox H58 H74 H53 H86 H39;eauto.
    apply le7_le7_range64; auto.
    unfolds in Hx;simpl in Hx;inverts Hx.

    rewrite statmbox_and_not_statmbox_eq_rdy in H55;tryfalse.
  }
  apply disj_rule.
  {
    eapply mbox_post_part5; eauto.
  }
  apply disj_rule.
  {
    unfold event_rdy_post4'.
    pure intro.
    inverts H7.
    lets Hx:get_tcb_stat_mbox H58 H74 H53 H86 H39;eauto.
    apply le7_le7_range64; auto.
    unfolds in Hx;simpl in Hx;inverts Hx.
    rewrite statmbox_and_not_statmbox_eq_rdy in H55;tryfalse.
  }
  apply disj_rule.
  {
    eapply mbox_post_part6; eauto.
  }
  {
    unfold event_rdy_post6'.
    pure intro.
    inverts H7.
    apply TcbMod.join_comm in H60.
    lets Hx: tcbjoin_join_ex2_main H74 H60.
    destruct Hx as (tn&Hn1&Hn2).
    lets Hx:get_tcb_stat_mbox H58 H72 H53 H76 H39;eauto.
    apply le7_le7_range64; auto.
    unfolds in Hx;simpl in Hx;inverts Hx.
    rewrite statmbox_and_not_statmbox_eq_rdy in H55;tryfalse.
  }

Qed.
*)

(* end part *)


Lemma MboxPostProof:
    forall  vl p r tid, 
      Some p =
      BuildPreA' os_api OSMboxPost mbox_postapi vl OSLInv tid init_lg ->
      Some r =
      BuildRetA' os_api OSMboxPost mbox_postapi vl OSLInv tid init_lg ->
      exists t d1 d2 s,
        os_api OSMboxPost = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio ,OSLInv, I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  intros.
  init_spec.
  destruct x0;
    unfolds in H2; simpljoin; try solve[ destruct H2; simpljoin; tryfalse].
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply  absinfer_mbox_post_null_return.
  clear;can_change_aop_solver.
  unfolds.
  unfold type_val_match.
  pauto.
  hoare forward.
  hoare forward.
  hoare unfold.
  destruct H; tryfalse.

  hoare unfold.

  hoare forward.
  destruct a.
  simpl.
  intro; tryfalse.
  hoare unfold.
  destruct a.
  simpl in H.
  tryfalse.
  instantiate (1:=Afalse).
  hoare forward.
  hoare unfold.
  
  destruct x; unfolds in H1; destruct H1; intros; simpljoin; tryfalse.
  
  hoare forward.
  hoare unfold.
  (* intro; tryfalse. *)
  hoare abscsq.
    apply noabs_oslinv.

  eapply absinfer_mbox_post_msg_null_return.
  clear;can_change_aop_solver.
  hoare forward.
  
  hoare forward.
  hoare unfold.
  destruct H0;intros; tryfalse.

  hoare unfold.
  hoare forward.
  destruct x.
  simpl.
  intro; tryfalse.
  hoare unfold.
  destruct x.
  simpl in H0.
  tryfalse.
  instantiate (1:=Afalse).
  hoare forward.

  hoare unfold.

  hoare forward prim.
  pauto.
  hoare unfold.
  hoare forward .
  sep cancel tcbdllflag.
  sep cancel Aop.
  sep cancel AECBList.
  sep cancel AOSTCBList.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBPrioTbl.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  eauto.
  
  simpl; eauto.
  
  go.
  eapply retpost_osev .
  Require Import linv_solver.

  linv_solver.
  linv_solver.
  
  hoare unfold.
  eapply backward_rule1.
  intros;eapply disj_star_elim.
  eauto.
  hoare forward.
  
  Focus 2.
  (* legal = 0 *)
  hoare unfold.
  hoare forward.
  change (Int.eq ($ 0) ($ 0)) with true.
  (* simpl; intro; tryfalse. *)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  inverts H8.
  eapply absinfer_mbox_post_p_not_legal_return.
  clear;can_change_aop_solver.
  auto.
  hoare forward prim.
  eauto.
  pauto.
  hoare forward.
  hoare forward.
  hoare unfold.
  false.
  destruct H6; intros.
  int auto.
  int auto.

  (* legal = 1, succ path *)
  hoare unfold.
  hoare forward.
  change (Int.eq ($ 1) ($ 0)) with false.
  (* simpl; intro; tryfalse. *)
  hoare unfold.
  false.
  int auto.
  instantiate (1:=Afalse).

  hoare forward.
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  destruct (Int.eq i0 ($ OS_EVENT_TYPE_MBOX)); intro; tryfalse.
  destruct (Int.eq i0 ($ OS_EVENT_TYPE_MBOX)); intro; tryfalse.
  hoare unfold.
  eapply backward_rule1.
  intros.
  sep lift 8%nat in H29.
  remember (Int.eq i0 ($ OS_EVENT_TYPE_MBOX)) as X.
  destruct X;simpl in H13;auto;tryfalse.
  unfold Int.notbool in H13;simpl in H13.
  rewrite eq_one_zero in H13.
  tryfalse.

  eapply eventtype_neq_mbox' in H29;eauto.
  hoare_split_pure_all.
  hoare abscsq.
    apply noabs_oslinv.

  inverts H18.
  eapply absinfer_mbox_post_wrong_type_return;auto.
  clear;can_change_aop_solver.
  hoare forward prim.
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose.
  instantiate (2:= (Vint32 i0 :: Vint32 i :: Vint32 i1 :: x3 :: x4 :: v'41 :: nil) ).
  unfolds; simpl; eauto.
  auto.
  auto.
  sep cancel 4%nat 2%nat.
  sep cancel 4%nat 2%nat.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  sep pauto.
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel AEventData.
  eauto.
  auto.
  eauto.
  unfolds ; simpl; auto.
  
  pauto.
  splits; [auto| struct_type_match_solver].
  auto.
  pauto.
  
  hoare forward.
  hoare forward.

  hoare unfold.
  (* succ path *)
  apply val_inj_eq in H13.
  subst i0.
  unfold AEventData.
  destruct v'40; hoare_split_pure_all; tryfalse.
  unfolds in H7.
  destruct v'45; destruct e; tryfalse.
  elim H7;intros; subst.

  unfolds in H16; simpl in H16.
  inverts H16.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  destruct (Int.eq i ($ 0)); intro; tryfalse.
  destruct (Int.eq i ($ 0)); intro; tryfalse.
  hoare unfold.

  instantiate (1:=Afalse).
  
  Focus 2.
  hoare forward.
  hoare unfold.
  apply val_inj_eq in H16.
  subst i.
  idtac.
  unfolds in H29.

  hoare forward.
  (* intro; tryfalse. *)
  (*********)

  struct_type_match_solver.
  clear -H27.
  pauto.
  clear -H27.
  pauto.
  
  hoare unfold.
  destruct m0; try solve [false; clear -H7 H13 H16;simpl in H7, H13, H16; tryfalse; int auto].

  hoare abscsq.
  apply noabs_oslinv.

  inverts H18.
  eapply absinfer_mbox_post_full_return.
  clear;can_change_aop_solver.

  2: eauto.
  eapply EcbMod.join_get_get_r.
  eauto.
  eapply EcbMod.join_get_get_l; eauto.
  eapply EcbMod.get_a_sig_a.
  
  apply CltEnvMod.beq_refl.
  
  hoare forward prim.
  unfold AECBList.
  sep pauto.

  2: exact H4.
  rewrite list_prop1.
  rewrite list_prop1.
  eapply evsllseg_merge; eauto.
  simpl.
  lets Heq : ecblistp_length_eq H4 H15.
  auto.
  sep cancel 3%nat 1%nat.
  unfold evsllseg; fold evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold node, AOSEventTbl.
  sep pauto.
  eauto.
  unfolds; simpl; auto.
  split;[auto| struct_type_match_solver].
  pauto.
  hoare forward.

  hoare forward.
  hoare unfold.
  hoare forward.


  apply val_inj_lemma in H7.
  subst m0.
  unfold AOSTCBPrioTbl.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  inverts H18.
  eapply  absinfer_mbox_post_put_mail_return.
  
  clear;can_change_aop_solver.

  unfolds in H8.
  simpljoin.
  (* ************* *)

  assert (w = nil).
  eapply post_exwt_succ_pre_mbox'; eauto.
  unfolds.
  splits; auto.

  subst w.
  eapply EcbMod.join_get_get_r.
  eauto.
  eapply EcbMod.join_get_get_l; eauto.
  eapply EcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.

  hoare forward prim.
  unfold AECBList.
  unfold AOSTCBPrioTbl.
  sep pauto.
  sep cancel Aptrmapsto.
  sep cancel Agvarenv'.
  instantiate (2:= (v'23 ++ (DMbox (Vptr x) :: nil) ++ v'24)).
  instantiate (2:=  (v'21 ++
                          ((V$OS_EVENT_TYPE_MBOX
                             :: V$0 :: Vint32 i1 :: (Vptr x) :: x4 :: v'41 :: nil, v'39) :: nil) ++
                          v'22)).
  rewrite list_prop1.
  rewrite list_prop1.
  eapply evsllseg_merge; eauto.
  simpl.
  lets Heq : ecblistp_length_eq H4 H15.
  auto.
  sep cancel 4%nat 1%nat.
  unfold evsllseg; fold evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold node, AOSEventTbl.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel evsllseg.
  eauto.
  unfolds; simpl; auto.
  eauto.
  unfolds; simpl; auto.
  auto.

  split;[auto| struct_type_match_solver].
  (* unfolds; simpl;right; eauto. (* TO DELETE *)*)
  go.
  go.

  rewrite list_prop1.
  rewrite list_prop1.
  eapply ecblist_p_compose; eauto.
  eapply EcbMod.join_set_r.
  eauto.
  clear -H9.
  unfolds.
  eexists.
  eapply EcbMod.join_get_l.
  eauto.
  eapply EcbMod.get_a_sig_a.
  EcbMod.beq_simpl_tac.

  unfold ECBList_P; fold ECBList_P.
  eexists; split; eauto.
  splits.
  auto.
  do 3 eexists; splits.
  unfolds; simpl; eauto.
  unfolds.
  instantiate (1:=v'43). 
  instantiate (1:= (absmbox (Vptr x), nil)).
  erewrite <- EcbMod.set_sig.
  eapply EcbMod.join_set_l.
  eauto.
  eexists.
  eapply EcbMod.get_a_sig_a.
  EcbMod.beq_simpl_tac.
  unfolds; split; auto.
  unfolds.
  split; intro; auto.
  clear -H34; tryfalse.
  auto.

  assert (w = nil).
  eapply post_exwt_succ_pre_mbox'; eauto.
  subst w.


  eapply mbox_rh_tcblist_ecblist_p_hold; eauto.
  eapply EcbMod.join_get_r; eauto.
  eapply EcbMod.join_get_l; eauto.
  eapply EcbMod.get_a_sig_a; eauto.
  apply CltEnvMod.beq_refl; auto.

  pauto.
  hoare forward.

  hoare unfold.

  apply  notint_neq_zero_eq in H16.
  clear H21 H30.
  hoare unfold.
  hoare forward.
  inverts H18.


  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold AEventData.
  unfold node, AOSEventTbl.
  unfold AOSTCBList, AOSTCBPrioTbl.
  hoare unfold.
  hoare forward.
  sep cancel Aop.
  sep cancel Aie.
  sep cancel Acs.
  sep cancel Ais.
  sep cancel Aisr.
  sep pauto.

  sep cancel AOSRdyTblGrp.
  sep pauto.
  unfold AEventNode.
  
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold AEventData.
  unfold node, AOSEventTbl.
  instantiate (16 := (DMbox m0)).
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep lifts (3::5::nil)%nat in H34.
  eapply inv_prop.tcbdllseg_compose in H34.
  sep cancel tcbdllseg.
  eauto.

  go.
  go.
  go.
  go.
  exact H17.

  go.
  go.
  go.
  clear -H16. intro; subst; int auto.
  go.
  go.
  go.
  go.
  (* Require Import OSTimeDlyPure. *)
  Require Import OSQPostPure.

  eapply TCBList_P_Combine; eauto.
  eapply tcbdllseg_get_last_tcb_ptr.
  instantiate (4:=s).
  sep cancel 3%nat 1%nat.
  

  eauto.
  auto.
  eauto.
  eauto.
  eapply tcbdllseg_combine_ptr_in_tcblist.
  instantiate (7:=s).
  sep cancel 3%nat 1%nat.
  sep cancel 4%nat 1%nat.
  eauto.
  intro; tryfalse.
  go. 
  
  linv_solver.
  linv_solver.

  hoare unfold.
  inverts H64.
(* ** ac:   Check post_exwt_succ_pre_mbox. *)
(* ** ac:   Print TCBList_P. *)

  (* destruct v'84 as ((prio&st)&msg). *)
  assert (exists p s m a, TcbJoin (v'89, Int.zero) (p, s, m) a v'48) as some_hyp.
(* ** ac:   SearchAbout tcblist_get. *)
(* ** ac:   Print R_PrioTbl_P. *)
  unfolds in H61.
  simpljoin.
  lets bb: H35 H69.
(* ** ac:   SearchAbout nth_val. *)
  2:apply oscore_common.nth_val'2nth_val'; exact H36.

  apply OSUnMapVallistElementLe7 in H42.
  apply OSUnMapVallistElementLe7 in H44.
  clear -H42 H44; mauto.
  simpljoin.
  do 3 eexists.
(* ** ac:   SearchAbout join. *)
  apply get_join.
  exact H40.
  destruct some_hyp as ( prio & stat & msg & someothertcbmod & some_hyp).


  
  (* apply tcblist_get_split in H37.
   * simpljoin.
   * rewrite H35 in H63.
   * SearchAbout TCBList_P. *)


  assert ( exists prio st msg, prio = (v'72<<ᵢ$ 3)+ᵢv'71/\ st<> rdy /\ w<>nil /\ GetHWait v'48 w (v'89,Int.zero) /\ TcbMod.get v'48 (v'89,Int.zero) = Some (prio,st,msg)).
  do 3 eexists.
  
(* Lemma post_exwt_succ_pre_mbox
 *      : forall (v'36 v'13 : vallist) (v'12 : int32) 
 *          (v'32 : block) (v'15 : int32) (v'24 : block) 
 *          (v'35 v'0 : val) (v'8 : tid) (v'9 v'11 : EcbMod.map)
 *          (x : val) (x0 : maxlen) (x1 : waitset)
 *          (v'6 v'10 : EcbMod.map) (v'38 v'69 v'39 : int32) 
 *          (v'58 : block) (a : priority) (b : taskstatus) 
 *          (c :msg) (v'62 v'7 : TcbMod.map) 
 *          (vhold : addrval),
 *        v'12 <> Int.zero ->
 *        R_PrioTbl_P v'36 v'7 vhold ->
 *        RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
 *        R_ECB_ETbl_P (v'32, Int.zero)
 *          (V$OS_EVENT_TYPE_MBOX
 *           :: Vint32 v'12
 *              :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
 *          v'13) v'7 ->
 *        RH_TCBList_ECBList_P v'11 v'7 v'8 ->
 *        EcbMod.join v'9 v'10 v'11 ->
 *        EcbMod.joinsig (v'32, Int.zero) (absmbox x , x1) v'6 v'10 ->
 *        Int.unsigned v'12 <= 255 ->
 *        array_type_vallist_match Int8u v'13 ->
 *        length v'13 = ∘OS_EVENT_TBL_SIZE ->
 *        nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
 *        Int.unsigned v'38 <= 7 ->
 *        nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
 *        Int.unsigned v'69 <= 255 ->
 *        nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
 *        Int.unsigned v'39 <= 7 ->
 *        nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
 *        Vptr (v'58, Int.zero) ->
 *        TcbJoin (v'58, Int.zero) (a, b, c) v'62 v'7 ->
 *        a = (v'38<<ᵢ$ 3)+ᵢv'39/\ b<> rdy /\
 *        x1 <> nil /\
 *        GetHWait v'7 x1 (v'58, Int.zero) /\
 *        TcbMod.get v'7 (v'58, Int.zero) = Some (a, b, c)
 * .
 * Admitted. *)
 
  eapply post_exwt_succ_pre_mbox;eauto.
  clear -H16.
  intro; subst; int auto.
(* ** ac:   SearchAbout OSUnMapVallist. *)
  
  
eapply OSUnMapVallistElementLe7; eauto.
(* ** ac: SearchAbout array_type_vallist_match. *)
assert (rule_type_val_match Int8u (nth_val' (Z.to_nat (Int.unsigned v'72)) v'58) = true).
eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match.
assert  (Z.to_nat (Int.unsigned v'72) < length v'58 \/ Z.to_nat (Int.unsigned v'72) >= length v'58  )%nat.
omega.
destruct H35; try assumption.
apply nth_val'_undef in H35.
rewrite H35 in H43.
inverts H43.
auto.

rewrite H43 in H35.
clear -H35.
unfolds in H35.
math simpl in H35.
exact H35.



eapply OSUnMapVallistElementLe7; eauto.
simpljoin.

  hoare_abscsq.
  apply noabs_oslinv.
  eapply absinfer_mbox_post_exwt_succ.
  go.

  unfold get; simpl.
  go.
  auto.
  eauto.
  exact H47.
  Require Import tcblist_setnode_lemmas.
  eapply backward_rule1.
  intro.
  intros.

  eapply set_node_elim.
  eauto.
  eauto.
  eauto.
  unfold get; simpl; eauto.
  eauto.
  4: unfolds; simpl; auto.

  Focus 4.
  sep cancel tcbdllseg.
  eauto.
(* ** ac:   Check TCBNode_P_set_rdy . *)
  eapply TCBNode_P_set_rdy.
  2:instantiate (1 := v'90).
  5:eauto.
  6: eauto.
  5:eauto.
  
(* ** ac:   SearchAbout tcblist_get. *)
  Focus 5.
  eapply TCBList_P_tcblist_get_TCBNode_P.
  eauto.
  eauto.
  eauto.
  apply OSUnMapVallistElementLe7 in H42.
  apply OSUnMapVallistElementLe7 in H44.
  clear -H42 H44; mauto.

(* ** ac:   SearchAbout ( Int.unsigned (( _ <<ᵢ ($ 3) ) + _ ) >>ᵢ ($ 3)  = _ ). *)
(* ** ac:   SearchAbout ( _ <<ᵢ ($ 3)). *)

  rewrite math_shrl_3_eq.
(* ** ac:   SearchAbout (nth_val). *)
  apply nth_val'2nth_val; auto.

  apply OSUnMapVallistElementLe7 in H44.
  clear -H44; omega.

  apply OSUnMapVallistElementLe7 in H42.
  clear -H42; int auto.
  mauto.

  assert (rule_type_val_match Int8u (nth_val' (Z.to_nat (Int.unsigned v'72)) v'52) = true).
  eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match.
  assert  (Z.to_nat (Int.unsigned v'72) < length v'52 \/ Z.to_nat (Int.unsigned v'72) >= length v'52  )%nat.
  omega.
  destruct H48; try assumption.
  apply nth_val'_undef in H48.
  rewrite H34 in H48.
  inverts H48.
  auto.

  rewrite H34 in H48.
  clear -H48.
  unfolds in H48.
  math simpl in H48.
  exact H48.
  unfolds in H41; inverts H41.
  
      apply Int.and_not_self.



      lets b1 : H44.
      lets b2 : H42.
  apply OSUnMapVallistElementLe7 in b1.
  apply OSUnMapVallistElementLe7 in b2.
  rewrite math_shrl_3_eq; [idtac | clear -b1 b2; solve[omega | mauto] ..].
  rewrite math_8range_eqy;[idtac | clear -b1 b2; solve[omega | mauto] ..].
  unfolds.

  rewrite math_shrl_3_eq; [idtac | clear -b1 b2; solve[omega | mauto] ..].
  rewrite math_8range_eqy;[idtac | clear -b1 b2; solve[omega | mauto] ..].
  repeat tri_exists_and_solver1.
  clear -b1 b2; solve[omega | mauto].
  clear -b1 b2; solve[omega | mauto].
(* ** ac:   SearchAbout OSMapVallist. *)
  erewrite <- math_mapval_core_prop.
  eauto.
  clear -b1; omega.
  assumption.
(* ** ac:   Print R_PrioTbl_P. *)
  unfolds in H61; simpljoin; assumption.

  hoare unfold.

  lets b1 : H44.
  lets b2 : H42.
  apply OSUnMapVallistElementLe7 in b1.
  apply OSUnMapVallistElementLe7 in b2.

  rewrite math_shrl_3_eq in *; [idtac | clear -b1 b2; solve[omega | mauto] ..].
  rewrite math_8range_eqy in * ;[idtac | clear -b1 b2; solve[omega | mauto] ..].
  
  hoare forward prim.
(* ** ac:   Show. *)


  unfold AECBList, AOSTCBPrioTbl, AOSTCBList.
  sep pauto.
  do 2 sep  cancel 1%nat 1%nat.
  sep cancel Aptrmapsto.
  sep cancel 6%nat 2%nat.

  eapply evsllseg_compose with
  (qptrl1:= v'21) (qptrl2:=v'22)
                  (l:= (V$OS_EVENT_TYPE_MBOX
                         ::  Vint32 v'57
                         :: Vint32 i1
                         :: m0 :: x4 :: v'41 :: nil))
                  (msgqls1:=v'23) (msgqls2 := v'24) (tl:=(Vptr (v'25, Int.zero)))
                  (x:=
                     (update_nth_val (Z.to_nat (Int.unsigned v'72)) v'58
                                     (Vint32 (v'73&ᵢInt.not v'74))))
                  (msgq:=DMbox m0);auto.
  go.
  sep cancel AEventNode.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
(* ** ac:   SearchAbout tcbdllflag. *)
  eapply tcbdllflag_set_node.
  sep cancel 2%nat 1%nat.
  eauto.
  eauto.
  eauto.
  unfolds; compute; auto.

(* ** ac:   SearchAbout R_PrioTbl_P. *)
  
  unfold set; simpl.
  eapply TcbMod_set_R_PrioTbl_P_hold.
  eauto.
  eauto.

(* ** ac:   SearchAbout RL_RTbl_PrioTbl_P. *)
(* ** ac:   Show. *)
(* ** ac:   Check  rl_rtbl_priotbl_p_hold1. *)
(* ** ac:   Print or. *)
(* ** ac:   Print val_inj. *)
  change (Vint32 (Int.or v'90 v'74)) with (val_inj (or (Vint32 v'90) (Vint32 v'74))).
(* ** ac:   Check  rl_rtbl_priotbl_p_hold1. *)
  rewrite <- H34.
  {
  eapply  rl_rtbl_priotbl_p_hold1.
  auto.

  apply OSUnMapVallistElementLe7 in H42.
  clear -H42; omega.
  2:eauto.
  2:eauto.

  apply OSUnMapVallistElementLe7 in H44.
  clear -H44; omega.
  assumption.
  assumption.
  assumption.
  
  eapply  osmapvalle128.
  eauto.
  }


(* ** ac:   Check math_mapval_core_prop. *)
  Focus 2.
  erewrite (math_mapval_core_prop  _ _ _ H46).
  eauto 1.

  Focus 2.
  erewrite (math_mapval_core_prop  _ _ _ H46).
  eauto 1.

  2:exact H48.

(* ** ac:   Check ecblist_p_post_exwt_hold_mbox. *)
  {
    lets bbb: H47.
(* ** ac:     Check get_join. *)
    assert ( exists tcs', join (sig (v'89, Int.zero) ((v'72<<ᵢ$ 3) +ᵢ  v'71, x1, x2)) tcs' v'48).
    
    eapply get_join .
    exact bbb.
    simpljoin.
    eapply ecblist_p_post_exwt_hold_mbox; eauto 1.
    (* admit. *)
    clear -H16.
    intro; subst v'56; int auto.
    assert (rule_type_val_match Int8u (nth_val' (Z.to_nat (Int.unsigned v'72)) v'58) = true).
    eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match.
    assert  (Z.to_nat (Int.unsigned v'72) < length v'58 \/ Z.to_nat (Int.unsigned v'72) >= length v'58  )%nat.
    omega.
    destruct H70; try assumption.
    apply nth_val'_undef in H70.
    rewrite H70 in H43.
    inverts H43.
    auto.

    rewrite H43 in H70.
    clear -H70.
    unfolds in H70.
    math simpl in H70.
    exact H70.

    eapply osmapvalle128; eauto.
    assert (m0 = Vnull).
    unfolds in r.
    destruct r.
    apply   H71.
    auto.


    unfolds; simpl.
    splits; intros; auto.
    tryfalse.
    
    
  }

(* ** ac:   Check rh_curtcb_set_nct. *)
  Lemma rh_curtcb_set
     : forall (v'8 : Modules.tid) (v'7 : TcbMod.map) 
         (x : abstcb.B) (tid0 : Modules.tid),
       RH_CurTCB v'8 v'7 ->
       RH_CurTCB v'8 (TcbMod.set v'7 tid0 x).
  Proof.
    intros.
    assert ( tid0 = v'8 \/ tid0 <> v'8).
    tauto.
    destruct H0.
    unfold RH_CurTCB in *.
    simpljoin.
    subst.
    unfold get ; simpl.
    rewrite TcbMod.set_a_get_a.
    destruct x.
    destruct p.
    eauto.
    go.
    apply rh_curtcb_set_nct;auto.
  Qed.

  apply rh_curtcb_set; auto.

  assert (exists xl,x1 = wait (os_stat_mbox (v'25, Int.zero)) xl).

  eapply rh_tcblist_ecblist_p_post_exwt_aux_mbox ;eauto.
  unfolds in H40.
  simpljoin; assumption.
  simpljoin.

  
  eapply rh_tcblist_ecblist_p_post_exwt_mbox; eauto.
  unfolds in H40.
  simpljoin; assumption.
  
  go.

  hoare forward.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aop.
  eauto.
  unfolds.
  left; reflexivity.

  go.
  linv_solver.
  linv_solver.

(* ** ac:   Locate "POST". *)

  simpl getasrt.
  unfold OS_SchedPost'.
  

  hoare forward.
  inverts H57.
  reflexivity.

  Grab Existential Variables.
  (* admit. *)
  clear -b1; omega.
  clear -b1; omega.
  exact (V$ 0).
  exact (V$ 0).
  eauto.
  exact ($ 0).
  exact (V$ 0).
  exact (V$ 0).
  exact (V$ 0).
  exact ($ 0).
Qed.



