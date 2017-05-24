(**************************  uc/OS-II  ******************************)
(*************************** OS_Q.C *********************************)
(****Proofs for API Fucntion:  void* OSQAccept(OS_EVENT* pevent)*****)
(**************************** Code: *********************************)
(*** 
void  *OSQAccept (OS_EVENT *pevent)
{
    void      *msg;
    OS_Q      *pq;
    BOOLEAN   legal;
1   if (pevent == (OS_EVENT * )0) 
    {
2       return ((void * )0);
    }
3   OS_ENTER_CRITICAL();
4   legal = OS_EventSearch(pevent);
5   if (!legal)
    {
6       OS_EXIT_CRITICAL();
7       return ((void * )0);
    }
8   if ( pevent -> OSEventType  !=  OS_EVENT_TYPE_Q )
    {
9       OS_EXIT_CRITICAL(); 
10      return ((void * )0); 
    } 
11  pq = (OS_Q * )pevent->OSEventPtrs;
12  if (pq->OSQEntries > 0) 
    {
13      msg = *pq->OSQOut++;
14      pq->OSQEntries--;
15      if (pq->OSQOut == pq->OSQEnd)
        {
16          pq->OSQOut = pq->OSQStart;
        }
    } 
    else
    {
17      msg = (void * )0;
    }
18  OS_EXIT_CRITICAL();
19  return (msg);
}
***)
 
Require Import ucos_include. 
Require Import OSQAcceptPure.
Require Import msgq_absop_rules.

Open Scope code_scope.
Open Scope int_scope.
(* ------------------- OS Q Accept -------------------------*)


Ltac sep_lift_absdata H :=
  match type of H with
    | _ |= ?P =>
      match find_aop P with
        | none _ =>
          idtac 1 "no absop in the pre-condition"; fail 1
        | some ?a =>
          match find_absdata P absecblsid with
            | none _ =>
              idtac 2 "no HECBList in the pre-condition";
                fail 2
            | some ?b =>
              match find_absdata P abstcblsid with
                | none _ => 
                  idtac 3 "no HTCBList in the pre-condition"; fail 3
                | some ?c =>
                  match find_absdata P ostmid with
                    | none _ =>
                      idtac 4 "no HTime in the pre-condition"; fail 4
                    | some ?e =>
                      match find_absdata P curtid with
                        | none _ =>
                          idtac 5 "no HCurTCB in the pre-condition"; fail 5
                        | some ?f =>
                              sep lifts (a::b::c::e::f::nil)  in H
                          end
                      end
              end
          end
      end
  end.

Ltac find_aisris' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_aisris' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_aisris' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | A_isr_is_prop => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_aisris Hp := let y := find_aisris' Hp in
                       eval compute in y.

Ltac isr_is_prop_elim':=
  match goal with
    | H:?s |= ?P |- ?s |= _ =>
      match find_aisr P with
        | none => idtac
        | some ?a =>
          match find_ais P with
            | none => idtac
            | some ?b =>
              match find_aisris P with
                | none => idtac
                | some ?c => sep lifts (a::b::c::nil)%nat in H;eapply elim_a_isr_is_prop in H;exact H
              end
          end
      end
  end.

Ltac isr_is_prop_elim:=eapply backward_rule1;[intros;isr_is_prop_elim' | ].

Ltac isr_is_prop_add':=
  match goal with
    | H:?s |= ?P |- ?s |= _ =>
      match find_aisr P with
        | none => idtac
        | some ?a =>
          match find_ais P with
            | none => idtac
            | some ?b =>
              sep lifts (a::b::nil)%nat in H;eapply add_a_isr_is_prop in H;exact H
          end
      end
  end.

Ltac isr_is_prop_add:=eapply backward_rule1;[intros;isr_is_prop_add' | ].

Ltac sep_lift_absdata' H :=
  match type of H with
    | _ |= ?P =>
      match find_aop P with
        | none _ =>
          idtac 1 "no absop in the pre-condition"; fail 1
        | some ?a =>
          match find_absdata P absecblsid with
            | none _ =>
              idtac 2 "no HECBList in the pre-condition";
                fail 2
            | some ?b =>
              match find_absdata P abstcblsid with
                | none _ => 
                  idtac 3 "no HTCBList in the pre-condition"; fail 3
                | some ?c =>
                  match find_absdata P ostmid with
                    | none _ =>
                      idtac 4 "no HTime in the pre-condition"; fail 4
                    | some ?e =>
                      match find_absdata P curtid with
                        | none _ =>
                          idtac 5 "no HCurTCB in the pre-condition"; fail 5
                        | some ?f =>
                          sep lifts (a::b::c::e::f::nil)  in H
                      end
                  end
              end
          end
      end
    end.

(*
Hint Resolve gooda_qcc retpost_osev.
*)
Open Scope code_scope.

Lemma OSQAccProof :
  forall tid vl p r, 
    Some p =
    BuildPreA' os_api OSQAccept
               (qacc, (Tptr Tvoid, Tptr os_ucos_h.OS_EVENT :: nil)) vl OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api OSQAccept
               (qacc, (Tptr Tvoid, Tptr os_ucos_h.OS_EVENT :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSQAccept = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid  {{p}} s {{Afalse}}.
Proof.
  init_spec; hoare unfold.
  (* parameter check ------------ L1 ~ L2 *)
  hoare unfold; hoare forward; pauto.
  pure_intro.
  assert(x=Vnull) by pauto.
  subst x.
  hoare_abscsq.
  apply noabs_oslinv.
  eapply qacc_absinfer_null; pauto.

  hoare forward;auto.
  hoare forward.

  (* encrit -----------------------L3 *)
  hoare forward prim.
  pure intro.
  assert (exists v, x= Vptr v) by pauto. 
  simpljoin1.
 
  (* function call OSQPtrSearch  -------------------- L4 *)
  unfold OSInv;hoare_unfold.
  hoare forward.
  sep cancel 1%nat 10%nat.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel AECBList.
  sep cancel AOSTCBList.
  sep cancel tcbdllflag.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTCBPrioTbl.
  exact H3.
  pauto.
  pauto.
  apply retpost_osev.
  intros.
  destruct H3.
  destruct H3.
  sep auto.
  sep auto.
  intros.
  sep auto.

  hoare unfold.
  eapply backward_rule1.
  intros;eapply disj_star_elim.
  eauto.
  apply disj_rule.

  (* return value check ------------ L5 ~ L7 *)
  pure intro.
  hoare forward.
  instantiate (1:=Afalse).
  pure_intro.
  destruct H11; simpljoin1.
  pauto.
 
  Focus 2.
  (* no queue*)
  pure intro.
  hoare forward. 
  instantiate (1:=Afalse).
  inverts H7.
  hoare abscsq.
  apply noabs_oslinv.
  apply qacc_absinfer_no_q.
  pauto.
  intro.
  do 3 destruct H5;tryfalse.

  Focus 2.
  eapply disj_rule.
  eapply backward_rule1.
  2:eapply pfalse_rule.
  intros.
  unfold1 sat in H5.
  simpljoin1; false.
  pure intro.
  
  destruct H5;
  assert (Int.eq ($ 0) ($ 0)=true) by pauto;
  rewrite H6 in H5;
  simpl in H5;tryfalse.
  
  hoare forward prim.
  sep pauto.
  pauto.
  hoare forward.

  (* check the event type------ L8 ~ L10 *)

  hoare forward.
  hoare unfold.
  hoare forward.
  pauto.
  pauto.
  pauto.
  
  instantiate (1:=Afalse).

  hoare_split_pure_all.
  destruct H12.
  remember (Int.eq i0 ($ OS_EVENT_TYPE_Q)) as X.
  destruct X.
  unfold val_inj in H12.
  simpl in H12.
  unfold Int.notbool in H12.
  rewrite Int.eq_false in H12.
  tryfalse.
  clear.
  int auto.

  eapply backward_rule1.
  intros.
  sep lift 8%nat in H20.
  eapply eventtype_neq_q in H20;eauto.
  hoare_split_pure_all.
  inverts H17.
  hoare abscsq.
  apply noabs_oslinv.
  eapply qacc_absinfer_no_q;auto.
  pauto.
  hoare forward prim.
  
  unfold AECBList.
  sep pauto.
  eapply evsllseg_compose.
  instantiate (2:= Vint32 i0 :: Vint32 i :: Vint32 i1 :: x2 :: x3 :: v'43 :: nil).
  unfold V_OSEventListPtr; simpl;  auto. 
  auto.
  auto.
  repeat (sep cancel evsllseg).
  (* AEventNode *)  

  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold node.
  sep pauto.
  sep cancel 1%nat 3%nat.
  sep cancel 1%nat 1%nat.
  eauto.
  eauto.
  unfolds;simpl;auto.
  auto.
  auto.
  pauto.
  auto.
  pauto.
  hoare forward.
  hoare forward.
  
  (*get the pointer of OSEVENT -------------- L11 *)
  pure intro. 
  hoare forward.
  simpl;split;pauto.
  
  (*check if has message ------------------ L12 *)
  apply val_inj_eq_q in H12.
  subst i0.
  unfold AEventData.
  destruct v'42.
  unfold AMsgData.
  unfold AOSQCtr.
  unfold AOSQBlk.
  hoare unfold.
  
  simpl in H12.
  inverts H12.

  assert (exists i', x5 = Vptr (v'40, i')).
  eapply osq_same_blk_st_out';eauto.
  simpljoin1.
  
  hoare forward.
  simpl;splits;pauto.
  destruct (Int.ltu ($ 0) i0);simpl;auto.
 
  (* get message ------------------------ L13*)
  pure intro.
  clear H20 H28.

  Definition OSInv1 tid tcbl1 tcbcur tcbl2 p1 tcbls:=
    EX (eventl osql qblkl : list vallist) (msgql : list EventData)
       (ectrl : list os_inv.EventCtr) (ptbl : vallist) (p2 : val) 
       (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
       (t : int32) (vhold : addrval) (ptfree : val) (lfree : list vallist),
    AOSEventFreeList eventl **
                     AOSQFreeList osql **
    AOSQFreeBlk qblkl **
    AECBList ectrl msgql ecbls tcbls **
    AOSMapTbl **
    AOSUnMapTbl **
    AOSTCBPrioTbl ptbl rtbl tcbls vhold **
    AOSIntNesting **
    AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl tid tcbls **
    AOSTCBFreeList ptfree lfree **
    AOSRdyTblGrp rtbl rgrp **
    AOSTime (Vint32 t) **
    HECBList ecbls **
    HTCBList tcbls **
    HTime t **
    HCurTCB tid ** AGVars ** [|RH_TCBList_ECBList_P ecbls tcbls tid|] ** A_isr_is_prop.
    
  instantiate (
      1:=
        <|| END (Some (nth_val' (Z.to_nat ((Int.unsigned x2 -  Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4)) v2 ))||>  **
            LV pq @ os_ucos_h.OS_Q ∗ |-> Vptr (v'42, Int.zero)  **
            LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr  (v'27, Int.zero)  **
            LV message @ (Void) ∗
            |-> nth_val' (Z.to_nat ((Int.unsigned x2 -  Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4)) v2  **
            LV legal @ Int8u |-> (V$1) **
            OSInv1 tid v'31 v'32 v'33 v'29 v'37 **
            atoy_inv' **
            Aisr empisr **
            Aie false **
            Ais nil **
            Acs (true :: nil) **
            A_dom_lenv
            ((pevent, os_ucos_h.OS_EVENT ∗)
               :: (message, (Void) ∗) :: (pq, os_ucos_h.OS_Q ∗) :: (legal, Int8u) :: nil) ** tcbdllflag v'29 (v'31 ++ v'32 :: v'33) ** p_local OSLInv tid init_lg **
            [|isptr (nth_val' (Z.to_nat ((Int.unsigned x2 -  Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4)) v2)|]
    ).


(*

  
  instantiate (
      1:=
        <|| rendop (Some (nth_val' (Z.to_nat ((Int.unsigned x2 -  Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4)) v2 ))||>  **
            LV pq @ OS_Q ∗ |-> Vptr (v'41, Int.zero) **
            LV pevent @ OS_EVENT ∗ |-> Vptr  (v'25, Int.zero) **
            LV message @ (Void) ∗
            |-> nth_val' (Z.to_nat ((Int.unsigned x2 -  Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4)) v2 **
            LV legal @ Int8u |-> (V$1) **
            OSInv **
            atoy_inv' **
            Aisr empisr **
            Aie false **
            Ais nil **
            Acs (true :: nil) **
            A_dom_lenv
            ((pevent, OS_EVENT ∗)
               :: (message, (Void) ∗) :: (pq, OS_Q ∗) :: (legal, Int8u) :: nil) **
            [|isptr (nth_val' (Z.to_nat ((Int.unsigned x2 -  Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4)) v2)|]
    ).
*)
  hoare lift 4%nat pre.
  remember ( Int.ltu ($ 0) i0 ) as Hbo.
  destruct Hbo;simpl in H12; tryfalse.
  apply eq_sym in HeqHbo.
  lets Hx: wellq_props HeqHbo H6 H15;eauto.
  (*   HeqHbo : Int.ltu ($ 0) i0 = true
   * H6 : RLH_ECBData_P
   *        (DMsgQ (Vptr (v'42, Int.zero))
   *           (x10
   *            :: x9
   *               :: x1
   *                  :: x4
   *                     :: Vptr (v'40, x2)
   *                        :: Vint32 i2
   *                           :: Vint32 i0 :: Vptr (v'40, Int.zero) :: nil)
   *           (x :: x0 :: nil) v2) v'47
   *          H15 : WellformedOSQ
   *         (x10
   *          :: x9
   *             :: x1
   *                :: x4
   *                   :: Vptr (v'40, x2)
   *                      :: Vint32 i2
   *                         :: Vint32 i0 :: Vptr (v'40, Int.zero) :: nil) *)


  simpljoin1.
  hoare forward;auto.
  simpl;splits;pauto.

  hoare forward; pauto.

  (* decrease the number of entrys ---------L14*)
  hoare forward;pauto.

  (* check if needs to reset OSQOut -------------- L15 ~ L16 *)
  inverts H17.

  lets Hx: h_has_same_msg H6;eauto.
  simpl;auto.
  simpljoin1.

  assert ( EcbMod.get v'36 (v'27, Int.zero) = Some (absmsgq ((nth_val' (Z.to_nat ((Int.unsigned x2 - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4)) v2) :: x5)  x6 , x7)) as Hget.
  eapply EcbMod.join_joinsig_get;eauto.
  simpljoin1.
  
  eapply forward_rule2.
  eapply abscsq_rule''.
  apply noabs_oslinv.

(*  
  intro;mytac;tryfalse.
  intro;mytac;tryfalse.
 *)
  Focus 2.

  hoare forward.
  simpl;splits;pauto.
  
  simpl;splits;pauto.
  
  clear -H34.
  unfold isptr in H34.
  destruct H34.
  subst;simpl;auto.
  destruct H.
  subst x1.
  destruct x.
  pauto.
  
  hoare forward.
  simpl;splits;pauto.

  eapply absinfer_disj.

  eapply absinfer_conseq_pre.
  Focus 2.

  intros.
  sep_lift_absdata' H17.
  exact H17.

  eapply qacc_absinfer_get_msg; pauto. 
  eapply absinfer_conseq_pre.
  Focus 2.

  
  intros.
  sep_lift_absdata' H17.
  exact H17.
  eapply qacc_absinfer_get_msg;  pauto.
  
  intros;destruct H17.

  sep remember (7::9::10::11::12::nil)%nat in H17.
  unfold AOSEventTbl in H17.
  assert (s|= AEventNode (Vptr (v'27, Int.zero)) 
             (V$OS_EVENT_TYPE_Q :: Vint32 i :: Vint32 i1 :: Vptr (v'42,Int.zero) :: x3 :: v'43 :: nil)
             v'41 
             (DMsgQ (Vptr (v'42,Int.zero)) 
                    (x10
                       :: x9
                       :: x1
                       :: x4
                       :: x9
                       :: Vint32 i2
                       :: Vint32 (i0-ᵢ$ 1) :: Vptr (v'40, Int.zero) :: nil)
                   (x :: x0 :: nil) v2) ** H42).
  unfold_msg.
  subst H42.
  sep semiauto;eauto.
  unfold AEventData.
  unfold AMsgData.
  unfold AOSQCtr.
  unfold AOSQBlk.
  unfold node.
  sep auto.
  
  unfold V_qfreeblk;simpl;auto.
  
  assert (x1=Vptr (v'40,(x2 +ᵢ Int.mul ($ 1) ($ 4)))). 
  clear -H51 H34.
  unfold isptr in*.
  destruct H34.
  subst x1.
  unfold val_inj in H51;tryfalse.
  destruct H;subst x1.
  destruct x.
  destruct (peq v'40 b);tryfalse.
  subst b.
  remember ( Int.eq (x2 +ᵢ Int.mul ($ 1) ($ 4)) i) as X.
  destruct X;unfold val_inj in H51;tryfalse.
  symmetry in HeqX.
  lets H100: Int.eq_spec (x2  +ᵢ Int.mul ($ 1) ($ 4)) i.
  rewrite HeqX in H100.
  subst i;auto.
  unfold val_inj in H51;tryfalse.
  subst x1.
  eapply get_wellformedosq_end with (x:=i0);eauto.
  
  simpl;splits;pauto.
  simpl;auto.
  simpl;splits;pauto.
  simpl;auto.
  simpl;splits;pauto.
  
  subst H42.
  unfold OSInv1.
  sep semiauto.
  sep cancel AOSQFreeBlk.
  sep cancel AOSTCBList.
  sep cancel AOSQFreeList.

  sep cancel AOSEventFreeList.
  sep lifts (2::4::5::nil)%nat in H43.
  eapply evsllseg_compose in H43;eauto.
  unfold AECBList.

  sep auto.
  eapply msgqnode_p_hold_end in H6;eauto.
  
  lets Hnewjoin: ecb_get_set_join_join Hget H8 H19.
  simpljoin1.
  
  eapply msgqlist_p_compose;eauto.
  clear -H52 H34.
  unfold isptr in*.
  destruct H34.
  subst x1.
  unfold val_inj in H52;tryfalse.
  destruct H;subst x1.
  destruct x.
  destruct (peq v'40 b);tryfalse.
  subst b.
  remember ( Int.eq (x2 +ᵢ Int.mul ($ 1) ($ 4)) i) as X.
  destruct X;unfold val_inj in H52;tryfalse.
  symmetry in HeqX.
  lets H100: Int.eq_spec (x2+ᵢInt.mul ($ 1) ($ 4)) i.
  rewrite HeqX in H100.
  subst i;auto.
  unfold val_inj in H52;tryfalse. 
  sep split in H43. 
  auto.
  simpl in H27;unfold isptr;destruct ( (nth_val'
             (Z.to_nat
                ((Int.unsigned x2 - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) /
                 4)) v2));tryfalse;auto.
  right;exists a;auto.

  eapply rh_tcbls_mqls_p_getmsg_hold;eauto.
  auto.
  auto.
  
  (*****not end*****)
 
  sep split in H17.
  assert (x1 <> Vptr(v'40,(x2 +ᵢInt.mul ($ 1) ($ 4)))).
  clear -H42 H34. 
  unfold isptr in *.
  destruct H34.
  subst x1;auto.
  destruct H;subst x1.
  destruct x.
  destruct (peq v'40 b);auto.
  subst b.
  intro.
  inverts H.
  rewrite Int.eq_true in H42.
  destruct H42;tryfalse.
  intro;inverts H;tryfalse.

  eapply msgqnode_p_hold_no_end in H6;eauto.

  lets Hnewjoin: ecb_get_set_join_join Hget H8 H19.
  simpljoin1.
  lets Hmqlsp: msgqlist_p_compose H7 H6 H50 H51;eauto.

  unfold OSInv1.
  sep semiauto;eauto.
  sep cancel AOSQFreeBlk.
  sep cancel AOSQFreeList.
  sep cancel AOSTCBList.

  unfold AECBList.
  sep semiauto.

  eapply evsllseg_compose;eauto.
  intros. 
  2: sep cancel 6%nat 2%nat.
  2: sep cancel 6%nat 2%nat.
  Focus 2.
  sep cancel AOSEventFreeList.
  sep cancel AOSTCBFreeList.

  instantiate (1:= (DMsgQ (Vptr (v'42, Int.zero))
                          (x10 :: x9 :: x1 :: x4 ::Vptr (v'40, x2+ᵢInt.mul ($ 1) ($ 4)) :: Vint32 i2 :: Vint32 (i0-ᵢ$ 1) :: Vptr (v'40,Int.zero) :: nil)
                          (x :: x0 :: nil)
                          v2)
              ).
  instantiate (1:=v'41).
  instantiate (1:= (V$OS_EVENT_TYPE_Q
                     :: Vint32 i :: Vint32 i1 :: Vptr (v'42,Int.zero) :: x3 :: v'43 :: nil) ).
  unfold AEventNode.
  unfold AEventData.
  unfold_msg.
(*  unfold AOSEventTbl in H41. *)
  sep semiauto;eauto.
  sep auto.
  
  simpl;splits;pauto.
  unfold V_qfreeblk;simpl;auto.

  eapply get_wellformedosq_end';eauto.
  simpl;splits;pauto.
  simpl;auto.
  simpl;splits;pauto.
  simpl;auto.
  apply Hmqlsp.
  simpl in H26;unfold isptr;destruct ( (nth_val'
             (Z.to_nat
                ((Int.unsigned x2 - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) /
                 4)) v2));tryfalse;auto.
  right;exists a;auto.

  (* H26 : isptr (Vptr (v'42, Int.zero)) *)


  eapply rh_tcbls_mqls_p_getmsg_hold;eauto.

  (*--------------no msg L17 -----------------------*)
  pure intro.
  remember (Int.ltu ($ 0) i0) as X.
  destruct H12;destruct X;tryfalse.

  clear H12.

  lets Hnomsg: msgqnode_p_nomsg H6;eauto.
  simpljoin1.
 
  lets Hgetnomsg: EcbMod.join_joinsig_get H19 H8.

  inverts H17.
  
  hoare abscsq.
  apply noabs_oslinv.
  eapply qacc_absinfer_no_msg;  pauto.
 
  hoare forward.
  {
  unfold OSInv1.
  apply disj_rule.
  hoare_split_pure_all.
  (* hoare lifts (1::7::8::9::10::6::nil)%nat pre. *)
  hoare forward prim.
  sep cancel 6%nat 1%nat.
  
(*  eapply seq_rule.
  eapply excrit1_rule'_ISnil_ISRemp.
  intros.
  sep lifts (2::3::4::10::5::1::nil)%nat in H12. *)
  exact H29.
  pauto.
(*  simpl;auto. *)
  
  hoare forward.
  pauto.
  (* Print  RLH_ECBData_P.
   * Print   MatchLHMsgList .
   * Print  RLH_ECBData_P.
   * Lemma aaa:
   *   forall v'42 xx yy v2 v'47,
   *   RLH_ECBData_P
   *        (DMsgQ (Vptr (v'42, Int.zero))
   *           xx
   *           yy v2) v'47 ->
   *   False.
   *   intros.
   *   unfolds in H.
   *   destruct v'47.
   *   destruct e; auto.
   *   simpljoin.
   * 
   * Print   MatchLHMsgList . *)
  (* pauto. *)

  hoare forward prim.
(* ** ac:   Show. *)


  
  (* hoare forward. *)
  unfold AOSEventTbl in H12.
  unfold AECBList.
  sep pauto.

  (* instantiate (1:= (DMsgQ (Vptr (v'42, Int.zero))
   *                         (x10 :: x9 :: x1 :: x4 ::Vptr (v'40, x2+ᵢInt.mul ($ 1) ($ 4)) :: Vint32 i2 :: Vint32 (i0-ᵢ$ 1) :: Vptr (v'40,Int.zero) :: nil)
   *                         (x :: x0 :: nil)
   *                         v2)
   *             ).
   * instantiate (1:=v'41).
   * instantiate (1:= (V$OS_EVENT_TYPE_Q
   *                    :: Vint32 i :: Vint32 i1 :: Vptr (v'42,Int.zero) :: x3 :: v'43 :: nil) ). *)

  instantiate (2:=(v'25++(DMsgQ (Vptr (v'42,Int.zero))  (x10
              :: x9
                 :: x1
                    :: x4
                       :: Vptr (v'40, x2)
                       :: Vint32 i2 :: Vint32 i0 :: Vptr (v'40,Int.zero) :: nil) (x :: x0 :: nil) v2::nil)++v'26)).
  
  instantiate (2:=(v'23++ (( (V$OS_EVENT_TYPE_Q
              :: Vint32 i :: Vint32 i1 :: Vptr (v'42,Int.zero) :: x3 :: v'43 :: nil),v'41)::nil)++v'24)).
  eapply evsllseg_compose;eauto.
  instantiate (1:=v'43).
  simpl;auto.
  sep cancel 8%nat 2%nat.
  sep cancel 8%nat 2%nat.
  unfold AEventNode.
  unfold AEventData.
  unfold_msg.
  sep pauto.
  sep cancel 3%nat 1%nat.
  sep cancel 3%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 3%nat 1%nat.
  sep cancel 3%nat 1%nat.
  
  exact H12.
  eauto.
  simpl;auto.
  eauto.
  simpl;splits;pauto.
  unfold V_qfreeblk;simpl;auto.
  simpl;splits;pauto.
  simpl;auto.
  split;auto.
  simpl;splits;pauto.
  eapply msgqlist_p_compose;eauto.
  pauto.

  (*--------------------------L15 ~ L16--------------------------------*)
  hoare forward.
  }
 
  (*---------false cases ------*)
  hoare_split_pure_all.
  unfolds in H12;simpl in H12.
  inverts H12.

  hoare_split_pure_all.
  unfolds in H12;simpl in H12.
  inverts H12.

  hoare lift 10%nat pre.
  apply backward_rule1 with Afalse.
  intros.
  sep split in H12.
  clear - H15.
  unfolds in H15.
  simpl in H15.
  inverts H15.

  apply pfalse_rule.
  
  Grab Existential Variables.
Qed.


Close Scope code_scope.





