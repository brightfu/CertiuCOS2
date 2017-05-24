Require Import include_frm.
Require Import Lists.ListSet.
Require Import os_code_defs.
Require Import os_ucos_h.
Require Export os_inv.
Require Import abs_op.
Require Import os_core.
Require Import code_notations.
Require Import inv_prop.


(*

*)
(*----------------------------------------------------------------*)
(* internal function spec                                         *)
(*----------------------------------------------------------------*)
Open Scope Z_scope.
Open Scope int_scope.
Require Import List.



Lemma GoodFunAsrt_Astruct' :
  forall vl v d, GoodFunAsrt(Astruct' v d vl).
Proof.
  inductions vl; intros.
  destruct d; simpl; auto.
  destruct d; simpl; auto.
  destruct t; destruct v;
  try solve [simpl; split; auto];
  try eapply IHvl.
Qed.

Lemma GoodFunAsrt_Astruct :
  forall v t vl, GoodFunAsrt(Astruct v t vl).
Proof.
  intros; unfold Astruct; destruct t; simpl; auto.
  apply GoodFunAsrt_Astruct'.
Qed.

Lemma GoodFunAsrt_Aarray' :
  forall vl n t l, GoodFunAsrt (Aarray' l n t vl).
Proof.
  inductions vl; intros.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct l.
  unfold GoodFunAsrt; fold GoodFunAsrt.
  split; simpl; auto.
Qed.

Lemma GoodFunAsrt_Aarray :
  forall l t vl, GoodFunAsrt(Aarray l t vl).
Proof.
  destruct t; simpl; auto.
  intros.
  apply GoodFunAsrt_Aarray'.
Qed.

Lemma GoodFunAsrt_AOSEvent :
  forall v osevent etbl,
    GoodFunAsrt (AOSEvent v osevent etbl).
Proof.
  intros.
  unfold AOSEvent; unfold GoodFunAsrt; fold GoodFunAsrt; intros.
  repeat (split; auto).
  apply GoodFunAsrt_Astruct.
  
  apply GoodFunAsrt_Aarray.
Qed.

Lemma GoodFunAsrt_AEventData :
  forall osevent d,
    GoodFunAsrt (AEventData osevent d).
Proof.
  intros.
  destruct d;
    try solve [
          unfold AEventData;
          unfold GoodFunAsrt; fold GoodFunAsrt;
          repeat (split; try (apply GoodFunAsrt_Astruct); try (apply GoodFunAsrt_Aarray);auto)].
Qed.

Lemma GoodFunAstr_AEventNode :
  forall v osevent etbl d,
    GoodFunAsrt (AEventNode v osevent etbl d).
Proof.
  intros.
  unfold AEventNode; unfold GoodFunAsrt; fold GoodFunAsrt.    
  split.
  apply GoodFunAsrt_AOSEvent.
  apply GoodFunAsrt_AEventData.
Qed.

Lemma GoodFunAsrt_evsllseg :
  forall vl head tailnext ecbls,
    GoodFunAsrt (evsllseg head tailnext vl ecbls).
Proof.
  inductions vl; intros.
  simpl; auto.
  simpl; destruct ecbls; simpl; auto.
  destruct a.
  unfold GoodFunAsrt; fold GoodFunAsrt.
  intros; split; auto.
  split.
  apply GoodFunAstr_AEventNode.
  apply IHvl.
Qed.

Lemma GoodFunAsrt_dllseg :
  forall l head headprev tail tailnext t pre next,
    GoodFunAsrt(dllseg head headprev tail tailnext l t pre next).
Proof.
  inductions l; intros.
  simpl; auto.
  simpl.
  repeat (split; auto).
  apply GoodFunAsrt_Astruct.
Qed.

Lemma GoodFunAsrt_tcbdllseg :
  forall head headprev tail tailnext l,
    GoodFunAsrt (tcbdllseg head headprev tail tailnext l).
Proof.
  intros; unfold tcbdllseg.
  apply GoodFunAsrt_dllseg.
Qed.

Lemma GoodFunAsrt_qblkf_sllseg :
  forall l head tailnext t next,
    GoodFunAsrt (qblkf_sllseg head tailnext l t next).
Proof.
  inductions l; intros.
  simpl; auto.
  repeat (split;
          try (apply GoodFunAsrt_Aarray);
          try (apply GoodFunAsrt_Astruct);
          try (apply GoodFunAsrt_AEventData);
          try (apply GoodFunAsrt_evsllseg);
          try (apply GoodFunAsrt_tcbdllseg);
          try (apply GoodFunAsrt_dllseg);
          auto).
Qed.

Lemma GoodFunAsrt_qblkf_sll :
  forall head l t next,
    GoodFunAsrt (qblkf_sll head l t next).
Proof.
  unfold qblkf_sll.
  intros; apply GoodFunAsrt_qblkf_sllseg.
Qed.

Lemma GoodFunAsrt_ecbf_sllseg :
  forall l head tailnext t next,
    GoodFunAsrt (ecbf_sllseg head tailnext l t next).
Proof.
  inductions l; intros.
  simpl; auto.
  repeat (split;
          try (apply GoodFunAsrt_Aarray);
          try (apply GoodFunAsrt_Astruct);
          try (apply GoodFunAsrt_AEventData);
          try (apply GoodFunAsrt_evsllseg);
          try (apply GoodFunAsrt_tcbdllseg);
          try (apply GoodFunAsrt_dllseg);
          auto).
Qed.

Lemma GoodFunAsrt_ecbf_sll :
  forall head l t next,
    GoodFunAsrt (ecbf_sllseg head Vnull l t next).
Proof.
  intros.
  apply GoodFunAsrt_ecbf_sllseg.
Qed.

Lemma GoodFunAsrt_sllseg :
  forall l head tailnext t next,
    GoodFunAsrt (sllseg head tailnext l t next).
Proof.
  inductions l; intros.
  simpl; auto.
  repeat (split;
          try (apply GoodFunAsrt_Aarray);
          try (apply GoodFunAsrt_Astruct);
          try (apply GoodFunAsrt_AEventData);
          try (apply GoodFunAsrt_evsllseg);
          try (apply GoodFunAsrt_tcbdllseg);
          try (apply GoodFunAsrt_dllseg);
          auto).
Qed.

Lemma GoodFunAsrt_sll :
  forall head l t next,
      GoodFunAsrt(sll head l t next).
Proof.
  intros.
  unfold sll.
  apply GoodFunAsrt_sllseg.
Qed.

Definition invlth_isr' (I:Inv) l h:=
  match leb l h with
    | true => atoy_inv'
    | false => Aemp
  end.

Lemma GoodFunAsrt_invlth_isr' :
  forall x l h,
    GoodFunAsrt (invlth_isr' x l h).
Proof.
  intros; unfold invlth_isr'.
  destruct (leb l h); simpl; auto.
Qed.


Ltac GoodFunAsrt_solver :=
  repeat (split;
          try (apply GoodFunAsrt_Aarray);
          try (apply GoodFunAsrt_Astruct);
          try (apply GoodFunAsrt_AEventData);
          try (apply GoodFunAsrt_evsllseg);
          try (apply GoodFunAsrt_tcbdllseg);
          try (apply GoodFunAsrt_dllseg);
          try (apply GoodFunAsrt_ecbf_sll);
          try (apply GoodFunAsrt_sll);
          try (apply GoodFunAsrt_qblkf_sll);
          try (apply GoodFunAsrt_invlth_isr');
          auto).
(*********************************)



Fixpoint nth_ectr (n : nat) (ll : list EventCtr) {struct ll} := 
  match ll with
  | nil => None
  | l :: ll' =>
      match n with
      | 0%nat => Some l
      | S n' => nth_ectr n' ll'
      end
  end.

(* OS_EventWaitListInit *)
(* pre *)

Open Scope code_scope.

Definition OS_EventWaitListInitPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX b  i1 i0 i2 x2 x3 v'22 v'24 s,
    Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) **
         Astruct (b,  Int.zero) OS_EVENT
         (Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: x2 :: x3 :: v'22 :: nil) **
         Aarray (b,  Int.zero+ᵢ($ 4+ᵢ($ 2+ᵢ($ 1+ᵢ($ 1+ᵢInt.zero)))))
         (Tarray Int8u ∘OS_EVENT_TBL_SIZE) v'24 ** A_isr_is_prop ** <||s||> **
         [| nth_val 0 vl = Some (Vptr (b, Int.zero)) /\ Int.unsigned i1 <= 255/\Int.unsigned i0 <= 255/\Int.unsigned i2 <= 65535 /\
            isptr x2 /\ isptr v'22 /\ logicl = logic_code s :: nil|] ** p_local OSLInv ct init_lg.



Theorem OS_EventWaitListInitPreGood (vl:vallist)  (logicl:list logicvar) ct:
  GoodFunAsrt (OS_EventWaitListInitPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.


Definition OS_EventWaitListInitPre : fpre :=
  fun vl ll ct=> mkfunasrt (OS_EventWaitListInitPreGood vl ll ct).


Notation INIT_EVENT_TBL :=
  (Vint32 Int.zero::
          Vint32 Int.zero::
          Vint32 Int.zero::
          Vint32 Int.zero::
          Vint32 Int.zero::
          Vint32 Int.zero::
          Vint32 Int.zero::
          Vint32 Int.zero::nil).


Definition OS_EventWaitListInitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX b i1 i2 x2 x3 v'22 s,
    Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) **
         Astruct (b, Int.zero) OS_EVENT
         (Vint32 i1 :: Vint32 Int.zero :: 
                 Vint32 i2 :: x2 :: x3 :: v'22 :: nil) **
         Aarray (b,  Int.zero+ᵢ($ 4+ᵢ($ 2+ᵢ($ 1+ᵢ($ 1+ᵢInt.zero)))))
         (Tarray Int8u ∘OS_EVENT_TBL_SIZE) INIT_EVENT_TBL ** A_isr_is_prop ** <||s||> **
         [| nth_val 0 vl = Some (Vptr (b, Int.zero)) /\ Int.unsigned i1 <= 255/\
            Int.unsigned i2 <= 65535 /\
            isptr x2 /\ isptr v'22 /\ v = None/\ logicl = logic_code s :: nil|] ** p_local OSLInv  ct init_lg.



Theorem OS_EventWaitListInitPostGood (vl:vallist) (v:option val) (logicl:list logicvar) ct:
  GoodFunAsrt (OS_EventWaitListInitPost' vl v logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.


Definition OS_EventWaitListInitPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_EventWaitListInitPostGood vl v ll ct).


Close Scope code_scope.
(*should be completed*)


(* OS_QPtrSearch *)
(* pre *)

Definition OS_EventSearchPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX msgql ectrl ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp mqls tcbls qid vhold s,
    Aie false  ** Ais nil ** Acs (true::nil) ** Aisr empisr **
    AECBList ectrl msgql mqls tcbls ** (* msgqlist *)
    AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ** (* tcblist *)
    tcbdllflag p1 (tcbl1 ++ tcbcur :: tcbl2) **
    AOSRdyTblGrp rtbl rgrp ** AOSTCBPrioTbl ptbl rtbl tcbls vhold** (* rdy table & prio table *)
    HECBList mqls ** HTCBList tcbls ** HCurTCB ct  (* high level *) **
     A_isr_is_prop ** <||s||> **
    [| RH_TCBList_ECBList_P mqls tcbls ct|] **
    [| nth_val 0 vl = Some (Vptr qid)|] **
    [| RH_CurTCB ct tcbls |] ** [|logicl = logic_code s::nil|] ** p_local OSLInv  ct init_lg.


Lemma GoodFunAsrt_tcbdllflag:
  forall  ls p,
    GoodFunAsrt (tcbdllflag p ls).
Proof.
  inductions ls.
  simpl.
  auto.
  intros.
  simpl.
  intros.
  unfold tcbdllflag in IHls.
  splits; auto.
Qed.

Theorem OS_EventSearchPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_EventSearchPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
  apply GoodFunAsrt_tcbdllflag; auto.
Qed.

Definition OS_EventSearchPre : fpre :=
  fun vl ll ct=> mkfunasrt (OS_EventSearchPreGood vl ll ct).

(* post *)

Definition OS_EventSearchPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  (EX msgqls ectrl1 ectrl2 msgqls1 msgqls2 ectrl ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp mqls tcbls qid p a b msgq vn mqls1 mqls2 mqls' mq vhold s,

  Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr **
      GV OSEventList @ (Tptr OS_EVENT)  |-> p ** 
      AEventNode (Vptr qid) a b msgq **
      evsllseg p (Vptr qid) ectrl1 msgqls1 **
      evsllseg vn Vnull ectrl2 msgqls2 **
       A_isr_is_prop **
      [|ECBList_P p Vnull ectrl msgqls mqls tcbls|] **
      [|ECBList_P p (Vptr qid) ectrl1 msgqls1 mqls1 tcbls|] **
      [|ECBList_P vn Vnull ectrl2 msgqls2 mqls2 tcbls|] **
      [| RLH_ECBData_P msgq mq |] ** 
      [| R_ECB_ETbl_P qid (a,b) tcbls |] **
      [| EcbMod.joinsig qid mq mqls2 mqls'/\ EcbMod.join mqls1 mqls' mqls |] **
      AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ** (* tcblist *)
      tcbdllflag p1 (tcbl1 ++ tcbcur :: tcbl2) **
      AOSRdyTblGrp rtbl rgrp ** AOSTCBPrioTbl ptbl rtbl tcbls vhold**(* rdy table & prio table *)
      HECBList mqls ** HTCBList tcbls ** HCurTCB ct  ** <||s ||> **  (* high level *) 
      [| RH_TCBList_ECBList_P mqls tcbls ct|] **
      [| RH_CurTCB ct tcbls |] **
      [| nth_val 0 vl = Some (Vptr qid)|] **
      [| ectrl = ectrl1 ++ ((a,b)::nil) ++ ectrl2 |] **
      [| msgqls = msgqls1 ++ (msgq::nil) ++msgqls2|] **
      [|length ectrl1 = length msgqls1 |] **
      [|V_OSEventListPtr a = Some vn|] **
      [| v = Some (V$1) |] ** [|logicl = logic_code s :: nil|] ** p_local OSLInv  ct init_lg) \\// 
   (EX  msgql ectrl ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp mqls tcbls  qid  vhold s,
    Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr **
        AECBList ectrl msgql mqls tcbls ** (* msgqlist *)
        AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ** (* tcblist *)
        tcbdllflag p1 (tcbl1 ++ tcbcur :: tcbl2) **
        AOSRdyTblGrp rtbl rgrp ** AOSTCBPrioTbl ptbl rtbl tcbls vhold** (* rdy table & prio table *)
        HECBList mqls ** HTCBList tcbls ** HCurTCB ct  ** <||s ||> **  (* high level *)
         A_isr_is_prop **
        [| RH_TCBList_ECBList_P mqls tcbls ct|] **
        [| RH_CurTCB ct tcbls |] **
        [| nth_val 0 vl = Some (Vptr qid)|] **
        [| (v = Some (V$0) /\  EcbMod.get mqls qid = None) |]
        ** [|logicl = logic_code s :: nil|]  ** p_local OSLInv  ct init_lg).


Theorem OS_EventSearchPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventSearchPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
 apply GoodFunAsrt_tcbdllflag; auto.
 apply GoodFunAsrt_tcbdllflag; auto.
Qed.

Definition OS_EventSearchPost : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_EventSearchPostGood vl v ll ct).

Fixpoint get_eid_ecbls (ecbls:list EventCtr):=
  match ecbls with
    | nil => nil 
    | (a,b)::ecbls' => (nth_val' 5 a) :: (get_eid_ecbls ecbls')
  end.

Definition get_eidls eid ecbls := eid::(List.removelast (get_eid_ecbls ecbls)).

Definition get_last_ptr (els : list EventCtr) :=
  match(last els (nil,nil)) with
    | (a,b) => V_OSEventListPtr a
  end.

Definition OS_EventRemovePre' (vl:vallist) (logicl:list logicvar) ct:= 
  EX (msgql1 msgql2 : list EventData)
     (ectrl1 ectrl2 : list EventCtr)  
     p qid s,
  Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr **
      GV OSEventList @ Tptr OS_EVENT |-> p **
      evsllseg p Vnull (ectrl1 ++ ectrl2) (msgql1 ++ msgql2) **
      A_isr_is_prop ** <||s||> **
      [|nth_val 0 vl = Some (Vptr qid) |] **
      [| length ectrl1 = length msgql1 |] **
      [| (ectrl1 = nil -> Vptr qid = p)
         /\ (ectrl1 <> nil -> Some (Vptr qid) = get_last_ptr ectrl1)|] ** 
      [| logicl = logic_val p ::  logic_leventc ectrl1 ::
                            logic_leventc ectrl2 :: logic_leventd msgql1 ::
                            logic_leventd msgql2 :: logic_code s ::
                            nil|]  ** p_local OSLInv  ct init_lg.

Theorem OS_EventRemovePreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_EventRemovePre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventRemovePre : fpre :=
  fun vl ll ct => mkfunasrt (OS_EventRemovePreGood vl ll ct).

(* post *)


Fixpoint update_nth  (t :  Type ) (n : nat) (vl : list t) (v : t) {struct vl} : list t :=
  match vl with
    | nil => nil
    | v' :: vl' =>
      match n with
      | 0%nat => v :: vl'
      | S n' => v' :: update_nth t n' vl' v
      end
  end.

Definition update_ectr (x : EventCtr)  (v : val) :=
  match x with
   | (a , b) => (update_nth _ 5%nat a v, b)
  end.

Fixpoint update_nth_ectrls (els : list EventCtr) (n: nat) (v:val) :=
  match els with
    | nil => nil
    | v' :: vl' =>
      match n with
        | 0%nat => (update_ectr v' v) :: vl'
        | S n' => v' :: update_nth_ectrls vl' n' v
      end
  end.


Definition upd_last_ectrls (els : list EventCtr) (v:val) :=
  update_nth_ectrls els (length els - 1)%nat v.



 Definition OS_EventPtrRemovePost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
 (EX (msgql1 msgql2 : list EventData)
     (ectrl1 ectrl2 ectrl1': list EventCtr) 
     p p' next  ectr msgq osevent etbl qid s,
  Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr **
      GV OSEventList @ Tptr OS_EVENT |-> p' **
      evsllseg p' Vnull (ectrl1'++ectrl2) (msgql1++msgql2) **
      AEventNode (Vptr qid) osevent etbl msgq **
       A_isr_is_prop ** <||s||> **
      [| logicl = logic_val p ::  logic_leventc ectrl1 ::
           logic_leventc  (ectr::ectrl2) :: logic_leventd msgql1 ::
                                logic_leventd (msgq::msgql2) ::logic_code s ::
                                 nil|]**
      [| nth_val 0 vl = Some (Vptr qid) |] **
      [| ectr = (osevent,etbl) |] **
      [| length ectrl1 = length msgql1 |] **
      [| Some next = V_OSEventListPtr osevent |] **
      [| (ectrl1 = nil -> (Vptr qid = p /\ p' = next /\ ectrl1' = nil))
       /\ (ectrl1 <> nil -> (p' = p /\ Some (Vptr qid) = get_last_ptr ectrl1 /\
       ectrl1' = upd_last_ectrls ectrl1 next))|]  ** p_local OSLInv  ct init_lg 
 ).



Theorem OS_EventPtrRemovePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventPtrRemovePost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventRemovePost : fpost :=
  fun vl v ll ct=> mkfunasrt (OS_EventPtrRemovePostGood vl v ll ct).

(* OS_EventTaskRdy *)
(* pre *)
Definition OS_EventTaskRdyPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX message msk vhold tcbls ptbl rtbl rgrp vltcb egrp qid osevent etbl d s head headprev tail tailnext,
  Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr **  A_isr_is_prop **
  AEventNode (Vptr qid) osevent etbl d ** (*has pure properties*)
  <||s||> **
  AOSUnMapTbl **
  AOSMapTbl **
  AOSRdyTblGrp rtbl rgrp ** (*has pure properties*)
  GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl **
  tcbdllseg head headprev tail tailnext vltcb **

  [| ptr_in_tcblist (Vptr ct) head vltcb |] **
  [| array_type_vallist_match (Tptr OS_TCB) ptbl /\ length ptbl = 64%nat |] **
  [| RL_RTbl_PrioTbl_P rtbl ptbl vhold |] **
  [| R_PrioTbl_P ptbl tcbls vhold |] **
  [| R_ECB_ETbl_P qid (osevent,etbl) tcbls |] **
  [| TCBList_P head vltcb rtbl tcbls |] **

  [| nth_val 0 vl = Some (Vptr qid) |] **
  [| nth_val 1 vl = Some message |] **
  [| nth_val 2 vl = Some (Vint32 msk) |] **
  
  [| V_OSEventGrp osevent = Some (Vint32 egrp) /\ egrp <> Int.zero |] **
  [| logicl = logic_val (Vptr vhold) :: logic_val head ::
              logic_val headprev :: logic_val tail :: logic_val tailnext ::
              logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp ::
              logic_lv osevent :: logic_lv etbl :: logic_leventd (d::nil) ::
              logic_code s :: logic_abstcb tcbls :: logic_llv vltcb ::
              logic_val (Vint32 egrp) :: nil |] ** p_local OSLInv ct init_lg.
  
Theorem OS_EventTaskRdyPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_EventTaskRdyPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskRdyPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_EventTaskRdyPreGood vl ll ct).

Fixpoint tcblist_get p head tcbl :=
  match tcbl with
    | nil => None
    | h::tcbl' =>
      if beq_val p head
      then
        Some h
      else
        match (V_OSTCBNext h) with
          | Some head' => tcblist_get p head' tcbl'
          | None => None
        end
  end.

Fixpoint set_node (p:val) (vl':vallist) (head:val) (l:list vallist) :=
  match l with
    | nil => nil
    | vl::l' =>
      if beq_val p head
      then vl'::l'
      else vl::set_node p vl' (nth_val' 0 vl) l'
  end.

Definition rel_edata_tcbstat edata tcbstat :=
  match edata with
    | DMsgQ _ _ _ _ =>
      tcbstat = Int.repr OS_STAT_Q
    | DSem _ =>
      tcbstat = Int.repr OS_STAT_SEM
    | DMbox _ =>
      tcbstat = Int.repr OS_STAT_MBOX
    | DMutex _ _ =>
      tcbstat = Int.repr OS_STAT_MUTEX
  end.

Open Scope int_scope.


Definition OS_EventTaskRdyPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX vhold tcbls vltcb vltcb' ptbl rtbl rtbl' rgrp rgrp' egrp egrp' etbl etbl' qid osevent osevent' d s head headprev tail tailnext message msk,
    Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop **
    AEventNode (Vptr qid) osevent' etbl' d ** <||s||> **
    AOSUnMapTbl **
    AOSMapTbl **
    AOSRdyTblGrp rtbl' rgrp' **

    GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl **    
    tcbdllseg head headprev tail tailnext vltcb' **

    [| nth_val 0 vl = Some (Vptr qid) |] **
    [| nth_val 1 vl = Some message |] **
    [| nth_val 2 vl = Some (Vint32 msk) |] **
    
    [| ptr_in_tcblist (Vptr ct) head vltcb'|] **
    [| array_type_vallist_match (Tptr OS_TCB) ptbl /\ length ptbl = 64%nat |] ** (*same as in pre*)
    [| RL_RTbl_PrioTbl_P rtbl' ptbl vhold |] **
    [| R_PrioTbl_P ptbl tcbls vhold |] ** (*same as in pre*)
    [| R_ECB_ETbl_P qid (osevent,etbl) tcbls |] ** (*same as in pre*)
    [| TCBList_P head vltcb rtbl tcbls |] ** (*same as in pre*)
    
    [| logicl = logic_val (Vptr vhold) :: logic_val head ::
                logic_val headprev :: logic_val tail :: logic_val tailnext ::
                logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp ::
                logic_lv osevent :: logic_lv etbl :: logic_leventd (d::nil) ::
                logic_code s :: logic_abstcb tcbls :: logic_llv vltcb ::
                logic_val (Vint32 egrp) :: nil |] **

    EX x y i1 bitx bity,
    [| nth_val' (Z.to_nat (Int.unsigned egrp)) OSUnMapVallist = Vint32 y |] **
    [| nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 i1 |] **
    [| nth_val' (Z.to_nat (Int.unsigned i1)) OSUnMapVallist = Vint32 x |] **
    [| nth_val' (Z.to_nat (Int.unsigned y)) OSMapVallist = Vint32 bity |] **
    [| nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 bitx |] **
    
    (* osevent' etbl' egrp' *)
    (* osevent' = osevent set egrp to egrp'
       etbl' = etbl clear highest bit
       RL_Tbl_Grp_P etbl' egrp' (in AOSEvent)
     *)
    [| osevent' = update_nth_val 1 osevent (Vint32 egrp') |] **
    [| etbl' = update_nth_val
                 (Z.to_nat (Int.unsigned y)) etbl (Vint32 (i1&ᵢInt.not bitx)) |] **
              
    (*ret value prio = get highest wait task in etbl*)
    [| v = Some (Vint32 ((y<<ᵢ$ 3)+ᵢx)) |] **

    (*relation between old vltcb and new vltcb*)
    (EX vl vl' next prev eptr msg dly stat prio tcbx tcby tcbbitx tcbbity t,
     [| nth_val' (Z.to_nat (Int.unsigned ((y<<ᵢ$ 3)+ᵢx))) ptbl  = (Vptr (t, Int.zero))
        /\ (t, Int.zero) <> vhold|] **
    [| tcblist_get (Vptr (t, Int.zero)) head vltcb = Some vl /\ struct_type_vallist_match OS_TCB_flag vl|] **
    [| vltcb' = set_node (Vptr (t, Int.zero)) vl' head vltcb |] **
    [| vl = next::prev::eptr::msg::dly::(Vint32 stat)::prio::tcbx::tcby::tcbbitx::tcbbity::nil|] **
    [| vl' = next::prev::Vnull::message::(Vint32 Int.zero)::(Vint32 (Int.and stat (Int.not msk)))::prio::tcbx::tcby::tcbbitx::tcbbity::nil|] **

    (*relation between data and tcbstat, for proving tcb rdy*)
    [| rel_edata_tcbstat d stat |]
    ) **
    
    (*rtbl' rgrp'*)
    (*rtbl' = rtbl set bit prio
      RL_Tbl_Grp_P rtbl' rgrp' *)
    (EX i1', [| nth_val' (Z.to_nat (Int.unsigned y)) rtbl = Vint32 i1' |] **    
      [| rtbl' = update_nth_val (Z.to_nat (Int.unsigned y)) rtbl (Vint32 (Int.or i1' bitx))|]) **
    
 (*pure properties on old values in AOSRdyTblGrp, keep them in the post condition *)
    [|RL_Tbl_Grp_P rtbl rgrp /\ prio_in_tbl ($ OS_IDLE_PRIO) rtbl|] **
    [|array_type_vallist_match Tint8 rtbl /\ length rtbl = nat_of_Z OS_RDY_TBL_SIZE|] **
    [|rule_type_val_match Tint8 rgrp = true|] **
    [|RL_Tbl_Grp_P etbl (Vint32 egrp)|] **
    [|array_type_vallist_match Tint8 etbl|]
    ** p_local OSLInv  ct init_lg.


Theorem OS_EventTaskRdyPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventTaskRdyPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskRdyPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_EventTaskRdyPostGood vl v ll ct).

(* OS_EventTaskWait *)
(* pre *)
Definition OS_EventTaskWaitPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX tcbcur rtbl rgrp qid osevent etbl d s,
   <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr **
    GV OSTCBCur @ Tptr OS_TCB |-r-> (Vptr ct) **
    node (Vptr ct) tcbcur OS_TCB_flag ** (*modified by zhanghui*)  (* OSTCBCur node *)
    [| RL_TCBblk_P tcbcur |] **
      AOSRdyTblGrp rtbl rgrp ** AEventNode (Vptr qid) osevent etbl d **
    [| logicl =logic_lv rtbl :: logic_val rgrp :: logic_lv tcbcur :: logic_lv osevent ::
                logic_lv etbl :: logic_leventd (d::nil) :: logic_code s :: nil |] **
    [| nth_val 0 vl = Some (Vptr qid) /\ (exists p,V_OSTCBPrio tcbcur = Some (Vint32 p) /\ Int.eq p ($ OS_IDLE_PRIO) = false) |] ** p_local OSLInv  ct init_lg.


Theorem OS_EventTaskWaitPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_EventTaskWaitPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskWaitPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_EventTaskWaitPreGood vl ll ct).

(* post *)
Definition OS_EventTaskWaitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:= 
  (EX tcbcur rtbl rgrp qid osevent etbl d
     tcbcur' rtbl' rgrp' osevent' etbl'
     y bitx bity ry ey egrp s,
  Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr **
    GV OSTCBCur @ Tptr OS_TCB |-r-> (Vptr ct) **
    node (Vptr ct) tcbcur' OS_TCB_flag (*modified by zhanghui*) ** (* OSTCBCur node *) 
    AOSRdyTblGrp rtbl' (Vint32 rgrp') ** AEventNode (Vptr qid) osevent' etbl' d **
    <||s||> **
    [| logicl = logic_lv rtbl :: logic_val (Vint32 rgrp) :: logic_lv tcbcur :: logic_lv osevent ::
                logic_lv etbl :: logic_leventd (d::nil) :: logic_code s :: nil |] **
    [| nth_val 0 vl = Some (Vptr qid) |] ** 
    [| tcbcur' = update_nth_val 2 tcbcur (Vptr qid) /\ 
       V_OSTCBY tcbcur = Some (Vint32 y) /\
       V_OSTCBBitX tcbcur = Some (Vint32 bitx) /\
       V_OSTCBBitY tcbcur = Some (Vint32 bity) /\
       nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 ry) /\
       rtbl' = update_nth_val (nat_of_Z (Int.unsigned y)) rtbl (Vint32 (Int.and ry (Int.not bitx))) /\
       nth_val (nat_of_Z (Int.unsigned y)) etbl = Some (Vint32 ey) /\ 
       etbl' = update_nth_val (nat_of_Z (Int.unsigned y)) etbl (Vint32 (Int.or ey bitx)) /\
       V_OSEventGrp osevent = Some (Vint32 egrp) /\
       osevent' = update_nth_val 1 osevent (Vint32 (Int.or egrp bity)) |] ** p_local OSLInv  ct init_lg).



Theorem OS_EventTaskWaitPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_EventTaskWaitPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_EventTaskWaitPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_EventTaskWaitPostGood vl v ll ct).



Definition OS_SchedPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX s v, Aie true ** Ais nil ** Acs nil ** Aisr empisr **
      <||isched;;s||> ** [|logicl = logic_code s :: nil|]  ** p_local OSLInv ct (logic_val v :: nil) ** [| isflag v |].

Definition OS_SchedPost' (vl:vallist) (v:option val)  (logicl:list logicvar) ct:=
    EX s, Aie true ** Ais nil ** Acs nil ** Aisr empisr **
        <||s||> ** [|logicl = logic_code s :: nil|]  ** p_local OSLInv ct init_lg.

Theorem OS_SchedPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_SchedPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Theorem OS_SchedPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_SchedPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_SchedPre : fpre :=
  fun vl ll ct => mkfunasrt (OS_SchedPreGood vl ll ct).

Definition OS_SchedPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_SchedPostGood vl v ll ct).

(* OSIntExit *)

(*
Definition fx is (O : osabst)  := is_nest is = false.
Definition nfx is  (O : osabst)  := is_nest is = true.
 *)

Definition OSIntExitPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX ir ie si i v, [|logicl=  (logic_isr ir) :: (logic_ie ie) ::
                                           (logic_is si) :: (logic_hid i) :: (logic_val v) :: nil |] ** Aisr (isrupd ir i%nat false) **
       Aie ie **
       Ais (i%nat :: si) **
       Acs nil ** <|| (isched;; END None ?? END None)||> **
       [| isr_is_prop (isrupd ir i%nat false) (i%nat :: si) |] **
       [| (i <= INUM)%nat /\ (forall j : nat, (0 <= j < i)%nat ->  (isrupd ir i%nat false) j = false) |] **
       ((
       (EX (eventl osql qblkl : list vallist) (msgql : list EventData)
           (ectrl : list EventCtr) (ptbl : vallist) (p1 p2 : val) 
           (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
           (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
           (tcbls : TcbMod.map) (t : int32) pf lf vhold,
        AOSEventFreeList eventl **
                         AOSQFreeList osql **
                         AOSQFreeBlk qblkl **
                         AECBList ectrl msgql ecbls tcbls **
                         AOSMapTbl **
                         AOSUnMapTbl **
                         AOSTCBPrioTbl ptbl rtbl tcbls vhold**
                         AOSIntNesting **
                         AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf**
                         AOSTCBFreeList' pf lf ct tcbls **
                         AOSRdyTblGrp rtbl rgrp **
                         AOSTime (Vint32 t) **
                         HECBList ecbls **
                         HTCBList tcbls **
                         HTime t **
                         HCurTCB ct **
                         AGVars **
                         [|RH_TCBList_ECBList_P ecbls tcbls ct|] ) ** invlth_isr' I 1%nat i%nat ** [| ie = false |] )\\//[|ie=true|])  ** p_local OSLInv ct (logic_val v :: nil) ** [| isflag v |].

Definition OSIntExitPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
  EX ir ie si i lv, [|logicl=  (logic_isr ir) :: (logic_ie ie)
                                           :: (logic_is si) :: (logic_hid i) :: (logic_val lv) :: nil |]  ** ((Aisr (isrupd ir i%nat false)**
       Aie ie **
       Ais (i%nat :: si) **
       Acs nil ** <||END None||> **
       [| isr_is_prop (isrupd ir i%nat false) (i%nat :: si) |] **
       [| (i<=INUM)%nat |] **
       ((
       (EX (eventl osql qblkl : list vallist) (msgql : list EventData)
           (ectrl : list EventCtr) (ptbl : vallist) (p1 p2 : val) 
           (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
           (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
           (tcbls : TcbMod.map) (t : int32) pf lf vhold,
        AOSEventFreeList eventl **
                         AOSQFreeList osql **
                         AOSQFreeBlk qblkl **
                         AECBList ectrl msgql ecbls tcbls **
                         AOSMapTbl **
                         AOSUnMapTbl **
                         AOSTCBPrioTbl ptbl rtbl tcbls vhold**
                         AOSIntNesting **
                         AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf **
                         AOSTCBFreeList' pf lf ct tcbls**
                         AOSRdyTblGrp rtbl rgrp **
                         AOSTime (Vint32 t) **
                         HECBList ecbls **
                         HTCBList tcbls **
                         HTime t **
                         HCurTCB ct **
                         AGVars **
                         [|RH_TCBList_ECBList_P ecbls tcbls ct|] ) ** invlth_isr' I 1%nat i%nat ** [| ie = false |]) \\// [|ie = true |])  **  p_local OSLInv ct ((logic_val lv)::nil) ** [|lv = Vint32 ($ 1) \/ si <> nil |]) \\// ( [|lv = Vint32 ($ 0) /\ si = nil |] ** Afalse)).

(* ** ac: Check tcbdllflag. *)
(* ** ac: Check GoodFunAsrt_tcbdllflag. *)
Lemma GoodFunAsrt_sllfreeflag :
  forall l x,
    GoodFunAsrt (sllfreeflag x l).
  unfold sllfreeflag.
  induction l.

  intros.
  unfold sllsegfreeflag.
  simpl.
  auto.

  intros.
  simpl.
  intros.
  split; auto.
Qed.
  
(* ** ac: Print Ltac GoodFunAsrt_solver. *)

Local Ltac GoodFunAsrt_solver ::=
  repeat
   (split; try apply GoodFunAsrt_Aarray;
     try apply GoodFunAsrt_Astruct;
     try apply GoodFunAsrt_AEventData;
     try apply GoodFunAsrt_evsllseg;
     try apply GoodFunAsrt_tcbdllseg; try apply GoodFunAsrt_dllseg;
     try apply GoodFunAsrt_ecbf_sll; try apply GoodFunAsrt_sll;
     try apply GoodFunAsrt_qblkf_sll;
     try apply GoodFunAsrt_invlth_isr';
     try apply GoodFunAsrt_tcbdllflag;
     try apply GoodFunAsrt_sllfreeflag;
     auto).

Theorem OSIntExitPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSIntExitPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Theorem OSIntExitPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSIntExitPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.


Definition OSIntExitPre : fpre :=
  fun vl ll ct => mkfunasrt (OSIntExitPreGood vl ll ct).

Definition OSIntExitPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSIntExitPostGood vl v ll ct).

(* OS_PrioChange *)
Definition OS_PrioChangePre' (vl:vallist) (logicl:list logicvar) (ct:tid):=
  EX ptcb prio pip next pre eptr msg dly stat p x y bitx bity rtbl rgrp ptbl vhold s,
  <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr **
     [| vl = (Vptr ptcb)::(Vint32 prio)::(Vint32 pip)::nil|] **
     [|logicl = (logic_val next)::(logic_val pre)::(logic_val eptr) :: (logic_val msg) :: (logic_val dly) :: (logic_val stat) :: (logic_val p) :: (logic_val x) :: (logic_val y) :: (logic_val bitx) :: (logic_val bity) :: (logic_lv rtbl) :: (logic_val rgrp) :: (logic_lv ptbl) :: (logic_val (Vptr vhold)) :: (logic_code s) :: nil|] **
     [| struct_type_vallist_match OS_TCB (next::pre::eptr::msg::dly::stat::p::x::y::bitx::bity::nil) |] **
     [| 0 <= Int.unsigned prio < 64 |] **
     [| 0 <= Int.unsigned pip < 64 |] **
     [| RL_TCBblk_P (next::pre::eptr::msg::dly::stat::p::x::y::bitx::bity::nil) |] **
     Astruct ptcb OS_TCB
     (next::pre::eptr::msg::dly::stat::p::x::y::bitx::bity::nil) **
     AOSRdyTblGrp rtbl rgrp **
     GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl  **
     G&OSPlaceHolder @ (Tint8) == vhold **
     AOSMapTbl.


Definition OS_PrioChangePost' (vl:vallist) (v:option val) (logicl:list logicvar) (ct:tid):=Aemp.
   (*
  EX ptcb prio pip next pre eptr msg dly stat p x y bitx bity rtbl rgrp ptbl vhold s x' y' bitx' bity' rtbl' rgrp' ptbl' x12 x11 x8,
  <||s||> ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr **
     [| vl = (Vptr ptcb)::(Vint32 prio)::(Vint32 pip)::nil|] **
     [|logicl = (logic_val next)::(logic_val pre)::(logic_val eptr) :: (logic_val msg) :: (logic_val dly) :: (logic_val stat) :: (logic_val p) :: (logic_val x) :: (logic_val y) :: (logic_val bitx) :: (logic_val bity) :: (logic_lv rtbl) :: (logic_val rgrp) :: (logic_lv ptbl) :: (logic_val (Vptr vhold)) :: (logic_code s) :: nil|] **
     [| struct_type_vallist_match OS_TCB (next::pre::eptr::msg::dly::stat::p::x::y::bitx::bity::nil) |] **
     [| 0 <= Int.unsigned prio < 64 |] **
     [| 0 <= Int.unsigned pip < 64 |] **
     [| x' = (Int.and prio ($7)) |] **
     [| y' = (Int.shru prio ($3)) |] **
     [| bity' = nth_val' (Z.to_nat (Int.unsigned y')) OSMapVallist |] **
     [| bitx' = nth_val' (Z.to_nat (Int.unsigned x')) OSMapVallist |] **
     [| nth_val' (Z.to_nat (Int.unsigned (pip>>ᵢ$ 3))) rtbl = Vint32 x12 |] **
     [| nth_val' (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3))) rtbl = Vint32 x8 |] **
     [| nth_val' (Z.to_nat (Int.unsigned (prio&$ 7))) rtbl = Vint32 x11 |] **
     [| rtbl' =  (update_nth_val
          (Z.to_nat (Int.unsigned (prio >>ᵢ $ 3)))
          (update_nth_val (Z.to_nat (Int.unsigned pip)) rtbl
             (val_inj (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(pip&$ 7)))))))
          (val_inj
             (or
                (nth_val'
                   (Z.to_nat
                      (Int.unsigned ((prio)>>ᵢ$ 3)))
                   (update_nth_val (Z.to_nat (Int.unsigned (pip>>ᵢ$ 3))) rtbl
                      (val_inj
                         (and (Vint32 x12) (Vint32 (Int.not ($ 1<<(pip&$ 7))))))))
                (Vint32 x11)))) |] **
(*     [| rgrp' = rgrp |] ** *)
     [| ptbl' = (update_nth_val (Z.to_nat (Int.unsigned pip))
          (update_nth_val
             (Z.to_nat (Int.unsigned prio)) ptbl
             (Vptr ptcb)) (Vptr vhold)) |] **
     [| RL_TCBblk_P (next::pre::eptr::msg::dly::stat::(Vint32 prio)::(Vint32 x')::(Vint32 y')::bitx'::bity'::nil) |] **
     Astruct ptcb OS_TCB
     (next::pre::eptr::msg::dly::stat::(Vint32 prio)::(Vint32 x')::(Vint32 y')::bitx'::bity'::nil) **
     AOSRdyTblGrp rtbl' rgrp' **
     GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) ptbl'  **
     G&OSPlaceHolder @ (Tint8) == vhold **
     AOSMapTbl.
*)

Theorem OS_PrioChangePreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_PrioChangePre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Theorem OS_PrioChangePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_PrioChangePost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.


Definition OS_PrioChangePre : fpre :=
  fun vl ll ct => mkfunasrt (OS_PrioChangePreGood vl ll ct).

Definition OS_PrioChangePost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_PrioChangePostGood vl v ll ct).

(* Time Tick *)
Open Scope code_scope.

Definition OSTimeTickPre' (vl:vallist) (logicl:list logicvar) ct:=
   EX isrr si v'5 v'7, EX v'8 v'9 v'10 v'11 v'14 v'17 v'18 tcbls tcbls1 tcbls2 v'3 v'2 v'12 v'15 s ctx v,  
   [|logicl = (logic_isr isrr) :: (logic_is si) ::
     logic_val (Vint32 v'14) :: (logic_val (Vptr v'5))  ::  (logic_val (Vptr v'5)) :: (logic_llv v'7) ::
     (logic_lv v'8) :: (logic_llv v'9) :: (logic_lv v'10) :: (logic_val v'11) ::
     (logic_val v'17) :: (logic_val v'18) :: (logic_abstcb tcbls) ::
     (logic_abstcb tcbls1) :: (logic_abstcb tcbls2) :: (logic_leventc v'3) :: (logic_leventd v'2) ::
     (logic_absecb v'12):: logic_code s ::logic_val (Vptr ctx):: logic_val v:: nil|] **
     Aisr (isrupd isrr 0%nat false) **
     Aie false **
     Ais (0%nat :: si) **
     Acs nil **
     <||s||> **
     GV OSTCBList @ OS_TCB ∗ |-> (Vptr v'5) **
     tcbdllseg (Vptr v'5) Vnull v'17 (Vptr ctx) v'7 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> (Vptr ct) **
     tcbdllseg (Vptr ctx) v'17 v'18 Vnull (v'8 :: v'9) **
     [|TcbMod.join tcbls1 tcbls2 tcbls|] **
     [|TCBList_P (Vptr v'5) v'7 v'10 tcbls1|] ** [|TCBList_P (Vptr ctx) (v'8::v'9) v'10 tcbls2|] ** 
     AOSRdyTblGrp v'10 v'11 **
     GV OSTime @ Int32u |-> (Vint32 v'14)**
     AECBList v'3 v'2 v'12 tcbls **
     [| RH_TCBList_ECBList_P v'12 tcbls v'15 |]   ** p_local OSLInv ct (logic_val v :: nil) ** [| isflag v |].


Definition tmdly_sub_1 (vl:vallist):=
  match nth_val 4%nat vl with
    | Some (Vint32 v) => Some (update_nth_val 5%nat vl (Vint32 (Int.sub v Int.one)))
    | _ => None
  end.

Definition set_rdy_grp tcbbity rgrp := bop_eval rgrp tcbbity Tint8 Tint8 obitor.

Definition nth_val_vallist tcby rtbl:=
  match tcby with
    | Vint32 v => nth_val (Z.to_nat (Int.unsigned v)) rtbl
    | _ => None
  end.

Definition set_rdy_tbl tcbbitx tcby rtbl:=
  match tcby with
    | Vint32 vi => 
      match nth_val (Z.to_nat (Int.unsigned vi)) rtbl with
        | Some v => match bop_eval v tcbbitx Tint8 Tint8 obitor with
                      | Some v' => Some (update_nth_val (Z.to_nat (Int.unsigned vi)) rtbl v')
                      | None => None
                    end
        | None => None
      end
    | _ => None
  end. 

Definition add_option_first (vl:vallist) (tri: option ((list vallist)*vallist*val*(list EventCtr))):=
  match tri with
    | Some (a,b,c,d) => Some (vl::a,b,c,d)
    | _ => None
  end.

Definition set_rdy (vl:vallist):=
  update_nth_val 3%nat (update_nth_val 6%nat vl (Vint32 (Int.repr OS_STAT_RDY))) Vnull.

Definition beq_addrval := 
fun n m : addrval =>
  let (b, i) := n in let (b', i') := m in beq_pos b b' && Int.eq i i'.


Definition rdy_ectr (vl:vallist) (ectr:EventCtr) :option EventCtr:=
  match ectr with
    | (v1::Vint32 v2::v3::v4::v5::v6::nil,etbl) =>
      match V_OSTCBY vl, (V_OSTCBBitX vl), (V_OSTCBBitY vl) with
        | Some (Vint32 y),Some (Vint32 bitx),Some (Vint32 bity) =>
          match nth_val' (Z.to_nat (Int.unsigned y)) etbl with
            | Vint32 xx =>
              match Int.eq (xx&ᵢInt.not bitx) ($ 0) with
                | true => Some (v1::Vint32 (v2&ᵢInt.not bity)::v3::v4::v5::v6::nil,
                                update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (xx&ᵢInt.not bitx)))
                | false => Some (v1::Vint32 v2::v3::v4::v5::v6::nil,
                                update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (xx&ᵢInt.not bitx)))
              end
            | _ => None
          end
        | _,_,_ => None
      end
    | _ => None
  end.


Fixpoint tick_rdy_ectr' (e:addrval) (vl:vallist) (head:val) (ectrl:list EventCtr) :=
  match head with
    | (Vptr e') =>
      match ectrl with
        |(osevent, etbl)::vll =>
         match beq_addrval e e' with
           | true => match (rdy_ectr vl (osevent, etbl)) with
                       | Some x => Some (x :: vll)
                       | None => None
                     end
           | false => match V_OSEventListPtr osevent with
                        | Some vn => match (tick_rdy_ectr' e vl vn vll) with
                                       | Some x => Some ((osevent, etbl)::x)
                                       | None => None
                                     end
                        | _ => None
                      end
         end
        | _ => Some ectrl
      end
    | Vnull => Some ectrl
    | _=> None
  end.


Definition tick_rdy_ectr (vl:vallist) (head:val) (ectrl:list EventCtr) :=
  match nth_val 2%nat vl with
    | Some (Vptr eid) => tick_rdy_ectr' eid vl head ectrl
    | Some (Vnull) => Some ectrl
    | _ => None
  end.

Fixpoint tcbls_rtbl_timetci_update (vll:list vallist) (rtbl:vallist) (rgrp:val) (head:val) (ectrl:list EventCtr) :=
  match vll with
    | nil => Some ((nil:list vallist),rtbl,rgrp,ectrl)
    | vl::vll' =>
      match vl with
        | (vnext :: vprev ::
           eid :: msg :: Vint32 vdly ::
           stat :: (Vint32 prio) ::
           (Vint32 vx) :: (Vint32 vy) ::
           (Vint32 vbitx) :: (Vint32 vbity) :: nil) =>
          match Int.eq vdly Int.zero with
            | true => add_option_first vl (tcbls_rtbl_timetci_update vll' rtbl rgrp head ectrl)
            | false =>
              match Int.eq (Int.sub vdly Int.one) Int.zero with
                | true =>
                  match set_rdy_grp (Vint32 vbity) rgrp with
                    | Some (Vint32 rgrp') =>
                      match set_rdy_tbl (Vint32 vbitx) (Vint32 vy) rtbl with
                        | Some rtbl' =>
                          match eid with
                            | Vnull =>
                              add_option_first
                                (vnext :: vprev ::
                                 eid :: msg :: Vint32 (Int.sub vdly Int.one) ::
                                 (Vint32 (Int.repr OS_STAT_RDY)) :: (Vint32 prio) ::
                                 (Vint32 vx) :: (Vint32 vy) ::
                                 (Vint32 vbitx) :: (Vint32 vbity) :: nil)
                                (tcbls_rtbl_timetci_update vll' rtbl' (Vint32 rgrp') head ectrl)
                            | Vptr eptr =>
                              match (tick_rdy_ectr vl head ectrl) with
                                | Some x => add_option_first
                                              (vnext :: vprev ::
                                                     Vnull:: msg :: Vint32 (Int.sub vdly Int.one) ::
                                                     (Vint32 (Int.repr OS_STAT_RDY)) :: (Vint32 prio) ::
                                                     (Vint32 vx) :: (Vint32 vy) ::
                                                     (Vint32 vbitx) :: (Vint32 vbity) :: nil)
                                              (tcbls_rtbl_timetci_update vll' rtbl' (Vint32 rgrp') head x)
                                | _ => None
                              end
                            | _ => None
                          end
                        | _ => None
                      end
                    | _ => None
                  end
                | false => add_option_first
                             (vnext :: vprev ::
                                    eid :: msg :: Vint32 (Int.sub vdly Int.one) ::
                                    stat :: (Vint32 prio) ::
                                    (Vint32 vx) :: (Vint32 vy) ::
                                    (Vint32 vbitx) :: (Vint32 vbity) :: nil)
                             (tcbls_rtbl_timetci_update vll' rtbl rgrp head ectrl)
              end
          end
        | _ => None
      end
  end.

Inductive  tickchange_l: vallist -> vallist -> val -> val -> list EventCtr -> vallist -> vallist -> val  -> list EventCtr -> Prop:=
| rdy_change_l: forall vnext vprev eid msg vdly stat prio vx vy vbitx vbity l rtbl rgrp head ectr,
                  l = (vnext :: vprev ::
                             eid :: msg :: Vint32 vdly ::
                             stat :: (Vint32 prio) ::
                             (Vint32 vx) :: (Vint32 vy) ::
                             (Vint32 vbitx) :: (Vint32 vbity) :: nil) ->
                  Int.eq vdly Int.zero = true ->
                  tickchange_l l rtbl rgrp head ectr l rtbl rgrp ectr
(* 'wait_change' and 'waite_change' *)
| wait_change_l: forall vnext vprev eid msg vdly stat prio vx vy vbitx vbity l l' rtbl rgrp head ectr,
                  l = (vnext :: vprev ::
                             eid :: msg :: Vint32 vdly ::
                             stat :: (Vint32 prio) ::
                             (Vint32 vx) :: (Vint32 vy) ::
                             (Vint32 vbitx) :: (Vint32 vbity) :: nil) ->
                  Int.eq vdly Int.zero = false ->
                  Int.eq (Int.sub vdly Int.one) Int.zero = false ->
                  l' =  (vnext :: vprev ::
                               eid:: msg :: Vint32 (Int.sub vdly Int.one) ::
                              stat :: (Vint32 prio) ::
                               (Vint32 vx) :: (Vint32 vy) ::
                               (Vint32 vbitx) :: (Vint32 vbity) :: nil)->
                  tickchange_l l rtbl rgrp head ectr l' rtbl rgrp ectr
| wait_rdy_change_l: forall vnext vprev eid msg vdly stat prio vx vy vbitx vbity
                            l l' rtbl rgrp head ectr rgrp' rtbl',
                       l = (vnext :: vprev ::
                                  eid :: msg :: Vint32 vdly ::
                                  stat :: (Vint32 prio) ::
                                  (Vint32 vx) :: (Vint32 vy) ::
                                  (Vint32 vbitx) :: (Vint32 vbity) :: nil) ->
                  Int.eq vdly Int.zero = false ->
                  Int.eq (Int.sub vdly Int.one) Int.zero = true ->
                  l' =  (vnext :: vprev ::
                               Vnull:: msg :: Vint32 (Int.sub vdly Int.one) ::
                               (Vint32 (Int.repr OS_STAT_RDY)) :: (Vint32 prio) ::
                               (Vint32 vx) :: (Vint32 vy) ::
                               (Vint32 vbitx) :: (Vint32 vbity) :: nil) ->
                  eid = Vnull ->
                  set_rdy_grp (Vint32 vbity) rgrp = Some rgrp' ->
                  set_rdy_tbl (Vint32 vbitx) (Vint32 vy) rtbl = Some rtbl' ->
                  tickchange_l l rtbl rgrp head ectr l' rtbl' rgrp' ectr
| waite_rdy_change_l:  forall vnext vprev eid msg vdly stat prio vx vy vbitx vbity
                            l l' rtbl rgrp head ectr rgrp' rtbl' eptr ectr',
                    l = (vnext :: vprev ::
                               eid :: msg :: Vint32 vdly ::
                               stat :: (Vint32 prio) ::
                               (Vint32 vx) :: (Vint32 vy) ::
                               (Vint32 vbitx) :: (Vint32 vbity) :: nil) ->
                    Int.eq vdly Int.zero = false ->
                    Int.eq (Int.sub vdly Int.one) Int.zero = true ->
                    l' =  (vnext :: vprev ::
                                 Vnull:: msg :: Vint32 (Int.sub vdly Int.one) ::
                                 (Vint32 (Int.repr OS_STAT_RDY)) :: (Vint32 prio) ::
                                 (Vint32 vx) :: (Vint32 vy) ::
                                 (Vint32 vbitx) :: (Vint32 vbity) :: nil) ->
                    eid = Vptr eptr ->
                    set_rdy_grp (Vint32 vbity) rgrp = Some rgrp' ->
                    set_rdy_tbl (Vint32 vbitx) (Vint32 vy) rtbl = Some rtbl' ->
                    tick_rdy_ectr l head ectr = Some ectr' -> 
                    tickchange_l l rtbl rgrp head ectr l' rtbl' rgrp' ectr'.

Inductive tickstep_l: list vallist -> vallist -> val -> val -> list EventCtr -> list vallist -> vallist -> val  -> list EventCtr -> Prop :=
| emp_update: forall rtbl rgrp head ectr,
                tickstep_l nil rtbl rgrp head ectr nil rtbl rgrp ectr
| tl_update: forall l ll rtbl rgrp head ectr l' ll' rtbl' rgrp' ectr' rtbl'' rgrp'' ectr'',
               tickchange_l l rtbl rgrp head ectr l' rtbl' rgrp' ectr' ->
               tickstep_l ll rtbl' rgrp' head ectr' ll' rtbl'' rgrp'' ectr'' ->
               tickstep_l (l::ll) rtbl rgrp head ectr (l'::ll') rtbl'' rgrp'' ectr''.

                    
Definition OSTimeTickPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:= 
   EX isrr si v'5  v'7, EX v'8 v'9 v'10 v'11 v'14 v'17 v'18  rtbl' rgrp' v'15 tcbls tcbls1 tcbls2 i v'20 v'3 v'2 ectrl' v'12 s ctx v,  
   [|logicl = (logic_isr isrr) :: (logic_is si) :: (logic_val (Vint32 v'14)) ::
              (logic_val (Vptr v'5)) ::   (logic_val (Vptr v'5)) ::
              (logic_llv v'7) :: (logic_lv v'8) :: (logic_llv v'9) :: (logic_lv v'10) ::
              (logic_val v'11) :: (logic_val v'17) :: (logic_val v'18) :: (logic_abstcb tcbls) ::
              (logic_abstcb tcbls1) :: (logic_abstcb tcbls2) ::  (logic_leventc v'3) :: (logic_leventd v'2) ::
              (logic_absecb v'12)::logic_code s ::logic_val (Vptr ctx)::logic_val v:: nil|] **
    [| array_type_vallist_match Int8u v'10|] **
    [| length v'10 = ∘OS_RDY_TBL_SIZE |] **
    [| v'11 = Vint32 i|] **                                                                                                                                                                                                  [| Int.unsigned i <= 255 |] **
    [| RL_Tbl_Grp_P v'10 v'11 |] **
    [| v'7 = nil /\ (Vptr ctx) = Vptr v'5 \/
                    (exists vl, v'7 <> nil /\ last v'7 nil = vl /\ nth_val 0 vl = Some (Vptr ctx)) |] **
    Aisr (isrupd isrr 0%nat false) **
    Aie false **
    Ais (0%nat :: si) **
    Acs nil **
    <||s||> **
    GV OSTCBList @ OS_TCB ∗ |-> (Vptr v'5) **
    GV OSEventList @ OS_EVENT ∗ |-> v'20 **
    evsllseg v'20 Vnull ectrl' v'2 **
    tcbdllseg (Vptr v'5) Vnull v'18 Vnull v'15 **
    [|TcbMod.join tcbls1 tcbls2 tcbls|] **
    [|TCBList_P (Vptr v'5) v'7 v'10 tcbls1|] ** [|TCBList_P (Vptr ctx) (v'8::v'9) v'10 tcbls2|] **
    [|ECBList_P v'20 Vnull v'3 v'2 v'12 tcbls|] **
    GV OSTCBCur @ OS_TCB ∗ |-r-> (Vptr ct) **
    GAarray OSRdyTbl (Tarray Int8u ∘OS_RDY_TBL_SIZE) rtbl' **
    GV OSRdyGrp @ Int8u |-> rgrp' **
    GV OSTime @ Int32u |-> Vint32 (Int.add v'14 Int.one) **
    [| tcbls_rtbl_timetci_update (v'7++(v'8::v'9)) v'10 v'11 v'20 v'3= Some (v'15,rtbl',rgrp',ectrl')|] **
    [| prio_in_tbl ($ OS_IDLE_PRIO) rtbl'|]  ** p_local OSLInv ct (logic_val v :: nil) ** [| isflag v |]
.

Theorem OSTimeTickPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSTimeTickPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Theorem OSTimeTickPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSTimeTickPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OSTimeTickPre : fpre :=
  fun vl ll ct => mkfunasrt (OSTimeTickPreGood vl ll ct).

Definition OSTimeTickPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSTimeTickPostGood vl v ll ct).


(*OS_TCBInit*)

Definition OS_TCBInitPre' (vl:vallist) (logicl:list logicvar) (ct:tid):=
  EX (ptfree:val) (lfree:list vallist) (rtbl:vallist) (ptbl:vallist) (rgrp:val) (p1 tail1 tail2:val) (l1 l2:list vallist) (prio: priority) (vhold: addrval) s vholdx,
      Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop **
      AOSTCBFreeList ptfree lfree **
      AOSMapTbl **
      <||s||> **
      [|nth_val 0 vl = Some (Vint32 prio) /\ Int.ltu ($ OS_LOWEST_PRIO) prio = false |] **
      (*prio table*)
      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
      G& OSPlaceHolder @ Int8u == vhold **
      PV vhold @ Int8u |-> vholdx **
      (* GV OSPlaceHolder @ Tint8 |-> vholdx ** *)
      [|array_type_vallist_match OS_TCB ∗ ptbl /\ length ptbl = 64%nat|] **
      [|RL_RTbl_PrioTbl_P rtbl ptbl vhold|] **
      (*tcb list*)
      GV OSTCBList @ OS_TCB ∗ |-> p1 **
      tcbdllseg p1 Vnull tail1 (Vptr ct) l1 **
      GV OSTCBCur @ OS_TCB ∗ |-r-> (Vptr ct) **
      tcbdllseg (Vptr ct) tail1 tail2 Vnull l2 **
      [|p1 <> Vnull|] **
      AOSRdyTblGrp rtbl rgrp **
      (*logic vars*)
      [|logicl = logic_val (Vptr vhold)::logic_val p1 ::
                 logic_val tail1 :: logic_val tail2 :: logic_llv l1 :: logic_llv l2 ::
                 logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp :: logic_code s :: nil|] ** p_local OSLInv ct init_lg.


Definition new_tcb_node_p (prio:priority) (prev:val) (next:val) (l:vallist) : Prop :=
    struct_type_vallist_match OS_TCB_flag l /\
    V_OSTCBPrio l = Some (Vint32 prio) /\
    V_OSTCBStat l = Some (Vint32 ($ OS_STAT_RDY)) /\
    V_OSTCBDly l = Some (Vint32 ($ 0)) /\
    V_OSTCBY l = Some (Vint32 (Int.shru prio ($ 3))) /\
    V_OSTCBBitY l = Some (nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) OSMapVallist) /\
    V_OSTCBX l = Some (Vint32 (Int.and prio ($ 7))) /\
    V_OSTCBBitX l = Some (nth_val' (Z.to_nat (Int.unsigned (Int.and prio ($ 7)))) OSMapVallist) /\
    V_OSTCBEventPtr l = Some Vnull /\
    V_OSTCBMsg l = Some Vnull /\
    V_OSTCBPrev l = Some prev /\
    V_OSTCBNext l = Some next.


Fixpoint set_nth {A:Type} (vl: list A) (n:nat) (v:A) : option (list A) :=
  match vl with
    | nil => None
    | h::t => match n with
                | O => Some (v::t)
                | S x => match set_nth t x v with
                           | Some r => Some (h::r)
                           | None => None
                         end
              end
  end.

Definition tcbls_change_prev_ptr (vl : list vallist) (ptr: val) : option (list vallist) :=
  match vl with
    | nil => None
    | h :: t => Some (update_nth_val 1%nat h ptr :: t)
  end.

Definition OS_TCBInitPost' (vl:vallist) (r:option val) (logicl:list logicvar) ct:=  

  Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** A_isr_is_prop **
  (( [| r = Some (Vint32 ($ OS_NO_MORE_TCB)) |] **
      EX (ptfree:val) (lfree:list vallist) (rtbl:vallist) (ptbl:vallist) (rgrp:val) (p1 tail1 tail2:val) (l1 l2:list vallist) (prio:priority) (vhold:addrval) s vholdx,
      AOSTCBFreeList ptfree lfree ** AOSMapTbl **
      (*prio table*)
      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
      G& OSPlaceHolder @ Int8u == vhold **
      PV vhold @ Int8u |-> vholdx **
(*      GV OSPlaceHolder @ Tint8 |-> vholdx ** *)
      <||s||> **
      [|array_type_vallist_match OS_TCB ∗ ptbl /\ length ptbl = 64%nat|] **
      [|RL_RTbl_PrioTbl_P rtbl ptbl vhold|] **
      (*tcb list*)
      GV OSTCBList @ OS_TCB ∗ |-> p1 **
      tcbdllseg p1 Vnull tail1 (Vptr ct) l1 **
      GV OSTCBCur @ OS_TCB ∗ |-r-> (Vptr ct) **
      tcbdllseg (Vptr ct) tail1 tail2 Vnull l2 **
      [|p1 <> Vnull|] **
      AOSRdyTblGrp rtbl rgrp **
      (*logic vars*)
      [|logicl = logic_val (Vptr vhold) :: logic_val p1 ::
                 logic_val tail1 :: logic_val tail2 :: logic_llv l1 :: logic_llv l2 ::
                 logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp :: logic_code s::nil|] **
      [| ptfree = Vnull |] ** p_local OSLInv ct init_lg
    ) 
    \\//
    ( [|r = Some (Vint32 ($ OS_NO_ERR))|] **
      EX (ptfree:val) (lfree:list vallist) (rtbl rtbl':vallist) (ptbl ptbl':vallist) (p1 tail1 tail1' tail2:val) anew (l1 l1' l2 l2':list vallist) (lnew:vallist) (rgrp rgrp':val) (prio:priority) (vhold:addrval) s vholdx,
      AOSTCBFreeList ptfree lfree ** AOSMapTbl **
      (*prio table*)
      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl' **
      G& OSPlaceHolder @ Int8u == vhold **
      PV vhold @ Int8u |-> vholdx **
(*      GV OSPlaceHolder @ Tint8 |-> vholdx ** *)
      <||s||> **
      [|array_type_vallist_match OS_TCB ∗ ptbl' /\ length ptbl' = 64%nat|] **
      [|RL_RTbl_PrioTbl_P rtbl' ptbl' vhold|] **
      (*new tcb head*)
      [|nth_val 0 vl = Some (Vint32 prio)|] **
      GV OSTCBList @ OS_TCB ∗ |-> (Vptr anew) **
      node (Vptr anew) lnew OS_TCB_flag ** PV get_off_addr anew flag_off @ Int8u |-> (V$ 1) **[| new_tcb_node_p prio Vnull p1 lnew|] **
      (*old tcbdllseg*)
      tcbdllseg p1 (Vptr anew) tail1' (Vptr ct) l1' **
      GV OSTCBCur @ OS_TCB ∗ |-r-> (Vptr ct) **
      tcbdllseg (Vptr ct) tail1' tail2 Vnull l2' **
      AOSRdyTblGrp rtbl' rgrp' **
      (*logic vars*)
      [| logicl = logic_val (Vptr vhold) :: logic_val p1 ::
                  logic_val tail1 :: logic_val tail2 :: logic_llv l1 :: logic_llv l2 ::
                  logic_lv ptbl :: logic_lv rtbl :: logic_val rgrp ::logic_code s :: nil |] **
      [| ptbl' = update_nth_val (Z.to_nat (Int.unsigned prio)) ptbl (Vptr anew) |] **
      [| rtbl' = update_nth_val
           (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
           (val_inj (or (nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl) (nth_val' (Z.to_nat (Int.unsigned (Int.and prio ($ 7)))) OSMapVallist))) |] **
      [| or rgrp (nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) OSMapVallist) = Some rgrp' |] **
      [| (l1 = nil /\ l1' = l1 /\ tcbls_change_prev_ptr l2 (Vptr anew) = Some l2') \/
         (l1 <> nil /\ tcbls_change_prev_ptr l1 (Vptr anew) = Some l1' /\ l2 = l2' /\ tail1 = tail1') |] ** p_local OSLInv ct init_lg
    )).



Theorem OS_TCBInitPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OS_TCBInitPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Theorem OS_TCBInitPostGood (vl:vallist) (v:option val) ll ct :
  GoodFunAsrt (OS_TCBInitPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.


Definition OS_TCBInitPre : fpre :=
  fun vl ll ct=> mkfunasrt (OS_TCBInitPreGood vl ll ct).

Definition OS_TCBInitPost : fpost :=
  fun vl v ll ct => mkfunasrt (OS_TCBInitPostGood vl v ll ct).


(* OS_isSomeMutexOwner *)
Definition OS_IsSomeMutexOwnerPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX msgql ectrl ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp mqls tcbls tcbptr vhold s,
    Aie false  ** Ais nil ** Acs (true::nil) ** Aisr empisr **
    AECBList ectrl msgql mqls tcbls ** (* msgqlist *)
    AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ** (* tcblist *)
    tcbdllflag p1 (tcbl1 ++ tcbcur :: tcbl2) **
    AOSRdyTblGrp rtbl rgrp ** AOSTCBPrioTbl ptbl rtbl tcbls vhold** (* rdy table & prio table *)
    HECBList mqls ** HTCBList tcbls ** HCurTCB ct  (* high level *) **
     A_isr_is_prop ** <||s||> **
    [| RH_TCBList_ECBList_P mqls tcbls ct|] **
    [| nth_val 0 vl = Some (Vptr tcbptr)|] **
    [| RH_CurTCB ct tcbls |] **
    [| logicl = logic_leventd msgql :: logic_leventc ectrl :: logic_lv ptbl :: logic_val p1 :: logic_val p2 :: logic_llv tcbl1 :: logic_lv tcbcur :: logic_llv tcbl2 :: logic_lv rtbl :: logic_val rgrp :: logic_absecb mqls :: logic_abstcb tcbls :: logic_val (Vptr tcbptr) :: logic_val (Vptr vhold) :: logic_code s :: nil |] ** 
    p_local OSLInv  ct init_lg.


Theorem OS_IsSomeMutexOwnerPreGood (vl:vallist) logicl ct:
  GoodFunAsrt (OS_IsSomeMutexOwnerPre' vl logicl ct).
Proof.
  GoodFunAsrt_solver.
Qed.


Definition OS_IsSomeMutexOwnerPre: fpre :=
  fun vl ll ct=> mkfunasrt (OS_IsSomeMutexOwnerPreGood vl ll ct).

(* post *)
Definition is_some_mutex_owner ptr ecbmap :=
  exists eid pr opr wls, (EcbMod.get ecbmap eid = Some (absmutexsem pr (Some (ptr, opr)), wls)).
(* Definition at_most_once_in_ecbmap ptr ecbmap :=
 *         forall x y wl x' y' wl',
 *           EcbMod.get ecbmap x' = Some (y', wl') ->
 *           EcbMod.get ecbmap x = Some (y, wl) ->
 *           In ptr wl ->
 *           In ptr wl' ->
 *           x' = x . *)

(* Definition task_delete_pure_hyp ptr ecbmap :=
 *   ~ is_some_mutex_owner ptr ecbmap (* /\ at_most_once_in_ecbmap ptr ecbmap *). *)

Definition OS_IsSomeMutexOwnerPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct:=
EX msgql ectrl ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp mqls tcbls tcbptr vhold s,
    Aie false  ** Ais nil ** Acs (true::nil) ** Aisr empisr **
    AECBList ectrl msgql mqls tcbls ** (* msgqlist *)
    AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ** (* tcblist *)
    tcbdllflag p1 (tcbl1 ++ tcbcur :: tcbl2) **
    AOSRdyTblGrp rtbl rgrp ** AOSTCBPrioTbl ptbl rtbl tcbls vhold** (* rdy table & prio table *)
    HECBList mqls ** HTCBList tcbls ** HCurTCB ct  (* high level *) **
     A_isr_is_prop ** <||s||> **
    [| RH_TCBList_ECBList_P mqls tcbls ct|] **
    [| nth_val 0 vl = Some (Vptr tcbptr)|] **
    [| RH_CurTCB ct tcbls |] **
    [| logicl = logic_leventd msgql :: logic_leventc ectrl :: logic_lv ptbl :: logic_val p1 :: logic_val p2 :: logic_llv tcbl1 :: logic_lv tcbcur :: logic_llv tcbl2 :: logic_lv rtbl :: logic_val rgrp :: logic_absecb mqls :: logic_abstcb tcbls :: logic_val (Vptr tcbptr) :: logic_val (Vptr vhold) :: logic_code s :: nil |] ** 
    p_local OSLInv  ct init_lg **
    [| (v = Some (V$0) /\ ~ is_some_mutex_owner tcbptr mqls) \/
       (v = Some (V$1) /\ is_some_mutex_owner tcbptr mqls) |]
.

Theorem OS_IsSomeMutexOwnerPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OS_IsSomeMutexOwnerPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition OS_IsSomeMutexOwnerPost : fpost :=
 fun vl v ll ct=> mkfunasrt (OS_IsSomeMutexOwnerPostGood vl v ll ct).





Open Scope list_scope.

Definition OS_Sched_spec : fspec:= (OS_SchedPre,OS_SchedPost,(Tvoid,nil)).

Definition OSIntExit_spec : fspec:= (OSIntExitPre,OSIntExitPost,(Tvoid,nil)). 

Definition OSTimeTick_spec : fspec:= (OSTimeTickPre,OSTimeTickPost,(Tvoid,nil)).

Definition OS_EventSearch_spec : fspec :=(OS_EventSearchPre, OS_EventSearchPost, (Tint8, (Tptr OS_EVENT) :: nil)).

Definition OS_EventRemove_spec : fspec :=(OS_EventRemovePre, OS_EventRemovePost, (Tvoid, (Tptr OS_EVENT) :: nil)).

Definition OS_EventTaskRdy_spec  : fspec :=(OS_EventTaskRdyPre, OS_EventTaskRdyPost, (Tint8, (Tptr OS_EVENT) :: (Tptr Tvoid) :: Tint8 :: nil)).

Definition OS_EventTaskWait_spec : fspec :=(OS_EventTaskWaitPre, OS_EventTaskWaitPost, (Tvoid, (Tptr OS_EVENT) :: nil)).

Definition OS_EventWaitListInit_spec : fspec := 
  (OS_EventWaitListInitPre, OS_EventWaitListInitPost,
   (Tvoid, (Tptr OS_EVENT)::nil)).

Definition OS_PrioChange_spec : fspec :=(OS_PrioChangePre, OS_PrioChangePost, (Tvoid, (Tptr OS_TCB) :: Tint8 :: Tint8 :: nil)).
 
Definition OS_TCBInit_spec : fspec :=
  (OS_TCBInitPre, OS_TCBInitPost, (Int8u, (Int8u (*:: Int32 :: Void∗ *) :: nil))).

Definition OS_IsSomeMutexOwner_spec : fspec :=(OS_IsSomeMutexOwnerPre, OS_IsSomeMutexOwnerPost, (Tint8, (Tptr OS_TCB) :: nil)).



Definition osq_spec_list := 
  (OS_EventSearch, OS_EventSearch_spec) ::
  (OS_EventRemove, OS_EventRemove_spec) ::
  (OS_EventTaskRdy,  OS_EventTaskRdy_spec) ::
  (OS_EventTaskWait, OS_EventTaskWait_spec) ::
  (OS_Sched,  OS_Sched_spec) ::
  (OSIntExit, OSIntExit_spec) ::
  (OSTimeTick, OSTimeTick_spec)::
  (OS_EventWaitListInit,OS_EventWaitListInit_spec) ::
  (OS_TCBInit, OS_TCBInit_spec) ::
  (OS_IsSomeMutexOwner, OS_IsSomeMutexOwner_spec) ::
  nil.  

Fixpoint convert_spec  (ls : list (fid * fspec)) : fid -> option fspec :=
   match ls with
   | nil => fun _ => None
   | (id,spec) :: ls' => 
     fun (id' : fid) =>  
       if Zeq_bool id id' then 
         Some spec else convert_spec ls' id'
   end.

Definition OS_spec :=  convert_spec osq_spec_list.

Close Scope list_scope.
