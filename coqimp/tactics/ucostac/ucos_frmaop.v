Require Import include_frm.
Require Export frmaop_sol.
Require Import os_inv.
Require Import os_code_defs.
Require Import os_ucos_h.
Require Import code_notations.

Open Scope code_scope.

Lemma good_frm_tcbdllseg : 
  forall vl head hp tail tn , 
    GoodFrm(tcbdllseg head hp tail tn vl).
Proof.
  intros.
  unfold tcbdllseg.
  apply good_frm_dllseg.
Qed.

Hint Resolve good_frm_tcbdllseg : good_frm_lemmas.

Lemma good_frm_AOSEventTbl : 
  forall x0 v0, GoodFrm (AOSEventTbl x0 v0).
Proof.
  intros.
  unfold AOSEventTbl.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSEventTbl : good_frm_lemmas.

Lemma good_frm_node : 
  forall v vl t , GoodFrm (node v vl t).
Proof. 
  introv.
  unfold node.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_node : good_frm_lemmas.


Lemma good_frm_AOSEvent : 
  forall a0 v x, GoodFrm  (AOSEvent a0 v x).
Proof.
  intros.
  unfold AOSEvent.
  good_frm_sovler.
Qed. 

Hint Resolve  good_frm_AOSEvent : good_frm_lemmas.

Lemma good_frm_AOSQBlk : 
  forall x1 v2 x2, GoodFrm (AOSQBlk x1 v2 x2).
Proof.
  introv.
  unfold AOSQBlk.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSQBlk : good_frm_lemmas.

Lemma good_frm_AOSQCtr :
  forall x1 v2, GoodFrm (AOSQCtr x1 v2).
Proof.
  introv.
  unfold AOSQCtr.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSQCtr : good_frm_lemmas.

Lemma good_frm_AMsgData : 
  forall  x v1 x1 x2, GoodFrm ( AMsgData x v1 x1 x2).
Proof.
  intros.
  unfold AMsgData.
  good_frm_sovler.
Qed. 

Hint Resolve   good_frm_AMsgData : good_frm_lemmas.

Lemma good_frm_amsgnode : 
  forall p a  b  v1 v2 v3 l, 
    GoodFrm (AEventNode p a b (DMsgQ l v1 v2 v3)).
Proof.
  introv.
  unfold AEventNode.
  unfold AEventData.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_amsgnode : good_frm_lemmas.

Lemma good_frm_mqsllseg :
  forall p n l msgqls, GoodFrm (evsllseg p n l msgqls).
Proof.
  introv.
  gen l n p msgqls.
  inductions l; intros; simpl; good_frm_sovler; auto.
  destruct msgqls.
  simpl;auto.
  destruct a.
  good_frm_sovler.
  unfold AEventNode.
  good_frm_sovler.
  unfold AEventData.
  destruct e; good_frm_sovler.
Qed.

Hint Resolve good_frm_mqsllseg  : good_frm_lemmas.


Lemma good_frm_ecbfslleg : 
  forall ls x y ,
    GoodFrm (ecbf_sllseg x  y ls OS_EVENT V_OSEventListPtr).
Proof.
   inductions ls; intros.  
   simpl.   auto. 
   unfold ecbf_sllseg; fold ecbf_sllseg.
    good_frm_sovler.
Qed.

Hint Resolve good_frm_ecbfslleg  : good_frm_lemmas.


Lemma good_frm_ecbfsll: forall ls x ,
                               GoodFrm (ecbf_sll x ls OS_EVENT V_OSEventListPtr).
Proof.
   unfold ecbf_sll. 
    intros.
    good_frm_sovler.
Qed.

Hint Resolve good_frm_ecbfsll  : good_frm_lemmas.

Lemma good_frm_AOSEventFreeList: 
  forall x ,
    GoodFrm (AOSEventFreeList x).
Proof.
  unfold AOSEventFreeList.
  intros.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSEventFreeList : good_frm_lemmas.


Lemma  good_frm_qblkf_sllseg : 
  forall x y qblkl, GoodFrm (qblkf_sllseg x y qblkl OS_Q_FREEBLK V_nextblk).
Proof.
  intros.
  gen x y.
  inductions qblkl.
  intros.
  unfold qblkf_sllseg.
  good_frm_sovler.
  intros.
  unfold qblkf_sllseg.
  fold qblkf_sllseg.   
  good_frm_sovler.
Qed.


Hint Resolve  good_frm_qblkf_sllseg : good_frm_lemmas.

Lemma  good_frm_qblkf_sll : 
  forall x qblkl, GoodFrm (qblkf_sll x qblkl OS_Q_FREEBLK V_nextblk).
Proof.
  intros.
  unfold qblkf_sll.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_qblkf_sll : good_frm_lemmas.

Lemma good_frm_AOSQFreeList: forall x ,
                               GoodFrm (AOSQFreeList x ).
Proof.
  unfold AOSQFreeList.
  intros.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSQFreeList : good_frm_lemmas.

Lemma good_frm_AOSQFreeBlk : forall qblkl, GoodFrm (AOSQFreeBlk qblkl).
Proof.
  introv.
  unfold AOSQFreeBlk.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSQFreeBlk : good_frm_lemmas.


Lemma good_frm_EventList'  : forall  qptrl msgql,
                               GoodFrm ((EX p : val,
       GV OSEventList @ OS_EVENT∗ |-> p ** evsllseg p Vnull qptrl msgql)).
Proof.
  intros.  
   good_frm_sovler.
Qed.

Hint Resolve good_frm_EventList' : good_frm_lemmas.

Lemma good_frm_AMsgQList : forall qptrl msgql mqls tcbls,
                             GoodFrm (AECBList qptrl msgql mqls tcbls ).
Proof.
  introv.
  unfold AECBList.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AMsgQList : good_frm_lemmas.  

Lemma good_frm_AOSMapTbl : GoodFrm AOSMapTbl.
Proof. 
  unfold AOSMapTbl.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSMapTbl : good_frm_lemmas. 


Lemma good_frm_AOSUnMapTbl : GoodFrm AOSUnMapTbl.
Proof. 
  unfold AOSUnMapTbl.
  good_frm_sovler.  
Qed.

Hint Resolve good_frm_AOSUnMapTbl : good_frm_lemmas. 

Lemma good_frm_AOSTCBPrioTbl:  forall  ptbl rtbl tcbls vhold,
                                GoodFrm (AOSTCBPrioTbl ptbl rtbl tcbls vhold).
Proof.
  unfold AOSTCBPrioTbl.
  intros.
  good_frm_sovler.
Qed.


Hint Resolve good_frm_AOSTCBPrioTbl : good_frm_lemmas. 


Lemma good_frm_AOSIntNesting : GoodFrm AOSIntNesting.
Proof.
  unfold AOSIntNesting.
   good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSIntNesting : good_frm_lemmas. 

Lemma good_frm_AOSTime : forall t,GoodFrm (AOSTime t).
Proof.
  unfold AOSTime.
  intros;  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSTime : good_frm_lemmas. 

Lemma good_frm_AGVars : GoodFrm AGVars.
Proof.
  unfold AGVars.
  intros.
   good_frm_sovler.
Qed.


Hint Resolve good_frm_AGVars : good_frm_lemmas. 



Lemma good_frm_AOSTCBList: forall x1 x2 x3 x4 x5 x6 x7,
                             GoodFrm (AOSTCBList x1 x2 x3 x4 x5 x6 x7).
Proof.
  introv.
  unfold AOSTCBList.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSTCBList  : good_frm_lemmas.

Lemma good_frm_tcbdllflsg : forall x1 x2, 
   GoodFrm (tcbdllflag x1 x2).
Proof.
  intros.
  gen x1.
  inductions x2.
  simpl; split; auto.
  intros.
  unfold tcbdllflag in *.
  simpl.
  intros; splits; auto.
Qed.

Hint Resolve   good_frm_tcbdllflsg   : good_frm_lemmas.

Lemma good_frm_AOSTCBList':
  forall x1 x2 x3 x4 x5 x6 x7 x8,
    GoodFrm (AOSTCBList' x1 x2 x3 x4 x5 x6 x7 x8).
Proof.
  introv.
  unfold AOSTCBList'.
  unfold GoodFrm.
  fold GoodFrm.
  split; intros.
  splits;  good_frm_sovler; auto.
  simpl; intros; splits; auto.
  good_frm_sovler.
  splits; good_frm_sovler; auto.
  unfold tcblist.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSTCBList'  : good_frm_lemmas.


Lemma good_frm_sllfreeflag :
  forall x1 x2,
    GoodFrm (sllfreeflag x1 x2).
Proof.
  introv.
  unfold sllfreeflag.
  gen x1.
  inductions x2. 
  intros.
  simpl; auto.
  intros.
  simpl.
  intros;splits; auto.
Qed.

Hint Resolve  good_frm_sllfreeflag  : good_frm_lemmas.

Lemma good_frm_AOSTCBFreeList: forall x1 x2,
                             GoodFrm (AOSTCBFreeList x1 x2).
Proof.
  introv.
  unfold AOSTCBFreeList.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSTCBFreeList  : good_frm_lemmas. 

Lemma good_frm_AOSTCBFreeList': 
  forall x1 x2 x3 x4,
    GoodFrm (AOSTCBFreeList' x1 x2 x3 x4).
Proof.
  introv.
  unfold AOSTCBFreeList'.
  good_frm_sovler.
  unfold GoodFrm. fold GoodFrm.
  splits.
  unfold TCBFree_Not_Eq.
  good_frm_sovler.
  unfold TCBFree_Eq.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSTCBFreeList'  : good_frm_lemmas. 

Lemma good_frm_AOSRdyTbl : forall vl,  
                               GoodFrm (AOSRdyTbl vl).
Proof.
  intros.
  unfold AOSRdyTbl .
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSRdyTbl  : good_frm_lemmas. 


Lemma good_frm_AOSRdyGrp : forall vl,  
                               GoodFrm (AOSRdyGrp vl).
Proof.
  intros.
  unfold AOSRdyGrp .
 good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSRdyGrp  : good_frm_lemmas. 

Lemma good_frm_AOSRdyTblGrp  : forall rtbl rgrp,  
                               GoodFrm (AOSRdyTblGrp rtbl rgrp).
Proof.
  intros.
  unfold   AOSRdyTblGrp .
 good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSRdyTblGrp  : good_frm_lemmas.


(***********************************************************)

(*
Ltac can_change_aop_solver :=
  try unfold OSInv;
  try unfold AOSEventFreeList,
  AOSQFreeList, AOSQFreeBlk, AECBList;
  try unfold AOSMapTbl, AOSUnMapTbl,
  AOSTCBPrioTbl, AOSIntNesting,
  AOSTCBList', AOSTCBFreeList';
  try unfold AOSRdyTblGrp,
  AOSRdyTbl, AOSRdyGrp, AOSTime, AGVars;
  try unfold AOSEvent, AOSEventTbl,
  AMsgData, AOSQCtr, AOSQBlk, node;
  try unfold tcblist;
  unfold can_change_aop;
  fold can_change_aop;
  intuition auto 1 with can_change_aop;
  simpl; intros;  intuition auto 1 with can_change_aop.
 *)

Lemma can_change_aop_osqctr:
  forall c d, 
  can_change_aop (AOSQCtr c d).
Proof.
  unfold AOSQCtr.
  intros.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_osqctr : can_change_aop.


Lemma  can_change_aop_aosqblk:
  forall x e f, 
  can_change_aop (AOSQBlk x e f).
Proof.
  unfold AOSQBlk.
  intros.
   can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_aosqblk : can_change_aop.

Theorem can_change_aop_msgq :
  forall c d e f,
    can_change_aop (AMsgData c d e f). 
Proof.
  intros.
  unfold AMsgData.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_msgq : can_change_aop.

Theorem can_change_aop_aevtdata:
  forall vl d , can_change_aop (AEventData vl d).
Proof.
  intros.
  unfold AEventData.
  destruct d; can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_aevtdata : can_change_aop.

Lemma can_change_aop_aoseventtbl:
  forall x d,
  can_change_aop (AOSEventTbl x d).
Proof.
  intros.
  unfold AOSEventTbl.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_aoseventtbl : can_change_aop.


Lemma  can_change_aop_aosevent:
  forall l vl d,
   can_change_aop (AOSEvent l vl d).
Proof.
  intros.
  unfold AOSEvent.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_aosevent : can_change_aop.

Theorem can_change_aop_msgqnode :
  forall l vl d c,
    can_change_aop (AEventNode l vl d c).
Proof.
  intros.
  unfold AEventNode.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_msgqnode : can_change_aop.

Theorem can_change_aop_msgqllseg :
  forall h tn l msgqls,
    can_change_aop (evsllseg h tn l msgqls).
Proof.
  intros.
  gen h tn msgqls.
  induction l; simpl in *; intuition auto.
  destruct msgqls.
  can_change_aop_solver.
  destruct a.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_msgqllseg : can_change_aop.


Theorem can_change_aop_tcbdllseg :
  forall h hp t tn l,
    can_change_aop (tcbdllseg h hp t tn l).
Proof.
  intros.
  unfold tcbdllseg.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_tcbdllseg : can_change_aop.


Theorem    can_change_aop_ecbfsllseg :
  forall ls x y,
    can_change_aop (ecbf_sllseg x y ls OS_EVENT V_OSEventListPtr).
Proof.
  inductions ls. 
  intros; simpl; intuition auto.
  unfold ecbf_sllseg; fold ecbf_sllseg.
  unfold dllseg; fold dllseg.
  intros.
  can_change_aop_solver.  
Qed.

Hint Resolve can_change_aop_ecbfsllseg: can_change_aop.

Theorem    can_change_aop_ecbfsll :
  forall ls x , can_change_aop (ecbf_sll x ls OS_EVENT V_OSEventListPtr).
Proof.

  intros; unfold ecbf_sll.
  can_change_aop_solver.  
Qed.


Hint Resolve can_change_aop_ecbfsll: can_change_aop.

Theorem  can_change_aop_qblkfseg :
forall x y ls, can_change_aop (qblkf_sllseg x y ls OS_Q_FREEBLK V_nextblk).
Proof.             
  intros.
  gen x y.
  inductions ls .
  unfold qblkf_sllseg.
  intros.
  can_change_aop_solver.  
  intros.
  unfold qblkf_sllseg.
  fold qblkf_sllseg.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_qblkfseg: can_change_aop.

Theorem  can_change_aop_qblkf :
  forall x ls, can_change_aop (qblkf_sll x  ls OS_Q_FREEBLK V_nextblk).
Proof.
  intros.
  unfold qblkf_sll.
  can_change_aop_solver.
Qed.     


Hint Resolve can_change_aop_qblkf: can_change_aop.

Theorem  can_change_aop_sllfreeflag :
  forall x17 x18, can_change_aop (sllfreeflag x17 x18).
Proof.
  intros.
  unfold sllfreeflag.
  gen x17.
  inductions x18.
  intros.
  simpl; auto.
  intros.
  simpl.
  intros.
  splits; auto.
Qed.

Hint Resolve  can_change_aop_sllfreeflag: can_change_aop.

Theorem  can_change_aop_tcbdllflag:
  forall x6 x5, can_change_aop (tcbdllflag x5 x6).
Proof.
  inductions x6.
  simpl; auto.
  intros.
  simpl.
  intros.
  splits; auto.
  unfold tcbdllflag in IHx6.
  auto.
Qed.

Hint Resolve  can_change_aop_tcbdllflag: can_change_aop.

Theorem can_change_aop_tcbnotin:
  forall x6 x19 ls,
    can_change_aop (TCB_Not_In x6 x19 ls).
 Proof.
   intros.
   unfold TCB_Not_In.
   unfold can_change_aop.
   fold can_change_aop.
   auto.
Qed.

 Hint Resolve  can_change_aop_tcbnotin: can_change_aop.

 Theorem can_change_aop_tcblist:
  forall p1 p2 tcbl1 ls rtbl ct tcbls ,
   can_change_aop (AOSTCBList p1 p2 tcbl1 ls  rtbl ct tcbls). 
Proof.
  intros.
  unfold AOSTCBList.
   can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_tcblist: can_change_aop.

Theorem can_change_aop_tcblist_new:
  forall p1 p2 tcbl1 ls rtbl ct tcbls ptfree,
   can_change_aop (AOSTCBList' p1 p2 tcbl1 ls  rtbl ct tcbls ptfree). 
Proof.
  intros.
  unfold AOSTCBList'.
  unfold can_change_aop.
  fold can_change_aop.
  split.
  intros.
  splits;  can_change_aop_solver; auto.
  simpl; auto.
  splits; can_change_aop_solver; auto.
  intros.
  splits; can_change_aop_solver; auto.
  simpl; auto.
  split; auto.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_tcblist_new: can_change_aop.

Lemma can_change_aop_noteq:
  forall ptfree ct lfree, 
   can_change_aop (TCBFree_Not_Eq ptfree ct lfree).
Proof.
  intros.
  unfold TCBFree_Not_Eq.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_noteq: can_change_aop.

Lemma can_change_aop_eq:
  forall ptfree ct lfree tcbls, 
   can_change_aop (TCBFree_Eq ptfree ct lfree tcbls).
Proof.
  intros.
  unfold TCBFree_Eq.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_eq: can_change_aop.

Theorem can_change_aop_tcbfreelist:
  forall ptfree lfree,
   can_change_aop (AOSTCBFreeList ptfree lfree).
Proof.
  intros.
  unfold AOSTCBFreeList.
  can_change_aop_solver.
Qed.
  
Hint Resolve  can_change_aop_tcbfreelist: can_change_aop.



Theorem can_change_aop_tcbfreelist_new:
  forall ptfree lfree ct tcbls,
   can_change_aop (AOSTCBFreeList' ptfree lfree ct tcbls).
Proof.
  intros.
  unfold AOSTCBFreeList'.
  unfold can_change_aop.
  fold can_change_aop.
  splits;  can_change_aop_solver.
Qed.
  
Hint Resolve  can_change_aop_tcbfreelist_new: can_change_aop.

Lemma can_change_aop_evtfls:
  forall x,
  can_change_aop (AOSEventFreeList x).
Proof.
  intros.
  unfold AOSEventFreeList.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_evtfls: can_change_aop.

Lemma can_change_aop_qfreels:
  forall x,
  can_change_aop (AOSQFreeList x).
Proof.
  intros.
  unfold AOSQFreeList.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_qfreels: can_change_aop.

Lemma can_change_aop_qfreeblk:
  forall x,
  can_change_aop (AOSQFreeBlk x).
Proof.
  intros.
  unfold AOSQFreeBlk.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_qfreeblk: can_change_aop.

Lemma can_change_aop_ecblist:
  forall x3 x2 x12 x13,
  can_change_aop (AECBList x3 x2 x12 x13).
Proof.
  intros.
  unfold AECBList.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_ecblist: can_change_aop.

Lemma can_change_aop_mtbl:
  can_change_aop AOSMapTbl.
Proof.
  intros.
  unfold AOSMapTbl.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_mtbl: can_change_aop.

Lemma can_change_aop_unmtbl:
  can_change_aop AOSUnMapTbl.
Proof.
  intros.
  unfold AOSUnMapTbl.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_unmtbl: can_change_aop.

Lemma can_change_aop_prtbl:
  forall x4 x10 x13 x16,
  can_change_aop  (AOSTCBPrioTbl x4 x10 x13 x16).
Proof.
  intros.
  unfold AOSTCBPrioTbl.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_prtbl: can_change_aop.


Lemma can_change_aop_intnest:
  can_change_aop AOSIntNesting.
Proof.
  intros.
  unfold AOSIntNesting.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_intnest: can_change_aop.

Lemma can_change_aop_rdytbl:
  forall x10 ,
  can_change_aop  (AOSRdyTbl x10).
Proof.
  intros.
  unfold AOSRdyTbl.
  can_change_aop_solver.
Qed.


Hint Resolve  can_change_aop_rdytbl: can_change_aop.

Lemma can_change_aop_rdygrp:
  forall x10 ,
  can_change_aop  (AOSRdyGrp x10).
Proof.
  intros.
  unfold AOSRdyGrp.
  can_change_aop_solver.
Qed.


Hint Resolve  can_change_aop_rdygrp: can_change_aop.


Lemma can_change_aop_rdytbgrp:
  forall x10 x11,
  can_change_aop  (AOSRdyTblGrp x10 x11).
Proof.
  intros.
  unfold AOSRdyTblGrp.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_rdytbgrp: can_change_aop.

Lemma can_change_aop_time:
  forall x14, 
  can_change_aop  (AOSTime (Vint32 x14)).
Proof.
  intros.
  unfold AOSTime.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_time: can_change_aop.

Lemma can_change_aop_gvars:
  can_change_aop AGVars.
Proof.
  intros.
  unfold AGVars.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_gvars: can_change_aop.

Lemma can_change_aop_plocal:
  forall tid l, can_change_aop (p_local OSLInv tid l).
Proof.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  intros.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_plocal : can_change_aop.

Lemma can_change_aop_isris:
  can_change_aop  A_isr_is_prop.
Proof.
  intros.
  unfold  A_isr_is_prop.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_isris: can_change_aop.                  

Theorem can_change_aop_OSQInv :
  can_change_aop OSInv.
Proof.
  unfold OSInv.
  can_change_aop_solver.  
Qed.


Close Scope code_scope.
