Require Import include_frm.
Require Import auxdef.
Require Import simulation.

Inductive evtrace:=
| evnil: evtrace
| evabort : evtrace
| evcons: val -> evtrace -> evtrace.

Inductive LETr : lworld -> evtrace -> Prop := 
  | LETr_emp : forall (p:lprog) (cst:clientst) (T:tasks) (t:tid) (S:osstate),
                 LETr  (p, T, cst, S , t) evnil
  | LETr_ne : forall p T T' t t' S S' cst cst' et,  
               lpstep  p T cst S t T' cst' S' t' ->
               LETr (p, T', cst', S', t') et -> 
               LETr (p, T, cst, S, t) et
  | LETr_e : forall p T T' t t' S S' cst cst' et' ev,  
               lpstepev  p T cst S t T' cst' S' t' ev->
               LETr (p, T',  cst',  S',  t') et' -> 
               LETr (p, T, cst, S , t) (evcons ev et')
  | LETr_abt : forall (p:lprog) (cst:clientst) (T:tasks) (t:tid) (S:osstate),
                 lpstepabt p T cst S t -> LETr (p, T, cst, S,  t) evabort. 


Inductive HETr : hworld -> evtrace -> Prop := 
  | HETr_emp : forall (p:hprog) (cst:clientst) (T:tasks)  (O:osabst),
                 HETr (p, T, cst, O) evnil
  | HETr_ne : forall p T T' O O' cst cst' et,  
               hpstep  p T cst O T' cst' O' ->
               HETr (p, T', cst', O') et -> 
               HETr (p, T, cst, O) et
  | HETr_e : forall p T T' O O' cst cst' et' ev,  
               hpstepev p T cst O T' cst' O' ev->
               HETr (p, T', cst', O') et' -> 
               HETr (p, T, cst, O) (evcons ev et')
  | HETr_abt : forall (p:hprog) (cst:clientst) (T:tasks)  (O:osabst),
                 hpstepabt p T cst O -> HETr (p, T, cst, O) evabort. 


Inductive ETrRef : lworld-> hworld -> Prop := 
  | etrref_subset : forall lw hw, 
                    (forall et, LETr lw et -> HETr hw et) -> 
                    ETrRef lw hw. 



Notation abtcblsid := abstcblsid.

Definition eqdomTO:= fun (T:tasks) (O:osabst) =>
                       exists tls,
                         get O abtcblsid = Some (abstcblist tls) /\(
                           forall t, (exists a, get tls t = Some a ) ->  (exists C,get T t = Some C)  ).
Definition eqdomto:= fun (T:tasks) (O:osabst) =>
                       exists tls,
                         get O abtcblsid = Some (abstcblist tls) /\(
                           forall t, (exists a, get tls t = Some a ) <->  (exists C,get T t = Some C)  ).

(*
Definition eqdomTCst:= fun (T:tasks) (cst:clientst) =>
                         forall t, (exists C,TasksMod.get T t = Some C) <-> (exists a , EntryMod.get (snd cst) t = Some a ).

Definition eqdomcstO (cst:clientst) O:=
  exists tls,
  OSAbstMod.get O abtcblsid = Some (abstcblist tls) /\
  forall t, (exists x,TcbMod.get tls t = Some x) <-> 
            (exists a, EntryMod.get (snd cst) t = Some a ).
 *)


Definition InitTasks (T:tasks) (p:progunit) (cst:clientst) (O:osabst) :=
  eqdomto T O /\ 
  forall t C,TasksMod.get T t = Some C -> 
  exists s f d1 d2 t, C = nilcont s /\ 
                      p f = Some (t, d1, d2, s).


Definition etrace_subset (lw: lworld)(hw: hworld)  := forall E, LETr lw E -> HETr hw E. 


Fixpoint GoodStmt (s:stmts) (p:progunit) {struct s}:= 
  match s with
    | sskip v  => True
    | sassign e e' => True
    | sif e s1 s2 => GoodStmt s1 p/\ GoodStmt s2 p
    | sifthen e s => GoodStmt s p
    | swhile e s' => GoodStmt s' p
    | sret => True
    | srete e => True
    | scall f el =>  p f = None
    | scalle e f el => p f = None
    | sseq s1 s2 => GoodStmt s1 p /\ GoodStmt s2 p
    | sprint e => True
    | _ => False
  end.    

Definition GoodClient (p1 p2 p3:progunit):= 
  (forall f a b c s, p1 f = Some (a,b,c,s) -> GoodStmt s p3) /\ (forall f, p1 f <> None -> p2 f = None) /\ forall f, (p2 f <> None -> p1 f = None).


Definition WellClient p1 p2 p3 := GoodClient p1 p2 p3 (*/\ good_ret_pu p1*).

Definition getSG  (Sl:osstate):= fst (fst (fst (fst Sl))).

Definition OSCorrect (Os:oscode) (A:osspec) (init:InitAsrt):=
  forall (t:tid) pc Wl Wh (T:tasks) S cst O, 
    OSAbstMod.get O curtid = Some (oscurt t) ->
    InitTasks T pc cst O -> init S O -> (WellClient pc (fst (fst Os)) (snd (fst Os)))-> TasksMod.indom T t ->
    Wl = ((pc, Os), T , cst, S, t) ->
    Wh = ((pc, A), T, cst, O) ->
    etrace_subset Wl Wh.

Lemma Hstepstar_no_ev : forall  hp ht cs os  ht' cs' os' E, 
               hpstepstar hp ht cs os ht' cs' os' -> 
                 HETr (hp, ht', cs', os')  E -> 
                       HETr (hp, ht, cs, os)  E. 
Proof.
  introv H1 H2.
  gen H2.
  inductions H1.
  auto.
  constructors.
  eauto.
  applys IHhpstepstar. 
  auto.
Qed. 

Lemma Hstepstar_with_ev : forall  hp ht cs os ht' cs' os' E ev, 
               hpstepevstar hp ht cs os ht' cs' os' ev -> 
                 HETr (hp, ht', cs', os')  E -> 
                       HETr (hp, ht, cs, os) (evcons ev  E). 
Proof.
  introv H1 H2.
  gen H2.
  inductions H1.
  intros.
  eapply Hstepstar_no_ev.
  eauto.
  eapply HETr_e. 
  eauto.
  applys Hstepstar_no_ev.
 eauto.
 eauto.
Qed.
 

Lemma progsim_imply_eref_aux : forall  (E : evtrace) (lp: lprog) (lt : tasks)
 (cs : clientst) (os : osstate) (t: tid), LETr (lp, lt, cs, os, t) E ->
  (forall 
 (hp: hprog) (ht: tasks) (bs : osabst) , ProgSim lp lt os  hp ht bs cs t ->
   HETr (hp, ht, cs, bs) E).
Proof.
introv HLe.
inductions HLe.
introv Hsim.
constructors.
introv Hsim.
inverts keep Hsim.
lets Hk : H1 H.
destruct Hk as (Th' & O' &  Hstep & Hpsim).
eapply  Hstepstar_no_ev.
eauto.
eapply IHHLe.
eauto.
eauto.

introv Hsim.
inverts keep Hsim.
lets (Th' & O' & Hstep & Hpsim) : H2 H.
eapply  Hstepstar_with_ev.
eauto.
eapply IHHLe.
eauto.
eauto.
introv Hsim.
inverts keep Hsim.
lets Hk : H3 H.
inverts Hk.
destruct H4 as (T'& cst' & O' & Hp & Ha).
eapply  Hstepstar_no_ev.
eauto.
constructors.
eauto.
Qed.

Definition prog_sim (lw : lworld) (hw:hworld) := 
         match lw,  hw with
          | (P, T, CS, los, t) , (P', T', CS', HOS) 
                     => OSAbstMod.get HOS curtid = Some (oscurt t) /\ CS = CS' /\ ProgSim P T los P' T' HOS  CS t
         end.

 

Ltac deslw lw :=
  let p := fresh "p" in
  let ts := fresh "ts" in
  let cs := fresh "cs" in
  let os := fresh "os" in
  let t := fresh "t" in
  destruct lw as [[[[p ts] cs] os ] t].


Ltac deshw hw :=
  let P := fresh "P" in
  let T := fresh "T" in
  let CS := fresh "CS" in
  let HOS := fresh "OS" in
  let t' := fresh "t'" in
  destruct hw as [[[[P T] CS] HOS ] t'].


Theorem progsim_imply_eref : forall lw hw, prog_sim lw hw ->  etrace_subset lw hw.
Proof.
introv Hpsim.
deslw lw.
deshw hw.
unfolds in Hpsim.
lets (Hp1 & Hp2 & Hp3) : Hpsim.
unfolds.
introv Hle.
simpls. 
eapply  progsim_imply_eref_aux; eauto.

rewrite <- Hp2.
eauto.

rewrite <- Hp2.
eauto.
Qed.
