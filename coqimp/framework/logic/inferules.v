Require Import memory.
Require Import language.
Require Import opsem.
Require Import assertion.
Set Asymmetric Patterns.
(*
Definition emposspec : osspec :=
  ( fun (i : fid) => None,   fun (i : hid) => None, fun _ _ =>  True ).
 *)

Notation hmstep := spec_step.
Notation hmstepstar:=spec_stepstar.

(*
Definition absimp' sc (p p' : asrt) := 
forall (s : taskst) (O : osabst) (gamma : absop),
(s, O, gamma) |= p ->
forall Of OO,
  join O Of OO ->
  exists O' gamma' OO OO',
    join O' Of OO' /\
    hmstepstar sc gamma OO gamma'
               OO' /\ (s, O', gamma') |= p'.
 *)

Definition satp o O p := forall aop,   (o,O, aop)  |= p.

Definition LocalInv := tid -> list logicvar ->  asrt.

Definition p_exact lasrt :=
  forall ge le M ir aux O le' M' aux' ir' O',
    satp (ge,le,M,ir,aux) O lasrt ->
    satp (ge,le',M',ir',aux') O' lasrt ->
    M' = M /\ O' = O.

Definition GoodLInvAsrt (p : LocalInv):= forall t lg, GoodLocalInvAsrt (p t lg) /\ p_exact (p t lg).

Definition CurTid t :=  (EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t).

Definition LINV p t lg :=  p t lg ** [|GoodLInvAsrt p|].

Definition p_local (p : LocalInv) (t:tid) lg  := CurTid t **  LINV p t lg.

Definition CurLINV p t := EX lg, CurTid t **  LINV p t lg ** Atrue.


(**For specifying the spawned tasked in ucos**)
Definition  init_lg := (logic_val  (Vint32 (Int.repr 1%Z)) :: nil).
(**Configure it in terms of different target kernels***)

Definition  absimplication sc (li : LocalInv) (p p' : asrt) (t : tid) := 
  forall (s : taskst) (O : osabst) (gamma : absop),
    (s, O, gamma) |= p /\ satp s O  (CurLINV li t)  ->
    exists O' gamma',
      hmstepstar sc gamma O gamma' O' /\ (s, O', gamma') |= p' /\
      satp s O'  (CurLINV li t)  .

Definition sched_self sc (O : osabst) :=
  exists t, get O curtid = Some (oscurt t) /\ sc O t.

Inductive absinferfull : ossched ->LocalInv ->  asrt -> asrt -> tid -> Prop :=
| absinfer_eq' :
    forall p sc li t,
      absinferfull sc li p p t
                   
| absinfer_trans' :
    forall p q r sc li t,
      absinferfull sc li p q t -> absinferfull sc li  q r t -> absinferfull sc li  p r t
                                                                            
| absinfer_disj':
    forall p1 p2 q1 q2 sc li t,
      absinferfull sc li p1 q1 t ->
      absinferfull sc li p2 q2 t ->
      absinferfull sc li (p1\\//p2) (q1\\// q2) t

| absinfer_conseq' :
    forall p q p' q' sc li t, 
      q ==> q' ->
      absinferfull sc li p q  t->
      p'==> p -> absinferfull sc li p' q' t

| absinfer_ex' :
    forall  (tp:Type) (p:tp->asrt) q sc li t,
      (forall x,absinferfull sc li (p x) q t)  -> absinferfull sc li  (EX x:tp,p x) q t 
                                                               
| absinfer_frm' :
    forall p q r sc li t,
      can_change_aop r ->
      p ==> (CurLINV li t)  ->
      absinferfull sc li p q t -> absinferfull sc li (p ** r) (q ** r) t
                                               
| absinfer_prim':
    forall p q step vl v sc li t,
      can_change_aop p ->
      can_change_aop q ->
      absimplication sc li (<||step (|vl|)||> ** p) (<||END v||> ** q) t
      -> absinferfull sc li (<||step (|vl|)||> ** p) (<||END v||> ** q) t
                      
| absinfer_seq': forall p q s1 s2 s1' sc li t,
                   can_change_aop p ->
                   can_change_aop q -> 
                   absinferfull sc li (<||s1||> ** p) (<||s1'||> ** q) t ->
                   absinferfull sc li  (<||s1 ;; s2 ||> **p ) (<||s1';;s2||>**q) t

                                
| absinfer_seq_end': forall p q s v sc li t,
                       can_change_aop p ->
                       can_change_aop q -> 
                       p ==> q ->
                       absinferfull sc li  (<||END v ;; s ||> **p ) (<||s||> ** q) t
                                    
| absinfer_choice1':
    forall p q s1 s2 sc li t,
      can_change_aop p ->
      can_change_aop q -> 
      p ==> q -> 
      absinferfull sc li (<||s1 ?? s2 ||> ** p) (<||s1||> ** q) t
                   
| absinfer_choice2' :
    forall p q s1 s2 sc li t,
      can_change_aop p ->
      can_change_aop q -> 
      p ==> q -> 
      absinferfull sc li (<||s1 ?? s2 ||> ** p ) (<||s2||> ** q) t
                   
|absinfer_assume' :
   forall  p (b:absexpr) q sc li t,
     can_change_aop p ->
     can_change_aop q ->
     p  ==> q ->
     (forall s, (s |= p) -> b (getabst s)) ->     
     absinferfull sc li (<||ASSUME b||> ** p) (<||END None||> ** q) t
                  
|absinfer_sched' :
   forall  p (b:absexpr) q sc li t,
     can_change_aop p ->
     can_change_aop q ->
     p  ==> q ->
     (forall s, (s |= p) -> sched_self sc  (getabst s)) ->     
     absinferfull sc li (<||sched||> ** p) (<||END None||> ** q) t.

Notation "  '#' sc , li , t '⊢' p '⇒' q " := (absinferfull sc li  p q t) (at level 80).

Definition match_tid_prio (tls:  TcbMod.map) (v v' : val) := 
  (exists pr a tid msg, v = Vptr tid /\
                        get tls tid = Some (pr, a, msg) /\ v' = Vint32 pr).

Definition  retpost (p : fpost) : Prop :=
  forall s vl v logicl tid, sat s (getasrt (p vl v logicl tid)) -> v <> None.

Fixpoint GoodStmt' s := 
  match s with
    | sskip _ => True
    | sassign _ _ => True
    | sif _ s1 s2 => GoodStmt' s1 /\ GoodStmt' s2
    | sifthen _ s => GoodStmt' s
    | swhile _ s' => GoodStmt' s'
    | sret => True
    | srete _ => True
    | scall f _ => True
    | scalle _ f _ => True
    | sseq s1 s2 => GoodStmt' s1 /\ GoodStmt' s2
    | sprint _ => True
    | sfexec _ _ _ => False
    | sfree _ _ => False
    | salloc _ _ => False
    | sprim _ => True
    | hapi_code _ => False
  end.



Definition GoodSched (sd : ossched) :=  
  (
    forall x a y t, join x a y -> sd x t -> sd y t
  ) /\
  (
    forall x t,  sd x t ->
                 (exists tcbls tcb,
                    get x abstcblsid =
                    Some (abstcblist tcbls) /\ 
                    get tcbls t = Some tcb)
  ) /\
  (
    forall O1 O2 O t t',
      join O1 O2 O ->
      sd O1 t ->
      sd O t' ->
      sd O1 t'
  ).


Fixpoint GoodFrm (p : asrt){struct p}: Prop :=
  match p with
    | Aie _ => False
    | Ais _ => False
    | ATopis  _ =>  False
    | Aisr _ => False
    | Acs _ => False         
    | p' //\\ q' =>  GoodFrm  p' /\ GoodFrm q'
    | p' \\// q' => GoodFrm  p' /\ GoodFrm  q'
    | p' ** q' => GoodFrm p' /\ GoodFrm q'
    | Aexists t p' => forall x, GoodFrm (p' x)
    | Anot _ => False
    | Aop _ => False
    | _ => True
  end.

Definition GoodI (I:Inv) (sd : ossched) (pa:LocalInv):=
  (
    forall o O O' ab OO, (o,O,ab) |= starinv_noisr I 0%nat (S INUM) -> join O O' OO-> O' = empabst
  ) /\ 
  (
    forall o O ab tid, (o,O,ab)|= SWINVt I tid->  
                       exists b tp, get (get_genv (get_smem o)) OSTCBCur = Some (b,(Tptr tp)) /\
                                    load (Tptr tp) (get_mem (get_smem o)) (b,0%Z) = Some (Vptr tid) /\
                                    get O curtid = Some (oscurt tid)
  )  /\
  (
    forall o O ab tid b tp M' ct,
      (o,O,ab)|= SWINVt I ct ->
      (o,O,ab) |= AHprio sd tid ** Atrue ->
      get (get_genv (get_smem o)) OSTCBCur = Some (b,(Tptr tp))  -> 
      store (Tptr tp) (get_mem (get_smem o)) (b,0%Z) (Vptr tid) = Some M' -> 
      exists tls,
        get O abstcblsid = Some (abstcblist tls)/\
        (
          (
            indom tls ct /\
            (substaskst o M', set O curtid (oscurt tid), ab) |= SWINVt I tid
          ) \/
          
          (
            ~ indom tls ct /\
            forall Mx Ox MM OO,
              satp (substaskst o Mx) Ox (EX lg, pa ct lg) ->
              join M' Mx MM ->
              join O Ox OO ->
              (substaskst o MM, set OO curtid (oscurt tid), ab) |= SWINVt I tid)
        )
  )/\ 
  GoodSched sd. 



Definition SWPRE_NDEAD sd x tc:= SWPRE sd x tc //\\ EX tls,Aabsdata abstcblsid (abstcblist tls) ** [| indom tls tc |] ** Atrue.

Definition SWPRE_DEAD sd x tc:= SWPRE sd x tc //\\ EX tls,Aabsdata abstcblsid (abstcblist tls) ** [|~indom tls tc |] ** Atrue.

(*
Definition p_local (p : LocalInv) (t:tid) lg  :=
  (EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t) ** p t lg ** [|GoodLInvAsrt p|].
 *)

Inductive InfRules: funspec -> ossched -> LocalInv -> Inv -> retasrt -> asrt ->
                    asrt -> stmts -> asrt -> tid -> Prop:=
(*| skip_rule :  forall (Spec:funspec) (I:Inv) (r:retasrt) (ri:asrt) (t:tid)
        (p:asrt) (v:option val),  InfRules Spec I r ri t p (sskip v) p (*done*)*)
| pfalse_rule: forall Spec  sd I r ri q s pa t, 
                 InfRules Spec sd pa I r ri
                          Afalse s q t
| pure_split_rule: forall Spec sd I r ri p q (pu:Prop) s pa t, 
                     (pu -> InfRules Spec sd pa I r ri 
                                     p s q t) -> (InfRules Spec sd pa I r ri 
                                                           (p**[|pu|]) s q t)

| genv_introret_rule :  forall Spec sd I r ri p q  s G pa t, 
                          InfRules Spec sd pa I r ri p s q  t->
                          InfRules Spec sd pa I (fun v => (Agenv G //\\ r v)) ri
                                   (Agenv G //\\ p) s q t

| genv_introexint_rule :  forall Spec sd I r ri p q s G pa t, 
                            InfRules Spec sd pa I r ri p s q t ->
                            InfRules Spec sd pa I r (Agenv G //\\ ri)
                                     (Agenv G //\\ p) s q t

| ret_rule : forall Spec sd  I r p pa t,   
               (p ==> r None) ->
               InfRules Spec sd pa I r Afalse p sret Afalse  t(*done*)


| iret_rule : forall Spec sd I ri p pa t,  (p ==>  ri ) -> 
                                           InfRules Spec  sd pa I arfalse ri p  (sprim exint ) Afalse  t(*done*)
                                                    
| rete_rule :  forall (Spec:funspec) sd I r p e v t pa tid, 
                 (p ==>  r (Some v) //\\  Rv e@t == v) ->
                 InfRules Spec sd pa I r Afalse p (srete e) Afalse tid
                          

| call_rule :forall f Spec sd I r ri pre post p P el vl logicl tp tl pa t,
               GoodFrm p ->
               Spec f = Some (pre, post, (tp, tl)) ->
               P ==> PRE [pre, vl, logicl, t] ** p ->
               P ==> Rvl el @ tl == vl ->
               tl_vl_match tl vl = true ->
               PRE [pre, vl, logicl, t] ==> CurLINV pa t ->
               EX v : option val, POST [post, vl, v, logicl, t] ==> CurLINV pa t ->
                InfRules Spec sd pa I r ri (P) (scall f el) 
                        (EX v,POST[post, vl, v ,logicl,t] ** p ) t (*done*)
                        
      | calle_rule :  forall f e l Spec sd  I r ri pre post p P el v' vl logicl tp tl pa t,  
                        GoodFrm p ->
                        retpost post ->
                        Spec f = Some (pre, post, (tp, tl)) ->
                        P ==> PRE [pre, vl, logicl, t] ** PV l @ tp |-> v' ** p ->
                        P ==> Rvl el @ tl == vl ->
                        PV l @ tp |-> v' ** p ==> Lv e @ tp == l ->
                        tl_vl_match tl vl = true ->
                        PRE [pre, vl, logicl, t] ==> CurLINV pa t ->
                        EX v : option val, POST [post, vl, v, logicl, t] ==> CurLINV pa t ->
                                           InfRules Spec sd pa I r ri ( P)
                                                    (scalle e f el) (EX v, POST[post, vl, Some v,logicl,t] ** PV l @ tp|-> v ** p )  t(*done*)

      | calle_rule_lvar: forall f x Spec sd t I r ri pre post P p el v' vl logicl tp tl pa tid,  
                           GoodFrm p ->
                           retpost post ->
                           Spec f = Some (pre, post, (tp, tl)) ->
                           P ==> PRE [pre, vl, logicl, tid] ** LV x @ t |-> v' ** p ->
                           P ==> Rvl el @ tl == vl ->
                           tl_vl_match tl vl = true ->
                           PRE [pre, vl, logicl, tid] ==> CurLINV pa tid ->
                           EX v : option val, POST [post, vl, v, logicl, tid] ==>
                                                   CurLINV pa tid ->
                                              InfRules Spec sd pa I r ri (P )
                                                       (scalle (evar x) f el) (EX v, POST[post, vl, Some v,logicl,tid] ** LV x @ t |-> v ** p) tid

| conseq_rule : forall   Spec  sd  I r ri p' p q q' s pa t, 
                  (p' ==>  p) ->  (q ==> q') ->
                  InfRules Spec sd pa I r ri p s q t->
                  InfRules Spec sd pa I r ri p' s q' t (*done*)

| r_conseq_rule : forall   Spec sd  I r ri r' p q ri' s pa t, 
                    (forall v,r v ==> r' v) ->  (ri ==> ri') ->
                    InfRules Spec  sd pa I r ri p s q t->
                    InfRules Spec sd pa I r' ri' p s q t (*done*)

| abscsq_rule_full : forall   Spec sd  I r ri p' p q q' s pa t, 
                       #sd,pa,t ⊢ p'⇒p  -> #sd, pa, t ⊢ q ⇒ q' ->
                                                    InfRules Spec sd pa I r ri p s q  t->
                                                    InfRules Spec sd pa I r ri p' s q' t (*done*)

  | seq_rule : forall  Spec sd  I r ri p p' q  s1 s2 pa t, 
                     InfRules Spec sd pa I r ri p s1 p' t -> 
                     InfRules Spec sd pa I r ri p' s2 q t ->
                     InfRules Spec sd pa I r ri p (sseq s1 s2) q t (*done*)
                              
   | if_rule :  forall Spec  sd I r ri p q e tp s1 s2 pa t,
                     (p ==> EX v , Rv e @ tp ==  v) ->
                     InfRules Spec sd pa I r ri (p//\\ Aistrue e) s1 q t  -> 
                     InfRules Spec sd pa I r ri (p //\\ Aisfalse e) s2 q t ->
                     InfRules Spec sd pa I r ri p (sif e s1 s2) q t (*done*)
                              
   | ift_rule :  forall Spec sd  I r ri p q e tp s pa t,
                      (p ==> EX v , Rv e @ tp ==  v) ->
                      (p//\\ Aisfalse e ==> q) ->
                      InfRules Spec sd pa I r ri (p//\\ Aistrue e) s q t  -> 
                      InfRules Spec  sd pa I r ri p (sifthen e s) q  t(*done*)


   | while_rule :  forall Spec sd  I r ri p  e s  tp pa t,  
                        ( p ==> EX v , Rv e @ tp ==  v) ->
                        InfRules  Spec sd pa I r ri ( p //\\ (Aistrue e)) s p t  -> 
                        InfRules Spec sd pa I r ri p (swhile e s) (p //\\ (Aisfalse e)) t   (*done*)

   | frame_rule :  forall Spec sd I p q frm s aop aop' pa t, 
                     GoodI I sd pa ->
                     GoodStmt' s ->
                     GoodFrm frm ->
                     p ==> CurLINV pa t ->
                     InfRules Spec sd pa I arfalse Afalse ( <|| aop ||> ** p) s ( <|| aop' ||> ** q) t -> 
                     InfRules Spec  sd pa I arfalse Afalse ( <|| aop ||> ** p ** frm ) s (<|| aop' ||> ** q ** frm) t (*done*)

   | frame_rule_all:  forall Spec sd  I r ri p q frm s pa t, 
                        GoodI I sd pa ->
                        GoodStmt' s ->
                        GoodFrm frm ->
                        p ==> CurLINV pa t ->
                        InfRules  Spec sd pa I r ri p s q t ->
                        InfRules Spec sd pa I  (fun v =>(r v) ** frm)
                                 (ri**frm) (p ** frm ) s (q ** frm )  t(*done*)

   | retspec_intro_rule :  forall Spec sd pa I r ri p q s t, 
                                InfRules Spec sd pa I arfalse Afalse p s q t -> 
                                InfRules Spec  sd pa I r  ri p  s q  t (*done*)

   | assign_rule : forall Spec  sd I r ri p e1 e2 l v1 v2 tp1 tp2 aop pa t,  
                        assign_type_match tp1 tp2 ->  
                        ((p ** PV l @ tp1|-> v1) ==> Lv e1 @ tp1 == l //\\ Rv e2 @ tp2 == v2) ->
                        (p ** PV l @ tp1 |-> v2 ==> CurLINV pa t) ->
                        InfRules Spec sd pa I r ri ((<||aop||> ** p ** PV l @ tp1 |-> v1) 
                                                   ) (sassign e1 e2) (<|| aop ||> ** p ** PV l @ tp1 |-> v2 ) t (*done*)

   | encrit1_rule : forall Spec sd I r ri isr is cs i aop pa t  P,
                         GoodFrm P ->
                         InfRules Spec sd pa I r ri 
                                  ( <|| aop ||> ** OS[isr, true, is, cs] ** (ATopis i) ** (Apure (i <= INUM)%nat) ** P ) 
                                  (sprim encrit)
                                  (<||aop||> ** OS[isr, false, is, true::cs] ** (invlth_isr I O i) ** P) t (*done*)


   | encrit2_rule :  forall Spec sd  I r ri isr is cs  aop pa t  P,
                          GoodFrm P ->
                          InfRules Spec sd pa I r ri 
                                   (<||aop||> ** OS[isr, false, is, cs] ** P) 
                                   (sprim encrit)
                                   (<||aop||> ** OS[isr, false, is, false::cs] ** P) t

   | excrit1_rule : forall Spec sd  I r ri isr is cs  i aop pa t  P,
                         GoodFrm P ->
                         P ==> CurLINV pa t ->
                         InfRules Spec sd pa I r ri 
                                  (<||aop||> ** OS[isr, false, is, true::cs] ** (ATopis i) ** (invlth_isr I O i) ** P)
                                  (sprim excrit)
                                  (<||aop||> ** OS[isr, true,  is, cs] ** P) t

   | excrit2_rule :  forall Spec  sd I r ri isr is cs aop pa t  P,
                          GoodFrm P ->            
                          InfRules Spec sd pa I r ri 
                                   (<||aop||> ** OS[isr, false, is, false::cs] ** P)
                                   (sprim excrit)
                                   (<||aop||> ** OS[isr, false, is, cs] ** P) t
                                   
   | cli1_rule :forall Spec sd  I r ri isr is i aop pa t P,
                     GoodFrm P ->
                     InfRules Spec sd pa I r ri 
                              ( <||aop||> ** OS[isr, true, is, nil]  ** (ATopis i) ** (Apure (i <= INUM)%nat) ** P 
                              )
                              (sprim cli)
                              (<||aop||> ** OS[isr, false,is, nil] ** (invlth_isr I O i) ** P) t
                              
   | cli2_rule : forall Spec  sd I r ri isr is aop pa t  P,
                      GoodFrm P ->
                      InfRules Spec sd pa I r ri 
                               (<||aop||> ** OS[isr, false, is, nil] ** P)
                               (sprim cli)
                               (<||aop||> ** OS[isr, false, is, nil] ** P) t

   | sti1_rule : forall Spec  sd I r ri isr i is  aop pa t P,  
                      GoodFrm P ->
                      P ==> CurLINV pa  t ->
                      InfRules Spec  sd pa I r ri 
                               (<||aop||> ** OS[isr, false, is, nil] **  (ATopis i) ** (invlth_isr I O i) ** P)   
                               (sprim sti)
                               (<||aop||> ** OS[isr, true, is, nil] ** P) t

   | sti2_rule :  forall Spec pa sd I r ri isr is aop t P,  
                    GoodFrm P ->
                    InfRules Spec sd pa I r ri 
                             (<||aop||> ** OS[isr, true, is, nil] ** P)
                             (sprim sti)
                             (<||aop||> ** OS[isr, true, is, nil] ** P) t

   | switch_rule :  forall  Spec sd lg  I r ri x li   t aop P P'  Px is cs,
                      GoodFrm Px ->
                      P ==> P' ** Px ->
                      P' ==> <|| sched;; aop ||>  ** SWINVt I t ** Ais is ** Acs cs  ->
                      P' ==> SWPRE_NDEAD sd x t ->
                      Px ==> LINV li t lg ** Atrue ->
                      InfRules Spec sd li  I r ri  P  
                               (sprim (switch x))  (<|| aop ||>  ** SWINVt I t ** Ais is ** Acs cs ** Px) t

   | switchdead_rule :
       forall  Spec sd lg  I r ri x li   t aop P P'  Px is cs,
         GoodFrm Px ->
         P ==> P' ** Px ->
         P' ==> <|| sched;; aop ||>  ** SWINVt I t ** Ais is ** Acs cs  ->
         P' ==> SWPRE_DEAD sd x t  ->
         Px ==> LINV li t lg ** Atrue ->
         InfRules Spec sd li  I r ri  P  
                 (sprim (switch x))  Afalse t

                                     
   | checkis_rule : forall  Spec sd pa I r ri x aop isr is ie cs v t P,
                         GoodFrm P ->
                         P ==> CurLINV pa t->
                         InfRules Spec sd pa I r ri
                                  (<||aop||> ** OS[isr, ie, is, cs] **  LV x @ Tint32 |-> v **  P) 
                                  (sprim (checkis x))
                                  (<||aop||> ** OS[isr, ie, is, cs] **  LV x @ Tint32 |-> (is_length is) ** P)  t

   | eoi_ieon_rule  :  forall Spec sd pa I r ri isr is id cs  i aop t  P,  
                        (0 <= Int.unsigned id < Z.of_nat INUM)%Z ->
                         i = Z.to_nat (Int.intval id) ->
                         GoodFrm P ->
                         P ==> CurLINV pa t ->
                         isr i = true ->
                          InfRules Spec sd pa I r ri 
                                     (  <||aop||> ** OS[isr, true, i::is, cs] ** (getinv (I i)) **  P)
                                     (sprim (eoi id))
                                     (  <||aop||> ** OS[isrupd isr i false, true, i::is, cs]  ** P) t
                                     
   | eoi_ieoff_rule  :  forall Spec sd pa I r ri isr is id  i cs aop t  P,  
                          (0 <= Int.unsigned id < Z.of_nat INUM)%Z ->
                          i = Z.to_nat (Int.unsigned id) ->
                          GoodFrm P ->
                          InfRules Spec sd pa I r ri 
                                      (<||aop||> ** OS[isr, false, i::is, cs] ** P)
                                      (sprim (eoi id))
                                      (<||aop||> ** OS[isrupd isr i false, false, i::is, cs] ** P) t

   | ex_intro_rule : forall Spec sd pa I r ri q s {tp:Type} p t,
                          (forall v',InfRules Spec sd pa I r ri (p v') s q t) ->
                          InfRules Spec sd pa I r ri (EX v:tp,p v) s q t

   | disj_rule : forall Spec sd pa I r ri p1 p2 s q t,
                      InfRules Spec sd pa I r ri p1 s q  t ->
                      InfRules Spec sd pa I r ri p2 s q t ->
                      InfRules Spec sd pa I r ri (p1\\//p2) s q t

                               
  | cre_rule :  forall (Spec : funspec) (sd : ossched) 
                           (I : Inv) (r : retasrt) (ri P : asrt) 
                           (aop : spec_code) (tls : TcbMod.map) 
                           (t1 : addrval) (prio : int32) (tls' : TcbMod.map)
                           (v1 v2 : val) (e1 e2 e3 : expr) (tp1 tp3 : type)
                           (pa : LocalInv) (t : tid) isr ie is cs,
                      GoodLInvAsrt pa ->
                      GoodFrm P ->
                      joinsig t1 (prio, rdy, Vnull) tls tls'  ->
                      indom tls t ->
                      P ==>
                       Rv e1 @ tp1 == v1 //\\
                       Rv e2 @ Tptr Tvoid == v2 //\\
                       Rv e3 @ tp3 == Vptr t1 //\\  CurLINV pa t ->
                      InfRules Spec sd pa I r ri 
                               (
                                 <|| spec_crt v1 v2 (Vint32 prio);; aop ||>  ** P **
                                     pa t1 init_lg  **
                                     Aabsdata abstcblsid (abstcblist tls) **
                                     Aabsdata curtid (oscurt t) **
                                     OS[isr, ie, is, cs]  
                               ) 
                               (sprim (stkinit e1 e2 e3))
                               (
                                 <|| aop ||>   ** P **
                                     Aabsdata abstcblsid (abstcblist tls') ** 
                                     Aabsdata curtid (oscurt t)  **
                                     OS[isr, ie, is, cs]
                               ) t

  | delself_rule : forall pa P  prio st msg tls' tls t e tp  aop r ri sd Spec I isr ie is cs,
                         GoodLInvAsrt pa ->
                         GoodFrm P ->
                         joinsig t (prio, st, msg) tls' tls  ->
                         P ==>  Rv e @ tp == Vptr t //\\  CurLINV pa t ->
                         InfRules Spec sd pa I r ri 
                                 (
                                   <|| spec_del  (Vint32 prio);; aop ||>  **
                                       P ** Aabsdata abstcblsid (abstcblist tls) **
                                       Aabsdata curtid (oscurt t) **
                                       OS[isr, ie, is, cs]  
                                 ) 
                                 (sprim (stkfree e))
                                 (
                                   <|| aop ||>  ** P  **
                                       Aabsdata abstcblsid (abstcblist tls') ** 
                                       Aabsdata curtid (oscurt t) **
                                       OS[isr, ie, is, cs]  
                                 ) t

 | delother_rule : forall pa P  prio st msg tls' tls t e tp t1 aop r ri sd Spec I isr ie is cs,
                         GoodLInvAsrt pa ->
                         GoodFrm P ->
                         joinsig t1 (prio, st, msg) tls' tls  ->
                         indom tls t ->
                         t <> t1 ->
                         P ==>  Rv e @ tp == Vptr t1 //\\  CurLINV pa t ->
                         InfRules Spec sd pa I r ri 
                                 (
                                   <|| spec_del  (Vint32 prio);; aop ||>  **
                                       P ** Aabsdata abstcblsid (abstcblist tls) **
                                       Aabsdata curtid (oscurt t) **
                                       OS[isr, ie, is, cs]  
                                 ) 
                                 (sprim (stkfree e))
                                 (
                                   <|| aop ||>  ** P ** (EX lg,  pa t1 lg)  **
                                       Aabsdata abstcblsid (abstcblist tls') ** 
                                       Aabsdata curtid (oscurt t) **
                                       OS[isr, ie, is, cs]  
                                 ) t.

Notation   " '{|' F , sd , pa , I , r , ri '|}' '|-' t '{{' p '}}' s '{{' q '}}'" :=
  (InfRules F sd pa I r ri p s q t) (at level 50). 

Definition EqDom (P : progunit) (F : funspec) : Prop :=
  forall f, (exists a, P f = Some a) <-> (exists b, F f = Some b).


Fixpoint getlenvdom  (dl:decllist) : edom :=
  match dl with
    |  dnil => nil
    |  dcons x t dl' => (x,t)::(getlenvdom dl')
  end. 

Fixpoint in_decllist (x:var) (dl : decllist) : bool :=
  match dl with
    | dnil => false
    | dcons x' t' dl' => orb (Zeq_bool x x')  (in_decllist x dl')
  end.


Fixpoint good_decllist (dl: decllist) : bool :=
  match dl with
    | dnil => true
    | dcons x t dl' => andb ( negb (in_decllist x dl')) (good_decllist dl')
  end.

Fixpoint buildp (dl:decllist) (vl:vallist) :option asrt:=
  match good_decllist dl with
    | true =>
      match dl, vl with
        | dnil,nil => Some Aemp
        | dcons x t dl',cons v vl' => match buildp dl' vl' with
                                        | Some p => Some (Astar (LV x @ t |-> v) p)
                                        | None => None
                                      end
        | dcons x t dl',nil => match buildp dl' nil with
                                 | Some p => Some (Astar (Aexists (fun (v:val) => 
                                                                     LV x @ t |-> v)) p)
                                 | None => None
                               end
        | _,_ => None
      end
    | false => None
  end.


Fixpoint buildq (dl:decllist) : option asrt:=
  if good_decllist dl then
    match dl with
      | dnil => Some Aemp
      | dcons x t dl' => match buildq dl' with
                           | Some p => Some ( (EX v, LV x @ t|-> v)  ** p )
                           | None => None
                         end
    end
  else None.


Fixpoint dl_vl_match (dl:decllist) (vl:vallist) :=
  match dl with
    | dnil => match vl with
                | nil => true
                | _ => false
              end
    | dcons x t dl' => match vl with
                         | v :: vl' => if type_val_match t v then dl_vl_match dl' vl' else false
                         | _ => false
                       end
  end.

(*
Definition BuildPreA (p:progunit) (f:fid) (abs:osapi) (vl:vallist) G:option asrt:= 
    match p f with
      | Some (t, d1, d2, s) => 
        match dl_vl_match d1 (rev vl) with 
          | true =>
            match buildp (revlcons d1 d2) vl with
              | Some p =>Some (Aconj (Agenv G)
                                     (Aconj 
                                        (Astar (p ** Aie true ** Ais nil ** Acs nil ** Aisr empisr)
                                               (A_dom_lenv (getlenvdom  (revlcons d1 d2)))) 
                                        (Aop (fst abs (rev vl))))) 
              | _ => None
            end
          | false => None
        end
      | _ => None
    end.


Definition BuildRetA (p:progunit) (f:fid) (abs:osapi) (vl:vallist) G:option retasrt:= 
  match p f with
    | Some (t, d1, d2, s) => match buildq (revlcons d1 d2) with
                               | Some p =>
                                 Some
                                   (fun (v:option val) => 
                                      (Aconj (Agenv G)
                                             (Aconj (Astar
                                                       (p** Aie true ** Ais nil ** Acs nil ** Aisr empisr)
                                                       (A_dom_lenv (getlenvdom  (revlcons d1 d2))))
                                                    (Aop (spec_done v)))))
                                       |_ => None
                                     end
    | _ => None
 end.
 *)




Definition BuildPreI (p:progunit) (f:fid) (vl:vallist) (logicl:list logicvar) (fp:fpre) tid : option asrt:= 
  match p f with
    | Some (t, d1, d2, s) => 
      match dl_vl_match d1 (rev vl) with 
        | true =>
          match buildp (revlcons d1 d2) vl with
            | Some p => Some  (p ** (getasrt (fp (rev vl) logicl tid))**
                                 (A_dom_lenv (getlenvdom  (revlcons d1 d2))))
            | _ => None
          end
        | false => None
      end
    | _ => None
  end.

Definition BuildRetI (p:progunit) (f:fid) (vl:vallist) (logicl:list logicvar) (fq:fpost) tid :option retasrt:= 
  match p f with
    | Some (t, d1 , d2,  s) =>
      match buildq (revlcons d1 d2) with
        | Some p => Some (fun (v:option val) =>
                            (p **  (getasrt (fq (rev vl) v logicl tid)) **
                               (A_dom_lenv (getlenvdom  (revlcons d1 d2)))))
        | _ => None
      end
    | _ => None
  end.

Definition lift (q : asrt):  retasrt := fun _ => q.

Definition WFFunEnv (P:progunit) (FSpec:funspec) (sd:ossched) pa (I:Inv) :Prop:=
  EqDom P FSpec /\
  forall f pre post t tl, FSpec f = Some (pre, post, (t, tl)) -> 
                          exists  d1 d2 s,   P f = Some (t, d1, d2, s)/\   
                                             tlmatch tl d1 /\
                                             good_decllist (revlcons d1 d2) = true /\ 
                                             (
                                               forall vl p r logicl tid,
                                                 Some p = BuildPreI P f vl logicl pre tid-> 
                                                 Some r = BuildRetI P f vl logicl post tid->
                                                 InfRules FSpec sd pa I r Afalse p s Afalse tid
                                             ).



(*----------------------*)

Definition EqDomAPI (api:progunit) (aspec:osapispec) :=
  (forall f, 
     (exists fdef, api f = Some fdef) <-> (exists fspec,aspec f=Some fspec))/\
  (forall f fdef fspec,  api f = Some fdef -> aspec f = Some fspec ->
                         tlmatch (snd (snd fspec)) (snd (fst (fst fdef))) /\ fst (fst (fst fdef)) = (fst (snd fspec)) ).

Definition EqDomInt (P:intunit) (intspec:osintspec) :=
  (forall i,
     (exists idef, P i = Some idef) <-> (exists absi,intspec i=Some absi)).

Definition InitAsrt:= osstate -> osabst -> Prop.


Definition retfalse:= fun (v:option val)=> Afalse.

Fixpoint dladd (d1 d2 : decllist) : decllist :=
  match d1 with
    | dnil => d2
    | dcons x y d1' => revlcons d1' (dcons x y d2)
  end.

Fixpoint dl_add d1 d2:= 
  match d1 with
    | dnil => d2
    | dcons a b d1' => dcons a b (dl_add d1' d2)
  end.



Definition BuildPreA':= 
  fun (p : progunit) (f : fid) (abs : osapi) (vl : vallist)  (pa : LocalInv) t lg=>
    match p f with
      | Some (_, d1, d2, _) =>
        match dl_vl_match d1 (rev vl) with
          | true =>
            match buildp (dladd d1 d2) vl with
              | Some p2 =>
                Some   
                  ( ((<|| (fst abs) (rev vl) ||> ** p_local pa t lg ** p2 **Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** A_dom_lenv (getlenvdom (revlcons d1 d2))))
                  
              | None => None
            end
          |false => None
        end
      | None => None
    end.


Definition BuildRetA':= 
  fun (p : progunit) (f : fid) (_ : osapi) (_ : vallist) (pa : LocalInv) t lg=>
    match p f with
      | Some (_, d1, d2, _) =>
        match buildq (dladd d1 d2) with
          | Some p2 =>
            Some
              (fun v : option val =>
                 ((  <|| spec_done v ||>  ** p_local pa t lg **p2 **  Aie true ** Ais nil ** Acs nil ** Aisr empisr) **  A_dom_lenv (getlenvdom (revlcons d1 d2))) )
              
          | None => None
        end
      | None => None
    end.

Inductive APIRule: progunit -> osapispec -> funspec -> ossched -> LocalInv -> Inv  -> list logicvar-> Prop :=
| api_rule :
    forall (P:progunit) (apispec:osapispec) (pa : LocalInv) (Spec:funspec) (sd : ossched) (I : Inv) lg,
      EqDomAPI P apispec ->
      (
        forall (f:fid) ab vl p r ft tid, 
          apispec f = Some (ab,ft) ->
          Some p = BuildPreA' P f (ab,ft) vl pa tid lg->
          Some r = BuildRetA' P f (ab,ft) vl pa tid lg ->
          (
            exists  t d1 d2 s,
              P f = Some (t, d1, d2, s) /\
              InfRules Spec sd pa I r Afalse p s Afalse tid
          ) 
      ) ->
      APIRule P apispec Spec sd pa I lg.

Inductive InterRule: progunit -> funspec -> ossched -> LocalInv -> Inv  -> Prop :=
| inter_rule :
    forall (P : progunit) (FSpec : funspec) (sd : ossched) (I : Inv) pa,
      EqDom P FSpec ->
      (forall (f : fid) (pre : fpre) (post : fpost) (t : type) (tl : typelist),
         FSpec f = Some (pre, post, (t, tl)) ->
         exists d1 d2 s,
           P f = Some (t, d1, d2, s) /\
           tlmatch tl d1 /\
           (forall (vl : vallist) (p : asrt) (r : retasrt) (logicl : list logicvar) tid,
              Some p = BuildPreI P f vl logicl pre tid->
              Some r = BuildRetI P f vl logicl post tid->
              {|FSpec , sd, pa , I, r, Afalse|}|- tid {{p}} s {{Afalse}})) ->
      InterRule P FSpec sd pa I.


Definition iretasrt' (i:hid) (isrreg:isr) (si:is)  (I:Inv) :asrt:= 
  (Astar (Aop (spec_done None)) 
         (Astar (Aisr (isrupd isrreg i false))
                (Astar (Ais (cons i si))
                       (Astar (Acs  nil)
                              (IRINV I ** A_dom_lenv nil))))).

Definition ipreasrt' (i:hid) (isrreg:isr) (si:is) (ispec:spec_code) (I:Inv):=
  (Astar (Aop ispec)
         (Astar (Aisr (isrupd isrreg i true))
                (Astar (Ais (cons i si))
                       (Astar (Acs  nil) 
                              ((Astar (Aie false))  
                                 (isr_inv ** invlth_noisr I 0%nat i ** A_dom_lenv nil)))))). 


Definition BuildintPre (i:nat) i_spec (isrreg:isr) (si:is) (I:Inv) (pintpre:LocalInv) t lg:=
  match i_spec i with
    | None => None
    | Some ispec => Some (ipreasrt' i isrreg si ispec  I ** p_local pintpre t lg)
  end.

Definition BuildintRet (i:nat) (i_spec:osintspec) (isrreg:isr) (si:is) (I:Inv) (pa:LocalInv) t lg:=
  match i_spec i with
    | None => None
    | Some ispec => Some (iretasrt' i isrreg si I ** p_local pa  t lg)
  end.


Inductive ItrpRule: intunit -> osintspec ->  funspec -> ossched  -> LocalInv  -> Inv  -> Prop :=
| itrp_rule: forall (P:intunit) (intspec:osintspec) (pa: LocalInv)(Spec:funspec) sd (I:Inv),
               EqDomInt P intspec ->
               (
                 forall i isrreg si p r t  lg,
                   Some p = BuildintPre i intspec isrreg si I pa t lg->
                   Some r = BuildintRet i intspec isrreg si I pa t lg->
                   exists s,
                     P i = Some s /\
                     {|Spec , sd, pa , I, retfalse, r|}|-t {{p}}s {{Afalse}}
                                                           
               ) ->
               ItrpRule P intspec Spec sd pa  I.


Definition eqevntls (env: CltEnvMod.map) (tls:TcbMod.map) :=
  forall (t:tid), indom env t <-> indom tls t.

Definition eqisttls (lst:ltaskstset) (tls:TcbMod.map) :=
  forall (t:tid), indom lst t <-> indom tls t.

Definition eqdomSO (S : osstate)  (O:osabst) :=
  match S with
    | (G,pi,M,isr,lst) =>
      match get O abstcblsid with
        | Some (abstcblist tls) => eqevntls pi tls /\ eqisttls lst tls
        | _ => False
      end
  end.


Definition init_rdy (pa : tid-> list logicvar -> asrt) (t:tid)  lg := pa t lg ** [| GoodLInvAsrt pa |] **  OS [empisr, true, nil , nil ]  ** A_dom_lenv nil.

Definition init_cur I (pa : tid-> list logicvar -> asrt)  t lg := (INV I) ** (EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t)  ** init_rdy pa t lg.

Inductive initst: osstate -> osabst -> Inv -> LocalInv -> list logicvar -> Prop:=
| init_O: forall S O G envs M isr lst E auxs I pa t lg,
            S = ((G,envs,M),isr,lst) ->
            envs = sig t E ->
            lst = sig t auxs ->
            get O curtid = Some (oscurt t) ->
            (forall ab, sat (((G,E,M),isr,auxs),O,ab) (init_cur I pa t lg)) ->
            initst S O I pa lg
| init_S: forall S O G envs envs' M m M' isr lst lst' E auxs I pa t tc lg,
            S = ((G,envs,M),isr,lst) ->
            join (sig t E) envs' envs ->
            join (sig t auxs) lst' lst ->
            join m M' M ->
            get O curtid = Some (oscurt tc) ->
            t <> tc ->
            (forall ab, sat (((G,E,m),isr,auxs),emp,ab) (init_rdy pa t lg ** A_dom_lenv nil)) ->
            initst ((G,envs',M'),isr,lst') O I pa lg ->
            initst S O I pa lg.
(*
Definition side_condition I pa schedmethod init:=
  (
    GoodI I schedmethod /\
    (forall S O,  init S O ->
                      (forall o, (projS S tid) = Some o  ->
                         forall ab, sat ((pair o O),ab) (init_asrt I pa tid )) /\ eqdomSO S O) 
  ).
 *)
Definition side_condition I pa schedmethod init lg:=
  (
    GoodI I schedmethod pa /\
    (forall S O,  init S O ->
                  initst S O I pa lg/\ eqdomSO S O) 
  ).



Inductive TopRule : oscode -> osspec -> InitAsrt -> Prop :=
| top_rule: forall osc A (init:InitAsrt) (I:Inv) (lasrt: LocalInv )(Spec:funspec) 
                   pa pi ip apispec intspec schedmethod ,
              osc = (pa,pi,ip) ->
              A = (apispec,intspec,schedmethod) ->
              APIRule pa apispec Spec schedmethod lasrt I init_lg ->
              ItrpRule ip intspec Spec schedmethod lasrt I ->
              InterRule pi Spec schedmethod lasrt  I ->
              side_condition I lasrt  schedmethod init init_lg -> 
              TopRule osc A init.


(***Abstract Implications when local invariants do not specify high-level states *****)

Definition  NoAbs (p: LocalInv) := 
  forall  o O t, satp o O  (CurLINV p t) ->
                 forall O', satp o O'  (CurLINV p t).

Definition  absimp sc (p p' : asrt) := 
  forall (s : taskst) (O : osabst) (gamma : absop),
    (s, O, gamma) |= p ->
    exists O' gamma',
      hmstepstar sc gamma O gamma' O' /\ (s, O', gamma') |= p'.

Lemma absimp_imp_full:
  forall sc p p' li t,  
    absimp sc  p p' -> 
    NoAbs li ->
    absimplication sc li p p' t.
Proof.          
  intros.
  unfolds.
  intros.
  destruct H1.
  apply H in H1.
  simp join.
  do 2 eexists; splits; eauto.
Qed.


Inductive absinfer :  ossched -> asrt -> asrt -> Prop :=
| absinfer_eq :
    forall p sc,
      absinfer sc p p
               
| absinfer_trans :
    forall p q r sc,
      absinfer sc p q -> absinfer sc q r -> absinfer sc p r
                                                     
| absinfer_disj:
    forall p1 p2 q1 q2 sc,
      absinfer sc p1 q1 ->
      absinfer sc p2 q2 ->
      absinfer sc (p1\\//p2) (q1\\// q2)

| absinfer_conseq :
    forall p q p' q' sc, 
      q ==> q' ->
      absinfer sc p q ->
      p'==> p -> absinfer sc p' q'

| absinfer_ex :
    forall  (tp:Type) (p:tp->asrt) q sc,
      (forall x,absinfer sc (p x) q) -> absinfer sc (EX x:tp,p x) q 
(**                                   
| absinfer_frm :
    forall p q r sc,
     p ==> 
      can_change_aop r ->
      absinfer sc p q -> absinfer sc (p ** r) (q ** r)
 *)
                                                 
| absinfer_prim:
    forall p q step vl v sc,
      can_change_aop p ->
      can_change_aop q ->
      absimp sc (<||step (|vl|)||> ** p) (<||END v||> ** q)
      -> absinfer sc (<||step (|vl|)||> ** p) (<||END v||> ** q)
                  
| absinfer_seq: forall p q s1 s2 s1' sc,
                  can_change_aop p ->
                  can_change_aop q -> 
                  absinfer sc (<||s1||> ** p) (<||s1'||> ** q) ->
                  absinfer sc (<||s1 ;; s2 ||> **p ) (<||s1';;s2||>**q)

                           
| absinfer_seq_end: forall p q s v sc,
                      can_change_aop p ->
                      can_change_aop q -> 
                      p ==> q ->
                      absinfer sc (<||END v ;; s ||> **p ) (<||s||> ** q)
                               
| absinfer_choice1 :
    forall p q s1 s2 sc,
      can_change_aop p ->
      can_change_aop q -> 
      p ==> q -> 
      absinfer sc (<||s1 ?? s2 ||> ** p) (<||s1||> ** q)
               
| absinfer_choice2 :
    forall p q s1 s2 sc,
      can_change_aop p ->
      can_change_aop q -> 
      p ==> q -> 
      absinfer sc (<||s1 ?? s2 ||> ** p ) (<||s2||> ** q)
               
|absinfer_assume :
   forall  p (b:absexpr) q sc,
     can_change_aop p ->
     can_change_aop q ->
     p  ==> q ->
     (forall s, (s |= p) -> b (getabst s)) ->     
     absinfer sc (<||ASSUME b||> ** p) (<||END None||> ** q)
              
|absinfer_sched :
   forall  p (b:absexpr) q sc,
     can_change_aop p ->
     can_change_aop q ->
     p  ==> q ->
     (forall s, (s |= p) -> sched_self sc  (getabst s)) ->     
     absinfer sc (<||sched||> ** p) (<||END None||> ** q).

Notation " sc '⊢' p '⇒' q " := (absinfer sc p q) (at level 80).

Lemma  absinfer_imp_full:
  forall li sc p q t,
    NoAbs li ->
    absinfer sc p q ->
    absinferfull sc li p q t .
Proof.
  intros.
  inductions H0.   
  apply  absinfer_eq'.
  eapply absinfer_trans'; eauto.
  eapply absinfer_disj'; eauto.
  eapply absinfer_conseq'; eauto.
  eapply absinfer_ex'; eauto.
  eapply absinfer_prim'; eauto.
  eapply  absimp_imp_full; eauto.
  eapply  absinfer_seq'; eauto.
  eapply absinfer_seq_end'; eauto.
  eapply absinfer_choice1'; eauto.
  eapply absinfer_choice2'; eauto.
  eapply absinfer_assume' ; eauto.
  eapply absinfer_sched' ; eauto.
Qed.

Lemma   abscsq_rule : 
  forall   Spec sd  I r ri p' p q q' s pa t, 
    NoAbs pa ->
    sd ⊢ p'⇒p  ->  sd  ⊢ q ⇒ q' ->
    InfRules Spec sd pa I r ri p s q  t->
    InfRules Spec sd pa I r ri p' s q' t .
Proof.
  intros.
  eapply abscsq_rule_full; eauto.
  eapply absinfer_imp_full; eauto.
  eapply absinfer_imp_full; eauto.
Qed.
