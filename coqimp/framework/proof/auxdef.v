Require Import Classical.
Require Export Map.
Require Import include_frm.
Require Import Maps.
Require Import simulation.
(*the definition of dladd is the same of revlcons*)

Definition get_lint (os:oscode):= snd os.
Definition get_ifun (os:oscode):= snd (fst os).
Definition get_afun (os:oscode):= fst (fst os).

Definition task_no_dead :=
  fun (O : osabst) (t : tid) =>
    forall tls, get O abstcblsid = Some (abstcblist tls) -> indom tls t.

(*Definition task_no_dead O t:=
  exists tls, get O abstcblsid = Some (abstcblist tls) /\ indom tls t.
 *)

Definition no_fun_same (p1 p2:progunit):=
  (forall f, p1 f <> None -> p2 f = None) /\ forall f, (p2 f <> None -> p1 f = None).


Fixpoint dladd (d1 d2 : decllist) : decllist :=
  match d1 with
  | dnil => d2
  | dcons x y d1' => revlcons d1' (dcons x y d2)
  end.

Definition emple_tst (o:taskst):= 
  match o with
    | ((ge,le,m),isr,ls) => ((ge,(empenv:env),m),isr,ls)
  end.

(*Definition empisr:= fun (i:hid) => false.*)

Definition RdyChange (o:taskst):=
  match o with
    | (m , b, c) => (m,empisr,c) 
  end.

Definition retfalse:= fun (v:option val)=> Afalse.

Definition Aisrhid :=fun (ir:isr) (i:hid) (b:bool)=>
                       Aconj (Aisr ir) (Apure (ir i = b)).

Definition iretasrt (i:hid) (isrreg:isr) (si:is) (I:Inv) G lasrt tid lg:asrt:= 
  (Aconj (Agenv G)
         (
         (
         (Aop (spec_done None)) **
         (Aisr (isrupd isrreg i false)) **
         (Ais (cons i si)) **
         (Acs  nil) **
         IRINV I ** A_dom_lenv nil
         ) **  p_local lasrt tid lg)).

Definition ipreasrt (i:hid) (isrreg:isr) (si:is) (ispec:spec_code) (I:Inv) G lasrt tid lg:=
  (Aconj (Agenv G) 
        (( (Aop ispec) **
                (Aisr (isrupd isrreg i true)) **
                    (Ais (cons i si)) **
                             (Acs  nil) **
                                    (Aie false) **
                                        (isr_inv) ** (invlth_noisr I 0 i ** A_dom_lenv nil))  **  p_local lasrt tid lg )). 

Definition eqdomOS (OS1:oscode) (A:osspec) :=
  match OS1 with
    | (api, ifun, intc) => 
      match A with
        | ( aspec, ispec,sd)
          => (forall f, 
                (exists fdef, api f = Some fdef) <-> (exists fspec,aspec f=Some fspec))/\
             (forall f fdef fspec,  api f = Some fdef -> aspec f = Some fspec ->
             tlmatch (snd (snd fspec)) (snd (fst (fst fdef))) /\ fst (fst (fst fdef)) = (fst (snd fspec)) )/\
             (forall i,
                (exists idef, intc i = Some idef) <-> (exists absi,ispec i=Some absi))                                        end
  end.

Definition emptaskenv  := fun (ts : taskst) =>
                         match ts with
                         | ((_,E,_),_,_) => E = emp
                        end.                       

Definition InitTaskSt lasrt t (s:reltaskst)  :Prop:= satp (fst s) (snd s) (CurTid t ** LINV lasrt t init_lg ** OS [empisr,true,nil,nil]) /\ emptaskenv (fst s) (*/\ fst (fst (fst (fst (fst s))))= InitG*).


Lemma tid_eq_dec: forall (t t':tid), {t=t'}+{t<>t'}.
Proof.
intros.
destruct t,t'.
assert ({b=b0} + {b<>b0}).
apply Pos.eq_dec.
destruct H.
subst.
assert ({i=i0} + {i<>i0}).
apply Int.eq_dec.
destruct H.
subst.
left.
auto.
right.
intro H.
apply n.
inversion H.
auto.
right.
intro H.
apply n.
inversion H;auto.
Qed.

Lemma beq_taskid: forall (x y : tid), {x = y} + {x <> y}.
Proof.
  apply tid_eq_dec.
Qed.

Module mmapspec.
  Definition domain:= tid.
  Definition image:= mem.
  Definition beq_Domain := beq_taskid.
End mmapspec.


Module TMSpecMod := Map.MapFun mmapspec.

Definition TMMap:= TMSpecMod.Map.


Module omapspec.
  Definition domain:= tid.
  Definition image:= osabst.
  Definition beq_Domain := beq_taskid.
End omapspec.


Module TOSpecMod := Map.MapFun omapspec.

Definition TOMap:= TOSpecMod.Map.

Inductive partM: mem -> tasks -> TMMap -> Prop :=
| partm_O:
    forall M Tm Tl,
      (forall t, Tm t = None) -> partM M Tl Tm
| partm_S:
    forall M M' Tm Tl Tl' t m,
      Tm t = Some m ->
      join m M' M ->
      partM M' Tl (TMSpecMod.remove Tm t ) ->
      partM M Tl' Tm.

Inductive partO: osabst -> tasks -> TOMap -> Prop:=
| parto_O:
    forall M Tm Tl,
      (forall t, Tm t = None) -> partO M Tl Tm
| parto_S:
    forall M M' Tm Tl Tl' t m,
      Tm t = Some m ->
      join m M' M ->
      partO M' Tl (TOSpecMod.remove Tm t ) ->
      partO M Tl' Tm.

(*
Definition partM (M:mem) (T:tasks) (Tm:TMMap):Prop:= 
  (forall (t:tid),
                        (exists (m:mem), TMSpecMod.maps_to Tm t m /\ sub m M))/\
  (forall t1 t2 m1 m2, 
     (t1<>t2)->TMSpecMod.maps_to Tm t1 m1 -> TMSpecMod.maps_to Tm t2 m2 -> (exists m3,join m1 m2 m3 /\ sub m3 M)).


Definition partO O (T:tasks) (To:TOMap):Prop:=
  (forall (t:tid),
                        (exists o, TOSpecMod.maps_to To t o /\ sub o O))/\
  (forall t1 t2 m1 m2, 
     (t1<>t2)->TOSpecMod.maps_to To t1 m1 -> TOSpecMod.maps_to To t2 m2 -> (exists m3,join m1 m2 m3 /\ sub m3 O)).*)
(*
Definition TMinit (T:tasks) lasrt tc: TMMap:=
  fun (t:tid) => if beq_tid t tc  then Some (CurTid t ** LINV lasrt t init_lg) else (LINV lasrt t init_lg).
*)

 
Fixpoint no_os (p:lprog) (ks:stmtcont):=
  match p with
    | (pc,(po,pi,ip)) =>
      match ks with
        | kstop => True
        | kseq s ks' => no_os p ks'
        | kcall f s e ks' => match (pumerge po pi) f with
                               | None => no_os p ks'
                               | Some x => False
                             end
        | kint c ke e ks' =>  False
        | kassignr e t ks' => no_os p ks'
        | kassignl v t ks' => no_os p ks'
        | kfuneval f vl tl el ks' => no_os p ks'
        | kif s1 s2 ks' => no_os p ks'
        | kwhile e s ks' => no_os p ks'
        | kret  ks' => no_os p ks'
        | kevent _ _ ks' => False
      end
  end.

Fixpoint goodks (p:lprog) (ks:stmtcont):= 
  match p with
    | (pc,(po,pi,ip)) =>
      match ks with
        | kstop => True
        | kseq s ks' => goodks p ks'
        | kcall f s e ks' => match (pumerge po pi) f with
                               | None => no_os p ks'
                               | Some x => goodks p ks'
                             end
        | kint c ke e ks' =>  goodks p ks'
        | kassignr e t ks' => goodks p ks'
        | kassignl v t ks' => goodks p ks'
        | kfuneval f vl tl el ks' => goodks p ks'
        | kif s1 s2 ks' => goodks p ks'
        | kwhile e s ks' => goodks p ks'
        | kret ks' => goodks p ks'
        | kevent _ _ ks' => False
      end
  end.




Definition TStWoMemEq (o o':taskst):= 
  match o, o' with 
      | ((a,b,c),d,e), ((a',b',c'),d',e') => a=a'/\b=b'/\d=d'/\e=e'
  end.



Definition good_t_ks p (T:tasks) := forall x c ke ks, get T x = Some (c,(ke,ks)) -> goodks p ks.


Definition is_nest (si:is) :=
  match si with
    | nil => false
    | _ => true
  end.


(*
Definition iretasrt' (i:hid) (isrreg:isr) (si:is)  (I:Inv) :asrt:= 
  (Aconj (Aop (spec_done None)) 
         (Astar (Aisr (isrupd isrreg i false))
                (Astar (Ais (cons i si))
                       (Astar (Acs  nil)
                                     (IRINV I ** A_dom_lenv nil))))).

Definition ipreasrt' (i:hid) (isrreg:isr) (si:is) (ispec:spec_code) (I:Inv):=
  (Aconj (Aop ispec)
        (Astar (Aisr (isrupd isrreg i true))
               (Astar (Ais (cons i si))
                      (Astar (Acs  nil) 
                             ((Astar (Aie false))  
                                       (isr_inv ** invlth_noisr I 0 i ** A_dom_lenv nil)))))). 

Definition BuildintPre (i:nat) i_spec (isrreg:isr) (si:is) (I:Inv):=
  match i_spec i with
    | None => None
    | Some ispec => Some (ipreasrt' i isrreg si (ispec ) I)
  end.

Definition BuildintRet (i:nat) (i_spec:osintspec) (isrreg:isr) (si:is) (I:Inv):=
  match i_spec i with
    | None => None
    | Some ispec => Some (iretasrt' i isrreg si I)
  end.
*)

Definition BuildPreA (p:progunit) (f:fid) (abs:osapi) (vl:vallist) G pa tid lg:option asrt:= 
    match p f with
      | Some (t, d1, d2, s) => 
        match dl_vl_match d1 (rev vl) with 
          | true =>
            match buildp (revlcons d1 d2) vl with
              | Some p =>Some (Aconj (Agenv G)
                                     (
                                        (Astar (Aop (fst abs (rev vl)) ** p_local pa tid lg ** p ** Aie true ** Ais nil ** Acs nil ** Aisr empisr)
                                               (A_dom_lenv (getlenvdom  (revlcons d1 d2)))) 
                                        )) 
              | _ => None
            end
          | false => None
        end
      | _ => None
    end.


Definition BuildRetA (p:progunit) (f:fid) (abs:osapi) (vl:vallist) G pa tid lg:option retasrt:= 
  match p f with
    | Some (t, d1, d2, s) => match buildq (revlcons d1 d2) with
                               | Some p =>
                                 Some
                                   (fun (v:option val) => 
                                      (Aconj (Agenv G)
                                              (Astar
                                                       ((Aop (spec_done v)) **p_local pa tid lg ** p** Aie true ** Ais nil ** Acs nil ** Aisr empisr)
                                                       (A_dom_lenv (getlenvdom  (revlcons d1 d2))))
                                                    ))
                                       |_ => None
                                     end
    | _ => None
  end.
(*
Definition BuildPreA':= 
  fun (p : progunit) (f : fid) (abs : osapi) (vl : vallist) =>
    match p f with
      | Some (_, d1, d2, _) =>
        match dl_vl_match d1 (rev vl) with
          | true =>
            match buildp (dladd d1 d2) vl with
              | Some p2 =>
                Some   
                  ( ((p2 ** Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
                                                                                      A_dom_lenv (getlenvdom (revlcons d1 d2))) //\\
                                                                                                                                <| (fst abs) (rev vl) |> )
                  
              | None => None
            end
          |false => None
    end
      | None => None
end.

Definition BuildRetA':= 
  fun (p : progunit) (f : fid) (_ : osapi) (_ : vallist) =>
    match p f with
      | Some (_, d1, d2, _) =>
        match buildq (dladd d1 d2) with
          | Some p2 =>
            Some
              (fun v : option val =>
                 ((p2 ** Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
                     A_dom_lenv (getlenvdom (revlcons d1 d2))) //\\ 
                                                               <| spec_done v |> )
            
          | None => None
        end
      | None => None
    end.
 *)

(*
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
*)
Fixpoint dl_add d1 d2:= 
  match d1 with
    | dnil => d2
    | dcons a b d1' => dcons a b (dl_add d1' d2)
  end.
 


Fixpoint length_eq (vl:vallist) dl:=
  match vl with
    | nil => match dl with
               |dnil => True
               |_ => False
             end
    | v::vl' => match dl with
                  | dcons a b dl' => length_eq vl' dl'
                  | _ => False
                end
  end.

Fixpoint good_clt_stmt (s:stmts) (p:progunit):=
  match s with 
    | sprim _ => False
    | sif e s1 s2 => good_clt_stmt s1 p/\ good_clt_stmt s2 p
    | sifthen e s => good_clt_stmt s p
    | swhile e s' => good_clt_stmt s' p
    | sseq s1 s2 => good_clt_stmt s1 p/\ good_clt_stmt s2 p
    | scall f el => p f = None
    | scalle e f el => p f = None
    | sfexec f vl tl =>  p f = None
    | hapi_code _  => False
    | _ => True
  end.

Definition good_clt_cureval (c:cureval) p:=
  match c with
    | curs s => good_clt_stmt s p
    | _ => True
  end.

Fixpoint good_clt_scont (ks:stmtcont) p:=
  match ks with
    | kstop => True 
    | kseq s ks' => good_clt_stmt s p/\ good_clt_scont ks' p
    | kcall f s le ks' => good_clt_stmt s p/\ good_clt_scont ks' p/\ p f = None
    | kint c ke le ks' => good_clt_scont ks' p
    | kassignr e t ks' => good_clt_scont ks' p
    | kassignl v t ks' => good_clt_scont ks' p
    | kfuneval f vl tl el ks' => good_clt_scont ks' p /\  p f = None
    | kif s1 s2 ks' => good_clt_stmt s1 p/\ good_clt_stmt s2 p/\ good_clt_scont ks' p
    | kwhile e s ks' => good_clt_stmt s p/\good_clt_scont ks' p
    | kret  ks' => good_clt_scont ks' p
    | kevent _ _ _ => False
  end.

Definition good_clt (C:code) p:=
  match C with 
    |(c,(ke,ks)) => good_clt_cureval c p/\ good_clt_scont ks p
  end.



Fixpoint good_is (si:is) := 
  match si with
    | nil => True
    | x::si' => x < INUM /\ good_is si'
  end.

Definition good_is_S (S:osstate):= 
  forall t tst, projS S t = Some tst -> 
  match tst with 
    | (a,b,c,d,(e,f,g)) => good_is f
  end.


Definition Bbj (B:osapispec) := forall f f' a b b', B f = Some (a,b) -> B f' = Some (a,b') -> f = f'.


Fixpoint good_dl_le (dl:decllist) (tst:taskst):=
  good_decllist dl=true/\
  match dl with 
    | dnil => True
    | dcons x t dl' => ~ indom (get_lenv (get_smem tst)) x /\ good_dl_le dl' tst
  end.


Definition n_dym_com_s (s:stmts):=
  match s with
    | sif e s1 s2 => GoodStmt' s1 /\ GoodStmt' s2
    | sifthen e s => GoodStmt' s
    | sseq s1 s2 => GoodStmt' s1 /\ GoodStmt' s2
    | swhile e s =>GoodStmt' s
    | hapi_code _ => False
    | _ => True
  end.   

Definition n_dym_com_ceval (c:cureval):=
  match c with
    | cure e => True
    | curs s => n_dym_com_s s
  end.

Fixpoint n_dym_com_int_scont (ks:stmtcont):=
  match ks with
    | kstop => True
    | kseq s ks' => GoodStmt' s/\ n_dym_com_int_scont ks'
    | kcall f s le ks' => GoodStmt' s /\ n_dym_com_int_scont ks'
    | kint _ _ _ _ => False
    | kassignr _ _ ks' => n_dym_com_int_scont ks'
    | kassignl _ _ ks' => n_dym_com_int_scont ks'
    | kfuneval _ _ _ _ ks' => n_dym_com_int_scont ks'
    | kif s1 s2 ks' => GoodStmt' s1 /\ GoodStmt' s2 /\ n_dym_com_int_scont ks'
    | kwhile e s ks' =>  GoodStmt' s /\ n_dym_com_int_scont ks'
    | kret ks' =>  n_dym_com_int_scont ks'
    | kevent _ _ _ => False
  end.
    
Definition n_dym_com_int_cd (C:code):=
  match C with
    | (c,(ke,ks)) => n_dym_com_ceval c/\ n_dym_com_int_scont ks
  end.



Fixpoint no_call_api_stmt (s:stmts) (p:progunit):=
  match s with 
    | sprim _ => True
    | sif e s1 s2 => no_call_api_stmt s1 p /\ no_call_api_stmt s2 p
    | sifthen e s => no_call_api_stmt s p
    | swhile e s' => no_call_api_stmt s' p
    | sseq s1 s2 => no_call_api_stmt s1 p /\ no_call_api_stmt s2 p
    | scall f el => p f = None
    | scalle e f el => p f = None
    | sfexec f vl tl => p f = None
    | hapi_code _ => False
    | _ => True
  end.

Definition no_call_api_cureval (c:cureval) p:=
  match c with
    | curs s => no_call_api_stmt s p
    | _ => True
  end.

Fixpoint no_call_api_scont (ks:stmtcont) p:=
  match ks with
    | kstop => True 
    | kseq s ks' => no_call_api_stmt s p/\ no_call_api_scont ks' p
    | kcall f s le ks' => no_call_api_stmt s p/\ no_call_api_scont ks' p/\ p f = None
    | kint c ke le ks' => no_call_api_cureval c p /\ no_call_api_scont ks' p
    | kassignr e t ks' => no_call_api_scont ks' p
    | kassignl v t ks' => no_call_api_scont ks' p
    | kfuneval f vl tl el ks' => no_call_api_scont ks' p /\  p f = None
    | kif s1 s2 ks' => no_call_api_stmt s1 p /\ no_call_api_stmt s2 p /\
                       no_call_api_scont ks' p
    | kwhile e s ks' => no_call_api_stmt s p/\no_call_api_scont ks' p
    | kret  ks' => no_call_api_scont ks' p
    | kevent _ _ _ => False
  end.

Definition no_call_api (C:code) p:=
  match C with 
    |(c,(ke,ks)) => no_call_api_cureval c p/\ no_call_api_scont ks p
  end.

Definition no_call_api_pu (p po:progunit):=
  forall (f:fid) t d1 d2 s, p f = Some (t,d1,d2,s) -> no_call_api_stmt s po. 

Definition no_call_api_ipu (p:intunit) (po:progunit):=
  forall (f:hid)  s, p f = Some s -> no_call_api_stmt s po. 

Definition no_call_api_os po pi ip:=
  no_call_api_pu po po /\ no_call_api_pu pi po /\ no_call_api_ipu ip po.
