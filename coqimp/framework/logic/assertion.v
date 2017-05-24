Require Import memory.
Require Import Lists.ListSet.
Require Import language.
Require Import opsem.
Require Import  NPeano.

Set Asymmetric Patterns.

Set Implicit Arguments.
Unset Strict Implicit.


Definition EventCtr:= (vallist * vallist).

Definition edom := list (var*type).

Definition absop:= spec_code.


Inductive asrt : Type := 
  Aemp
| Aconj (p1: asrt) (p2: asrt)
| Afalse 
| Atrue
| Adisj (p1: asrt) (p2: asrt)
| Astar (p1: asrt) (p2: asrt)
| Anot : asrt -> asrt
| Apure : Prop -> asrt    (*modal*)
| Aexists (ty:Type)  (P:ty->asrt)
| Amapsto : addr -> type -> bool -> val -> asrt
(*
| Amapstor: addr -> type -> val -> asrt
*)
(*
| Amapstolsval : addr -> type -> vallist ->asrt 
*)
| Alvarenv : var -> type -> addr -> asrt (*modal*)
| Agvarenv : var -> type -> addr ->  asrt  (*modal*)
| Agenv : env -> asrt
| A_eval_expr : expr -> type -> val -> asrt
| A_eval_list : exprlist ->  typelist -> vallist -> asrt
| A_dom_lenv : edom -> asrt  (*modal*)
| A_notin_lenv :  var -> asrt (*modal*)
| Alval : expr  -> type -> addrval  -> asrt
| Aistrue : expr -> asrt
| Aisfalse : expr -> asrt
| AHprio : ossched -> tid -> asrt 
| Aie :    ie ->  asrt (*modal*)
| Ais :  is -> asrt (*modal*)
| ATopis : hid -> asrt (*modal*)
| Aisr : isr  -> asrt (*modal*)
| Acs : cs ->  asrt (*modal*)
| Aabsdata : absdataid -> absdata -> asrt
| Aop : absop -> asrt.

Notation "'[|' P '|]'" := (Apure P) (at level 29, no associativity).
Infix "**" := Astar (at level 30, right associativity). 
Infix "//\\" := Aconj (at level 31, right associativity).
Infix "\\//" := Adisj (at level 31, right associativity).
Notation "'Rv' e '@' t '==' v" := (A_eval_expr e t v) (at level 20).
Notation "'Lv' e '@' t '==' a" := (Alval e t a) (at level 20).
Notation "'Rvl' el '@' tl '==' vl" :=  (A_eval_list el tl vl)(at level 20). 

Notation "  <|| op ||>  " :=  (Aop op) (at level 20).
Notation "l # t |=> v '@' b " := (Amapsto l t b v)  (at level 20).
Notation "l # t |-> v " := (l # t |=> v@true)  (at level 20).
Notation "l # t |-r-> v " := (l # t |=> v@false) (at level 20).

Definition Agvarenv' x t l := Agvarenv x t (addrval_to_addr l).
Definition Alvarenv' x t l := Alvarenv x t (addrval_to_addr l).

Notation "'G&' x '@' t '==' l " := (Agvarenv' x t l) (at level 20).
Notation "'L&' x '@' t '==' l " := (Alvarenv' x t l) (at level 20).
Notation "'EX' x , p " :=
  (Aexists (fun x => p))
    (at level 32, x ident, right associativity).
Notation "'EX' x : t , p " :=
  (Aexists (fun x : t => p))
    (at level 32, x ident, right associativity).
Notation "'EX' x .. y , p" :=
  (Aexists (fun x => .. (Aexists (fun y => p)) ..))
    (at level 32, x binder, right associativity).  
(*
Definition Aptrmapsto (l : addrval) (t : type) (v : val) : asrt :=
  (addrval_to_addr l) # t |-> v.
*)
Definition Aptrmapsto (l : addrval) (t : type) (p:bool) (v : val) : asrt :=
  (addrval_to_addr l) # t |=> v @ p.

Definition Agvarmapsto (x :var) (tp :type) p (v :val) : asrt :=
  EX b : block, G& x @ tp == (b,Int.zero) ** Aptrmapsto (b, Int.zero) tp p v.
 
Definition Alvarmapsto (x :var) (tp :type) p (v :val) : asrt :=
  EX b : block, L& x @ tp == (b,Int.zero) ** Aptrmapsto (b, Int.zero) tp p v.


Notation "'PV' l '@' t '|=>' v '@' b" := (Aptrmapsto l t b v)  (at level 20).
Notation "'GV' x '@' t '|=>' l '@' b" := (Agvarmapsto x t b l) (at level 20).
Notation "'LV' x '@' t '|=>' l '@' b" := (Alvarmapsto x t b l) (at level 20).

Notation "'PV' l '@' t '|->' v " := (PV l @ t |=> v @ true)  (at level 20).
Notation "'GV' x '@' t '|->' l " := (GV x @ t |=> l @ true) (at level 20).
Notation "'LV' x '@' t '|->' l " := (LV x @ t |=> l @ true) (at level 20).

(*
Definition Aptrmapstor (l : addrval) (t : type) (v : val) : asrt :=
  (addrval_to_addr l) # t |-r-> v.

Definition Agvarmapstor (x :var) (tp :type) (v :val) : asrt :=
  EX b : block, G& x @ tp == (b,Int.zero) ** Aptrmapstor (b, Int.zero) tp v.
 
Definition Alvarmapstor (x :var) (tp :type) (v :val) : asrt :=
  EX b : block, L& x @ tp == (b,Int.zero) ** Aptrmapstor (b, Int.zero) tp v.
*)

Notation "'PV' l '@' t '|-r->' v " := (PV l @ t |=> v @ false)  (at level 20). 
Notation "'GV' x '@' t '|-r->' l " := (GV x @ t |=> l @ false) (at level 20).
Notation "'LV' x '@' t '|-r->' l " := (LV x @ t |=> l @ false) (at level 20).

Definition retasrt := option val -> asrt.

Definition reltaskst := prod taskst osabst.

Definition RstateOP :=  prod reltaskst absop.

Notation empenv := emp.

Notation empmem := (emp:mem).

Definition emptaskst := fun (ts : taskst) =>
                         match ts with
                         | ((_,_,M),_,_) => M = empmem
                        end.
                         
(*
Definition empftaskst := fun (ts : taskst) =>
                         match ts with
                         | ((_,le,M),_,_) =>  le = empenv /\ 
                              forall (l : addr),
                                MemMod.get M l = Some v -> snd v = true
                        end.

*)
Notation empabst := (emp:osabst).                           
                        
Definition emposabst :=  fun (st:osabst) => st = empabst.
                        

Definition empst (s : RstateOP) :=  match s with
              | ((lo, ho), op) => emptaskst lo /\  emposabst ho 
              end.


(*
Definition empfst  (s : RstateOP) :=  match s with
              | ((lo, ho), op) => empftaskst lo /\  emposabst ho
              end.
*)
Definition getmem (s : RstateOP) : mem :=  
             match s with
              | ((lo, ho), op) =>   get_mem (get_smem lo)
             end.

Definition getlenv  (s : RstateOP) : env :=  
               match s with
              | ((lo, ho), op) =>  get_lenv (get_smem lo)
              end.

Definition getgenv  (s : RstateOP) : env :=  
               match s with
              | ((lo, ho), op) =>  get_genv (get_smem lo)
              end.

Definition getabst (s : RstateOP) : osabst := 
               match s with
              | ((lo, ho), op) =>  ho
              end.

Definition substabst (s : RstateOP) (o : osabst):  RstateOP :=
             match s with
              | ((lo, ho), op) =>   ((lo ,o),op)
              end.

Definition substaskst (st : taskst) (M : mem) : taskst := 
            match st with
             | ((G,E,M'),ir,aux) =>   ((G,E,M),ir,aux)
           end.

Definition  substaskstm (st:taskst) (M:mem):taskst:=
            match st with
              | ((G,E,M'),ir,aux) =>   ((G,E,M),ir,aux)
            end.

         
Definition substmem (s : RstateOP)  (M : mem):  RstateOP :=
             match s with
              | ((lo, ho), op) =>   ((substaskst lo M ,ho),op)
              end.

Definition substmo  (s : RstateOP) (M : mem) (o : osabst):  RstateOP :=
               match s with
              | ((lo, ho), op) =>   ((substaskst lo  M , o),op)
              end.    

Definition getsmem (s : RstateOP) : smem :=   match s with
              | ((lo, ho), op) =>    (get_smem lo)
              end.

Definition gettaskst (s : RstateOP) : taskst :=
  match s with
    | ((lo, ho), op) =>   lo
  end.

Definition getie (ts :taskst)  := 
  match ts with
    | (_,_,(ie,_,_)) => ie
  end.

Definition getis (ts :taskst)  := 
  match ts with
    | (_,_,(_,is,_)) => is
  end.

Definition getcs (ts :taskst)  := 
  match ts with
    | (_,_,(_,_,cs)) => cs
  end.

Definition getisr (ts :taskst)  := 
  match ts with
    | (_,isr,_) => isr
  end.

Definition getabsop (s : RstateOP) : absop :=  
  match s with
    | ((lo, ho), op) =>   op
  end.

Definition subabsop  (s : RstateOP) (op : absop) :  RstateOP :=
  match s with
    | (rs,_) => (rs ,op)
  end.


Definition SysmemJoinM (m:smem) (M1:mem) (m':smem):=
  exists G E M0 M', m  = (G, E, M0) /\ m' = (G,E,M') /\  join M0 M1 M'.


Definition joinmem (ts : taskst)(M : mem)(ts' : taskst) : Prop :=
  exists G E M1 M2 ir ls, ts = ((G, E, M1), ir, ls) /\
                          ts' =  ((G, E, M2), ir, ls) /\
                          join M1 M M2.

Definition rval (e : expr) (v : val) (m : smem) :=  evalval e m = Some v /\ v <> Vundef.

Definition lval (e :expr) (v : val) (m : smem) :=  evaladdr  e m = Some v /\ exists l, v = Vptr l.

Definition typecheck  (e :expr) (t : type ) (m : smem) :=  evaltype  e m = Some t.

Fixpoint  typechklist (el : exprlist) (tl : typelist) (vl : vallist) (m : smem){struct el} := 
  match el, tl, vl  with
    | nil,nil, nil => True
    | cons e el', cons t tl', cons v vl' =>  (rval e v) m /\ (typecheck e t)  m /\ (typechklist el' tl' vl') m 
    | _,_,_ => False
  end.

Fixpoint  evalexprlist (el : exprlist) (tl : typelist) (vl : vallist)  (m : smem) {struct el} :=
  match el, tl, vl  with
    | nil,nil, nil => True
    | cons e el', cons t tl', cons v vl' => 
      evalval e m = Some v /\ evaltype e m = Some t 
      /\ evalexprlist el' tl' vl' m /\ v <> Vundef 
    | _,_,_ => False
  end.


Definition ptomval (l : addr) (b:bool) (v : memval) (M : mem) := M = sig l (b,v).
(*
Definition ptomvalr (l : addr) (v : memval) (M : mem) := M = sig l (false,v).
*)

Fixpoint  ptomvallist (l : addr) (b1: bool) ( vl : mvallist)  (M: mem) {struct vl} : Prop :=
   match  vl, l with
   | nil, _  => M = emp
   | u :: vl', (b, i) =>
     exists M1 M2, join M1 M2 M /\ 
                   ptomval l b1 u M1 /\ ptomvallist (b, (Z.add i  1%Z)) b1 vl' M2
   end.


Definition mapstoval (l : addr) (t : type) (b: bool) (v : val)  (m : mem) := 
  exists vl, encode_val t v = vl /\ (ptomvallist l b vl m).


(*
Fixpoint  ptomvallistr (l : addr) ( vl : mvallist) (M: mem) {struct vl} : Prop :=
   match  vl, l with
   | nil, _  => M = emp
   | u :: vl', (b, i) =>
     exists M1 M2, join M1 M2 M /\ 
                   ptomvalr l u M1 /\ ptomvallistr (b, (Z.add i  1%Z)) vl' M2
   end.
*)

(*
Definition mapstovalr (l : addr) (t : type) (v : val) (m : mem) := 
  exists vl, encode_val t v = vl /\ (ptomvallistr l vl m).

Fixpoint arraymapstovallist (l : addr) (t : type) (vl : vallist) (m : mem){struct vl} :=
  match vl with
    | nil => m = emp
    | v :: vl' => exists m1 m2, 
                    join m1 m2 m /\
                    (mapstoval l t v m1) /\  
                    exists b i,
                      l = (b, i) /\ arraymapstovallist (b, (Z.add i (Z_of_nat (typelen t)))) t vl' m2 
  end.

Fixpoint structmapstovallist (l : addr)(dls : decllist)
         (vl : vallist) (m : mem){struct vl} :=
  match vl, dls with
    | nil,dnil => m = empmem
    | v :: vl', dcons id t dls' =>
      exists m1 m2, 
        join m1 m2 m /\
        (mapstoval l t v m1) /\
        exists b i,
          l =  (b, i) /\ structmapstovallist 
                           (b, (Z.add i (Z_of_nat (typelen t)))) dls' vl' m2 
    | _,  _ => False
  end.
*)


Definition gettopis (ii : is) : hid :=  match ii with
                                        | nil => INUM
                                        | i :: is' => i 
                                       end.

Definition eq_dom_env (E :env) (d : edom) : Prop := 
                      forall x t, set_In (x,t) d <-> exists l, get E x =Some (l,t).
             

Fixpoint sat (s : RstateOP)(p : asrt) {struct p}:= 
  match p with
    | Aemp => empst s
    | [| vp |] => vp /\ empst s
    | p //\\ q => sat s p /\ sat s q
    | p \\// q => sat s p \/ sat s q
    | Afalse => False
    | Atrue =>  True
    | Anot p =>  ~ sat s p
    | p ** q => exists  M1 M2 M o1 o2 o , 
                             M = getmem s /\  join M1 M2 M
                            /\ o = getabst s /\ join o1 o2 o
                           /\ sat (substmo s  M1 o1) p
                           /\ sat (substmo s  M2 o2) q 
    | A_eval_expr e t v => evalval e (getsmem s) = Some v /\ evaltype e (getsmem s) = Some t /\ v <> Vundef
                            
    | A_eval_list el tl vl => evalexprlist el tl vl (getsmem s) 

    | Alval e t l =>   evaladdr e (getsmem s) = Some (Vptr l) /\ 
                               evaltype e (getsmem s) = Some t 

    | Alvarenv x t l => exists b,
                        get (getlenv s) x =  Some (b,t) /\ l = (b,0%Z)/\ 
                                  getmem s = empmem /\ emposabst (getabst s)

    | Agvarenv x t l => exists b,
                          get (getgenv s) x =  Some (b,t)/\ l = (b,0%Z) /\
                                     getmem s = empmem /\ emposabst (getabst s)

    | Amapsto l  t b  v =>   (mapstoval l t b v) (getmem s) /\ emposabst (getabst s)
(*
    | l # t |-r-> v =>   (mapstovalr l t v) (getmem s) /\ emposabst (getabst s) 
*)
   (*
    | Amapstolsval l t vl => match t with
                             | Tarray t' n => n = length vl /\
                                   arraymapstovallist l t' vl  (getmem s)/\ emposabst (getabst s)
                             | Tstruct id dls => 
                                  structmapstovallist l dls vl (getmem s) /\ emposabst (getabst s)
                             | _ => False
                            end
    *)    
    | Agenv G => G = getgenv s

    | A_dom_lenv d =>   eq_dom_env (getlenv s) d /\ empst s
 
    | A_notin_lenv x =>    (~indom (getlenv s) x) /\ empst s
 
    | Aistrue e  =>   exists v, evalval e (getsmem s) = Some v /\
                               istrue v = Some true 
    | Aisfalse e  =>   exists v, evalval e (getsmem s) = Some v /\ 
                           istrue v = Some false 
    | Aexists t p' =>  exists (x : t), sat s (p' x)

    | AHprio sd tid =>    sd (getabst s) tid /\ emptaskst (gettaskst s)
             
    | Aie i =>    getie (gettaskst s) = i /\ empst s     
    
    | Ais i =>      getis (gettaskst s) = i /\ empst s
    
    | ATopis i =>  gettopis (getis (gettaskst s)) =  i /\ empst s
    
    | Aisr i =>      getisr (gettaskst s)  = i /\ empst  s     
    
    | Acs i =>   getcs (gettaskst s) = i  /\ empst s 
    
    | <|| op ||> =>  getabsop  s = op /\ empst  s     
    
    | Aabsdata id absdata => sig id absdata = getabst s /\ 
                                        emptaskst (gettaskst s) 

  end.

Notation "s '|=' P" := (sat s P) (at level 33, no associativity).
Notation "P ==> Q" := 
  (forall s, s |= P -> s |= Q)
    (at level 33, right associativity).
Notation "P <==> Q" := 
  (forall s, s |= P <-> s |= Q)
    (at level 33, right associativity).



(*
Definition Aop' a := Aop a //\\ Aemp.
Notation "  <|| op ||>  " :=  (Aop' op) (at level 20).
*)
(*
Notation "'done'" := (Aop (rendop None))(at level 20).
Notation "'done' v " := (Aop (rendop (Some v)))(at level 20).
Notation " r 'noret' " := (r None) (at level 20).
Notation " r 'ret' v " := (r (Some v))(at level 20).
*)
Notation ieon := (Aie true) (only parsing).
Notation ieoff := (Aie false) (only parsing).
Notation "'OS' [ isr , ie , is , cs ] " := ((Aisr isr) ** (Aie ie) ** (Ais is) ** (Acs cs))(at level 20).


Definition arfalse :=  fun (v : option val) => Afalse.

Fixpoint  GoodInvAsrt (p : asrt ) {struct p}: Prop :=
           match p with
           | Aemp => True
           | [| vp |] => True
           | p' //\\ q' =>  GoodInvAsrt  p' /\ GoodInvAsrt q'
           | p' \\// q' => GoodInvAsrt  p' /\ GoodInvAsrt  q'
           | p' ** q' => GoodInvAsrt  p' /\ GoodInvAsrt  q'
           | Afalse => True
           | Atrue =>  True
           | Amapsto l t b v => True
     (*   | l # t |-> v =>  True
           | l # t |-r-> v =>  True
      *)
         (*  | Amapstolsval l t vl => True*)
           | Aexists t p' => forall x, GoodInvAsrt (p' x)
           | Aabsdata id absdata  => True
           | Agvarenv x t l => True
           | Aisr _ => True
           | Ais _ => True
           | ATopis _ => True
           | _ => False
         end.

Fixpoint  GoodLocalInvAsrt (p : asrt ) {struct p}: Prop :=
           match p with
           | Aemp => True
           | [| vp |] => True
           | p' //\\ q' =>  GoodLocalInvAsrt  p' /\ GoodLocalInvAsrt q'
           | p' \\// q' => GoodLocalInvAsrt  p' /\ GoodLocalInvAsrt  q'
           | p' ** q' => GoodLocalInvAsrt  p' /\ GoodLocalInvAsrt  q'
           | Afalse => True
           | Atrue =>  True
           | Amapsto l t b v => True
     (*   | l # t |-> v =>  True
           | l # t |-r-> v =>  True
      *)
         (*  | Amapstolsval l t vl => True*)
           | Aexists t p' => forall x, GoodLocalInvAsrt (p' x)
           | Aabsdata id absdata  => True
           | Agvarenv x t l => True
           | _ => False
         end.



Fixpoint  AbsOsEmpAsrt (p : asrt ) {struct p}: Prop :=
           match p with
           | Aemp => True
           | [| vp |] => True
           | p' //\\ q' =>  AbsOsEmpAsrt  p' /\ AbsOsEmpAsrt q'
           | p' \\// q' => AbsOsEmpAsrt  p' /\ AbsOsEmpAsrt  q'
           | p' ** q' => AbsOsEmpAsrt  p' /\ AbsOsEmpAsrt  q'
           | Amapsto l t b v => True
(*           | l # t |-> v =>  True
           | l # t |-r-> v =>  True
 *)   
           | Aexists t p' => forall x, AbsOsEmpAsrt (p' x)
           | Agvarenv x t l => True
           | Alvarenv x t l => True
          (* | Amapstolsval l t vl => True*)
           | A_dom_lenv d => True
           | A_notin_lenv  x => True
           | _ => False
         end.


Fixpoint   Emp_AbsOs_Asrt (p : asrt ) {struct p}: Prop :=
           match p with
           | Aemp => True
           | [| vp |] => True
           | p' //\\ q' =>   Emp_AbsOs_Asrt  p' /\  Emp_AbsOs_Asrt q'
           | p' \\// q' =>  Emp_AbsOs_Asrt  p' /\  Emp_AbsOs_Asrt  q'
           | p' ** q' =>  Emp_AbsOs_Asrt  p' /\  Emp_AbsOs_Asrt  q'
           | Amapsto l t b v => True
(*
           | l # t |-> v =>  True
           | l # t |-r-> v =>  True
*)
           | Aexists t p' => forall x,  Emp_AbsOs_Asrt (p' x)
           | Agvarenv x t l => True
           | Alvarenv x t l => True
         (*  | Amapstolsval l t vl => True   *)   
           | Aie i =>   True                              
           | Ais i =>    True                              
           | ATopis i =>  True                                          
           | Aisr i => True                                                   
           | Acs i =>  True
           |  A_dom_lenv d => True
           |  A_notin_lenv x => True
           | _ => False
         end.

Definition get_isr_s (s:RstateOP):= match s with
                                    | ((_, _, _, isr, _),_,_) => isr
                                    end.

Definition get_is_s (s:RstateOP):= match s with
                                    | ((_, _, _, _, (_,si,_)),_,_) => si
                                   end.

Definition set_isr_s (s:RstateOP) (ir:isr) :=
  match s with
    | ((a,b,c,d,e),x,aop)=> ((a,b,c,ir,e),x,aop)
  end.

Definition set_is_s (s:RstateOP) (si:is):=
  match s with
    | ((a,b,c,d,(ie,is,cs)),x,aop)=> ((a,b,c,d,(ie,si,cs)),x,aop)
  end.

Definition set_isisr_s (s:RstateOP) (ir:isr) (si:is):=
  match s with
    | ((a,b,c,d,(ie,is,cs)),x,aop)=> ((a,b,c,ir,(ie,si,cs)),x,aop)
  end.

Definition inv_isr_prop p:= (forall s, s |= p ->
                                       forall i,(set_isr_s s (isrupd (get_isr_s s) i false)) |= p ) /\
                            (forall s, s|=p -> forall i, (set_isisr_s s (isrupd (get_isr_s s) i true) (i::(get_is_s s)))|=p) /\
                            (forall s i is, s|=p -> (get_isr_s s) i = false -> get_is_s s =i::is -> (set_is_s s is) |= p) /\
                            (forall s is ,s|=p -> (get_isr_s s = empisr) -> (set_is_s s is) |= p).

(* modified by zhanghui
Definition sub:= fun (m M:mem) => exists m', join m m' M.

Definition subabst:= fun (m M:osabst) => exists m', join m m' M.
 *)
Require Import Maps.

Definition precise (p : asrt) : Prop := forall s M1 M2  o1 o2 , 
     sat (substmo s M1 o1) p -> sat (substmo s M2 o2) p ->
     (forall M, sub M1 M -> sub M2 M -> M1 = M2) /\ 
     (forall o, sub o1 o ->  sub o2 o -> o1 = o2). 

Definition inv_prop p := precise p /\ inv_isr_prop p.

Record invasrt := mkinvasrt {getinv : asrt; invp : GoodInvAsrt getinv; prec : inv_prop getinv}.


Definition Inv:= hid -> invasrt.

Fixpoint starinv_isr (I : Inv) (low : hid) (n : hid){struct n} : asrt :=
  match n with
    | 0%nat =>
      EX r : isr,
             ([|r low = true|] //\\ Aisr r) \\//
             ([|r low = false|] //\\ Aisr r) ** getinv (I low)
    | S n' =>
      (EX r : isr,
              ([|r low = true|] //\\ Aisr r) \\//
              ([|r low = false|] //\\ Aisr r) ** getinv (I low)) **
              starinv_isr I (S low) n'
  end.

Definition II := fun (i : hid) => Aemp.

Fixpoint starinv_noisr (I : Inv) (low : hid) (n : hid){struct n} : asrt :=
  match n with
    | 0%nat => getinv (I low)
    | S n' => getinv (I low) ** starinv_noisr I (S low) n'
  end.

Open Local Scope nat_scope.

Definition invlth_noisr  (I : Inv) (low : hid) (high : hid) : asrt  
                   :=  starinv_noisr I low  (high - low).

Definition invlth_isr  (I : Inv) (low : hid) (high : hid) : asrt  := 
                 starinv_isr  I low  (high- low).

Definition isrclr : asrt :=  EX r : isr, Aisr r //\\ [|forall i : hid, r i = false|].

Definition isr_inv : asrt :=
  EX r : isr,
         Aisr r //\\
              (EX k : hid, ATopis k //\\ [|forall j : nat, 0 <= j < k -> r j = false|]).
 
(*Definition isr_inv : asrt :=
         Aisr empisr.
*)
Definition inv_ieon (I : Inv): asrt := Aie true ** invlth_isr I 0 INUM.

Definition inv_ieoff (I : Inv) : asrt :=
  Aie false ** (EX k : hid, ATopis k **  (([| k < INUM|] ** (invlth_isr I (k + 1) INUM))\\// [|k = INUM|])) .

Definition iret_ieon :  asrt := isr_inv //\\ (Aie true).

Definition iret_ieoff (I : Inv) : asrt :=
  (isr_inv //\\ Aie false) ** 
  (EX (ii : is) (k : nat), [|hd_error ii = Some k|] ** Ais ii ** invlth_isr I 0 k).

Definition INV (I : Inv) : asrt := 
  getinv (I (S INUM)) ** (inv_ieon I \\// inv_ieoff I).

Definition SWPRE (sd : ossched )(x: var) tc: asrt :=
  EX t: tid,  AHprio sd t ** isrclr ** (EX tp : type, GV x @ (Tptr tp) |-> (Vptr t)) ** (EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr tc)) ** Atrue.

Definition SWINV(I : Inv) : asrt :=
  (isrclr ** Aie false) ** (EX k : hid, ATopis k ** invlth_isr I 0 k).

Definition SWINVt I t := SWINV I  ** (EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t). 


Definition RDYINV(I : Inv) t: asrt :=
  ((Aie true //\\ isrclr) ** (EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t)) \\// SWINVt I t.



Definition IRINV (I : Inv) : asrt :=
  iret_ieon \\// iret_ieoff I.

Definition InitTaskAsrt : asrt :=
  (Aie true //\\ Ais nil) //\\ Acs nil.

Fixpoint GoodFrame (p : asrt){struct p}: Prop :=
           match p with
           | Aemp => True
           | [| vp |] => True
           | p' //\\ q' =>  GoodFrame  p' /\ GoodFrame q'
           | p' \\// q' => GoodFrame  p' /\ GoodFrame  q'
           | p' ** q' => GoodFrame p' /\ GoodFrame q'
           | l # t |-> v =>  True
           | l # t |-r-> v =>  True
           (*| Amapstolsval l t vl => True*)
           | Aexists t p' => forall x, GoodFrame (p' x)
           | _ => False
         end.


Fixpoint GoodFunAsrt (p : asrt) : Prop :=
         match p with
           | Aemp => True
           | [| P |] => True
           | Afalse  => True
           | Atrue  => True
           | l # t |-> v => True
           | l # t |-r-> v =>  True
          (* | Amapstolsval l t vl => True*)
           | Agvarenv x t l => True
           | AHprio sd t => True
           | Aie ie => True
           | Ais is =>  True
           | ATopis id => True
           | Aisr isr => True
           | Acs cs => True
           | Aabsdata id data => True
           | Aconj p' q' =>  GoodFunAsrt  p' /\ GoodFunAsrt q'
           | Adisj p' q' => GoodFunAsrt  p' /\ GoodFunAsrt  q'
           | Astar p' q' => GoodFunAsrt  p' /\ GoodFunAsrt  q'
           | Aexists t p' => forall x, GoodFunAsrt (p' x)
           | Aop _ => True 
           | _ => False
         end.

Fixpoint can_change_aop (p:asrt) :=
  match p with 
    | Astar p1 p2 => (can_change_aop p1) /\ (can_change_aop p2)
    | p1 //\\ p2 =>  (can_change_aop p1)  /\ (can_change_aop p2)
    | p1 \\// p2 =>  (can_change_aop p1) /\ (can_change_aop p2)
    | Aop aop => False
    | Anot p' => False
    | Aexists t p' => forall x : t, can_change_aop (p' x)
    | _ => True
  end.


Inductive EventData :=
 | DMsgQ : val -> vallist->vallist->vallist-> EventData
 | DSem : int32 -> EventData
 | DMbox: msg -> EventData
 | DMutex: val -> val  -> EventData.

Inductive logicvar:=
| logic_isr: isr -> logicvar
| logic_is: is -> logicvar
| logic_ie: ie -> logicvar
| logic_cs: cs -> logicvar
| logic_hid: hid -> logicvar
| logic_val: val -> logicvar
| logic_lv: vallist -> logicvar
| logic_llv: list vallist -> logicvar
| logic_leventd: list EventData -> logicvar
| logic_leventc:list EventCtr -> logicvar
| logic_abstcb: TcbMod.map -> logicvar
| logic_absecb: EcbMod.map -> logicvar
| logic_code : spec_code -> logicvar.



Record  funasrt: Type := mkfunasrt{getasrt : asrt ; getprop : GoodFunAsrt getasrt}.

Definition fpre :=  vallist -> list logicvar -> tid ->  funasrt.

Definition fpost :=  vallist -> option val -> list logicvar -> tid ->  funasrt.

Definition  fspec := (fpre * fpost * funtype )%type.

Definition funspec := fid -> option fspec.

Notation "'PRE' [ p , vl , logicl , ct ]" := (getasrt (p vl logicl ct))(at level 20). 
Notation "'POST' [ p , vl , v , logicl , ct ] " := (getasrt (p vl v logicl ct))(at level 20, vl at next level). 


(***Some basic assertions***)
Open Scope int_scope.

(* assertion of array *)

Definition isptr v := v = Vnull \/ exists p, v = Vptr p.


Fixpoint Aarray' (l:addrval) n t vl :=
  match vl, n with
    | nil,0 => Aemp
    | v :: vl', S n' => 
      let (b,i) := l in
      PV l @ t |-> v ** Aarray' (b, (Int.add i (Int.repr (Z_of_nat (typelen t))))) n' t vl'
    | _,  _ => Afalse
  end.

Definition Aarray l t vl :=
  match t with
    | Tarray t' n => Aarray' l n t' vl 
    | _ => Afalse
  end.

Definition LAarray x t vl :=
  EX l,  L& x @ t == l ** Aarray l t vl.

Definition GAarray x t vl :=
  EX l,  G& x @ t == l ** Aarray l t vl.


Definition id_addrval (l:addrval) (id:var) (t:type) :=
  match t with
  | Tstruct s dcls => match field_offset id dcls with
                      | Some off => let (b,i):=l in
                                      Some (b, Int.add i off)
                      | None => None
                      end
  | _ => None
  end.  

Fixpoint Aarray_rm (l:addrval) (n:nat) (t:type) (vl:list val) (m:nat) {struct vl}:=
  match l with 
    | (b,i) =>
      match vl with
        | nil => Aemp
        | cons v vl' => match n with
                          | 0 => Afalse 
                          | S n' => 
                            match m with
                              | 0 => Aarray' (b, Int.add i (Int.repr (BinInt.Z.of_nat (typelen t)))) n' t vl'
                              | S m' => PV l @ t |-> v ** Aarray_rm (b, Int.add i (Int.repr (BinInt.Z.of_nat (typelen t)))) n' t vl' m'
                            end
                        end
      end
  end.

Fixpoint array_type_vallist_match (t:type) (vl:vallist) {struct vl}:=
  match vl with
  | nil => True
  | v::vl' => rule_type_val_match t v = true /\  array_type_vallist_match t vl'
  end.

(* assertion of struct *)

Fixpoint Astruct' (l : addrval) dls vl {struct dls}:=
  match vl, dls with
    | nil,dnil => Aemp
    | v :: vl', dcons id t dls' => 
        match t with 
        | Tarray t' n => let (b,i):=l in Astruct' (b, (Int.add i (Int.repr (Z_of_nat (typelen t))))) dls' vl'
        | Tstruct _ _ => let (b,i):=l in Astruct' (b, (Int.add i (Int.repr (Z_of_nat (typelen t))))) dls' vl' 
        | _ => let (b,i):=l in
               PV l @ t |-> v ** Astruct' (b, (Int.add i (Int.repr (Z_of_nat (typelen t))))) dls' vl'
        end
    | _,  _ => Afalse
  end.

Definition Astruct l t vl :=
  match t with
    | Tstruct id dls => Astruct' l dls vl 
    | _ => Afalse
  end.

(*
Fixpoint Auxlist (l : addrval) dls vl {struct dls}:=
  match vl, dls with
    | nil,dnil => Aemp
    | v :: vl', dcons id t dls' => 
        match t with 
        | Tarray t' n => let (b,i):=l in Auxlist (b, (Int.add i (Int.repr (Z_of_nat (typelen t))))) dls' vl'
        | Tstruct _ _ => let (b,i):=l in Auxlist (b, (Int.add i (Int.repr (Z_of_nat (typelen t))))) dls' vl' 
        | _ => let (b,i):=l in
               PV l @ t |-r-> v ** Auxlist (b, (Int.add i (Int.repr (Z_of_nat (typelen t))))) dls' vl'
        end
    | _,  _ => Afalse
  end.
*)

Fixpoint Astruct_rm (l:addrval) (dls:decllist) (vl:list val) (id:ident) {struct vl}:=
  match l with 
    | (b,i) =>
      match vl with
        | nil => Aemp
        | cons v vl' => match dls with
                      | dnil => Afalse
                      | dcons id' t dls' => 
                        if Zbool.Zeq_bool id id' 
                        then 
                          Astruct' (b,Int.add i (Int.repr (BinInt.Z.of_nat (typelen t)))) dls' vl' 
                        else 
                          match t with 
                            | Tarray t' n => Astruct_rm (b, Int.add i (Int.repr (BinInt.Z.of_nat (typelen t)))) dls' vl' id
                            | Tstruct _ _ => Astruct_rm (b, Int.add i (Int.repr (BinInt.Z.of_nat (typelen t)))) dls' vl' id 
                            | _ =>  PV l @ t |-> v ** (Astruct_rm (b, Int.add i (Int.repr (BinInt.Z.of_nat (typelen t)))) dls' vl' id)
                          end
                    end
      end
  end.

Fixpoint struct_type_vallist_match' dls vl {struct vl}:=
  match vl, dls with
    | nil,dnil => True
    | v :: vl', dcons id t dls' => 
        match t with 
        | Tarray t' n => struct_type_vallist_match' dls' vl'
        | Tstruct id ds  => struct_type_vallist_match' dls' vl'
        | _ => rule_type_val_match t v =true/\ struct_type_vallist_match' dls' vl'
        end
    | _,  _ => False
  end.

Definition struct_type_vallist_match t vl :=
  match t with
    | Tstruct id dls => struct_type_vallist_match' dls vl 
    | _ => False
  end.

(* nth val of vallist *)

Fixpoint nth_val (n : nat) (vl : vallist) {struct vl}:=
  match vl with
    | nil => None
    | v::vl' => match n with
                  | 0 => Some v
                  | S n' => nth_val n' vl'
                end
  end.

Fixpoint nth_id (n : nat) (decl : decllist){struct decl} :=
  match decl with
    | dnil => None
    | dcons id t decl' => match n with
                  | 0 => Some id
                  | S n' => nth_id n' decl'
                end
  end.

Fixpoint nth_vallist (n : nat) (ll:list vallist) {struct ll} :=
  match ll with
    | nil => None
    | l::ll' => match n with
                  | 0 => Some l
                  | S n' => nth_vallist n' ll'
                end
  end.

Fixpoint update_nth_val (n : nat) (vl : vallist) (v : val){struct vl} :=
  match vl with
    | nil => nil
    | v'::vl' => match n with
                  | 0 => v::vl'
                  | S n' => v'::(update_nth_val n' vl' v)
                end
  end.


Fixpoint id_nth' id decl n:=
  match decl with
    | dnil => None
    | dcons id' t decl'=> match Zbool.Zeq_bool id id' with
                            | true => Some n
                            | false => id_nth' id decl' (S n)
                          end
  end. 

Definition id_nth id decl := id_nth' id decl 0.

Definition update_nth_val_op n vl v:= 
  match NPeano.Nat.ltb n (length vl) with
    | false => None
    | true => Some (update_nth_val n vl v)
  end.

Fixpoint remove_nth_val (n : nat) (vl : vallist){struct vl} :=
  match vl with
    | nil => nil
    | v'::vl' => match n with
                  | 0 => vl'
                  | S n' => v'::(remove_nth_val n' vl')
                end
  end.

Definition remove_nth_val_op n vl :=
  match NPeano.Nat.ltb n (length vl) with
    | false => None
    | true => Some (remove_nth_val n vl)
  end.

Fixpoint remove_nth_vallist (n : nat) (vl : list vallist) {struct vl} :=
  match vl with
    | nil => nil
    | v'::vl' => match n with
                  | 0 => vl'
                  | S n' => v'::(remove_nth_vallist n' vl')
                end
  end.

Definition remove_nth_vallist_op n vl:=
  match NPeano.Nat.ltb n (length vl) with
    | false => None
    | true => Some (remove_nth_vallist n vl)
  end.


Definition node (v:val) (vl:vallist) (t:type) :=
  EX b, [| v= Vptr (b,Int.zero) /\ struct_type_vallist_match t vl |]
          ** Astruct (b,Int.zero) t vl.

(*
Definition node_aux (v:val) (vl:vallist) (t:type) vl' dls :=
  EX b, [| v= Vptr (b,Int.zero) /\ struct_type_vallist_match t vl |]
          ** Astruct (b,Int.zero) t vl
          ** Auxlist (b, Int.repr (Z.of_nat (typelen t))) dls vl'.
          *)

Fixpoint sllseg (head tailnext : val)  (l:list vallist) (t:type) (next: vallist -> option val):=
  match l with
    | nil => [| head = tailnext |]
    | vl::l' => [| head <> Vnull |] ** EX vn, [|next vl = Some vn|] **
                node head vl t ** sllseg vn tailnext l' t next
  end.

Definition sll head l t next := sllseg head Vnull l t next.

(* double linked list definition *)

Fixpoint dllseg (head headprev tail tailnext : val) (l:list vallist) 
         (t:type) (pre next: vallist -> option val):=
  match l with
    | nil => [| head = tailnext |] ** [| headprev = tail |]
    | vl::l' => [| head <> Vnull |] ** EX vn,
                [|next vl = Some vn|] ** [|pre vl = Some headprev|] **
                node head vl t ** dllseg vn head tail tailnext l' t pre next
  end.

(*
Fixpoint dllseg_aux (head headprev tail tailnext : val) (l laux:list vallist)
         (t:type) dls (pre next: vallist -> option val):=
  match l,laux with
    | nil,nil => [| head = tailnext |] ** [| headprev = tail |]
    | vl::l',vl'::laux' => [| head <> Vnull |] ** EX vn,
                [|next vl = Some vn|] ** [|pre vl = Some headprev|] **
                                      node_aux head vl t vl' dls ** dllseg_aux vn head tail tailnext l' laux' t dls pre next
    | _,_ => Afalse
  end.
*)

Definition dll head tail l t pre n:= dllseg head Vnull tail Vnull l t pre n.


Fixpoint nth_val' n vl :=
  match vl with
  | nil => Vundef
  | (v :: vl')%list =>
    match n with
    | 0 => v
    | S n' => nth_val' n' vl'
    end
  end.

Close Scope int_scope.
