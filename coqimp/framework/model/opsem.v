Require Import memory.
Require Import language.
Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.


Definition OSTCBHighRdy:= 59%Z.
Definition OSTCBCur:=60%Z.

Definition gets_g (s:osstate):= (fst (fst (fst (fst s)))).
Definition gets_m (s:osstate) := (snd (fst (fst s))).
Definition get_env (m:smem):= (snd (fst m)).

Definition Dteq (D1 D2:clientst)(t:tid):Prop:=
  match D1 with 
    | ( _ ,evs1, _) => match D2 with
                         | ( _, evs2, _) =>
                           forall (t':tid), ~(t'=t) ->  get evs1 t' = get evs2 t'
                       end
  end. 

Definition Piteq (pi1 pi2: ltaskstset) (t:tid):Prop:=
  forall (t':tid), ~(t'=t) -> get pi1 t'= get pi2 t'.

Definition Steq (S1 S2 :osstate) (t:tid):Prop:=
  match S1 with
    | (D1, ir,  pi1)  => match S2 with 
                           | ( D2 , ir',  pi2) => Dteq D1 D2 t /\ Piteq pi1 pi2 t
                         end
  end.

Definition Dnewt (D:clientst) (t:tid):clientst:=
  match D with 
    | ( ge, cvs,  M) => ( ge, ( set cvs t emp), M)
  end.

Definition Tlnewt (tl:ltaskstset) (t:tid) :ltaskstset:=
  set tl t (true, nil, nil).

Definition Snewt (S:osstate) (t:tid):osstate:=
  match S with
    | (D, ir, tl) =>  ((Dnewt D t),   ir,  (Tlnewt tl t))
  end.


Definition projD (D:clientst) (t:tid) := 
  match D with (x,y,z) => 
               match  get y t with
                 | Some e => Some (x, e , z)
                 | _ => None
               end
  end.

Definition projS (S:osstate) (t:tid) :=
  match S with ( x, y, z)  =>
               match (projD x t),(get z t) with
                 | Some m,Some n => Some (m , y  , n)
                 | _,_ => None
               end
  end.


Definition vtoZ (v:val):option Z:=
  match v with
    | Vint32 a => Some (Int.unsigned a)
    |_=>None
  end.


(* modified by zhanghui*)
Open Local Scope Z_scope.
Definition type_val_match (t:type) (v:val) :=
  match t,v with
    | Tnull, Vnull => true
    | Tptr t, Vnull => true
    | Tcom_ptr id,Vnull => true
    | Tint8,Vint32 v => (*if v is in the range of Tint8 return True, if not return False*)
      match (Int.unsigned v) <=? Byte.max_unsigned with
        | true => true
        | false => false
      end
    | Tint16,Vint32 v => (*if v is in the range of Tint16 return True, if not return False*)
      match (Int.unsigned v) <=? Int16.max_unsigned with
        | true => true
        | false => false
      end
    | Tint32,Vint32 v =>true
    | Tptr t,Vptr l => true
    | Tcom_ptr id,Vptr l => true
    | Tarray _ _, _ => true
    | Tstruct _ _, _ =>true
    | _,_=> false
  end.

Fixpoint tl_vl_match (tl:typelist) (vl:vallist) :=
  match tl with 
    | nil => 
      match vl with 
        | nil => true
        | _ => false
      end
    | t :: tl' => 
      match vl with
        | v :: vl' => if type_val_match t v then tl_vl_match tl' vl' else false
        | _ => false
      end
  end.  

Fixpoint field_offsetfld (id:var) (fld:decllist) (pos:int32):option int32:=
  match fld with 
    |dnil => None
    |dcons id' t fld'=>if Zeq_bool id id' then Some pos else field_offsetfld id fld' (Int.add (Int.repr (Z_of_nat (typelen t))) pos)
  end.

Definition field_offset (id:var) (fld:decllist) : option int32:= field_offsetfld id fld (Int.zero).

Definition istrue (v:val) : option bool :=
  match v with 
    | Vptr a => Some true
    | Vnull => Some false
    | Vint32 a =>  if (Int.eq a Int.zero) then Some false else Some true
    | _ => None
  end.

Fixpoint revlcons (d1 d2 :decllist): decllist :=
  match d1 with 
    | dnil => d2 
    | dcons x y d1' => revlcons d1' (dcons x y d2)
  end.

Fixpoint callcont (ks:stmtcont): option stmtcont:=
  match ks with
    | kstop => None
    | kint x y e ks'=> None
    | kcall  f  y z ks'=> Some (kcall f  y z ks')
    | kseq x  ks' => callcont ks'
    | kassignl x y ks' => callcont ks'
    | kassignr x y ks' => callcont ks'
    (*
| kcalle x y z ks' => callcont ks'
     *)
    | kfuneval  x y z w ks' => callcont ks'
    | kif x y ks' => callcont ks'
    | kwhile x y ks' => callcont ks'
    | kret  ks' => callcont ks'
    | kevent _ _ ks' => callcont ks'
  end .

Fixpoint intcont (ks:stmtcont): option stmtcont:=
  match ks with
    | kstop => None
    | kint x y e ks'=> Some (kint x y e ks')
    | kcall f  y z ks'=> None
    | kseq x  ks' => intcont ks'
    | kassignl x y ks' => intcont ks'
    | kassignr x y ks' => intcont ks'
    (*
| kcalle x y z ks' => intcont ks'
     *)
    | kfuneval   x y z w ks' => intcont ks'
    | kif x y ks' => intcont ks'
    | kwhile x y ks' => intcont ks'
    | kret  ks' => intcont ks'
    | kevent _ _ ks' => intcont ks'
  end .


Fixpoint AddStmtToKs (s:stmts) (ks:stmtcont):stmtcont:=
  match ks with
    | kstop => kseq s kstop
    | kseq s' ks' => kseq s' (AddStmtToKs s ks')
    | kcall f x E ks' => kcall f x  E (AddStmtToKs s ks')
    | kint c ke e ks' => kint c ke e (AddStmtToKs s ks')
    | kassignl e t ks' => kassignl e t (AddStmtToKs s ks')
    | kassignr v t ks' => kassignr v t (AddStmtToKs s ks')
    (*
    | kcalle f el t ks' => kcalle  f el t (AddStmtToKs s ks')
     *)
    | kfuneval  f vl tl el ks' => kfuneval  f vl tl el (AddStmtToKs s ks')
    | kif s' s'' ks' => kif s' s'' (AddStmtToKs s ks')
    | kwhile e s' ks' => kwhile e s' (AddStmtToKs s ks')
    | kret ks' => kret (AddStmtToKs s ks')

    | kevent a b  ks' => kevent a b (AddStmtToKs s ks')
  end.


Fixpoint AddKsToTail (ks1 ks2:stmtcont):stmtcont:=
  match ks2 with
    | kstop => ks1
    | kseq s' ks' => kseq s' (AddKsToTail ks1 ks')
    | kcall f x E ks' => kcall f x E (AddKsToTail ks1 ks')
    | kint c ke e ks' => kint c ke e (AddKsToTail ks1 ks')
    | kassignl e t ks' => kassignl e t (AddKsToTail ks1 ks')
    | kassignr v t ks' => kassignr v t (AddKsToTail ks1 ks')
    (*
    | kcalle f el t ks' => kcalle  f el t (AddKsToTail ks1 ks')
     *)
    | kfuneval  f vl tl el ks' => kfuneval  f vl tl el (AddKsToTail ks1 ks')
    | kif s' s'' ks' => kif s' s'' (AddKsToTail ks1 ks')
    | kwhile e s' ks' => kwhile e s' (AddKsToTail ks1 ks')
    | kret  ks' => kret  (AddKsToTail ks1 ks')
    | kevent a b  ks' => kevent a b (AddKsToTail ks1 ks')
  end.


Notation " ks2 '##' ks1 " := (AddKsToTail ks1 ks2)(at level 25, left associativity).

Fixpoint len_exprcont (ke : exprcont) : nat :=
  match ke with
    | kenil => O
    | keop1 _ _ ke' => S (len_exprcont ke')
    | keop2r _ _ _ _ ke' => S (len_exprcont ke')
    | keop2l _ _ _ _ ke' => S (len_exprcont ke')
    | kederef _ ke' => S (len_exprcont ke')
    | keoffset _ ke' => S (len_exprcont ke')
    | kearrbase _ _ ke' => S (len_exprcont ke')
    | kearrindex _ _ ke' => S (len_exprcont ke')
    | kecast _ _ ke' => S (len_exprcont ke')
  end.

Fixpoint len_stmtcont (ks : stmtcont) : nat :=
  match ks with
    | kstop => O
    | kseq _ ks' => S (len_stmtcont ks')
    | kcall  _ _ _ ks' => S (len_stmtcont ks')
    | kint _ _ _ ks' => S (len_stmtcont ks')
    | kassignl _ _ ks' => S (len_stmtcont ks')
    | kassignr _ _ ks' => S (len_stmtcont ks')
    (*
  | kcalle _ _ _ ks' => S (len_stmtcont ks')
     *)
    | kfuneval  _ _ _ _ ks' => S (len_stmtcont ks')
    | kif _ _ ks' => S (len_stmtcont ks')
    | kwhile _ _ ks' => S (len_stmtcont ks')
    | kret ks' => S (len_stmtcont ks')

                    
    | kevent a b ks' => S (len_stmtcont ks')
  end.


Definition nilcont (s:stmts): code := ((curs s), (kenil, kstop)).

(*
Definition uop_eval (v:val) (op1:uop):= Some (Vint32 Int.zero).

Definition uop_type (t:type) (op1:uop):= Some t.

Definition bop_eval (v v':val) (op2:bop):= Some (Vint32 Int.zero).

Definition bop_type (t1 t3:type) (op2 :bop):= Some Tint8.
 *)

Definition is_int_type t:=
  match t with
    | Tint8 => true
    | Tint16 => true
    | Tint32 => true
    | _ => false
  end.

Fixpoint evaltype (e:expr) (m:smem){struct e}:option type:=
  match m with 
      (genv, lenv, my) =>
      match e with
        | enull => Some Tnull
        | econst32 n => Some Tint32
        | evar x => match get lenv x with 
                      | Some (pair a t) =>  Some t 
                      | None => match get genv x with 
                                  | Some (pair a t) => Some t 
                                  | None => None
                                end
                    end
        | eunop uop e1 => match evaltype e1 m with
                            | Some t => uop_type t uop 
                            | None => None
                          end
        | ebinop bop e1 e2 => match evaltype e1 m, evaltype e2 m  with
                                | Some t1, Some t2 => bop_type t1 t2 bop
                                | _, _ => None
                              end   
        | ederef e' => match evaltype e' m with
                         | Some (Tptr t) => Some t
                         (*if type is Tcom_ptr ??*)
                         | _ => None
                       end
        | eaddrof e' => match e' with
                          | evar x  =>  match evaltype e' m  with
                                          | Some t =>  Some (Tptr t)
                                          | None => None
                                        end
                          | ederef e'' =>  match evaltype e'' m with
                                             | Some (Tptr t) => Some (Tptr t)
                                             | _=> None
                                           end
                          | efield e'' id  =>  match evaltype e' m  with
                                                 | Some t =>  Some (Tptr t)
                                                 | None => None
                                               end
                          | earrayelem e1 e2 =>  match evaltype e' m  with
                                                   | Some t =>  Some (Tptr t)
                                                   | None => None
                                                 end
                          | _ => None
                        end
        | efield e' id => match evaltype e' m with
                            | Some (Tstruct id' dl) => ftype id dl
                            | _=> None
                          end
        | ecast e' t => match evaltype e' m, t with 
                          | Some (Tptr t'), Tptr t'' => Some t
                          | Some Tnull, Tptr t' => Some t
                          | Some (Tcom_ptr t'), Tptr t'' => Some t  
                          | Some Tint8 , Tint8 => Some t
                          | Some Tint8 , Tint16 => Some t
                          | Some Tint8 , Tint32 => Some t
                          | Some Tint16 , Tint8 => Some t
                          | Some Tint16 , Tint16 => Some t
                          | Some Tint16 , Tint32 => Some t
                          | Some Tint32 , Tint8 => Some t
                          | Some Tint32 , Tint16 => Some t
                          | Some Tint32 , Tint32 => Some t
                          | _,_ => None
                        end

        | earrayelem e1 e2 => match evaltype e1 m, evaltype e2 m with
                                |Some (Tarray t n), Some Tint8 => Some t
                                |Some (Tarray t n), Some Tint16 => Some t
                                |Some (Tarray t n), Some Tint32 => Some t
                                |Some (Tptr t), Some Tint8 => Some t
                                |Some (Tptr t), Some Tint16 => Some t
                                |Some (Tptr t), Some Tint32 => Some t
                                | _ , _=>None
                              end
      end
  end.

Inductive assign_type_match : type -> type -> Prop:=
| eq_tnull: forall t1, (exists t, t1 = (Tptr t)) \/ (exists t,t1=(Tcom_ptr t)) \/ (t1=Tnull) -> assign_type_match t1 Tnull 
| eq_tvoid: assign_type_match Tvoid Tvoid
| eq_vptr: forall t1 t2, (exists t t', t1= (Tptr t) /\ t2 = (Tptr t'))->
                         assign_type_match t1 t2
| eq_vcomptr: forall t1 t2, ((exists t, t1= (Tptr t)) \/ (exists t, t1= (Tcom_ptr t))) /\ ((exists id,t2 = (Tcom_ptr id))\/(exists t,t2 = Tptr t)) ->
                            assign_type_match t1 t2
| eq_array: forall t1 t2, (exists t n, t1= (Tarray t n) /\ t2 = (Tarray t n))->
                          assign_type_match t1 t2
| array_to_vptr:  forall t1 t2, (exists t n, t1= (Tptr t) /\ t2 = (Tarray t n))->
                                assign_type_match t1 t2
| eq_struct: forall t1 t2,  (exists id dl, t1= (Tstruct id dl) /\ t2 = (Tstruct id dl))->
                            assign_type_match t1 t2
| eq_int: forall t1 t2, ((t1=Tint8\/t1=Tint16\/t1=Tint32)/\(t2=Tint8\/t2=Tint16\/t2=Tint32))->
                        assign_type_match t1 t2.



Fixpoint typematch (el:exprlist) (dl:decllist) (m:smem) :Prop:=
  match el,dl with
    | nil,dnil => True
    | cons e el',dcons x t dl' => (exists t',evaltype e m = Some t' /\ assign_type_match t t')/\ typematch el' dl' m
    | _,_=> False
  end.

Definition getoff (b:block) (i:offset) (id:ident) (e:expr) (m:smem):option addrval:=
  match evaltype e m with
    | Some (Tstruct id' dl) => match field_offset id dl with
                                 | Some off => Some ( b, ( Int.add (Int.repr i) off))
                                 | _ => None
                               end
    | _ => None
  end.


Definition get_genv (m : smem) :=
  match m with
    | (ge, le , M) => ge
  end.


Definition get_lenv (m : smem) :=
  match m with
    | (ge, le , M) => le
  end.


Definition get_mem (m : smem) :=
  match m with
    | (ge, le , M) => M
  end.

Definition addrval_to_addr (a:addrval):=
  match a with
    | (b,i) => (b,Int.unsigned i)
  end.
Definition addr_to_addrval (a:addr):=
  match a with
    | (b,i) => (b,Int.repr i)
  end.

Definition load (t : type) (m : mem) (l : addr) : option val :=
  match t with 
    | Tarray _ _ => Some (Vptr (addr_to_addrval l))
    | _ => loadm t m l 
  end.

Definition cast_eval i t t':=
  match t,t' with
    | Tint8,Tint8 => Some i
    | Tint8,Tint16 => Some i
    | Tint8,Tint32 => Some i
    | Tint16,Tint16 => Some i
    | Tint16,Tint32 => Some i
    | Tint32,Tint32 => Some i
                            
    | Tint32,Tint8 => Some (Int.modu i (Int.repr Byte.modulus))
    | Tint32,Tint16 => Some  (Int.modu i (Int.repr Int16.modulus))
    | Tint16,Tint8 => Some (Int.modu i (Int.repr Byte.modulus))
    | _,_ => None
  end.


Lemma cast_eval_tptr_none:
  forall x t,cast_eval x (Tptr t) (Tptr t) = None.
Proof.
  intros.
  simpl.
  auto.
Qed.

Fixpoint evalval (e:expr) (m:smem) :option val:= 
  match evaltype e m with
    | Some t =>  
      match e with 
        | enull => Some Vnull
        | econst32 n => Some (Vint32 n)
        | evar x => match get (get_lenv m) x with
                      | Some (pair a t) => load t (get_mem m) (a,0%Z)
                      | None =>
                        match get (get_genv  m) x with
                          | Some (pair a t) => load t (get_mem m) (a,0%Z)
                          | None => None
                        end
                    end
        | eunop op1 e' =>  match evalval e' m with
                             | Some v=> uop_eval v op1
                             | _ => None
                           end
                             
        | ebinop op2 e1 e2 =>  match evalval e1 m, evalval e2 m with
                                 | Some v1,Some v2 => match evaltype e1 m, evaltype e2 m with
                                                        | Some t1, Some t2 => bop_eval v1 v2 t1 t2 op2
                                                        | _,_ => None
                                                      end 
                                 | _,_ => None
                               end
        | eaddrof e' =>  match e' with
                           | evar x =>  evaladdr e' m 
                           | ederef e'' => evalval e'' m
                           | efield e'' id => evaladdr e' m 
                           | earrayelem e1 e2 => evaladdr e' m 
                           | _ => None
                         end
        | ederef e' => match evalval e' m with
                         | Some (Vptr ad) =>  load t (get_mem  m) (addrval_to_addr ad) 
                         | _ => None
                       end
        | efield e' id => match (evaladdr e' m) with
                            | (Some (Vptr ( b,  i))) => match getoff b (Int.unsigned i) id e' m with
                                                          | Some ad => load t (get_mem m) (addrval_to_addr ad)
                                                          | _ => None
                                                        end
                            | _ => None
                          end
        | ecast e' t' =>
          match evaltype e' m with
            | Some te =>
              match is_int_type te,is_int_type t' with
                | true, true =>
                  match evalval e' m with
                    | Some (Vint32 x) => match (cast_eval x te t') with
                                           | Some x' => Some (Vint32 x')
                                           | None => None
                                         end
                    | _ => None
                  end
                | _ , _ => evalval e' m
              end
            | _ => None
          end
        | earrayelem e1 e2 => match (evalval e1 m),(evalval e2 m) with
                                |Some (Vptr ( b,  i)), Some v =>
                                 match v with
                                   | Vint32 z => load t (get_mem m) ( b, Int.unsigned (Int.add i
                                                                                               (Int.mul (Int.repr (Z_of_nat (typelen t))) z )))
                                   |_ => None
                                 end
                                |_,_=>None
                              end
                                
      end
    | _ => None
  end
with evaladdr (e:expr) (m:smem) :option val:=
       match e with
         | evar x => match get (get_lenv m) x with
                       |Some (pair a t) => Some (Vptr (a,Int.zero))
                       |_ => match get (get_genv m) x with
                               |Some (pair a t) => Some (Vptr (a,Int.zero))
                               |_ => None
                             end
                     end
         | ederef e' => evalval e' m
         | efield e' id => match evaladdr e' m with
                             | (Some (Vptr ( b, i))) => match getoff b (Int.unsigned i) id e' m with
                                                          |Some ad => Some (Vptr  ad)
                                                          |_=> None
                                                        end
                             | _ => None
                           end
         | earrayelem e1 e2 => match (evaltype e1 m), (evalval e1 m),(evalval e2 m) with
                                 |Some (Tarray t n), Some (Vptr (b, i)), Some v =>
                                  match v with
                                    | Vint32 z => Some (Vptr (b, (Int.add i (Int.mul (Int.repr (Z_of_nat (typelen t))) z))))
                                    |_=>None
                                  end
                                 |Some (Tptr t), Some (Vptr (b, i)), Some v =>
                                  match v with
                                    | Vint32 z => Some (Vptr (b, (Int.add i (Int.mul (Int.repr (Z_of_nat (typelen t))) z))))
                                    |_=>None
                                  end
                                 |_, _ ,_=>None
                               end
         |_=> None
       end.


Fixpoint getaddrlist (l:list (prod var (prod block type))):list (prod block type):=
  match l with
    | nil => nil
    | cons (pair x (pair ad t)) l'=> cons (pair ad t) (getaddrlist l')  
  end.

Definition getaddr (le:env):list (prod block type):=
  match le with
    | EnvMod.listset_con a _=> getaddrlist a
  end.

Fixpoint tlmatch (tl:typelist) (dl:decllist) :Prop:=
  match tl with
    | nil => match dl with
               | dnil => True
               | _ => False
             end
    | cons t tl' => match dl with
                      | dcons  _ t' dl'=> tlmatch tl' dl'/\ t'=t
                      | _ => False
                    end
  end.

(*
CoInductive infnat :=
| infcons : infnat -> infnat.

Fixpoint inadd (infn:infnat) (n: nat) :infnat:=
  match n with
    | O => infn
    | S n' => inadd (infcons infn) n'
  end.
 *)
Inductive estep: cureval -> exprcont -> smem -> cureval -> exprcont -> smem -> Prop :=
| enull_step : forall m ke,
                 estep (cure enull) ke m [Vnull] ke m
| ec32_step: forall (i:int32) (m:smem) (ke:exprcont), 
               estep (cure (econst32 i)) ke m [Vint32 i] ke m
| evar_step : forall (x:var) (v:val) (m:smem) (ke:exprcont),
                evalval (evar x) m =Some v ->  estep (cure (evar x)) ke m [v] ke m
| eaddr_step: forall (x:var) (v:val) (m:smem) (ke:exprcont),
                evalval (eaddrof (evar x)) m = Some v ->  
                estep (cure (eaddrof (evar x))) ke m [v] ke m
| ederef_step: forall (e:expr) (t:type) (m:smem) (ke:exprcont),
                 evaltype e m = Some (Tptr t) -> 
                 estep (cure (ederef e)) ke m (cure e) (kederef t ke) m
| eaddrderef_step: forall e m ke,
                     estep (cure (eaddrof (ederef e))) ke m (cure e) ke m
| esidaddr_step: forall (e:expr) (id id':ident) i (dl:decllist) (ke:exprcont) (m:smem),
                   evaltype e m = Some (Tstruct id' dl) ->
                   field_offset id dl = Some i -> 
                   estep (cure (eaddrof (efield e id))) ke m (cure (eaddrof e))
                         (keoffset i ke) m
| eaptrelemaddr_step:  forall (e1 e2:expr) (t:type)  (ke:exprcont) (m:smem),
                         evaltype e1 m = Some (Tptr t) ->  
                         estep (cure (eaddrof (earrayelem e1 e2))) ke m  
                               (cure e1) (kearrbase e2 t ke) m
| eaelemaddr_step:  forall (e1 e2:expr) (t:type) (n:nat)  (ke:exprcont) (m:smem),
                      evaltype e1 m = Some (Tarray t n) ->  
                      estep (cure (eaddrof (earrayelem e1 e2))) ke m  
                            (cure  e1) (kearrbase e2 t ke) m
| esid_step : forall (e:expr) (id id':ident) (t:type) (dl:decllist)
                     (ke:exprcont) (m:smem),
                evaltype e m = Some (Tstruct id' dl) -> ftype id dl = Some t -> 
                estep (cure (efield e id)) ke m (cure (eaddrof (efield e id)))
                      (kederef t ke) m
| eaelem_step :  forall (e1 e2:expr) (t:type) (n:nat)  (ke:exprcont) (m:smem),
                   evaltype e1 m = Some (Tarray t n) ->  
                   estep (cure (earrayelem e1 e2)) ke m (cure (eaddrof (earrayelem e1 e2)))
                         (kederef t ke) m
| eaptrelem_step :  forall (e1 e2:expr) (t:type)  (ke:exprcont) (m:smem),
                      evaltype e1 m = Some (Tptr t) ->  
                      estep (cure (earrayelem e1 e2)) ke m (cure (eaddrof (earrayelem e1 e2)))
                            (kederef t ke) m
| euopstep:  forall (e:expr) (t:type) (op1:uop) (ke:exprcont) (m:smem),
               evaltype e m = Some t ->  
               estep (cure (eunop op1 e)) ke m (cure e) (keop1 op1 t ke) m
| ebop_step:  forall (e1 e2:expr) (t1 t2:type) (op2:bop) (ke:exprcont) (m:smem),
                evaltype e1 m = Some t1 -> evaltype e2 m =Some t2 ->  
                estep (cure (ebinop op2 e1 e2)) ke m (cure e1) (keop2r op2 e2 t1 t2 ke) m
| ecast_step: forall (e:expr) (t t' t'': type) (m:smem) (ke:exprcont),
                t=Tptr t' -> evaltype e m = Some (Tptr t'') ->  
                estep (cure (ecast e t)) ke m (cure e) ke m
| ecastnull_step: forall (e:expr) (t t' : type) (m:smem) (ke:exprcont),
                    t=Tptr t' -> evaltype e m = Some Tnull ->  
                    estep (cure (ecast e t)) ke m (cure e) ke m
| ecastcomptr_step: forall (e:expr) (t t' : type) (m:smem) (ke:exprcont) x,
                      t = Tptr t' -> evaltype e m = Some (Tcom_ptr x) ->  
                      estep (cure (ecast e t)) ke m (cure e) ke m
| ecastint_step: forall (e:expr) (t t' : type) (m:smem) (ke:exprcont),
                   evaltype e m = Some t' -> is_int_type t = true -> is_int_type t' = true ->  
                   estep (cure (ecast e t)) ke m (cure e) (kecast t' t ke) m
| evcastint_step: forall v v' ke t t' m,
                    cast_eval v t t' = Some v' ->
                    estep [Vint32 v] (kecast t t' ke) m [Vint32 v'] ke m
| evderef_step : forall (genv lenv:env) (M:mem) (a:addrval) (v:val) (t:type) 
                        (m:smem) (ke:exprcont),
                   m= (genv, lenv, M) -> load t M (addrval_to_addr a) =Some v -> 
                   estep [Vptr a] (kederef t ke) m  [v] ke m
| evoff_step : forall (b:block) (i i':int32) (ke:exprcont) (m:smem),
                 estep [Vptr (b, i)] (keoffset i' ke) m 
                       [Vptr (b, (Int.add i i'))] ke m
| evaddrelem_step : forall (v:val) (e:expr) (t:type) (ke:exprcont) (m:smem),
                      estep [v] (kearrbase e t ke) m (cure e) (kearrindex v t ke) m
| evaddrv_step: forall (v:val) (b:block) (i i' i'':int32)
                       (t:type) (ke:exprcont) (m:smem),
                  v = Vint32 i'' -> i'= Int.repr (Z_of_nat (typelen t)) ->
                  estep  [v] (kearrindex (Vptr (b, i)) t ke) m
                         [Vptr ( b, (Int.add i (Int.mul i' i'')))] ke m
| evuop_step : forall (op1:uop) (v v':val) (ke:exprcont) (m:smem) (t:type),
                 uop_eval v op1 = Some v' -> 
                 estep [v] (keop1 op1 t ke) m [v'] ke m
| evbop1_step : forall (op2:bop) (e:expr) (v:val) (t1 t2:type) (ke:exprcont) (m:smem),
                  estep [v] (keop2r op2 e t1 t2 ke) m
                        (cure e) (keop2l op2 v t1 t2 ke) m
| evbop2_step : forall (op2:bop) (v v' v'':val) (t1 t2 :type) (ke:exprcont) (m:smem),
                  bop_eval v' v t1 t2 op2=Some v'' -> 
                  estep [v] (keop2l op2 v' t1 t2 ke) m  [v'']  ke m.


Inductive estepstar :  cureval -> exprcont -> smem -> cureval -> exprcont -> smem -> Prop:=
| e_step0 : forall c ke m, estepstar c ke m c ke m
| e_stepn : forall c ke m c' ke' m' c'' ke'' m'', estep c ke m c' ke' m'-> 
                                                  estepstar c' ke' m' c'' ke'' m'' -> 
                                                  estepstar c ke m c'' ke'' m''.

Definition getfunrettype (fn : function) := match fn with
                                              | (t, _ ,_,_) => t
                                            end.


Inductive sstep: progunit -> cureval -> stmtcont -> smem -> cureval -> stmtcont -> smem -> Prop :=
(*Assign Steps*)
| sassign_step: forall (e1 e2:expr) (t1 t2:type) (ks:stmtcont) (m:smem) (p:progunit),
                  evaltype e1 m =Some t1 -> 
                  evaltype e2 m=Some t2 -> 
                  assign_type_match t1 t2 ->
                  sstep p (curs (sassign e1 e2)) ks m (cure e2) (kassignr e1 t1 ks) m

| sassignrv_step : forall (m:smem) (p:progunit) (v:val) (e:expr) (t:type) (ks:stmtcont),
                     sstep p [v] (kassignr e t ks) m 
                           (cure (eaddrof e))(kassignl v t ks) m

| sassignend_step : forall (m m':smem) (ge le :env) (M M':mem) (a:addrval) (v:val) 
                           (p:progunit) (ks:stmtcont) (t:type),
                      m= (ge, le, M) -> 
                      m'= ( ge, le, M') ->
                      store t M (addrval_to_addr a) v =Some M' ->
                      sstep p [Vptr a] (kassignl v t ks) m (curs (sskip None)) ks m' 

(*Function call Steps*)
| scalle_step: forall (p:progunit) (e:expr) (t:type) (m:smem) 
                      (f:fid) (ks:stmtcont) (el:exprlist),
                 evaltype e m =Some t ->
                 sstep p (curs (scalle e f el)) ks m (curs (scall f el))(kassignr e t ks) m

| spcall_step : forall (p:progunit) (t:type) (e:expr) (el:exprlist)
                       (m:smem) (ks:stmtcont) (f:fid), 
                  evaltype e m =Some t ->
                  sstep p (curs (scall f (cons e el))) ks m 
                        (cure e) (kfuneval f nil (t::nil) el ks) m

| snpcall_step : forall (m:smem)(f:fid) (p:progunit) (ks: stmtcont),
                   sstep p (curs (scall f nil)) ks m (curs (sfexec f nil nil)) ks m

| svfeval_step: forall (p:progunit) (v:val) (e:expr) (vl:vallist)
                       (el:exprlist) (ks:stmtcont) (m:smem) (f:fid) (tl:typelist) (t:type),
                  evaltype e m = Some t -> 
                  sstep p  [v] (kfuneval f vl tl (cons e el) ks) m 
                        (cure e) (kfuneval f (cons v vl) (t::tl) el ks) m
| svfevalnil_step: forall (p:progunit) (v:val) (vl:vallist) 
                          (ks:stmtcont) (m:smem) (f:fid) tl,
                     sstep p [v] (kfuneval f vl tl nil ks) m 
                           (curs (sfexec f (cons v vl ) tl)) ks m

| sfexec_step : forall (m m' :smem) (ge le:env) (M:mem) (p:progunit)
                       (t:type)(d1 d2:decllist)
                       (s:stmts) (ks:stmtcont) (vl:vallist) (f:fid) tl,
                  m=(ge, le, M) -> 
                  m'=  (ge, emp, M) -> 
                  p f=Some (t, d1, d2, s)->  
                  tlmatch (List.rev tl) d1  -> 
                  tl_vl_match tl vl = true ->
                  sstep p (curs (sfexec f vl tl)) ks m 
                        (curs (salloc vl (revlcons d1 d2))) 
                        (kcall f  s le ks) m'

| sallocp_step : forall (m m':smem) (ge le le':env) (M M' M'':mem)
                        (b:block) (v:val) (p:progunit) 
                        (vl:vallist) (dl:decllist) (ks:stmtcont) (x:var) (t:type),
                   m= (ge, le, M) -> 
                   m' = ( ge, le', M'') ->
                   alloc x t le M le' M' -> 
                   get le' x = Some (b,t)-> 
                   store t M'  (b, 0%Z) v = Some M''->
                   sstep p (curs (salloc  (cons v vl) (dcons x t dl))) ks m 
                         (curs (salloc  vl dl)) ks m'

| salloclv_step : forall (m m':smem) (ge le le':env) (M M':mem)
                         (t:type) (x:var) (p:progunit)
                         (dl:decllist) (ks:stmtcont),
                    m =  (ge, le, M) -> 
                    m' = (ge,le', M') ->
                    alloc x t le M le' M' ->
                    sstep p (curs (salloc  nil (dcons x t dl))) ks m
                          (curs (salloc  nil dl)) ks m'

| sallocend_step: forall (p:progunit) (f :fid) 
                         (s:stmts) (ks:stmtcont) (m:smem) (E:env),
                    sstep p (curs (salloc  nil dnil)) (kcall f s E ks) m 
                          (curs s) (kcall f s  E ks) m

| sret_step: forall (p:progunit) (m:smem)(M:mem) (ge le le':env)(f :fid)
                    (ks ks':stmtcont)  (al:freelist) (s: stmts),
               m=(ge, le, M) -> 
               callcont ks =Some (kcall f s le' ks') ->
               getaddr le = al ->
               sstep p (curs sret) ks m (curs (sfree al None)) ks m


| srete_step : forall (p:progunit) (ks:stmtcont)  
                      (e:expr) (m:smem),
                 sstep p (curs (srete e)) ks m (cure e) (kret ks) m

| sretv_step: forall (p:progunit) (m:smem) (le ge:env)
                     (M:mem) (ks:stmtcont) (f:fid)  
                     (al:freelist) (v:val)(s : stmts) ,
                m=(ge, le, M) ->
                callcont ks <> None -> 
                getaddr le = al->
                sstep p [v] (kret ks) m (curs (sfree al (Some v))) ks m 

| sfree_step : forall (m m':smem) (le ge :env) (M M':mem) (b:block) (t:type) (p:progunit) 
                      (al:freelist) (ks:stmtcont) (v:option val),
                 m=(ge, le, M) -> 
                 m' = (ge, le , M') -> 
                 free t b M =Some M' -> 
                 sstep p (curs (sfree (cons (pair b t) al) v)) ks m 
                       (curs (sfree al v)) ks m'

| sfreeend_step : forall (p:progunit) (ks ks':stmtcont) (m m':smem)
                         (ge le le':env) (M:mem) (s : stmts)(f:fid) (v:option val),
                    m= (ge, le, M) -> 
                    m' = (ge, le', M) -> 
                    callcont ks =Some (kcall f  s le' ks') ->
                    sstep p (curs (sfree nil v)) ks m (curs (sskip v)) ks' m'
(*

| sfreev_step : forall (m m':smem) (le ge :env) (M M':mem) (b:block) (t:type) (p:progunit) 
                     (al:freelist) (ks:stmtcont) (v:val),
                m=(ge, le, M) -> 
                m'= ( ge, le, M') -> 
                free t b M =Some M' -> 
                sstep p (curs (sfreev (cons (pair (b, 0%Z) t) al) v)) ks m 
                                  (curs (sfreev al v)) ks m'

 
| sfreevend_step : forall (p:progunit) (ks ks':stmtcont) (f:fid) (t: type)
                  (m m':smem) (v:val)(M:mem) (ge le le':env)(s : stmts),
                   m=( ge, le, M) -> 
                   m'= ( ge, le', M) -> 
                   t <> Tvoid -> 
                   callcont ks =Some (kcall f t s le' ks') ->
                   sstep p (curs (sfreev nil v)) ks m (curv v) ks' m'
 *)

(*Sequential Step*)                   
| sseq_step : forall (s1 s2:stmts) (ks:stmtcont) (m:smem) (p:progunit),
                sstep p (curs (sseq s1 s2)) ks m (curs s1) (kseq s2 ks) m

| svseq_step : forall (p:progunit) (v:val) (s:stmts) (ks:stmtcont) (m:smem),
                 sstep p [v] (kseq s ks) m (curs s) ks m

| sskip_step : forall (s:stmts) (ks:stmtcont) (m:smem) (p:progunit),
                 sstep p SKIP (kseq s ks) m (curs s) ks m


(*If then else Step*)
| sif_step : forall (e:expr) (s1 s2 :stmts) (ks:stmtcont) (m:smem) (p:progunit),
               sstep p (curs (sif e s1 s2)) ks m (cure e) (kif s1 s2 ks) m

| sifthen_step: forall  (e:expr) (s :stmts) (ks:stmtcont) (m:smem) (p:progunit),
                  sstep p (curs (sifthen e s)) ks m (cure e) (kif s (sskip None) ks) m

| svift_step: forall (p:progunit) (v:val) (s1 s2:stmts) (ks:stmtcont) (m:smem),
                istrue v = Some true ->
                sstep p (curs (sskip (Some v))) (kif s1 s2 ks) m (curs s1) ks m
| sviff_step: forall (p:progunit) (v:val) (s1 s2:stmts) (ks:stmtcont) (m:smem),
                istrue v = Some false ->
                sstep p (curs (sskip (Some v))) (kif s1 s2 ks) m (curs s2) ks m

(*While Step*)

| swhile_step : forall (e:expr) (s:stmts) (ks:stmtcont) (m:smem) (p:progunit),
                  sstep p (curs (swhile e s)) ks m (cure e) (kwhile e s ks) m


| svwhilet_step: forall (p:progunit) (v:val) (s:stmts) (e:expr) (ks:stmtcont) (m:smem),
                   istrue v=Some true ->
                   sstep p  (curs (sskip (Some v))) (kwhile e s ks) m (curs s) (kseq (swhile e s) ks) m

| svwhilef_step: forall (p:progunit) (v:val) (s:stmts) (e:expr) (ks:stmtcont) (m:smem),
                   istrue v=Some false ->
                   sstep p (curs (sskip (Some v))) (kwhile e s ks) m SKIP ks m.



Inductive sstepev : progunit -> cureval -> stmtcont -> smem -> cureval -> stmtcont -> smem -> val -> Prop:=
|sprint_step: forall (e:expr) (v:val) (m:smem) (ks:stmtcont) (s:stmts) (p:progunit),
                evalval e m = Some v -> sstepev p (curs (sprint e)) ks m SKIP ks m v.


Inductive cstep: progunit -> code -> smem -> code -> smem -> Prop :=
| expr_step : forall (p:progunit) (C:code) (m m':smem) (c c':cureval)
                     (ke ke':exprcont) (ks:stmtcont),
                C = ( c, ( ke, ks)) -> 
                estep c ke m c' ke' m' ->
                cstep p C m (c', ( ke', ks)) m'
| stmt_step : forall (p:progunit) (C:code) (m m':smem) (c c':cureval)
                     (ks ks':stmtcont),
                C = (c, (kenil, ks)) -> 
                sstep p c ks m c' ks' m' ->
                cstep p C m (c', (kenil , ks')) m'.

Inductive cstepev : progunit-> code -> smem -> code -> smem -> val-> Prop :=
| stmt_stepev :  forall (expr_step p p:progunit) (C:code) (m:smem) (c c':cureval)
                        (ks ks':stmtcont) (v:val),
                   C = (c, (kenil, ks)) -> 
                   sstepev p c ks m c' ks' m v ->
                   cstepev p C m (c', (kenil, ks')) m v. 

Inductive cstepstar: progunit -> code -> smem -> code -> smem -> Prop :=
| c_stepstar0: forall (p:progunit) (C:code) (m:smem),
                 cstepstar p C m C m
| c_stepstarn: forall (p:progunit) (C C' C'':code) (m m' m'':smem),
                 cstep p C m C' m' -> cstepstar p C' m' C'' m''->
                 cstepstar p C m C'' m''.

Definition cstepabt (p:progunit) (C:code) (m:smem) := 
  ~ (exists C' m' ev, cstep p C m C' m' \/ cstepev p C m C' m' ev).


Definition pumerge (p1 p2:progunit):=
  fun (f:fid) => match p1 f with 
                   | Some fc => Some fc 
                   | None => match p2 f with 
                               | Some fc => Some fc
                               | None => None
                             end
                 end.

Open Local Scope Z_scope.
Definition is_length (si:is):=
  match (length si) with
    | 1%nat => Vint32 Int.one
    | _ => Vint32 Int.zero
  end.

Inductive loststep: progunit -> code -> taskst -> code -> taskst -> Prop:=
| ostc_step: forall (C C':code) (m m':smem) (i:isr) (au:localst) (p:progunit),
               cstep p C m C' m'
               -> loststep p C (m , i, au) C' ( m', i, au)

| exint_step: forall (C:code) (ks ks':stmtcont) (c:cureval) (ke:exprcont)  
                     (ir:isr) (ei:ie) (si:is) (ci:cs) (i:hid) (p:progunit) ge le m le',
                C =(curs (sprim exint), (kenil, ks)) -> 
                intcont ks = Some (kint c ke le' ks') ->
                loststep p C ((ge,le,m), ir,  ( ei, (cons i si), ci)) 
                         (c, ( ke, ks')) ((ge,le',m),ir, (true, si, ci))

| eoi_step:  forall (C:code) (ks:stmtcont) (m:smem)  (au:localst)
                    (ir:isr) ( id: hid)  (p:progunit) (i:int32),
               C =((curs (sprim (eoi i))), (kenil, ks)) ->
               id = (Z.to_nat (Int.unsigned i))  -> 0 <= Int.unsigned i < Z_of_nat INUM->
               loststep p C (m, ir, au) 
                        (SKIP, (kenil, ks)) 
                        (m , (isrupd ir id false) , au)

| cli_step : forall (C:code) (ks:stmtcont) (m:smem)
                    (ir:isr) (ei:ie) (si:is) (ci:cs) (p:progunit),
               C = ((curs (sprim cli)), (kenil, ks)) -> 
               loststep p C (m, ir, (ei, si, ci)) 
                        (SKIP, (kenil, ks)) 
                        (m, ir , (false, si, ci))

| sti_step : forall (C:code) (ks:stmtcont) (m:smem)
                    (ir:isr) (ei:ie) (si:is) (ci:cs) (p:progunit),
               C =((curs (sprim sti)), (kenil, ks)) -> 
               loststep p C (m, ir, (ei, si, ci)) 
                        (SKIP, (kenil, ks)) 
                        (m, ir, (true, si, ci))

| encrit_step : forall (C:code) (ks:stmtcont) (m:smem)
                       (ir:isr) (ei:ie) (si:is) (ci:cs)  (p:progunit),
                  C =((curs (sprim encrit)), (kenil, ks)) -> 
                  loststep p C (m , ir,  (ei,  si, ci)) 
                           (SKIP, (kenil, ks)) 
                           (m,  ir , (false, si, (cons ei ci)))

| excrit_step : forall (C:code) (ks:stmtcont) (m:smem)
                       (ir:isr) (ei ei':ie) (si:is) (ci:cs)(p:progunit),
                  C =((curs (sprim excrit)), (kenil, ks)) -> 
                  loststep p C ( m ,ir, (ei,  si, (cons ei' ci))) 
                           (SKIP, (kenil,  ks)) 
                           ( m,ir, (ei',  si, ci))
| checkis_step : forall  (C:code) (ks:stmtcont) (m:smem)
                         (ir:isr) (ei ei':ie) (si:is) (ci:cs) (x:var) (p:progunit) G E M M' m' b x,
                   C =((curs (sprim (checkis x))), (kenil, ks)) ->
                   m=(G,E,M) ->
                   get E x = Some (b,Tint32) ->
                   store Tint32 M (b,0%Z) (is_length si) = Some M'->
                   m'= (G,E,M') ->
                   loststep p C ( m ,ir, (ei,  si, ci)) 
                            (SKIP, (kenil,  ks)) 
                            ( m',ir, (ei,  si, ci)).

Open Local Scope nat_scope.


Inductive lintstep : intunit -> code -> taskst -> code -> taskst ->Prop:=
| li_step : forall (C:code) (c:cureval) (ke:exprcont) (ks:stmtcont) (ir:isr) (si:is) (i i':hid) (s:stmts)
                   (theta:intunit) ge le m,
              C=(c, (ke, ks)) -> 
              higherint ir i -> i<INUM -> theta i =Some s ->
              lintstep theta C ((ge,le,m) , ir, (true, si, nil)) 
                       ((curs s), (kenil, (kint c ke le ks))) 
                       ((ge,emp,m),(isrupd ir i true) , (false, (cons i si), nil)).


Definition InOS (C:code) (p:progunit) : Prop :=
  exists (c:cureval) (ke:exprcont) (ks:stmtcont), 
    C= (c, (ke, ks)) /\ (
      (exists (f:fid) (vl:vallist) (fc:function) tl,  
         c = curs (sfexec f vl tl) /\ p f =Some fc) \/
      (exists (f:fid) (le:env) (ks':stmtcont) (t:type) (d1 d2:decllist) (s:stmts) s',
         callcont ks = Some (kcall f s le ks')/\ p f = Some (t,d1,d2,s') )\/
      ~(intcont ks = None)
    ).

Parameter pdata: var.

Inductive ltstep: lprog -> tid -> code -> clientst -> taskst -> code -> 
                  clientst -> taskst -> Prop :=
| clt_step: forall (p:lprog)(pc po pi:progunit) (ip:intunit) (C C':code) 
                   (m m':smem)(cenvs:cltenvs) 
                   (ge le le':env) (M M':mem) (t:tid) (cst cst':clientst) (tst:taskst),
              p= (pc, (po, pi, ip)) -> 
              cstep (pumerge pc po) C m C' m' ->
              ~ (InOS C (pumerge po pi)) -> 
              m = (ge, le, M) -> m' = (ge, le', M') ->
              get cenvs t = Some le ->
              cst = (ge,cenvs, M) -> cst'= (ge, ( set cenvs t le'), M') -> 
              ltstep p t C cst tst C' cst' tst

| inapi_step : forall (p:lprog)(pc po pi:progunit) (ip:intunit) (C C':code) 
                      (cst:clientst) (tst tst':taskst) (t:tid),
                 p= (pc, (po, pi, ip)) -> 
                 loststep (pumerge po pi) C tst C' tst' -> 
                 InOS C (pumerge po pi) ->
                 ltstep p t C cst tst C' cst tst'.      

Inductive ltstepev: lprog -> tid -> code -> clientst -> taskst -> code -> 
                    clientst -> taskst -> val -> Prop :=
| clt_stepev: forall (p:lprog)(pc po pi:progunit) (ip:intunit) (C C':code) (v:val)
                     (m :smem)  (cenvs:cltenvs) 
                     (ge le:env) (M :mem) (t:tid) (cst :clientst) (tst:taskst),
                p=(pc, (po, pi, ip)) -> 
                cstepev (pumerge pc po) C m C' m v ->
                ~ (InOS C (pumerge po pi)) -> 
                m = (ge, le, M) -> 
                cst = (ge, cenvs, M ) -> 
                get cenvs t = Some le ->
                ltstepev p t C cst tst C' cst tst v.  

Definition loststepabt (p:progunit) (C:code) (tst: taskst) : Prop := 
  ~(exists C' tst', loststep p C tst C' tst').



Inductive ltstepabt: lprog -> tid -> code -> clientst -> taskst -> Prop :=
| taskabort: forall  (p:lprog) (t:tid) (pc po pi:progunit)(cst:clientst) (ip:intunit) (C:code)
                     (tst:taskst),
               p=(pc, (po, pi, ip)) ->  
               ~((exists (C':code) (tst':taskst) (cst':clientst), ltstep p t C cst tst C' cst' tst')
                 \/(exists (C':code) (tst':taskst) (cst':clientst) ev, ltstepev p t C cst tst C' cst' tst' ev)
                )-> ltstepabt p t C cst tst.


Inductive lpstep: lprog -> tasks -> clientst -> osstate -> tid -> 
                  tasks -> clientst -> osstate ->tid -> Prop :=
| pint_step : forall (pc pi po:progunit) (ip:intunit) (p:lprog) (T T':tasks) (cst:clientst)
                     (S S':osstate) (t:tid) (tst tst':taskst) (C C':code),
                p=(pc, (po, pi, ip)) ->
                get T t = Some C ->  set T t C'= T'->
                projS S t = Some tst -> projS S' t = Some tst'-> Steq S S' t->
                lintstep ip C tst C' tst' ->
                lpstep p T cst S t T' cst S' t

| pt_step : forall (p:lprog) (T T':tasks) (S S':osstate) (t:tid) 
                   (tst tst':taskst)(C C':code) 
                   (cst cst':clientst)  ,
              get T t = Some C ->  set T t C'= T'->
              projS S t =Some tst -> projS S' t =Some tst' ->
              Steq S S' t ->
              ltstep p t C cst tst C' cst' tst' ->
              lpstep p T cst S t T' cst' S' t
| pswitch_step: forall (p:lprog) pc po pi ip (T T':tasks) (x:var)  (S S':osstate) (cst:clientst) (t t':tid) (ks:stmtcont) (tst:taskst) l tp b ge les m m' ir au,
                  p =(pc,(po,pi,ip)) ->
                  (*InOS ((curs (sprim (switch x))), (kenil, ks))  (pumerge po pi) ->*)
                  projS S t = Some tst ->
                  get (get_genv (get_smem tst)) x = Some (l,(Tptr tp)) ->
                  load (Tptr tp) (get_mem (get_smem tst)) (l,0%Z) = Some (Vptr t')-> 
                  get T t = Some ((curs (sprim (switch x))), (kenil, ks)) ->
                  set T t (SKIP, (kenil, ks))= T'->
                  S = (ge,les,m,ir,au) ->
                  S' = (ge,les,m',ir,au)->
                  get ge OSTCBCur = Some (b,(Tptr tp)) ->
                  store (Tptr tp) m (b,0%Z) (Vptr t') = Some m'-> 
                  lpstep p T cst S t T' cst S' t'
| pstkinit_step: forall (p:lprog) (T T':tasks) (S:osstate) (t t':tid) (tst:taskst)(C C':code) 
                        (cst cst':clientst)  (ks:stmtcont) (e1 e2 e3:expr)
                        (tau:type) (d1 d2:decllist) (s:stmts) (pc pi po:progunit) (ip:intunit) (f:fid) v1 v m_os ir au cenvs M M' ge le,
                   p=(pc, (po, pi, ip)) ->
                   get T t = Some C ->
                   C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))->
                   C'= (SKIP, (kenil, ks))->
                   set T t C'= T'->
                   evalval e1 m_os = Some v1 ->
                   evalval e2 m_os = Some v -> 
                   evalval e3 m_os = Some (Vptr t')->
                   vtoZ v1 =Some f ->
                   pc f = Some (tau, d1, d2, s) ->
                   cstepstar pc ((curs (sfexec f (cons v nil) ((Tptr Tvoid)::nil))), (kenil, kstop))
                             (ge,emp,M) ((curs s), (kenil, (kcall f s emp kstop))) (ge,le,M') ->
                   evaltype e2 m_os = Some (Tptr Tvoid) ->
                   tst =(m_os, ir, au) ->
                   projS S t =Some tst ->
                   cst = (ge, cenvs, M) ->
                   cst'=(ge, ( set cenvs t' le), M') ->
                   lpstep p T cst S t ( set T' t' (nilcont s)) cst' (Snewt S t') t
| pstkinitskip_step: forall (p:lprog) (T T':tasks) (S :osstate) (t t':tid) (tst:taskst)(C C':code) 
                            (cst:clientst)  (ks:stmtcont) (e1 e2 e3:expr)
                            (pc pi po:progunit) (ip:intunit) (f:fid) v1 v m_os ir au cenvs M ge,
                       p=(pc, (po, pi, ip)) ->
                       get T t = Some C ->
                       C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))->
                       C'= (SKIP, (kenil, ks))->
                       set T t C'= T'->
                       evalval e1 m_os = Some v1 ->
                       evalval e2 m_os = Some v -> 
                       evalval e3 m_os = Some (Vptr t')->
                       vtoZ v1 =Some f ->
                       (pc f = None \/ 
                        (exists t d1 d2 s,
                           pc f = Some (t ,d1,d2,s) /\
                           ~(exists le M', cstepstar pc ((curs (sfexec f (cons v nil) ((Tptr Tvoid)::nil))), (kenil, kstop)) (ge, emp,M) ((curs s), (kenil, (kcall f s emp kstop))) (ge,le,M')))) ->
                       evaltype e2 m_os = Some (Tptr Tvoid) ->
                       tst =(m_os, ir, au) ->
                       projS S t =Some tst ->
                       cst = (ge, cenvs, M) ->
                       lpstep p T cst S t ( set T' t' (nilcont (sskip None))) cst (Snewt S t') t

| pstkfree_step: forall T T' C C' (ks:stmtcont) (m:smem) (e:expr) (t':tid) (pc po pi:progunit) (ip:intunit)
                        (ir:isr) (au:localst) (p:lprog) D ge cenvs M D' t S,
                   p= (pc, (po, pi, ip)) ->
                   get T t = Some C ->
                   C =(curs (sprim (stkfree e)), (kenil, ks)) ->
                   C'= (SKIP, (kenil, ks))->
                   set T t C'= T'->
                   D = (ge,cenvs,M) ->
                   D' = (ge, (del cenvs t'), M)->
                   evalval e m = Some (Vptr t') ->
                   projS S t = Some (m,ir,au) ->
                   lpstep p T D S t T' D' S t.


Inductive lpstepev: lprog -> tasks -> clientst -> osstate -> tid -> 
                    tasks -> clientst -> osstate ->tid -> val -> Prop :=
| pt_stepev :  forall (p:lprog) (T T':tasks) (S :osstate) (t :tid)
                      (tst:taskst)
                      (cst:clientst) (c:cureval) (C C':code) 
                      (ev:val), 
                 get T t = Some C ->  set T t C'= T'->
                 projS S t =Some tst ->
                 ltstepev p t C cst tst C' cst tst ev ->
                 lpstepev p T cst S t T' cst S t ev.

Definition IsEnd (C : code) : Prop := exists v, C = (curs (sskip v), (kenil, kstop)).

Definition IsSwitch (C : code) : Prop := exists x ks,
                                           C = (curs (sprim (switch x)),(kenil, ks)).

Definition IsFcall (C:code) : Prop := exists f vl tl ks,
                                        C = (curs (sfexec f vl tl), (kenil,ks)).

Definition IsRet (C : code) : Prop := (exists ks, C = (curs sret, (kenil, ks))
                                                  /\ callcont ks = None/\intcont ks =None).

Definition IsRetE (C : code) : Prop := (exists v ks, C = ([v], (kenil , 
                                                                (kret ks)))/\
                                                     callcont ks = None/\intcont ks =None).

Definition IsIRet (C : code) : Prop := (exists ks, C = (curs (sprim exint), (kenil, ks)) /\ intcont ks = None/\callcont ks =None).


Definition IsStkInit (C:code):= (exists e1 e2 e3 ks, C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))).

Definition IsStkFree (C:code):= (exists e ks, C = (curs (sprim (stkfree e)),(kenil,ks))).

Inductive lpstepabt: lprog ->  tasks -> clientst -> osstate -> tid -> Prop:=
| progabort: forall (p:lprog) (T :tasks) (S :osstate) (t:tid) (tst :taskst) 
                    (cst:clientst)(C:code) (v : option val) ,
               get T t = Some C -> 
               projS S t =Some tst ->
               ~ IsSwitch C ->
               ~ IsStkInit C ->
               ~ IsStkFree C ->
               ~ IsEnd C ->
               ltstepabt p t C cst tst ->
               lpstepabt p T cst S t
| crt_abt: forall (p:lprog) (T :tasks) (S :osstate) (t:tid) (tst :taskst) 
                  (cst:clientst)(C:code) e1 e2 e3 ks ,
               get T t = Some C -> 
               projS S t =Some tst ->
               C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks)) ->
               (~ exists v1 v t',
                    evalval e1 (get_smem tst) = Some v1 /\
                    evalval e2 (get_smem tst) = Some v /\
                    evalval e3 (get_smem tst) = Some (Vptr t')
               ) ->
               lpstepabt p T cst S t
| del_abt: forall (p:lprog) (T :tasks) (S :osstate) (t:tid) (tst :taskst) 
                  (cst:clientst)(C:code) e ks,
               get T t = Some C -> 
               projS S t =Some tst ->
               C = (curs (sprim (stkfree e)),(kenil,ks)) ->
               (~ exists t',
                    evalval e (get_smem tst) = Some (Vptr t')
               )  ->
               lpstepabt p T cst S t
| switch_abt: forall (p:lprog) (T :tasks) (S :osstate) (t:tid) (tst :taskst) 
                     (cst:clientst)(C:code) x ks,
                get T t = Some C -> 
                projS S t =Some tst ->
                C = (curs (sprim (switch x)),(kenil,ks)) ->
                (~ exists l tp t',
                     get (get_genv (get_smem tst)) x = Some (l,(Tptr tp)) /\
                     load (Tptr tp) (get_mem (get_smem tst)) (l,0%Z) = Some (Vptr t') 
                )  ->
                lpstepabt p T cst S t.

(****)
Definition eqdomtls (tls tls':TcbMod.map):=
  forall tid, indom tls tid <-> indom tls' tid.


Definition eqdomO (O O':osabst):= (forall (x:absdataid), indom O x <-> indom O' x) /\
                                  ( forall tls,  get O abstcblsid = Some (abstcblist tls) ->
                                                 exists tls',  get O' abstcblsid = Some (abstcblist tls') /\ eqdomtls tls tls' ).
(*
Definition eqdomO (O O':osabst):= (forall x,  indom O x <->  indom O' x) /\
                                  ( (~ exists tls,  get O abstcblsid = Some (abstcblist tls)) \/
                                    exists tls tls',  get O abstcblsid = Some (abstcblist tls) /\
                                                      get O' abstcblsid = Some (abstcblist tls') /\
                                                     eqdomtls tls tls' ).
 *)
Definition tidsame (O O':osabst):=  get O curtid =  get O' curtid.

Inductive spec_step: ossched -> spec_code -> osabst -> spec_code -> osabst -> Prop :=
| spec_prim_step:
    forall sc O O' (step:osabstep) v Of vl OO OO',
      step vl O (v,O') ->
      eqdomO O O' ->
      tidsame O O' ->
      join O Of OO ->
      join O' Of OO' ->
      spec_step sc (spec_prim vl step) OO (spec_done v) OO'
                
| spec_seq_step1:
    forall v cd O sc,
      spec_step sc (spec_seq (spec_done v) cd) O cd O 

| spec_seq_step2:
    forall O O' s1 s2 s1' sc,
      spec_step sc s1 O s1' O' ->
      spec_step sc (spec_seq s1 s2) O (spec_seq s1' s2) O'

| spec_choice_step1:
    forall O s1 s2 sc,
      spec_step sc (spec_choice s1 s2) O s1 O

| spec_choice_step2:
    forall O s1 s2 sc,
      spec_step sc (spec_choice s1 s2) O s2 O

| spec_assume_step:
    forall O Of (b:absexpr) OO sc ,
      b O ->
      join O Of OO ->
      spec_step sc (spec_assume b)  OO  (spec_done None) OO
                
| spec_sched_step:
    forall t O Of OO (sc:ossched),
      get O curtid = Some (oscurt t) ->
      sc O t -> 
      join O Of OO ->
      spec_step sc sched OO (spec_done None) OO
. 


Inductive spec_stepstar:  ossched -> spec_code -> osabst -> spec_code -> osabst -> Prop :=
| spec_stepO:
    forall c O sc,
      spec_stepstar sc c O c O
| spec_stepS:
    forall c O c' O' c'' O'' sc,
      spec_step sc c O c' O' ->
      spec_stepstar sc c' O' c'' O'' ->
      spec_stepstar sc c O c'' O''.

Inductive hapistep:  osspec -> code -> osabst -> code -> osabst -> Prop:=
| hapienter_step:
    forall (A :osspec) (B:osapispec) (C:osintspec) (D : ossched) (O:osabst) (cd cd':code)
           (ks:stmtcont) (f:fid) (vl:vallist) r tl tp ,
      A= (B, C, D) ->
      tl_vl_match tl vl = true->
      cd = (curs (sfexec f (List.rev vl) (List.rev tl)), (kenil, ks)) ->
      cd'=  (curs (hapi_code (r vl)), (kenil, ks))->
      B f = Some (r,(tp,tl)) ->
      hapistep  A cd O cd' O
                
| hidapi_step :
    forall (A :osspec) (O O':osabst)
           ke ks cd cd',
      spec_step (snd A) cd O cd' O' ->
      hapistep A ((curs (hapi_code cd )),(ke, ks)) O ((curs (hapi_code cd')),(ke,ks)) O'

| hapiexit_step :
    forall (A :osspec) (O:osabst)
           ke ks v,
      hapistep A ((curs (hapi_code (spec_done v))),(ke, ks)) O ((curs (sskip v)),(ke,ks)) O
               
| hintex_step: forall  (A :osspec) c ke ks  O,
                 hapistep A  (curs (hapi_code (spec_done None)),(kenil,kevent c ke ks)) O
                          (c,(ke,ks)) O.

Inductive htstep: hprog -> tid -> code -> clientst -> osabst -> code -> clientst -> osabst -> Prop:=
| htclt_step : forall (p:hprog) (pc:progunit) (A:osspec) (c c':code) (m m':smem)
                      (cenvs:cltenvs)  (ge le le':env) (M M':mem) (t:tid) 
                      (cst cst':clientst) (O:osabst),
                 p= (pc, A) -> 
                 cstep pc c m c' m' -> 
                 m = (ge, le, M) -> m' = (ge, le', M') ->
                 get cenvs t = Some le ->
                 cst = (ge,cenvs, M) ->
                 cst'=  (ge, ( set cenvs t le'), M') ->
                 htstep p t c cst O c' cst' O
| hapi_step : forall (p:hprog)(A: osspec) (pc:progunit) (O O':osabst) (c c':code) (cst:clientst) t,
                p=(pc, A) ->
                hapistep  A c O c' O'->
                htstep p t c cst O c' cst O'.


Inductive htstepev:  hprog  -> tid -> code -> clientst -> osabst -> code -> clientst -> osabst -> val -> Prop:=
| hclt_stepev : forall (p:hprog) (pc:progunit) (A:osspec) (c c':code) (m :smem)
                       (cenvs:cltenvs)  (ge le:env) (M M':mem) (t:tid) (ev:val)
                       (cst:clientst) (O:osabst),
                  p= (pc, A) -> 
                  cstepev pc c m c' m ev->
                  m = (ge, le, M) ->
                  cst = (ge, cenvs, M) ->
                  get cenvs t = Some le -> 
                  htstepev p t c cst O c' cst O ev.

Definition IsCrt (C:code) := exists v1 v2 v3 scre k, C = (curs (hapi_code (spec_seq (spec_crt v1 v2 (Vint32 v3)) scre)), k).
Definition IsDel (C:code) := exists v sdel k, C = (curs (hapi_code (spec_seq (spec_del (Vint32 v)) sdel)), k).
Definition IsSc (C:code) := exists s k, C = (curs (hapi_code (spec_seq sched s)), k).

Inductive htstepabt: hprog -> tid -> code -> clientst -> osabst -> Prop:=
| htstep_abt : forall (p:hprog) (pc:progunit) (A:osspec) (c:code)  (t:tid) 
                      (cst :clientst) (O:osabst),
                 p= (pc, A) ->
                 ~ IsEnd c ->
                 ~ IsCrt c ->
                 ~ IsDel c ->
                 ~ IsSc c ->
                 ~(exists c' cst' O', htstep p t c cst O c' cst' O') ->
                 ~(exists c' cst' O' ev, htstepev p t c cst O c' cst' O' ev) ->
                 htstepabt p t c cst O.

Inductive htstepstar:  hprog  -> tid -> code -> clientst -> osabst -> code -> clientst -> osabst -> Prop:=
| ht_starO: forall (p:hprog)  (c:code) (cst:clientst) (O:osabst) t,
              htstepstar p t c cst O c cst O
| ht_starS: forall (p:hprog)  (c c' c'':code) (cst cst' cst'':clientst) (O O' O'':osabst) t,
              htstep p t c cst O c' cst' O' -> htstepstar p t c' cst' O' c'' cst'' O''->
              htstepstar p t c cst O c'' cst'' O''.


Inductive htstepevstar: hprog -> tid -> code -> clientst -> osabst -> 
                        code -> clientst -> osabst -> val -> Prop:=
| htev_stepstar: forall (p:hprog)  (c c' c'' c''':code) 
                        (O O' O'':osabst) (ev:val) cst cst' cst'' t,
                   htstepstar p t c cst O c' cst' O' ->
                   htstepev p t c' cst' O' c'' cst' O' ev ->
                   htstepstar p t c'' cst' O' c''' cst'' O'' ->
                   htstepevstar p t c cst O c''' cst'' O'' ev.

Inductive htstepabtstar: hprog  -> tid ->  code -> clientst -> osabst -> Prop:=
| htabtstar: forall (p:hprog)  (c:code) (cst:clientst) (O:osabst) t,
               (exists (c':code) (cst':clientst) (O':osabst), 
                  htstepstar p t c cst O c' cst' O' /\
                  htstepabt p t c' cst' O')
               -> htstepabtstar p t c cst O.

Inductive htistep: osintspec -> code  -> osabst -> code  -> osabst -> Prop:=
| hinten_step: forall  (C :osintspec)  (O:osabst) c ke ks (i:hid) l,
                 C i = Some l ->
                 htistep C (c,(ke,ks)) O (curs (hapi_code l),(kenil,kevent c ke ks)) O.


Inductive hpstep: hprog -> tasks -> clientst -> osabst ->  
                  tasks -> clientst -> osabst -> Prop:=
| hp_step: forall (p:hprog) (T T':tasks) (O O':osabst) (cst cst':clientst) 
                  (C C':code) (t:tid),
             get O curtid = Some (oscurt t) ->
             htstep p t C cst O C' cst' O' ->
             get T t = Some C -> T' =  set T t C' ->
             hpstep p T cst O T' cst' O'
                    
| hi_step : forall (p:hprog) pc A  ispec B  (T T':tasks)
                   (O O':osabst) (cst:clientst) 
                   (C C':code) (t:tid),
              p = (pc, (A, ispec, B)) ->
              get O curtid = Some (oscurt t) ->
              get T t = Some C ->
              T' =  set T t C' ->
              htistep ispec C O C' O' ->
              hpstep p T cst O T' cst O'
                     
| hswi_step: forall (p:hprog) pc A B sd (T T':tasks) (cst:clientst) (O:osabst) (t t':tid) C ke ks s,
               p = (pc,(A,B,sd)) ->
               sd O t'->
               get O curtid = Some (oscurt t) ->
               get T t = Some C ->
               C = (curs (hapi_code (spec_seq sched s)), (ke,ks)) ->
               T' =  set T t (curs (hapi_code s),(ke,ks)) ->
               hpstep p T cst O T' cst (set O curtid (oscurt t'))
                      
| hpcrt_step : forall (T:tasks) (O O':osabst) (t t':tid)
                      (s:stmts) (cst cst':clientst)
                      (pc:progunit) (A:osspec) (tau:type) (d1 d2:decllist) 
                      (C C' :code) f tls tls' v1 v2 v3 ge le M M' cenvs ke ks scre,
                 get T t = Some C ->
                 C = (curs (hapi_code (spec_seq (spec_crt v1 v2 (Vint32 v3)) scre)), (ke,ks)) ->
                 C' = (curs (hapi_code scre), (ke, ks)) ->
                 get O curtid = Some (oscurt t) ->

                 vtoZ v1 =Some f ->
                 
                 pc f = Some (tau, d1, d2, s)->
                 cstepstar pc ((curs (sfexec f (cons v2 nil) ((Tptr Tvoid)::nil))), (kenil, kstop))
                           (ge,emp,M) ((curs s), (kenil, (kcall f s emp kstop))) (ge,le,M') ->
                 cst = (ge, cenvs, M) ->
                 cst'=(ge, (set cenvs t' le), M') ->
                 
                 get O abstcblsid = Some (abstcblist tls) ->
                 set O abstcblsid (abstcblist tls') = O' ->
                 join tls (sig t' (v3,rdy,Vnull)) tls' ->
                 
                 hpstep (pc, A) T cst O
                        ( set ( set T t C') t' (nilcont s)) 
                        cst' O'
                        
| hpcrtskip_step : forall (T:tasks) (O O':osabst) (t t':tid)
                          (cst:clientst)
                          C C' (pc:progunit) (A:osspec)
                           f tls tls' v1 v2 v3 ge M cenvs ke ks scre,
                     get T t = Some C ->
                     C = (curs (hapi_code (spec_seq (spec_crt v1 v2 (Vint32 v3)) scre)), (ke,ks)) ->
                     C' = (curs (hapi_code scre), (ke, ks)) ->
                     get O curtid = Some (oscurt t) ->

                     vtoZ v1 =Some f ->
                     
                     (pc f = None \/ 
                      (exists t d1 d2 s,
                         pc f = Some (t ,d1,d2,s) /\
                         ~(exists le M', cstepstar pc ((curs (sfexec f (cons v2 nil) ((Tptr Tvoid)::nil))), (kenil, kstop)) (ge, emp,M) ((curs s), (kenil, (kcall f s emp kstop))) (ge,le,M')))) ->
                     
                    
                     cst = (ge, cenvs, M) ->
                     
                     get O abstcblsid = Some (abstcblist tls) ->
                     set O abstcblsid (abstcblist tls') = O' ->
                     join tls (sig t' (v3,rdy,Vnull)) tls' ->                 
                     hpstep (pc, A) T cst O
                            ( set ( set T t C') t' (nilcont (sskip None))) cst O'
| hpdel_step: forall p T T' t t' C C' sdel ke ks ge cenvs M O O' tls tls' cst cst' prio st msg,
                
                   get T t = Some C ->
                   C =(curs (hapi_code (spec_seq (spec_del (Vint32 prio)) sdel)), (ke,ks)) ->
                   C'= (curs (hapi_code sdel), (ke, ks))->
                   set T t C'= T'->
                   cst = (ge,cenvs,M) ->
                   cst' = (ge, (del cenvs t'), M)->
                   get O abstcblsid = Some (abstcblist tls) ->
                   set O abstcblsid (abstcblist tls') = O' ->
                   get tls t' = Some (prio,st,msg) ->
                   join tls' (sig t' (prio,st,msg)) tls->
                   get O curtid = Some (oscurt t) ->
                   hpstep p T cst O T' cst' O'.


Definition abs_crt_step (O : OSAbstMod.map)  O' t t' p :=  
  t <> t' /\
  exists tls tls',
    get O curtid = Some (oscurt t) /\
    get O abstcblsid = Some (abstcblist tls) /\
    joinsig t' (p,rdy,Vnull) tls tls' /\
    O' = set O abstcblsid (abstcblist tls') .

Definition del_task (O : OSAbstMod.map)  O' t p :=
  exists tls tls' st msg,
    get O abstcblsid = Some (abstcblist tls) /\
    joinsig  t  (p, st, msg) tls' tls /\ 
    O' = set O abstcblsid (abstcblist tls').

Definition abs_delself_step (O : OSAbstMod.map)  O' t t' p := 
  t = t' /\  get O curtid = Some (oscurt t) /\  del_task O O' t' p.


Definition abs_delother_step (O : OSAbstMod.map)  O' t t' p:=  
  t <>  t' /\  get O curtid = Some (oscurt t) /\  del_task O O' t' p.

Inductive hpstepev: hprog -> tasks -> clientst -> osabst  ->  
                    tasks -> clientst -> osabst -> val -> Prop:=
| hpt_stepev: forall (p:hprog) (T T':tasks) (O:osabst) (cst:clientst) 
                     (C C':code) (t:tid) (ev:val),
                get O curtid = Some (oscurt t) ->
                htstepev p t C cst O C' cst O ev->
                get T t = Some C ->
                T' =  set T t C' ->
                hpstepev p T cst O  T' cst O  ev.

Inductive hpstepabt: hprog -> tasks -> clientst -> osabst -> Prop :=
| hpabt_step : forall (p: hprog) (T :tasks) (cst:clientst) (O:osabst) (t:tid) (C:code),
                 get O curtid = Some (oscurt t) ->
                 get T t = Some C ->
                 htstepabt p t C cst O -> 
                 hpstepabt p T cst O
| hpcreabt_step : forall (T:tasks) (O:osabst) (t:tid)
                         (cst:clientst)
                         p (C :code) v1 v2 v3 ke ks scre,
                    get T t = Some C ->
                    C = (curs (hapi_code (spec_seq (spec_crt v1 v2 (Vint32 v3)) scre)), (ke,ks)) ->
                    get O curtid = Some (oscurt t) ->
                    (~ exists O' t', abs_crt_step O O' t t' v3) ->
                    hpstepabt p T cst O
| hpdelabt_step : forall (T:tasks) O t
                         (cst:clientst)
                         p C v ke ks sdel,
                    get T t = Some C ->
                    C = (curs (hapi_code (spec_seq (spec_del (Vint32 v)) sdel)), (ke,ks)) ->
                    get O curtid = Some (oscurt t) ->
                    (~ exists O' t', abs_delself_step O O' t t' v \/ abs_delother_step O O' t t' v) ->
                    hpstepabt p T cst O
| hscabt_step: forall (T:tasks) (O:osabst) (t:tid)
                      (cst:clientst)
                      p (C:code) ke ks s pc A B sd,
                 p = (pc,(A,B,sd)) ->
                 get T t = Some C ->
                 C = (curs (hapi_code (spec_seq sched s)), (ke,ks)) ->
                 get O curtid = Some (oscurt t) ->
                 (~ exists t', sd O t') ->
                 hpstepabt p T cst O.

Inductive hpstepstar: hprog -> tasks -> clientst -> osabst  ->  
                      tasks -> clientst -> osabst  -> Prop:=
| hp_stepO: forall (p:hprog) (T:tasks) (cst:clientst) O,
              hpstepstar p T cst O  T cst O 
| hp_stepS: forall p T T' T'' cst cst' cst'' O O' O'',
              hpstep p T cst O T' cst' O' ->
              hpstepstar p T' cst' O'  T'' cst'' O''->
              hpstepstar p T cst O T'' cst'' O'' .

Inductive hpstepevstar: hprog -> tasks -> clientst -> osabst  ->  
                        tasks -> clientst -> osabst  -> val -> Prop:=
| hp_stepev: forall p T T' T'' T'''  cst cst' cst''  O O' O'' ev,
               hpstepstar p T cst O  T' cst' O' ->
               hpstepev p T' cst' O'  T'' cst' O'  ev->
               hpstepstar p T'' cst' O'  T''' cst'' O''->
               hpstepevstar p T cst O  T''' cst'' O'' ev.

Inductive hpstepabtstar: hprog -> tasks -> clientst -> osabst -> Prop:=
| hp_stepstarabt: forall p T cst O ,
                    (exists T' cst' O' , hpstepstar p T cst O  T' cst' O' /\
                                         hpstepabt p T' cst' O') -> hpstepabtstar p T cst O.

