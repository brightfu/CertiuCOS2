Require Import memory.

Set Implicit Arguments.
Unset Strict Implicit.

(**The High-level Specification Language **)
Definition priority := int32.
Definition ecbid := addrval.
Definition msg := val.
Definition maxlen := int32.
Definition  ostime := int32.
Definition waitset := list tid.

Inductive tcbstats:=
| os_stat_sem: ecbid -> tcbstats
| os_stat_q: ecbid -> tcbstats
| os_stat_time:  tcbstats
| os_stat_mbox: ecbid -> tcbstats
| os_stat_mutexsem: ecbid -> tcbstats.

Inductive taskstatus :=
 | rdy: taskstatus
 | wait : tcbstats -> int32 -> taskstatus.

Module abstcb.
  Definition B : Set := ( priority * taskstatus * msg)%type.
  Definition holder : B:= (Int.zero, rdy, Vnull).
End abstcb.

Module TcbMod := MapLib.MapFun tidspec abstcb.

(* Definition tcbdel := fun (M:TcbMod.map) a => TcbMod.minus M (TcbMod.sig a (Int.zero,rdy,Vnull)). *)

Instance TcbMap: PermMap tid ( priority * taskstatus * msg) TcbMod.map :=
  {
    usePerm := TcbMod.usePerm;
    isRw := TcbMod.isRw;
    flip := TcbMod.flip;
    sameV := TcbMod.sameV;
    same := TcbMod.same;
    emp := TcbMod.emp;
    join := TcbMod.join;
    del := TcbMod.del;
    get := TcbMod.get;
    set := TcbMod.set;
    sig := TcbMod.sig;
    merge := TcbMod.merge;
    minus := TcbMod.minus
}.
Proof.
  exact TcbMod.map_dec_a.
  intros; tryfalse.
  intros; tryfalse.
  exact TcbMod.map_join_emp.
  exact TcbMod.map_join_pos.
  exact TcbMod.map_join_comm.
  exact TcbMod.map_join_assoc.
  exact TcbMod.map_join_cancel.
  exact TcbMod.map_join_deter.
  exact TcbMod.map_sv_ref.
  exact TcbMod.map_sv_comm.
  exact TcbMod.map_sv_assoc.
  exact TcbMod.map_perm_eql.
  exact TcbMod.map_flip_isRw.
  exact TcbMod.map_flip_sv.
  exact TcbMod.map_emp_get.
  exact TcbMod.map_eql.
  exact TcbMod.map_disjoint.
  exact TcbMod.map_get_unique.
  exact TcbMod.map_get_sig.
  exact TcbMod.map_get_sig'.
  exact TcbMod.map_get_set.
  exact TcbMod.map_get_set'.
  exact TcbMod.map_join_get_none.
  exact TcbMod.map_join_get_some.
  exact TcbMod.map_join_getp_some.
  exact TcbMod.map_set_emp.
  exact TcbMod.map_set_sig.
  exact TcbMod.map_join_set_none.
  exact TcbMod.map_join_set_perm.
  exact TcbMod.map_join_get_sig.
  exact TcbMod.map_join_get_sig_perm.
  exact TcbMod.map_merge_sem.
  intros; tryfalse.
  exact TcbMod.map_join_merge.
  exact TcbMod.map_merge_comm.
  intros; tryfalse.
  intros; tryfalse.
  exact TcbMod.map_minus_sem.
  intros; tryfalse.
  exact TcbMod.map_join_minus.
  exact TcbMod.map_del_sem.
Defined.

Definition owner:= option (tid * int32).

Inductive edata:=
| abssem: int32 -> edata
| absmsgq : list msg -> maxlen -> edata
| absmbox: msg -> edata
| absmutexsem: int32 -> owner -> edata.

Module absecb.
  Definition B : Set := prod edata waitset.
  Definition holder : B := (absmbox Vnull, nil).
End absecb.

Module EcbMod := MapLib.MapFun tidspec absecb.

(* Definition ecbdel := fun (M:EcbMod.map) a => EcbMod.minus M (EcbMod.sig a (absmbox Vnull,nil)). *)

Instance EcbMap: PermMap tid (prod edata waitset) EcbMod.map :=
  {
    usePerm := EcbMod.usePerm;
    isRw := EcbMod.isRw;
    flip := EcbMod.flip;
    sameV := EcbMod.sameV;
    same := EcbMod.same;
    emp := EcbMod.emp;
    join := EcbMod.join;
    del := EcbMod.del;
    get := EcbMod.get;
    set := EcbMod.set;
    sig := EcbMod.sig;
    merge := EcbMod.merge;
    minus := EcbMod.minus
  }.
Proof.
  exact EcbMod.map_dec_a.
  intros; tryfalse.
  intros; tryfalse.
  exact EcbMod.map_join_emp.
  exact EcbMod.map_join_pos.
  exact EcbMod.map_join_comm.
  exact EcbMod.map_join_assoc.
  exact EcbMod.map_join_cancel.
  exact EcbMod.map_join_deter.
  exact EcbMod.map_sv_ref.
  exact EcbMod.map_sv_comm.
  exact EcbMod.map_sv_assoc.
  exact EcbMod.map_perm_eql.
  exact EcbMod.map_flip_isRw.
  exact EcbMod.map_flip_sv.
  exact EcbMod.map_emp_get.
  exact EcbMod.map_eql.
  exact EcbMod.map_disjoint.
  exact EcbMod.map_get_unique.
  exact EcbMod.map_get_sig.
  exact EcbMod.map_get_sig'.
  exact EcbMod.map_get_set.
  exact EcbMod.map_get_set'.
  exact EcbMod.map_join_get_none.
  exact EcbMod.map_join_get_some.
  exact EcbMod.map_join_getp_some.
  exact EcbMod.map_set_emp.
  exact EcbMod.map_set_sig.
  exact EcbMod.map_join_set_none.
  exact EcbMod.map_join_set_perm.
  exact EcbMod.map_join_get_sig.
  exact EcbMod.map_join_get_sig_perm.
  exact EcbMod.map_merge_sem.
  intros; tryfalse.
  exact EcbMod.map_join_merge.
  exact EcbMod.map_merge_comm.
  intros; tryfalse.
  intros; tryfalse.
  exact EcbMod.map_minus_sem.
  intros; tryfalse.
  exact EcbMod.map_join_minus.
  exact EcbMod.map_del_sem.
Defined.


Inductive absdataid:=
| abstcblsid : absdataid
| absecblsid: absdataid
| ostmid : absdataid
| curtid:absdataid.


Definition absdataid_eq (id1 id2:absdataid):=
  match id1, id2 with
    | abstcblsid, abstcblsid => true
    | absecblsid,absecblsid => true
    | ostmid, ostmid => true
    | curtid,curtid => true
    | _,_ => false
  end.

Definition absdataid_lt (id1 id2:absdataid):=
  match id1, id2 with
    | abstcblsid, abstcblsid => false
    | abstcblsid, _ => true
    | absecblsid, abstcblsid => false
    | absecblsid, absecblsid => false
    | absecblsid, _ =>true
    | ostmid, abstcblsid =>false
    | ostmid, absecblsid => false
    | ostmid, ostmid => false
    | ostmid, _ => true
    | curtid, _ => false 
  end.

Module absdataidspec.
  Definition A := absdataid.
  Definition beq := absdataid_eq.
  Definition blt := absdataid_lt.
 
Lemma beq_true_eq : forall a a' : A,
    beq a a' = true -> a = a'.
Proof.
  intros.
  destruct a,a';simpl in H;auto;tryfalse.
Qed.    


Lemma beq_false_neq : forall a a' : A,
    beq a a' = false -> a <> a'.
Proof. 
  intros.
  destruct a,a';simpl in H; introv Hf; auto;tryfalse.
Qed.  

Lemma eq_beq_true : forall a a' : A,
    a = a' -> beq a a' = true.
Proof.
  intros.
  destruct a,a';simpl in H;auto;tryfalse.
Qed.

Lemma neq_beq_false : forall a a' : A,
    a <> a' -> beq a a' = false.
Proof.
intros.
destruct a ,a';simpl in H;auto;tryfalse.
Qed.

Lemma blt_trans : 
  forall a a' a'' : A,
    blt a a' = true -> blt a' a'' = true -> blt a a'' = true.
Proof.
  unfold blt; intros.
  destruct a,a',a'';simpl in H, H0;auto;tryfalse.
Qed.

Lemma blt_irrefl :
  forall a : A,
    blt a a = false.
Proof.  
  unfold blt; intros.
  destruct a;simpl;auto.
Qed.

Lemma blt_asym : 
  forall a b : A, 
    blt a b = true -> blt b a = false.
Proof.  
  unfold blt; intros.
  destruct a,b;simpl in *;auto;tryfalse.
Qed.

Lemma blt_beq_dec :
  forall a b : A,
    {blt a b = true} + {beq a b = true} + {blt b a = true}.
Proof.
  unfold blt; unfold beq; intros.
  remember (absdataid_lt a b) as bool1; destruct bool1.
  left; left; auto.
  remember (absdataid_eq a b) as bool2; destruct bool2.
  left; right; auto.
  destruct a,b;simpl in *;auto;tryfalse.
Qed.  


End absdataidspec.

Inductive absdata:= 
| abstcblist: TcbMod.map -> absdata
| absecblist : EcbMod.map -> absdata
| ostm: ostime -> absdata
| oscurt: addrval -> absdata.

Module absdatastru.
 
 Definition B := absdata. 
 Definition holder : B := (abstcblist emp).
 
End absdatastru.

Module OSAbstMod := MapLib.MapFun absdataidspec absdatastru.

Definition osabst:= OSAbstMod.map. 

(* Definition abstdel := fun (M:OSAbstMod.map) a => OSAbstMod.minus M (OSAbstMod.sig a (abstcblist emp)). *)

Instance AMap: PermMap absdataid absdata osabst :=
  {
    usePerm := OSAbstMod.usePerm;
    isRw := OSAbstMod.isRw;
    flip := OSAbstMod.flip;
    sameV := OSAbstMod.sameV;
    same := OSAbstMod.same;
    emp := OSAbstMod.emp;
    join := OSAbstMod.join;
    del := OSAbstMod.del;
    get := OSAbstMod.get;
    set := OSAbstMod.set;
    sig := OSAbstMod.sig;
    merge := OSAbstMod.merge;
    minus := OSAbstMod.minus
  }.
Proof.
  exact OSAbstMod.map_dec_a.
  intros; tryfalse.
  intros; tryfalse.
  exact OSAbstMod.map_join_emp.
  exact OSAbstMod.map_join_pos.
  exact OSAbstMod.map_join_comm.
  exact OSAbstMod.map_join_assoc.
  exact OSAbstMod.map_join_cancel.
  exact OSAbstMod.map_join_deter.
  exact OSAbstMod.map_sv_ref.
  exact OSAbstMod.map_sv_comm.
  exact OSAbstMod.map_sv_assoc.
  exact OSAbstMod.map_perm_eql.
  exact OSAbstMod.map_flip_isRw.
  exact OSAbstMod.map_flip_sv.
  exact OSAbstMod.map_emp_get.
  exact OSAbstMod.map_eql.
  exact OSAbstMod.map_disjoint.
  exact OSAbstMod.map_get_unique.
  exact OSAbstMod.map_get_sig.
  exact OSAbstMod.map_get_sig'.
  exact OSAbstMod.map_get_set.
  exact OSAbstMod.map_get_set'.
  exact OSAbstMod.map_join_get_none.
  exact OSAbstMod.map_join_get_some.
  exact OSAbstMod.map_join_getp_some.
  exact OSAbstMod.map_set_emp.
  exact OSAbstMod.map_set_sig.
  exact OSAbstMod.map_join_set_none.
  exact OSAbstMod.map_join_set_perm.
  exact OSAbstMod.map_join_get_sig.
  exact OSAbstMod.map_join_get_sig_perm.
  exact OSAbstMod.map_merge_sem.
  intros; tryfalse.
  exact OSAbstMod.map_join_merge.
  exact OSAbstMod.map_merge_comm.
  intros; tryfalse.
  intros; tryfalse.
  exact OSAbstMod.map_minus_sem.
  intros; tryfalse.
  exact OSAbstMod.map_join_minus.
  exact OSAbstMod.map_del_sem.
Defined.

Definition osabstep := vallist -> osabst -> (option val * osabst) -> Prop.

Definition absexpr := osabst -> Prop.

Inductive spec_code:=
| spec_prim :  vallist-> osabstep -> spec_code
| sched : spec_code
| spec_crt : val -> val -> val -> spec_code
| spec_del : val -> spec_code
| spec_done : option val -> spec_code
| spec_seq : spec_code -> spec_code -> spec_code
| spec_choice : spec_code -> spec_code -> spec_code
| spec_assume : absexpr -> spec_code.

Notation " x '(|' vl '|)' " := (spec_prim vl x) (at level 40).
Notation  " 'END' v " := (spec_done v)(at level 40).
Notation  " x ';;' y " := (spec_seq x y) (right associativity, at level 44). 
Notation  " x '??' y " := (spec_choice x y) (right associativity, at level 45).
Notation  " 'ASSUME' b " := (spec_assume b) (at level 40).


(**The Low-level Language ***)

(**The expressions and statements for the Low-level Language**)
Definition fid :=  ident.

(**The max number of interrupt handlers**)
Definition INUM := 2%nat.

Definition  hid := nat.

Inductive expr:=
 | enull : expr
 | evar : var -> expr
 | econst32 : int32 -> expr
 | eunop : uop -> expr -> expr
 | ebinop : bop -> expr -> expr -> expr
 | ederef : expr -> expr
 | eaddrof : expr -> expr 
 | efield : expr -> ident -> expr
 | ecast : expr -> type -> expr
 | earrayelem : expr -> expr -> expr.  (* expr1 [ expr2 ] *)

Definition exprlist : Set := list expr.

Inductive prim :=
 | exint : prim
 | switch : var -> prim
 | eoi : int32 -> prim
 | excrit : prim
 | encrit : prim
 | cli : prim
 | sti : prim
 | checkis : var -> prim 
 | stkinit : expr -> expr -> expr -> prim
 | stkfree : expr -> prim.

Inductive stmts :=
 | sskip : option val -> stmts
 | sassign : expr -> expr -> stmts (* expr1 = expr2 *)
 | sif : expr -> stmts -> stmts -> stmts (* if ( expr ) stmts1 else stmts2 *)
 | sifthen:expr->stmts->stmts
 | swhile : expr -> stmts -> stmts
 | sret : stmts
 | srete : expr -> stmts
 | scall : fid -> exprlist -> stmts
 | scalle : expr -> fid -> exprlist -> stmts
 | sseq : stmts -> stmts -> stmts (* right associative *)
 | sprint : expr -> stmts
 | sfexec : fid -> vallist -> typelist -> stmts
 | sfree : freelist -> option val ->  stmts
(*
 | sfreev : freelist -> val -> stmts
*)
 | salloc : vallist -> decllist -> stmts
 | sprim : prim -> stmts

 | hapi_code:spec_code -> stmts .

Open Scope type_scope.

Definition function  :=  (type  *  decllist * decllist *  stmts).

Definition progunit  := fid -> option function.

Definition intunit  := hid -> option stmts.

Definition oscode := (progunit * progunit * intunit).

Definition lprog  := (progunit * oscode).


Inductive cureval:=
|cure : expr -> cureval
(*
|curv : val-> cureval
*)
|curs : stmts -> cureval.
Notation "'SKIP'  " := (curs (sskip None))  (at level 0).

Notation "'[' v ']'" := (curs (sskip (Some v))) (at level 0).

(*Definition of continuation, which is a pair of expression continuation and statement continuation*)
Inductive exprcont:=
| kenil : exprcont
| keop1 : uop -> type -> exprcont -> exprcont
| keop2r : bop -> expr -> type -> type -> exprcont -> exprcont
| keop2l: bop -> val -> type -> type ->exprcont -> exprcont
| kederef : type -> exprcont -> exprcont 
| keoffset: int32 -> exprcont -> exprcont
| kearrbase: expr -> type -> exprcont -> exprcont
| kearrindex: val -> type -> exprcont -> exprcont
| kecast: type -> type -> exprcont -> exprcont.

Inductive stmtcont:=
| kstop : stmtcont
| kseq : stmts -> stmtcont -> stmtcont
| kcall : fid  -> stmts -> env -> stmtcont -> stmtcont
| kint : cureval -> exprcont -> env -> stmtcont -> stmtcont
| kassignr: expr -> type -> stmtcont -> stmtcont
| kassignl : val -> type -> stmtcont -> stmtcont
(*
| kcalle : fid -> exprlist -> type -> stmtcont -> stmtcont
*)
| kfuneval : fid -> vallist -> typelist -> exprlist -> stmtcont -> stmtcont
| kif : stmts -> stmts -> stmtcont -> stmtcont
| kwhile : expr -> stmts -> stmtcont -> stmtcont
| kret :   stmtcont -> stmtcont

| kevent : cureval -> exprcont -> stmtcont -> stmtcont
.

Definition  cont := (exprcont * stmtcont).

Definition code  := (cureval * cont).

Module CodeSpec.
  Definition B:= code.
  Definition holder : B := (curs (sskip None), (kenil, kstop)).
End CodeSpec.

Module TasksMod := MapLib.MapFun tidspec CodeSpec.

Definition tasks :=TasksMod.map.

(* Definition tasksdel := fun (M:tasks) a => TasksMod.minus M (TasksMod.sig a (curs (sskip None),(kenil,kstop))). *)

Instance TasksMap: PermMap tid code tasks :=
  {
    usePerm := TasksMod.usePerm;
    isRw := TasksMod.isRw;
    flip := TasksMod.flip;
    sameV := TasksMod.sameV;
    same := TasksMod.same;
    emp := TasksMod.emp;
    join := TasksMod.join;
    del := TasksMod.del;
    get := TasksMod.get;
    set := TasksMod.set;
    sig := TasksMod.sig;
    merge := TasksMod.merge;
    minus := TasksMod.minus
  }.
Proof.
  exact TasksMod.map_dec_a.
  intros; tryfalse.
  intros; tryfalse.
  exact TasksMod.map_join_emp.
  exact TasksMod.map_join_pos.
  exact TasksMod.map_join_comm.
  exact TasksMod.map_join_assoc.
  exact TasksMod.map_join_cancel.
  exact TasksMod.map_join_deter.
  exact TasksMod.map_sv_ref.
  exact TasksMod.map_sv_comm.
  exact TasksMod.map_sv_assoc.
  exact TasksMod.map_perm_eql.
  exact TasksMod.map_flip_isRw.
  exact TasksMod.map_flip_sv.
  exact TasksMod.map_emp_get.
  exact TasksMod.map_eql.
  exact TasksMod.map_disjoint.
  exact TasksMod.map_get_unique.
  exact TasksMod.map_get_sig.
  exact TasksMod.map_get_sig'.
  exact TasksMod.map_get_set.
  exact TasksMod.map_get_set'.
  exact TasksMod.map_join_get_none.
  exact TasksMod.map_join_get_some.
  exact TasksMod.map_join_getp_some.
  exact TasksMod.map_set_emp.
  exact TasksMod.map_set_sig.
  exact TasksMod.map_join_set_none.
  exact TasksMod.map_join_set_perm.
  exact TasksMod.map_join_get_sig.
  exact TasksMod.map_join_get_sig_perm.
  exact TasksMod.map_merge_sem.
  intros; tryfalse.
  exact TasksMod.map_join_merge.
  exact TasksMod.map_merge_comm.
  intros; tryfalse.
  intros; tryfalse.
  exact TasksMod.map_minus_sem.
  intros; tryfalse.
  exact TasksMod.map_join_minus.
  exact TasksMod.map_del_sem.
Defined.

Module EnvSpec.
  Definition B:= env.
  Definition holder : B := emp.
End EnvSpec.

Module CltEnvMod:= MapFun tidspec EnvSpec.

Definition cltenvs := CltEnvMod.map.
(* Definition cltenvdel := fun (M:CltEnvMod.map) a => CltEnvMod.minus M (CltEnvMod.sig a emp). *)

Instance CMap: PermMap tid env cltenvs :=
  {
    usePerm := CltEnvMod.usePerm;
    isRw := CltEnvMod.isRw;
    flip := CltEnvMod.flip;
    sameV := CltEnvMod.sameV;
    same := CltEnvMod.same;
    emp := CltEnvMod.emp;
    join := CltEnvMod.join;
    del := CltEnvMod.del;
    get := CltEnvMod.get;
    set := CltEnvMod.set;
    sig := CltEnvMod.sig;
    merge := CltEnvMod.merge;
    minus := CltEnvMod.minus
  }.
Proof.
  exact CltEnvMod.map_dec_a.
  intros; tryfalse.
  intros; tryfalse.
  exact CltEnvMod.map_join_emp.
  exact CltEnvMod.map_join_pos.
  exact CltEnvMod.map_join_comm.
  exact CltEnvMod.map_join_assoc.
  exact CltEnvMod.map_join_cancel.
  exact CltEnvMod.map_join_deter.
  exact CltEnvMod.map_sv_ref.
  exact CltEnvMod.map_sv_comm.
  exact CltEnvMod.map_sv_assoc.
  exact CltEnvMod.map_perm_eql.
  exact CltEnvMod.map_flip_isRw.
  exact CltEnvMod.map_flip_sv.
  exact CltEnvMod.map_emp_get.
  exact CltEnvMod.map_eql.
  exact CltEnvMod.map_disjoint.
  exact CltEnvMod.map_get_unique.
  exact CltEnvMod.map_get_sig.
  exact CltEnvMod.map_get_sig'.
  exact CltEnvMod.map_get_set.
  exact CltEnvMod.map_get_set'.
  exact CltEnvMod.map_join_get_none.
  exact CltEnvMod.map_join_get_some.
  exact CltEnvMod.map_join_getp_some.
  exact CltEnvMod.map_set_emp.
  exact CltEnvMod.map_set_sig.
  exact CltEnvMod.map_join_set_none.
  exact CltEnvMod.map_join_set_perm.
  exact CltEnvMod.map_join_get_sig.
  exact CltEnvMod.map_join_get_sig_perm.
  exact CltEnvMod.map_merge_sem.
  intros; tryfalse.
  exact CltEnvMod.map_join_merge.
  exact CltEnvMod.map_merge_comm.
  intros; tryfalse.
  intros; tryfalse.
  exact CltEnvMod.map_minus_sem.
  intros; tryfalse.
  exact CltEnvMod.map_join_minus.
  exact CltEnvMod.map_del_sem.
Defined.

(**The Low-level World**)
Definition  clientst :=  (env * cltenvs * mem)%type.
(*Interrupt Enable*)
Definition ie := bool.
(**Interrupt Stack**)
Definition is := list hid.
(**Historical values of ie**)
Definition cs := list ie.

Definition localst := (ie * is * cs)%type.

Module LocalStSpec.
  Definition B:= localst.
  Definition holder : B := (true, nil, nil).
End LocalStSpec.

Module TaskLStMod:= MapFun tidspec LocalStSpec.

Definition ltaskstset:= TaskLStMod.map.

(* Definition tasklstdel := fun (M:ltaskstset) a => TaskLStMod.minus M (TaskLStMod.sig a (true,nil,nil)). *)

Instance TaskLStMap: PermMap tid localst ltaskstset :=
  {
    usePerm := TaskLStMod.usePerm;
    isRw := TaskLStMod.isRw;
    flip := TaskLStMod.flip;
    sameV := TaskLStMod.sameV;
    same := TaskLStMod.same;
    emp := TaskLStMod.emp;
    join := TaskLStMod.join;
    del := TaskLStMod.del;
    get := TaskLStMod.get;
    set := TaskLStMod.set;
    sig := TaskLStMod.sig;
    merge := TaskLStMod.merge;
    minus := TaskLStMod.minus
  }.
Proof.
  exact TaskLStMod.map_dec_a.
  intros; tryfalse.
  intros; tryfalse.
  exact TaskLStMod.map_join_emp.
  exact TaskLStMod.map_join_pos.
  exact TaskLStMod.map_join_comm.
  exact TaskLStMod.map_join_assoc.
  exact TaskLStMod.map_join_cancel.
  exact TaskLStMod.map_join_deter.
  exact TaskLStMod.map_sv_ref.
  exact TaskLStMod.map_sv_comm.
  exact TaskLStMod.map_sv_assoc.
  exact TaskLStMod.map_perm_eql.
  exact TaskLStMod.map_flip_isRw.
  exact TaskLStMod.map_flip_sv.
  exact TaskLStMod.map_emp_get.
  exact TaskLStMod.map_eql.
  exact TaskLStMod.map_disjoint.
  exact TaskLStMod.map_get_unique.
  exact TaskLStMod.map_get_sig.
  exact TaskLStMod.map_get_sig'.
  exact TaskLStMod.map_get_set.
  exact TaskLStMod.map_get_set'.
  exact TaskLStMod.map_join_get_none.
  exact TaskLStMod.map_join_get_some.
  exact TaskLStMod.map_join_getp_some.
  exact TaskLStMod.map_set_emp.
  exact TaskLStMod.map_set_sig.
  exact TaskLStMod.map_join_set_none.
  exact TaskLStMod.map_join_set_perm.
  exact TaskLStMod.map_join_get_sig.
  exact TaskLStMod.map_join_get_sig_perm.
  exact TaskLStMod.map_merge_sem.
  intros; tryfalse.
  exact TaskLStMod.map_join_merge.
  exact TaskLStMod.map_merge_comm.
  intros; tryfalse.
  intros; tryfalse.
  exact TaskLStMod.map_minus_sem.
  intros; tryfalse.
  exact TaskLStMod.map_join_minus.
  exact TaskLStMod.map_del_sem.
Defined.

(*Definition isr register*)
Definition isr :=  hid -> bool.

Definition isrupd (r : isr) (x : hid) (b : bool):= 
      fun (y : hid) => if beq_nat x y then b else r y.


Fixpoint leb_nat (m : nat) : nat -> bool :=
  match m with
  | O => fun _ : nat => true
  | S m' => fun n : nat => match n with
                           | O  => false
                           | S n' =>  leb_nat  m' n'
                           end
  end.

Fixpoint highpri' (r : isr) (n : nat) : hid :=
  match n with
   | O => INUM
   | S n' => let y := highpri' r n' in 
                 if r n' then
                    if (leb_nat  n' y) then n' else y 
                 else y
 end.

Definition highpri (r:isr) := highpri' r INUM.

Definition higherint (r:isr) (i:hid) :=  forall i', i'<= i -> r i' = false. 

Definition empisr := fun (x : hid) => false. 

Definition  osstate  := (clientst * isr * ltaskstset).

Definition  smem  :=  (env * env * mem).

Definition  taskst := (smem *  isr * localst).

Definition get_smem (ts : taskst) :=
      match ts with
      (m, _, _) => m
     end.

Definition  lworld :=  (lprog * tasks * clientst * osstate * tid).


(**The High-level World**)

Definition funtype : Set := prod type typelist.

Definition api_code := vallist -> spec_code.

Definition osapi := prod api_code  funtype.
  
Definition osapispec :=  fid -> option osapi.

Definition int_code := spec_code.

Definition osintspec := hid -> option int_code.

Definition ossched := osabst -> tid -> Prop.

Definition osspec := (osapispec * osintspec * ossched).

Definition hprog := (progunit * osspec). 

Definition hworld := (hprog * tasks * clientst * osabst ). 

Definition isrdy (st:taskstatus):=
  match st with
    | rdy => True
    | _ => False
  end.

Definition eqenv (o o': taskst) : Prop :=
     match o, o' with
          | (G,E,M,isr,aux),(G',E',M',isr',aux') => G =G' /\ E = E' 
      end.

