Require Import language.
Require Import memory.
Require Import opsem.

(*expressions*)

Notation "'NULL'" := (enull) (at level 5) : code_scope.
Notation "′ I" := (econst32 (Int.repr I) ) (at level 5)  : code_scope.
Notation "x ′" := (evar x) (at level 5) : code_scope.
Notation "∗ A" := (ederef A) (at level 35)  : code_scope.
Notation " '&ₐ' A" := (eaddrof A) (at level 35) : code_scope.
Notation "'〈' T '〉' E " := (ecast E T) (at level 35)  : code_scope.
Notation "A '[' E ']' " := (earrayelem A E ) (at level 10)  : code_scope.
Notation "E '→' I" := (efield (ederef E) I) (at level 10)  : code_scope.
Notation "'∼'  X" := (eunop negation X) (at level 35)  : code_scope.
Notation "A '−' B" := (ebinop ominus A B) (at level 50, left associativity) : code_scope.
Notation "A '+ₑ' B" := (ebinop oplus A B) (at level 50, left associativity)  : code_scope.
Notation " '++' E" := (sassign E (ebinop oplus E (econst32 (Int.repr 1) ) ) ) (at level 50, left associativity)  : code_scope.
Notation "−− E" := (sassign E (ebinop ominus E (econst32 (Int.repr 1) ) ) ) (at level 50, left associativity)  : code_scope.
Notation "A '×' B" := (ebinop omulti A B) (at level 40, left associativity)  : code_scope.
Notation "A '÷' B" := (ebinop odiv A B) (at level 40, left associativity)  : code_scope.
Notation "A '≪' B" := (ebinop olshift A B) (at level 55, left associativity)  : code_scope.
Notation "A '≫' B" := (ebinop orshift A B) (at level 55, left associativity)  : code_scope.
Notation "A '&&ₑ' B" := (ebinop oand A B) (at level 67, left associativity)  : code_scope.
Notation " A '||ₑ' B " := (ebinop oor A B) (at level 68, left associativity)  : code_scope.
Notation "A '&ₑ' B" := (ebinop obitand A B) (at level 65, left associativity) : code_scope. 
Notation "A '|ₑ'  B" := (ebinop obitor A B) (at level 66, left associativity)  : code_scope.
Notation "A '==ₑ' B" := (ebinop oeq A B) (at level 61, left associativity)  : code_scope.
Notation "A '!=ₑ' B" := (eunop oppsite (ebinop oeq A B) ) 
                         (at level 61, left associativity)  : code_scope.
Notation "A '<ₑ' B" := (ebinop olt A B) (at level 57, B at next level, left associativity)  : code_scope.
Notation "A '>ₑ' B" := (ebinop olt B A) (at level 57, left associativity)  : code_scope. 
Notation "A '≥' B" := (ebinop oor (ebinop olt B A) (ebinop oeq A B) ) (at level 57, left associativity)  : code_scope.


(*statements*)
Notation "L '=ₑ' R" := (sassign L R) (at level 70)  : code_scope.
(*
Notation "x '=ₓ' R" :=  (sassign (evar x) R) (at level 70)  : code_scope.
*)
Notation "L '&=' R" := (sassign L (ebinop obitand L R) ) (at level 70, right associativity) : code_scope.
Notation "'IF' ( E ) { S1 } 'ELSE' { S2 }" := (sif E S1 S2) (at level 90,right associativity, format "'[v    ' 'IF' ( E ) '/' '['  S1  ']' '//' 'ELSE'  '[' S2   ']'  ']'" ) : code_scope.
Notation "'If' ( E ) { S }" := (sifthen E S) (at level 90, format 
 "'[v    ' 'If' ( E ) '/'  S   ']'") : code_scope.
Notation "'WHILE' ( E ) { S }" := (swhile E S) (at level 90, format  
"'[v    ' 'WHILE' ( E ) '/'  S  ']'")  : code_scope.
Notation "'RETURN'" := (sret) (at level 90) : code_scope.
Notation "'RETURN' E " := (srete E) (at level 90) : code_scope.
Notation "I '(­)'" := (scall I nil ) (at level 10) : code_scope .
Notation "I '(­'  e1 '­)' " := (scall I (e1::nil)%list)  (at level 10)  : code_scope.
Notation "I '(-' e1 , e2 '-)'" := (scall I (e1::e2::nil)%list)  (at level 10)  : code_scope.
Notation "I '(­' e1 , e2 , e3 '­)'" := (scall I (e1::e2::e3::nil)%list)  (at level 10)  : code_scope.
Notation "I '(­' e1 , e2 , e3 , e4 '­)'" := (scall I (e1::e2::e3::e4::nil)%list)  (at level 10)  : code_scope.
Notation "I '(­' e1 , e2 , e3 , e4 , e5 '­)'" := (scall I (e1::e2::e3::e4::e5::nil)%list)  (at level 10)  : code_scope.
Notation "I '(­' e1 , e2 , e3 , e4 , e5 , e6 '­)'" := 
  (scall I (e1::e2::e3::e4::e5::e6::nil)%list)  (at level 10)  : code_scope.
Notation "x '=ᶠ' I '(·)' " := (scalle x I nil) (at level 10) : code_scope.
Notation "x '=ᶠ' I '(·' e1 '·)' " := (scalle x I (e1::nil)%list) (at level 10) : code_scope.
Notation "x '=ᶠ' I '(·' e1 , e2 '·)' " := (scalle x I (e1::e2::nil)%list) (at level 10) : code_scope.
Notation "x '=ᶠ' I '(·' e1 , e2 , e3 '·)' " := (scalle x I (e1::e2::e3::nil)%list) (at level 10) : code_scope.
Notation "x '=ᶠ' I '(·' e1 , e2 , e3 , e4  '·)' " := (scalle x I (e1::e2::e3::e4::nil)%list) (at level 10) : code_scope.
Notation "x '=ᶠ' I '(·' e1 , e2 , e3 , e4 , e5  '·)' " := (scalle x I (e1::e2::e3::e4::e5::nil)%list) (at level 10) : code_scope.
Notation "x '=ᶠ' I '(·' e1 , e2 , e3 , e4 , e5 , e6  '·)' " := (scalle x I (e1::e2::e3::e4:: e5 :: e6 nil)%list) (at level 10) : code_scope.
Notation "S1 ';ₛ' S2" := (sseq S1 S2) (at level 97, right associativity, format"S1 ';ₛ' '//' S2") : code_scope.
Notation "'printf' E" := (sprint E) (at level 90) : code_scope.
Notation "'IRET'" := (sprim exint) (at level 90): code_scope .
Notation "'SWITCH'" := (sprim (switch OSTCBHighRdy) ) (at level 90) : code_scope.
Notation "'EOI' ( I )" := (sprim (eoi (Int.repr I) ) ) (at level 90) : code_scope.
Notation "'EXIT_CRITICAL'" := (sprim excrit) (at level 90): code_scope .
Notation "'ENTER_CRITICAL'" := (sprim encrit) (at level 90) : code_scope.
Notation "'CLI'" := (sprim cli) (at level 90) : code_scope.
Notation "'STI'" := (sprim sti) (at level 90): code_scope .
Notation " x '<-' 'CHECKIS' " := (sprim (checkis x)) (at level 90): code_scope .

(* types *)
Notation "'Void'" := (Tvoid) (at level 5) : code_scope .
Notation "'Int8u'" := (Tint8) (at level 5) : code_scope .
Notation "'Int16u'" := (Tint16) (at level 5) : code_scope.
Notation "'Int32'" := (Tint32) (at level 5) : code_scope .
Notation "'Int32u'" := (Tint32) (at level 5) : code_scope.
Notation "'Ptr'" := (Tptr) (at level 5) : code_scope.
Notation "T ∗" := (Tptr T) (at level 5): code_scope .
Notation "'STRUCT' id '­{' dl '}­'" := (Tstruct id dl) (at level 5): code_scope .
Notation " 'STRUCT' id ⋆ " := (Tcom_ptr id) (at level 5): code_scope .

(* declaration list, we support max length 15*)
(*
Notation "I ：： T ；； R" := (dcons I T R) (at level 90, right associativity) : code_scope .
*)
Notation "'⌞'  '⌟'" := (dnil)(at level 5, right associativity) : code_scope .
Notation "'⌞' I @ T '⌟'" := (dcons I T dnil)(at level 5, right associativity) : code_scope .
Notation "'⌞' I1 @ T1 ';' I2 @ T2 '⌟' " := 
  (dcons I1 T1 (dcons I2 T2 dnil)) (at level 5, right associativity) : code_scope .
Notation "'⌞' I1 @ T1 ';'  I2 @ T2  ';'  I3 @ T3 '⌟' " := 
  (dcons I1 T1 (dcons I2 T2 (dcons I3 T3 dnil))) (at level 5, right associativity) : code_scope .

Notation "'⌞' I1 @ T1 ';'  I2 @ T2  ';'  I3 @ T3 ';' I4 @ T4 '⌟' " := 
 (dcons I1 T1 (dcons I2 T2 (dcons I3 T3 (dcons I4 T4 dnil))))
    (at level 5, right associativity) : code_scope .


Notation "'⌞' I1 @ T1 ';'  I2 @ T2  ';'  I3 @ T3 ';' I4 @ T4 ';' I5 @ T5 '⌟' " := 
(dcons I1 T1 (dcons I2 T2 (dcons I3 T3 (dcons I4 T4 (dcons I5 T5 dnil)))))
    (at level 5, right associativity) : code_scope .

Notation "'⌞' I1 @ T1 ';'  I2 @ T2  ';'  I3 @ T3 ';' I4 @ T4 ';'  I5 @ T5 ';'  I6 @ T6 '⌟' " := 
(dcons I1 T1 (dcons I2 T2 (dcons I3 T3 (dcons I4 T4
 (dcons I5 T5 (dcons I6 T6 dnil))))))
    (at level 5, right associativity) : code_scope .

Notation "'⌞' I1 @ T1 ';'  I2 @ T2  ';'  I3 @ T3 ';' I4 @ T4 ';'  I5 @ T5 ';'  I6 @ T6 ; I7 @ T7 '⌟' " := 
(dcons I1 T1 (dcons I2 T2 (dcons I3 T3 (dcons I4 T4 (dcons I5 T5
 (dcons I6 T6 (dcons I7 T7 dnil)))))))
    (at level 5, right associativity) : code_scope .

Notation "'⌞' I1 @ T1 ';'  I2 @ T2  ';'  I3 @ T3 ';' I4 @ T4 ';'  I5 @ T5 ';'  I6 @ T6 ';' I7 @ T7 ';' I8 @ T8 '⌟' " := 
(dcons I1 T1 (dcons I2 T2 (dcons I3 T3 (dcons I4 T4 (dcons I5 T5 (dcons I6 T6
 (dcons I7 T7 (dcons I8 T8 dnil))))))))
    (at level 5, right associativity) : code_scope .


Notation "'⌞' I1 @ T1 ';'  I2 @ T2  ';'  I3 @ T3 ';' I4 @ T4 ';'  I5 @ T5 ';'  I6 @ T6 ';' I7 @ T7 ';' I8 @ T8 ';' I9 @ T9 '⌟' " := 
(dcons I1 T1 (dcons I2 T2 (dcons I3 T3 (dcons I4 T4 (dcons I5 T5 (dcons I6 T6 (dcons I7 T7 (dcons I8 T8 (dcons I9 T9 dnil)))))))))
    (at level 5, right associativity) : code_scope .

Notation "'⌞' I1 @ T1 ';'  I2 @ T2  ';'  I3 @ T3 ';' I4 @ T4 ';'  I5 @ T5 ';'  I6 @ T6 ';' I7 @ T7 ';' I8 @ T8 ';' I9 @ T9 ';' I10 @ T10 '⌟' " := 
(dcons I1 T1 (dcons I2 T2 (dcons I3 T3 (dcons I4 T4 (dcons I5 T5 (dcons I6 T6 (dcons I7 T7 (dcons I8 T8 (dcons I9 T9 (dcons I10 T10 dnil))))))))))
    (at level 5, right associativity) : code_scope .


Notation "'⌞' I1 @ T1 ';'  I2 @ T2  ';'  I3 @ T3 ';' I4 @ T4 ';'  I5 @ T5 ';'  I6 @ T6 ';' I7 @ T7 ';' I8 @ T8 ';' I9 @ T9 ';' I10 @ T10 ';' I11 @ T11 '⌟' " := (dcons I1 T1 (dcons I2 T2 (dcons I3 T3 (dcons I4 T4 (dcons I5 T5 (dcons I6 T6 (dcons I7 T7 (dcons I8 T8 (dcons I9 T9 (dcons I10 T10 (dcons I11 T11 dnil)))))))))))
    (at level 5, right associativity) : code_scope .

Notation "'⌞' I1 @ T1 ';'  I2 @ T2  ';'  I3 @ T3 ';' I4 @ T4 ';'  I5 @ T5 ';'  I6 @ T6 ';' I7 @ T7 ';' I8 @ T8 ';' I9 @ T9 ';' I10 @ T10 ';' I11 @ T11 ';' I12 @ T12 '⌟' " := (dcons I1 T1 (dcons I2 T2 (dcons I3 T3 (dcons I4 T4 (dcons I5 T5 (dcons I6 T6 (dcons I7 T7 (dcons I8 T8 (dcons I9 T9 (dcons I10 T10 (dcons I11 T11 (dcons I12 T12 dnil))))))))))))
    (at level 5, right associativity) : code_scope .



(* others *)
Notation "'CFalse'" := (econst32 Int.zero) (at level 5) : code_scope .
Notation "'CTrue'" := (econst32 Int.one) (at level 5) : code_scope .
Notation "'Skip'" := (sskip None) (at level 5) : code_scope .

Notation "∘ M" := (Coqlib.nat_of_Z M) (at level 5): code_scope . 




Definition cfun := (ident * function)%type.


Fixpoint  convert_cfuns (ls : list cfun)  : fid -> option function :=
  match ls with
    | nil => fun _ => None
    | (x :: ls')%list => match x with
                           | (id, imp) => 
                             fun (id' : fid) => 
                               if Zbool.Zeq_bool id id' then Some imp
                               else (convert_cfuns ls') id'
                         end
  end.    


Notation  " t '·'  fid '·(' arglist ')·' '·{' lvars ';'  body '}·' "
:= (fid, (t, arglist, lvars, body))  (at level 90): code_scope.

(*
Definition getFunType fid : type :=
    match os_api fid with
    | Some (t, _ , _ , _) => t
    | None => Tnull
    end.

Definition getFunArgs fid : decllist :=
    match os_api fid with
    | Some (_, args , _ , _) => args
    | None => dnil
    end.

Definition getFunDecls fid : decllist :=
    match os_api fid with
    | Some (_ , _ , decls , _) => decls
    | None => dnil
    end.

Definition getFunBody fid : stmts :=
    match os_api fid with
    | Some (_ , _ , _ , body) => body
    | None => sskip None
    end.
*)
