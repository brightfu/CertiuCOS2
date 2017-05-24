Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

Notation " hid '↝' '{' stmts '}' " := (hid%nat, stmts)  (at level 90): code_scope.

Definition OSTickISR_impl  :=
 OSTickISR ↝ 
 {

     EOI(0);ₛ
     OSTimeTick(­);ₛ
     OSIntExit(­);ₛ
     IRET
 }.


Definition OSToyISR_impl  :=
 OSToyISR ↝ 
 {

     ++OSIntToyCount′;ₛ
     STI;ₛ 
     EOI(1);ₛ     
     OSIntExit(­);ₛ
     IRET
 }.

Definition ifun := (nat * stmts).


Fixpoint  convert_ifuns (ls : list ifun)  : hid -> option stmts :=
  match ls with
    | nil => fun _ => None
    | (x :: ls')%list => 
      match x with
        | (id, imp) => 
          fun (id' : hid) => 
            if EqNat.beq_nat id id' then Some imp
            else (convert_ifuns ls') id'
      end
  end. 
    
Close Scope code_scope.
