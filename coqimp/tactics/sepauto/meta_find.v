Require Import include_frm.
Require Import seplog_tactics.
Require Import sep_combine_lemmas.
Local Open Scope code_scope.


(* meta find *)
Inductive find_tmp_result :=
| tmp_res_Y :find_tmp_result
| tmp_res_N: find_tmp_result
.

Ltac meta_find'_Impl n ptrn_f ptrn H:=
  match H with 
    | ?A ** ?B =>
      match meta_find'_Impl n ptrn_f ptrn A with
        | (tmp_res_Y, ?a, ?AA) =>
          constr:(tmp_res_Y, a, AA)
        | (tmp_res_N, ?a)  =>
          meta_find'_Impl a ptrn_f ptrn B 
          (* match meta_find' ptrn_f ptrn B with
           *   | (tmp_res_Y, ?b, ?BB) =>
           *     constr:(tmp_res_Y, (a + b)%nat, BB)
           *   | (tmp_res_N, ?b) =>
           *     constr:(tmp_res_N, (a + b)%nat)
           * end *)
      end
    | ?A => match (ptrn_f A) with
              | ptrn =>
                constr:(tmp_res_Y, (1 + n)%nat, A)
              | _ =>
                constr:(tmp_res_N, (1 + n)%nat)
            end
  end.

Inductive find_result :=
| fres_Y : nat -> asrt -> find_result
| fres_N : find_result.


Ltac meta_find' n ptrn_f ptrn H :=
  match meta_find'_Impl n ptrn_f ptrn H with
    | (tmp_res_Y, ?n, ?A) =>
      let n' := eval compute in n in constr:(fres_Y n' A)
    | (tmp_res_N, ?n) =>
      constr:(fres_N)
  end.



Ltac meta_find ptrn_f ptrn H := meta_find' 0%nat ptrn_f ptrn H.

Ltac meta_find_in_H ptrn_f ptrn H :=
  match type of H with
    | ?s |= ?P =>
      meta_find ptrn_f ptrn P
    |_ => fail
  end.

Ltac meta_find_and_lift_in_H ptrn_f ptrn H:=
  match meta_find_in_H ptrn_f ptrn H with
    | fres_Y ?n ?A => sep lift n in H
    | _ => fail
  end.

Ltac meta_find_from_nth'Impl n ptrn_f ptrn H dupn:=
  match n with
    | O =>
      meta_find' dupn ptrn_f ptrn H
    | S ?n' =>
      match H with 
        | ?A ** ?B =>
          meta_find_from_nth'Impl n' ptrn_f ptrn B dupn
        | ?A => fres_N
      end
  end.

Ltac meta_find_from_nth' n ptrn_f ptrn H := meta_find_from_nth'Impl n ptrn_f ptrn H n.

Ltac meta_find_from_nth n ptrn_f ptrn H := meta_find_from_nth' n ptrn_f ptrn H.
  (* match meta_find_from_nth' n ptrn_f ptrn H with *)
    (* | fres_N => fres_N *)
    (* | fres_Y ?res' ?a => let res := eval compute in (res' + n) in constr:(fres_Y res a) *)
  (* end. *)

Ltac meta_find_in_H_from_nth n ptrn_f ptrn H:=
  match type of H with
    | ?s |= ?P => 
      meta_find_from_nth n ptrn_f ptrn P
    |_ => fail
  end.


Ltac meta_find_and_lift_in_H_from_n n ptrn_f ptrn H:=
  match meta_find_in_H_from_nth n ptrn_f ptrn H with
    | fres_Y ?nn ?A => sep lift nn in H
    | _ => fail "cannot find such an asrt"
  end.

Ltac meta_find_in_goal ptrn_f ptrn :=
  match goal with
    | |- ?s |= ?P =>
      meta_find ptrn_f ptrn P
    |_ => fail
  end.

Ltac meta_find_and_lift_in_goal ptrn_f ptrn :=
  match meta_find_in_goal ptrn_f ptrn with
    | fres_Y ?n ?A => sep lift n 
    | _ => fail
  end.

Ltac meta_find_in_goal_from_nth n ptrn_f ptrn :=
  match goal with
    | |- ?s |= ?P => 
      meta_find_from_nth n ptrn_f ptrn P
    |_ => fail
  end.


Ltac meta_find_and_lift_in_goal_from_n n ptrn_f ptrn :=
  match meta_find_in_goal_from_nth n ptrn_f ptrn with
    | fres_Y ?nn ?A => sep lift nn 
    | _ => fail "cannot find such an asrt"
  end.

(* end of meta find*)

