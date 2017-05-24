Require Import include_frm.
Require Import sep_auto.
Require Import derived_rules.
Require Import symbolic_execution.

Ltac hoare_if :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {| _ , _, _, _, _, _ |}|-?ct {{ _ }} (sif _ _ _) {{ _ }} =>
      eapply if_rule2';
        [ symbolic execution
        | idtac 
        | idtac ]
    | |- {| _ , _, _, _, _, _ |}|-?ct {{ _ }} (sifthen _ _) {{ _ }} =>
      eapply ift_rule'';
        [ symbolic execution
        | idtac ]
  end.
