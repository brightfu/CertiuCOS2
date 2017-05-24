Require Import include_frm.
Require Import seplog_tactics.
Require Import sep_combine_lemmas.
Require Import meta_find.
Local Open Scope code_scope.


(* extension for handle(combine/ cancel) -r-> *)
Ltac is_roPV4l_asrt H:=
  match H with
    | PV ?l @ ?t |-r-> _ => l
    | _ => constr:0%nat
  end.


Ltac is_roLV4l_asrt H:=
  match H with
    | LV ?l @ ?t |-r-> _ => l
    | _ => constr:0%nat
  end.

Ltac is_roGV4l_asrt H:=
  match H with
    | GV ?l @ ?t |-r-> _ => l
    | _ => constr:0%nat
  end.

Ltac find_roPV4l_and_lift_in_H H l := meta_find_and_lift_in_H is_roPV4l_asrt l H.
Ltac find_roPV4l_and_lift_in_H_from_n n H l := meta_find_and_lift_in_H_from_n n is_roPV4l_asrt l H.

Ltac find_roPV4l_and_lift_in_goal l := meta_find_and_lift_in_goal is_roPV4l_asrt l.
Ltac find_roPV4l_and_lift_in_goal_from_n n l := meta_find_and_lift_in_goal_from_n n is_roPV4l_asrt l .

Ltac find_roLV4l_and_lift_in_H H l := meta_find_and_lift_in_H is_roLV4l_asrt l H.
Ltac find_roLV4l_and_lift_in_H_from_n n H l := meta_find_and_lift_in_H_from_n n is_roLV4l_asrt l H.

Ltac find_roLV4l_and_lift_in_goal l := meta_find_and_lift_in_goal is_roLV4l_asrt l.
Ltac find_roLV4l_and_lift_in_goal_from_n n l := meta_find_and_lift_in_goal_from_n n is_roLV4l_asrt l .

Ltac find_roGV4l_and_lift_in_H H l := meta_find_and_lift_in_H is_roGV4l_asrt l H.
Ltac find_roGV4l_and_lift_in_H_from_n n H l := meta_find_and_lift_in_H_from_n n is_roGV4l_asrt l H.

Ltac find_roGV4l_and_lift_in_goal l := meta_find_and_lift_in_goal is_roGV4l_asrt l.
Ltac find_roGV4l_and_lift_in_goal_from_n n l := meta_find_and_lift_in_goal_from_n n is_roGV4l_asrt l .

Ltac encode_val_eq_solver H := idtac.

Ltac sep_combine_lro_in_H H l:=
  let encode_val_eq := fresh in
  find_roLV4l_and_lift_in_H H l; find_roLV4l_and_lift_in_H_from_n 1%nat H l; 
  first [lets encode_val_eq : H ; eapply LV_combine_ro_frm_p1 in H ; eapply LV_combine_ro_frm_p2 in encode_val_eq; encode_val_eq_solver encode_val_eq
        | lets encode_val_eq : H ; eapply LV_combine_ro_p1 in H ; eapply LV_combine_ro_p2 in encode_val_eq  ; encode_val_eq_solver encode_val_eq  ].

Ltac sep_combine_gro_in_H H l:=
  let encode_val_eq := fresh in
  find_roGV4l_and_lift_in_H H l; find_roGV4l_and_lift_in_H_from_n 1%nat H l; 
  first [lets encode_val_eq : H ; eapply GV_combine_ro_frm_p1 in H ; eapply GV_combine_ro_frm_p2 in encode_val_eq; encode_val_eq_solver encode_val_eq
        | lets encode_val_eq : H ; eapply GV_combine_ro_p1 in H ; eapply GV_combine_ro_p2 in encode_val_eq; encode_val_eq_solver encode_val_eq].

  (* find_roGV4l_and_lift_in_H H l; find_roGV4l_and_lift_in_H_from_n 1%nat H l;
   * first [eapply GV_combine_ro_frm in H | eapply GV_combine_ro in H]. *)

Ltac sep_combine_pro_in_H H l:=
  let encode_val_eq := fresh in
  find_roPV4l_and_lift_in_H H l; find_roPV4l_and_lift_in_H_from_n 1%nat H l; 
  first [lets encode_val_eq : H ; eapply PV_combine_ro_frm_p1 in H ; eapply PV_combine_ro_frm_p2 in encode_val_eq; encode_val_eq_solver encode_val_eq
        | lets encode_val_eq : H ; eapply PV_combine_ro_p1 in H ; eapply PV_combine_ro_p2 in encode_val_eq; encode_val_eq_solver encode_val_eq].

  (* find_roPV4l_and_lift_in_H H l; find_roPV4l_and_lift_in_H_from_n 1%nat H l;
   * first [eapply PV_combine_ro_frm in H | eapply PV_combine_ro in H]. *)

Ltac sep_combine_ro_in_H H l :=
  first [sep_combine_lro_in_H H l | sep_combine_gro_in_H H l | sep_combine_pro_in_H H l].

Ltac sep_combine_lro_in_goal l:=
  find_roLV4l_and_lift_in_goal l; find_roLV4l_and_lift_in_goal_from_n 1%nat l;
   first [eapply LV_combine_ro'_frm | eapply LV_combine_ro' ]; auto. 

Ltac sep_combine_gro_in_goal l:=
  find_roGV4l_and_lift_in_goal l; find_roGV4l_and_lift_in_goal_from_n 1%nat l;
   first [eapply GV_combine_ro'_frm  | eapply GV_combine_ro' ]; auto. 

Ltac sep_combine_pro_in_goal l:=
  find_roPV4l_and_lift_in_goal l; find_roPV4l_and_lift_in_goal_from_n 1%nat l;
   first [eapply PV_combine_ro'_frm  | eapply PV_combine_ro' ]; auto. 

Ltac sep_combine_ro_in_goal l :=
  first [sep_combine_lro_in_goal l | sep_combine_gro_in_goal l | sep_combine_pro_in_goal l].

Ltac change_val_in_goal :=
  first [ eapply LV_change_val_frm | eapply GV_change_val_frm | eapply PV_change_val_frm
          |eapply LV_change_val    | eapply GV_change_val     | eapply PV_change_val].

Ltac change_val_in_H H :=
  first [ eapply LV_change_val_frm in H| eapply GV_change_val_frm in H | eapply PV_change_val_frm in H 
          |eapply LV_change_val in H | eapply GV_change_val in H     | eapply PV_change_val in H ].

Ltac separate_LV_in_H H :=
  first [ eapply LV_separate_rw in H | eapply LV_separate_rw_frm in H ].

Ltac separate_GV_in_H H :=
  first [ eapply GV_separate_rw in H | eapply GV_separate_rw_frm in H ].

Ltac separate_PV_in_H H :=
  first [ eapply PV_separate_rw in H | eapply PV_separate_rw_frm in H ].

Ltac separate_val_in_H H := first [separate_LV_in_H H| separate_GV_in_H H | separate_PV_in_H H].

Ltac separate_LV_in_goal :=
  first [ eapply LV_combine_ro_p1 | eapply LV_combine_ro_frm_p1 ].

Ltac separate_GV_in_goal :=
  first [ eapply GV_combine_ro_p1  | eapply GV_combine_ro_frm_p1  ].

Ltac separate_PV_in_goal :=
  first [ eapply GV_combine_ro_p1  | eapply GV_combine_ro_frm_p1  ].

Ltac separate_val_in_goal := first [separate_LV_in_goal | separate_GV_in_goal | separate_PV_in_goal].


Tactic Notation "sep" "combine" constr(l) := sep_combine_ro_in_goal l.
Tactic Notation "sep" "combine" constr(l) "in" hyp(H) := sep_combine_ro_in_H H l.
Tactic Notation "sep" "change" "val" := change_val_in_goal.
Tactic Notation "sep" "change" "val" "in" hyp(H) := change_val_in_H H.
Tactic Notation "sep" "separate" "in" hyp(H) := separate_val_in_H H.
Tactic Notation "sep" "separate" := separate_val_in_goal .
