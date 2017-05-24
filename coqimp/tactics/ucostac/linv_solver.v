Require Import include_frm.
Require Import sep_auto.
Require Import sep_lemmas_ext.
Require Import os_inv. (* just for disj_split ? *)
Ltac disj_asrt_destruct H :=
  let H' := fresh in 
  match type of H with
    | ?s |= ( _ \\// _) ** _ => rewrite disj_split in H; disj_asrt_destruct H
    | ?s |= _ \\// _ =>apply DisjPropE in H; destruct H; disj_asrt_destruct H
    | _ => idtac
  end.

Ltac linv_solver :=
  repeat intro;
  match goal with
    | H: ?s |= ?a |- ?s |= ?a' =>
      sep normal in H; sep destruct H; disj_asrt_destruct H; sep destruct H; sep eexists; sep cancel p_local; simpl; auto 1
  end.


Tactic Notation "linv" "solver" := linv_solver.
