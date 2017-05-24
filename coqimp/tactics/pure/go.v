Require Import include_frm.
Require Import struct_type_match_solver.
Require Import frmaop_sol.

Lemma tcbmod_joinsig_get :
  forall x y mqls mqls',
    TcbMod.joinsig x y mqls mqls' ->
    TcbMod.get mqls' x = Some y.
Proof.
  intros.
  eapply TcbMod.join_get_l; eauto.
  apply TcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
Qed.

Lemma ecbmod_joinsig_get :
  forall x y mqls mqls',
    EcbMod.joinsig x y mqls mqls' ->
    EcbMod.get mqls' x = Some y.
Proof.
  intros.
  eapply EcbMod.join_get_l; eauto.
  apply EcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
Qed.

Ltac ecbget_joins_sig_solver' :=
  eauto 1;
  let aaa:= fresh in 
  match goal with
    | H : EcbMod.join (EcbMod.sig ?key ?val) ?mb ?mab |- EcbMod.get ?a ?key = Some _ =>
      lets aaa: ecbmod_joinsig_get H; clear H
    (*| H : EcbMod.get ?a ?key = Some _ |- EcbMod.get ?a ?key = Some _ =>
        eauto*)
    | H : EcbMod.get ?ma ?key = Some _ |- EcbMod.get ?a ?key = Some _ =>
      match goal with
        | H' : EcbMod.join ma ?mb ?mab |- _ =>
          lets aaa: EcbMod.join_get_get_l H' H; clear H
        | H' : EcbMod.join ?mb ma ?mab |- _ =>
          lets aaa: EcbMod.join_get_get_r H' H; clear H
      end
  end; ecbget_joins_sig_solver'.


Ltac ecbget_joins_sig_solver :=
  unfold EcbMod.joinsig in *; ecbget_joins_sig_solver'.

Ltac tcbget_joins_sig_solver' :=
  eauto 1; 
  let aaa:= fresh in 
  match goal with
    | H : TcbMod.join (TcbMod.sig ?key ?val) ?mb ?mab |- TcbMod.get ?a ?key = Some _ =>
      lets aaa: tcbmod_joinsig_get H; clear H
    | H : TcbMod.get ?ma ?key = Some _ |- TcbMod.get ?a ?key = Some _ =>
      match goal with
        | H' : TcbMod.join ma ?mb ?mab |- _ => lets aaa: TcbMod.join_get_get_l H' H; clear H
        | H' : TcbMod.join ?mb ma ?mab |- _ => lets aaa: TcbMod.join_get_get_r H' H; clear H
      end
  end; tcbget_joins_sig_solver'.

Ltac tcbget_joins_sig_solver :=
  unfold TcbMod.joinsig in *;  tcbget_joins_sig_solver'.

Ltac joinsig_solver :=
  match goal with
    | |- EcbMod.get _ _ = Some _ => ecbget_joins_sig_solver
    | |- TcbMod.get _ _ = Some _ => tcbget_joins_sig_solver
  end.


Ltac go :=
  match goal with
    | |- struct_type_vallist_match _ _ => struct_type_match_solver
    | |- GoodFrm _ => clear; (good_frm_sovler || auto)
    | |- can_change_aop _ => clear; can_change_aop_solver 
    | |- tidspec.beq _ _ = true =>apply CltEnvMod.beq_refl
    | |- tidspec.beq _ _ = false => apply tidspec.neq_beq_false; auto
    | |- EcbMod.get _ _ = Some _       => ecbget_joins_sig_solver
    | |- TcbMod.get _ _ = Some _       => tcbget_joins_sig_solver
    | |- _ /\ _                        => split; go
    | |- _ = _                         => try unfolds; simpl; auto 1
    | |- _                             => eauto 1
  end.

