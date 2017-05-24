Require Import include_frm.
Require Import int_auto.
Require Import sep_auto.
Require Import math_sol.
Require Import frmaop_sol.
Require Import code_notations.
Require Import pure_lib.
Require Import tv_match.

Open Scope code_scope.
Open Scope Z_scope.


Ltac pauto' := 
  match goal with
  | H : _ |- {| _ , _ , _ , _, _, _ |}|-_ {{ _ }} _ {{ _ }} => idtac
  | H : _ |- _ |= _ => idtac
  | H : false = (Int.unsigned _   <=? 65535)  |- _ => 
    erewrite Int_i2_i_1 in H; eauto; inverts H
  | H : (Int.unsigned _  <=? 65535) = false |- _ =>  
    erewrite Int_i2_i_1 in H; eauto; inverts H
  | H: _ |- ?x = ?x => reflexivity
  | H:?x <= ?y |- _ => apply Zle_imp_le_bool in H; pauto'
  | H: context [Byte.max_unsigned] |- _ =>
    rewrite byte_max_unsigned_val in H; pauto'
  | H:_ |- context [Byte.max_unsigned] =>
    rewrite byte_max_unsigned_val; pauto'
  | H: context [Int16.max_unsigned] |- _ =>
    rewrite int16_max_unsigned_val in H; pauto'
  | H:_ |- context [Int16.max_unsigned] =>
    rewrite int16_max_unsigned_val; pauto'
  | H: context [Int.max_unsigned] |- _ =>
    rewrite max_unsigned_val in H; pauto'
  | H:_ |- context [Int.max_unsigned] =>
    rewrite max_unsigned_val ; pauto'
  | H:  context [if ?x then _ else _] |- _ =>
    let Hr := fresh in remember x as Hr; destruct Hr; pauto'   
  | H:_ |- _ /\ _ => splits; pauto'
  | H:_ |- struct_type_vallist_match _ _ =>  simpl;splits;pauto'
  | H:_ |- rule_type_val_match _ _ = true => simpl rule_type_val_match; pauto'
  | |- can_change_aop _ => can_change_aop_solver || auto
  | |- GoodFrm _ => good_frm_sovler || auto
  | H:_   |-  context [if ?x then _ else _]  => 
           let Hr := fresh in
            remember x as Hr;  destruct Hr ; pauto'
  | H: _ |- ?t (_ :: _) = Some _ => try unfold t; simpl ; auto  
  | H: _ |- _ =>   auto || eauto || auto with pauto_lemmas 
                 || eauto with pauto_lemmas || intuition eauto 
  end.

Close Scope Z_scope.
Close Scope code_scope.

