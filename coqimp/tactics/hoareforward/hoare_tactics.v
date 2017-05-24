Require Import Coq.Bool.IfProp.
Require Import Coq.Logic.Classical_Prop.
Require Import Recdef.
Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import include_frm.
Require Import sep_auto.
Require Import hoare_conseq.
Require Import derived_rules.
Require Import hoare_assign.
Require Import hoare_if.
Require Import hoare_ret.
Require Import hoare_call.
Require Import cancel_abs.
Set Implicit Arguments.                                                                                                                                                                                                              
(* function call *)



Ltac hoare_split_pure n :=
  hoare lift n pre;
  apply pure_split_rule'; intro.

Ltac hoare_intro_pure n :=
  hoare lift n pre;
  apply pure_intro_rule'; intro;
  hoare lower 1%nat pre.

Ltac hoare_cut_pure x :=
  apply prop_elim_rule1 with x;
  [ repeat (apply pure_ex_intro_rule; first [ apply ex_intro_rule' | apply ex_intro_rule ]; intro)
  | intros; idtac ].

Ltac hoare_split_pure_all' :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
      match find_apure P with
        | some ?n => hoare_split_pure n; hoare_split_pure_all'
        | none _ => idtac
      end
  end.

Ltac hoare_ex_intro :=
  repeat match goal with
         | |- {| _, _, _, _, _, _ |} |- _  {{ EX _, _ }} _ {{ _ }} =>
           first [ apply ex_intro_rule' ; intros
                 | apply ex_intro_rule; intros ]
         end.


Ltac hoare_split_pure_all :=
  hoare normal pre; hoare_ex_intro; hoare_split_pure_all'.


Ltac hoare_assert_pure x :=
  apply prop_elim_rule2 with x;
  [ intros; idtac
  | repeat (apply pure_ex_intro_rule; first [ apply ex_intro_rule' | apply ex_intro_rule ]; intro) ].

(*
Ltac move_aop_last :=
  match goal with
    | H:_ |- {|_ , _, _, _|}|- {{?p}}_ {{_}} =>
      match find_aop p with
        | some ?n => hoare lower n%nat pre
        | none => fail "No aop"
      end
    | _ => idtac
  end.
*)

Ltac array_leneq :=
  match goal with
  | H:_ |- {|_ , _, _, _, _, _|}|- _ {{?p}}_ {{_}} =>
      match p with
        | Aarray _ (Tarray ?t ?n) ?vl ** ?A =>
           first [ let x:= fresh in 
                   assert (length vl = n) as x by auto;
                     clear x  
                 | hoare_assert_pure (length vl = n);
                   [ eapply  array_length_intro; eauto
                   | hoare_split_pure_all]]
        |_  => idtac 
      end; hoare lower 1%nat pre
  end.

Ltac array_leneq_n n :=
  match n with
    | S ?n' => array_leneq;  array_leneq_n n'
    | _ => idtac
  end.

Ltac array_leneq_intro :=
  match goal with
    | H:_ |- {|_ , _, _, _, _, _|}|-_ {{?p}}_ {{_}} =>
      let lg := asrt_to_list p in
      let n:= (eval compute in (length lg)) in  array_leneq_n n
  end.


Ltac unfold_funpost :=
  match goal with
    | H:_
      |- {|_ , _, _, _, _, _|}|- _ {{?p}}_ {{_}} =>
      match p with
        | EX _,  POST  [?t, _, _ ,_ ,_] ** _=> 
          unfold getasrt;unfold t;
          match goal with
            | H:_
              |- {|_ , _, _, _, _, _|}|-_ {{?p}}_ {{_}} =>
              match p with
                | EX _,  (?t _ _ _ _) ** _=> 
                  unfold t
              end
          end
      end
  end.

Ltac elim_nil :=
  match goal with
    | H :  (length ?v > 0)%nat |- _ => destruct v; simpl in H;
                                        [false;  inverts H  | idtac]
    | H :  nth_val 0 ?v  = Some _ |- _ => destruct v; 
                                         [simpl in H ; false;  inverts H  |  idtac]
    | _ => idtac                                       
   end.

Tactic Notation "elim" "nil" := elim_nil.


Ltac find_aisr' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_aisr' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_aisr' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | Aisr _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_aisr Hp :=
  let y := find_aisr' Hp in
  eval compute in y.

Ltac find_aie' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_aie' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_aie' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | Aie _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_aie Hp :=
  let y := find_aie' Hp in
  eval compute in y.

Ltac find_ais' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_ais' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_ais' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | Ais _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_ais Hp :=
  let y := find_ais' Hp in
  eval compute in y.

Ltac find_acs' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_acs' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_acs' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | Acs _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_acs Hp :=
  let y := find_acs' Hp in
  eval compute in y.


(*
Ltac retpost_funs :=
  try (apply retpost_qptrsearch)(*;try (apply retpost_eventrdy);try (apply retpost_eventwait)*).
 *)

Ltac find_pre' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_pre' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_pre' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | getasrt _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_pre Hp :=
  let y := find_pre' Hp in
  eval compute in y.


    
 (* abstract consequence rule *)


Ltac hoare_abscsq :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
      match find_aop P with
        | none _ =>
          idtac 1 "no absop in the pre-condition"; fail 1
        | some ?a =>
          match find_absdata P absecblsid with
            | none _ =>
              idtac;
                hoare lift a pre;eapply abscsq_rule'
            | some ?b =>
              match find_absdata P abstcblsid with
                | none _ => 
                  idtac 3 ; fail 3
                | some ?c =>
              (*    match find_absdata P tmsglsid with
                    | none _ => 
                      idtac 4 "no HTmsg in the pre-condition"; fail 4
                    | some ?d =>
               *)       match find_absdata P ostmid with
                        | none _ =>
                          idtac 4 "no HTime in the pre-condition"; fail 4
                        | some ?e =>
                          match find_absdata P curtid with
                            | none _ =>
                              idtac 5 "no HCurTCB in the pre-condition"; fail 5
                            | some ?f =>
                                      hoare lifts (a::b::c::e::f::nil) pre;
                                        eapply abscsq_rule'
                              end
                          end
                      end
              end
          end
  end.

Ltac hoare_abscsq' :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ ?P }} =>
      match find_aop P with
        | none _ =>
          idtac 1 "no absop in the pre-condition"; fail 1
        | some ?a =>
          match find_absdata P absecblsid with
            | none _ =>
              idtac;
                hoare lift a post;eapply abscsq_rule''
            | some ?b =>
              match find_absdata P abstcblsid with
                | none _ => 
                  idtac 3; fail 3
                | some ?c =>
              (*    match find_absdata P tmsglsid with
                    | none _ => 
                      idtac 4 "no HTmsg in the pre-condition"; fail 4
                    | some ?d =>
               *)       match find_absdata P ostmid with
                        | none _ =>
                          idtac 4 "no HTime in the pre-condition"; fail 4
                        | some ?e =>
                          match find_absdata P curtid with
                            | none _ =>
                              idtac 5 "no HCurTCB in the pre-condition"; fail 5
                            | some ?f =>
                                  hoare lifts (a::b::c::e::f::nil) post;
                                    eapply abscsq_rule'
                              end
                          end
                  end
              end
          end
  end.

Tactic Notation "hoare" "abscsq" := hoare_abscsq.

Tactic Notation "hoare" "abscsq" "post" := hoare_abscsq'.



(* hoare forward *)

Ltac hoare_forward_first :=
  first [ hoare_assign
        | hoare_if
        | hoare_ret
        | hoare_call
        | hoare_calle_lvar
        | idtac ].


Ltac hoare_forward_stmts' :=
  let s := fresh in
  let H := fresh in
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} (sseq _ _) {{ _ }} =>
    eapply seq_rule; [ hoare_forward_stmts'
                     | idtac ]
  | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
    eapply forward_rule2; [ hoare_forward_first
                          | try sep_unfold_funpost;
                            first [ intros s H; exact H
                                  | sep pauto ] ]
  end.



Ltac hoare_forward_stmts :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalse_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse }} _ {{ _ }} =>
      apply hoare_disj_afalse_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse ** ?P \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalseP_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse **?P }} _ {{ _ }} =>
      apply hoare_disj_afalseP_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// _ }} _ {{ _ }} =>
      eapply disj_rule
    | _ => hoare normal pre; hoare_ex_intro;  hoare_forward_stmts'
  end.


Ltac hoare_forward_stmts'_nsepauto :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} (sseq _ _) {{ _ }} =>
      eapply seq_rule; [ hoare_forward_stmts'_nsepauto
                       | idtac ]
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
      eapply forward_rule2; [ hoare_forward_first
                            | ]
  end.



Ltac hoare_forward_stmts_nsepauto :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalse_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse }} _ {{ _ }} =>
      apply hoare_disj_afalse_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse ** ?P \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalseP_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse **?P }} _ {{ _ }} =>
      apply hoare_disj_afalseP_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// _ }} _ {{ _ }} =>
      eapply disj_rule
    | _ => hoare normal pre; hoare_ex_intro;  hoare_forward_stmts'_nsepauto
  end.


Tactic Notation "hoare" "forward" := hoare_forward_stmts.








