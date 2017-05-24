Require Import include_frm.
Require Import math_rewrite.
Require Import int_auto.

Local Open Scope int_scope.
Local Open Scope Z_scope.

(* the following lemmas if for strut_type_vallist_match tactic *)
Lemma isptr_is_definitely_ptr :
  forall x, isptr x ->  match x with
   | Vundef => false
   | Vnull => true
   | Vint32 _ => false
   | Vptr _ => true
   end = true.
Proof.
  intros.
  destruct x;
  destruct H;
  simpljoin;
  tryfalse.
Qed.

Lemma le255_and_le255 :
  forall x v'37,
    Int.unsigned x<=255 -> Int.unsigned (x &ᵢ v'37) <= 255.
Proof.
  intros.
  set (Int.and_le x v'37).
  omega.
Qed.

Lemma ptr_isptr : forall x, isptr (Vptr x).
  intros.
  unfolds.
  right; eexists; eauto.
Qed.

Lemma Vnull_is_ptr : isptr Vnull.
Proof.
  unfolds; auto.
Qed.

Hint Resolve le255_and_le255                    : struct_type_match_side_lib.
Hint Resolve ptr_isptr                          : struct_type_match_side_lib.
Hint Resolve Vnull_is_ptr                       : struct_type_match_side_lib.
Hint Resolve isptr_is_definitely_ptr            : struct_type_match_side_lib.

Ltac struct_single_condition_solver :=
  let H := fresh in
  try math_simpl H;
    try solve [ auto with struct_type_match_side_lib
                            (* here just bsimpl*r* just to compat with old version *)
               |math prove neg H; bsimplr; auto with struct_type_match_side_lib; omega].

Ltac struct_type_match_solver_new :=
  match goal with
    | |- struct_type_vallist_match ?a _ => unfold a
  end;
  unfold struct_type_vallist_match; simpl; repeat splits ; struct_single_condition_solver. 

Ltac struct_type_match_solver := struct_type_match_solver_new.

(* Require Import os_ucos_h.
 * 
 * Lemma struct_type_vallist_match_os_tcb :
 *   forall xx v'82 v'80 v'37 v'75 v'76 v'77 v'78 v'79 xxx yyy flag,
 *     isptr xxx ->
 *     isptr yyy ->
 *     isptr v'82 -> 
 *     isptr v'80 ->
 *     Int.unsigned v'37 <= 255 ->
 *     Int.unsigned v'75 <= 255 ->
 *     Int.unsigned v'76 <= 255 ->
 *     Int.unsigned v'77 <= 255 ->
 *     Int.unsigned v'78 <= 255 ->
 *     Int.unsigned v'79 <= 255 ->
 *     Int.unsigned xx <= 65535-> 
 *     Int.unsigned flag <= 255 ->
 *     struct_type_vallist_match OS_TCB
 *                               (v'82
 *                                  :: v'80
 *                                  :: xxx
 *                                  :: yyy
 *                                  :: Vint32 xx
 *                                  :: Vint32 (v'37 &ᵢ v'75)
 *                                  :: Vint32 v'75
 *                                  :: Vint32 v'76
 *                                  :: Vint32 v'77
 *                                  :: Vint32 v'78 :: Vint32 v'79 :: Vint32 flag::  nil).
 * Proof.
 *   intros.
 *   struct_type_match_solver_new.
 * Qed. *)

(* Lemma struct_type_vallist_match_os_event_mbox:  forall v'51 v'52 v'49 v'50 v'55, isptr v'50 -> isptr v'51 -> Int.unsigned v'52 <= 255 -> Int.unsigned v'49 <= 65535-> struct_type_vallist_match OS_EVENT (V$OS_EVENT_TYPE_MBOX
 *       :: Vint32 v'52 :: Vint32 v'49 :: v'50 :: v'55 :: v'51 :: nil).
 *   intros.
 *   pauto.
 * Qed. *)

(* Lemma struct_type_vallist_match_os_event:  forall v'51 v'52 v'49 v'50 v'55 xx, isptr v'50 -> isptr v'51 ->Int.unsigned xx <=255 -> Int.unsigned v'52 <= 255 -> Int.unsigned v'49 <= 65535-> struct_type_vallist_match OS_EVENT (Vint32 xx
 *       :: Vint32 v'52 :: Vint32 v'49 :: v'50 :: v'55 :: v'51 :: nil).
 * Proof.
 *   intros.
 *   struct_type_match_solver_new.
 * Qed. *)


(* Ltac const_le_solver := match goal with 
 * | |- Int.unsigned  ($ ?e ) <= _ => try solve [clear; unfold e; int auto]
 * end.
 * 
 * Ltac struct_type_match_solver := match goal with
 * | |- struct_type_vallist_match OS_EVENT _ =>  apply  struct_type_vallist_match_os_event
 * | |- struct_type_vallist_match OS_TCB _   =>  apply  struct_type_vallist_match_os_tcb
 * end; try solve [ auto 3 with struct_type_match_side_lib | unfolds; auto 3 with struct_type_match_side_lib | const_le_solver]. *)

