Require Import os_inv.
Require Import include_frm.
Require Import int_auto.
Require Import sep_auto.
Require Import math_sol.
Require Import code_notations.
Require Import ucos_frmaop.
Require Import pure.
Require Import pure_lib.
Require Import tv_match.

Ltac unfold_field_fun' :=
  try unfold V_OSQPtr in *;
  try unfold V_OSEventListPtr in *;
  try unfold V_OSTCBNext in *;
  try unfold V_OSTCBPrev in *;
  try unfold V_OSTCBEventPtr in *;
  try unfold V_OSTCBMsg in *;
  try unfold V_OSTCBDly in *;
  try unfold V_OSTCBStat in *;
  try unfold V_OSTCBPrio in *;
  try unfold V_OSTCBX in *;
  try unfold V_OSTCBY in *;
  try unfold V_OSTCBBitX in *;
  try unfold V_OSTCBBitY in *;
  try unfold  V_OSEventType in *;
  try unfold V_OSEventGrp  in *;
  try unfold  V_OSEventCnt in *;
  try unfold V_OSEventPtr  in *;
  try unfold V_OSQStart in *;
  try unfold  V_OSQEnd in *;
  try unfold  V_OSQIn in *;
  try unfold  V_OSQOut in *; 
  try unfold   V_OSQSize in *;
  try unfold  V_OSQEntries in *;
  try unfold  V_qfreeblk  in *;
  try unfold V_nextblk in *;
  try unfold V_next  in *;
  try unfold  V_qeventptr in *.

Open Scope int_scope.

Ltac pauto := 
  unfold_field_fun';
  simpl nth_val in *; 
  repeat
    match goal with
      | H  : Some _ = Some _ |- _ =>  inverts H
      | H : Vptr _ = Vptr _ |- _ => inverts H
      | H : Vint32 _ = Vint32 _ |- _ => inverts H
      | _ => idtac
    end;
  try solve
      [auto || eauto || auto 
       with pauto_lemmas 
              || eauto with pauto_lemmas || pauto'].
              
Ltac clean_ptr H H' v:=
  let x:= fresh in
  destruct H;
    [assert (exists x,v=Vptr x) by pauto;simp join;clear H H'| 
     false;eapply isptr_val_inj_false;eauto].

                           
Ltac cauto :=
  match goal with
  | H : context [ GAarray ?id (Tarray ?t ?n) ?vl ] |- context [ length ?vl ] =>
    let H100 := fresh in
    assert (length vl = n) as H100
        by (sep destroy H;
            match goal with
            | H0 : _ |= GAarray id (Tarray t n) vl |- _ => apply GAarray_imp_length in H0; exact H0
            end); rewrite H100; clear H100; simpl; cauto
  | H : context [ LAarray ?id (Tarray ?t ?n) ?vl ] |- context [ length ?vl ] =>
    let H100 := fresh in
    assert (length vl = n) as H100
        by (sep destroy H;
            match goal with
            | H0 : _ |= GAarray id (Tarray t n) vl |- _ => apply LAarray_imp_length in H0; exact H0
            end); rewrite H100; clear H100; simpl; cauto
  | H : Int.ltu Int.zero ?i = false |- ?i = Int.zero => apply ltu_zero_false_imp_eq_zero in H; auto
  | |- Int.unsigned (Int.shru _ ($ 3)) < 8 => apply shru_3_lt_8; try omega
  | |- (Z.to_nat _ < _)%nat =>
    apply Nat2Z.inj_lt; rewrite Z2Nat.id; [ cauto | clear; int auto ]
  | _ => idtac
  end.
  
  Ltac solve_if_neq :=
    match goal with
      |  |- context[if ?c then _ else _] =>   
         try solve 
             [ let x := fresh in
               (destruct c; simpl; introv x; tryfalse) |
               apply true_if_else_true;
                 apply Zle_is_le_bool;
                 try rewrite byte_max_unsigned_val; 
                 try rewrite max_unsigned_val; 
                 try omega; auto
             ]

    end.

Lemma isptr_val_eq :
 forall x, isptr x -> 
           val_eq x Vnull = Some (Vint32 Int.one) \/
           val_eq x Vnull = Some (Vint32 Int.zero).
Proof.
  intros.
  unfolds in H.
  destruct H.
  unfold val_eq.
  destruct x; tryfalse.
  left; auto.
  simp join.
  unfold val_eq.
  destruct x0.
  right; auto.
Qed.

Ltac neq_solver :=
  match goal with
    |   |-  context[val_eq ?x Vnull]  =>
        match goal with 
          | |- _ <> _ =>
            let H:= fresh in
            assert (
                val_eq x Vnull = Some (Vint32 Int.one) \/
                val_eq x Vnull = Some (Vint32 Int.zero)
              ) as H by (apply isptr_val_eq; auto) ;
              destruct H;rewrite H; simpl; neq_solver          
        end
    |   |-  _ <> _ =>  let H:= fresh in introv H; simpl in H;  false
  end.

  Ltac simp_if :=
    repeat progress
           match goal with
             |  |- context[if ?c then _ else _] =>   
                let x := fresh in
                (destruct c; simpl) 
           end.

  Ltac pure_auto := first [ simp_if; neq_solver | pauto' |  go ].

  Close  Scope int_scope.
