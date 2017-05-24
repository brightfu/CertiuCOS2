Require Import include_frm.
Require Import base_tac.
Require Import int_auto.

Open Scope Z_scope.

Ltac list_destruct H vl n :=
  let v := fresh in
  match n with
    | 0%nat => simp join; tryfalse
    | S ?n' => destruct vl as [ nil | v ]; [ simpl in H; simp join; tryfalse | list_destruct H vl n' ]
  end.

Lemma if_true_false_eq_true_elim :
  forall b : bool,
    (if b then true else false) = true ->
    b = true.
Proof.
  intros.
  destruct b; tryfalse || auto.
Qed.

Lemma if_true_false_eq_true_intro :
  forall b : bool,
    b = true ->
    (if b then true else false) = true.
Proof.
  intros.
  subst b; simpl; auto.
Qed.

Lemma if_true_false_eq_false_elim :
  forall b : bool,
    (if b then true else false) = false ->
    b = false.
Proof.
  intros.
  destruct b; tryfalse || auto.
Qed.

Lemma if_true_false_eq_false_intro :
  forall b : bool,
    b = false ->
    (if b then true else false) = false.
Proof.
  intros.
  subst b; simpl; auto.
Qed.

(* leb_max_true *)

Lemma byte_max_unsigned_val :
  Byte.max_unsigned = 255%Z.
Proof.
  unfold Byte.max_unsigned.
  unfold Byte.modulus.
  unfold two_power_nat, Byte.wordsize.
  unfold shift_nat, Wordsize_8.wordsize.
  unfold nat_rect.
  omega.
Qed.

Lemma int16_max_unsigned_val :
  Int16.max_unsigned = 65535%Z.
Proof.
  unfold Int16.max_unsigned.
  unfold Int16.modulus.
  unfold two_power_nat, Int16.wordsize.
  unfold shift_nat, Wordsize_16.wordsize.
  unfold nat_rect.
  omega.
Qed.

Lemma leb_bytemax_true_elim :
  forall i,
    Int.unsigned i <=? Byte.max_unsigned = true ->
    Int.unsigned i <= 255.
Proof.
  intros.
  rewrite byte_max_unsigned_val in H.
  apply Z.leb_le in H; auto.
Qed.

Lemma leb_int16max_true_elim :
  forall i,
    Int.unsigned i <=? Int16.max_unsigned = true ->
    Int.unsigned i <= 65535.
Proof.
  intros.
  rewrite int16_max_unsigned_val in H.
  apply Z.leb_le in H; auto.
Qed.

Lemma leb_bytemax_true_intro :
  forall i,
    Int.unsigned i <= 255 ->
    Int.unsigned i <=? Byte.max_unsigned = true.
Proof.
  intros.
  rewrite byte_max_unsigned_val.
  apply Z.leb_le; auto.
Qed.

Lemma leb_int16max_true_intro :
  forall i,
    Int.unsigned i <= 65535 ->
    Int.unsigned i <=? Int16.max_unsigned = true.
Proof.
  intros.
  rewrite int16_max_unsigned_val.
  apply Z.leb_le; auto.
Qed.

(* rule type val match *)
Open Scope code_scope.

Lemma rule_type_val_match_int8u_elim :
  forall v,
    rule_type_val_match Int8u v = true ->
    exists i, v = Vint32 i /\ Int.unsigned i <= 255.
Proof.
  intros.
  destruct v; simpl in *; tryfalse.
  exists i; intuition auto.
  apply if_true_false_eq_true_elim in H.
  apply leb_bytemax_true_elim in H; auto.
Qed.

Lemma rule_type_val_match_int16u_elim :
  forall v,
    rule_type_val_match Int16u v = true ->
    exists i, v = Vint32 i /\ Int.unsigned i <= 65535.
Proof.
  intros.
  destruct v; simpl in *; tryfalse.
  exists i; intuition auto.
  apply if_true_false_eq_true_elim in H.
  apply leb_int16max_true_elim in H; auto.
Qed.

Lemma rule_type_val_match_int32u_elim :
  forall v,
    rule_type_val_match Int32 v = true ->
    exists i, v = Vint32 i.
Proof.
  intros.
  destruct v; simpl in *; tryfalse.
  eauto.
Qed.

Lemma rule_type_val_match_ptr_elim :
  forall v t,
    rule_type_val_match (Tptr t) v = true ->
    isptr v.
Proof.
  intros.
  destruct v; simpl in *; tryfalse.
  unfold isptr; auto.
  unfold isptr; intuition eauto.
Qed.

Lemma rule_type_val_match_comptr_elim :
  forall v t,
    rule_type_val_match (Tcom_ptr t) v = true ->
    isptr v.
Proof.
  intros.
  destruct v; simpl in *; tryfalse.
  unfold isptr; auto.
  unfold isptr; intuition eauto.
Qed.

Ltac rule_type_val_match_elim :=
  match goal with
    | H : rule_type_val_match Int8u ?v = true |- _ =>
      let i := fresh "i" in
      apply rule_type_val_match_int8u_elim in H;
        destruct H as [ i [ ? H ]]; subst v;
        rule_type_val_match_elim
    | H : rule_type_val_match Int16u ?v = true |- _ =>
      let i := fresh "i" in
      apply rule_type_val_match_int16u_elim in H;
        destruct H as [ i [ ? H ]]; subst v;
        rule_type_val_match_elim
    | H : rule_type_val_match Int32u ?v = true |- _ =>
      let i := fresh "i" in
      apply rule_type_val_match_int32u_elim in H;
        destruct H as [ i H ]; subst v;
        rule_type_val_match_elim
    | H : rule_type_val_match (Tptr _) _ = true |- _ =>
      apply rule_type_val_match_ptr_elim in H;
        rule_type_val_match_elim
    | H : rule_type_val_match (Tcom_ptr _) _ = true |- _ =>
      apply rule_type_val_match_comptr_elim in H;
        rule_type_val_match_elim
    | _ => idtac
  end.

(* struct type vallist match *)

Lemma struct_type_vallist_match_elim_0: 
  forall v1,
    struct_type_vallist_match' dnil v1 -> v1 = nil.
Proof.
  inductions v1; simpl in *; intros; auto; tryfalse.
Qed.


Fixpoint remove_array_struct  (d:decllist) (vl : vallist) {struct d} :=
   match d , vl with
    | dnil, nil  =>  Some nil
    | dcons x t dls , v::vl' => 
      match t with
          | Tarray _  _  => remove_array_struct dls vl'
          | Tstruct _ _ => remove_array_struct dls vl'
          | _ =>
            match remove_array_struct dls vl' with
              | None => None
              | Some ls => Some ((t,v) :: ls)
            end
      end
    | _,_ => None
   end.

Fixpoint  rule_type_val_match_list (x: list (type * val)){struct x} : Prop:=
  match x with
      | nil => True
      | (t,v)::vl =>  rule_type_val_match t v = true/\ 
                      rule_type_val_match_list vl
  end.

Lemma struct_array_rm_type_val_match: 
  forall d v v', 
    remove_array_struct d v = Some v' -> 
    struct_type_vallist_match' d  v -> 
                 rule_type_val_match_list v'.

Proof.
 inductions d; inductions v; intros;simpl in *; auto; tryfalse.
 inverts H. simpl; auto.
 destruct t;simp join ;eauto.
 remember ( remove_array_struct d v) as Hr.
 destruct Hr; tryfalse.
 inverts H.
 apply eq_sym in HeqHr.
 lets Hd : IHd  HeqHr H1.
 simpl;splits; auto.
 remember ( remove_array_struct d v) as Hr.
 destruct Hr; tryfalse.
 remember ( remove_array_struct d v) as Hr.
 destruct Hr; tryfalse.
 inverts H.
 apply eq_sym in HeqHr.
 lets Hd : IHd  HeqHr H1.
 simpl;splits; auto.
remember ( remove_array_struct d v) as Hr.
 destruct Hr; tryfalse.
 inverts H.
 apply eq_sym in HeqHr.
 lets Hd : IHd  HeqHr H1.
 simpl;splits; auto.
remember ( remove_array_struct d v) as Hr.
 destruct Hr; tryfalse.
 inverts H.
 apply eq_sym in HeqHr.
 lets Hd : IHd  HeqHr H1.
 simpl;splits; auto.
 remember ( remove_array_struct d v) as Hr.
 destruct Hr; tryfalse.
 inverts H.
 apply eq_sym in HeqHr.
 lets Hd : IHd  HeqHr H1.
 simpl;splits; auto.
  remember ( remove_array_struct d v) as Hr.
 destruct Hr; tryfalse.
 inverts H.
 apply eq_sym in HeqHr.
 lets Hd : IHd  HeqHr H1.
 simpl;splits; auto.
Qed.

Lemma struct_type_vallist_match_elim_1 :
  forall x t v,
    struct_type_vallist_match'  (dcons x t dnil)   v ->
    exists v1 ,
      v = v1 :: nil.
Proof.
  intros;  simpl; subst.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t;simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_0 in H;subst; 
      do 1 eexists; eauto
  end. 
Qed.


Lemma struct_type_vallist_match_elim_2 :
  forall x1 t1 x2 t2 v ,
    struct_type_vallist_match'  (dcons x1 t1 (dcons x2 t2 dnil))  v ->
    exists v1 v2 ,
      v = v1::v2 :: nil.
Proof.
  intros;  simpl; subst.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t1;simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
     eapply struct_type_vallist_match_elim_1 in H; eauto ;simp join; do 3 eexists;auto
  end. 
Qed.

Lemma struct_type_vallist_match_elim_3 :
  forall x1 t1 x2 t2  x3 t3 v,
    struct_type_vallist_match' (dcons x1 t1 (dcons x2 t2 (dcons x3 t3 dnil)))  v ->
    exists v1 v2 v3,
      v = v1 ::  v2:: v3 :: nil.
Proof.
  intros;  simpl.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t1;simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_2 in H ; auto ; simp join
  end; 
  do 3 eexists; eauto.
Qed.

Lemma struct_type_vallist_match_elim_4 : 
  forall x1 t1 x2 t2  x3 t3 x4 t4 v,
    struct_type_vallist_match'(dcons x1 t1 (dcons x2 t2 (dcons x3 t3 (dcons x4 t4 dnil))))  v ->
    exists v1 v2 v3 v4,
      v = v1 ::  v2:: v3 :: v4 :: nil.
Proof.
  intros;  simpl.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t1;simp join; 
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_3 in H;auto; simp join
  end;
  do 4 eexists; eauto.
Qed.

Lemma struct_type_vallist_match_elim_5 : 
  forall x1 t1 x2 t2  x3 t3 x4 t4 x5 t5 v, 
    struct_type_vallist_match'(dcons x1 t1 (dcons x2 t2 (dcons x3 t3 (dcons x4 t4 (dcons x5 t5 dnil)))))  v -> 
    exists v1 v2 v3 v4 v5,
      v = v1 ::  v2:: v3 :: v4 :: v5 :: nil.
Proof.
  intros;  simpl.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t1;simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_4 in H;auto;simp join
  end; 
  do 5 eexists; eauto.
Qed.


Lemma struct_type_vallist_match_elim_6:
  forall x1 t1 x2 t2  x3 t3 x4 t4 x5 t5 x6 t6 v,
    struct_type_vallist_match'(dcons x1 t1 (dcons x2 t2 (dcons x3 t3 (dcons x4 t4 (dcons x5 t5 (dcons x6 t6 dnil))))))  v -> 
    exists v1 v2 v3 v4 v5 v6,
      v = v1 ::  v2:: v3 :: v4 :: v5 ::v6:: nil.
Proof.
  intros;  simpl.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t1;simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_5 in H;auto;simp join
  end; 
  do 6 eexists; eauto.
Qed.

Lemma struct_type_vallist_match_elim_7:
  forall x1 t1 x2 t2 x3 t3 x4 t4 x5 t5 x6 t6 x7 t7 v,
    struct_type_vallist_match'(dcons x7 t7 (dcons x1 t1 (dcons x2 t2 (dcons x3 t3 (dcons x4 t4 (dcons x5 t5 (dcons x6 t6 dnil)))))))  v -> 
    exists v1 v2 v3 v4 v5 v6 v7,
      v = v7:: v1 ::  v2:: v3 :: v4 :: v5 ::v6:: nil.
Proof.
  intros;  simpl.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t7;simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_6 in H;auto; simp join
  end; 
  do 7 eexists;  eauto.
Qed.

Lemma struct_type_vallist_match_elim_8 : 
  forall x1 t1 x2 t2 x3 t3 x4 t4 x5 t5 x6 t6 x7 t7 x8 t8 v,
    struct_type_vallist_match'(dcons x8 t8 (dcons x7 t7 (dcons x1 t1 (dcons x2 t2 (dcons x3 t3 (dcons x4 t4 (dcons x5 t5 (dcons x6 t6 dnil))))))) ) v -> 
    exists v1 v2 v3 v4 v5 v6 v7 v8,
      v = v8 ::v7:: v1 ::  v2:: v3 :: v4 :: v5 ::v6:: nil.
Proof.
  intros;  simpl.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t8;simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_7 in H;auto;simp join
  end; 
  do 8 eexists;  eauto.
Qed.


Lemma struct_type_vallist_match_elim_9 : 
  forall x1 t1 x2 t2 x3 t3 x4 t4 x5 t5 x6 t6 x7 t7 x8 t8 x9 t9 v,  
    struct_type_vallist_match'(dcons x9 t9 (dcons x8 t8 (dcons x7 t7 (dcons x1 t1 (dcons x2 t2 (dcons x3 t3 (dcons x4 t4 (dcons x5 t5 (dcons x6 t6 dnil))))))))) v ->
    exists v1 v2 v3 v4 v5 v6 v7 v8 v9,
      v = v9 ::v8 ::v7:: v1 ::  v2:: v3 :: v4 :: v5 ::v6:: nil.
Proof.
  intros;  simpl.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t9;simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_8 in H;auto; simp join
  end; 
  do 9 eexists;  eauto.
Qed.

Lemma struct_type_vallist_match_elim_10 :
  forall x1 t1 x2 t2 x3 t3 x4 t4 x5 t5 x6 t6 x7 t7 x8 t8 x9 t9 x10 t10 v,
    struct_type_vallist_match'(dcons x10 t10 (dcons x9 t9 (dcons x8 t8 (dcons x7 t7 (dcons x1 t1 (dcons x2 t2 (dcons x3 t3 (dcons x4 t4 (dcons x5 t5 (dcons x6 t6 dnil)))))))))) v -> 
    exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
      v = v10::v9 ::v8 ::v7:: v1 ::  v2:: v3 :: v4 :: v5 ::v6:: nil.
Proof.
  intros;  simpl.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t10; simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_9 in H;auto; simp join
  end; 
  do 10 eexists;  eauto.
Qed.


Lemma struct_type_vallist_match_elim_11 :
  forall x1 t1 x2 t2 x3 t3 x4 t4 x5 t5 x6 t6 x7 t7 x8 t8 x9 t9 x10 t10 x11 t11 v,
    struct_type_vallist_match'(dcons x11 t11(dcons x10 t10 (dcons x9 t9 (dcons x8 t8 (dcons x7 t7 (dcons x1 t1 (dcons x2 t2 (dcons x3 t3 (dcons x4 t4 (dcons x5 t5 (dcons x6 t6 dnil))))))))))) v ->  
    exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
      exists v11,
        v =v11:: v10::v9 ::v8 ::v7:: v1 ::  v2:: v3 :: v4 :: v5 ::v6:: nil.
Proof.
  intros;  simpl.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t11;simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_10 in H;auto; simp join
  end; 
  do 11 eexists;  eauto.
Qed.


Lemma struct_type_vallist_match_elim_12 :
  forall x1 t1 x2 t2 x3 t3 x4 t4 x5 t5 x6 t6 x7 t7 x8 t8 x9 t9 x10 t10 x11 t11 x12 t12 v,
    struct_type_vallist_match'(dcons x12 t12 (dcons x11 t11(dcons x10 t10 (dcons x9 t9 (dcons x8 t8 (dcons x7 t7 (dcons x1 t1 (dcons x2 t2 (dcons x3 t3 (dcons x4 t4 (dcons x5 t5 (dcons x6 t6 dnil)))))))))))) v -> 
    exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
      exists v11 v12,
        v =v12::v11:: v10::v9 ::v8 ::v7:: v1 ::  v2:: v3 :: v4 :: v5 ::v6:: nil.
Proof.
  intros;  simpl.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t12;simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_11 in H;auto; simp join
  end; 
  do 12 eexists;  eauto; repeat (splits; auto).
Qed.


Lemma struct_type_vallist_match_elim_13 :
  forall x1 t1 x2 t2 x3 t3 x4 t4 x5 t5 x6 t6 x7 t7 x8 t8 x9 t9 x10 t10 x11 t11 x12 t12 x13 t13 v,  
    struct_type_vallist_match'(dcons x13 t13 (dcons x12 t12 (dcons x11 t11(dcons x10 t10 (dcons x9 t9 (dcons x8 t8 (dcons x7 t7 (dcons x1 t1 (dcons x2 t2 (dcons x3 t3 (dcons x4 t4 (dcons x5 t5 (dcons x6 t6 dnil))))))))))))) v -> 
    exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
      exists v11 v12 v13,
        v =v13 ::v12::v11:: v10::v9 ::v8 ::v7:: v1 ::  v2:: v3 :: v4 :: v5 ::v6:: nil.
Proof.
  intros;  simpl.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t13;simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_12 in H;auto;simp join
  end; 
  do 13 eexists;  eauto; repeat (splits; auto).
Qed.

Ltac listlen x :=
  match x with
    | dnil => constr:0%nat
    | dcons _ _ ?x' => let y := listlen x' in
                       constr:(S y)
  end.

Ltac struct_type_vallist_match_elim :=
  match goal with
    | H : struct_type_vallist_match ?t _ |- _  =>
      try unfold t in H; simpl struct_type_vallist_match in H;
      match type of H with
        | struct_type_vallist_match' ?t' _  => 
          let Hr := fresh in let Hp := fresh in 
          match listlen t' with
            | 0%nat => lets Hr : struct_type_vallist_match_elim_0  H
            | 1%nat => lets Hr : struct_type_vallist_match_elim_1  H
            | 2%nat => lets Hr : struct_type_vallist_match_elim_2  H
            | 3%nat => lets Hr : struct_type_vallist_match_elim_3  H
            | 4%nat => lets Hr : struct_type_vallist_match_elim_4  H
            | 5%nat => lets Hr : struct_type_vallist_match_elim_5  H
            | 6%nat => lets Hr : struct_type_vallist_match_elim_6  H
            | 7%nat => lets Hr : struct_type_vallist_match_elim_7  H
            | 8%nat => lets Hr : struct_type_vallist_match_elim_8  H
            | 9%nat => lets Hr : struct_type_vallist_match_elim_9  H
            | 10%nat => lets Hr : struct_type_vallist_match_elim_10  H
            | 11%nat => lets Hr : struct_type_vallist_match_elim_11  H
            | 12%nat => lets Hr : struct_type_vallist_match_elim_12  H
            | 13%nat => lets Hr : struct_type_vallist_match_elim_13  H
            | _ => fail 1
          end;
            [ simp join; lets Hp : struct_array_rm_type_val_match H; 
              simpl remove_array_struct; eauto; clear H; unfold rule_type_val_match_list in Hp; simp join;
             struct_type_vallist_match_elim
            | (simpl; auto) .. ]
      end
    | _ => rule_type_val_match_elim
  end.

(* type val match *)

Lemma type_val_match_int8u_elim :
  forall v,
    type_val_match Int8u v = true ->
    exists i, v = Vint32 i /\ Int.unsigned i <= 255.
Proof.
  intros.
  destruct v; simpl in *; tryfalse.
  exists i; intuition auto.
  apply if_true_false_eq_true_elim in H.
  apply leb_bytemax_true_elim in H; auto.
Qed.

Lemma type_val_match_int16u_elim :
  forall v,
    type_val_match Int16u v = true ->
    exists i, v = Vint32 i /\ Int.unsigned i <= 65535.
Proof.
  intros.
  destruct v; simpl in *; tryfalse.
  exists i; intuition auto.
  apply if_true_false_eq_true_elim in H.
  apply leb_int16max_true_elim in H; auto.
Qed.

Lemma type_val_match_int32u_elim :
  forall v,
    type_val_match Int32u v = true ->
    exists i, v = Vint32 i.
Proof.
  intros.
  destruct v; simpl in *; tryfalse.
  eauto.
Qed.

Lemma type_val_match_ptr_elim :
  forall v t,
    type_val_match (Tptr t) v = true ->
    isptr v.
Proof.
  intros.
  destruct v; simpl in *; tryfalse.
  unfold isptr; auto.
  unfold isptr; eauto.
Qed.

Lemma type_val_match_comptr_elim :
  forall v t,
    type_val_match (Tcom_ptr t) v = true ->
    isptr v.
Proof.
  intros.
  destruct v; simpl in *; tryfalse.
  unfold isptr; auto.
  unfold isptr; eauto.
Qed.

Ltac type_val_match_elim :=
  match goal with
    | H : type_val_match Int8u ?v = true |- _ =>
      let i := fresh "i" in
      apply type_val_match_int8u_elim in H;
        destruct H as [ i [ ? H ]]; subst v;
        type_val_match_elim
    | H : type_val_match Int16u ?v = true |- _ =>
      let i := fresh "i" in
      apply type_val_match_int16u_elim in H;
        destruct H as [ i [ ? H ]]; subst v;
        type_val_match_elim
    | H : type_val_match Int32u ?v = true |- _ =>
      let i := fresh "i" in
      apply type_val_match_int32u_elim in H;
        destruct H as [ i H ]; subst v;
        type_val_match_elim
    | H : type_val_match (Tptr _) _ = true |- _ =>
      apply type_val_match_ptr_elim in H;
        type_val_match_elim
    | H : type_val_match (Tcom_ptr _) _ = true |- _ =>
      apply type_val_match_comptr_elim in H;
        type_val_match_elim
    | _ => idtac
  end.

Lemma true_if_else_true: 
  forall x, x =true -> (if x then true else false) = true.
Proof.
  intros.
  rewrite H.
  auto.
Qed.
  
Ltac rtmatch_solve:=   
  apply true_if_else_true;
  apply Zle_is_le_bool;
  try rewrite byte_max_unsigned_val; 
  try rewrite max_unsigned_val;
  try omega.

Close Scope Z_scope.
