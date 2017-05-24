Require Import include_frm.
Require Import sep_auto.
Require Import math_auto.

Import DeprecatedTactic.

Set Implicit Arguments.

(* separation line *)


Lemma map_get_join_val :
  forall  (x y z: mem) t b v, 
    join x y z ->
    HalfPermMap.get x t = Some (b, v) ->
    exists b, HalfPermMap.get z t = Some (b, v).
Proof.
  intros.
  unfold join in H.
  unfold memMap in H.
  unfold HalfPermMap.join in H.
  unfold HalfPermMap.disjoint in H.
  unfold HalfPermMap.merge in H.
  destruct H.
  rewrite H1.
  unfold HalfPermMap.get in *.
  lets aa: H t.
  rewrite H0 in *.
  destruct b.
  destruct (y t).
  inversion aa.
  eauto.
  destruct (y t).
  destruct b.
  destruct b.
  inversion aa.
  inverts aa.
  unfold HalfPermMap.rjoin.
  2:eauto.
  destruct (HalfPermMap.dec_C c c ).
  eauto.
  eauto.
Qed.


Lemma loadbytes_mono: 
  forall m M m' l n v ,  
    join m M m' -> 
    loadbytes m l n = Some v ->
    loadbytes m' l n = loadbytes m l n.
Proof.
  intros.
  generalize dependent l.
  generalize dependent v.
  induction n.
  intros.
  simpl.
  auto.
  intros.
  destruct l.
  simpl.
  simpl in H0.
  change (match get m (b, o) with
               | Some (_, u) =>
                 match loadbytes m (b, (o + 1)%Z) n with
                   | Some bl => Some (u :: bl)
                   | None => None
                 end
               | None => None
             end
         ) with ((fun x =>    match x with
                                | Some (_, u) =>
                                  match loadbytes m (b, (o + 1)%Z) n with
                                    | Some bl => Some (u :: bl)
                                    | None => None
                                  end
                                | None => None
                              end
                 ) (get m (b,o))) in *.

  remember (get m ( b, o)) as bb.
  unfold get in Heqbb.
  simpl in Heqbb.
  assert (HalfPermMap.get m (b,o) = bb).
  auto.
  destruct bb.
  destruct p.
  lets ff: map_get_join_val H.
  apply ff in H1.
  unfold HalfPermMap.get in Heqbb.
  mytac.
  unfold get.
  simpl.
  rewrite H1.
  remember (   loadbytes m (b, (o + 1)%Z) ).
  rewrite Heqo0.
  remember (o0 n).
  assert ((exists bl, o1 = Some bl) \/ o1 = None).
  destruct o1.
  left; eauto.
  right; auto.
  destruct H2; intros.
  destruct H2.
  erewrite IHn.
  auto.
  rewrite <- Heqo0.
  rewrite <- Heqo1.
  eauto.
  rewrite H2 in H0.
  inversion H0.
  inversion H0.
Qed.


Lemma ptomvallist_loadbytes : 
  forall l vl m perm, 
    ptomvallist l perm  vl m -> 
    loadbytes m l (length vl) = Some vl.
Proof.
  intros.
  gen l m H.
  inductions vl; intros.
  simpl.
  auto.
  simpl.
  destruct l.
  simpl in H.
  do 3 destruct H.
  destruct H0.
  apply IHvl in H1.
  clear IHvl.
  unfolds in H0.
  pose proof loadbytes_mono.
  pose proof (H2 x0 x m (b, (o + 1)%Z) (length vl) vl).
  clear H2.
  apply map_join_comm in H.
  pose proof (H3 H H1).
  clear H3.
  rewrite <- H2 in H1.
  clear H2.
  rewrite H1.
  subst.
  apply map_join_comm in H.
  lets fff:  map_get_join_val H (map_get_sig (b,o) (perm, a)).
  destruct fff.
  unfold get.
  simpl.
  rewrite H0.
  auto.
Qed.

Open Scope nat_scope.

Lemma type_val_mach_encode_val_decode_val : 
  forall t v, rule_type_val_match t v =true -> 
              decode_val t (encode_val t v) = v.
Proof.
  intros.
  destruct t; destruct v; simpl in H; tryfalse; simpl; auto.

  unfolds.
  simpl.
  destruct ((Int.unsigned i <=? Byte.max_unsigned)%Z) eqn : eq1; tryfalse.
  replace (Byte.unsigned (Byte.repr (Int.unsigned i)) + 0)%Z with (Byte.unsigned (Byte.repr (Int.unsigned i))).
  pose proof Int.unsigned_range i.
  destruct H0.
  rewrite Z.leb_le in eq1.
  rewrite Byte.unsigned_repr.
  rewrite Int.repr_unsigned.
  assert (Int.zero_ext 8 i = i).
  pose proof Int.zero_ext_mod 8 i.
  assert ((0 <= 8 < Int.zwordsize)%Z).
  unfold Int.zwordsize.
  unfold Int.wordsize.
  unfold Wordsize_32.wordsize.
  simpl.
  omega.
  apply H2 in H3; clear H2.
  rewrite Coqlib.Zmod_small in H3.
  assert (Int.repr (Int.unsigned (Int.zero_ext 8 i)) = Int.repr (Int.unsigned i)).
  rewrite H3.
  auto.
  rewrite Int.repr_unsigned in H2.
  rewrite Int.repr_unsigned in H2.
  auto.
  unfold Byte.max_unsigned in eq1.
  unfold Byte.modulus in eq1.
  unfold Byte.wordsize in eq1.
  unfold Wordsize_8.wordsize in eq1.
  unfold two_power_nat in eq1.
  unfold two_p.
  unfold two_power_pos.
  rewrite shift_pos_nat.
  assert (Pos.to_nat 8 = 8).
  auto.
  rewrite H2.
  omega.
  rewrite H2.
  auto.
  omega.
  omega.

  unfolds.
  simpl.
  destruct ((Int.unsigned i <=? Int16.max_unsigned)%Z) eqn : eq1; tryfalse.
  replace (Byte.unsigned (Byte.repr (Int.unsigned i / 256)) + 0)%Z with (Byte.unsigned (Byte.repr (Int.unsigned i / 256))).
  pose proof Int.unsigned_range i.
  destruct H0.
  rewrite Z.leb_le in eq1.
  replace (Byte.unsigned (Byte.repr (Int.unsigned i / 256))) with (Int.unsigned i / 256)%Z.
  replace (Byte.unsigned (Byte.repr (Int.unsigned i))) with ((Int.unsigned i) mod Byte.modulus)%Z.
  rewrite Z.add_comm.
  unfold Byte.modulus.
  unfold Byte.wordsize.
  unfold Wordsize_8.wordsize.
  unfold two_power_nat.
  unfold shift_nat.
  simpl.
  rewrite Z.mul_comm.
  rewrite <- Z.div_mod.
  rewrite Int.repr_unsigned.
  assert (Int.zero_ext 16 i = i).
  pose proof Int.zero_ext_mod 16 i.
  assert ((0 <= 16 < Int.zwordsize)%Z).
  unfold Int.zwordsize.
  unfold Int.wordsize.
  unfold Wordsize_32.wordsize.
  simpl.
  omega.
  apply H2 in H3; clear H2.
  rewrite Coqlib.Zmod_small in H3.
  assert (Int.repr (Int.unsigned (Int.zero_ext 16 i)) = Int.repr (Int.unsigned i)).
  rewrite H3.
  auto.
  rewrite Int.repr_unsigned in H2.
  rewrite Int.repr_unsigned in H2.
  auto.
  unfold Int16.max_unsigned in eq1.
  unfold Int16.modulus in eq1.
  unfold Int16.wordsize in eq1.
  unfold Wordsize_16.wordsize in eq1.
  unfold two_power_nat in eq1.
  unfold two_p.
  unfold two_power_pos.
  rewrite shift_pos_nat.
  assert (Pos.to_nat 16 = 16).
  auto.
  rewrite H2.
  omega.
  rewrite H2.
  auto.
  omega.
  rewrite <- Byte.unsigned_repr_eq.
  auto.
  rewrite Byte.unsigned_repr.
  auto.
  unfold Byte.max_unsigned.
  unfold Byte.modulus.
  simpl.
  unfold Int16.max_unsigned in eq1.
  unfold Int16.modulus in eq1.
  simpl in eq1.
  split.
  apply Z.div_pos.
  auto.
  omega.
  assert (255 = 65535 / 256)%Z.
  compute.
  auto.
  rewrite H2.
  assert (256 > 0)%Z.
  omega.
  pose proof Z_div_le (Int.unsigned i) 65535 256 H3 eq1.
  auto.
  omega.

  unfolds.
  simpl.
  replace (Byte.unsigned (Byte.repr (Int.unsigned i / 256 / 256 / 256)) + 0)%Z with (Byte.unsigned (Byte.repr (Int.unsigned i / 256 / 256 / 256))).
  pose proof Int.unsigned_range i.
  destruct H0.
  replace (Byte.unsigned (Byte.repr (Int.unsigned i / 256 / 256 / 256))) with (Int.unsigned i / 256 / 256 / 256)%Z.
  replace (Byte.unsigned (Byte.repr (Int.unsigned i))) with (Int.unsigned i mod Byte.modulus)%Z.
  replace (Byte.unsigned (Byte.repr (Int.unsigned i / 256))) with (Int.unsigned i / 256 mod Byte.modulus)%Z.
  replace (Byte.unsigned (Byte.repr (Int.unsigned i / 256 / 256))) with (Int.unsigned i / 256 / 256 mod Byte.modulus)%Z.
  rewrite Z.add_comm.
  unfold Byte.modulus.
  unfold Byte.wordsize.
  unfold Wordsize_8.wordsize.
  unfold two_power_nat.
  unfold shift_nat.
  simpl.
  assert (((Int.unsigned i / 256 / 256) mod 256 + Int.unsigned i / 256 / 256 / 256 * 256) =
          (Int.unsigned i / 256 / 256))%Z.
  rewrite Z.add_comm.
  rewrite Z.mul_comm.
  rewrite <- Z_div_mod_eq.
  auto.
  omega.
  rewrite H2.
  assert (((Int.unsigned i / 256) mod 256 + Int.unsigned i / 256 / 256 * 256) = (Int.unsigned i / 256))%Z.
  rewrite Z.add_comm.
  rewrite Z.mul_comm.
  rewrite <- Z_div_mod_eq.
  auto.
  omega.
  rewrite H3.
  assert ((Int.unsigned i mod 256 + Int.unsigned i / 256 * 256) = Int.unsigned i)%Z.
  rewrite Z.add_comm.
  rewrite Z.mul_comm.
  rewrite <- Z_div_mod_eq.
  auto.
  omega.
  rewrite Z.add_comm.
  rewrite H4.
  rewrite Int.repr_unsigned.
  auto.
  rewrite Byte.unsigned_repr_eq.
  auto.
  rewrite Byte.unsigned_repr_eq.
  auto.
  rewrite Byte.unsigned_repr_eq.
  auto.
  rewrite Byte.unsigned_repr_eq.
  rewrite Coqlib.Zmod_small.
  auto.
  split.
  apply Z.div_pos.
  apply Z.div_pos.
  apply Z.div_pos.
  auto.
  omega.
  omega.
  omega.
  unfold Int.modulus in H1.
  unfold Int.wordsize in H1.
  unfold Wordsize_32.wordsize in H1.
  unfold two_power_nat in H1.
  unfold shift_nat in H1.
  simpl in H1.
  unfold Byte.modulus.
  unfold two_power_nat.
  unfold shift_nat.
  simpl.
  apply Zdiv_lt_upper_bound.
  omega.
  apply Zdiv_lt_upper_bound.
  omega.
  apply Zdiv_lt_upper_bound.
  omega.
  simpl.
  auto.
  omega.

  unfolds.
  destruct a.
  simpl.
  unfold Coqlib.proj_sumbool.
  rewrite Coqlib.peq_true.
  destruct (Int.eq_dec i i) eqn : eq1.
  simpl.
  auto.
  false.

  unfolds.
  destruct a.
  simpl.
  unfold Coqlib.proj_sumbool.
  rewrite Coqlib.peq_true.
  destruct (Int.eq_dec i0 i0) eqn : eq1.
  simpl.
  auto.
  false.
Qed.


Lemma mapstoval_loadbytes: 
  forall b i t v m perm, 
    rule_type_val_match t v = true -> 
    mapstoval (b,i) t perm v m -> 
    exists bls, loadbytes m (b,i) (typelen t) = Some bls /\ (decode_val t bls = v).
Proof.
  intros.
  unfolds in H0.
  destruct H0.
  destruct H0.
  substs.
  apply ptomvallist_loadbytes in H1.
  rewrite encode_val_length in H1.
  exists (encode_val t v).
  split.
  auto.

  apply type_val_mach_encode_val_decode_val.
  auto.
Qed.

Lemma loadm_mono : 
forall m M m' t l v,  
   join m M m' ->
   loadm t m l = Some v -> 
   loadm t m' l = loadm t m l .
Proof.
  intros.
  destruct l.
  simpl in *.
  remember (loadbytes m (b, o) (typelen t)) as bb.
  destruct bb.
  symmetry in Heqbb.
  assert (loadbytes m' (b, o) (typelen t) = Some l).
  erewrite loadbytes_mono;eauto.
  rewrite H1.
  auto.
  inversion H0.
Qed.

Lemma load_mono: forall m M m' t l v,  join m M m' ->
                                       load t m l = Some v -> load t m' l = load t m l .
Proof.
  unfold load;intros;destruct t;try eapply loadm_mono;eauto.
Qed.

Lemma load_local:
  forall m t l v m1 m2, join m1 m2 m ->
                        load t m1 l = Some v ->
                        load t m l = Some v.
Proof.
  intros.
  erewrite load_mono;eauto.
Qed.

Lemma mapstoval_load: 
  forall l t v m perm, rule_type_val_match t v = true -> mapstoval l t perm v m -> load t m l = Some v.
Proof.
  intros.
  unfold load.
  destruct l.
  destruct t;simpl in H;tryfalse;unfold loadm.

  pose proof @mapstoval_loadbytes b o Tnull v m perm H H0.
  destruct H1.
  destruct H1.
  rewrite H1.
  rewrite H2.
  auto.

  pose proof @mapstoval_loadbytes b o Tint8 v m perm H H0.
  destruct H1.
  destruct H1.
  rewrite H1.
  rewrite H2.
  auto.

  pose proof @mapstoval_loadbytes b o Tint16 v m perm H H0.
  destruct H1.
  destruct H1.
  rewrite H1.
  rewrite H2.
  auto.

  pose proof @mapstoval_loadbytes b o Tint32 v m perm H H0.
  destruct H1.
  destruct H1.
  rewrite H1.
  rewrite H2.
  auto.

  pose proof @mapstoval_loadbytes b o (Tptr t) v m perm H H0.
  destruct H1.
  destruct H1.
  rewrite H1.
  rewrite H2.
  auto.

  pose proof @mapstoval_loadbytes b o (Tcom_ptr i) v m perm H H0.
  destruct H1.
  destruct H1.
  rewrite H1.
  rewrite H2.
  auto.
Qed.


Lemma mapstoval_load_vptr : 
  forall l tp v v' m perm, 
    (forall t n,tp<> Tarray t n) -> 
    mapstoval l tp perm (Vptr v)  m -> 
    load tp m l = Some (Vptr v') -> v = v'.
Proof.
  introv Hx.
  intros.
  apply mapstoval_load in H.
  rewrite H in H0.
  inv H0.
  auto.
  unfolds in H.
  destruct H.
  destruct H.
  unfolds in H0.
  destruct l.
  unfold loadm in H0.
  destruct tp.

  destruct ( loadbytes m (b, o) (typelen Tnull)) eqn : eq1; tryfalse.
  inv H0.
  unfolds in H3.
  destruct (proj_bytes l).
  tryfalse.
  destruct l; tryfalse; simpl; auto.
  repeat (destruct m0; tryfalse;
          destruct l; tryfalse).


  destruct ( loadbytes m (b, o) (typelen Tvoid)) eqn : eq1; tryfalse.
  inv H0.
  unfolds in H3.
  destruct (proj_bytes l).
  tryfalse.
  destruct l; tryfalse; simpl; auto.
  repeat (destruct m0; tryfalse;
          destruct l; tryfalse).


  destruct ( loadbytes m (b, o) (typelen Tint8)) eqn : eq1; tryfalse.
  inv H0.
  unfolds in H3.
  destruct (proj_bytes l).
  tryfalse.
  destruct l; tryfalse; simpl; auto.
  repeat (destruct m0; tryfalse;
          destruct l; tryfalse).



  destruct ( loadbytes m (b, o) (typelen Tint16)) eqn : eq1; tryfalse.
  inv H0.
  unfolds in H3.
  destruct (proj_bytes l).
  tryfalse.
  destruct l; tryfalse; simpl; auto.
  repeat (destruct m0; tryfalse;
          destruct l; tryfalse).


  destruct ( loadbytes m (b, o) (typelen Tint32)) eqn : eq1; tryfalse.
  inv H0.
  unfolds in H3.
  destruct (proj_bytes l).
  tryfalse.
  destruct l; tryfalse; simpl; auto.
  repeat (destruct m0; tryfalse;
          destruct l; tryfalse).


  destruct ( loadbytes m (b, o) (typelen (Tptr tp))) eqn : eq1; tryfalse.
  inv H0.
  unfolds in H3.
  destruct (proj_bytes l).
  tryfalse.
  destruct l; tryfalse; simpl; auto.
  repeat (destruct m0; tryfalse;
          destruct l; tryfalse).

  lets Ha:Hx Tvoid 0.
  tryfalse.


  destruct ( loadbytes m (b, o) (typelen (Tcom_ptr i))) eqn : eq1; tryfalse.
  inv H0.
  unfolds in H3.
  destruct (proj_bytes l).
  tryfalse.
  destruct l; tryfalse; simpl; auto.
  repeat (destruct m0; tryfalse;
          destruct l; tryfalse).

  lets Ha:Hx Tvoid 0.
  tryfalse.

  destruct ( loadbytes m (b, o) (typelen (Tstruct i d))) eqn : eq1; tryfalse.
  inv H0.
  unfolds in H3.
  destruct (proj_bytes l).
  tryfalse.
  destruct l; tryfalse; simpl; auto.
  repeat (destruct m0; tryfalse;
          destruct l; tryfalse).

Qed.

(*
Lemma nindom_get : forall (a : env) x, ~indom a x -> get a x = None.
Proof.
  intros.
  unfold indom in H.
  simpl in H.
  unfold EnvMod.indom in H.
  unfold get.
  simpl.
  destruct (EnvMod.get a x).
  false.
  apply H.
  eauto.
  auto.
Qed.
 *)

Lemma loadbytes_local: forall m1 m2 m bls b i t, join m1 m2 m -> loadbytes m1 (b,i) (typelen t) = Some bls -> loadbytes m (b,i) (typelen t) = Some bls.
Proof.
  intros.
  rewrite <- H0.
  eapply loadbytes_mono.
  eauto.
  eauto.
Qed.

(* separation line *)

Lemma nth_id_some_in_decllist_true : forall n dls id, nth_id n dls = Some id -> in_decllist id dls = true.
Proof.
  intro.
  induction n; intros.
  destruct dls; simpl in H; tryfalse.
  inversion H.
  substs.
  simpl.
  apply Bool.orb_true_iff.
  left.
  apply Zbool.Zeq_is_eq_bool.
  auto.
  destruct dls; simpl in H; tryfalse.
  simpl.
  apply Bool.orb_true_iff.
  right.
  eapply IHn.
  auto.
Qed.

Lemma in_decllist_field_offsetfld_some : forall dls id, in_decllist id dls = true -> forall n, exists off, field_offsetfld id dls n = Some off.
Proof.
  intro.
  induction dls; intros.
  simpl in H.
  inversion H.
  simpl in H.
  apply Bool.orb_true_iff in H.
  destruct H.
  apply Zbool.Zeq_is_eq_bool in H.
  substs.
  eexists.
  simpl.
  assert (Zbool.Zeq_bool i i = true).
  apply Zbool.Zeq_is_eq_bool.
  auto.
  rewrite H.
  auto.
  simpl.
  destruct (Zbool.Zeq_bool id i).
  eauto.
  eapply IHdls.
  auto.
Qed.

Lemma field_offsetfld_pos_mono : forall dls id pos1 off1,
                                   field_offsetfld id dls pos1 = Some off1
                                   -> forall pos2 off2, field_offsetfld id dls pos2 = Some off2
                                                        -> forall n, Int.add n pos1 = pos2
                                                                     -> Int.add n off1 = off2.
Proof.
  intro.
  induction dls; intros.
  simpl in H.
  inversion H.
  simpl in H.
  simpl in H0.
  destruct (Zbool.Zeq_bool id i).
  inversion H.
  inversion H0.
  substs.
  auto.
  eapply IHdls.
  apply H.
  apply H0.
  substs.
  rewrite Int.add_commut.
  rewrite Int.add_assoc.
  replace (Int.add pos1 n) with (Int.add n pos1).
  auto.
  apply Int.add_commut.
Qed.

Lemma nth_id_field_offsetfld_some : forall decl n id, nth_id n decl = Some id -> forall pos, exists off, field_offsetfld id decl pos = Some off.
Proof.
  intros.
  apply nth_id_some_in_decllist_true in H.
  apply in_decllist_field_offsetfld_some.
  auto.
Qed.


Lemma nth_id_exists_off: forall decl n id, nth_id n decl = Some id -> exists off, field_offset id decl = Some off.
Proof.
  intro.
  destruct decl; intros.
  simpl in H.
  inversion H.
  destruct n.
  inversion H.
  unfold field_offset.
  simpl.
  simpl in H.
  assert (Zbool.Zeq_bool id id = true).
  apply Zbool.Zeq_is_eq_bool.
  auto.
  rewrite H0.
  eauto.
  simpl in H.
  unfold field_offset.
  simpl.
  destruct ( Zbool.Zeq_bool id i).
  eauto.
  eapply nth_id_field_offsetfld_some.
  eauto.
Qed.


Lemma field_asrt_impl: 
  forall p id x tid decl b i off tp perm, 
    ftype id decl = Some tp ->
    field_offset id decl = Some off -> 
    ((LV x @ Tptr (Tstruct tid decl) |=> Vptr (b, i) @ perm) ** p) ==> (Lv (efield (ederef (evar x)) id) @ tp == (b,Int.add i off)).
Proof.
  intros.
  unfold sat.
  destruct  s as [[]].
  destruct t as [[[[]]]].
  unfold sat in H1;fold sat in H1;mytac.
  simpl in H5;mytac.
  simpl.
  rewrite H8.
  apply mapstoval_loadbytes in H9.
  destruct H9 as (bls&H9).
  destruct H9.
  simpl in H2.
  lets Hl:loadbytes_local H2 H1.
  rewrite Int.unsigned_zero in Hl.
  assert (loadbytes m (x11, BinNums.Z0) (typelen (Tptr (Tstruct tid decl))) = Some bls).
  auto.
  unfold load.
  unfold loadm.
  rewrite H4.
  rewrite H3.
  unfold getoff.
  simpl.
  rewrite H8.
  rewrite H0.
  rewrite Int.repr_unsigned.
  auto.
  simpl;auto.
  simpl.
  simpl in H5;mytac.
  rewrite H8.
  auto.
Qed.

Lemma field_asrt_impl_g: 
  forall p id x tid decl b i off tp perm, 
    ftype id decl = Some tp ->
    field_offset id decl = Some off -> 
    ((A_notin_lenv x ** GV x @ Tptr (Tstruct tid decl) |=> Vptr (b, i) @ perm) ** p) ==> (Lv (efield (ederef (evar x)) id) @ tp == (b,Int.add i off)).
Proof.
  intros.
  unfold sat.
  destruct  s as [[]].
  destruct t as [[[[]]]].
  unfold sat in H1;fold sat in H1;mytac.
  simpl in *;mytac.
  rewrite H11.
  apply (EnvMod.nindom_get )in H10.
  change (  (fun xxx => match
                 match
                   match xxx with
                     | Some (_, t) => Some t
                     | None => Some (Tptr (Tstruct tid decl))
                   end
                 with
                   | Some _ =>
                     match xxx with
                       | Some (a0, t0) => load t0 m (a0, 0%Z)
                       | None => load (Tptr (Tstruct tid decl)) m (x15, 0%Z)
                     end
                   | None => None
                 end
               with
                 | Some Vundef => None
                 | Some Vnull => None
                 | Some (Vint32 _) => None
                 | Some (Vptr (b0, i1)) =>
                   match getoff b0 (Int.unsigned i1) id (ederef (evar x)) (e, e0, m) with
                     | Some ad => Some (Vptr ad)
                     | None => None
                   end
                 | None => None
               end = Some (Vptr (b, Int.add i off))
            ) (get e0 x) ).
  rewrite H10.
  apply mapstoval_loadbytes in H13.
  destruct H13 as (bls&H13).
  destruct H13.
  simpl in H2.
  lets Hl:loadbytes_local H2 H1.
  rewrite Int.unsigned_zero in Hl.
  assert (loadbytes m (x15, BinNums.Z0) (typelen (Tptr (Tstruct tid decl))) = Some bls).
  auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H3.
  unfold getoff.
  simpl.
  change ( ( fun xxx =>
               match
                 match
                   match
                     match xxx with
                       | Some (_, t) => Some t
                       | None =>
                         match get e x with
                           | Some (_, t) => Some t
                           | None => None
                         end
                     end
                   with
                     | Some Tnull => None
                     | Some Tvoid => None
                     | Some Tint8 => None
                     | Some Tint16 => None
                     | Some Tint32 => None
                     | Some (Tptr t) => Some t
                     | Some (Tcom_ptr _) => None
                     | Some (Tarray _ _) => None
                     | Some (Tstruct _ _) => None
                     | None => None
                   end
                 with
                   | Some Tnull => None
                   | Some Tvoid => None
                   | Some Tint8 => None
                   | Some Tint16 => None
                   | Some Tint32 => None
                   | Some (Tptr _) => None
                   | Some (Tcom_ptr _) => None
                   | Some (Tarray _ _) => None
                   | Some (Tstruct _ dl) =>
                     match field_offset id dl with
                       | Some off0 => Some (b, Int.add (Int.repr (Int.unsigned i)) off0)
                       | None => None
                     end
                   | None => None
                 end
               with
                 | Some ad => Some (Vptr ad)
                 | None => None
               end = Some (Vptr (b, Int.add i off))
           ) (get e0 x) ).
  rewrite H10.
  rewrite H11.
  rewrite Int.repr_unsigned.
  auto.
  simpl.
  rewrite H0.
  auto.
  simpl;auto.
  simpl in *;mytac.
  apply EnvMod.nindom_get in H10.
  change ( (fun xxx =>    match
                match
                  match xxx with
                    | Some (_, t) => Some t
                    | None =>
                      match get e x with
                        | Some (_, t) => Some t
                        | None => None
                      end
                  end
                with
                  | Some Tnull => None
                  | Some Tvoid => None
                  | Some Tint8 => None
                  | Some Tint16 => None
                  | Some Tint32 => None
                  | Some (Tptr t) => Some t
                  | Some (Tcom_ptr _) => None
                  | Some (Tarray _ _) => None
                  | Some (Tstruct _ _) => None
                  | None => None
                end
              with
                | Some Tnull => None
                | Some Tvoid => None
                | Some Tint8 => None
                | Some Tint16 => None
                | Some Tint32 => None
                | Some (Tptr _) => None
                | Some (Tcom_ptr _) => None
                | Some (Tarray _ _) => None
                | Some (Tstruct _ dl) => ftype id dl
                | None => None
              end = Some tp
           ) (get e0 x) ).
  rewrite H10.
  rewrite H11.
  auto.
Qed.
Lemma nth_id_Some_imply_in_decllist :
  forall n id dls,
    nth_id n dls = Some id ->
    in_decllist id dls = true.
Proof.
  intros.
  gen n id.
  induction dls;intros.
  inverts H.
  destruct n;tryfalse.
  simpl in *.
  inverts H.
  apply Bool.orb_true_intro.
  left.
  apply Zbool.Zeq_is_eq_bool.
  auto.
  simpl in *.
  apply Bool.orb_true_intro.
  right.
  eapply IHdls.
  eauto.
Qed.

Lemma gooddecl_neq: 
  forall i t dls n id,
    good_decllist (dcons i t dls)=true -> nth_id n dls = Some id -> 
    Zbool.Zeq_bool id i = false.
Proof.
  intros.
  simpl in H.
  apply andb_prop in H.
  destruct H.
  remember (Zbool.Zeq_bool id i) as b.
  destruct b.
  symmetry in Heqb.
  apply Zbool.Zeq_bool_eq in Heqb.
  inverts Heqb.
  apply nth_id_Some_imply_in_decllist in H0.
  rewrite H0 in H.
  tryfalse.
  auto.
Qed.


Lemma struct_rm_update_eq:
  forall s b i decl vl id v vi n,
    good_decllist decl =true -> nth_id n decl = Some id -> nth_val n vl = Some vi -> s |= Astruct_rm (b,i) decl vl id -> s |= Astruct_rm (b,i) decl (update_nth_val n vl v) id.
Proof.
  intros.
  generalize dependent s.
  generalize dependent b.
  generalize dependent i.
  generalize dependent vi.
  generalize dependent n.
  generalize dependent vl.
  generalize dependent id.
  generalize dependent v.
  induction decl.
  intros.
  destruct n;tryfalse.
  intros.
  destruct vl.
  destruct n;tryfalse.
  destruct n.
  simpl.
  simpl in H.
  inverts H.
  simpl in H0;inverts H0.
  assert (Zbool.Zeq_bool id id=true).
  apply Zbool.Zeq_is_eq_bool;auto.
  rewrite H.
  simpl in H1.
  inverts H1.
  simpl in H2.
  rewrite H in H2.
  auto.
  simpl.
  assert (Zbool.Zeq_bool id i = false).
  eapply gooddecl_neq;eauto.
  rewrite H3.
  simpl in H2.
  rewrite H3 in H2.
  inverts H0.
  inverts H1.
  destruct t;sep_auto;
  simpl in H;
  apply Bool.andb_true_iff  in H;
  destruct H;
  lets IH: IHdecl H0;clear IHdecl;
  lets IH':IH H5 H4;
  eapply IH' in H2;eauto.
Qed.

Lemma array_rm_update_eq': forall s b i vl v vi n m t,  m < n -> nth_val m vl = Some vi -> s |= Aarray_rm (b,i) n t (update_nth_val m vl v) m  -> s |= Aarray_rm (b,i) n t vl m.
Proof.
  intros.
  generalize dependent s.
  generalize dependent b.
  generalize dependent i.
  generalize dependent vi.
  generalize dependent n.
  generalize dependent vl.
  generalize dependent v.
  induction m.
  intros.
  destruct vl;tryfalse.
  simpl in H0;inverts H0.
  simpl in *.
  auto.
  intros.
  destruct n;tryfalse.
  omega.
  destruct vl;tryfalse.
  simpl in H0.
  assert (m<n).
  omega.
  unfold Aarray_rm;fold Aarray_rm.
  lets IH:IHm H2 H0.
  unfold update_nth_val in H1;fold update_nth_val in H1.
  unfold Aarray_rm in H1;fold Aarray_rm in H1.
  sep_auto.
  apply IH.
  eauto.
Qed.
(*
Lemma arrayelem_asrt_impl_g: 
  forall n m p p' b i t e2 x te2, 
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    p <==>
      (A_notin_lenv x ** Agvarenv x (Tarray t n) (addrval_to_addr (b, i))) ** p' ->
    p ==> Rv e2 @ te2 == Vint32 (Int.repr (BinInt.Z.of_nat m)) ->
    p ==>
      (Lv (earrayelem (evar x) e2) @ t == (b,Int.add i (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))  (Int.repr (BinInt.Z.of_nat m))))).
Proof.
  introv Ht.
  intros.
  destruct H with s.
  destruct H0 with s;auto.
  clear H H0.
  apply H2 in H1.
  clear H2 H3.
  destruct H5.
  destruct s as [[]].
  destruct t0 as [[[[]]]].
  simpl in *;mytac.
  apply EnvMod.nindom_get in H11.
  rewrite H11.
  rewrite H12.
  rewrite H4.
  rewrite <- Int.unsigned_zero in H3.
  apply aux_for_hoare_lemmas.unsigned_zero in H3.
  subst i.
  auto.
  apply EnvMod.nindom_get in H11.
  rewrite H11.
  rewrite H12.
  rewrite H.
  simpl in H3.
  simpl in *.
  destruct Ht;subst;auto.
  destruct H1;subst;auto.
Qed.
 *)


Lemma int_count_eq: forall i t m, Int.add (Int.add i (Int.repr (BinInt.Z.of_nat (typelen t))))
                                          (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                                   (Int.repr (BinInt.Z.of_nat m))) =  Int.add i
                                                                                              (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                                                                                       (Int.repr (BinInt.Z.of_nat (S m)))).
Proof.
  intros.
  rewrite Int.add_assoc.
  assert ((Int.repr (Z.of_nat (S m))) = Int.add (Int.repr (Z.of_nat m)) Int.one).
  assert (S m = m + 1).
  omega.
  rewrite H.
  rewrite Nat2Z.inj_add.
  simpl.
  unfold Int.add.
  rewrite Int.unsigned_one.
  rewrite Int.unsigned_repr_eq.
  assert (1 = 1 mod Int.modulus)%Z.
  compute.
  auto.
  rewrite H0 at 2.
  apply Int.eqm_samerepr.
  unfold Int.eqm.
  apply Int.eqmod_add.
  apply Int.eqmod_mod.
  compute.
  auto.
  apply Int.eqmod_mod.
  compute.
  auto.
  rewrite H.
  rewrite Int.mul_add_distr_r.
  rewrite Int.mul_one.
  replace (Int.add (Int.repr (Z.of_nat (typelen t)))
                   (Int.mul (Int.repr (Z.of_nat (typelen t))) (Int.repr (Z.of_nat m)))) with
  (Int.add
     (Int.mul (Int.repr (Z.of_nat (typelen t))) (Int.repr (Z.of_nat m)))
     (Int.repr (Z.of_nat (typelen t)))).
  auto.
  rewrite Int.add_commut.
  auto.
Qed.


Lemma array_asrt_eq: 
  forall n vl b i v t m,
    m < n ->
    nth_val m vl = Some v ->
    Aarray' (b,i) n t vl <==> PV (b,Int.add i (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) (Int.repr (BinInt.Z.of_nat m)))) @ t |-> v ** (Aarray_rm (b,i) n t vl m).
Proof.
  intros.
  generalize dependent s.
  generalize dependent b.
  generalize dependent i.
  generalize dependent n.
  generalize dependent m.
  induction vl.
  intros.
  destruct m;tryfalse.
  intros.
  destruct m;  
    simpl in H0;inverts H0.
  destruct n.
  inverts H.
  unfold Aarray_rm.
  unfold Aarray';fold Aarray'.
  assert(Int.repr (BinInt.Z.of_nat 0)=Int.zero).
  auto.
  rewrite H0.
  rewrite Int.mul_zero.
  rewrite Int.add_zero.
  split;intros;auto.
  lets IH: IHvl H2.
  destruct n.
  inversion H.
  assert (m<n).
  omega.
  lets IH': IH H0.
  unfold Aarray';fold Aarray'.
  unfold Aarray_rm;fold Aarray_rm.
  clear IH.
  assert (Int.add (Int.add i (Int.repr (BinInt.Z.of_nat (typelen t))))
                  (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                           (Int.repr (BinInt.Z.of_nat m))) =  Int.add i
                                                                      (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                                                               (Int.repr (BinInt.Z.of_nat (S m))))).
  apply int_count_eq.
  assert ( Aarray' (b, (Int.add i (Int.repr (BinInt.Z.of_nat (typelen t))))) n t vl <==>
                   PV (b,
                       Int.add (Int.add i (Int.repr (BinInt.Z.of_nat (typelen t))))
                               (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t)))
                                        (Int.repr (BinInt.Z.of_nat m)))) @ t |-> v **
                   Aarray_rm (b, (Int.add i (Int.repr (BinInt.Z.of_nat (typelen t))))) n t vl m).
  apply IH'.
  clear IH'.
  split;intros;  sep_auto;  destruct H3 with s.
  apply H5 in H4.
  rewrite <- H1;sep_auto.
  rewrite <- H1 in H4.
  apply H6;sep_auto.
Qed.


Lemma gooddecl_gettype: 
  forall i t dls n t' id,
    good_decllist (dcons i t dls)=true -> nth_id n dls = Some id -> ftype id (dcons i t dls) = Some t' -> ftype id dls = Some t'.
Proof.
  intros.
  simpl in *.
  apply andb_prop in H.
  destruct H.
  remember (Zbool.Zeq_bool id i) as b.
  destruct b.
  symmetry in Heqb.
  apply Zbool.Zeq_bool_eq in Heqb.
  rewrite Heqb in H0.
  inverts Heqb.
  apply nth_id_Some_imply_in_decllist in H0.
  rewrite H0 in H.
  tryfalse.
  auto.
Qed.

Close Scope Z_scope.
Open Scope nat_scope.

Lemma id_nth_ge:forall decl n id m, id_nth' id decl n = Some m -> m>=n.
Proof.
  intros.
  generalize dependent n.
  generalize dependent m.
  induction decl.
  intros.
  simpl in H.
  false.
  intros.
  simpl in H.
  assert (Zbool.Zeq_bool id i =true \/ Zbool.Zeq_bool id i = false).
  destruct (Zbool.Zeq_bool id i).
  left;auto.
  right;auto.
  destruct H0.
  rewrite H0 in H.
  inverts H.
  omega.
  rewrite H0 in H.
  assert (m>= S n).
  eapply IHdecl;eauto.
  omega.
Qed.

Lemma id_nth'_suc: forall id decl n m, id_nth' id decl (S n) = Some (S m) -> 
                                       id_nth' id decl n = Some m .
Proof.
  intros.
  generalize dependent n.
  generalize dependent m.
  induction decl.
  intros.
  simpl in H.
  false.
  intros.
  simpl in *.
  assert (Zbool.Zeq_bool id i =true \/ Zbool.Zeq_bool id i = false).
  destruct (Zbool.Zeq_bool id i).
  left;auto.
  right;auto.
  destruct H0.
  rewrite H0 in *.
  inversion H.
  auto.
  rewrite H0 in *.
  apply IHdecl;auto.
Qed.

Lemma id_nth_eq: 
  forall n id decl, 
    good_decllist decl = true -> id_nth id decl = Some n -> nth_id n decl = Some id.
Proof.
  intros.
  generalize dependent id.
  generalize dependent n.
  induction decl.
  intros.
  simpl in *.
  unfold id_nth in H0.
  simpl in H0.
  false.
  intros.
  destruct n.
  simpl in *.
  clear IHdecl.
  unfold id_nth in H0.
  simpl in H0.
  assert (Zbool.Zeq_bool id i =true \/ Zbool.Zeq_bool id i = false).
  destruct (Zbool.Zeq_bool id i).
  left;auto.
  right;auto.
  destruct H1;rewrite H1 in H0.
  apply Zbool.Zeq_bool_eq in H1.
  subst;auto.
  apply id_nth_ge in H0.
  omega.
  simpl.
  apply IHdecl.
  simpl in H.
  apply  Bool.andb_true_iff in H.
  destruct H;auto.
  unfold id_nth in *.
  simpl in H0.
  assert (Zbool.Zeq_bool id i =true \/ Zbool.Zeq_bool id i = false).
  destruct (Zbool.Zeq_bool id i).
  left;auto.
  right;auto.
  destruct H1.
  rewrite H1 in H0.
  inverts H0.
  rewrite H1 in H0.
  eapply id_nth'_suc;eauto.
Qed.


Lemma up_val_op_ex: forall vl v n vl' , update_nth_val_op n vl v = Some vl' -> update_nth_val n vl v = vl'  /\ (exists vi, nth_val n vl = Some vi).
Proof.
  intros.
  unfold update_nth_val_op in H.
  destruct (NPeano.Nat.ltb n (length vl)) eqn : eq1; tryfalse.
  inversion H; clear H.
  split.
  auto.
  gen v n vl'.
  inductions vl; intros.
  simpl in H1.
  substs.
  simpl in eq1.
  destruct n; simpl in eq1; tryfalse.
  simpl.
  destruct n.
  eauto.
  simpl in eq1.
  unfold NPeano.Nat.ltb in eq1.
  unfold NPeano.Nat.ltb in eq1.
  simpl in eq1.
  destruct (length vl) eqn : eq2.
  inversion eq1.
  simpl in H1.
  destruct (update_nth_val n vl v) eqn : eq3.
  eapply IHvl.
  auto.
  eapply eq3.
  eapply IHvl.
  auto.
  eapply eq3.
Qed.


Lemma eval_type_addr_eq : forall e ge le m t, evaltype (eaddrof e) (ge, le, m) = Some (Tptr t) -> evaltype e (ge, le, m) = Some t.
Proof.
  intros.
  simpl in *;destruct e;tryfalse;auto.
  destruct (evaltype (evar v) (ge, le, m));tryfalse.
  inversion H;auto.
  simpl.
  destruct (evaltype e (ge, le, m));tryfalse.
  destruct t0;tryfalse.
  inversion H;auto.
  destruct (evaltype (efield e i) (ge, le, m));tryfalse.
  inversion H;auto.
  destruct (evaltype (earrayelem e1 e2) (ge, le, m));tryfalse.
  inversion H;auto.
Qed.

Lemma eval_addr_eq: forall e ge le m b i, evalval (eaddrof e) (ge, le, m) = Some (Vptr (b, i)) -> evaladdr e (ge,le,m) = Some (Vptr (b,i)).
Proof.
  intros.
  simpl in *.
  destruct e;tryfalse.
  destruct (evaltype (evar v) (ge, le, m));tryfalse;auto.
  destruct (evaltype e (ge, le, m));tryfalse;auto.
  destruct t;tryfalse;auto.
  destruct (evaltype (efield e i0) (ge, le, m));tryfalse;auto.
  destruct (evaltype (earrayelem e1 e2) (ge, le, m));tryfalse;auto.
Qed.

Lemma gooddecl_off_add: 
  forall i t dls n  id off,
    good_decllist (dcons i t dls)=true -> nth_id n dls = Some id -> 
    field_offset id (dcons i t dls) = Some off ->
    exists off', field_offset id dls = Some off' /\ Int.add (Int.repr (BinInt.Z_of_nat (typelen t))) off'= off.
Proof.
  intros.
  unfolds in H1.
  simpl in H1.
  destruct (Zbool.Zeq_bool id i) eqn : eq1.
  inversion H1.
  substs.
  simpl in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.negb_true_iff in H.
  apply Zbool.Zeq_bool_eq in eq1.
  substs.
  clear H1.
  false.
  gen i t n.
  induction dls; intros.
  simpl in H0.
  inversion H0.
  destruct n.
  simpl in H0.
  inversion H0.
  substs.
  simpl in H.
  apply Bool.orb_false_iff in H.
  destruct H.
  assert (Zbool.Zeq_bool i0 i0 = true).
  apply Zbool.Zeq_is_eq_bool.
  auto.
  rewrite H3 in H.
  inversion H.
  eapply IHdls.
  simpl in H2.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  apply Bool.negb_true_iff in H1.
  auto.
  simpl in H.
  apply Bool.orb_false_iff in H.
  destruct H.
  eapply H1.
  auto.
  simpl in H0.
  eapply H0.

  destruct n.
  destruct dls.
  simpl in H0.
  inversion H0.
  simpl in H0.
  inversion H0.
  substs.
  simpl in H1.
  assert (Zbool.Zeq_bool id id = true).
  apply Zbool.Zeq_is_eq_bool.
  auto.
  rewrite H2 in H1.
  inversion H1.
  exists Int.zero.
  split.
  unfolds.
  simpl.
  rewrite H2.
  auto.
  auto.
  destruct dls.
  simpl in H0.
  inversion H0.
  simpl in H0.
  simpl in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.negb_true_iff in H.
  apply Bool.orb_false_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  apply Bool.negb_true_iff in H2.
  simpl in H1.



  apply nth_id_some_in_decllist_true in H0.
  destruct (Zbool.Zeq_bool id i0) eqn : eq2.
  apply Zbool.Zeq_is_eq_bool in eq2.
  substs.
  false.
  pose proof in_decllist_field_offsetfld_some dls id H0.
  pose proof H5 (Int.add (Int.repr (BinInt.Z.of_nat (typelen t0))) Int.zero).
  destruct H6.
  unfold field_offset.
  simpl.
  rewrite eq2.
  exists x.
  split.
  auto.
  pose proof field_offsetfld_pos_mono dls id H6 H1.
  apply H7.
  apply Int.add_permut.
Qed.


Lemma struct_asrt_eq: 
  forall n dls vl id off b i v t,
    (forall ids dl, t <> Tstruct ids dl)->
    (forall t' n, t <> Tarray t' n)->
    nth_id n dls = Some id ->
    nth_val n vl = Some v ->
    ftype id dls = Some t ->
    good_decllist dls = true ->
    field_offset id dls = Some off -> 
    Astruct' (b,i) dls vl <==> PV (b,Int.add i off) @ t |-> v ** (Astruct_rm (b,i) dls vl id).
Proof.
  introv Hstr.
  introv Harr.
  intros.
  generalize dependent s.
  generalize dependent b.
  generalize dependent i.
  generalize dependent n.
  generalize dependent vl.
  generalize dependent id.
  generalize dependent off.
  generalize dependent t.
  induction dls.
  intros.
  destruct n;tryfalse.
  rename t into t0.
  intros.
  assert(good_decllist dls=true).
  simpl in H2.
  apply Bool.andb_true_iff  in H2.
  destruct H2;auto.
  lets IH : IHdls H4.
  clear IHdls.
  destruct n.
  simpl in H.
  inverts H.
  destruct vl;tryfalse.
  simpl in H0.
  inverts H0.
  unfold Astruct_rm;fold Astruct_rm.
  assert (Zbool.Zeq_bool id id=true).
  apply Zbool.Zeq_is_eq_bool;auto.
  rewrite H.
  simpl in H1.
  rewrite H in H1.
  inverts H1.
  unfold Astruct';fold Astruct'.

  assert(Int.add i0 Int.zero = i0).
  apply Int.add_zero;auto.

  destruct t;auto;tryfalse;
  unfold field_offset in H3;
  simpl in H3;
  rewrite H in H3;
  inverts H3;
  rewrite H0;auto;
  splits;auto.
  simpl in H.
  destruct vl.
  simpl in H0;tryfalse.
  simpl in H0.
  lets Hft: gooddecl_gettype H2 H H1.
  lets Hoff: gooddecl_off_add H2 H H3.
  destruct Hoff.
  destruct H5.
  lets IHn: IH Hft H5;clear IH.
  auto.
  auto.
  lets IHn': IHn H H0.
  clear IHn.
  unfold Astruct';fold Astruct'.
  unfold Astruct_rm;fold Astruct_rm.
  assert(Zbool.Zeq_bool id i=false).
  eapply gooddecl_neq;eauto.
  rewrite H7.
  lets IH:IHn' (Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen t0)))) b.
  clear IHn'.

  assert (Int.add (Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen t0)))) x = Int.add i0 (Int.add (Int.repr (BinInt.Z.of_nat (typelen t0))) x)).
  apply Int.add_assoc;auto.
  rewrite H8 in IH.
  rewrite H6 in IH.
  destruct t0.
  eapply insert_star with (p:=Astruct' (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen Tnull)))) dls
                                       vl) (r:=Astruct_rm (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen Tnull))))
                                                          dls vl id) (l:=PV (b, i0) @ Tnull |-> v0 ) (q:=PV (b, Int.add i0 off) @ t |-> v) (s:=s);eauto.
  eapply insert_star with (p:=Astruct' (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen Tvoid)))) dls
                                       vl) (r:=Astruct_rm (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen Tvoid))))
                                                          dls vl id) (l:=PV (b, i0) @ Tvoid |-> v0 ) (q:=PV (b, Int.add i0 off) @ t |-> v) (s:=s);eauto.
  eapply insert_star with (p:=Astruct' (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen Tint8)))) dls
                                       vl) (r:=Astruct_rm (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen Tint8))))
                                                          dls vl id) (l:=PV (b, i0) @ Tint8 |-> v0 ) (q:=PV (b, Int.add i0 off) @ t |-> v) (s:=s);eauto.
  eapply insert_star with (p:=Astruct' (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen Tint16)))) dls
                                       vl) (r:=Astruct_rm (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen Tint16))))
                                                          dls vl id) (l:=PV (b, i0) @ Tint16 |-> v0 ) (q:=PV (b, Int.add i0 off) @ t |-> v) (s:=s);eauto.
  eapply insert_star with (p:=Astruct' (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen Tint32)))) dls
                                       vl) (r:=Astruct_rm (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen Tint32))))
                                                          dls vl id) (l:=PV (b, i0) @ Tint32 |-> v0 ) (q:=PV (b, Int.add i0 off) @ t |-> v) (s:=s);eauto.
  eapply insert_star with (p:=Astruct' (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen (Tptr t0))))) dls
                                       vl) (r:=Astruct_rm (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen (Tptr t0)))))
                                                          dls vl id) (l:=PV (b, i0) @ (Tptr t0) |-> v0 ) (q:=PV (b, Int.add i0 off) @ t |-> v) (s:=s);eauto.
  eapply insert_star with (p:=Astruct' (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen (Tcom_ptr i1))))) dls
                                       vl) (r:=Astruct_rm (b, Int.add i0 (Int.repr (BinInt.Z.of_nat (typelen (Tcom_ptr i1)))))
                                                          dls vl id) (l:=PV (b, i0) @ (Tcom_ptr i1) |-> v0 ) (q:=PV (b, Int.add i0 off) @ t |-> v) (s:=s);eauto.
  unfold Astruct';fold Astruct'.
  destruct IH with s.
  splits;auto.
  destruct IH with s.
  splits;auto.
Qed.


(*---------------------------------------*)

(** sep get rv *)

Theorem lvar_to_lv : 
  forall x l t P,
    L& x @ t == l ** P ==> Lv (evar x) @ t == l.
Proof.
  intros.
  destruct s as [ [ [ [ [ [ ] ] ] ] ] ]; simpl in *; mytac.
  rewrite H3; auto.
  cut (l = (x6, Int.zero)).
  intros; subst l; auto.
  destruct l; simpl in H5.
  inversion H5.
  assert (Int.repr (Int.unsigned i0) = i0) by apply Int.repr_unsigned.
  rewrite <- H.
  rewrite H1.
  auto.
  rewrite H3; auto.
Qed.

Theorem gvar_to_lv : 
  forall x l t P,
    A_notin_lenv x ** G& x @ t == l ** P ==> Lv (evar x) @ t == l.
Proof.
  intros.
  destruct s as [ [ [ [ [ [ ] ] ] ] ] ]; simpl in *; mytac.
  unfold get in H8.
  simpl in H8.
  apply EnvMod.nindom_get in H3.
  change ( (fun xxx =>
              match xxx with
                | Some (a0, _) => Some (Vptr (a0, Int.zero))
                | None =>
                  match get e x with
                    | Some (a0, _) => Some (Vptr (a0, Int.zero))
                    | None => None
                  end
              end = Some (Vptr l)
           ) (get e0 x)).
  rewrite H3.
  change (( fun xx =>    match xx with
                           | Some (a0, _) => Some (Vptr (a0, Int.zero))
                           | None => None
                         end = Some (Vptr l)
          ) (get e x)).
  rewrite H8; auto.
  cut (l = (x12, Int.zero)).
  intros; subst l; auto.
  destruct l; simpl in H10.
  inversion H10.
  assert (Int.repr (Int.unsigned i0) = i0) by apply Int.repr_unsigned.
  rewrite <- H.
  rewrite H1.
  auto.
  apply EnvMod.nindom_get in H3.
  rewrite H8.
  unfold get.
  simpl.
  rewrite H3.
  auto.
Qed.

Lemma rule_type_val_match_nvundef:
  forall v t, rule_type_val_match t v = true -> v<> Vundef.
Proof.
  intros.
  destruct v,t;auto; tryfalse; intro; tryfalse.
Qed.

Lemma lv_mapsto_to_rv :
  forall l t e s P v perm, 
    rule_type_val_match t v = true ->
    (*v <> Vundef ->*)
    s |= Lv e @ t == l ->
    s |=  (addrval_to_addr l)  # t |=> v @ perm ** P ->
    s |= Rv e @ t == v.
Proof.
  introv H.
  assert (v<>Vundef).
  eapply rule_type_val_match_nvundef;eauto.
  intros.
  destruct s as [[]].
  destruct t0 as [[[[]]]].
  simpl in *;mytac;auto.
  destruct e;simpl in *;auto;tryfalse.
  destruct (get e1 v0).
  destruct p.
  destruct t0;inverts H1;inverts H9;eapply mapstoval_loadbytes in H6;eauto;destruct H6;destruct H1; unfold load;unfold loadm.

  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1;
  assert (loadbytes m (b, BinNums.Z0) (typelen Tnull) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.


  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen Tvoid) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.


  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen Tint8) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.

  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen Tint16) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.

  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen Tint32) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.

  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen (Tptr t0)) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.

  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen (Tcom_ptr i0)) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.

  unfold decode_val in H2.
  destruct (proj_bytes x1) in H2;false.


  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen (Tstruct i0 d)) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.

  destruct (get e0 v0).
  destruct p.
  destruct t0;inverts H1;inverts H9;eapply mapstoval_loadbytes in H6;eauto;destruct H6;destruct H1;unfold load ;unfold loadm.

  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1;
  assert (loadbytes m (b, BinNums.Z0) (typelen Tnull) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.

  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen Tvoid) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.


  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen Tint8) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.

  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen Tint16) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.

  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen Tint32) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.

  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen (Tptr t0)) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.


  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen (Tcom_ptr i0)) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.

  unfold decode_val in H2.
  destruct (proj_bytes x1) in H2;false.

  eapply loadbytes_local in H1;eauto;rewrite Int.unsigned_zero in H1.
  assert (loadbytes m (b, BinNums.Z0) (typelen (Tstruct i0 d)) = Some x1);auto;
  rewrite H4;
  rewrite H2;auto.

  false.

  destruct (evaltype e (e0, e1, m)).
  destruct t0;tryfalse.
  inverts H9.
  rewrite H1.


  destruct l.
  simpl in *.
  apply mapstoval_loadbytes in H6.
  destruct H6.
  destruct H2.
  eapply loadbytes_local in H2;eauto.

  unfold load;unfold loadm.
  assert ( loadbytes m (b, Int.unsigned i0) (typelen t) = Some x1);auto.
  rewrite H5.
  rewrite H4;auto.
  destruct t;auto.
  simpl in H;tryfalse.
  auto.
  false.

  destruct (evaltype e (e0, e1, m) );tryfalse.
  destruct t0;tryfalse;auto.
  rewrite H9.
  destruct ( evaladdr e (e0, e1, m) );tryfalse;auto.
  destruct v0;auto;tryfalse.
  destruct a0.
  destruct (getoff b (Int.unsigned i2) i0 e (e0, e1, m));auto;tryfalse.
  inverts H1.
  destruct l;simpl in *.
  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H1.
  eapply loadbytes_local in H1;eauto.
  assert ( loadbytes m (b0, Int.unsigned i3) (typelen t) = Some x1);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H2;auto.
  destruct t;auto.
  simpl in H;tryfalse.

  destruct (evaltype e2 (e0, e1, m));auto;tryfalse.
  destruct t0;auto;tryfalse.
  destruct (evaltype e3 (e0, e1, m));auto;tryfalse.
  destruct t1;auto;tryfalse.
  destruct (evalval e2 (e0, e1, m));auto;tryfalse.
  inverts H9.
  destruct v0;auto;tryfalse.
  destruct a0.
  destruct ( evalval e3 (e0, e1, m) );auto;tryfalse.
  destruct v0;auto;tryfalse.
  inverts H1.
  simpl in *.

  apply mapstoval_loadbytes in H6.
  destruct H6.
  destruct H1.
  eapply loadbytes_local in H1;eauto.
  assert (loadbytes m
                    (b,
                     Int.unsigned
                       (Int.add i0 (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) i1)))
                    (typelen t) = Some x1);auto.
  unfold load ;unfold loadm.
  rewrite H4.
  rewrite H2;auto.
  auto.

  destruct t;auto.
  simpl in H;tryfalse.
  auto.

  inverts H9.
  destruct (evalval e2 (e0, e1, m));auto;tryfalse.
  destruct v0;auto;tryfalse.
  destruct a0.
  destruct ( evalval e3 (e0, e1, m) );auto;tryfalse.
  destruct v0;auto;tryfalse.
  inverts H1.
  simpl in *.

  apply mapstoval_loadbytes in H6.
  destruct H6.
  destruct H1.
  eapply loadbytes_local in H1;eauto.
  assert (loadbytes m
                    (b,
                     Int.unsigned
                       (Int.add i0 (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) i1)))
                    (typelen t) = Some x1);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H2;auto.

  destruct t;auto.
  simpl in H;tryfalse.
  auto.

  inverts H9.
  destruct (evalval e2 (e0, e1, m));auto;tryfalse.
  destruct v0;auto;tryfalse.
  destruct a0.
  destruct ( evalval e3 (e0, e1, m) );auto;tryfalse.
  destruct v0;auto;tryfalse.
  inverts H1.
  simpl in *.

  apply mapstoval_loadbytes in H6.
  destruct H6.
  destruct H1.
  eapply loadbytes_local in H1;eauto.
  assert (loadbytes m
                    (b,
                     Int.unsigned
                       (Int.add i0 (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) i1)))
                    (typelen t) = Some x1);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H2;auto.

  destruct t;auto.
  simpl in H;tryfalse.
  auto.

  destruct (evaltype e3 (e0, e1, m));auto;tryfalse.
  destruct t1;auto;tryfalse.
  destruct (evalval e2 (e0, e1, m));auto;tryfalse.
  inverts H9.
  destruct v0;auto;tryfalse.
  destruct a0.
  destruct ( evalval e3 (e0, e1, m) );auto;tryfalse.
  destruct v0;auto;tryfalse.
  inverts H1.
  simpl in *.

  apply mapstoval_loadbytes in H6.
  destruct H6.
  destruct H1.
  eapply loadbytes_local in H1;eauto.
  assert (loadbytes m
                    (b,
                     Int.unsigned
                       (Int.add i0 (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) i1)))
                    (typelen t) = Some x1);auto.
  unfold load ;unfold loadm.
  rewrite H4.
  rewrite H2;auto.
  auto.

  destruct t;auto.
  simpl in H;tryfalse.
  auto.

  inverts H9.
  destruct (evalval e2 (e0, e1, m));auto;tryfalse.
  destruct v0;auto;tryfalse.
  destruct a0.
  destruct ( evalval e3 (e0, e1, m) );auto;tryfalse.
  destruct v0;auto;tryfalse.
  inverts H1.
  simpl in *.

  apply mapstoval_loadbytes in H6.
  destruct H6.
  destruct H1.
  eapply loadbytes_local in H1;eauto.
  assert (loadbytes m
                    (b,
                     Int.unsigned
                       (Int.add i0 (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) i1)))
                    (typelen t) = Some x1);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H2;auto.

  destruct t;auto.
  simpl in H;tryfalse.
  auto.

  inverts H9.
  destruct (evalval e2 (e0, e1, m));auto;tryfalse.
  destruct v0;auto;tryfalse.
  destruct a0.
  destruct ( evalval e3 (e0, e1, m) );auto;tryfalse.
  destruct v0;auto;tryfalse.
  inverts H1.
  simpl in *.

  apply mapstoval_loadbytes in H6.
  destruct H6.
  destruct H1.
  eapply loadbytes_local in H1;eauto.
  assert (loadbytes m
                    (b,
                     Int.unsigned
                       (Int.add i0 (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) i1)))
                    (typelen t) = Some x1);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H2;auto.

  destruct t;auto.
  simpl in H;tryfalse.
  auto.

Qed.



Theorem cast_rv_tptr :
  forall s e v t1 t2,
    s |= Rv e @ (Tptr t1) == v ->
    rule_type_val_match (Tptr t1) v = true ->
    s |= Rv (ecast e (Tptr t2)) @ (Tptr t2) == v.
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  splits;auto.
  simpl.
  rewrite H1.
  simpl.
  auto.
  simpl.
  rewrite H1.
  auto.
Qed.

Theorem cast_rv_struct_tptr :
  forall s e v t1 t2,
    s |= Rv e @ (Tcom_ptr t1) == v ->
    rule_type_val_match (Tcom_ptr t1) v = true ->
    s |= Rv (ecast e (Tptr t2)) @ (Tptr t2) == v.
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  splits;auto.
  simpl.
  rewrite H1.
  simpl.
  auto.
  simpl.
  rewrite H1.
  auto.
Qed.

Theorem cast_rv_tnull :
  forall s e v t,
    s |= Rv e @ Tnull == v ->
    rule_type_val_match Tnull v = true ->
    s |= Rv (ecast e (Tptr t)) @ (Tptr t) == v.
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  splits;auto.
  simpl.
  rewrite H1.
  auto.
  simpl.
  rewrite H1.
  auto.
Qed.

Theorem cast_rv_ptr :
  forall (s : RstateOP) (e : expr) (v : val) t1  (t2 : type),
    s |= Rv e @ t1  == v ->
    rule_type_val_match t1 v = true ->
    (exists t1', t1 = Tcom_ptr t1' )  \/ (exists t1', t1 =  Tptr t1' ) \/ t1 = Tnull  ->
    s |= Rv (ecast e (Tptr t2))  @ (Tptr t2)  == v.
Proof.
  intros.
  destruct H1; simpljoin.
  eapply cast_rv_struct_tptr; eauto.
  destruct H1; simpljoin.
  eapply cast_rv_tptr; eauto.
  eapply cast_rv_tnull; eauto.
Qed.


Theorem cast_rv_tint32_tint8 :
  forall s e v v',
    s |= Rv e @ Tint32 == (Vint32 v) ->
    cast_eval v Tint32 Tint8 = Some v' ->
    s |= Rv (ecast e (Tint8)) @ (Tint8) == (Vint32 v').
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  splits;auto.
  simpl.
  rewrite H1.
  auto.
  simpl.
  rewrite H.
  simpl in H0.
  inverts H0.
  auto.
  simpl.
  rewrite H1.

  auto.
  intro; tryfalse.
Qed.


Theorem cast_rv_tint8_tint16 :
  forall s e v v',
    s |= Rv e @ Tint8 == (Vint32 v) ->
    cast_eval v Tint8 Tint16 = Some v' ->
    s |= Rv (ecast e (Tint16)) @ (Tint16) == (Vint32 v').
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  splits;auto.
  simpl.
  rewrite H1.
  simpl.
  rewrite H.
  simpl in H0.
  inverts H0.
  auto.
  simpl.
  rewrite H1.
  auto.
  intro; tryfalse.
Qed.

(*
Definition val_inj (v : option val) : val :=
  match v with
    | Some v' => v'
    | None => Vundef
  end.
*)


Theorem bop_rv :
  forall s bop e1 e2 v1 t1 v2 t2 v t,
    s |= Rv e1 @ t1 == v1 ->
    s |= Rv e2 @ t2 == v2 ->
    val_inj (bop_eval v1 v2 t1 t2 bop) = v ->
    v <> Vundef ->
    bop_type t1 t2 bop = Some t ->
    s |= Rv (ebinop bop e1 e2) @ t == v.
Proof.
  intros.
  destruct s as [ [ [ [ [ [ ] ] ] ] ] ].
  simpl in *; mytac; auto.
  rewrite H.
  rewrite H6.
  rewrite H4.
  rewrite H3.
  rewrite H0.
  destruct (bop_eval v1 v2 t1 t2 bop); simpl in H2; tryfalse.
  destruct v; tryfalse || auto.
  rewrite H6.
  rewrite H4.
  auto.
Qed.

Theorem uop_rv :
  forall s uop e v t v' t',
    s |= Rv e @ t == v ->
    val_inj (uop_eval v uop) = v' ->
    v' <> Vundef ->
    uop_type t uop = Some t' ->
    s |= Rv (eunop uop e) @ t' == v'.
Proof.
  intros.
  destruct s as [ [ [ [ [ [ ] ] ] ] ] ].
  simpl in *; mytac; auto.
  rewrite H.
  rewrite H3.
  rewrite H2.
  destruct (uop_eval v uop); simpl in H1; tryfalse.
  destruct v0; tryfalse || auto.
  rewrite H3.
  auto.
Qed.


Lemma nth_val_imp_nth_val'_1 :
  forall m vl,
    (Int.unsigned m < Z.of_nat (length vl))%Z ->
    nth_val (Z.abs_nat (Int.unsigned m)) vl = Some (nth_val' (Z.to_nat (Int.unsigned m)) vl).
Proof.
  intros.
  cut (exists n, m = Int.repr (Z.of_nat n) /\(0 <= Z.of_nat n <= Int.max_unsigned)%Z).
  intros; mytac.
  rewrite Int.unsigned_repr in H; auto.
  rewrite Int.unsigned_repr; auto.
  rewrite Zabs2Nat.id.
  rewrite Nat2Z.id.
  apply Nat2Z.inj_lt in H.
  gen H; clear; intros.
  gen vl x; induction vl, x; intros; simpl in *.
  omega.
  omega.
  auto.
  apply IHvl.
  omega.
  destruct m.
  exists (Z.to_nat intval).
  split.
  2 : rewrite Z2Nat.id.
  2 : unfold Int.max_unsigned; omega.
  2 : omega.
  rewrite Z2Nat.id.
  2 : omega.
  rewrite <- Int.repr_unsigned at 1.
  simpl; auto.
Qed.

Lemma nth_val_imp_nth_val'_2 :
  forall n vl,
    n < length vl ->
    nth_val n vl = Some (nth_val' n vl).
Proof.
  intros.
  gen vl n.
  induction vl, n; intros; simpl in *.
  omega.
  omega.
  auto.
  apply IHvl.
  omega.
Qed.

Theorem deref_rv :
  forall s e l t v' P perm,
    s |= Rv e @ Tptr t == Vptr l ->
    s |= PV l @ t |=> v' @ perm  ** P ->
    rule_type_val_match t v' = true ->
    (*  v' <> Vundef ->*)
    s |= Rv (ederef e) @ t == v'.
Proof.
  introv Hm.
  introv H.
  introv H0.
  assert (v'<>Vundef).
  eapply rule_type_val_match_nvundef;eauto.
  intros.
  destruct s as [[]].
  destruct t0 as [[[[]]]].
  simpl in *.
  mytac; auto.
  rewrite H9.
  rewrite H8.
  eapply mapstoval_load in H5; auto.
  eapply load_local ;eauto.
  rewrite H9; auto.
Qed.



Lemma array_type_vallist_match_imp_rule_type_val_match :
  forall vl n t,
    n < length vl ->
    array_type_vallist_match t vl ->
    rule_type_val_match t (nth_val' n vl) = true.
Proof.
  induction vl, n; intros; simpl in *; mytac.
  omega.
  omega.
  auto.
  apply IHvl; auto.
  omega.
Qed.

Lemma ge0_z_nat_le:
  forall z n,
    (0<=z)%Z ->
    (z < Z.of_nat n)%Z -> 
    ((Z.to_nat z) < n)%nat.
Proof.
  intros.
  rewrite <- Nat2Z.id.
  apply Z2Nat.inj_lt; omega.
Qed.


Lemma sub_mul_eq_add_mul:
  forall i i0 x n, 
    Int.sub i i0 = Int.mul x (Int.repr (Z.of_nat n)) ->
    (0 <= Int.unsigned i - Int.unsigned i0 <= Int.max_unsigned)%Z ->
    i = Int.add i0 (Int.mul (Int.repr (Z.of_nat n))
                            (Int.repr (Int.unsigned x))).
Proof.
  intros.
  rewrite Int.repr_unsigned.
  rewrite Int.mul_commut.
  rewrite <- H.
  unfold Int.add.
  unfold Int.sub.
  rewrite Int.unsigned_repr.
  assert (Int.unsigned i0 + (Int.unsigned i - Int.unsigned i0) = Int.unsigned i)%Z.
  omega.
  rewrite  H1.
  rewrite Int.repr_unsigned;auto.
  simpl.
  auto.
Qed.

Theorem deref_ptr_of_array_member_rv':
  forall P s t' t vl e i0 b i x v n,
    s |= Aarray (b,i0) t' vl ** P->
    t' = Tarray t n ->
    s |= Rv e @ (Tptr t)  == Vptr (b,i) ->
    Int.sub i i0 = Int.mul x (Int.repr (Z_of_nat (typelen t )))->
    (0 <= Int.unsigned i - Int.unsigned i0 <= 4294967295)%Z  ->
    (Z.of_nat n < 4294967295)%Z -> 
    (Int.unsigned x < Z.of_nat n)%Z ->
    (Int.unsigned x < Z.of_nat (length vl))%Z ->
    rule_type_val_match t v = true ->
    nth_val' (Z.to_nat (Int.unsigned x)) vl = v ->
    s |= Rv (ederef e) @ t == v.
Proof.
  intros.
  eapply deref_rv;eauto.
  instantiate (1:= Aarray_rm (b, i0) n t vl (Z.to_nat (Int.unsigned x)) ** P).
  lets H100:H.
  sep auto.
  unfold Aarray in H100.
  clear H1 H.
  apply array_asrt_eq with (v:=nth_val' (Z.to_nat (Int.unsigned x)) vl) (m:=((Z.to_nat (Int.unsigned x)))) in H100.

  2:eapply ge0_z_nat_le;eauto.
  Focus 2.
  lets H1000:Int.unsigned_range x.
  omega.
  Focus 2.
  rewrite <- Zabs2Nat.abs_nat_nonneg at 1.
  eapply nth_val_imp_nth_val'_1;eauto.
  lets H1000:Int.unsigned_range x.
  omega.
  sep auto.
  rewrite Z2Nat.id in H100.
  2:lets H1000:Int.unsigned_range x;
    omega.
  assert (i=Int.add i0
                    (Int.mul (Int.repr (Z.of_nat (typelen t)))
                             (Int.repr (Int.unsigned x)))).
  eapply sub_mul_eq_add_mul;eauto.
  subst i.
  eauto.
Qed.
(*
  subst v.
  apply array_type_vallist_match_imp_rule_type_val_match; auto.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id.
  auto.
  lets H100 : Int.unsigned_range x.
  omega.
Qed.
 *)
Lemma max_unsigned_val : Int.max_unsigned = 4294967295%Z.
Proof.
  auto.
Qed.

Lemma unsigned_minus_le_max :
  forall a b, 
    (Int.unsigned a - Int.unsigned b <= 4294967295)%Z.
Proof.
  intros.
  generalize (Int.unsigned_range_2 a).
  generalize (Int.unsigned_range_2 b).
  rewrite max_unsigned_val.
  intros; omega.
Qed.

Lemma sub_zero_eq :
  forall i1 i2,
    Int.sub i1 i2 = Int.zero ->
    i1 = i2.
Proof.
  intros.
  assert (Int.add (Int.sub i1 i2) i2 = Int.add Int.zero i2) as H100.
  rewrite H; auto.
  rewrite <- Int.sub_add_l in H100.
  assert (Int.sub (Int.add i1 i2) (Int.add Int.zero i2) = Int.add Int.zero i2) as H200.
  rewrite Int.add_zero_l at 1; auto.
  rewrite Int.sub_shifted in H200.
  rewrite Int.sub_zero_l in H200.
  rewrite Int.add_zero_l in H200.
  auto.
Qed.


Theorem deref_ptr_of_array_member_rv'' :
  forall P s t' t vl e l l' x v n,
    s |= Aarray l t' vl ** P->
    t' = Tarray t n ->
    (Z.of_nat n < 4294967295)%Z -> 
    s |= Rv e @ (Tptr t)  == Vptr l' ->
    typelen t <> 0 ->
    (Z.of_nat (typelen t) < 4294967295)%Z ->
    fst l = fst l' ->
    (Int.unsigned (snd l) <= Int.unsigned (snd l'))%Z ->
    Int.divu (Int.sub (snd l') (snd l)) (Int.repr (Z_of_nat (typelen t))) = x ->
    Int.modu (Int.sub (snd l') (snd l)) (Int.repr (Z_of_nat (typelen t))) = Int.zero ->
    (Int.unsigned x < Z.of_nat n)%Z ->
    (Int.unsigned x < Z.of_nat (length vl))%Z ->
    rule_type_val_match t v = true ->
    nth_val' (Z.to_nat (Int.unsigned x)) vl = v ->
    s |= Rv (ederef e) @ t == v.
Proof.
  intros.
  destruct l, l'.
  simpl fst in *; simpl snd in *; subst.
  eapply deref_ptr_of_array_member_rv'; eauto.
  Focus 2.
  split.
  apply Zle_minus_le_0; auto.
  apply unsigned_minus_le_max.
  remember (Int.repr (Z.of_nat (typelen t))) as x100.
  assert (x100 <> Int.zero) as H100.
  subst x100.
  clear - H3 H4.
  intro; apply H3.
  assert (Int.unsigned (Int.repr (Z.of_nat (typelen t))) = Int.unsigned Int.zero) as H100.
  rewrite H; auto.
  rewrite Int.unsigned_repr in H100.
  change (Int.unsigned Int.zero) with 0%Z in H100.
  apply Nat2Z.inj.
  auto.
  split.
  omega.
  change Int.max_unsigned with  4294967295%Z.
  omega.
  remember (Int.sub i0 i) as x200.
  clear Heqx100 Heqx200.
  lets H200 : Int.modu_divu x200 x100 H100.
  rewrite H8 in H200.
  apply sub_zero_eq; auto.
Qed.

Close Scope nat_scope.
Open Scope Z_scope.

Lemma Int_div_to_Z_div :
  forall i1 i2 z1 z2,
    (Int.unsigned i2 <= Int.unsigned i1)%Z ->
    (0 < z1)%Z ->
    (z1 < 4294967295)%Z ->
    (Int.unsigned i1 - Int.unsigned i2) / z1 = z2 ->
    Int.unsigned (Int.divu (Int.sub i1 i2) (Int.repr z1)) = z2.
Proof.
  intros.
  unfold Int.divu.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  unfold Int.sub.
  rewrite Int.unsigned_repr.
  auto.
  split.
  apply Zle_minus_le_0; auto.
  apply unsigned_minus_le_max.
  rewrite max_unsigned_val; omega.
  assert (Int.unsigned (Int.repr z1) >= 1)%Z as H100.
  rewrite Int.unsigned_repr; auto.
  omega.
  rewrite max_unsigned_val; omega.
  split.
  apply Z.div_pos.
  remember (Int.sub i1 i2); clear; int auto.
  omega.
  apply Z.div_le_upper_bound.
  omega.
  assert (1 * Int.max_unsigned <= Int.unsigned (Int.repr z1) * Int.max_unsigned)%Z as H200.
  apply Z.mul_le_mono_nonneg_r.
  clear; int auto.
  omega.
  assert (Int.unsigned (Int.sub i1 i2) <= 1 * Int.max_unsigned)%Z as H300.
  remember (Int.sub i1 i2); clear; int auto.
  eapply Z.le_trans; eauto.
Qed.

Lemma Int_modu_to_Z_mod :
  forall i1 i2 z1 z2,
    (Int.unsigned i2 <= Int.unsigned i1)%Z ->
    (0 < z1)%Z ->
    (z1 < 4294967295)%Z ->
    (0 <= z2)%Z ->
    (z2 <= 4294967295)%Z ->
    (Int.unsigned i1 - Int.unsigned i2) mod z1 = z2 ->
    Int.modu (Int.sub i1 i2) (Int.repr z1) = Int.repr z2.
Proof.
  intros.
  unfold Int.modu.
  rewrite Int.unsigned_repr.
  2 : int auto.
  unfold Int.sub.
  rewrite Int.unsigned_repr.
  Focus 2.
  split.
  apply Zle_minus_le_0; auto.
  apply unsigned_minus_le_max.
  apply unsigned_inj.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  auto.
  int auto.
  lets H100 : Z_mod_lt (Int.unsigned i1 - Int.unsigned i2)%Z z1.
  int auto.
Qed.

Open Scope nat_scope.

Theorem deref_ptr_of_array_member_rv''' :
  forall P s t' t vl e l l' x v n,
    s |= Aarray l t' vl ** P->
    t' = Tarray t n ->
    (Z.of_nat n < 4294967295)%Z -> 
    s |= Rv e @ (Tptr t)  == Vptr l' ->
    typelen t <> 0 ->
    fst l = fst l' ->
    (Z.of_nat (typelen t) < 4294967295)%Z ->
    fst l = fst l' ->
    (Int.unsigned (snd l) <= Int.unsigned (snd l'))%Z ->
    ((Int.unsigned (snd l') - Int.unsigned (snd l)) / (Z_of_nat (typelen t)) = x)%Z ->
    ((Int.unsigned (snd l') - Int.unsigned (snd l)) mod (Z_of_nat (typelen t)) = 0)%Z ->
    (x < Z.of_nat n)%Z ->
    (x < Z.of_nat (length vl))%Z ->
    rule_type_val_match t v = true ->
    nth_val' (Z.to_nat x) vl = v ->
    s |= Rv (ederef e) @ t == v.
Proof.
  intros.
  cut (x = Int.unsigned (Int.divu (Int.sub (snd l') (snd l)) (Int.repr (Z.of_nat (typelen t))))).
  intro H100.
  eapply deref_ptr_of_array_member_rv''; eauto.
  apply Int_modu_to_Z_mod; auto || omega.
  rewrite <- H100; auto.
  rewrite <- H100; auto.
  rewrite <- H100; auto.
  symmetry; apply Int_div_to_Z_div; auto.
  remember (typelen t) as len.
  clear - H3.
  omega.
Qed.

Theorem deref_ptr_of_array_member_rv :
  forall P s t' t vl e b i i' x v n,
    s |= Rv e @ (Tptr t)  == Vptr (b,i') ->
    s |= Aarray (b,i) t' vl ** P->
    t' = Tarray t n ->
    (Z.of_nat n < 4294967295)%Z ->    
    typelen t <> 0 ->
    (Z.of_nat (typelen t) < 4294967295)%Z ->
    (Int.unsigned i <= Int.unsigned i')%Z ->
    ((Int.unsigned i' - Int.unsigned i) / (Z_of_nat (typelen t)) = x)%Z ->
    (Z_of_nat (typelen t) * x = (Int.unsigned i' - Int.unsigned i))%Z ->
    (x < Z.of_nat n)%Z ->
    (x < Z.of_nat (length vl))%Z ->
    rule_type_val_match t v = true ->
    nth_val' (Z.to_nat x) vl = v ->
    s |= Rv (ederef e) @ t == v.
Proof.
  intros.
  eapply deref_ptr_of_array_member_rv'''; eauto.
  apply Z_div_exact_full_1; subst; auto.
Qed.

Theorem var_rv :
  forall s x t l v P perm,    
    s |= Rv (eaddrof (evar x)) @ Tptr t == Vptr l ->
    s |= PV l @ t |=> v  @ perm ** P ->
    (*v<>Vundef ->*)
    rule_type_val_match t v = true->
    s |= Rv (evar x) @ t == v.
Proof.
  introv H.
  introv H0.
  introv H2.
  assert(v<>Vundef).
  eapply rule_type_val_match_nvundef;eauto.

  destruct s as [[]].
  destruct t0 as [[[[]]]].
  simpl in *.
  destruct l.
  splits;auto.
  destruct (get e0 x);auto;tryfalse.
  destruct p.
  mytac.
  inverts H.
  inverts H9.
  simpl in H6.
  rewrite Int.unsigned_zero in H6.
  destruct t;auto;tryfalse.


  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H.
  eapply loadbytes_local in H;eauto.
  assert (loadbytes m (b, 0%Z) (typelen Tnull)=Some x2);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H0;auto.

  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H.
  eapply loadbytes_local in H;eauto.
  assert ( loadbytes m (b, BinNums.Z0) (typelen Tint8) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H0;auto.


  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H.
  eapply loadbytes_local in H;eauto.
  assert ( loadbytes m (b, BinNums.Z0) (typelen Tint16) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H0;auto.


  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H.
  eapply loadbytes_local in H;eauto.
  assert ( loadbytes m (b, BinNums.Z0) (typelen Tint32) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H0;auto.

  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H.
  eapply loadbytes_local in H;eauto.
  assert ( loadbytes m (b, BinNums.Z0) (typelen (Tptr t)) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H0;auto.


  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H.
  eapply loadbytes_local in H;eauto.
  assert ( loadbytes m (b, BinNums.Z0) (typelen (Tcom_ptr i0)) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H0;auto.



  destruct (get e x);auto;tryfalse.
  destruct p.
  mytac.
  inverts H.
  inverts H9.
  simpl in H6.
  rewrite Int.unsigned_zero in H6.
  destruct t;auto;tryfalse.

  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H.
  eapply loadbytes_local in H;eauto.
  assert ( loadbytes m (b, BinNums.Z0) (typelen Tnull) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H0;auto.

  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H.
  eapply loadbytes_local in H;eauto.
  assert ( loadbytes m (b, BinNums.Z0) (typelen Tint8) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H0;auto.


  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H.
  eapply loadbytes_local in H;eauto.
  assert ( loadbytes m (b, BinNums.Z0) (typelen Tint16) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H0;auto.


  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H.
  eapply loadbytes_local in H;eauto.
  assert ( loadbytes m (b, BinNums.Z0) (typelen Tint32) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H0;auto.

  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H.
  eapply loadbytes_local in H;eauto.
  assert ( loadbytes m (b, BinNums.Z0) (typelen (Tptr t)) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H0;auto.

  eapply mapstoval_loadbytes in H6;eauto.
  destruct H6.
  destruct H.
  eapply loadbytes_local in H;eauto.
  assert ( loadbytes m (b, BinNums.Z0) (typelen (Tcom_ptr i0)) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H4.
  rewrite H0;auto.

  destruct H;tryfalse.

  destruct (get e0 x).
  destruct p.
  mytac.
  inverts H9;auto.

  destruct ( get e x).
  destruct p.
  mytac.
  inverts H9;auto.

  mytac; tryfalse.
Qed.

(**
Axiom expr_struct_rv :
  forall s e t l id t' v' P,
    s |= Rv (eaddrof e) @ Tptr t == Vptr l ->
    s |= SP l @ t # id @ t' |-> v' ** P ->
    s |= Rv (efield e id) @ t' == v'.
 *)

Theorem addrof_deref_rv :
  forall s e t l,
    s |= Rv e @ (Tptr t) == (Vptr l) ->
    s |= Rv (eaddrof (ederef e)) @ (Tptr t) == (Vptr l).
Proof.
  intros.
  destruct s as [[]].
  destruct t0 as [[[[]]]].
  simpl in *.
  destruct H.
  destruct H0.
  rewrite H0.
  destruct t;auto;tryfalse.
Qed.



Theorem addrof_lvar_rv :
  forall s x t l P,
    s |= L& x @ t == l ** P ->
    s |= Rv (eaddrof (evar x)) @ Tptr t == Vptr l.
Proof.
  intros.
  destruct s as [[]].
  destruct t0 as [[[[]]]].
  simpl in *;mytac.
  rewrite H3.
  destruct l.
  simpl in H5.
  inverts H5.
  rewrite <- Int.unsigned_zero in H1.
  apply unsigned_inj in H1.
  subst.
  auto.
  rewrite H3.
  auto.
  intro.
  inverts H.
Qed.



Theorem addrof_array_elem_rv :
  forall s e1 e2 t1 t2 b i j t,
    s |= Rv e1 @ t1 == (Vptr (b,i)) ->
    s |= Rv e2 @ t2 == Vint32 j ->
    t2 = Tint8 \/ t2 = Tint16 \/ t2 = Tint32 ->
    (t1 = Tptr t \/ exists n, t1 = Tarray t n) ->
    s |= Rv (eaddrof (earrayelem e1 e2)) @ (Tptr t) == (Vptr (b,(Int.add i
                                                                         (Int.mul (Int.repr (Z.of_nat (typelen t))) j)))).
Proof.
  intros.
  destruct s as [[]].
  destruct t0 as [[[[]]]].
  destruct H2.

  simpl in *;mytac.
  rewrite H5.
  rewrite H0.
  rewrite H3.
  destruct t2;destruct H1;tryfalse;destruct H1;tryfalse.
  rewrite H.
  auto.
  rewrite H;auto.
  rewrite H;auto.
  rewrite H5.
  rewrite H3.
  destruct t2;destruct H1;tryfalse;destruct H1;tryfalse;auto.
  intro; tryfalse.

  simpl in *;mytac.
  rewrite H5.
  rewrite H0.
  rewrite H3.
  destruct t2;destruct H1;tryfalse;destruct H1;tryfalse.
  rewrite H.
  auto.
  rewrite H;auto.
  rewrite H;auto.
  rewrite H5.
  rewrite H3.
  destruct t2;destruct H1;tryfalse;destruct H1;tryfalse;auto.
  intro; tryfalse.
Qed.

Theorem lvar_rv :
  forall s x t v P perm,
    s |= LV x @ t |=> v @ perm ** P ->
    (* v <> Vundef ->*)
    rule_type_val_match t v = true ->
    s |= Rv (evar x) @ t == v.
Proof.
  intros.
  unfold Alvarmapsto in H.
  sep normal in H.
  sep_destruct H.
  eapply var_rv; auto.
  eapply addrof_lvar_rv.
  eauto.
  sep lift 2 in H; eauto.
Qed.

Theorem addrof_gvar_rv :
  forall s x t l P,
    s |= A_notin_lenv x ** G& x @ t == l ** P ->
    s |= Rv (eaddrof (evar x)) @ Tptr t == Vptr l.
Proof.
  intros.
  destruct s as [[]].
  destruct t0 as [[[[]]]].
  simpl in *;mytac.
  unfold get in *; simpl in *.
  lets H100 : EnvMod.nindom_get H3.
  rewrite H100.
  rewrite H8.
  destruct l.
  simpl in H10.
  inverts H10.
  rewrite <- Int.unsigned_zero in H1.
  apply unsigned_inj in H1.

  subst.
  auto.
  lets H100 : EnvMod.nindom_get H3.
  unfold get in *; simpl in *.
  rewrite H100.
  rewrite H8.
  auto.
  intro.
  inverts H.
Qed.

Theorem gvar_rv' :
  forall s x t v P perm,
    s |= A_notin_lenv x ** GV x @ t |=> v @ perm ** P ->
    (*v <> Vundef ->*)
    rule_type_val_match t v = true ->
    s |= Rv (evar x) @ t == v.
Proof.
  intros.
  unfold Agvarmapsto in H.
  sep normal in H; sep_destruct H.
  eapply var_rv; auto.
  eapply addrof_gvar_rv.
  sep lifts (3::1::nil)%list in H; eauto.
  sep lift 2 in H; eauto.
Qed.

Open Scope list_scope.

Fixpoint var_notin_dom (x:var) (l:edom) :=
  match l with
    | nil => true
    | (y,t)::l' => if BinInt.Z.eqb x y then false else (var_notin_dom x l')
  end.

Close Scope list_scope.

Lemma dom_lenv_imp_notin_lenv :
  forall l P x,
    var_notin_dom x l = true ->
    A_dom_lenv l ** P ==> A_notin_lenv x ** P.
Proof.
  intros.
  simpl in *; mytac.
  destruct_s s; simpl in *; mytac.
  do 6 eexists; mytac; eauto.
  unfold eq_dom_env in *.
  intro.
  apply EnvMod.indom_get in H0.
  mytac.
  destruct x0.
  assert (exists b, EnvMod.get e0 x = Some (b, t)) by eauto.
  apply H4 in H1.
  gen H H1; clear; intros.
  induction l; simpl in *.
  auto.
  destruct a.
  remember (BinInt.Z.eqb x v) as bool; destruct bool.
  tryfalse.
  symmetry in Heqbool; apply BinInt.Z.eqb_neq in Heqbool.
  destruct H1.
  inverts H0; tryfalse.
  lets IHl1 : IHl H H0; auto.
Qed.


Theorem gvar_rv :
  forall s x t v l P perm,
    s |= A_dom_lenv l ** GV x @ t |=> v @ perm ** P ->
    var_notin_dom x l = true ->
    (* v <> Vundef ->*)
    rule_type_val_match t v = true ->
    s |= Rv (evar x) @ t == v.
Proof.
  intros.
  eapply gvar_rv'; auto.
  eapply dom_lenv_imp_notin_lenv; eauto.
Qed.

Theorem null_rv :
  forall s,
    s |= Rv enull @ Tnull == Vnull.
Proof.
  intros.
  destruct s as [ [ [ [ [ [ ] ] ] ] ] ]; simpl.
  splits.
  auto.
  auto.
  intro; tryfalse.
Qed.

Theorem const_rv :
  forall s i,
    s |= Rv econst32 i @ Tint32 == Vint32 i.
Proof.
  intros.
  destruct s as [ [ [ [ [ [ ] ] ] ] ] ]; simpl.
  splits.
  auto.
  auto.
  intro; tryfalse.
Qed.

Lemma struct_member_rv':
  forall s x t l vl tid decl n id t' v P perm,
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    rule_type_val_match t' v =true->
    (*v<> Vundef ->*)
    good_decllist decl = true ->
    s |= LV x @ (Tptr t) |=> Vptr l @ perm ** Astruct l t vl ** P->
    t = Tstruct tid decl ->
    nth_id n decl = Some id ->
    ftype id decl = Some t' ->
    nth_val n vl = Some v ->
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  introv Hnstr.
  introv Hnarr.
  introv Htv.
  assert (v<> Vundef) as Hvn.
  eapply rule_type_val_match_nvundef;eauto.
  introv Hgooddecl.
  intros.
  destruct s as ((o&O)&aop).
  unfold sat in *;fold sat in *;mytac.
  unfold substmo in *.
  destruct o as [[[[]]]].
  unfold substaskst in *.
  unfold getsmem in *.
  unfold getmem in *.
  unfold get_smem in *.
  unfold get_mem in *.
  simpl in *;mytac.
  rewrite H8.
  rewrite H2.
  rewrite Int.unsigned_zero in H10.
  lets Hf: mapstoval_loadbytes H10.
  simpl;auto.
  destruct Hf.
  destruct H.
  lets Hf: loadbytes_local H4 H.
  assert ( loadbytes m (x15, BinNums.Z0) (typelen (Tptr (Tstruct tid decl))) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H5.
  rewrite H0.
  clear H.
  destruct l.
  unfold getoff.
  unfold evaltype.
  rewrite H8.
  lets Hoff: nth_id_exists_off H1.
  destruct Hoff.
  rewrite H.
  assert (load t' x6 (addrval_to_addr (b, Int.add (Int.repr (Int.unsigned i0)) x3)) =
          Some v).
  unfold addrval_to_addr.
  rewrite struct_asrt_eq with (n:=n) in H12;eauto.
  unfold sat in H12;fold sat in H12;mytac.
  simpl in H15.
  rewrite Int.repr_unsigned.
  simpl in H7.
  eapply load_local;eauto.
  eapply mapstoval_load;eauto.
  simpl;eauto.
  destruct H15;eauto.
  auto.
  apply map_join_comm in H4.
  eapply load_local;eauto.
  eapply load_local;eauto.
  destruct o as [[[[]]]].
  simpl in *;mytac.
  rewrite H8.
  auto.
  auto.
Qed.

Theorem struct_member_rv'':
  forall s x t l vl tid decl n id t' v P perm,
    s |= LV x @ (Tptr t) |=> Vptr l @ perm ** Astruct l t vl ** P->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some t' ->
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    id_nth id decl = Some n ->
    nth_val n vl = Some v ->
    (*v <> Vundef ->*)
    rule_type_val_match t' v = true ->    
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros.
  eapply struct_member_rv';eauto.
  eapply id_nth_eq;eauto.
Qed.


Lemma id_nth_eq_0 :
  forall id i t decl,
    id_nth id (dcons i t decl) = Some 0 -> Zeq_bool id i = true.
Proof.
  intros.
  unfold id_nth in *.
  unfold1 id_nth' in *.
  remember (Zeq_bool id i) as X.
  destruct X;tryfalse.
  auto.
  apply id_nth_ge in H.
  omega.
Qed.


Lemma id_nth_ueq_0 :
  forall id i t n decl,
    id_nth id (dcons i t decl) = Some (S n) -> Zeq_bool id i = false /\ id_nth id decl = Some n.
Proof.
  intros.
  unfold id_nth in *.
  assert (Zeq_bool id i = false).
  unfold1 id_nth' in *.
  remember (Zeq_bool id i ) as X.
  destruct X.
  inverts H.
  auto.
  split;auto.
  clear -H.
  unfold1 id_nth' in H.
  remember (Zeq_bool id i) as X.
  destruct X;tryfalse.
  apply id_nth'_suc;auto.
Qed.



Theorem struct_member_rv:
  forall s x t l vl tid decl n id t' v P perm,
    s |= LV x @ (Tptr t) |=> Vptr l @ perm ** Astruct l t vl ** P ->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some t' ->
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    id_nth id decl = Some n ->
    n < length vl ->
    struct_type_vallist_match t vl ->
    nth_val' n vl = v ->
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros.
  subst v.
  assert (rule_type_val_match t' (nth_val' n vl) = true).
  subst t.
  unfold struct_type_vallist_match in H7.
  clear l x s H P tid.
  gen vl decl n id t'.
  induction vl,decl, n; intros; simpl in *; tryfalse.
  apply id_nth_eq_0 in H5; subst.
  rewrite H5 in H2.
  inverts H2.
  destruct t'; intuition auto.
  false.
  exact (H4 t' n eq_refl).
  false.
  eapply H3; eauto.
  eapply IHvl; eauto.
  4 : instantiate (1 := decl).
  4 : instantiate (1 := id).
  apply andb_true_iff in H1; mytac; auto.
  destruct t; intuition auto.
  omega.
  apply id_nth_ueq_0 in H5; intuition auto.
  apply id_nth_ueq_0 in H5; mytac.
  rewrite H in H2.
  auto.
  eapply struct_member_rv''; eauto.
  apply nth_val_imp_nth_val'_2; auto.
Qed.

Lemma struct_member_rv_g':
  forall s x t l vl tid decl n id t' v P perm ,
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    rule_type_val_match t' v =true->
    (*v<> Vundef ->*)
    good_decllist decl = true ->
    s |= (A_notin_lenv x ** GV x @ (Tptr t) |=> Vptr l @ perm) ** Astruct l t vl ** P->
    t = Tstruct tid decl ->
    nth_id n decl = Some id ->
    ftype id decl = Some t' ->
    nth_val n vl = Some v ->
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  introv Hnstr.
  introv Hnarr.
  introv Htv.
  assert (v<> Vundef) as Hvn.
  eapply rule_type_val_match_nvundef;eauto.
  introv Hgooddecl.
  intros.
  destruct s as ((o&O)&aop).
  unfold sat in *;fold sat in *;mytac.
  unfold substmo in *.
  destruct o as [[[[]]]].
  unfold substaskst in *.
  unfold getsmem in *.
  unfold getmem in *.
  unfold get_smem in *.
  unfold get_mem in *.
  simpl in *;mytac.
  unfold get in *; simpl in *.
  apply EnvMod.nindom_get in H17.
  rewrite H17.
  rewrite H8.
  rewrite Int.unsigned_zero in H10.
  lets Hf: mapstoval_loadbytes H10.
  simpl;auto.
  destruct Hf.
  destruct H.
  lets Hf: loadbytes_local H4 H.
  assert ( loadbytes m (x19, BinNums.Z0) (typelen (Tptr (Tstruct tid decl))) = Some x2);auto.
  unfold load;unfold loadm.
  rewrite H2.
  rewrite H5.
  rewrite H0.
  clear H.
  destruct l.
  unfold getoff.
  unfold evaltype.
  unfold get in *; simpl in *.
  rewrite H17.
  rewrite H8.
  lets Hoff: nth_id_exists_off H1.
  destruct Hoff.
  rewrite H.

  assert (load t' x1 (addrval_to_addr (b, Int.add (Int.repr (Int.unsigned i0)) x3)) =
          Some v).
  unfold addrval_to_addr.
  rewrite struct_asrt_eq with (n:=n) in H12;eauto.
  unfold sat in H12;fold sat in H12;mytac.
  simpl in H7.
  rewrite Int.repr_unsigned.
  simpl in H15.
  eapply load_local;eauto.
  eapply load_local;eauto.
  eapply mapstoval_load;auto.
  destruct H15;eauto.
  apply map_join_comm in H4.
  eapply load_local;eauto.
  destruct o as [[[[]]]].
  simpl in *;mytac.
  apply EnvMod.nindom_get in  H17.
  unfold get in *; simpl in *.
  rewrite H17.
  rewrite H8.
  auto.
  auto.
Qed.

Theorem struct_member_rv_g'':
  forall s x t l vl tid decl n id t' v P perm,
    s |= (A_notin_lenv x ** GV x @ (Tptr t) |=> Vptr l @ perm) ** Astruct l t vl ** P ->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some t' ->
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    id_nth id decl = Some n ->
    nth_val n vl = Some v ->
    (*v <> Vundef ->*)
    rule_type_val_match t' v = true ->    
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros.
  eapply struct_member_rv_g';eauto.
  eapply id_nth_eq;eauto.
Qed.

Theorem struct_member_rv_g''':
  forall s ls x t l vl tid decl n id t' v P perm,
    s |= A_dom_lenv ls ** GV x @ (Tptr t) |=> Vptr l @ perm ** Astruct l t vl ** P->
    var_notin_dom x ls = true ->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some t' ->
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    id_nth id decl = Some n ->
    nth_val n vl = Some v ->
    (*v <> Vundef ->*)
    rule_type_val_match t' v = true ->    
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros.
  eapply struct_member_rv_g''; eauto.
  sep normal.
  eapply dom_lenv_imp_notin_lenv; eauto.
Qed.

Lemma struct_tvmatch_imp_rule_tvmatch:
  forall (vl : list val) (decl : decllist),
   good_decllist decl = true ->
   struct_type_vallist_match' decl vl ->
   forall n : nat,
   n < length vl ->
   forall id : ident,
   id_nth id decl = Some n ->
   forall t' : type,
   ftype id decl = Some t' ->
   (forall (ids : ident) (dl : decllist), t' <> Tstruct ids dl) ->
   (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
   rule_type_val_match t' (nth_val' n vl) = true.
Proof.
  induction vl,decl, n; intros; simpl in *; tryfalse.
  apply id_nth_eq_0 in H2; subst.
  rewrite H2 in H3.
  inverts H3.
  destruct t'; intuition auto.
  false.
  exact (H5 t' n eq_refl).
  false.
  eapply H4; eauto.
  eapply IHvl; eauto.
  4 : instantiate (1 := decl).
  4 : instantiate (1 := id).
  apply andb_true_iff in H; mytac; auto.
  destruct t; intuition auto.
  omega.
  apply id_nth_ueq_0 in H2; intuition auto.
  apply id_nth_ueq_0 in H2; mytac.
  rewrite H2 in H3.
  auto.
Qed.

Theorem struct_member_rv_g:
  forall s ls x t l vl tid decl n id t' v P perm,
    s |= A_dom_lenv ls ** GV x @ (Tptr t) |=> Vptr l @ perm ** Astruct l t vl ** P->
    var_notin_dom x ls = true ->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some t' ->
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    id_nth id decl = Some n ->
    n < length vl ->
    struct_type_vallist_match t vl ->
    nth_val' n vl = v ->
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros.
  subst v.
  assert (rule_type_val_match t' (nth_val' n vl) = true).
  subst t.
  unfold struct_type_vallist_match in H8.
  clear l x s H H0 P tid ls.
  gen vl decl n id t'.
  induction vl,decl, n; intros; simpl in *; tryfalse.
  apply id_nth_eq_0 in H6; subst.
  rewrite H6 in H3.
  inverts H3.
  destruct t'; intuition auto.
  false.
  exact (H5 t' n eq_refl).
  false.
  eapply H4; eauto.
  eapply IHvl; eauto.
  4 : instantiate (1 := decl).
  4 : instantiate (1 := id).
  apply andb_true_iff in H2; mytac; auto.
  destruct t; intuition auto.
  omega.
  apply id_nth_ueq_0 in H6; intuition auto.
  apply id_nth_ueq_0 in H6; mytac.
  rewrite H in H3.
  auto.
  eapply struct_member_rv_g'''; eauto.
  apply nth_val_imp_nth_val'_2; auto.
Qed.

Fixpoint sub_decllist (d1 d2: decllist){struct d1} : bool :=
 match d1 with
    | dnil => true
    | dcons x1 t1 d1' =>
      match d2 with
         | dnil => false
         | dcons x2 t2 d2' => andb (andb (Zeq_bool x1 x2) (type_eq t1 t2)) (sub_decllist d1' d2')
      end
end.

Lemma sub_decllist_ftype:
  forall d1 d2 t id, 
    sub_decllist d1 d2 =true -> 
    ftype id d1 = Some t -> 
    ftype id d2 = Some t. 
Proof.
  inductions d1.
  simpl; intros; tryfalse. 
  intros.
  simpl in H.
  destruct d2; tryfalse.
 apply andb_true_iff in H.
 destruct H.
 apply andb_true_iff in H.
 destruct H.
 apply type_eq_true_eq in H2.
 subst.
 apply Zeq_bool_eq in H.
 subst.
 simpl.
 simpl in H0.
  remember (Zeq_bool id i0) as Ha.
  destruct Ha; auto.
Qed.

Lemma sub_decllist_offsetfld:
  forall d1 d2 t id i,
    sub_decllist d1 d2 =true -> 
    field_offsetfld id d1 i = Some t  -> 
    field_offsetfld id d2 i= Some t. 
Proof.
inductions d1.
  simpl; intros; tryfalse. 
  intros.
  simpl in H.
  destruct d2; tryfalse.
 apply andb_true_iff in H.
 destruct H.
 apply andb_true_iff in H.
 destruct H.
 apply type_eq_true_eq in H2.
 subst.
 apply Zeq_bool_eq in H.
 subst.
 unfold field_offset in *.
 simpl in *.
  remember (Zeq_bool id i1) as Ha.
  destruct Ha; auto.
Qed.


Lemma sub_decllist_offset:
  forall d1 d2 t id,
    sub_decllist d1 d2 =true -> 
    field_offset id d1 = Some t  -> 
    field_offset  id d2 = Some t. 
Proof.
  intros.
  eapply sub_decllist_offsetfld; eauto.
Qed.



(*
Theorem struct_member_rv_g:
  forall s ls x t l vl tid decl n id t' v P perm,
    s |= A_dom_lenv ls ** GV x @ (Tptr t) |=> Vptr l @ perm ** Astruct l t vl ** P->
    var_notin_dom x ls = true ->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some t' ->
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    id_nth id decl = Some n ->
    n < length vl ->
    struct_type_vallist_match t vl ->
    nth_val' n vl = v ->
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros.
  subst v.
  assert (rule_type_val_match t' (nth_val' n vl) = true).
  subst t.
  unfold struct_type_vallist_match in H8.
  clear l x s H H0 P tid ls.
  gen vl decl n id t'.
  induction vl,decl, n; intros; simpl in *; tryfalse.
  apply id_nth_eq_0 in H6; subst.
  rewrite H6 in H3.
  inverts H3.
  destruct t'; intuition auto.
  false.
  exact (H5 t' n eq_refl).
  false.
  eapply H4; eauto.
  eapply IHvl; eauto.
  4 : instantiate (1 := decl).
  4 : instantiate (1 := id).
  apply andb_true_iff in H2; mytac; auto.
  destruct t; intuition auto.
  omega.
  apply id_nth_ueq_0 in H6; intuition auto.
  apply id_nth_ueq_0 in H6; mytac.
  rewrite H in H3.
  auto.
  eapply struct_member_rv_g'''; eauto.
  apply nth_val_imp_nth_val'_2; auto.
Qed.*)


Theorem struct_member_array_rv_g:
  forall s ls x t l vl tid decl id t' n P ad perm,
    s |=   A_dom_lenv ls **  GV x @ (Tptr t) |=> Vptr l @ perm ** Astruct l t vl ** P->
    var_notin_dom x ls = true ->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some (Tarray t' n) ->
    id_addrval l id t = Some ad ->
    s |= Rv (efield (ederef (evar x)) id) @ (Tarray t' n) == Vptr ad.
Proof.
  intros.
  destruct_s s.
  eapply dom_lenv_imp_notin_lenv in H; eauto.
  simpl in *;mytac.
  apply EnvMod.nindom_get in H8;auto.
  unfold get in *; simpl in *.
  rewrite H8.
  rewrite H23.
  rewrite H3.
  unfold load;unfold loadm.
  rewrite Int.unsigned_zero in H24.
  lets Hf: mapstoval_loadbytes H24.
  simpl;auto.
  destruct Hf.
  destruct H.
  lets Hf: loadbytes_local H10 H.
  assert ( loadbytes m (x25, 0%Z) (typelen (Tptr (Tstruct tid decl))) = Some x0);auto.
  rewrite H5.
  rewrite H1.
  destruct l.
  unfold getoff.
  unfold evaltype.
  unfold get in *; simpl in *.
  rewrite H8;rewrite H23.
  unfold id_addrval in H4.
  remember (field_offset id decl ) as X.
  destruct X;tryfalse.
  rewrite Int.repr_unsigned.
  simpl.
  rewrite Int.repr_unsigned.
  inverts H4;auto.
  apply EnvMod.nindom_get in H8;auto.
  unfold get in *; simpl in *.
  rewrite H8;rewrite H23.
  auto.
  intro; tryfalse.
Qed.



Definition isarray_type t:= exists t'' n, 
                              t = Tarray t'' n.

Theorem struct_member_rv_g_general:
  forall s ls x t l vl tid decl id P v t' perm,
    s |=   A_dom_lenv ls **  GV x @ (Tptr t) |=> Vptr l @ perm ** Astruct l t vl ** P->
    var_notin_dom x ls = true ->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some t' -> 
    (
      isarray_type t'-> 
      exists ad, id_addrval l id t = Some ad /\ v = Vptr ad
    ) ->
    (
      ~ isarray_type t' ->
      (
        exists n,
          (forall a b, t' <> Tstruct a b) /\
          id_nth id decl = Some n /\
          n < length vl /\
          struct_type_vallist_match t vl /\
          nth_val' n vl = v 
      )
    ) -> 
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros.
  mytac.
  assert (isarray_type t' \/ ~isarray_type t' ).
  tauto.
  destruct H1.
  lets Hx: H4 H1.
  mytac.
  unfolds in H1;mytac.
  eapply struct_member_array_rv_g;eauto.
  lets Hx : H5 H1.
  mytac.
  eapply struct_member_rv_g;eauto.
  unfold isarray_type in H1.
  intros.
  introv.
  introv Hf.
  apply H1;eauto.
Qed.



(*
Theorem struct_member_array_rv_ro:
  forall s x t l vl tid decl id t' n P ad,
    s |=  LV x @ (Tptr t) |-r-> Vptr l ** Astruct l t vl ** P->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some (Tarray t' n) ->
    id_addrval l id t = Some ad ->
    s |= Rv (efield (ederef (evar x)) id) @ (Tarray t' n) == Vptr ad.
Proof.
  intros.
  destruct_s s.
  simpl in *;mytac.
  rewrite H17.
  rewrite H2.
  unfold load;unfold loadm.
  rewrite Int.unsigned_zero in H18.
  lets Hf: mapstoval_loadbytes H18.
  simpl;auto.
  destruct Hf.
  destruct H.
  lets Hf: loadbytes_local H4 H.
  assert ( loadbytes m (x19, 0%Z) (typelen (Tptr (Tstruct tid decl))) = Some x2);auto.
  rewrite H5.
  rewrite H0.
  destruct l.
  unfold getoff.
  unfold evaltype.
  rewrite H17.
  unfold id_addrval in H3.
  remember (field_offset id decl ) as X.
  destruct X;tryfalse.
  rewrite Int.repr_unsigned.
  simpl.
  rewrite Int.repr_unsigned.
  inverts H3;auto.
  rewrite H17.
  auto.
  intro; tryfalse.
Qed.
*)


Theorem struct_member_array_rv:
  forall s x t l vl tid decl id t' n P ad perm,
    s |=  LV x @ (Tptr t) |=> Vptr l @ perm  ** Astruct l t vl ** P->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some (Tarray t' n) ->
    id_addrval l id t = Some ad ->
    s |= Rv (efield (ederef (evar x)) id) @ (Tarray t' n) == Vptr ad.
Proof.
  intros.
  destruct_s s.
  simpl in *;mytac.
  rewrite H17.
  rewrite H2.
  unfold load;unfold loadm.
  rewrite Int.unsigned_zero in H18.
  lets Hf: mapstoval_loadbytes H18.
  simpl;auto.
  destruct Hf.
  destruct H.
  lets Hf: loadbytes_local H4 H.
  assert ( loadbytes m (x19, 0%Z) (typelen (Tptr (Tstruct tid decl))) = Some x2);auto.
  rewrite H5.
  rewrite H0.
  destruct l.
  unfold getoff.
  unfold evaltype.
  rewrite H17.
  unfold id_addrval in H3.
  remember (field_offset id decl ) as X.
  destruct X;tryfalse.
  rewrite Int.repr_unsigned.
  simpl.
  rewrite Int.repr_unsigned.
  inverts H3;auto.
  rewrite H17.
  auto.
  intro; tryfalse.
Qed.



Theorem struct_offset_rv :
  forall s e t tid decl a id t' off,
    s |= Rv eaddrof e @ Tptr t ==  Vptr a ->
    t = Tstruct tid decl ->
    field_offset id decl = Some off ->
    ftype id decl = Some t' ->
    s |= Rv eaddrof (efield e id) @ Tptr t' == Vptr (fst a, Int.add (snd a) off).
Proof.
  intros.
  unfold sat in *.
  destruct H.
  destruct H3.
  subst t.
  destruct s as [[]].
  destruct t as [[[[]]]].
  unfold getsmem in *.
  unfold get_smem in *.
  splits;auto.
  assert (evaltype e (e0, e1, m) = Some (Tstruct tid decl)).
  eapply eval_type_addr_eq;eauto.
  simpl.
  rewrite H0.
  rewrite H2.
  destruct a.
  apply eval_addr_eq in H.
  rewrite H.
  simpl.
  unfold getoff.
  rewrite H0.
  rewrite H1.
  simpl.
  assert (Int.repr (Int.unsigned i0)=i0).
  apply Int.repr_unsigned.
  rewrite H5.
  auto.
  simpl.
  assert (evaltype e (e0, e1, m) = Some (Tstruct tid decl)).
  eapply eval_type_addr_eq;eauto.
  rewrite H0.
  rewrite H2.
  auto.
  intro; tryfalse.
Qed.

Theorem struct_member_rv_general:
  forall s  x t l vl tid decl id P v t' perm,
    s |=  LV x @ (Tptr t) |=> Vptr l @ perm ** Astruct l t vl ** P->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some t' -> 
    (
      isarray_type t'-> 
      exists ad, id_addrval l id t = Some ad /\ v = Vptr ad
    ) ->
    (
      ~ isarray_type t' ->
      (
        exists n,
          (forall a b, t' <> Tstruct a b) /\
          id_nth id decl = Some n /\
          n < length vl /\
          struct_type_vallist_match t vl /\
          nth_val' n vl = v 
      )
    ) -> 
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros.
  mytac.
  assert (isarray_type t' \/ ~isarray_type t' ).
  tauto.
  destruct H0.
  lets Hx: H3 H0.
  mytac.
  unfolds in H0;mytac.
  eapply struct_member_array_rv;eauto.
  lets Hx : H4 H0.
  mytac.
  eapply struct_member_rv;eauto.
  unfold isarray_type in H0.
  intros.
  introv.
  introv Hf.
  apply H0;eauto.
Qed.



Lemma int_Z_ltu: 
  forall m n,
    Int.ltu m (Int.repr (Z.of_nat n)) = true->
    BinInt.Z.abs_nat (Int.unsigned m) < n.
Proof.
  intros.
  unfold Int.ltu in H.
  destruct (Coqlib.zlt (Int.unsigned m) (Int.unsigned (Int.repr (Z.of_nat n)))); tryfalse.
  clear H.
  rewrite Zabs2Nat.abs_nat_nonneg.

  rewrite Int.unsigned_repr_eq in l.
  pose proof Zmod_le (Z.of_nat n) Int.modulus.
  assert (0 < Int.modulus)%Z.
  unfold Int.modulus.
  unfold Int.wordsize.
  unfold Wordsize_32.wordsize.
  unfold two_power_nat.
  unfold shift_nat.
  simpl.
  omega.
  assert (0 <= Z.of_nat n)%Z.
  omega.
  pose proof H H0 H1; clear H H0 H1.
  assert (Int.unsigned m < Z.of_nat n)%Z.
  omega.
  rewrite <- Nat2Z.id.
  apply Z2Nat.inj_lt.
  pose proof Int.unsigned_range m.
  destruct H0.
  auto.
  omega.
  auto.
  pose proof Int.unsigned_range m.
  destruct H.
  auto.
Qed.

Theorem array_member_rv' :
  forall s x t te2 l vl n m v e2 P,
    s |= Alvarenv x (Tarray t n) (addrval_to_addr l) ** Aarray l (Tarray t n) vl ** P ->
    s |= Rv e2 @ te2  == Vint32 m ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    Int.ltu m Int.zero = false ->
    Int.ltu m (Int.repr (BinInt.Z_of_nat n)) = true  ->
    (*  Int.cmp Cge m Int.zero = true ->
    Int.cmp Clt m (Int.repr (BinInt.Z_of_nat n)) =true  ->*)
    nth_val (BinInt.Z.abs_nat (Int.unsigned m)) vl = Some v ->
    (*v<> Vundef ->*)
    rule_type_val_match t v =true->
    s |= Rv (earrayelem (evar x) e2) @ t == v.
Proof.
  intros.
  rename H5 into Htv.
  assert (v<> Vundef).
  eapply rule_type_val_match_nvundef;eauto.
  destruct s as ((o&O)&aop).
  destruct l as (b&i).
  unfold sat in *;fold sat in *;mytac.
  unfold substmo in *.
  destruct o as [[[[]]]].
  unfold substaskst in *.
  unfold getsmem in *.
  unfold getmem in *.
  unfold get_smem in *.
  unfold get_mem in *.
  simpl in *;mytac.
  rewrite H11.
  rewrite H6.
  destruct H1.
  rewrite H.
  rewrite H0.
  erewrite array_asrt_eq in H16;eauto.
  unfold sat in H16;fold sat in H16;mytac.
  simpl in H16.
  destruct H14.
  rewrite <- Int.unsigned_zero in H12.
  apply unsigned_inj in H12.
  subst i.
  assert (Int.repr
            (BinInt.Z.of_nat (BinInt.Z.abs_nat (Int.unsigned m))) = m).
  rewrite Nat2Z.inj_abs_nat.
  rewrite Z.abs_eq.
  apply Int.repr_unsigned.
  lets H100:Int.unsigned_range m.
  omega.

  rewrite H9 in H.
  lets Hf: mapstoval_loadbytes H.
  auto.
  destruct Hf.
  destruct H12.
  assert (loadbytes m0
                    (x12,
                     Int.unsigned
                       (Int.add Int.zero
                                (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) m)))
                    (typelen t) = Some x2).
  eapply loadbytes_local;eauto.
  eapply loadbytes_local;eauto.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  simpl.
  rewrite Int.repr_unsigned.
  rewrite H18.

  destruct t;auto;simpl in Htv;tryfalse; rewrite H14;auto.
  eapply int_Z_ltu;eauto.
  destruct H.
  rewrite H.
  rewrite H0.
  erewrite array_asrt_eq in H16;eauto.
  unfold sat in H16;fold sat in H16;mytac.
  simpl in H16.
  destruct H14.
  rewrite <- Int.unsigned_zero in H12.
  apply unsigned_inj in H12.
  subst i.
  assert (Int.repr
            (BinInt.Z.of_nat (BinInt.Z.abs_nat (Int.unsigned m))) = m).
  rewrite Nat2Z.inj_abs_nat.
  rewrite Z.abs_eq.
  apply Int.repr_unsigned.
  lets H100:Int.unsigned_range m.
  omega.
  rewrite H9 in H.
  lets Hf: mapstoval_loadbytes H.
  auto.
  destruct Hf.
  destruct H12.
  assert (loadbytes m0
                    (x12,
                     Int.unsigned
                       (Int.add Int.zero
                                (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) m)))
                    (typelen t) = Some x2).
  eapply loadbytes_local;eauto.
  eapply loadbytes_local;eauto.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  simpl.
  rewrite Int.repr_unsigned.
  rewrite H18.
  destruct t;auto;simpl in Htv;tryfalse; rewrite H14;auto.
  eapply int_Z_ltu;eauto.
  rewrite H.
  rewrite H0.
  erewrite array_asrt_eq in H16;eauto.
  unfold sat in H16;fold sat in H16;mytac.
  simpl in H16.
  destruct H14.
  rewrite <- Int.unsigned_zero in H12.
  apply unsigned_inj in H12.
  subst i.
  assert (Int.repr
            (BinInt.Z.of_nat (BinInt.Z.abs_nat (Int.unsigned m))) = m).
  rewrite Nat2Z.inj_abs_nat.
  rewrite Z.abs_eq.
  apply Int.repr_unsigned.
  lets H100:Int.unsigned_range m.
  omega.

  rewrite H9 in H.
  lets Hf: mapstoval_loadbytes H.
  auto.
  destruct Hf.
  destruct H12.
  assert (loadbytes m0
                    (x12,
                     Int.unsigned
                       (Int.add Int.zero
                                (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) m)))
                    (typelen t) = Some x2).
  eapply loadbytes_local;eauto.
  eapply loadbytes_local;eauto.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  simpl.
  rewrite Int.repr_unsigned.
  rewrite H18.
  destruct t;auto;simpl in Htv;tryfalse; rewrite H14;auto.
  eapply int_Z_ltu;eauto.
  destruct o as [[[[]]]].
  simpl in *;mytac.
  rewrite H11.
  rewrite H6.
  destruct H1.
  rewrite H.
  auto.
  destruct H;rewrite H;auto.
  auto.
Qed.

Theorem array_member_rv'' :
  forall s x t t' te2 vl n m v e2 P,
    s |= LAarray x t' vl ** P ->
    t' = Tarray t n ->
    s |= Rv e2 @ te2  == Vint32 m ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    Int.ltu m (Int.repr (BinInt.Z_of_nat n)) = true  ->
    nth_val (BinInt.Z.abs_nat (Int.unsigned m)) vl = Some v ->
    (*v<> Vundef ->*)
    rule_type_val_match t v =true->
    s |= Rv (earrayelem (evar x) e2) @ t == v.
Proof.
  intros.
  unfold LAarray in H.
  unfold Alvarenv' in H.
  sep normal in H; sep destruct H.
  subst t'.
  eapply array_member_rv'; eauto.
  unfold Int.ltu.
  rewrite Int.unsigned_zero.
  remember (zlt (Int.unsigned m) 0 ) as X.
  destruct X.
  clear -l.
  lets H100:Int.unsigned_range m.
  omega.
  auto.
Qed.


Theorem array_member_rv :
  forall s x t t' te2 vl n m e2 v P,
    s |= LAarray x t' vl ** P ->
    t' = Tarray t n ->
    s |= Rv e2 @ te2  == Vint32 m ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    (Z.of_nat n < 4294967295)%Z -> 
    (Int.unsigned m < Z.of_nat n)%Z ->
    (Int.unsigned m < Z.of_nat (length vl))%Z ->
    rule_type_val_match t v = true ->
    nth_val' (Z.to_nat (Int.unsigned m)) vl = v ->
    s |= Rv (earrayelem (evar x) e2) @ t == v.
Proof.
  intros.
  subst v.
  eapply array_member_rv''; eauto.
  unfold Int.ltu.
  rewrite Int.unsigned_repr.
  apply zlt_true.
  auto.
  split; try omega.
  unfold Int.max_unsigned.
  unfold Int.modulus.
  unfold two_power_nat, Int.wordsize.
  unfold shift_nat, Wordsize_32.wordsize.
  unfold nat_rect.
  omega.
  apply nth_val_imp_nth_val'_1; auto.
Qed.
(*
  apply array_type_vallist_match_imp_rule_type_val_match; auto.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id.
  auto.
  lets H100 : Int.unsigned_range m.
  omega.
Qed.
 *)

Theorem array_member_rv_g' :
  forall s x t te2 l vl n m v e2 P,
    s |= (A_notin_lenv x ** Agvarenv x (Tarray t n) (addrval_to_addr l)) ** Aarray l (Tarray t n) vl ** P->
    s |= Rv e2 @ te2  == Vint32 m ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    Int.ltu m Int.zero = false ->
    Int.ltu m (Int.repr (BinInt.Z_of_nat n)) =true  ->
    nth_val (BinInt.Z.abs_nat (Int.unsigned m)) vl = Some v ->
    (*    v<> Vundef -> *)
    rule_type_val_match t v = true->
    s |= Rv (earrayelem (evar x) e2) @ t == v.
Proof.
  intros.
  rename H5 into Htv.
  assert (v<>Vundef).
  eapply rule_type_val_match_nvundef;eauto.
  destruct s as ((o&O)&aop).
  destruct l as (b&i).
  unfold sat in *;fold sat in *;mytac.
  unfold substmo in *.
  destruct o as [[[[]]]].
  unfold substaskst in *.
  unfold getsmem in *.
  unfold getmem in *.
  unfold get_smem in *.
  unfold get_mem in *.
  simpl in *;mytac.
  apply EnvMod.nindom_get in  H21.
  unfold get in *; simpl in *.
  rewrite H21.
  rewrite H22.
  rewrite H6.
  destruct H1.
  rewrite H.
  rewrite H0.
  erewrite array_asrt_eq in H16;eauto.
  unfold sat in H16;fold sat in H16;mytac.
  simpl in H12.
  destruct H12.
  rewrite <- Int.unsigned_zero in H9.
  apply unsigned_inj in H9.

  subst i.
  assert (Int.repr
            (BinInt.Z.of_nat (BinInt.Z.abs_nat (Int.unsigned m))) = m).
  rewrite Nat2Z.inj_abs_nat.
  rewrite Z.abs_eq.
  apply Int.repr_unsigned.
  lets H100:Int.unsigned_range m.
  omega.
  rewrite H9 in H.
  lets Hf: mapstoval_loadbytes H.
  auto.
  destruct Hf.
  destruct H10.
  assert (loadbytes m0
                    (x18,
                     Int.unsigned
                       (Int.add Int.zero
                                (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) m)))
                    (typelen t) = Some x2).
  eapply loadbytes_local;eauto.
  eapply loadbytes_local;eauto.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  simpl.
  rewrite Int.repr_unsigned.
  rewrite H16.
  destruct t;auto;simpl in Htv;tryfalse; rewrite H12;auto.

  eapply int_Z_ltu;eauto.
  destruct H.
  rewrite H.
  rewrite H0.
  erewrite array_asrt_eq in H16;eauto.
  unfold sat in H16;fold sat in H16;mytac.
  simpl in H12.
  destruct H12.
  rewrite <- Int.unsigned_zero in H9.
  apply unsigned_inj in H9.
  subst i.
  assert (Int.repr
            (BinInt.Z.of_nat (BinInt.Z.abs_nat (Int.unsigned m))) = m).
  rewrite Nat2Z.inj_abs_nat.
  rewrite Z.abs_eq.
  apply Int.repr_unsigned.
  lets H100:Int.unsigned_range m.
  omega.
  rewrite H9 in H.
  lets Hf: mapstoval_loadbytes H.
  auto.
  destruct Hf.
  destruct H10.
  assert (loadbytes m0
                    (x18,
                     Int.unsigned
                       (Int.add Int.zero
                                (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) m)))
                    (typelen t) = Some x2).
  eapply loadbytes_local;eauto.
  eapply loadbytes_local;eauto.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  simpl.
  rewrite Int.repr_unsigned.
  rewrite H16.
  destruct t;auto;simpl in Htv;tryfalse; rewrite H12;auto.
  eapply int_Z_ltu;eauto.
  rewrite H.
  rewrite H0.
  erewrite array_asrt_eq in H16;eauto.
  unfold sat in H16;fold sat in H16;mytac.
  simpl in H12.
  destruct H12.
  rewrite <- Int.unsigned_zero in H9.
  apply unsigned_inj in H9.
  subst i.
  assert (Int.repr
            (BinInt.Z.of_nat (BinInt.Z.abs_nat (Int.unsigned m))) = m).
  rewrite Nat2Z.inj_abs_nat.
  rewrite Z.abs_eq.
  apply Int.repr_unsigned.
  lets H100:Int.unsigned_range m.
  omega.
  rewrite H9 in H.
  lets Hf: mapstoval_loadbytes H.
  auto.
  destruct Hf.
  destruct H10.
  assert (loadbytes m0
                    (x18,
                     Int.unsigned
                       (Int.add Int.zero
                                (Int.mul (Int.repr (BinInt.Z.of_nat (typelen t))) m)))
                    (typelen t) = Some x2).
  eapply loadbytes_local;eauto.
  eapply loadbytes_local;eauto.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  simpl.
  rewrite Int.repr_unsigned.
  rewrite H16.
  destruct t;auto;simpl in Htv;tryfalse; rewrite H12;auto.
  eapply int_Z_ltu;eauto.
  destruct o as [[[[]]]].
  simpl in *;mytac.
  apply EnvMod.nindom_get in  H21.
  unfold get in *; simpl in *.
  rewrite H21.
  rewrite H22.
  rewrite H6.
  destruct H1.
  rewrite H.
  auto.
  destruct H;rewrite H;auto.
  auto.
Qed.




Theorem array_member_rv_g'' :
  forall s ls x t t' te2 vl n m v e2 P,
    s |= A_dom_lenv ls ** GAarray x t' vl ** P->
    var_notin_dom x ls = true ->
    t' = Tarray t n ->
    s |= Rv e2 @ te2  == Vint32 m ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    Int.ltu m (Int.repr (BinInt.Z_of_nat n)) =true  ->
    nth_val (BinInt.Z.abs_nat (Int.unsigned m)) vl = Some v ->
    (*v<> Vundef ->*)
    rule_type_val_match t v = true->
    s |= Rv (earrayelem (evar x) e2) @ t == v.
Proof.
  intros.
  unfold GAarray in H; unfold Agvarenv' in H.
  sep normal in H; sep destruct H.
  subst t'.
  eapply array_member_rv_g'; eauto.
  sep normal.
  eapply dom_lenv_imp_notin_lenv; eauto.
  sep auto.
  unfold Int.ltu.
  rewrite Int.unsigned_zero.
  remember (zlt (Int.unsigned m) 0 ) as X.
  destruct X.
  clear -l.
  lets H100:Int.unsigned_range m.
  omega.
  auto.
Qed.


Theorem array_member_rv_g :
  forall s ls x t t' te2 vl n m e2 v P vm,
    s |= A_dom_lenv ls ** GAarray x t' vl ** P->
    var_notin_dom x ls = true ->
    t' = Tarray t n ->
    s |= Rv e2 @ te2  == vm ->
    vm = Vint32 m ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    (Z.of_nat n < 4294967295)%Z ->
    (Int.unsigned m < Z.of_nat n)%Z ->
    (Int.unsigned m < Z.of_nat (length vl))%Z ->
    rule_type_val_match t v = true ->
    nth_val' (Z.to_nat (Int.unsigned m)) vl = v ->
    s |= Rv (earrayelem (evar x) e2) @ t == v.
Proof.
  intros.
  subst vm.
  subst v.
  eapply array_member_rv_g''; eauto.
  unfold Int.ltu.
  rewrite Int.unsigned_repr.
  apply zlt_true.
  auto.
  auto.
  split; try omega.
  unfold Int.max_unsigned.
  unfold Int.modulus.
  unfold two_power_nat, Int.wordsize.
  unfold shift_nat, Wordsize_32.wordsize.
  unfold nat_rect.
  omega.
  apply nth_val_imp_nth_val'_1; auto.
Qed.
(*
  apply array_type_vallist_match_imp_rule_type_val_match; auto.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id.
  auto.
  lets H100 : Int.unsigned_range m.
  omega.
Qed.
 *)
Theorem expr_array_member_rv' :
  forall s e1 t te1 te2 l vl n m v e2 P,
    s |= Aarray l (Tarray t n) vl ** P ->
    s |= Rv e1 @ te1  == Vptr l ->
    s |= Rv e2 @ te2  == Vint32 m ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    Int.ltu m Int.zero = false ->
    Int.ltu m (Int.repr (BinInt.Z_of_nat n)) = true  ->
    nth_val (BinInt.Z.abs_nat (Int.unsigned m)) vl = Some v ->
    rule_type_val_match t v =true->
    te1 = Tarray t n \/ te1 = Tptr t ->
    s |= Rv (earrayelem e1 e2) @ t == v.
Proof.
  intros.
  rename H6 into Htv.
  rename H7 into Hte1.
  assert (v<> Vundef).
  eapply rule_type_val_match_nvundef;eauto.
  destruct s as ((o&O)&aop).
  destruct l as (b&i).
  unfold sat in *;fold sat in *;mytac.
  unfold substmo in *.
  destruct o as [[[[]]]].
  unfold substaskst in *.
  unfold getsmem in *.
  unfold getmem in *.
  unfold get_smem in *.
  unfold get_mem in *.
  simpl in *;mytac.
  rewrite H9.
  rewrite H7.
  rewrite H0.
  rewrite H1.

  destruct Hte1;destruct te1;tryfalse.
  destruct H2.
  subst te2.
  inverts H.
  erewrite array_asrt_eq in H14;eauto.
  unfold sat in H14;fold sat in H14;mytac.
  simpl in H17.
  destruct H16.
  simpl in H.

  lets Hf: mapstoval_loadbytes H.
  auto.
  destruct Hf.
  destruct H16.
  assert (loadbytes m0
                    (b,
                     Int.unsigned
                       (Int.add i
                                (Int.mul (Int.repr (Z.of_nat (typelen t)))
                                         (Int.repr (Z.of_nat (Z.abs_nat (Int.unsigned m)))))))
                    (typelen t) = Some x5 ).
  eapply loadbytes_local;eauto.
  eapply loadbytes_local;eauto.
  rewrite Nat2Z.inj_abs_nat in H19.
  rewrite Z.abs_eq in H19.
  rewrite Int.repr_unsigned in H19.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  simpl.
  rewrite Int.repr_unsigned.
  rewrite H19.
  destruct t;auto;simpl in Htv;tryfalse; rewrite H18;auto.
  lets H100:Int.unsigned_range m.
  omega.
  eapply int_Z_ltu;eauto.

  destruct H2;subst te2.
  inverts H.
  erewrite array_asrt_eq in H14;eauto.
  unfold sat in H14;fold sat in H14;mytac.
  simpl in H17.
  destruct H16.
  simpl in H.

  lets Hf: mapstoval_loadbytes H.
  auto.
  destruct Hf.
  destruct H16.
  assert (loadbytes m0
                    (b,
                     Int.unsigned
                       (Int.add i
                                (Int.mul (Int.repr (Z.of_nat (typelen t)))
                                         (Int.repr (Z.of_nat (Z.abs_nat (Int.unsigned m)))))))
                    (typelen t) = Some x5 ).
  eapply loadbytes_local;eauto.
  eapply loadbytes_local;eauto.
  rewrite Nat2Z.inj_abs_nat in H19.
  rewrite Z.abs_eq in H19.
  rewrite Int.repr_unsigned in H19.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  simpl.
  rewrite Int.repr_unsigned.
  rewrite H19.
  destruct t;auto;simpl in Htv;tryfalse; rewrite H18;auto.
  lets H100:Int.unsigned_range m.
  omega.
  eapply int_Z_ltu;eauto.

  inverts H.
  erewrite array_asrt_eq in H14;eauto.
  unfold sat in H14;fold sat in H14;mytac.
  simpl in H17.
  destruct H16.
  simpl in H.

  lets Hf: mapstoval_loadbytes H.
  auto.
  destruct Hf.
  destruct H16.
  assert (loadbytes m0
                    (b,
                     Int.unsigned
                       (Int.add i
                                (Int.mul (Int.repr (Z.of_nat (typelen t)))
                                         (Int.repr (Z.of_nat (Z.abs_nat (Int.unsigned m)))))))
                    (typelen t) = Some x5 ).
  eapply loadbytes_local;eauto.
  eapply loadbytes_local;eauto.
  rewrite Nat2Z.inj_abs_nat in H19.
  rewrite Z.abs_eq in H19.
  rewrite Int.repr_unsigned in H19.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  simpl.
  rewrite Int.repr_unsigned.

  rewrite H19.

  destruct t;auto;simpl in Htv;tryfalse; rewrite H18;auto.
  lets H100:Int.unsigned_range m.
  omega.
  eapply int_Z_ltu;eauto.

  destruct H2.
  subst te2.
  inverts H.
  erewrite array_asrt_eq in H14;eauto.
  unfold sat in H14;fold sat in H14;mytac.
  simpl in H17.
  destruct H16.
  simpl in H.

  lets Hf: mapstoval_loadbytes H.
  auto.
  destruct Hf.
  destruct H16.
  assert (loadbytes m0
                    (b,
                     Int.unsigned
                       (Int.add i
                                (Int.mul (Int.repr (Z.of_nat (typelen t)))
                                         (Int.repr (Z.of_nat (Z.abs_nat (Int.unsigned m)))))))
                    (typelen t) = Some x5 ).
  eapply loadbytes_local;eauto.
  eapply loadbytes_local;eauto.
  rewrite Nat2Z.inj_abs_nat in H19.
  rewrite Z.abs_eq in H19.
  rewrite Int.repr_unsigned in H19.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  simpl.
  rewrite Int.repr_unsigned.

  rewrite H19.

  destruct t;auto;simpl in Htv;tryfalse; rewrite H18;auto.
  lets H100:Int.unsigned_range m.
  omega.
  eapply int_Z_ltu;eauto.

  destruct H2;subst te2.
  inverts H.
  erewrite array_asrt_eq in H14;eauto.
  unfold sat in H14;fold sat in H14;mytac.
  simpl in H17.
  destruct H16.
  simpl in H.

  lets Hf: mapstoval_loadbytes H.
  auto.
  destruct Hf.
  destruct H16.
  assert (loadbytes m0
                    (b,
                     Int.unsigned
                       (Int.add i
                                (Int.mul (Int.repr (Z.of_nat (typelen t)))
                                         (Int.repr (Z.of_nat (Z.abs_nat (Int.unsigned m)))))))
                    (typelen t) = Some x5 ).
  eapply loadbytes_local;eauto.
  eapply loadbytes_local;eauto.
  rewrite Nat2Z.inj_abs_nat in H19.
  rewrite Z.abs_eq in H19.
  rewrite Int.repr_unsigned in H19.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  simpl.
  rewrite Int.repr_unsigned.

  rewrite H19.

  destruct t;auto;simpl in Htv;tryfalse; rewrite H18;auto.
  lets H100:Int.unsigned_range m.
  omega.
  eapply int_Z_ltu;eauto.




  inverts H.
  erewrite array_asrt_eq in H14;eauto.
  unfold sat in H14;fold sat in H14;mytac.
  simpl in H17.
  destruct H16.
  simpl in H.

  lets Hf: mapstoval_loadbytes H.
  auto.
  destruct Hf.
  destruct H16.
  assert (loadbytes m0
                    (b,
                     Int.unsigned
                       (Int.add i
                                (Int.mul (Int.repr (Z.of_nat (typelen t)))
                                         (Int.repr (Z.of_nat (Z.abs_nat (Int.unsigned m)))))))
                    (typelen t) = Some x5 ).
  eapply loadbytes_local;eauto.
  eapply loadbytes_local;eauto.
  rewrite Nat2Z.inj_abs_nat in H19.
  rewrite Z.abs_eq in H19.
  rewrite Int.repr_unsigned in H19.
  unfold load;unfold loadm.
  simpl addr_to_addrval.
  simpl.
  rewrite Int.repr_unsigned.

  rewrite H19.

  destruct t;auto;simpl in Htv;tryfalse; rewrite H18;auto.
  lets H100:Int.unsigned_range m.
  omega.
  eapply int_Z_ltu;eauto.


  destruct o as [[[[]]]].
  simpl in *;mytac.
  rewrite H9.
  rewrite H7.
  destruct Hte1;destruct H2;subst;auto.
  destruct H2;subst;auto.
  destruct H2;subst;auto.
  auto.
Qed.


Theorem expr_array_member_rv :
  forall  s e1 t te1 te2 l vl n m v e2 P,
    s |= Rv e1 @ te1  == Vptr l ->
    s |= Aarray l (Tarray t n) vl ** P ->
    s |= Rv e2 @ te2  == Vint32 m ->
    te1 = Tarray t n \/ te1 = Tptr t ->
    te2 = Tint8 \/ te2 = Tint16 \/ te2 = Tint32 ->
    (Z.of_nat n < 4294967295)%Z -> 
    (Int.unsigned m < Z.of_nat n)%Z ->
    (Int.unsigned m < Z.of_nat (length vl))%Z ->
    rule_type_val_match t v = true ->
    nth_val' (Z.to_nat (Int.unsigned m)) vl = v ->
    s |= Rv (earrayelem e1 e2) @ t == v.
Proof.
  intros.
  subst v.
  eapply expr_array_member_rv'; eauto.
  unfold Int.ltu.
  rewrite Int.unsigned_zero.
  apply zlt_false.
  lets Hx:Int.unsigned_range m.
  omega.
  unfold Int.ltu.
  apply zlt_true.
  rewrite Int.unsigned_repr;auto.
  split; try omega.
  unfold Int.max_unsigned.
  unfold Int.modulus.
  unfold two_power_nat, Int.wordsize.
  unfold shift_nat, Wordsize_32.wordsize.
  unfold nat_rect.
  omega.
  apply nth_val_imp_nth_val'_1; auto.
Qed.

(*************************************************************)
(*************************************************************)
(*************************************************************)
Lemma struct_member_rv_flag: 
  forall s x id l off t t' P perm decl tid v perm1,
    s |= LV x @ Tptr t |=> Vptr l @ perm1 ** PV (get_off_addr l off) @ t' |=> v @ perm ** P ->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some t' ->
    field_offset id decl = Some off->
    rule_type_val_match t' v = true ->
    s |= Rv efield (ederef (evar x)) id @ t' == v.
Proof.
  introv Hsa Ht Hg Hfi Hfs Hss.
  destruct_s s.
  simpl in *; mytac.
  rewrite H14.
  lets Hxx :  mapstoval_load  H15.
  simpl; auto.
  rewrite Hfi.
  lets Hl : load_local H0 Hxx.
  assert (Int.unsigned Int.zero = 0%Z).
  clear. int auto.
  rewrite H in Hl.
  rewrite Hl.
  destruct l.
  lets Hxxx :  mapstoval_load H8; eauto.
  unfold getoff.
  simpl.
  rewrite H14.
  rewrite Hfs.
  simpl.
  simpl in Hxxx.
  assert (Int.repr (Int.unsigned i2) = i2).
  clear .
  int auto.
  rewrite H1.
  assert (exists xx, join x6 xx m).
  clear -H5 H0.
  join auto.
  clear H5 H0.
  mytac.
  eapply load_local; eauto.
  rewrite H14; auto.
  eapply rule_type_val_match_nvundef; eauto.
Qed.


Lemma struct_member_rv_flag_g:
  forall s x id l off t t' P perm decl tid v ls perm1,
    s |= A_dom_lenv ls ** GV x @ Tptr t |=> Vptr l @ perm1 ** PV (get_off_addr l off) @ t' |=> v @ perm ** P ->
    var_notin_dom x ls = true ->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some t' ->
    field_offset id decl = Some off->
    rule_type_val_match t' v = true ->
    s |= Rv efield (ederef (evar x)) id @ t' == v.
Proof.
  introv Hsa Ht Hg Hfi Hfs Hss .
  introv Hsf.
  lets Hx :  dom_lenv_imp_notin_lenv Ht Hsa.
  clear Hsa.
  destruct_s s.
  simpl in *; mytac.
  apply EnvMod.nindom_get in H3;auto.
  unfold get in *;simpl in *.
  rewrite H3.
  rewrite H19.
  rewrite Hfs.
  lets Hxx :  mapstoval_load  H20.
  simpl; auto.
  lets Hl : load_local H5 Hxx.
  assert (Int.unsigned Int.zero = 0%Z).
  clear. int auto.
  rewrite H in Hl.
  rewrite Hl.
  destruct l.
  lets Hxxx :  mapstoval_load H13; eauto.
  unfold getoff.
  simpl.
  unfold get in *; simpl.
  rewrite H3.
  rewrite H19.
  rewrite Hss.
  assert (Int.repr (Int.unsigned i2) = i2).
  clear .
  int auto.
  rewrite H0.
  assert (exists xx, join x12 xx m).
  clear -H5 H10.
  join auto.
  clear H5 H10.
  mytac.
  eapply load_local; eauto.
  unfold get; simpl.
  apply EnvMod.nindom_get in H3;auto.
  rewrite H3; auto.
  unfold get in *; simpl in H19.
  rewrite H19.
  auto.
  eapply rule_type_val_match_nvundef; eauto.
Qed.  

(*
  apply array_type_vallist_match_imp_rule_type_val_match; auto.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id.
  auto.
  lets H100 : Int.unsigned_range m.
  omega.
Qed.
 *)


(*************************************************************)
(*************************************************************)
(*************************************************************)
Theorem struct_member_rv_g_typeneq:
  forall s ls x t l vl tid decl n id t' v P perm tp  tid' decl',
    s |= A_dom_lenv ls ** GV x @ (Tptr tp) |=> Vptr l @ perm ** Astruct l t vl ** P->
    var_notin_dom x ls = true ->
    tp = Tstruct tid' decl' -> 
    t = Tstruct tid decl ->
    sub_decllist decl decl' =true -> 
    good_decllist decl = true ->
    ftype id decl = Some t' ->
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    id_nth id decl = Some n ->
    n < length vl ->
    struct_type_vallist_match t vl ->
    nth_val' n vl = v ->
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros.
  destruct_s s.
  eapply dom_lenv_imp_notin_lenv in H; eauto.
  simpl in *;mytac.
  apply EnvMod.nindom_get in H15;auto.
  unfold get in *; simpl in *.
  rewrite H15.
  rewrite H30.
  lets Hfs : sub_decllist_ftype H5; eauto.
  rewrite Hfs.
  unfold load;unfold loadm.
  rewrite Int.unsigned_zero in H31.
  lets Hf: mapstoval_loadbytes H31.
  simpl;auto.
  destruct Hf.
  destruct H.
  lets Hf: loadbytes_local H17 H.
  assert (loadbytes m (x25, 0%Z) (typelen (Tptr (Tstruct tid' decl'))) = Some x0) by auto.
  rewrite H2.
  rewrite H1.
  destruct l.
  unfold getoff.
  unfold evaltype.
  unfold get ; simpl.
  rewrite H15.
  rewrite H30.
  lets Hx : id_nth_eq H4 H8.
  lets Hoff: nth_id_exists_off Hx.
  destruct Hoff.
  lets Hy: sub_decllist_offset H3 H11.
  rewrite Hy.
  assert (load t' x7 (addrval_to_addr (b, Int.add (Int.repr (Int.unsigned i2)) x1)) =
          Some  (nth_val' n vl)).
  unfold addrval_to_addr.
  lets Hz: nth_val_imp_nth_val'_2 H9.
  rewrite struct_asrt_eq with (n:=n) in H25;eauto.
  unfold sat in H25;fold sat in H25;mytac.
  simpl in H13.
  rewrite Int.repr_unsigned.
  simpl in H18.
  eapply load_local;eauto.
  eapply load_local;eauto.
  eapply mapstoval_load;auto.
  eapply struct_tvmatch_imp_rule_tvmatch;eauto.
  destruct H18;eauto.
  apply map_join_comm in H17.
  eapply load_local;eauto.
  apply EnvMod.nindom_get in  H15.
  unfold get in *; simpl in *.
  rewrite H15.
  rewrite H30.
  eapply sub_decllist_ftype;eauto.
  eapply rule_type_val_match_nvundef;eauto.
  eapply struct_tvmatch_imp_rule_tvmatch;eauto.
Qed.




Theorem struct_member_rv_typeneq:
  forall s x t l vl tid decl n id t' v P perm tp  tid' decl',
    s |= LV x @ (Tptr tp) |=> Vptr l @ perm ** Astruct l t vl ** P->
    tp = Tstruct tid' decl' -> 
    t = Tstruct tid decl ->
    sub_decllist decl decl' =true -> 
    good_decllist decl = true ->
    ftype id decl = Some t' ->
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    id_nth id decl = Some n ->
    n < length vl ->
    struct_type_vallist_match t vl ->
    nth_val' n vl = v ->
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros.
  destruct_s s.
  simpl in *;mytac.
  unfold get in *; simpl in *.
  rewrite H24.
  lets Hfs : sub_decllist_ftype H4; eauto.
  rewrite Hfs.
  unfold load;unfold loadm.
  rewrite Int.unsigned_zero in H25.
  lets Hf: mapstoval_loadbytes H25.
  simpl;auto.
  destruct Hf.
  destruct H.
  lets Hf: loadbytes_local H11 H.
  assert (loadbytes m (x19, 0%Z) (typelen (Tptr (Tstruct tid' decl'))) = Some x2) by auto.
  rewrite H1.
  rewrite H0.
  destruct l.
  unfold getoff.
  unfold evaltype.
  unfold get ; simpl.
  rewrite H24.
  lets Hx : id_nth_eq H3 H7.
  lets Hoff: nth_id_exists_off Hx.
  destruct Hoff.
  lets Hy: sub_decllist_offset H2 H10.
  rewrite Hy.
  assert (load t' x1 (addrval_to_addr (b, Int.add (Int.repr (Int.unsigned i2)) x3)) =
          Some  (nth_val' n vl)).
  unfold addrval_to_addr.
  lets Hz: nth_val_imp_nth_val'_2 H8.
  rewrite struct_asrt_eq with (n:=n) in H19;eauto.
  unfold sat in H19;fold sat in H19;mytac.
  simpl in H13.
  rewrite Int.repr_unsigned.
  simpl in H17.
  apply map_join_comm in H11.
  eapply load_local;eauto.
  eapply load_local;eauto.
  eapply mapstoval_load;auto.
  eapply struct_tvmatch_imp_rule_tvmatch;eauto.
  destruct H17;eauto.
  apply map_join_comm in H11.
  eapply load_local;eauto.
  rewrite H24.
  eapply sub_decllist_ftype;eauto.
  eapply rule_type_val_match_nvundef;eauto.
  eapply struct_tvmatch_imp_rule_tvmatch;eauto.
Qed.


Theorem struct_member_array_rv_g_typeneq:
  forall s ls x t l vl tid decl id t' n P ad perm tt tid' decl',
    s |=   A_dom_lenv ls **  GV x @ (Tptr tt) |=> Vptr l @ perm ** Astruct l t vl ** P->
    var_notin_dom x ls = true ->
    tt = Tstruct tid' decl' -> 
    t = Tstruct tid decl ->
    sub_decllist decl decl'  = true-> 
    ftype id decl = Some (Tarray t' n) ->
    id_addrval l id t = Some ad ->
    s |= Rv (efield (ederef (evar x)) id) @ (Tarray t' n) == Vptr ad.
Proof.
  intros.
  destruct_s s.
  eapply dom_lenv_imp_notin_lenv in H; eauto.
  simpl in *;mytac.
  apply EnvMod.nindom_get in H9;auto.
  unfold get in *; simpl in *.
  rewrite H9.
  rewrite H24.
  lets Hfs : sub_decllist_ftype H4; eauto.
  rewrite Hfs.
  unfold load;unfold loadm.
  rewrite Int.unsigned_zero in H25.
  lets Hf: mapstoval_loadbytes H25.
  simpl;auto.
  destruct Hf.
  destruct H.
  lets Hf: loadbytes_local H11 H.
  assert ( loadbytes m (x25, 0%Z) (typelen (Tptr (Tstruct tid' decl'))) = Some x0);auto.
  rewrite H2.
  rewrite H1.
  destruct l.
  unfold getoff.
  unfold evaltype.
  unfold get ; simpl.
  rewrite H9;rewrite H24.
  unfold id_addrval in H5.
  remember (field_offset id decl ) as X.
  destruct X;tryfalse.
  apply eq_sym in HeqX.
  lets Hac :  sub_decllist_offset HeqX; eauto.
  rewrite Hac.
  rewrite Int.repr_unsigned.
  simpl.
  rewrite Int.repr_unsigned.
  inverts H5;auto.
  apply EnvMod.nindom_get in H9;auto.
  unfold get in *; simpl in *.
  rewrite H9;rewrite H24.
  eapply sub_decllist_ftype; eauto.
  intro; tryfalse.
Qed.


Lemma struct_member_array_rv_typeneq
     : forall s x t l vl tid decl id t' n P ad perm tt decl' tid',
       s
       |= LV x @ Tptr tt |=> Vptr l @ perm ** Astruct l t vl ** P ->
       tt = Tstruct tid' decl' ->
       t = Tstruct tid decl ->
       sub_decllist decl decl' = true ->
       ftype id decl = Some (Tarray t' n) ->
       id_addrval l id t = Some ad ->
       s |= Rv efield (ederef (evar x)) id @ Tarray t' n == Vptr ad.
Proof.
  intros.
  destruct_s s.
  simpl in *;mytac.
  rewrite H18.
  lets Hx: sub_decllist_ftype H2 H3.
  rewrite Hx.
  unfold load;unfold loadm.
  rewrite Int.unsigned_zero in H19.
  lets Hf: mapstoval_loadbytes H19.
  simpl;auto.
  destruct Hf.
  destruct H.
  lets Hf: loadbytes_local H5 H.
  assert ( loadbytes m (x19, 0%Z) (typelen (Tptr (Tstruct tid' decl'))) = Some x2);auto.
  rewrite H1.
  rewrite H0.
  destruct l.
  unfold getoff.
  unfold evaltype.
  rewrite H18.
  unfold id_addrval in H4.
  remember (field_offset id decl ) as X.
  destruct X;tryfalse.
  rewrite Int.repr_unsigned.
  symmetry in HeqX.
  lets Hy: sub_decllist_offset H2 HeqX.
  rewrite Hy.
  simpl.
  rewrite Int.repr_unsigned.
  inverts H4;auto.
  rewrite H18.
  eapply sub_decllist_ftype;eauto.
  intro; tryfalse.
Qed.

Theorem struct_member_rv_general_typeneq:
  forall s  x t l vl tid decl id P v t' perm tp tid' decl',
    s |=  LV x @ (Tptr tp) |=> Vptr l @ perm ** Astruct l t vl ** P->
    t = Tstruct tid decl ->

    tp = Tstruct tid' decl' ->
    sub_decllist decl decl' = true ->
    
    good_decllist decl = true ->
    ftype id decl = Some t' -> 
    (
      isarray_type t'-> 
      exists ad, id_addrval l id t = Some ad /\ v = Vptr ad
    ) ->
    (
      ~ isarray_type t' ->
      (
        exists n,
          (forall a b, t' <> Tstruct a b) /\
          id_nth id decl = Some n /\
          n < length vl /\
          struct_type_vallist_match t vl /\
          nth_val' n vl = v 
      )
    ) -> 
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros.
  mytac.
  assert (isarray_type t' \/ ~isarray_type t' ).
  tauto.
  destruct H0.
  lets Hx: H5 H0.
  mytac.
  unfolds in H0;mytac.
  eapply struct_member_array_rv_typeneq;eauto.
  lets Hx : H6 H0.
  mytac.
  eapply struct_member_rv_typeneq;eauto.
  unfold isarray_type in H0.
  intros.
  introv.
  introv Hf.
  apply H0;eauto.
Qed.


Theorem struct_member_rv_g_general_typeneq:
  forall s ls x t l vl tid decl id P v t' perm tp tid' decl',
    s |=   A_dom_lenv ls **  GV x @ (Tptr tp) |=> Vptr l @ perm ** Astruct l t vl ** P->
    var_notin_dom x ls = true ->
    t = Tstruct tid decl ->
    
    tp = Tstruct tid' decl' ->
    sub_decllist decl decl' = true ->
    
    good_decllist decl = true ->
    ftype id decl = Some t' -> 
    (
      isarray_type t'-> 
      exists ad, id_addrval l id t = Some ad /\ v = Vptr ad
    ) ->
    (
      ~ isarray_type t' ->
      (
        exists n,
          (forall a b, t' <> Tstruct a b) /\
          id_nth id decl = Some n /\
          n < length vl /\
          struct_type_vallist_match t vl /\
          nth_val' n vl = v 
      )
    ) -> 
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros.
  mytac.
  assert (isarray_type t' \/ ~isarray_type t' ).
  tauto.
  destruct H1.
  lets Hx: H6 H1.
  mytac.
  unfolds in H1;mytac.
  eapply struct_member_array_rv_g_typeneq;eauto.
  lets Hx : H7 H1.
  mytac.
  eapply struct_member_rv_g_typeneq;eauto.
  unfold isarray_type in H1.
  intros.
  introv.
  introv Hf.
  apply H1;eauto.
Qed.
