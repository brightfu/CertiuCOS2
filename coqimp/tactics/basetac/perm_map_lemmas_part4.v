Require Import memory.
Require Import language.
Require Import join_lib.
Require Import join_tactics.

Import veg.

Lemma mem_join_join_disjoint_merge_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4 m5 m6 m7,
    usePerm = true ->
    join m1 m2 m3 ->
    join m4 m5 m2 ->
    join m6 m7 m4 ->
    disjoint m1 (merge m7 m5).
  hy.
Qed.

Lemma mem_join_join_disjoint_merge :
  forall (m1:mem) m2 m3 m4 m5 m6 m7,
    join m1 m2 m3 ->
    join m4 m5 m2 ->
    join m6 m7 m4 ->
    disjoint m1 (merge m7 m5).
Proof.
  intros; eapply mem_join_join_disjoint_merge_auto; ica.
Qed.

Lemma disjoint_join_merge_merge :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2 m3 m4,
    join m1 m2 m3 ->
    disjoint m3 m4 ->
    merge m2 (merge m4 m1) = merge m3 m4.
Proof.
  hy.
Qed.

Lemma disjoint_join_join_disjoint :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2 m3 m4 m5 m6,
    disjoint m1 m2 ->
    join m3 m4 m1 ->
    join m5 m6 m2 ->
    disjoint m3 m5.
Proof.
  hy.
Qed.

Lemma disjoint_join_merge_merge' :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2 m3 m4,
    join m1 m2 m3 ->
    disjoint m3 m4 ->
    merge m1 (merge m2 m4) = merge m3 m4.
Proof.
  hy.
Qed.

Lemma disjoint_join_merge_merge'' :
  forall {A B T:Type} {MC:PermMap A B T}
         Mc Ms x x0,
    disjoint Mc Ms ->
    join x x0 Ms ->
    merge (merge x0 Mc) x = merge Mc Ms.
Proof.
  hy.
Qed.

Lemma disjoint_join_join_merge_join_disjoint_merge_merge :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2 m3 m4 m5 m6 m7 m8,
    disjoint m1 m2 ->
    join m3 m4 m1  ->
    join m5 m6 m2  ->
    join m7 m8 (merge m3 m5) ->
    disjoint (merge m4 m7) (merge m6 m8).
Proof.
  hy.
Qed.

Lemma disjoint_join_join_merge4 :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2 m3 m4 m5 m6 m7 m8,
    disjoint m1 m2 ->
    join m3 m4 m1 ->
    join m5 m6 m2 ->
    join m7 m8 (merge m3 m5) ->
    merge (merge m4 m7) (merge m6 m8) = merge m1 m2.
Proof.
  hy.
  invert_flip.
  crush.
Qed.

Lemma disjoint_join_merge_disjoint :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2 m3 m4 m5 m6 m7 m8,
    disjoint m1 m2 ->
    join m3 m4 m1 ->
    join m5 m6 m2 ->
    join m7 m8 (merge m3 m5) ->
    disjoint m8 m6.
Proof.
  hy.
Qed.

Lemma disjoint_join_merge_disjoint' :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2 m3 m4 m5 m6 m7 m8,
    disjoint m1 m2 ->
    join m3 m4 m1 ->
    join m5 m6 m2 ->
    join m7 m8 (merge m3 m5) ->
    disjoint m7 m4.
Proof.
  hy.
Qed.

Lemma join_join_join_disjoint13 :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2 m3 m4 m5 m6 m7,
    join m1 m2 m3 ->
    join m4 m5 m6 ->
    join m3 m6 m7 ->
    disjoint m1 m4.
Proof.
  hy.
Qed.

Lemma mem_join_sub_l_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m,
    usePerm = true ->
    join m1 m2 m -> Maps.sub m1 m.
  hy.
Qed.

Lemma mem_join_sub_l :
  forall (m1:mem) m2 m,
    join m1 m2 m -> Maps.sub m1 m.
Proof.
  intros; eapply mem_join_sub_l_auto; ica.
Qed.

Lemma mem_join_sub_r_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m,
    usePerm = true ->
    join m1 m2 m -> Maps.sub m2 m.
  hy.
Qed.

Lemma mem_join_sub_r :
  forall (m1:mem) m2 m,
    join m1 m2 m -> Maps.sub m2 m.
Proof.
  intros; eapply mem_join_sub_r_auto; ica.
Qed.

Lemma osabst_join_sub_l_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m,
    usePerm = false ->
    join m1 m2 m -> Maps.sub m1 m.
  hy.
Qed.


Lemma osabst_join_sub_l :
  forall (m1:osabst) m2 m,
    join m1 m2 m -> Maps.sub m1 m.
Proof.
  intros; eapply osabst_join_sub_l_auto; ica.
Qed.

Lemma osabst_join_sub_r_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m,
    usePerm = false ->
    join m1 m2 m -> Maps.sub m2 m.
  hy.
Qed.


Lemma osabst_join_sub_r :
  forall (m1:osabst) m2 m,
    join m1 m2 m -> Maps.sub m2 m.
Proof.
  intros; eapply osabst_join_sub_r_auto; ica.
Qed.

Lemma disjoint_sub_merge_r :
  forall {A B T:Type} {MC:PermMap A B T}
         m1 m2,
    disjoint m1 m2 ->
    Maps.sub m2 (merge m1 m2).
Proof.
  hy.
Qed.


Lemma Mem_disjoint_join_disjoint_auto:
  forall (A B T : Type) (MC : PermMap A B T) M1 M2 x1 x0 x,
    usePerm = true ->
    disjoint M1 M2 ->
    join x1 x0 (merge M1 M2) ->
    join x x0 M2 -> 
    disjoint M1 x /\ x1 = merge M1 x.
  intros; split; hy.
Qed.

Lemma Mem_disjoint_join_disjoint:
  forall (M1:mem) M2 x1 x0 x,
    disjoint M1 M2 ->
    join x1 x0 (merge M1 M2) ->
    join x x0 M2 -> 
    disjoint M1 x /\ x1 = merge M1 x.
Proof.
  intros; eapply Mem_disjoint_join_disjoint_auto; ica.
Qed.

Lemma OSAbst_disjoint_join_disjoint_auto:
  forall (A B T : Type) (MC : PermMap A B T) M1 M2 x1 x0 x,
    usePerm = false ->
    disjoint M1 M2 ->
    join x1 x0 (merge M1 M2) ->
    join x x0 M2 -> 
    disjoint M1 x /\ x1 = merge M1 x.
  intros; split; hy.
Qed.

Lemma OSAbst_disjoint_join_disjoint:
  forall (M1:osabst) M2 x1 x0 x,
    disjoint M1 M2 ->
    join x1 x0 (merge M1 M2) ->
    join x x0 M2 -> 
    disjoint M1 x /\ x1 = merge M1 x.
Proof.
  intros; eapply OSAbst_disjoint_join_disjoint_auto; ica.
Qed.

Lemma osabst_join_sub_join_minus_minus_auto :
  forall (A B T : Type) (MC : PermMap A B T) o1 o2 o3 o4,
    usePerm = false ->
    join o1 o2 o3 ->
    Maps.sub o3 o4 ->
    join o1 (minus o4 o3) (minus o4 o2).
  hy.
Qed.

Lemma osabst_join_sub_join_minus_minus :
  forall (o1:osabst) o2 o3 o4,
    join o1 o2 o3 ->
    Maps.sub o3 o4 ->
    join o1 (minus o4 o3) (minus o4 o2).
Proof.
  intros; eapply osabst_join_sub_join_minus_minus_auto; ica.
Qed.

Lemma join_merge23_join :
  forall {A B T:Type} {MC:PermMap A B T} m1 m2 m12 m3 m123,
    usePerm = false ->
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join m1 (merge m2 m3) m123.
Proof.
  hy.
Qed.  


Lemma mem_join_join_merge12_join_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m12 m3 m123,
    usePerm = true ->
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join (merge m1 m2) m3 m123.
  hy.
Qed.

Lemma mem_join_join_merge12_join :
  forall (m1:mem) m2 m12 m3 m123,
    join m1 m2 m12 ->
    join m12 m3 m123 ->
    join (merge m1 m2) m3 m123.
Proof.
  intros; eapply mem_join_join_merge12_join_auto; ica.
Qed.

Lemma get_none_join_sig_set :
  forall {A B T:Type} {MC:PermMap A B T}
         m a x,
    get m a = None ->
    join (sig a x) m (set m a x).
Proof.
  hy.
Qed.


Lemma get_none_disjoint_sig :
  forall {A B T:Type} {MC:PermMap A B T}
         m a x,
    get m a = None ->
    disjoint (sig a x) m.
Proof.
  hy.
Qed.

Lemma mem_join_sig_true_get_l_auto :
  forall (A B T : Type) (MC : PermMap A B T) a x m1 m,
    usePerm = true ->
    isRw x = true ->
    join (sig a x) m1 m ->
    get m a = Some x.
Proof.
  hy.
Qed.  

Lemma mem_join_sig_true_get_l :
  forall a x m1 m,
    join (sig a (true, x)) m1 m ->
    get m a = Some (true, x).
Proof.
  intros.
  eapply mem_join_sig_true_get_l_auto; ica.
Qed.

Lemma mem_join_sig_true_get_eq_auto :
  forall (A B T : Type) (MC : PermMap A B T) a1 a2 x m1 m,
    usePerm = true ->
    isRw x = true ->
    join (sig a1 x) m1 m ->
    a1 <> a2 ->
    get m a2 = get m1 a2.
  hy.
Qed.

Lemma mem_join_sig_true_get_eq :
  forall a1 a2 x (m1:mem) m,
    join (sig a1 (true, x)) m1 m ->
    a1 <> a2 ->
    get m a2 = get m1 a2.
Proof.
  intros; eapply mem_join_sig_true_get_eq_auto; ica.
Qed.



Ltac infer ::= infer_v. (** when meet set, sig ,del , we need replace infer_q with infer_v **)

Lemma mem_join_set_true_comm'_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 a x,
    usePerm = true ->
    get m1 a = None ->
    isRw x = true ->
    join (set m1 a x) m2 m3 ->
    join m1 (set m2 a x) m3.
  hy.
Qed.

Lemma mem_join_set_true_comm' :
  forall (m1:mem) m2 m3 a x,
    get m1 a = None ->
    join (set m1 a (true, x)) m2 m3 ->
    join m1 (set m2 a (true, x)) m3.
Proof.
  intros; eapply mem_join_set_true_comm'_auto; ica.
Qed.

Lemma mem_join_set_true_join'_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 a x x',
    usePerm = true ->
    join m1 m2 m3 ->
    isRw x = true ->
    get m1 a = Some x ->
    isRw x' = true ->
    join (set m1 a x') m2 (set m3 a x').
  hy.
Qed.

Lemma mem_join_set_true_join' :
  forall (m1:mem) m2 m3 a x',
    join m1 m2 m3 ->
    (exists x, get m1 a = Some (true, x)) ->
    join (set m1 a (true, x')) m2 (set m3 a (true, x')).
Proof.
  intros.
  destruct H0.
  intros; eapply mem_join_set_true_join'_auto; ica.
Qed.


Lemma mem_join_get_none_auto :
  forall (A B T : Type) (MC : PermMap A B T)  m1 m2 m3 a,
    usePerm = true ->
    get m1 a = None ->
    get m2 a = None ->
    join m1 m2 m3 ->
    get m3 a = None.
  hy.
Qed.

Lemma mem_join_get_none :
  forall  (m1:mem) m2 m3 a,
    get m1 a = None ->
    get m2 a = None ->
    join m1 m2 m3 ->
    get m3 a = None.
Proof.
  intros; eapply mem_join_get_none_auto; auto.
  exact H.
  exact H0.
  auto.
Qed.

Lemma set_sig_eq :
  forall {A B T:Type} {MC:PermMap A B T} a x x',
    set (sig a x) a x' = sig a x'.
Proof.
  jeauto2.
Qed.  

Lemma mem_join_get_none'_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 a x,
    usePerm = true ->
    isRw x = true ->
    join (sig a x) m1 m2 ->
    get m1 a = None.
  hy.
Qed.

Lemma mem_join_get_none' :
  forall (m1:mem) m2 a x,
    join (sig a (true, x)) m1 m2 ->
    get m1 a = None.
Proof.
  intros; eapply mem_join_get_none'_auto; ica.
Qed.


Lemma mem_sig_true_set_eq_auto :
  forall (A B T : Type) (MC : PermMap A B T) m M a x,
    usePerm = true ->
    isRw x = true ->
    join (sig a x) m M ->
    M = set m a x.
  hy.
Qed.

Lemma mem_sig_true_set_eq :
  forall (m:mem) M a x,
    join (sig a (true, x)) m M ->
    M = set m a (true, x).
Proof.
  intros; eapply mem_sig_true_set_eq_auto; ica.
Qed.

Lemma join_join_merge1:
  forall {A B T:Type} {MC:PermMap A B T} m0 M' M x1 x2,
    join m0 M' M ->
    join x1 x2 M' ->
    join (merge x1 m0) x2 M.
Proof.
  hy.
Qed.

Lemma join_sig_get_r :
  forall {A B T:Type} {MC:PermMap A B T}
         e1 e2 t t' x x',
    usePerm = false ->
    join (sig t x) e1 e2 ->
    t' <> t ->
    get e2 t' = Some x' ->
    get e1 t' = Some x'.
Proof.
  hy.
Qed.


Lemma mem_join_disjoint_merge_minus_merge_eq_auto :
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m3 m4,
    usePerm = true ->
    join m1 m2 m3 ->
    disjoint m3 m4 ->
    merge m2 m4 = minus (merge m3 m4) m1.
  hy.
Qed.

Lemma mem_join_disjoint_merge_minus_merge_eq :
  forall (m1:mem) m2 m3 m4,
    join m1 m2 m3 ->
    disjoint m3 m4 ->
    merge m2 m4 = minus (merge m3 m4) m1.
Proof.
  intros; eapply mem_join_disjoint_merge_minus_merge_eq_auto; ica.
Qed.
