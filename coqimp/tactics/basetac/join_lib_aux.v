Require Import include_frm.
Require Import join_lib.

Lemma disj_disj_set_disj:
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m a v v',
    isRw v = true ->
    disjoint m1 m ->
    disjoint m2 m ->
    get m2 a = Some v ->
    disjoint (set m1 a v') m.
Proof.
  hy.
Qed.

Lemma disj_disj_set_disj':
  forall (A B T : Type) (MC : PermMap A B T) m1 m2 m a v v',
    isRw v = true ->
    disjoint m m1 ->
    disjoint m m2->
    get m2 a = Some v ->
    disjoint m (set m1 a v').
Proof.
  hy.
Qed.

Lemma sub_set_sub:
  forall (A B T : Type) (MC : PermMap A B T) (m m': T) (a:A) (b:B),
    Maps.sub m m' ->
    Maps.sub (Maps.set m a b) (Maps.set m' a b).
Proof.
  hy.
Qed.

Lemma get_disj_sub_set:
  forall (A B T : Type) (MC : PermMap A B T) m' m M v v' a,
    isRw v = true ->
    get m' a = Some v ->
    disjoint m m' ->
    Maps.sub m M ->
    Maps.sub m (set M a v').
Proof.
  hy.
Qed.


Lemma join_join_join_merge:
  forall (A B T : Type) (MC : PermMap A B T) Ml Ms M Ml' Ms',
    join Ml Ms M -> join Ml' Ms' Ms -> join (merge Ml Ml') Ms' M.
Proof.
  hy.
Qed.

Lemma join_join_minus:
  forall  (A B T : Type) (MC : PermMap A B T) M1 M2 M11 M12 M,
    join M1 M2 M ->
    join M11 M12 M1 ->
    join (minus M M12) M12 M.
Proof.
  hy.
Qed.


Lemma join_join_sub_minus:
  forall  (A B T : Type) (MC : PermMap A B T) M1 M2 M11 M12 M,
    join M1 M2 M ->
    join M11 M12 M1 ->
    Maps.sub M11 (minus M M12).
Proof.
  hy.
Qed.


Lemma minus_sub
: forall  (A B T : Type) (MC : PermMap A B T) M1 M M2,
    usePerm = false ->
    Maps.sub M1 M ->
    disjoint M1 M2 -> Maps.sub M1 (minus M M2).
Proof.
  hy.
Qed.


Lemma join_join_sub_sub_minus:
  forall (A B T : Type) (MC : PermMap A B T) M1 M2 M11 M12 M m,
    join M1 M2 M ->
    join M11 M12 M1 ->
    Maps.sub m M2 ->
    Maps.sub m (minus M M12).
Proof.
  hy.
Qed.

Lemma join_join_sub_disj:
  forall (A B T : Type) (MC : PermMap A B T) M1 M2 M11 M12 M m,
    join M1 M2 M ->
    join M11 M12 M1 ->
    Maps.sub m M2 ->
    disjoint m M11.
Proof.
  hy.
Qed.

Lemma join_merge_minus:
  forall (A B T : Type) (MC : PermMap A B T) M1 M2 M m,
    join M1 M2 M ->
    Maps.sub m M1 ->
    join (merge m M2) (minus M1 m) M.
Proof.
  hy.
Qed.


(**added by xfw**)
Lemma join_sig_get_neq:
  forall (A B T:Type) (X:PermMap A B T) tcbls t x x0 x2 x3,
    usePerm = false ->
    get tcbls t = Some x ->
    t <> x0 ->
    join (sig x0 x3) x2 tcbls ->
    get x2 t = Some x.
Proof.
  hy.
Qed.


Lemma indom_sig_eq:
  forall (A B T:Type) (X:PermMap A B T) a b y,
    indom (sig a y) b ->
    a = b.
Proof.
  intros.
  indom_rewrite.
  infer' (pnil, sig a y) b; crush.
Qed.


Lemma joinsig_indom_neq:
  forall (A B T:Type) (X:PermMap A B T) (a a':A) (b:B) (M M':T),
    join (sig a b) M' M ->
    indom M a' ->
    a<>a' ->
    indom M' a'.
Proof.
  intros.
  indom_rewrite.
  unfold indom.
  exists x.
  hy.
Qed.


Lemma sub_joinsig_get:
  forall (A B T:Type) (X:PermMap A B T) a b m M MM,
    usePerm = false ->
    join (sig a b) m M ->
    Maps.sub M MM ->
    get MM a = Some b.
Proof.
  hy.
Qed.


Lemma joinsig_set_sub_sub:
  forall (A B T:Type) (X:PermMap A B T) t x tcbls tcbls' tls y tls',
    usePerm = false ->
    joinsig t x tcbls tcbls' ->
    set tls t y = tls' ->
    Maps.sub tcbls' tls ->
    Maps.sub tcbls tls'.
Proof.
  intros.
  unfold joinsig in *.
  subst.
  hy.
Qed.
