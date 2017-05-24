(* Require Export mathlib. *)
Require Export  OSTimeDlyPure.
(*Need to be fixed*)
Require Import ucos_include.
Local Open Scope Z_scope.


Lemma range_ostcby:
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11,
    RL_TCBblk_P
      (x1
         :: x2
         :: x3
         :: x4
         :: Vint32 x5
         :: Vint32 x6
         :: Vint32 x7
         :: Vint32 x8
         :: Vint32 x9 :: Vint32 x10 :: Vint32 x11 :: nil) ->
    Int.unsigned x9 < 8 /\  Int.unsigned x10 <=128.
Proof.
  introv Hs.

  funfold Hs.
  clear -H13.
  mauto.
Qed.

