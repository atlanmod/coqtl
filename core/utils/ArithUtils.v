Require Import Arith.

Require Import NotationUtils.

Definition ble_nat := leb.

Definition max (l : list nat) : nat :=
  fold_right max 0 l.

Lemma max_list_upperBound : forall l a ,
  In a l ->
  a <= max l.
Proof.
  intros.
  induction l; simpl.
  - contradiction.
  - apply Nat.max_le_iff.
    destruct H; subst; auto.
Qed.
