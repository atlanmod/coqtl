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

Fixpoint indexes (length: nat): list nat :=
  match length with
  | 0 => nil
  | S length' => (length') :: indexes(length')
  end.

Lemma indexes_nat_upperBound:
  forall x len, In x (indexes len) <-> x < len.
Proof.
  split; intros.
  - induction len; inversion H.
    + subst len. auto.
    + transitivity len; auto.
  - induction len; inversion H.
    + left. reflexivity.
    + right. auto.
Qed.
