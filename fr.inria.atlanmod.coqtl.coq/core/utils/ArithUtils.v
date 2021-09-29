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

Fixpoint indexes (length: nat) :=
  match length with
  | 0 => nil
  | S length' => 0 :: (map (fun x => x + 1) (indexes length'))
  end.
(*Fixpoint indexesFrom (length start:nat) : list nat :=
  match length with
  | 0 => nil
  | S length' => start :: indexesFrom length' (start + 1)
  end.

Definition indexes (length: nat) := 
  indexesFrom length 0.*)

Lemma indexes_nat_upperBound:
  forall x len, In x (indexes len) <-> x < len.
Proof.
Admitted.
  (*split; intros.
  - induction len; inversion H.
    + subst len. auto.
    + transitivity len; auto.
  - induction len; inversion H.
    + left. reflexivity.
    + right. auto.
Qed. *)
