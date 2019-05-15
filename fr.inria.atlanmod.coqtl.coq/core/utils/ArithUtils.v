Require Import ZArith.
Require Import NotationUtils.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Lemma ge_trans : forall a b c,
  a >= b -> b >= c -> a >= c.
Proof.
  intuition.
Qed.

Lemma O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n.
  apply le_n.
  apply le_S. apply IHn.
Qed.

Lemma n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H.
  apply le_n.
  apply le_S. apply IHle.
Qed.


Lemma ble_nat_true : forall n m,
    ble_nat n m = true -> n <= m.
Proof.
  intros n m. generalize dependent n. induction m.
  - destruct n.
    -- intros. apply le_n.
    -- simpl. intros. inversion H.
  - intros. destruct n.
    -- apply O_le_n.
    -- apply n_le_m__Sn_le_Sm. apply IHm.
                 simpl in H. apply H.
Qed.


Lemma ble_nat_false : forall n m,
    ble_nat n m = false -> n > m.
Proof.
induction n; intros.
- inversion H.
- destruct m.
  -- auto with arith.
  -- apply lt_n_S.
     apply IHn.
     simpl in H.
     assumption.
Qed.



Fixpoint max (l : list nat) : nat :=
  match l with
  | nil => 0
  | a::m => let b:= max m in if ble_nat a b then b else a
  end.

Lemma max_list_upperBound : forall l a ,
  In a l ->
  a <= max l.
Proof.
Admitted.
      
Fixpoint indexes (length: nat): list nat :=
  match length with
  | 0 => nil
  | S length' => (length') :: indexes(length')
  end.
