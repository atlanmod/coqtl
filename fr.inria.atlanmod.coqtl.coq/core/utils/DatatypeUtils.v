Require Import core.utils.CpdtTactics.

Lemma option_res_dec :
   forall {A B: Type} (f: A -> option B),
      forall a: A, f a <> None ->
      (exists (b: B),
          f a = Some b).
Proof.
  intros. destruct (f a) as [ fa | ].
  - exists fa. reflexivity.
  - congruence.
Qed.
