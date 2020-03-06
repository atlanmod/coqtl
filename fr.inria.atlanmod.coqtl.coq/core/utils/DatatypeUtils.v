Require Import core.utils.CpdtTactics.

Lemma option_res_dec : 
   forall {A B: Type} (f: A -> option B),
      forall a: A, f a <> None ->
      (exists (b: B),
          f a = Some b).
Proof.
  intros.
  induction (f a).
  - exists a0. crush.
  - crush.
Qed.