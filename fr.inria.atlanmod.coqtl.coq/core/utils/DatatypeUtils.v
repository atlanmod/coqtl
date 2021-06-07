Require Import core.utils.CpdtTactics.

Definition isNone (A: Type) (e : option A) : bool :=
 match e with
  | None => true
  | Some a => false
 end.

Lemma option_res_dec :
   forall {A B: Type} (f: A -> option B),
      forall a: A, f a <> None <->
      (exists (b: B),
          f a = Some b).
Proof.
  intros. 
  split. 
  - destruct (f a) as [ fa | ].
    -- exists fa. reflexivity.
    -- congruence.
  - intro.
    crush.
Qed.

Theorem None_is_not_non_None :
  forall {T : Type} (x : option T), not (x <> None) -> x = None.
Proof.
  intros. destruct x.
  - destruct H. discriminate.
  - reflexivity.
Qed.
