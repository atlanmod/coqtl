Set Implicit Arguments.

Class EqDec (A : Type) :=
  { eq_b : A -> A -> bool ; }.

(* To replace with
Class EqDec (A : Type) :=
  eq_dec : forall (x y : A), {x = y} + {x <> y}.

Definition eq_b {A: Type} `{EqDec A} (x y : A) : bool :=
  if eq_dec x y then true else false.
*)
