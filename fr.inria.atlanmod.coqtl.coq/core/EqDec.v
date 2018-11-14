(** * Decidability **)
Require Import String.


Class EqDec (A: Type) :=
  {
    (* Decidability of equality *)
    eqDec: forall (c1:A) (c2:A), { c1 = c2 } + { c1 <> c2 };

  }.
