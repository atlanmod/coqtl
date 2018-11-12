(** * Metamodel **)
Require Import String.


Class Iterator (IteratorElement: Type) :=
  {
    (* Decidability of equality *)
    eqIteratorElement_dec: forall (c1:IteratorElement) (c2:IteratorElement), { c1 = c2 } + { c1 <> c2 };

  }.
