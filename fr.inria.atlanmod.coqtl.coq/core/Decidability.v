(** * Decidability Class **)

Class Decidability (A: Type)  :=
  {
    (* Decidability of equality *)
    eq_dec: forall (c1:A) (c2:A), { c1 = c2 } + { c1 <> c2 };
  }.
