Require Export List.

(* if e1 is successfully evaluated to x, then evaluate e2, otherwise stop *)
Notation "x <- e1 ; e2" :=
  (match e1 with
   | None => None
   | Some x => e2 end)
    (right associativity, at level 60).


Notation "'return' x" := ( Some x ) (no associativity, at level 60).

(*Notation "'when' b 'perform' m" := (if b then m else None) (no associativity, at level 60).*)

Fixpoint applyAll {A: Type} {B: Type} (lf : list (A -> B)) (lx : list A) : list B :=
  match lf, lx with
  | f::llf, x::llx => (f x) :: (applyAll llf llx)
  | _, _ => nil
  end.

Notation "'[' r1 ; .. ; r2 ']'" :=
  (cons r1 .. (cons r2 nil) ..)
    (right associativity, at level 9).
