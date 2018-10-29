(** * Iterator Class **)
Require Export core.Reflective.
Require Export core.Decidability.

Class Iterator 
  (IteratorElement: Type) (IteratorClass: Type) 
`{Reflective_Elem: Reflective IteratorElement IteratorClass} 
`{Decidability IteratorElement}
`{Decidability IteratorClass} := {
getIterReflective_Elem := Reflective_Elem;
}.
