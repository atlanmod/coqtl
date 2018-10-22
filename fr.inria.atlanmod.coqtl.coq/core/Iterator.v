(** * Iterator Class **)
Require Export core.Typing.
Require Export core.Decidability.

Class Iterator 
  (IteratorElement: Type) (IteratorClass: Type) 
`{Typing IteratorElement IteratorClass} 
`{Decidability IteratorElement}
`{Decidability IteratorClass} := {}.
