(** * Iterator Class **)
Require Export core.Typing.
Require Export core.Decidability.

Class Iterator 
  (IteratorElement: Type) (IteratorClass: Type) 
`{Typing_Elem: Typing IteratorElement IteratorClass} 
`{Decidability IteratorElement}
`{Decidability IteratorClass} := {
getIterTyping_Elem := Typing_Elem;
}.
