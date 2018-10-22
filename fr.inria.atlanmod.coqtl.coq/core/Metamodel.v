(** * Metamodel Class **)
Require Export core.Typing.
Require Export core.Decidability.
Require Export core.Object.

Class Metamodel 
  (ModelElement: Type) (ModelLink: Type) 
  (ModelClass: Type) (ModelReference: Type) 
`{Typing ModelElement ModelClass} `{Typing ModelLink ModelReference}
`{Decidability ModelClass} `{Decidability ModelReference}
`{Object ModelElement} := {}.
