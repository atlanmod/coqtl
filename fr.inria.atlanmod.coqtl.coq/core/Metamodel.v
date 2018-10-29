(** * Metamodel Class **)
Require Export core.Reflective.
Require Export core.Decidability.
Require Export core.Object.

Class Metamodel 
  (ModelElement: Type) (ModelLink: Type) 
  (ModelClass: Type) (ModelReference: Type) 
`{Reflective_Elem: Reflective ModelElement ModelClass} `{Reflective_Link : Reflective ModelLink ModelReference}
`{Decidability ModelClass} `{Decidability ModelReference}
`{Object ModelElement} := {

getReflective_Elem := Reflective_Elem;
getReflective_Link := Reflective_Link;
getModelLink := ModelLink;
}.

