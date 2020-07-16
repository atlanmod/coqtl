(**

 Definition of Model

 **)


Set Implicit Arguments.

Class Model (ModelElement: Type) (ModelLink: Type) :=
  {
    modelElements : list ModelElement;
    modelLinks : list ModelLink;
  }.

Definition allModelElements {ModelElement: Type} {ModelLink: Type} (m: Model ModelElement ModelLink) : list ModelElement :=
  (@modelElements _ _ m).

Definition allModelLinks {ModelElement: Type} {ModelLink: Type} (m: Model ModelElement ModelLink) : list ModelLink :=
  (@modelLinks _ _ m).
