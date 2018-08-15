Set Implicit Arguments.

(** * Model
  Each model is constructed by a list of {@code ModelElement} and {@ModelLink}. **)

Class Model (ModelElement: Type) (ModelLink: Type) :=
  {
    modelElements : list ModelElement;
    modelLinks : list ModelLink;
  }.

Definition allModelElements {ModelElement: Type} {ModelLink: Type} (m: Model ModelElement ModelLink) : list ModelElement :=
  (@modelElements _ _ m).

Definition allModelLinks {ModelElement: Type} {ModelLink: Type} (m: Model ModelElement ModelLink) : list ModelLink :=
  (@modelLinks _ _ m).

(*
 allModelElements and allModelLinks are fields of record Model.
 To use them on a Model m:
 @allModelElements _ _ a.
 *)