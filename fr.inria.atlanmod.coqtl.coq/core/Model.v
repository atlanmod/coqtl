Require Import core.Metamodel.

Set Implicit Arguments.

(** * Model
  Each model is constructed by a list of {@code ModelElement} and {@ModelLink}. **)


Class Model (ModelElement: Type) (ModelLink: Type) :=
  {
    allModelElements : list ModelElement;
    allModelLinks : list ModelLink;
  }.

(*
 allModelElements and allModelLinks are fields of record Model.
 To use them on a Model m:
 @allModelElements _ _ a.
 *)