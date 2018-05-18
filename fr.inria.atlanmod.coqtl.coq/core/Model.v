Require Import core.Metamodel.

Set Implicit Arguments.

(** * Model
  Each model is constructed by a list of {@code ModelElement} and {@ModelLink}. **)

Inductive Model (ModelElement: Type) (ModelLink: Type): Type :=
  BuildModel: list ModelElement -> list ModelLink -> Model ModelElement ModelLink.

Definition allModelElements {ModelElement: Type} {ModelLink: Type} (m : Model ModelElement ModelLink) : list ModelElement :=
  match m with BuildModel l _ => l end.

Definition allModelLinks {ModelElement: Type} {ModelLink: Type} (m : Model ModelElement ModelLink) : list ModelLink :=
  match m with BuildModel _ l => l end. 