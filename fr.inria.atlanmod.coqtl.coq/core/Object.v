Set Implicit Arguments.
Require Import String.

Class Object (ModelElement: Type) :=
  {
    getId : ModelElement -> string; 
    setId : ModelElement -> string -> ModelElement
  }.
