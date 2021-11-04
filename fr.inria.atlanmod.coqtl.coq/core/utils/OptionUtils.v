Require Import String.

Definition valueOption {A: Type} (a: option A) (default: A) : A := 
  match a with
    | None => default
    | Some s => s
  end.

Class ValueOption (A: Type) := {
   value : option A -> A
}.

Instance ValueString : ValueOption string := {
   value (a: option string) := valueOption a ""%string
}.
