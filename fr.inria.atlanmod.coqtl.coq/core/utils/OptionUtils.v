Require Import String.

Definition valueOption {A: Type} (a: option A) (default: A) := 
  match a with
    | None => default
    | Some s => s
  end.

Definition valueString (a: option string) :=
  valueOption a ""%string.
