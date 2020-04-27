Require Import String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Strings.Ascii.

Definition natToDigit (n : nat) : ascii :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | _ => "9"
  end.

Fixpoint natToString' (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
  | 0 => acc'
  | S time' =>
    match n / 10 with
    | 0 => acc'
    | n' => natToString' time' n' acc'
    end
  end.

Definition natToString (n : nat) : string :=
  natToString' n n "".


Definition boolToString (b: bool) : string :=
  if b then "true" else "false".
