Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.Metamodel.
Require Import core.Model.
Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

(* Encoding of Church Number*)

Definition vector := list nat.

Definition churchNum 
  := vector->(vector->vector)->vector.

Definition zero : churchNum 
  := fun x =>fun f => x.

Definition suc : churchNum -> churchNum
  := fun n => fun x  => fun f => f (n x f).

Definition eval: churchNum -> churchNum :=
  fun n => fun x  => fun f => (n x f).

(* Example *)

Definition plus_one (l: list nat) : list nat := map (fun n => n+1) l. 

Eval compute in (eval (suc (zero)) ([1;2;3]) plus_one).

