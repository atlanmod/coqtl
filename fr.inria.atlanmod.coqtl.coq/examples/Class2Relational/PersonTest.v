Require Import String.
Require Import List.

Require Import core.CoqTL.
Require Import core.utils.tPrint.

Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.
Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.PersonModel.



(* Require Import Class2RelationalVerif. *)

Compute execute Class2Relational PersonModel.
