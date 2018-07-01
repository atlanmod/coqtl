Require Import String.
Require Import List.

Require Import coqtl.transformation.CoqTL.

Require Import coqtl.test.Class2Relational.ClassMetamodel.
Require Import coqtl.test.Class2Relational.RelationalMetamodel.
Require Import coqtl.test.Class2Relational.Class2Relational.
Require Import coqtl.test.Class2Relational.PersonModel.



(* Require Import Class2RelationalVerif. *)

Compute execute Class2Relational PersonModel.
