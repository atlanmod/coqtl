Require Import String.
Require Import List.

Require Import core.CoqTL.
Require Import core.utils.tPrint.

Require Import example.ClassMetamodel.
Require Import example.RelationalMetamodel.
Require Import example.Class2Relational.
Require Import example.PersonModel.



(* Require Import Class2RelationalVerif. *)

Compute execute Class2Relational PersonModel.
