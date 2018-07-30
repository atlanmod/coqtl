Require Import String.
Require Import List.

Require Import core.CoqTL.
Require Import core.utils.tPrint.
Require Import core.Model.

Require Import examples.Class2RelationalMV.ClassMetamodel.
Require Import examples.Class2RelationalMV.RelationalMetamodel.
Require Import examples.Class2RelationalMV.Class2Relational.
Require Import examples.Class2RelationalMV.PersonModel.


(* Require Import Class2RelationalVerif. *)

Compute execute Class2Relational PersonModel .

