Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Semantics.

Require Import transformations.TT2BDD.TT.
Require Import transformations.TT2BDD.BDD.
Require Import transformations.TT2BDD.TT2BDDAbstract.
Require Import transformations.TT2BDD.tests.TTModel.

Compute (execute TT2BDD TTable_OR).