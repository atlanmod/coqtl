Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Omega.
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Semantics.

Require Import examples.TT2BDD.TT.
Require Import examples.TT2BDD.BDD.
Require Import examples.TT2BDD.TT2BDDAbstract.
Require Import examples.TT2BDD.tests.TTModel.

Compute (execute TT2BDD TTable_OR).