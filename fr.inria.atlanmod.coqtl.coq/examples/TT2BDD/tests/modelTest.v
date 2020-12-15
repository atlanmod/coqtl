Require Import model.
Require Import List.
Require Import String.
Require Import TT.
Require Import TTSemantics.

Open Scope string.

(* We want to prove the following equivalence: 
   given an assignment for all input ports, and given an output port, 
   the TT and the BDD give the same value for that output port *)

Compute (valueOf (eval InputModel 
    (BuildTruthTable "170144208_TruthTable" "" "Test")
    (("a", false)::("b",true)::nil))
    "s").
