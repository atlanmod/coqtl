Require Import model.
Require Import List.
Require Import String.
Require Import TT.
Require Import TTSemantics.

Open Scope string.

Compute (eval InputModel 
    (BuildTruthTable "170144208_TruthTable" "" "Test")
    (("a", true)::("b",false)::nil)).
