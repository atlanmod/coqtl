Require Import model.
Require Import List.
Require Import String.
Require Import TT.
Require Import TTSemantics.

Open Scope string.



Compute (valueOf (eval InputModel 
    (BuildTruthTable "170144208_TruthTable" "" "Test")
    (("a", false)::("b",true)::nil))
    "s").

Compute (allInputPorts InputModel (BuildTruthTable "170144208_TruthTable" "" "Test")).