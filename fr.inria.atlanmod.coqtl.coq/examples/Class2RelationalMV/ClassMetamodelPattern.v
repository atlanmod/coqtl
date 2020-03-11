Require Import examples.Class2RelationalMV.ClassMetamodel.

(* Class Metamodel pattern *)
Notation "'[[' r1 ; .. ; r2 ']]'" := (cons (ClassMetamodel_toEObject r1) .. (cons (ClassMetamodel_toEObject r2) nil) ..) (right associativity, at level 9).