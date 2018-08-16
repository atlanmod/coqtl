Require Import examples.Class2Relational.ClassMetamodel.

(* Class Metamodel pattern *)
Notation "'[[' r1 ; .. ; r2 ']]'" := (cons (r1: ClassMetamodel_EObject) .. (cons (r2: ClassMetamodel_EObject) nil) ..) (right associativity, at level 9).