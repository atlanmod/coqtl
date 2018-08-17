Require Import examples.ClassGraph2Tree.ClassMetamodel.

(* Class Metamodel pattern *)
Notation "'[[' r1 ; .. ; r2 ']]'" := (cons (r1: ClassMetamodel_EObject) .. (cons (r2: ClassMetamodel_EObject) nil) ..) (right associativity, at level 9).