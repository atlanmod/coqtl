Require Import examples.Graph2Tree.GraphMetamodel.

(* Class Metamodel pattern *)
Notation "'[[' r1 ; .. ; r2 ']]'" := (cons (GraphMetamodel_toEObject r1) .. (cons (GraphMetamodel_toEObject r2) nil) ..) (right associativity, at level 9).