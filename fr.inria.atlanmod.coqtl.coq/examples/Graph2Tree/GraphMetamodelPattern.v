Require Import examples.Graph2Tree.GraphMetamodel.

(* Class Metamodel pattern *)
Notation "'[[' r1 ; .. ; r2 ']]'" := (cons (r1: GraphMetamodel_EObject) .. (cons (r2: GraphMetamodel_EObject) nil) ..) (right associativity, at level 9).