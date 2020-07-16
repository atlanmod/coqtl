Require Import examples.Class2RelationalMV.RelationalMetamodel.

(* Rules *)
Notation "'[[' r1 ; .. ; r2 ']]'" := (cons (r1: RelationalMetamodel_EObject) .. (cons (r2: RelationalMetamodel_EObject) nil) ..) (right associativity, at level 9).