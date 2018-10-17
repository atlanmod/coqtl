Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.
Require Import DecimalNat.
Require Import DecimalString.


Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.Model.
Require Import core.CoqTL.
Require Import core.DefaultIterator.

Require Import examples.Graph2Tree.GraphMetamodel.
Require Import examples.Graph2Tree.GraphMetamodelPattern.
Require Import examples.Graph2Tree.GraphModel.
Require Import examples.Graph2Tree.GraphModel2.


Open Scope coqtl.



Definition Graph2TreeNoIter :=
  transformation Graph2Tree from GraphMetamodel to GraphMetamodel uses DefaultIterator
    with m as GraphModel := [
      rule Node2Node
        from
          n class NodeEClass
        to2 [
          "n" :
            n' class NodeEClass :=
              BuildNode newId (getNodeName n)
        ]
    ].


Close Scope coqtl.


Definition Graph2Tree := parseTransformation (Graph2TreeNoIter). 

