Require Import List.

Require Import core.Model.

Require Import examples.Graph2Tree.GraphMetamodel.

Definition testGraphModel : Model GraphMetamodel_EObject GraphMetamodel_ELink :=
  (Build_Model
     (
      (Build_GraphMetamodel_EObject NodeEClass (BuildNode "0" "A")) 
      :: (Build_GraphMetamodel_EObject NodeEClass (BuildNode "1" "B")) 
      :: nil)
     (
      (Build_GraphMetamodel_ELink NodeEdgesEReference (BuildNodeEdges (BuildNode "0" "A") ((BuildNode "1" "B")::nil))) 
      :: (Build_GraphMetamodel_ELink NodeEdgesEReference (BuildNodeEdges (BuildNode "1" "B") ((BuildNode "0" "A")::nil) )) 
      :: nil)
  ).
