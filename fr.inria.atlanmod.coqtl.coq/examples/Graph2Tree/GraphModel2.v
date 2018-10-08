Require Import List.

Require Import core.Model.

Require Import examples.Graph2Tree.GraphMetamodel.

Definition testGraphModel2 : Model GraphMetamodel_EObject GraphMetamodel_ELink :=
  (Build_Model
     (
      (Build_GraphMetamodel_EObject NodeEClass (BuildNode "0" "P")) 
      :: (Build_GraphMetamodel_EObject NodeEClass (BuildNode "1" "A"))
      :: (Build_GraphMetamodel_EObject NodeEClass (BuildNode "2" "B"))
      :: (Build_GraphMetamodel_EObject NodeEClass (BuildNode "3" "C"))
      :: nil)
     (
      (Build_GraphMetamodel_ELink NodeEdgesEReference (BuildNodeEdges (BuildNode "0" "P") ((BuildNode "1" "A")::(BuildNode "2" "B")::(BuildNode "3" "C")::nil))) 
      :: (Build_GraphMetamodel_ELink NodeEdgesEReference (BuildNodeEdges (BuildNode "1" "A") ((BuildNode "2" "B")::nil) )) 
      :: (Build_GraphMetamodel_ELink NodeEdgesEReference (BuildNodeEdges (BuildNode "2" "B") ((BuildNode "1" "A")::(BuildNode "3" "C")::nil) )) 
      :: nil)
  ).
