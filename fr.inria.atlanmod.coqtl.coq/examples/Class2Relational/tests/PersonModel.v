Require Import List.
Require Import String.

Require Import core.Model.

Require Import examples.Class2Relational.ClassMetamodel.

(* 
    Class id=0 name='Person'
      Attribute id=1 derived=false name='parent' type='Person'
      Attribute id=2 derived=true name='sibling' type='Person'
*)

Definition PersonModel : Model ClassMetamodel_EObject ClassMetamodel_ELink :=
  (Build_Model
     (* elements *)
     ((ClassMetamodel_BuildEObject ClassEClass (BuildClass 0 "Person")) :: (ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute 1 false "parent")) :: 
      (ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute 2 true "sibling")) :: nil)
     (* links *)
     ((ClassMetamodel_BuildELink ClassAttributesEReference (BuildClassAttributes (BuildClass 0 "Person") ((BuildAttribute 1 false "parent")::nil))) ::
      (ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType (BuildAttribute 1 false "parent") (BuildClass 0 "Person"))) ::
      (ClassMetamodel_BuildELink ClassAttributesEReference (BuildClassAttributes (BuildClass 0 "Person") ((BuildAttribute 2 true "sibling")::nil))) ::
      (ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType (BuildAttribute 2 true "sibling") (BuildClass 0 "Person"))) :: 
      nil)
  ).
