Require Import List.
Require Import String.

Require Import core.Model.

Require Import transformations.Class2RelationalTest.ClassMetamodel.

(* 
    Class id=0 name='Person'
      Attribute id=1 derived=false name='parent' type='Person'
      Attribute id=2 derived=true name='sibling' type='Person'
*)

Definition PersonModel : Model ClassMetamodel_EObject ClassMetamodel_ELink :=
  (Build_Model
     (* elements *)
     ((Build_ClassMetamodel_EObject ClassEClass (BuildClass 0 "Person")) :: (Build_ClassMetamodel_EObject AttributeEClass (BuildAttribute 1 false "parent")) :: 
      (Build_ClassMetamodel_EObject AttributeEClass (BuildAttribute 2 true "sibling")) :: nil)
     (* links *)
     ((Build_ClassMetamodel_ELink ClassAttributesEReference (BuildClassAttributes (BuildClass 0 "Person") ((BuildAttribute 1 false "parent")::nil))) ::
      (Build_ClassMetamodel_ELink AttributeTypeEReference (BuildAttributeType (BuildAttribute 1 false "parent") (BuildClass 0 "Person"))) ::
      (Build_ClassMetamodel_ELink ClassAttributesEReference (BuildClassAttributes (BuildClass 0 "Person") ((BuildAttribute 2 true "sibling")::nil))) ::
      (Build_ClassMetamodel_ELink AttributeTypeEReference (BuildAttributeType (BuildAttribute 2 true "sibling") (BuildClass 0 "Person"))) :: 
      nil)
  ).
