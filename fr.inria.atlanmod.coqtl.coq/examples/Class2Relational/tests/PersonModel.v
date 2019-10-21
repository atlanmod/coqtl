Require Import List.
Require Import String.

Require Import core.Model.

Require Import examples.Class2Relational.ClassMetamodel.

Definition PersonModel : Model ClassMetamodel_EObject ClassMetamodel_ELink :=
  (Build_Model
     (* elements *)
     ((ClassMetamodel_BuildEObject ClassEClass (BuildClass 0 "Person")) :: (ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute 1 false "father")) :: 
      (ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute 2 true "mere")) :: nil)
     (* links *)
     ((ClassMetamodel_BuildELink ClassAttributesEReference (BuildClassAttributes (BuildClass 0 "Person") ((BuildAttribute 1 false "father")::nil))) ::
      (ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType (BuildAttribute 1 false "father") (BuildClass 0 "Person"))) ::
      (ClassMetamodel_BuildELink ClassAttributesEReference (BuildClassAttributes (BuildClass 0 "Person") ((BuildAttribute 2 true "mere")::nil))) ::
      (ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType (BuildAttribute 2 true "mere") (BuildClass 0 "Person"))) :: 
      nil)
  ).
