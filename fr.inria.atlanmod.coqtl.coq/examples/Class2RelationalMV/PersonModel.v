Require Import List.

Require Import core.Model.

Require Import example.ClassMetamodel.

Definition PersonModel : Model ClassMetamodel_EObject ClassMetamodel_ELink :=
  (Build_Model
     ((ClassMetamodel_BuildEObject ClassEClass (BuildClass 0 "Person")) :: (ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute 1 false "father")) :: (ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute 2 true "friends")) :: nil)
     ((ClassMetamodel_BuildELink ClassAttributesEReference (BuildClassAttributes (BuildClass 0 "Person") ((BuildAttribute 1 false "father")::(BuildAttribute 2 true "friends")::nil))) :: (ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType (BuildAttribute 1 false "father") (BuildClass 0 "Person"))) :: (ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType (BuildAttribute 2 true "friends") (BuildClass 0 "Person"))) :: nil)
  ).

