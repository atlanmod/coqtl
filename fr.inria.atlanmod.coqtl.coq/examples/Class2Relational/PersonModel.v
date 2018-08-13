Require Import List.

Require Import core.Model.

Require Import examples.Class2Relational.ClassMetamodel.

Definition PersonModel : Model ClassMetamodel_EObject ClassMetamodel_ELink :=
  (Build_Model
     ((Build_ClassMetamodel_EObject ClassEClass (BuildClass "0" "Person")) :: (Build_ClassMetamodel_EObject AttributeEClass (BuildAttribute "1" false "father")) :: (Build_ClassMetamodel_EObject AttributeEClass (BuildAttribute "2" true "friends")) :: nil)
     ((Build_ClassMetamodel_ELink ClassAttributesEReference (BuildClassAttributes (BuildClass "0" "Person") ((BuildAttribute "1" false "father")::(BuildAttribute "2" true "friends")::nil))) :: (Build_ClassMetamodel_ELink AttributeTypeEReference (BuildAttributeType (BuildAttribute "1" false "father") (BuildClass "0" "Person"))) :: (Build_ClassMetamodel_ELink AttributeTypeEReference (BuildAttributeType (BuildAttribute "2" true "friends") (BuildClass "0" "Person"))) :: nil)
  ).
