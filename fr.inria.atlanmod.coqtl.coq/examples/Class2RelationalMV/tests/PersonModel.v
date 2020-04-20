Require Import List.
Require Import String.

Require Import core.Model.

Require Import examples.Class2RelationalMV.ClassMetamodel.

Definition PersonModel : Model ClassMetamodel_EObject ClassMetamodel_ELink :=
  (Build_Model
     (* elements *)
     ((Build_ClassMetamodel_EObject ClassEClass (BuildClass "0" "Person")) :: (Build_ClassMetamodel_EObject AttributeEClass (BuildAttribute "1" false "father")) :: 
      (Build_ClassMetamodel_EObject AttributeEClass (BuildAttribute "2" true "mere")) :: nil)
     (* links *)
     ((Build_ClassMetamodel_ELink ClassAttributesEReference (BuildClassAttributes (BuildClass "0" "Person") ((BuildAttribute "1" false "father")::nil))) ::
      (Build_ClassMetamodel_ELink AttributeTypeEReference (BuildAttributeType (BuildAttribute "1" false "father") (BuildClass "0" "Person"))) ::
      (Build_ClassMetamodel_ELink ClassAttributesEReference (BuildClassAttributes (BuildClass "0" "Person") ((BuildAttribute "2" true "mere")::nil))) ::
      (Build_ClassMetamodel_ELink AttributeTypeEReference (BuildAttributeType (BuildAttribute "2" true "mere") (BuildClass "0" "Person"))) :: 
      nil)
  ).
