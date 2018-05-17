Require Import List.

Require Import core.CoqTL.

Require Import example.ClassMetamodel.

Definition PersonModel : Model ClassMetamodel_EObject ClassMetamodel_ELink :=
  (BuildModel
     ((ClassMetamodel_BuildEObject ClassEClass (BuildClass 0 "Person")) :: (ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute 1 false "father")) :: nil)
     ((ClassMetamodel_BuildELink ClassAttributesEReference (BuildClassAttributes (BuildClass 0 "Person") ((BuildAttribute 1 false "father")::nil))) ::
      (ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType (BuildAttribute 1 false "father") (BuildClass 0 "Person"))) :: nil)
  ).


