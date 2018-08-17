Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.Model.
Require Import core.CoqTL.

Require Import examples.ClassGraph2Tree.ClassMetamodel.
Require Import examples.ClassGraph2Tree.ClassMetamodelPattern.

Definition rootClass (m : ClassModel) : ClassMetamodel_EObject :=
  hd ((BuildClass "" ""): ClassMetamodel_EObject) (allModelElements m).

Definition ClassGraph2Tree' :=
  transformation ClassGraph2Tree from ClassMetamodel to ClassMetamodel
    with m as ClassModel := [

      rule Class2Class
        from
          element c class ClassEClass
        to [
          output "cl"
            element c' class ClassEClass :=
              BuildClass newId (getClassName c)
            links [
              reference ClassAttributesEReference :=
                attrs <- getClassAttributes c m;
                attrs' <- resolveAll ClassGraph2Tree m "at" AttributeEClass
                  (map (fun a:Attribute => [[ a ]]) attrs);
                return BuildClassAttributes c' attrs'
             ]
        ];

      rule Attribute2Attribute
        from
          element a class AttributeEClass 
        to [
          output "at"
            element a' class AttributeEClass := 
               BuildAttribute newId (getAttributeMultiValued a) (getAttributeName a)
            links [
              reference AttributeTypeEReference :=
                cl <- getAttributeType a m;
                cl' <- resolve ClassGraph2Tree m "cl" ClassEClass [[ cl ]];
                return BuildAttributeType a' cl'
            ] 
        ]
  ].

Definition ClassGraph2Tree := parseTransformation ClassGraph2Tree'.
