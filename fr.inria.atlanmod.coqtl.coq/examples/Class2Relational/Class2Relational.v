Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.CoqTL.

Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.
Require Import examples.Class2Relational.ClassMetamodelPattern.

Definition Class2RelationalConcrete :=
  transformation Class2Relational from ClassMetamodel to RelationalMetamodel
    with m as ClassModel := [

      rule Class2Table
        from
          element c class ClassEClass
        to [
          output "tab"
            element t class TableEClass :=
              BuildTable newId (getClassName c)
            links [
              reference TableColumnsEReference :=
                attrs <- getClassAttributes c m;
                cols <- resolveAll Class2Relational m "col" ColumnEClass
                  (map (fun a:Attribute => [[ a ]]) attrs);
                return BuildTableColumns t cols
             ]
        ];

      rule Attribute2Column
        from
          element a class AttributeEClass 
            when negb (getAttributeMultiValued a)
        to [
          output "col"
            element c class ColumnEClass := 
               BuildColumn newId (getAttributeName a)
            links [
              reference ColumnReferenceEReference :=
                cl <- getAttributeType a m;
                tb <- resolve Class2Relational m "tab" TableEClass [[ cl ]];
                return BuildColumnReference c tb
            ] 
        ]
  ].

Definition Class2Relational := parseTransformation Class2RelationalConcrete.
