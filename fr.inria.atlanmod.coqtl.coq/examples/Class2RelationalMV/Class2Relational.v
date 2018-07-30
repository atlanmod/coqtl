Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.CoqTL.

Require Import examples.Class2RelationalMV.ClassMetamodel.
Require Import examples.Class2RelationalMV.RelationalMetamodel.

Definition Class2RelationalConcrete :=
  transformation Class2Relational from ClassMetamodel to RelationalMetamodel
    with m as ClassModel := [

       rule Class2Table
         from
           element c class ClassEClass from ClassMetamodel
             when true
         to
          [
           output "tab"
             element t class TableClass from RelationalMetamodel :=
               BuildTable (getClassId c) (getClassName c)
             links
               [
                 reference TableColumnsReference from RelationalMetamodel :=
                   attrs <- getClassAttributes c m;
                    cols <- (resolveAll Class2Relational m "col" ColumnClass
                                       (map (fun a:Attribute => [ClassMetamodel_toEObject a]) attrs));
                    key <- resolve Class2Relational m "key" ColumnClass [ClassMetamodel_toEObject c];
                   return BuildTableColumns t (cons key cols)
               ];
           output "key"
             element k class ColumnClass from RelationalMetamodel :=
               BuildColumn (getClassId c) (append "id" (getClassName c))
             links nil
          ];

      rule SinglevaluedAttribute2Column
        from
          element a class AttributeEClass from ClassMetamodel 
            when (negb (getAttributeMultivalued a))
        to
         [
          output "col"
            element c class ColumnClass from RelationalMetamodel := 
               BuildColumn (getAttributeId a) (getAttributeName a)
            links
              [
                reference ColumnReferenceReference from RelationalMetamodel :=
                  cl <- getAttributeType a m;
                  tb <- resolve Class2Relational m "tab" TableClass [ClassMetamodel_toEObject cl];
                  return BuildColumnReference c tb
              ] 
         ];

      rule MultivaluedAttribute2Column
        from
          element a class AttributeEClass from ClassMetamodel 
            when (getAttributeMultivalued a)
        to
         [
          output "col"
            element c class ColumnClass from RelationalMetamodel := 
               BuildColumn (getAttributeId a) (getAttributeName a)
            links
              [
                reference ColumnReferenceReference from RelationalMetamodel :=
                  tb <- resolve Class2Relational m "pivot" TableClass [ClassMetamodel_toEObject a];
                  return BuildColumnReference c tb
              ];
                 
           output "pivot"
            element t class TableClass from RelationalMetamodel := 
               BuildTable (getAttributeId a) (append "Pivot" (getAttributeName a))
            links
              [
                reference TableColumnsReference from RelationalMetamodel :=
                  psrc <- resolve Class2Relational m "psrc" ColumnClass [ClassMetamodel_toEObject a];
                  ptrg <- resolve Class2Relational m "ptrg" ColumnClass [ClassMetamodel_toEObject a];
                  return BuildTableColumns t [psrc; ptrg]
              ];
                 
            output "psrc"
            element c class ColumnClass from RelationalMetamodel := 
               BuildColumn (getAttributeId a) "key"
            links nil;
                 
            output "ptrg"
            element c class ColumnClass from RelationalMetamodel := 
               BuildColumn (getAttributeId a) (getAttributeName a)
            links
              [
                reference ColumnReferenceReference from RelationalMetamodel :=
                  cl <- getAttributeType a m;
                  tb <- resolve Class2Relational m "tab" TableClass [ClassMetamodel_toEObject cl];
                  return BuildColumnReference c tb
              ] 
         ]

  ].

Print Class2RelationalConcrete. 
(* Compute maxArity (parseTransformation Class2Relational). *)

Definition Class2Relational := parseTransformation Class2RelationalConcrete.
