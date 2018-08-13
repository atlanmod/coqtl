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

       rule "Class2Table"
         from
           element c class ClassEClass from ClassMetamodel
         to
          [
           output "tab"
             element t class TableEClass from RelationalMetamodel :=
               BuildTable newId (getClassName c)
             links
               [
                 reference TableColumnsEReference from RelationalMetamodel :=
                   attrs <- getClassAttributes c m;
                   cols <- (resolveAll Class2Relational m "col" ColumnEClass
                                       (map (fun a:Attribute => [a: ClassMetamodel_EObject]) attrs));
                   key <- resolve Class2Relational m "key" ColumnEClass [c: ClassMetamodel_EObject];
                   return BuildTableColumns t (key :: cols)
               ];
           output "key"
             element k class ColumnEClass from RelationalMetamodel :=
               BuildColumn newId (getClassName c ++ "id")
             links nil
          ];

      rule "SinglevaluedAttribute2Column"
        from
          element a class AttributeEClass from ClassMetamodel 
            when (negb (getAttributeMultiValued a))
        to
         [
          output "col"
            element c class ColumnEClass from RelationalMetamodel := 
               BuildColumn newId (getAttributeName a)
            links
              [
                reference ColumnReferenceEReference from RelationalMetamodel :=
                  cl <- getAttributeType a m;
                  tb <- resolve Class2Relational m "tab" TableEClass [cl: ClassMetamodel_EObject];
                  return BuildColumnReference c tb
              ]
         ];

      rule "MultivaluedAttribute2Column"
        from
          element a class AttributeEClass from ClassMetamodel 
            when (getAttributeMultiValued a)
        to
         [
          output "col"
            element c class ColumnEClass from RelationalMetamodel := 
               BuildColumn newId (getAttributeName a)
            links
              [
                reference ColumnReferenceEReference from RelationalMetamodel :=
                  tb <- resolve Class2Relational m "pivot" TableEClass [a: ClassMetamodel_EObject];
                  return BuildColumnReference c tb
              ];
                 
          output "pivot"
            element t class TableEClass from RelationalMetamodel := 
               BuildTable newId (getAttributeName a ++ "Pivot")
            links
              [
                reference TableColumnsEReference from RelationalMetamodel :=
                  psrc <- resolve Class2Relational m "psrc" ColumnEClass [a: ClassMetamodel_EObject];
                  ptrg <- resolve Class2Relational m "ptrg" ColumnEClass [a: ClassMetamodel_EObject];
                  return BuildTableColumns t [psrc; ptrg]
              ];
                 
          output "psrc"
            element c class ColumnEClass from RelationalMetamodel := 
               BuildColumn newId "key"
            links nil;
                 
          output "ptrg"
            element c class ColumnEClass from RelationalMetamodel := 
               BuildColumn newId (getAttributeName a)
            links
              [
                reference ColumnReferenceEReference from RelationalMetamodel :=
                  cl <- getAttributeType a m;
                  tb <- resolve Class2Relational m "tab" TableEClass [cl: ClassMetamodel_EObject];
                  return BuildColumnReference c tb
              ] 
         ]

  ].

Print Class2RelationalConcrete. 
(* Compute maxArity (parseTransformation Class2Relational). *)

Definition Class2Relational := parseTransformation Class2RelationalConcrete.

                                              