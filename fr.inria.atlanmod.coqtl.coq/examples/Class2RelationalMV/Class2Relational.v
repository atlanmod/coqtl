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
Require Import examples.Class2RelationalMV.ClassMetamodelPattern.

Open Scope coqtl.

Definition Class2RelationalMVConcrete :=
  transformation Class2Relational from ClassMetamodel to RelationalMetamodel
    with m as ClassModel := [

      rule Class2Table
        from
          c class ClassEClass
        to [
          "tab" :
            t class TableEClass :=
              BuildTable newId (getClassName c)
            with [
              ref TableColumnsEReference :=
                attrs <- getClassAttributes c m;
                cols <- (resolveAll Class2Relational m "col" ColumnEClass
                  (map (fun a:Attribute => [[ a ]]) attrs));
                key <- resolve Class2Relational m "key" ColumnEClass [[ c ]];
                return BuildTableColumns t (key :: cols)
            ]; 
          "key" :
            k class ColumnEClass :=
              BuildColumn newId (getClassName c ++ "id")
        ];

      rule SinglevaluedAttribute2Column
        from
          a class AttributeEClass 
            when negb (getAttributeMultiValued a)
        to [
          "col" :
            c class ColumnEClass := 
              BuildColumn newId (getAttributeName a)
            with [
              ref ColumnReferenceEReference :=
                cl <- getAttributeType a m;
                tb <- resolve Class2Relational m "tab" TableEClass [[ cl ]];
                return BuildColumnReference c tb
            ]
        ];
      
      rule MultivaluedAttribute2Column
        from
          a class AttributeEClass 
            when getAttributeMultiValued a
        to [
          "col" :
            c class ColumnEClass := 
              BuildColumn newId (getAttributeName a)
            with [
              ref ColumnReferenceEReference :=
                tb <- resolve Class2Relational m "pivot" TableEClass [[ a ]];
                return BuildColumnReference c tb
            ];
                 
          "pivot" :
            t class TableEClass := 
              BuildTable newId (getAttributeName a ++ "Pivot")
            with [
               ref TableColumnsEReference :=
                 psrc <- resolve Class2Relational m "psrc" ColumnEClass [[ a ]];
                 ptrg <- resolve Class2Relational m "ptrg" ColumnEClass [[ a ]];
                 return BuildTableColumns t [psrc; ptrg]
            ];
                 
          "psrc" :
            c class ColumnEClass := 
               BuildColumn newId "key";
                 
          "ptrg" :
            c class ColumnEClass := 
              BuildColumn newId (getAttributeName a)
            with [
              ref ColumnReferenceEReference :=
                cl <- getAttributeType a m;
                tb <- resolve Class2Relational m "tab" TableEClass [[ cl ]];
                return BuildColumnReference c tb
            ]
        ]
].

Close Scope coqtl.

Unset Printing Notations.
Print Class2RelationalMVConcrete.

Definition Class2RelationalMV := parseTransformation Class2RelationalMVConcrete.
