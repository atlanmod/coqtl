Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import utils.Utils_Top.
Require Import CoqTL.

Require Import ClassMetamodel.
Require Import RelationalMetamodel.

Definition Class2Relational :=
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
                   cols <- resolveAll Class2Relational m "col" ColumnClass
                      (singletons (map ClassMetamodel_toEObject (A:=Attribute) attrs));
                   return BuildTableColumns t cols
               ]
          ];

      rule Attribute2Column
        from
          element a class AttributeEClass from ClassMetamodel 
            when (negb (getAttributeDerived a))
        to
         [
          output "col"
            element c class ColumnClass from RelationalMetamodel := 
               BuildColumn (getAttributeId a) (getAttributeName a)
            links
              [
                reference ColumnReferenceReference from RelationalMetamodel :=
                  cl <- getAttributeType a m;
                  tb <- resolve Class2Relational m "tab" TableClass ([ClassMetamodel_toEObject cl]);
                  return BuildColumnReference c tb
              ] 
         ]

  ].

Unset Printing Notations.

(* Print Class2Relational. *)
(* Check Class2Relational. *)
