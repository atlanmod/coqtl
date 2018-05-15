Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.Utils_Top.
Require Import core.CoqTL.

Require Import ClassMetamodel.
Require Import RelationalMetamodel.



(* TODO: avoid all ClassMetamodel_xxx calls *)

Definition Class2Relational :=
  transformation Class2Relational from ClassMetamodel to RelationalMetamodel
    of m instanceof ClassModel
    := [
       rule Class2Table
         from
           element c class ClassEClass from ClassMetamodel
             when true
         to [
           output "tab"
             element t class TableClass from RelationalMetamodel :=
               BuildTable (getClassId c) (getClassName c)
             links
               [ reference TableColumnsReference from RelationalMetamodel :=
                  ( y' <- (getClassAttributes c m);
                    let y''  := map (A:=Attribute) ClassMetamodel_toEObject y' in
                    let y''' := listToListList y'' in  
                    let y    := optionList2List
                               (map (resolve (Class2Relational m)
                                             "col"%string ColumnClass) y''')  in
                    Some (BuildTableColumns t y)) ] ];

        rule Attribute2Column
        from
          element a class AttributeEClass from ClassMetamodel 
            when (negb (getAttributeDerived a) )
        to [
          output "col" (* TODO why is this useful *)
            element c class ColumnClass from RelationalMetamodel := 
               BuildColumn (getAttributeId a) (getAttributeName a)
            links
              [ reference ColumnReferenceReference from RelationalMetamodel :=
                 ( cl <- getAttributeType a m;
                   tb  <- (resolve (Class2Relational m) "tab"%string TableClass ((ClassMetamodel_toEObject cl)::nil));
                   return BuildColumnReference c tb
                 ) 
              ] 
            ]

  ].

Unset Printing Notations.

(* Print Class2Relational. *)
(* Check Class2Relational. *)

