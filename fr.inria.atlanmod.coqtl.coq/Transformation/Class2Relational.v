Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import Utils.Utils_Top.
Require Import Utils.CoqTL.

Require Import Transformation.ClassMetamodel.
Require Import Transformation.RelationalMetamodel.



(* TODO: avoid all ClassMetamodel_xxx calls *)

Definition Class2Relational :=
  transformation Class2Relational from ClassMetamodel to RelationalMetamodel
    of m instanceof ClassModel
    := [
      rule Attribute2Column
        from
          element a instanceof AttributeEClass from ClassMetamodel 
          when (negb (getAttributeDerived a) )
        to [
          output "t" (* TODO why is this useful *)
            element c instanceof ColumnClass from RelationalMetamodel := 
              (BuildColumn
                 (getAttributeId a)
                 (getAttributeName a))
            references
              [ reference ColumnReferenceReference from RelationalMetamodel :=
                 ( y' <- (getAttributeType a m);
                   y  <- (resolve (Class2Relational m) "t"%string TableClass (ClassMetamodel_toEObject y'::nil));
                   Some (BuildColumnReference c y)
                 ) 
              ] 
            ];

       rule Class2Table
         from
           element c instanceof ClassEClass from ClassMetamodel
           when true
         to [
           output "t"
             element t instanceof TableClass from RelationalMetamodel :=
               (BuildTable
                  (getClassId c)
                  (getClassName c))
             references
               [ reference TableColumnsReference from RelationalMetamodel :=
                  ( y' <- (getClassAttributes c m);
                    let y''  := map (A:=Attribute) ClassMetamodel_toEObject y' in
                    let y''' := listToListList y'' in  
                    let y    := optionList2List
                               (map (resolve (Class2Relational m)
                                             "t"%string ColumnClass) y''')  in
                    Some (BuildTableColumns t y)) ] ]
  ].

Unset Printing Notations.

(* Print Class2Relational. *)
(* Check Class2Relational. *)

