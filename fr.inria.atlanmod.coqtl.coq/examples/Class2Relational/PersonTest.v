Require Import String.
Require Import List.

Require Import core.CoqTL.
Require Import core.utils.tPrint.

Require Import example.ClassMetamodel.
Require Import example.RelationalMetamodel.
Require Import example.Class2Relational.
Require Import example.PersonModel.



(* Require Import Class2RelationalVerif. *)

Compute execute Class2Relational PersonModel.


(* Expected Output :
      = {|
       Model.modelElements := RelationalMetamodel_BuildEObject TableClass
                                (BuildTable 0 "Person")
                              :: RelationalMetamodel_BuildEObject ColumnClass
                                   (BuildColumn 1 "father") :: nil;
       Model.modelLinks := RelationalMetamodel_BuildELink
                             TableColumnsReference
                             (BuildTableColumns (BuildTable 0 "Person")
                                (BuildColumn 1 "father" :: nil))
                           :: RelationalMetamodel_BuildELink
                                ColumnReferenceReference
                                (BuildColumnReference
                                   (BuildColumn 1 "father")
                                   (BuildTable 0 "Person")) :: nil |}
     : TargetModel RelationalMetamodel_EObject RelationalMetamodel_ELink
 *)