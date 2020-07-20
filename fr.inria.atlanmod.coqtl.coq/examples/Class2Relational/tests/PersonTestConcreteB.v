Require Import String.
Require Import List.

Require Import core.Semantics.
Require Import core.ConcreteSyntaxB.
Require Import core.utils.PrintUtils.
Require Import core.utils.ListUtils.
Require Import core.utils.TupleUtils.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.
Require Import examples.Class2Relational.Class2RelationalConcreteB.
Require Import examples.Class2Relational.tests.PersonModel.

(* Require Import Class2RelationalVerif. *)

(* Expected Output :
      = {|
       Model.modelElements := RelationalMetamodel_BuildEObject TableClass
                                (BuildTable 0 "Person")
                              :: RelationalMetamodel_BuildEObject ColumnClass
                                   (BuildColumn 1 "parent") :: nil;
       Model.modelLinks := RelationalMetamodel_BuildELink
                             TableColumnsReference
                             (BuildTableColumns (BuildTable 0 "Person")
                                (BuildColumn 1 "parent" :: nil))
                           :: RelationalMetamodel_BuildELink
                                ColumnReferenceReference
                                (BuildColumnReference
                                   (BuildColumn 1 "parent")
                                   (BuildTable 0 "Person")) :: nil |}
     : TargetModel RelationalMetamodel_EObject RelationalMetamodel_ELink
*)

(* Expected output (short):
    Table id=0 name='Person'
      Column id=1 name='parent' reference='Person'
*)

Compute (execute (parse Class2Relational) PersonModel).
