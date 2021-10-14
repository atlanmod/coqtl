Require Import String.
Require Import List.

Require Import core.Model.
Require Import core.Semantics.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ConcreteSyntax.
Require Import core.utils.Utils.
Require Import transformations.Class2RelationalTest.ClassMetamodel.
Require Import transformations.Class2RelationalTest.RelationalMetamodel.
Require Import transformations.Class2RelationalTest.Class2Relational.
Require Import transformations.Class2RelationalTest.tests.PersonModel.

(* Require Import Class2RelationalVerif. *)

(* Expected Output :
      = {|
       modelElements := [Build_RelationalMetamodel_Object TableClass
                           (BuildTable 0 "Person");
                        Build_RelationalMetamodel_Object ColumnClass
                          (BuildColumn 1 "parent")];
       modelLinks := [Build_RelationalMetamodel_Link TableColumnsReference
                        (BuildTableColumns (BuildTable 0 "Person")
                           [BuildColumn 1 "parent"]);
                     Build_RelationalMetamodel_Link ColumnReferenceReference
                       (BuildColumnReference (BuildColumn 1 "parent")
                          (BuildTable 0 "Person"))] |}
     : TransformationConfiguration.TargetModel
*)

(* Expected output (short):
    Table id=0 name='Person'
      Column id=1 name='parent' reference='Person'
*)

Compute 
  (Model_beq beq_RelationalMetamodel_Object beq_RelationalMetamodel_Link 
    (execute Class2Relational PersonModel) 
    {|
       Model.modelElements := Build_RelationalMetamodel_Object TableClass
                                (BuildTable 0 "Person")
                              :: Build_RelationalMetamodel_Object ColumnClass
                                   (BuildColumn 1 "parent") :: nil;
       Model.modelLinks := Build_RelationalMetamodel_Link
                             TableColumnsReference
                             (BuildTableColumns (BuildTable 0 "Person")
                                (BuildColumn 1 "parent" :: nil))
                           :: Build_RelationalMetamodel_Link
                                ColumnReferenceReference
                                (BuildColumnReference
                                   (BuildColumn 1 "parent")
                                   (BuildTable 0 "Person")) :: nil |}).
