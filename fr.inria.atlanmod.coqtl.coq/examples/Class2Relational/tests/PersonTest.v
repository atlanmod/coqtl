Require Import String.
Require Import List.

Require Import core.CoqTL.
Require Import core.utils.PrintUtils.
Require Import core.utils.ListUtils.
Require Import core.utils.TupleUtils.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.
Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.tests.PersonModel.

(* Require Import Class2RelationalVerif. *)

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


Definition RuleInTypes := ClassEClass :: AttributeEClass :: nil.

Definition m :=  (Model.allModelElements PersonModel).

Definition allInstances (t: ClassMetamodel_EClass) :=
 map (Metamodel.toModelElement t)
  (optionList2List (map (Metamodel.toModelClass t) m)).


Definition TupleOfRule :=
  map (allInstances) RuleInTypes.


Compute (prod_cons hd_error(TupleOfRule) tl( TupleOfRule)).



Compute execute Class2Relational PersonModel.
