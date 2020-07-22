(**
 CoqTL user theorem: Column_name_uniqueness
 Def: if all attributes of the same class have unique names,
      then the generated columns of the same table
      have unique names.
 **)

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import String.
Require Import core.utils.Utils.

(*Require Import core.Semantics.
Require Import core.Certification.*)
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Theorem Column_name_uniqueness:
forall (cm : ClassModel) (rm : RelationalModel), 
(* transformation *) 
    rm = execute Class2Relational cm ->
(* precondition *)   
(forall (a1: Attribute) (a2: Attribute) (c: Class) (ats: list Attribute), 
    In (ClassMetamodel_toObject AttributeClass a1) (allModelElements cm) -> 
    In (ClassMetamodel_toObject AttributeClass a2) (allModelElements cm) -> 
    In (ClassMetamodel_toObject ClassClass c) (allModelElements cm) -> 
    getClassAttributes c cm = Some ats ->
    In a1 ats ->
    In a2 ats ->
    a1 <> a2 -> 
    getAttributeName a1 <> getAttributeName a2) ->
(* postcondition *)  
(forall (c1: Column) (c2: Column) (t: Table) (cls: list Column), 
    In (RelationalMetamodel_toObject ColumnClass c1) (allModelElements rm) -> 
    In (RelationalMetamodel_toObject ColumnClass c2) (allModelElements rm) -> 
    In (RelationalMetamodel_toObject TableClass t) (allModelElements rm) -> 
    getTableColumns t rm = Some cls ->    
    In c1 cls ->
    In c2 cls ->
    c1 <> c2 -> 
    getColumnName c1 <> getColumnName c2).
Proof.
Admitted.
