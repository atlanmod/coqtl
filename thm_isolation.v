Require Import Class2Relational.
Require Import ClassMetamodel.
Require Import RelationalMetamodel.
Require Import CoqTL.
Require Import Utils.
Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  






Theorem Class2Relational_keeps_isolation :
  forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   (forall (c : Class), forall (attr:Attribute), In (ClassMetamodel_toEObject attr) (allModelElements cm) -> getAttributeType attr cm <> Some c -> (* precondition *)
    exists (t: Table), forall (col:Column), In (RelationalMetamodel_toEObject col) (allModelElements rm) -> getColumnReference col rm <> Some t). (* postcondiiton *) 
Proof.
  intros cm rm tr c attr attr_cm c_iso.


Abort.
