(**

 CoqTL user theorem: All_classes_instantiate

 Def: all classes in the source model will create table in the target model

 Proved with engine specification

 **)

Require Import String.

Require Import core.utils.TopUtils.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Require Import core.utils.CpdtTactics.

Theorem All_classes_instantiate_spec:
  forall (cm : ClassModel) (c: Class),
  exists (t: RelationalMetamodel_EObject) tp,
    instantiatePattern Class2Relational cm [ClassMetamodel_toEObject c] = Some tp /\
    In t tp.
Proof.
  intros.
  eexists.
  apply tr_instantiatePattern_in.
  do 2 eexists.
  repeat split.
  - left. reflexivity.
  - reflexivity.
  - left. reflexivity.
Qed.