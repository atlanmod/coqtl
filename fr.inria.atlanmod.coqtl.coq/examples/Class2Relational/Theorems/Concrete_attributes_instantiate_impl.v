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

Theorem Concrete_attributes_instantiate_impl :
  forall (cm : ClassModel) (a: Attribute),
    getAttributeDerived a = false ->
    exists (c: Column),
      instantiatePattern Class2Relational cm [ClassMetamodel_toEObject a] = Some [RelationalMetamodel_toEObject c].
Proof.
  intros.
  eexists _.
  unfold instantiatePattern. unfold matchPattern. simpl.
  rewrite H. simpl.
  unfold instantiateRuleOnPattern. simpl.
  rewrite H. simpl.
  unfold instantiateIterationOnPattern. simpl.
  rewrite H. simpl.
  unfold instantiateElementOnPattern. simpl.
  rewrite H. simpl.
  reflexivity.
Qed.