Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.CoqTL.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Theorem All_classes_match :
  forall (cm : ClassModel) (c: Class) ,
    exists (r: RuleA ClassMetamodel_EClass RelationalMetamodel_EClass RelationalMetamodel_EReference),
      matchPattern Class2Relational cm [ClassMetamodel_toEObject c] = Some r.    
Proof.
  intros.
  exists (hd (BuildRuleA nil (BuildGuardExpressionA 0) nil) (TransformationA_getRules Class2Relational)).
  unfold matchPattern.
  reflexivity.
Qed.

Theorem All_classes_instantiate :
  forall (cm : ClassModel) (c: Class),
    exists (t: Table),
      instantiatePattern Class2Relational cm [ClassMetamodel_toEObject c] = Some [RelationalMetamodel_toEObject t].
Proof.
  intros.
  exists (BuildTable (getClassId c) (getClassName c)).
  unfold instantiatePattern.
  unfold instantiateRuleOnPattern.
  reflexivity.
Qed.

Theorem Concrete_attributes_instantiate :
  forall (cm : ClassModel) (a: Attribute), getAttributeDerived a=false -> 
    exists (c: Column), 
      instantiatePattern Class2Relational cm [ClassMetamodel_toEObject a] = Some [RelationalMetamodel_toEObject c].
Proof.
  intros.
  exists (BuildColumn (getAttributeId a) (getAttributeName a)).
  unfold instantiatePattern.
  unfold instantiateRuleOnPattern.
  unfold matchPattern.
  simpl.
  rewrite H.
  simpl.
  rewrite H.
  simpl.
  reflexivity.
Qed.
