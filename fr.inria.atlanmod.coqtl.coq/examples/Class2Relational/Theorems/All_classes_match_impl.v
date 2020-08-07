Require Import String.

Require Import core.utils.Utils.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Require Import core.utils.CpdtTactics.

Theorem All_classes_match_impl:
  forall (cm : ClassModel) (c : Class),
  exists (r : Rule),
    matchPattern Class2Relational cm [ClassMetamodel_toObject ClassClass c] = [r].
Proof.
  eexists.
  reflexivity.
Qed.