Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.CoqTL.
Require Import core.Model.
Require Import core.utils.CpdtTactics.

Require Import examples.Class2RelationalMV.Class2Relational.
Require Import examples.Class2RelationalMV.ClassMetamodel.
Require Import examples.Class2RelationalMV.RelationalMetamodel.


Theorem information_preservation :
  forall (rm : Model RelationalMetamodel_EObject RelationalMetamodel_ELink)
    (cm: Model ClassMetamodel_EObject ClassMetamodel_ELink),
    rm = execute Class2Relational cm ->
    forall (a: Attribute),
      In (ClassMetamodel_toEObject a) (allModelElements cm) ->
      exists (c: Column),
        In (RelationalMetamodel_toEObject c) (allModelElements rm) ->
        getColumnName c = getAttributeName a.
Proof.
  intros.
  exists (BuildColumn (getAttributeId a ++ "_MA2C_col") (getAttributeName a)).
  crush.
Qed.