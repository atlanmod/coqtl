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
    rm = execute Class2RelationalMV cm ->
    forall (a: Attribute),
      In (ClassMetamodel_toEObject a) (allModelElements cm) ->
      exists (c: Column),
        In (RelationalMetamodel_toEObject c) (allModelElements rm) /\
        getColumnName c = getAttributeName a.
  intros.
  destruct a eqn:a_dest.
  destruct b eqn:b_dest; 
    (eapply outp_incl_elements with (sp := [ClassMetamodel_toEObject a]) in H; 
     [ eexists (BuildColumn _ s0); crush | 
       unfold incl; crush | 
       crush ]).
Qed.
