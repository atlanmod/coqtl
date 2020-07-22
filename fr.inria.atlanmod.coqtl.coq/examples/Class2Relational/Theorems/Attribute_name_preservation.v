(**
CoqTL user theorem: Attribute_name_preservation
Def: all non-derived attributes in the source model will create 
    a column in the target model with the same name
**)

Require Import String.
Require Import Omega.
Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Semantics.
Require Import core.Certification.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.


Theorem Attribute_name_preservation:
    forall (rm : RelationalModel) (cm: ClassModel),
        (* transformation *)
        rm = execute Class2Relational cm ->
        (* postcondition *)  
        forall (a: Attribute),
        In (ClassMetamodel_toObject AttributeClass a) (allModelElements cm) ->
        getAttributeDerived a = false ->
        exists (c: Column),
            In (RelationalMetamodel_toObject ColumnClass c) (allModelElements rm) /\
            getColumnName c = getAttributeName a.
Proof.
    intros.
    exists (BuildColumn (getAttributeId a) (getAttributeName a)).
    split.
    - rewrite H.
      rewrite tr_execute_in_elements.
      exists ([ClassMetamodel_toObject AttributeClass a]).
      split.
      + apply allTuples_incl_length.
        * unfold incl.
          intros.
          apply in_inv in H2.
          destruct H2.
          -- rewrite <- H2. assumption.
          -- contradiction.
        * unfold maxArity. simpl. omega.
      + destruct a.
        simpl in H1.
        rewrite H1.
        simpl. 
        left.
        reflexivity.
    - reflexivity.
Qed.
