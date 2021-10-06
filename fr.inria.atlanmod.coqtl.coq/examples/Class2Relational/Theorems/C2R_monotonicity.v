Require Import String.

Require Import core.utils.Utils.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.Properties.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Require Import core.utils.CpdtTactics.

Theorem All_classes_instantiate_impl:
  monotonicity _ Class2Relational.
Proof.
  unfold monotonicity.
  unfold Model_incl. unfold SourceModel_incl.
  unfold incl.
  simpl.
  intros.
  destruct H.
  split.
  - intros.
    apply in_flat_map.
    apply in_flat_map in H1. repeat destruct H1.
    exists x.
    split.
    + unfold allTuples in *.
      simpl in *.
      unfold prod_cons in *.
      simpl in *.
      apply in_app_iff.
      apply in_app_iff in H1.
      destruct H1.
      * left.
        apply in_flat_map.
        apply in_flat_map in H1.
        repeat destruct H1.
        exists x0.
        split.
        apply H.
        assumption.
        assumption.
      * right.
        assumption.
    + unfold instantiatePattern in *.
      apply in_flat_map. apply in_flat_map in H2.
      repeat destruct H2.
      exists x0.
      unfold matchPattern in *.
      apply filter_In in H2.
      destruct H2.
      unfold matchRuleOnPattern in *.
      unfold Class2Relational, Class2Relational' in H2.
      simpl in H2. destruct H2.
      split.
      * apply filter_In.
        crush.
      * crush.
      * split.
        -- apply filter_In.
           crush.
        -- crush.
  - intros.
    apply in_flat_map.
    apply in_flat_map in H1. repeat destruct H1.
    exists x.
    split.
    + unfold allTuples in *.
      simpl in *.
      unfold prod_cons in *.
      simpl in *.
      apply in_app_iff.
      apply in_app_iff in H1.
      destruct H1.
      * left.
        apply in_flat_map.
        apply in_flat_map in H1.
        repeat destruct H1.
        exists x0.
        split.
        apply H.
        assumption.
        assumption.
      * right.
        assumption.
    + unfold applyPattern in *.
      apply in_flat_map. apply in_flat_map in H2.
      repeat destruct H2.
      exists x0.
      unfold matchPattern in *.
      apply filter_In in H2.
      destruct H2.
      unfold matchRuleOnPattern in *.
      unfold Class2Relational, Class2Relational' in H2.
      simpl in H2. destruct H2.
      * split.
        -- apply filter_In.
           crush.
        -- rewrite <- H2. rewrite <- H2 in H3.
           unfold applyRuleOnPattern, applyIterationOnPattern, applyElementOnPattern in *.
           simpl in *.
           unfold  ConcreteExpressions.makeElement in *.
           simpl in *.
Admitted.
           