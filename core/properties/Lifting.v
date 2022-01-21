Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import Expressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.

Theorem Forall_patterns :
forall (tc: TransformationConfiguration) (p: TargetModelElement -> Prop) 
    (sm: SourceModel) (tr: Transformation),
    Forall p (allModelElements (execute tr sm)) <-> 
        Forall (fun sp => Forall p (instantiatePattern tr sm sp)) (allTuples tr sm).
Proof.
  intros.
  apply Forall_flat_map.
Qed.

Theorem Forall_rules :
forall (tc: TransformationConfiguration) (p: TargetModelElement -> Prop) 
  (sm: SourceModel) (tr: Transformation),
  Forall p (allModelElements (execute tr sm)) <-> 
    Forall 
      (fun r => 
        Forall 
          (fun sp => Forall 
            (fun e => (matchRuleOnPattern r sm sp = true) -> p e)
            (instantiateRuleOnPattern r sm sp)) 
          (allTuples tr sm)) 
      (Transformation_getRules tr).
Proof.
  simpl.
  intros.
  rewrite Forall_flat_map.
  unfold instantiatePattern. 
  unfold matchPattern.
  rewrite !Forall_forall.
  split.
  - intros.
    rewrite !Forall_forall.
    intros.
    rewrite !Forall_forall.
    intros.
    specialize (H x0 H1).
    rewrite !Forall_forall in H.
    specialize (H x1).
    apply H.
    apply in_flat_map.
    exists x.
    split.
    apply filter_In.
    split.
    assumption. assumption. assumption.
  - intros.
    rewrite !Forall_forall.
    intros.
    apply in_flat_map in H1. repeat destruct H1.
    apply filter_In in H1. destruct H1.
    specialize (H x1 H1).
    rewrite !Forall_forall in H.
    specialize (H x H0).
    rewrite !Forall_forall in H.
    crush.
Qed.

Theorem Forall_rules_suff :
forall (tc: TransformationConfiguration) (p: TargetModelElement -> Prop) 
  (sm: SourceModel) (tr: Transformation),
    Forall 
      (fun r => 
        Forall 
          (fun sp => Forall p (instantiateRuleOnPattern r sm sp)) 
          (allTuples tr sm)) 
      (Transformation_getRules tr)
        -> Forall p (allModelElements (execute tr sm)).
Proof.
    simpl.
    intros.
    rewrite Forall_flat_map.
    unfold instantiatePattern. 
    unfold matchPattern.
    rewrite !Forall_forall.
     intros.
      rewrite !Forall_forall.
      intros.
      apply in_flat_map in H1. repeat destruct H1.
      apply filter_In in H1. destruct H1.
      rewrite !Forall_forall in H.
      specialize (H x1 H1).
      rewrite !Forall_forall in H.
      specialize (H x H0).
      rewrite !Forall_forall in H.
      crush.
Qed.

Theorem Forall_rules_suff' :
forall (tc: TransformationConfiguration) (p: TargetModelElement -> Prop) 
  (sm: SourceModel) (tr: Transformation),
    Forall 
      (fun r => forall sp t, In sp (allTuples tr sm) -> 
         In t (instantiateRuleOnPattern r sm sp) -> p t)
      (Transformation_getRules tr) 
    -> Forall p (allModelElements (execute tr sm)).
Proof.
    simpl.
    intros.
    rewrite Forall_flat_map.
    unfold instantiatePattern. 
    unfold matchPattern.
    rewrite !Forall_forall.
     intros.
      rewrite !Forall_forall.
      intros.
      apply in_flat_map in H1. repeat destruct H1.
      apply filter_In in H1. destruct H1.
      rewrite !Forall_forall in H.
      specialize (H x1 H1).
      specialize (H x x0 H0 H2).
      crush.
Qed.

Theorem Forall_rules_suff'' :
forall (tc: TransformationConfiguration) (p: TargetModelElement -> Prop) 
  (sm: SourceModel) (tr: Transformation),
    Forall 
      (fun r => forall sp t, In t (instantiateRuleOnPattern r sm sp) -> p t)
      (Transformation_getRules tr) 
        -> Forall p (allModelElements (execute tr sm)).
Proof.
    simpl.
    intros.
    rewrite Forall_flat_map.
    unfold instantiatePattern. 
    unfold matchPattern.
    rewrite !Forall_forall.
    intros.
    rewrite !Forall_forall.
    intros.
    apply in_flat_map in H1. repeat destruct H1.
    apply filter_In in H1. destruct H1.
    rewrite !Forall_forall in H.
    specialize (H x1 H1).
    specialize (H x x0 H2).
    crush.
Qed.

Theorem Forall_expressions :
forall (tc: TransformationConfiguration) (p: TargetModelElement -> Prop) 
  (sm: SourceModel) (tr: Transformation),
  Forall p (allModelElements (execute tr sm)) <-> 
    Forall 
      (fun r => 
        Forall 
          (fun sp => Forall 
            (fun i => Forall 
              (fun o => 
                (evalGuardExpr r sm sp = Some true) ->
                  match evalOutputPatternElementExpr sm sp i o with
                  | Some e => p e | None => True end)
              (Rule_getOutputPatternElements r))
            (seq 0 (evalIteratorExpr r sm sp)))
          (allTuples tr sm))
      (Transformation_getRules tr).
Proof.
  simpl.
  intros.
  rewrite Forall_flat_map.
  unfold instantiatePattern. 
  unfold matchPattern.
  rewrite !Forall_forall.
  split.
  - intros.
    rewrite !Forall_forall.
    intros.
    rewrite !Forall_forall.
    intros.
    specialize (H x0 H1).
    rewrite !Forall_forall in H.
    rewrite !Forall_forall.
    intros.
    destruct (evalOutputPatternElementExpr sm x0 x1 x2) eqn:dst.
    specialize (H t).
    apply H.
    apply in_flat_map.
    exists x.
    split.
    apply filter_In.
    split.
    assumption. 
    unfold matchRuleOnPattern. rewrite H4. reflexivity.
    unfold instantiateRuleOnPattern.
    apply in_flat_map. exists x1. split.
    assumption.
    unfold instantiateIterationOnPattern.
    apply in_flat_map. exists x2. split.
    assumption.
    unfold instantiateElementOnPattern.
    crush. crush.
  - intros.
    rewrite !Forall_forall.
    intros.
    apply in_flat_map in H1. repeat destruct H1.
    apply filter_In in H1. destruct H1.
    specialize (H x1 H1).
    rewrite !Forall_forall in H.
    specialize (H x H0).
    rewrite !Forall_forall in H.
    unfold instantiateRuleOnPattern in H2.
    apply in_flat_map in H2. repeat destruct H2.
    specialize (H x2 H2).
    rewrite !Forall_forall in H.
    unfold instantiateIterationOnPattern in H4.
    apply in_flat_map in H4. repeat destruct H4.
    specialize (H x3 H4).
    unfold matchRuleOnPattern in H3.
    destruct (evalGuardExpr x1 sm x). destruct b.
    + unfold instantiateElementOnPattern in H5. 
      destruct (evalOutputPatternElementExpr sm x x2 x3).
      * crush.
      * crush.
    + crush.
    + crush.
Qed.

Theorem Forall_expressions_suff :
forall (tc: TransformationConfiguration) (p: TargetModelElement -> Prop) 
  (sm: SourceModel) (tr: Transformation),
    Forall 
      (fun r => 
        forall sp i o, In o (Rule_getOutputPatternElements r) -> 
          match evalOutputPatternElementExpr sm sp i o with
          | Some e => p e | None => True end)
      (Transformation_getRules tr) 
      -> Forall p (allModelElements (execute tr sm)).
Proof.
  simpl.
  intros.
  rewrite Forall_flat_map.
  unfold instantiatePattern. 
  unfold matchPattern.
  rewrite !Forall_forall.
  intros.
    rewrite !Forall_forall.
    intros.
    apply in_flat_map in H1. repeat destruct H1.
    apply filter_In in H1. destruct H1.
    rewrite !Forall_forall in H.
    specialize (H x1 H1 x).
    unfold instantiateRuleOnPattern in H2.
    apply in_flat_map in H2. repeat destruct H2.
    unfold instantiateIterationOnPattern in H4.
    apply in_flat_map in H4. repeat destruct H4.
    specialize (H x2 x3 H4).
    unfold matchRuleOnPattern in H3.
    destruct (evalGuardExpr x1 sm x). destruct b.
    + unfold instantiateElementOnPattern in H5. 
      destruct (evalOutputPatternElementExpr sm x x2 x3).
      * crush.
      * crush.
    + crush.
    + crush.
Qed.

Theorem Forall_rules_patterns :
forall (tc: TransformationConfiguration) (correct: list SourceModelElement -> TargetModelElement -> Prop) 
  (sm: SourceModel) (tr: Transformation),
    Forall 
      (fun r => forall sp t, 
       In sp (allTuples tr sm) -> matchRuleOnPattern r sm sp = true 
         -> In t (instantiateRuleOnPattern r sm sp) -> correct sp t)
      (Transformation_getRules tr) 
        <-> 
    Forall
      (fun sp => Forall (correct sp) (instantiatePattern tr sm sp)) 
    (allTuples tr sm).
Proof.
  intros tc correct sm tr.
  rewrite! Forall_forall.
  split.
  - intros.
    rewrite! Forall_forall.
    unfold instantiatePattern, matchPattern.
    intros.
    apply in_flat_map in H1. repeat destruct H1.
    apply filter_In in H1. destruct H1.
    specialize (H x1 H1 x x0 H0 H3).
    crush.
  - intros.
    specialize (H sp).
    rewrite! Forall_forall in H.
    specialize (H H1 t).
    assert (In t (instantiatePattern tr sm sp)). {
      unfold instantiatePattern, matchPattern.
      apply in_flat_map.
      exists x.
      split.
      - apply filter_In.
        split. assumption. assumption.
      - assumption.  
    }
    specialize (H H4).
    crush.
Qed.

Theorem Forall_rules_patterns' :
forall (tc: TransformationConfiguration) (correct: list SourceModelElement -> TargetModelElement -> Prop) 
  (sm: SourceModel) (tr: Transformation),
    Forall 
      (fun r => forall sp t, matchRuleOnPattern r sm sp = true 
         -> In t (instantiateRuleOnPattern r sm sp) -> correct sp t)
      (Transformation_getRules tr) 
        <-> 
    forall sp, Forall (correct sp) (instantiatePattern tr sm sp).
Proof.
  intros tc correct sm tr.
  rewrite! Forall_forall.
  split.
  - intros.
    rewrite! Forall_forall.
    unfold instantiatePattern, matchPattern.
    intros.
    apply in_flat_map in H0. repeat destruct H0.
    apply filter_In in H0. destruct H0.
    specialize (H x0 H0 sp x H2 H1).
    crush.
  - intros.
    specialize (H sp).
    rewrite! Forall_forall in H.
    specialize (H t).
    assert (In t (instantiatePattern tr sm sp)). {
      unfold instantiatePattern, matchPattern.
      apply in_flat_map.
      exists x.
      split.
      - apply filter_In.
        split. assumption. assumption.
      - assumption.  
    }
    specialize (H H3).
    crush.
Qed.

Theorem Forall_rules_patterns_suff :
forall (tc: TransformationConfiguration) (correct: list SourceModelElement -> TargetModelElement -> Prop) 
  (sm: SourceModel) (tr: Transformation),
    Forall 
      (fun r => forall sp t, In t (instantiateRuleOnPattern r sm sp) -> correct sp t)
      (Transformation_getRules tr) 
        -> 
    Forall
      (fun sp => Forall (correct sp) (instantiatePattern tr sm sp)) 
    (allTuples tr sm).
Proof.
  intros tc correct sm tr.
  rewrite! Forall_forall.
  intros.
  rewrite! Forall_forall.
  unfold instantiatePattern, matchPattern.
  intros.
  apply in_flat_map in H1. repeat destruct H1.
  apply filter_In in H1. destruct H1.
  specialize (H x1 H1 x x0 H2).
  crush.
Qed.

(* TODO: same for links and Exists *)
