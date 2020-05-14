Require Import core.utils.TopUtils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.
Require Import core.Engine.
Require Import core.Syntax.

Require Import core.Semantics.
Require Import core.Certification.

Require Import core.Semantics_v2.

Section Certification.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink)
          (Rule := Rule smm tmm)
          (Transformation := Transformation smm tmm)
          (MatchedTransformation := MatchedTransformation smm tmm).

  (** * Certification **)

  (** ** execute **)

  Theorem exe_preserv:
    forall (tr: Transformation) (sm : SourceModel),
      Semantics.execute tr sm = Semantics_v2.execute tr sm.
  Proof.
    intros.
    unfold Semantics.execute, Semantics_v2.execute.
    simpl.
    f_equal.
    * induction (allTuples tr sm).
      ** simpl. reflexivity.
      ** simpl. rewrite IHl. unfold instantiatePattern at 1. destruct (matchPattern tr sm a) eqn:Hmatch.
         ***  reflexivity.
         ***  simpl. f_equal. f_equal. unfold instantiatePattern. rewrite Hmatch. simpl. reflexivity.
    * induction (allTuples tr sm).
      ** simpl. reflexivity.
      ** simpl. rewrite IHl. unfold applyPattern at 1. destruct (matchPattern tr sm a) eqn:Hmatch.
         ***  reflexivity.
         ***  simpl. f_equal. f_equal. unfold applyPattern. rewrite Hmatch. simpl. reflexivity.
  Qed.

  Theorem tr_execute_in_elements :
    forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
      In te (allModelElements (execute tr sm)) <->
      (exists (sp : list SourceModelElement) (tp : list TargetModelElement),
          incl sp (allModelElements sm) /\
          instantiatePattern tr sm sp = Some tp /\
          In te tp).
  Proof.
    intros.
    rewrite <- exe_preserv.
    apply Certification.tr_execute_in_elements.
  Qed.

  Theorem tr_execute_in_links :
    forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
      In tl (allModelLinks (execute tr sm)) <->
      (exists (sp : list SourceModelElement) (tpl : list TargetModelLink),
          incl sp (allModelElements sm) /\
          applyPattern tr sm sp = Some tpl /\
          In tl tpl).
  Proof.
    intros.
    rewrite <- exe_preserv.
    apply Certification.tr_execute_in_links.
  Qed.

  (** * Typeclass instantiation **)

  Instance CoqTLEngine :
    TransformationEngine :=
    {
      SourceModelElement := SourceModelElement;
      SourceModelClass := SourceModelClass;
      SourceModelLink := SourceModelLink;
      SourceModelReference := SourceModelReference;
      TargetModelElement := TargetModelElement;
      TargetModelClass := TargetModelClass;
      TargetModelLink := TargetModelLink;
      TargetModelReference := TargetModelReference;

      Transformation := Transformation;
      Rule := Rule;
      OutputPatternElement := OutputPatternElement;
      OutputPatternElementReference := OutputPatternElementReference;

      getRules := Transformation_getRules;
      getInTypes := Rule_getInTypes;
      getIteratorType := Rule_getIteratorType;
      getOutputPattern := Rule_getOutputPattern;
      getOutType := OutputPatternElement_getOutType';
      getOutputElementReferences := OutputPatternElement_getOutputElementReferences';

      execute := Semantics_v2.execute;
      matchPattern := matchPattern;
      instantiatePattern := instantiatePattern;
      applyPattern := applyPattern;

      matchRuleOnPattern := matchRuleOnPattern';
      instantiateRuleOnPattern := instantiateRuleOnPattern';
      applyRuleOnPattern := applyRuleOnPattern';

      instantiateIterationOnPattern := instantiateIterationOnPattern;
      applyIterationOnPattern := applyIterationOnPattern;

      instantiateElementOnPattern := instantiateElementOnPattern;
      applyElementOnPattern := applyElementOnPattern;

      applyReferenceOnPattern := applyReferenceOnPattern;

      evalIterator := evalIterator;

      tr_execute_in_elements := tr_execute_in_elements;
      tr_execute_in_links := tr_execute_in_links;

      tr_instantiatePattern_in := tr_instantiatePattern_in;
      tr_instantiatePattern_non_None := tr_instantiatePattern_non_None;
      tr_instantiatePattern_None := tr_instantiatePattern_None;

      tr_instantiateRuleOnPattern_in := tr_instantiateRuleOnPattern_in;
      tr_instantiateRuleOnPattern_non_None := tr_instantiateRuleOnPattern_non_None;

      tr_instantiateIterationOnPattern_in := tr_instantiateIterationOnPattern_in;
      tr_instantiateIterationOnPattern_non_None := tr_instantiateIterationOnPattern_non_None;

      tr_instantiateElementOnPattern_None := tr_instantiateElementOnPattern_None;
      tr_instantiateElementOnPattern_None_iterator := tr_instantiateElementOnPattern_None_iterator;

      tr_applyPattern_in := tr_applyPattern_in;
      tr_applyPattern_non_None := tr_applyPattern_non_None;
      tr_applyPattern_None := tr_applyPattern_None;

      tr_applyRuleOnPattern_in := tr_applyRuleOnPattern_in;
      tr_applyRuleOnPattern_non_None := tr_applyRuleOnPattern_non_None;

      tr_applyIterationOnPattern_in := tr_applyIterationOnPattern_in;
      tr_applyIterationOnPattern_non_None := tr_applyIterationOnPattern_non_None;

      tr_applyElementOnPattern_in := tr_applyElementOnPattern_in;
      tr_applyElementOnPattern_non_None := tr_applyElementOnPattern_non_None;

      tr_applyReferenceOnPattern_None := tr_applyReferenceOnPattern_None;
      tr_applyReferenceOnPattern_None_iterator := tr_applyReferenceOnPattern_None_iterator;

      tr_matchPattern_in := tr_matchPattern_in;
      tr_matchPattern_None := tr_matchPattern_None;

      tr_matchRuleOnPattern_None := tr_matchRuleOnPattern_None;

      tr_maxArity_in := tr_maxArity_in;
    }.

End Certification.
