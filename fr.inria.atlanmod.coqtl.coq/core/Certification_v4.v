Require Import core.utils.TopUtils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.
Require Import core.Engine.
Require Import core.Syntax.

Require Import core.Semantics.
Require Export core.Certification.

Require Import core.Semantics_v4.

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

  (** ** instantiatePattern *)

  Theorem instantiatePattern_preserv:
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      Semantics_v4.instantiatePattern tr sm sp = Semantics.instantiatePattern tr sm sp.
  Proof.
    intros.
    unfold Semantics_v4.instantiatePattern, Semantics.instantiatePattern.
    destruct (matchPattern tr sm sp).
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem tr_instantiatePattern_in :
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
      (exists tp: list TargetModelElement, instantiatePattern tr sm sp = Some tp /\
                                      In te tp) <->
      (exists (r : Rule) (tp1 : list TargetModelElement),
          In r (matchPattern tr sm sp) /\
          instantiateRuleOnPattern r sm sp = Some tp1 /\
          In te tp1).
  Proof.
    setoid_rewrite instantiatePattern_preserv.
    apply Certification.tr_instantiatePattern_in.
  Qed.

  Theorem tr_instantiatePattern_non_None :
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      instantiatePattern tr sm sp <> None <->
      (exists (r: Rule),
          In r (matchPattern tr sm sp) /\
          instantiateRuleOnPattern' r tr sm sp <> None).
  Proof.
    intros.
    rewrite instantiatePattern_preserv.
    apply Certification.tr_instantiatePattern_non_None.
  Qed.

  Theorem tr_instantiatePattern_None :
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      length sp > maxArity tr ->
      instantiatePattern tr sm sp = None.
  Proof.
    intros.
    rewrite instantiatePattern_preserv.
    apply Certification.tr_instantiatePattern_None.
    assumption.
  Qed.

  (** ** applyPattern *)

  Theorem applyPattern_preserv:
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      Semantics_v4.applyPattern tr sm sp = Semantics.applyPattern tr sm sp.
  Proof.
    intros.
    unfold Semantics_v4.applyPattern, Semantics.applyPattern.
    destruct (matchPattern tr sm sp).
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem tr_applyPattern_in :
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
      (exists tpl: list TargetModelLink, applyPattern tr sm sp = Some tpl /\
                                    In tl tpl) <->
      (exists (r : Rule) (tpl1 : list TargetModelLink),
          In r (matchPattern tr sm sp) /\
          applyRuleOnPattern r tr sm sp = Some tpl1 /\
          In tl tpl1).
  Proof.
    setoid_rewrite applyPattern_preserv.
    apply Certification.tr_applyPattern_in.
  Qed.

  Theorem tr_applyPattern_non_None :
    forall  (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) ,
      applyPattern tr sm sp <> None <->
      (exists  (r : Rule),
          In r (matchPattern tr sm sp) /\
          applyRuleOnPattern r tr sm sp <> None).
  Proof.
    intros.
    rewrite applyPattern_preserv.
    apply Certification.tr_applyPattern_non_None.
  Qed.

  Theorem tr_applyPattern_None :
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      length sp > maxArity tr ->
      applyPattern tr sm sp = None.
  Proof.
    intros.
    rewrite applyPattern_preserv.
    apply Certification.tr_applyPattern_None.
    assumption.
  Qed.

  (** ** execute *)

  Theorem exe_preserv:
    forall (tr: Transformation) (sm : SourceModel),
      Semantics.execute tr sm = Semantics_v4.execute tr sm.
  Proof.
    intros.
    unfold Semantics.execute, Semantics_v4.execute.
    f_equal.
    - induction (allTuples tr sm).
      + simpl. reflexivity.
      + simpl. rewrite IHl. rewrite <- instantiatePattern_preserv. reflexivity.
    - induction (allTuples tr sm).
      + simpl. reflexivity.
      + simpl. rewrite IHl. rewrite <- applyPattern_preserv. reflexivity.
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
    setoid_rewrite instantiatePattern_preserv.
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
    setoid_rewrite applyPattern_preserv.
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

      execute := Semantics_v4.execute;
      matchPattern := matchPattern;
      instantiatePattern := Semantics_v4.instantiatePattern;
      applyPattern := Semantics_v4.applyPattern;

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

      smm := smm;
      tmm := tmm;

      getGuard := Rule_getGuard;
      getRefType := OutputPatternElementReference_getRefType';
      getOutputReference := OutputPatternElementReference_getOutputReference';
      getOutPatternElement := OutputPatternElement_getOutPatternElement';

      matchTransformation := matchTransformation ;
      unmatchTransformation := unmatchTransformation; 

      resolveAll := resolveAllIter;
      resolve := resolveIter;      
      evalOutputPatternElement := evalOutputPatternElement';

      tr_instantiateElementOnPattern_Leaf := tr_instantiateElementOnPattern_Leaf;
      tr_applyReferenceOnPattern_Leaf := tr_applyReferenceOnPattern_Leaf;
      tr_matchRuleOnPattern_Leaf := tr_matchRuleOnPattern_Leaf;

      tr_resolveAll_in := tr_resolveAllIter_in;
      tr_resolve_Leaf := tr_resolveIter_Leaf';

    }.

End Certification.
