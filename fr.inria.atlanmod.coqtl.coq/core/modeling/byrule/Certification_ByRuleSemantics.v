Require Import String.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import Engine.

Require Import Bool.
Require Import core.Syntax.
Require Import Arith.
Require Import Semantics.
Require Import ByRuleSemantics.
Require Import Certification.

Scheme Equality for list.


Section ByRuleSemanticsCertification.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}. 

Lemma allModelElementsOfTypeInModel :
  forall (c: SourceModelClass) (sm : SourceModel),
  incl (allModelElementsOfType c sm) (allModelElements sm).
Proof.
  unfold allModelElementsOfType, incl.
  intros.
  apply filter_In in H.
  destruct H.
  assumption.
Qed.

Lemma allModelElementsOfTypesInModel :
  forall (sp : list SourceModelElement) (l: list SourceModelClass) (sm : SourceModel),
  In sp (allModelElementsOfTypes l sm) -> incl sp (allModelElements sm).
Proof.
  intros.
  unfold allModelElementsOfTypes in H.
  apply in_map_iff in H. destruct H. destruct H.
  rewrite <- H.
  apply allModelElementsOfTypeInModel.
Qed.

Lemma InAllTuplesOfTypes : 
  forall (a : SourceModelElement) (sp: list SourceModelElement) (s: SourceModelClass) (l : list SourceModelClass) (sm: SourceModel),
  In (a :: sp) (allTuplesOfTypes (s :: l) sm)
  -> In (sp) (allTuplesOfTypes l sm).
Proof.
  intros.
  unfold allTuplesOfTypes, prod_cons in H.
  simpl in H.
  apply in_flat_map in H. destruct H. destruct H.
  apply in_map_iff in H0.
  crush.
Qed.

Lemma allTuplesOfTypesInModel :
  forall (sp : list SourceModelElement) (l: list SourceModelClass) (sm : SourceModel),
  In sp (allTuplesOfTypes l sm) -> incl sp (allModelElements sm).
Proof.
  intros.
  unfold allTuplesOfTypes in H.
  generalize dependent sp.
  induction l; intros.
  - simpl in H. destruct H.
    + rewrite <- H. unfold incl. intros. inversion H0.
    + contradiction.
  - destruct sp.
    + unfold incl. intros. inversion H0.
    + simpl in H.
      unfold prod_cons in H.
      apply in_flat_map in H. repeat destruct H.
      apply in_map_iff in H0. repeat destruct H0.
      unfold incl.
      intros.
      simpl in H0.
      destruct H0.
      * pose allModelElementsOfTypeInModel.
        unfold incl in i.
        apply i with (c:=a).
        rewrite <- H0.
        assumption.
      * unfold incl in IHl.
        simpl in IHl.
        generalize H0.
        apply IHl.
        assumption.
Qed.

Lemma allTuplesByRuleInModel :
  forall (sp : list SourceModelElement) (tr: Transformation) (sm : SourceModel),
  In sp (allTuplesByRule tr sm) -> incl sp (allModelElements sm).
Proof.
  intros.
  unfold allTuplesByRule in H.
  apply in_flat_map in H. destruct H. destruct H.
  apply allTuplesOfTypesInModel with (l:=(Rule_getInTypes x)).
  assumption.
Qed.

Lemma allTuplesOfTypesLength :
  forall (sp: list SourceModelElement) (l : list SourceModelClass) (sm : SourceModel),
  In sp (allTuplesOfTypes l sm) -> Datatypes.length sp = Datatypes.length l.
Proof.
  intros.
  generalize dependent sp.
  induction l; intros.
  - simpl in H. destruct H. rewrite <- H. reflexivity. contradiction.
  - unfold allTuplesOfTypes in H. simpl in H.
    unfold prod_cons in H. 
    apply in_flat_map in H.
    destruct H. destruct H.
    apply in_map_iff in H0.
    destruct H0. destruct H0.
    unfold allTuplesOfTypes, prod_cons in IHl.
    apply IHl in H1.
    simpl.
    rewrite <- H1.
    rewrite <- H0.
    reflexivity.
Qed.

Lemma maxArityLength :
  forall (tr: Transformation) (r: Rule),
  In r (Transformation_getRules tr) -> 
  Datatypes.length (Rule_getInTypes r) <= maxArity tr.
Proof.
  intros.
  unfold maxArity.
  apply max_list_upperBound.
  apply in_map_iff.
  exists (Rule_getInTypes r).
  split. reflexivity.
  apply in_map_iff.
  exists r.
  split. reflexivity.
  assumption.
Qed.

Lemma In_by_rule : 
  forall (sp: list SourceModelElement) (tr: Transformation) (sm: SourceModel),
  In sp (allTuplesByRule tr sm) -> In sp (allTuples tr sm).
Proof.
  intros.
  apply allTuples_incl_length.
  * apply allTuplesByRuleInModel with (tr:=tr).
    assumption.
  * unfold allTuplesByRule in H.
    apply in_flat_map in H. destruct H. destruct H.
    apply allTuplesOfTypesLength in H0.
    rewrite H0.
    apply maxArityLength.
    assumption.
Qed.

Lemma In_allTuplesOfTypes_inv :
  forall (a: SourceModelElement) (sp: list SourceModelElement) 
  (s: SourceModelClass) (l: list SourceModelClass)
  (sm: SourceModel),
  hasType s a = true
  -> In sp (allTuplesOfTypes l sm) 
  -> In a (allModelElements sm)
  -> In (a :: sp) (allTuplesOfTypes (s :: l) sm).
Proof.
  intros.
  unfold allTuplesOfTypes.
  simpl.
  unfold allTuplesOfTypes in H0.
  apply prod_cons_in_inv with (se:=a) (ss:=sp).
  - unfold allModelElementsOfType, hasType.
    apply filter_In.
    split.
    + assumption.
    + apply H.
  - assumption.
Qed.

Lemma In_by_rule_match :
  forall (sp: list SourceModelElement) (tr: Transformation) (sm: SourceModel) (r: Rule),
  In sp (allTuples tr sm) /\ hd_error (matchPattern tr sm sp) = return r    
  -> In sp (allTuplesOfTypes (Rule_getInTypes r) sm).
Proof.
  intros.
  destruct H.
  apply allTuples_incl in H.
  apply hd_error_In in H0.
  unfold matchPattern in H0.
  apply filter_In in H0.
  destruct H0.
  unfold matchRuleOnPattern in H1.
  destruct (checkTypes sp (Rule_getInTypes r)) eqn:dct.
  2: { inversion H1. }
  1: {
    remember (Rule_getInTypes r) as l.
    clear H1 H0 Heql.
    generalize dependent l.
    induction sp; intros.
    - simpl in dct.
      destruct l.
      + simpl.
        left.
        reflexivity.
      + inversion dct.
    - destruct l.
      + simpl in dct. inversion dct.
      + simpl in dct.
        destruct (toModelClass s a) eqn:dtmc.
        2: { inversion dct. }
        1: {
          apply In_allTuplesOfTypes_inv.
          - unfold hasType.
            rewrite dtmc.
            reflexivity.
          - apply IHsp.
            + apply incl_cons_inv in H.
              destruct H.
              assumption.
            + assumption.
          - apply incl_cons_inv in H.
            destruct H.
            assumption.
        }
  }
Qed.

Lemma In_by_rule_instantiate : 
  forall (sp: list SourceModelElement) (tr: Transformation) (sm: SourceModel),
  In sp (allTuples tr sm) /\ instantiatePattern tr sm sp <> nil -> In sp (allTuplesByRule tr sm).
Proof.
  intros.
  destruct H.
  unfold allTuplesByRule.
  apply in_flat_map.
  destruct (hd_error (matchPattern tr sm sp)) eqn:dst.
  2: {
    destruct (matchPattern tr sm sp) eqn:hdst.
    - unfold instantiatePattern in H0.
      rewrite hdst in H0.
      simpl in H0. 
      unfold not in H0.
      contradiction H0.
      reflexivity.
    - inversion dst. 
  }
  1: {
    exists r. 
    split.
    + apply hd_error_In in dst.
      apply tr_matchPattern_in in dst.
      destruct dst.
      assumption.
    + apply In_by_rule_match with (tr:=tr).
      split.
      assumption.
      assumption.
  }
Qed.

Lemma In_by_rule_apply : 
forall (sp: list SourceModelElement) (tr: Transformation) (sm: SourceModel),
In sp (allTuples tr sm) /\ applyPattern tr sm sp <> nil -> In sp (allTuplesByRule tr sm).
Proof.
  intros.
  destruct H.
  unfold allTuplesByRule.
  apply in_flat_map.
  destruct (hd_error (matchPattern tr sm sp)) eqn:dst.
  2: {
    destruct (matchPattern tr sm sp) eqn:hdst.
    - unfold applyPattern in H0.
      rewrite hdst in H0.
      simpl in H0. 
      unfold not in H0.
      contradiction H0.
      reflexivity.
    - inversion dst. 
  }
  1: {
    exists r. 
    split.
    + apply hd_error_In in dst.
      apply tr_matchPattern_in in dst.
      destruct dst.
      assumption.
    + apply In_by_rule_match with (tr:=tr).
      split.
      assumption.
      assumption.
  }
Qed.

Theorem tr_execute_in_elements :
  forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
  In te (allModelElements (execute tr sm)) <->
  (exists (sp : list SourceModelElement),
      In sp (allTuples tr sm) /\
      In te (instantiatePattern tr sm sp)).
Proof.
  intros.
  unfold execute. simpl.
  rewrite in_flat_map.
  split.
  * intros.
    destruct H. destruct H.
    exists x.
    split.
    + apply In_by_rule. assumption.
    + assumption.
  * intros.
    destruct H. destruct H.
    exists x.
    split.
    + apply In_by_rule_instantiate.
      split.
      - assumption.
      - unfold not. intros. rewrite H1 in H0. contradiction.
    + assumption.
Qed.

Theorem tr_execute_in_links :
  forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
    In tl (allModelLinks (execute tr sm)) <->
    (exists (sp : list SourceModelElement),
        In sp (allTuples tr sm) /\
        In tl (applyPattern tr sm sp)).
Proof.
  intros.
  unfold execute. simpl.
  rewrite in_flat_map.
  split.
  * intros.
    destruct H. destruct H.
    exists x.
    split.
    + apply In_by_rule. assumption.
    + assumption.
  * intros.
    destruct H. destruct H.
    exists x.
    split.
    + apply In_by_rule_apply.
      split.
      - assumption.
      - unfold not. intros.
        rewrite H1 in H0. contradiction.
    + assumption.
Qed.

Theorem tr_execute_in :
  forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement) (tl : TargetModelLink),
    (In te (allModelElements (execute tr sm)) <-> In te (allModelElements (Semantics.execute tr sm)))
    /\ (In tl (allModelLinks (execute tr sm)) <-> In tl (allModelLinks (Semantics.execute tr sm))).
Proof.
  intros.
  split.
  - rewrite tr_execute_in_elements.
    rewrite Certification.tr_execute_in_elements.
    split. trivial. trivial.
  - rewrite tr_execute_in_links.
    rewrite Certification.tr_execute_in_links.
    split. trivial. trivial.
Qed. 

Instance ByRuleEngine :
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
  OutputPatternLink := OutputPatternLink;

  TraceLink := TraceLink;

  getRules := Transformation_getRules;

  getInTypes := Rule_getInTypes;
  getGuardExpr := Rule_getGuardExpr;
  getOutputPattern := Rule_getOutputPatternElements;

  getOutputLinks := OutputPatternElement_getOutputLinks;

  execute := execute;

  matchPattern := matchPattern;
  matchRuleOnPattern := matchRuleOnPattern;

  instantiatePattern := instantiatePattern;
  instantiateRuleOnPattern := instantiateRuleOnPattern;
  instantiateIterationOnPattern := instantiateIterationOnPattern;
  instantiateElementOnPattern := instantiateElementOnPattern;

  applyPattern := applyPattern;
  applyRuleOnPattern := applyRuleOnPattern;
  applyIterationOnPattern := applyIterationOnPattern;
  applyElementOnPattern := applyElementOnPattern;
  applyLinkOnPattern := applyLinkOnPattern;

  evalOutputPatternElementExpr := evalOutputPatternElementExpr;
  evalIteratorExpr := evalIteratorExpr;

  resolveAll := resolveAllIter;
  resolve := resolveIter;

  tr_execute_in_elements := tr_execute_in_elements;
  tr_execute_in_links := tr_execute_in_links;

  tr_matchPattern_in := tr_matchPattern_in;
  tr_instantiatePattern_in := tr_instantiatePattern_in;
  tr_instantiateRuleOnPattern_in := tr_instantiateRuleOnPattern_in;
  tr_instantiateIterationOnPattern_in := tr_instantiateIterationOnPattern_in;

  tr_applyPattern_in := tr_applyPattern_in;
  tr_applyRuleOnPattern_in := tr_applyRuleOnPattern_in;
  tr_applyIterationOnPattern_in := tr_applyIterationOnPattern_in;
  tr_applyElementOnPattern_in := tr_applyElementOnPattern_in;

  (*tr_matchPattern_None := tr_matchPattern_None;

  tr_matchRuleOnPattern_None := tr_matchRuleOnPattern_None;

  tr_instantiatePattern_non_None := tr_instantiatePattern_non_None;
  tr_instantiatePattern_None := tr_instantiatePattern_None;

  tr_instantiateRuleOnPattern_non_None := tr_instantiateRuleOnPattern_non_None;

  tr_instantiateIterationOnPattern_non_None := tr_instantiateIterationOnPattern_non_None;

  tr_instantiateElementOnPattern_None := tr_instantiateElementOnPattern_None;
  tr_instantiateElementOnPattern_None_iterator := tr_instantiateElementOnPattern_None_iterator;

  tr_applyPattern_non_None := tr_applyPattern_non_None;
  tr_applyPattern_None := tr_applyPattern_None;

  tr_applyRuleOnPattern_non_None := tr_applyRuleOnPattern_non_None;

  tr_applyIterationOnPattern_non_None := tr_applyIterationOnPattern_non_None;

  tr_applyElementOnPattern_non_None := tr_applyElementOnPattern_non_None;

  tr_applyLinkOnPattern_None := tr_applyLinkOnPattern_None;
  tr_applyLinkOnPattern_None_iterator := tr_applyLinkOnPattern_None_iterator;

  tr_maxArity_in := tr_maxArity_in;

  tr_instantiateElementOnPattern_Leaf := tr_instantiateElementOnPattern_Leaf;
  tr_applyLinkOnPattern_Leaf := tr_applyLinkOnPattern_Leaf;
  tr_matchRuleOnPattern_Leaf := tr_matchRuleOnPattern_Leaf;

  tr_resolveAll_in := tr_resolveAllIter_in;
  tr_resolve_Leaf := tr_resolveIter_Leaf';*)
}. 

End ByRuleSemanticsCertification.
