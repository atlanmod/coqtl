Require Import String.
Require Import Bool.
Require Import core.utils.Utils.
Require Import core.modeling.Metamodel.
Require Import core.Model.
Require Import core.modeling.ModelingEngine.
Require Import core.modeling.twophases.TwoPhaseEngine.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.modeling.ModelingCertification.
Require Import core.modeling.twophases.TwoPhaseSemantics.
Require Import Coq.Logic.FunctionalExtensionality.


Section TwoPhaseCertification.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}. 
(** EXECUTE TRACE *)

Lemma tr_executeTraces_in_elements :
forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
      In te (allModelElements (executeTraces tr sm)) <->
      (exists (tl : TraceLink) (sp : list SourceModelElement),
          In sp (allTuples tr sm) /\
          In tl (tracePattern tr sm sp) /\
          te = TraceLink_getTargetElement tl).
Proof.
  intros.
  split.
  + intro. 
    assert (exists (tl : TraceLink),
                In tl (trace tr sm) /\
                te = (TraceLink_getTargetElement tl) ).
    { simpl in H.
          induction (trace tr sm).
          ++ crush.
          ++ intros.
              simpl in H.
              destruct H. 
              +++ exists a.
                  crush.
              +++ specialize (IHl H).
                  destruct IHl.
                  exists x.
                  crush. }
    destruct H0.
    destruct H0.
    assert (exists (sp : list SourceModelElement),
                In sp (allTuples tr sm) /\
                In x (tracePattern tr sm sp)).
    { apply in_flat_map. crush. }
    destruct H2.
    destruct H2.
    exists x. exists x0.
    crush.
  + intros.
    destruct H. 
    destruct H.
    destruct H.
    destruct H0.
    rewrite H1.
    apply in_map.
    apply in_flat_map.
    exists x0.
    split. 
    ++ exact H.
    ++ exact H0.
Qed. 

Lemma tr_executeTraces_in_links :
forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
      In tl (allModelLinks (executeTraces tr sm)) <->
          (exists (sp : list SourceModelElement),
          In sp (allTuples tr sm) /\
          In tl (applyPatternTraces tr sm sp (trace tr sm))).
Proof.
  intros.
  split.
  - simpl. intro.
    apply in_flat_map in H.
    destruct H.
    exists x.
    crush.
  - intro.
    apply in_flat_map.
    crush.
Qed.

(** Instantiate *)

(* Please check the lemma formula *)


(* These lemmas of traces are useful when we get sth like (In e traces) *)

Lemma tr_trace_in:
forall (tr: Transformation) (sm : SourceModel) (tl : TraceLink),
  In tl (trace tr sm) <->
  (exists (sp : list SourceModelElement),
      In sp (allTuples tr sm) /\
      In tl (tracePattern tr sm sp)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_tracePattern_in:
forall (tr: Transformation) (sm : SourceModel) (sp : list SourceModelElement) (tl : TraceLink),
  In tl (tracePattern tr sm sp) <->
  (exists (r:Rule),
      In r (matchPattern tr sm sp) /\
      In tl (traceRuleOnPattern r sm sp)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_traceRuleOnPattern_in:
forall (r: Rule) (sm : SourceModel) (sp : list SourceModelElement) (tl : TraceLink),
  In tl (traceRuleOnPattern r sm sp) <->
  (exists (iter: nat),
      In iter (seq 0 (evalIteratorExpr r sm sp)) /\
      In tl (traceIterationOnPattern r sm sp iter)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_traceIterationOnPattern_in:
forall (r: Rule) (sm : SourceModel) (sp : list SourceModelElement) (iter: nat) (tl : TraceLink),
  In tl (traceIterationOnPattern r sm sp iter) <->
  (exists (o: OutputPatternElement),
      In o (Rule_getOutputPatternElements r) /\
      In tl ((fun o => optionToList (traceElementOnPattern o sm sp iter)) o)).
Proof.
  intros.
  apply in_flat_map.
Qed.

(* TODO works inside TwoPhaseSemantics.v *)
Lemma tr_traceElementOnPattern_leaf:
forall (o: OutputPatternElement) (sm : SourceModel) (sp : list SourceModelElement) (iter: nat) (o: OutputPatternElement) (tl : TraceLink),
  Some tl = (traceElementOnPattern o sm sp iter) <->
  (exists (e: TargetModelElement),
      Some e = (instantiateElementOnPattern o sm sp iter) /\
      tl = (buildTraceLink (sp, iter, OutputPatternElement_getName o) e)).
Proof.
  intros.
  split.
  - intros. 
    unfold traceElementOnPattern in H.
    destruct (instantiateElementOnPattern o0 sm sp iter) eqn: e1.
    -- exists t.
      split. crush. crush.
    -- crush.
  - intros.
    destruct H.
    destruct H.
    unfold traceElementOnPattern.
    destruct (instantiateElementOnPattern o0 sm sp iter).
    -- crush.
    -- crush.
Qed. 



(** * Apply **)

Lemma tr_applyTraces_in :
forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (tls: list TraceLink),
  In tl (applyTraces tr sm tls) <->
  (exists (sp : list SourceModelElement),
      In sp (allTuples tr sm) /\
      In tl (applyPatternTraces tr sm sp tls)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyPatternTraces_in:
forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (tls: list TraceLink),
  In tl (applyPatternTraces tr sm sp tls) <->
  (exists (r : Rule),
          In r (matchPattern tr sm sp) /\
          In tl (applyRuleOnPatternTraces r tr sm sp tls)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyRuleOnPatternTraces_in : 
forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (tls: list TraceLink),
    In tl (applyRuleOnPatternTraces r tr sm sp tls) <->
    (exists (i: nat),
        In i (seq 0 (evalIteratorExpr r sm sp)) /\
        In tl (applyIterationOnPatternTraces r tr sm sp i tls)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyIterationOnPatternTraces_in : 
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat)  (tls: list TraceLink),
      In tl (applyIterationOnPatternTraces r tr sm sp i tls) <->
      (exists (ope: OutputPatternElement),
          In ope (Rule_getOutputPatternElements r) /\ 
          In tl (applyElementOnPatternTraces ope tr sm sp i tls)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyElementOnPatternTraces_in : 
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) 
            (i:nat) (ope: OutputPatternElement)  (tls: list TraceLink),
      In tl (applyElementOnPatternTraces ope tr sm sp i tls) <->
      (exists (oper: OutputPatternLink) (te: TargetModelElement),
          In oper (OutputPatternElement_getOutputLinks ope) /\ 
          (evalOutputPatternElementExpr sm sp i ope) = Some te /\
          applyLinkOnPatternTraces oper tr sm sp i te tls = Some tl).
Proof.
  split.
  * intros.
    apply in_flat_map in H.
    destruct H.
    exists x.
    unfold optionToList in H.
    destruct H.
    destruct (evalOutputPatternElementExpr sm sp i ope) eqn: eval_ca.
    - destruct (applyLinkOnPatternTraces x tr sm sp i t) eqn: ref_ca.
      -- eexists t.
          split; crush.
      -- contradiction.
    - contradiction.
  * intros.
    apply in_flat_map.
    destruct H.
    exists x.
    unfold optionToList.
    destruct H.
    destruct H.
    destruct H0.
    split.
    - assumption.
    - crush.
Qed.

Lemma tr_applyLinkOnPatternTraces_leaf : 
    forall (oper: OutputPatternLink)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: list SourceModelElement) (iter: nat) (te: TargetModelElement) (tls: list TraceLink),
      applyLinkOnPatternTraces oper tr sm sp iter te tls  = evalOutputPatternLinkExpr sm sp te iter tls oper.
Proof.
  crush.
Qed.

Theorem exe_preserv : 
  forall (tr: Transformation) (sm : SourceModel),
    core.modeling.twophases.TwoPhaseSemantics.executeTraces tr sm = core.Semantics.execute tr sm.
Proof.
  intros.
  unfold core.Semantics.execute, executeTraces. simpl.
  f_equal.

  unfold trace.
  rewrite flat_map_concat_map. rewrite flat_map_concat_map.
  rewrite concat_map. f_equal.
  rewrite map_map. f_equal.

  unfold tracePattern, Semantics.instantiatePattern.
  apply functional_extensionality. intros.
  rewrite flat_map_concat_map. rewrite flat_map_concat_map.
  rewrite concat_map. f_equal.
  rewrite map_map. f_equal.

  unfold traceRuleOnPattern, Semantics.instantiateRuleOnPattern.
  apply functional_extensionality. intros.
  rewrite flat_map_concat_map. rewrite flat_map_concat_map.
  rewrite concat_map. f_equal.
  rewrite map_map. f_equal.

  unfold traceIterationOnPattern, Semantics.instantiateIterationOnPattern.
  apply functional_extensionality. intros.
  rewrite flat_map_concat_map. rewrite flat_map_concat_map.
  rewrite concat_map. f_equal.
  rewrite map_map. f_equal.

  unfold traceElementOnPattern.
  apply functional_extensionality. intros.
  (* TODO FACTOR OUT *)
  assert ((Semantics.instantiateElementOnPattern x2 sm x x1) = (instantiateElementOnPattern x2 sm x x1)).
  { crush. }
  destruct (instantiateElementOnPattern x2 sm x x1). 
  reflexivity. reflexivity.  
Qed. 

Lemma tr_execute_in_elements' :
forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
  In te (allModelElements (executeTraces tr sm)) <->
  (exists (sp : list SourceModelElement),
      In sp (allTuples tr sm) /\
      In te (instantiatePattern tr sm sp)).
Proof.
  intros.
  assert ((executeTraces tr sm) = (execute tr sm)). { apply exe_preserv. }
  rewrite H.
  specialize (Certification.tr_execute_in_elements tr sm te).
  crush.
Qed.

Lemma tr_execute_in_links' :
forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
  In tl (allModelLinks (executeTraces tr sm)) <->
  (exists (sp : list SourceModelElement),
      In sp (allTuples tr sm) /\
      In tl (applyPattern tr sm sp)).
Proof.
  intros.
  assert ((executeTraces tr sm) = (execute tr sm)). { apply exe_preserv. }
  rewrite H.
  specialize (Certification.tr_execute_in_links tr sm tl).
  crush.
Qed.

(*Instance TwoPhaseCoqTLEngine :
TransformationEngineModeling (@ModelingCoqTLEngine SourceModelElement SourceModelLink TargetModelElement TargetModelLink):=
{
  SourceModelClass := SourceModelClass;
  SourceModelReference := SourceModelReference;
  TargetModelClass := TargetModelClass;
  TargetModelReference := TargetModelReference;

  resolveAll := resolveAllIter;
  resolve := resolveIter;

  (* lemmas *)

  tr_resolveAll_in := tr_resolveAllIter_in;
  tr_resolve_Leaf := tr_resolveIter_leaf;
}. 

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

    (* syntax and accessors *)

    Transformation := Transformation;
    Rule := Rule;
    OutputPatternElement := OutputPatternElement;
    OutputPatternLink := OutputPatternLink;

    TraceLink := TraceLink;

    Transformation_getRules := Transformation_getRules;

    Rule_getInTypes := Rule_getInTypes;
    Rule_getOutputPatternElements := Rule_getOutputPatternElements;

    OutputPatternElement_getOutputLinks := OutputPatternElement_getOutputLinks;

    TraceLink_getSourcePattern := TraceLink_getSourcePattern;
    TraceLink_getIterator := TraceLink_getIterator;
    TraceLink_getName := TraceLink_getName;
    TraceLink_getTargetElement := TraceLink_getTargetElement;

    (* semantic functions *)

    execute := executeTraces;

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
    evalOutputPatternLinkExpr := evalOutputPatternLinkExpr;
    evalGuardExpr := evalGuardExpr;

    trace := trace;

    resolveAll := resolveAllIter;
    resolve := resolveIter;

    (* lemmas *)

    tr_execute_in_elements := tr_execute_in_elements';
    tr_execute_in_links := tr_execute_in_links';

    tr_matchPattern_in := tr_matchPattern_in;
    tr_matchRuleOnPattern_Leaf := tr_matchRuleOnPattern_Leaf;

    tr_instantiatePattern_in := tr_instantiatePattern_in;
    tr_instantiateRuleOnPattern_in := tr_instantiateRuleOnPattern_in;
    tr_instantiateIterationOnPattern_in := tr_instantiateIterationOnPattern_in;
    tr_instantiateElementOnPattern_leaf := tr_instantiateElementOnPattern_leaf;

    tr_applyPattern_in := tr_applyPattern_in;
    tr_applyRuleOnPattern_in := tr_applyRuleOnPattern_in;
    tr_applyIterationOnPattern_in := tr_applyIterationOnPattern_in;
    tr_applyElementOnPattern_in := tr_applyElementOnPattern_in;
    tr_applyLinkOnPatternTraces_leaf := tr_applyLinkOnPattern_leaf;

    tr_resolveAll_in := tr_resolveAllIter_in;
    tr_resolve_Leaf := tr_resolveIter_leaf;

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
  }.*)


(* Instance CoqTLEngineTrace :
  (TransformationEngineTrace CoqTLEngine).
Proof.
  eexists.
(* tr_executeTraces_in_elements *) exact tr_executeTraces_in_elements.
(* tr_executeTraces_in_links *) exact tr_executeTraces_in_links.

(* tr_tracePattern_in *) exact tr_tracePattern_in.
(* tr_traceRuleOnPattern_in *) exact tr_traceRuleOnPattern_in.
(* tr_traceIterationOnPattern_in *) exact tr_traceIterationOnPattern_in.
(* tr_traceElementOnPattern_leaf *) exact tr_traceElementOnPattern_leaf.

(* tr_applyPatternTraces_in  *) exact tr_applyPatternTraces_in.
(* tr_applyRuleOnPattern_in *) exact tr_applyRuleOnPatternTraces_in.
(* tr_applyIterationOnPattern_in *) exact tr_applyIterationOnPatternTraces_in.
(* tr_applyElementOnPatternTraces_in *) exact tr_applyElementOnPatternTraces_in.
(* tr_applyLinkOnPatternTraces_leaf *) exact tr_applyLinkOnPatternTraces_leaf.

Qed.

*)

End TwoPhaseCertification.