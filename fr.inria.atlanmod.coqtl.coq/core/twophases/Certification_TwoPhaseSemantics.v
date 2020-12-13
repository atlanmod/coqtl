Require Import String.
Require Import Omega.
Require Import Bool.
Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.
Require Import core.Engine.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.twophases.TwoPhaseSemantics.
Require Import Coq.Logic.FunctionalExtensionality.

Section Certification.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink)
          (Transformation := @Transformation SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink).

  (** EXECUTE TRACE *)

  Lemma tr_executeTraces_in_elements :
  forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
    In te (allModelElements (executeTraces tr sm)) <->
    In te (fst (instantiateTraces tr sm)).
  Proof.
    intros.
    simpl.
    crush.
  Qed. 

  Lemma tr_executeTraces_in_links :
  forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
    In tl (allModelLinks (executeTraces tr sm)) <->
    In tl (applyTraces tr sm (trace tr sm)).
  Proof.
    intros.
    simpl.
    crush.
  Qed.

  (** Instantiate *)

  (* Please check the lemma formula *)
  Lemma tr_instantiateTraces_in :
  forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
    In te (fst (instantiateTraces tr sm)) <->
    (exists (tl : (@TraceLink SourceModelElement TargetModelElement)),
        In tl (trace tr sm) /\
        te = (TraceLink_getTargetElement tl) ).
  Proof.
    intros.
    simpl.
    split.
    + induction (trace tr sm).
      ++ crush.
      ++ intros.
         simpl in H.
         destruct H. 
         +++ exists a.
             crush.
         +++ specialize (IHl H).
             destruct IHl.
             exists x.
             crush.
    + intros.
      destruct H. 
      destruct H.
      rewrite H0.
      apply in_map.
      exact H.
  Qed.

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

  Definition traceRuleOnPattern1 := (@traceRuleOnPattern SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink).
 
  Lemma tr_traceRuleOnPattern_in:
  forall (r: Rule) (sm : SourceModel) (sp : list SourceModelElement) (tl : TraceLink),
    In tl (traceRuleOnPattern1 r sm sp) <->
    (exists (iter: nat),
        In iter (indexes (evalIteratorExpr r sm sp)) /\
        In tl (traceIterationOnPattern r sm sp iter)).
  Proof.
    intros.
    apply in_flat_map.
  Qed.

  Definition traceIterationOnPattern1 := (@traceIterationOnPattern SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink).
 
  Lemma tr_traceIterationOnPattern_in:
  forall (r: Rule) (sm : SourceModel) (sp : list SourceModelElement) (iter: nat) (tl : TraceLink),
    In tl (traceIterationOnPattern1 r sm sp iter) <->
    (exists (o: OutputPatternElement),
        In o (Rule_getOutputPatternElements (SourceModelClass := SourceModelClass) r) /\
        In tl ((fun o => optionToList (traceElementOnPattern o sm sp iter)) o)).
  Proof.
    intros.
    apply in_flat_map.
  Qed.

  (* TODO works inside TwoPhaseSemantics.v *)
(*   Definition OutputPatternElement1 := (@OutputPatternElement SourceModelElement SourceModelLink SourceModelClass TargetModelElement ).
  
  Lemma tr_traceElementOnPattern_in:
  forall (o: OutputPatternElement1) (sm : SourceModel) (sp : list SourceModelElement) (iter: nat) (o: OutputPatternElement) (tl : TraceLink),
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
Qed. *)

  Definition evalOutputPatternElementExpr1 :=  (@evalOutputPatternElementExpr SourceModelElement SourceModelLink SourceModelClass TargetModelElement ).
  
  Theorem tr_instantiateElementOnPattern_leaf:
    forall (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat),
      instantiateElementOnPattern o sm sp iter = evalOutputPatternElementExpr1 sm sp iter o.
  Proof.
    crush.
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

  Lemma tr_applyRuleOnPattern_in : 
  forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (tls: list TraceLink),
      In tl (applyRuleOnPatternTraces r tr sm sp tls) <->
      (exists (i: nat),
          In i (indexes (evalIteratorExpr r sm sp)) /\
          In tl (applyIterationOnPatternTraces r tr sm sp i tls)).
  Proof.
   intros.
   apply in_flat_map.
  Qed.


  Lemma tr_applyIterationOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat)  (tls: list TraceLink),
        In tl (applyIterationOnPatternTraces r tr sm sp i tls) <->
        (exists (ope: OutputPatternElement),
            In ope (Rule_getOutputPatternElements (SourceModelClass := SourceModelClass) r) /\ 
            In tl (applyElementOnPatternTraces ope tr sm sp i tls)).
  Proof.
    intros.
    apply in_flat_map.
  Qed.

  Lemma tr_applyElementOnPatternTraces_in : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) 
             (i:nat) (ope: OutputPatternElement)  (tls: list TraceLink),
        In tl (applyElementOnPatternTraces ope tr sm sp i tls) <->
        (exists (oper: OutputPatternElementReference) (te: TargetModelElement),
            In oper (OutputPatternElement_getOutputElementReferences ope) /\ 
            (evalOutputPatternElementExpr sm sp i ope) = Some te /\
            applyReferenceOnPatternTraces oper tr sm sp i te tls = Some tl).
  Proof.
    split.
    * intros.
      apply in_flat_map in H.
      destruct H.
      exists x.
      unfold optionToList in H.
      destruct H.
      destruct (evalOutputPatternElementExpr sm sp i ope) eqn: eval_ca.
      - destruct (applyReferenceOnPatternTraces x tr sm sp i t) eqn: ref_ca.
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

  Lemma applyReferenceOnPatternTraces_leaf : 
      forall (oper: OutputPatternElementReference)
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) (te: TargetModelElement) (tls: list TraceLink),
        applyReferenceOnPatternTraces oper tr sm sp iter te tls  = evalOutputPatternLinkExpr sm sp te iter tls oper.
  Proof.
   crush.
  Qed.



  (** * Resolve *)

  Theorem tr_resolveAll_in:
    forall (tls: list TraceLink) (sm: SourceModel) (name: string)
      (type: TargetModelClass) (sps: list(list SourceModelElement)),
      resolveAll tls sm name type sps = resolveAllIter tls sm name type sps 0.
  Proof.
    crush.
  Qed.

  Theorem tr_resolveAllIter_in:
    forall (tls: list TraceLink) (sm: SourceModel) (name: string)
      (type: TargetModelClass) (sps: list(list SourceModelElement)) (iter: nat)
      (te: denoteModelClass type),
      (exists tes: list (denoteModelClass type),
          resolveAllIter tls sm name type sps iter = Some tes /\ In te tes) <->
      (exists (sp: list SourceModelElement),
          In sp sps /\
          resolveIter tls sm name type sp iter = Some te).
  Proof.
    intros.
        intros.
    split.
    - intros.
      destruct H. destruct H.
      unfold resolveAllIter in H.
      inversion H.
      rewrite <- H2 in H0.
      apply in_flat_map in H0.
      destruct H0. destruct H0.
      exists x0. split; auto.
      destruct (resolveIter tls sm name type x0 iter).
      -- unfold optionToList in H1. crush.
      -- crush.
    - intros.
      destruct H. destruct H.
      remember (resolveAllIter tls sm name type sps iter) as tes1.
      destruct tes1 eqn: resolveAll.
      -- exists l.
         split. auto.
         unfold resolveAllIter in Heqtes1.
         inversion Heqtes1.
         apply in_flat_map.
         exists x. split. auto.
         destruct (resolveIter tls sm name type x iter).
         --- crush.
         --- crush.
      -- unfold resolveAllIter in Heqtes1.
         crush.
  Qed.

  Theorem tr_resolve_in:
    forall (tls: list TraceLink) (sm: SourceModel) (name: string)
      (type: TargetModelClass) (sp: list SourceModelElement),
      resolve tls sm name type sp = resolveIter tls sm name type sp 0.
  Proof.
    crush.
  Qed.

  (* this one direction, the other one is not true since exists cannot gurantee uniqueness in find *)
  Theorem tr_resolveIter_leaf:
    forall (tls:list TraceLink) (sm : SourceModel) (name: string) (type: TargetModelClass)
      (sp: list SourceModelElement) (iter: nat) (x: denoteModelClass type),
      resolveIter tls sm name type sp iter = return x ->
       (exists (tl : TraceLink),
         In tl tls /\
         Is_true (list_beq SourceModelElement beq_ModelElement (TraceLink_getSourcePattern tl) sp) /\
         ((TraceLink_getIterator tl) = iter) /\ 
         ((TraceLink_getName tl) = name)%string /\
         (toModelClass type (TraceLink_getTargetElement tl) = Some x)). 
  Proof.
  intros.
  unfold resolveIter in H.
  destruct (find (fun tl: TraceLink => 
  (Semantics.list_beq SourceModelElement beq_ModelElement (TraceLink_getSourcePattern tl) sp) &&
  ((TraceLink_getIterator tl) =? iter) &&
  ((TraceLink_getName tl) =? name)%string) tls) eqn: find.
  - exists t.
    apply find_some in find.
    destruct find.
    symmetry in H1.
    apply andb_true_eq in H1.
    destruct H1.
    apply andb_true_eq in H1.
    destruct H1.
    crush.
    -- apply beq_nat_true. crush.
    -- apply String.eqb_eq. crush.
  - crush.
  Qed.


  Theorem exe_preserv : 
    forall (tr: Transformation) (sm : SourceModel),
      core.twophases.TwoPhaseSemantics.executeTraces tr sm = core.Semantics.execute tr sm.
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

      TraceLink := TraceLink;

      getRules := Transformation_getRules;

      getInTypes := Rule_getInTypes;
      getGuardExpr := Rule_getGuardExpr;
      getOutputPattern := Rule_getOutputPatternElements;

      getOutputElementReferences := OutputPatternElement_getOutputElementReferences;
   
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
      applyReferenceOnPattern := applyReferenceOnPattern;

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

      tr_applyReferenceOnPattern_None := tr_applyReferenceOnPattern_None;
      tr_applyReferenceOnPattern_None_iterator := tr_applyReferenceOnPattern_None_iterator;

      tr_maxArity_in := tr_maxArity_in;

      tr_instantiateElementOnPattern_Leaf := tr_instantiateElementOnPattern_Leaf;
      tr_applyReferenceOnPattern_Leaf := tr_applyReferenceOnPattern_Leaf;
      tr_matchRuleOnPattern_Leaf := tr_matchRuleOnPattern_Leaf;

      tr_resolveAll_in := tr_resolveAllIter_in;
      tr_resolve_Leaf := tr_resolveIter_Leaf';*)
    }. 

End Certification.