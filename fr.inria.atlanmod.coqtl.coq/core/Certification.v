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

Section Certification.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}.
  Context {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}.
  Context {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}.
  Context {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}.
  Context (SourceModel := Model SourceModelElement SourceModelLink).
  Context (TargetModel := Model TargetModelElement TargetModelLink).
  Context (Transformation := @Transformation SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink).

  Lemma tr_execute_in_elements :
  forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
    In te (allModelElements (execute tr sm)) <->
    (exists (sp : list SourceModelElement),
        In sp (allTuples tr sm) /\
        In te (instantiatePattern tr sm sp)).
  Proof.
    intros.
    apply in_flat_map.
  Qed.

  Lemma tr_execute_in_links :
  forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
    In tl (allModelLinks (execute tr sm)) <->
    (exists (sp : list SourceModelElement),
        In sp (allTuples tr sm) /\
        In tl (applyPattern tr sm sp)).
  Proof.
    intros.
    apply in_flat_map.
  Qed.

  Lemma tr_matchPattern_in :
  forall (tr: Transformation) (sm : SourceModel),
    forall (sp : list SourceModelElement)(r : Rule),
      In r (matchPattern tr sm sp) <->
        In r (Transformation_getRules tr) /\
        matchRuleOnPattern r sm sp = true.
  Proof.
    intros.
    apply filter_In.
  Qed.

  Definition evalGuardExpr1 :=  (@evalGuardExpr SourceModelElement SourceModelLink
        SourceModelClass SourceModelReference smm TargetModelElement TargetModelLink).
  

  Lemma tr_matchRuleOnPattern_Leaf : 
  forall (tr: Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
     matchRuleOnPattern r sm sp =
       match evalGuardExpr1 r sm sp with Some true => true | _ => false end.
  Proof.
   crush.
  Qed.

  Lemma tr_instantiatePattern_in :
  forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
    In te (instantiatePattern tr sm sp) <->
    (exists (r : Rule),
        In r (matchPattern tr sm sp) /\
        In te (instantiateRuleOnPattern r sm sp)).
  Proof.
    intros.
    apply in_flat_map.
  Qed.

  Lemma tr_instantiateRuleOnPattern_in :
  forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
    In te (instantiateRuleOnPattern r sm sp) <->
    (exists (i: nat),
        In i (indexes (evalIteratorExpr r sm sp)) /\
        In te (@instantiateIterationOnPattern SourceModelElement SourceModelLink
        SourceModelClass TargetModelElement TargetModelLink r sm sp i)).
  Proof.
   intros.
   apply in_flat_map.
  Qed.

  Lemma tr_instantiateIterationOnPattern_in : 
  forall (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement) (i:nat),
    In te (instantiateIterationOnPattern r sm sp i)
    <->
    (exists (ope: OutputPatternElement),
        In ope (Rule_getOutputPatternElements (SourceModelClass := SourceModelClass) r) /\ 
        instantiateElementOnPattern (TargetModelLink:=TargetModelLink) ope sm sp i = Some te).
  Proof.
    split.
    * intros.
      apply in_flat_map in H.
      destruct H.
      exists x.
      unfold optionToList in H.
      destruct H.
      split. 
      - assumption.
      - destruct (instantiateElementOnPattern x sm sp i).
        ** crush.
        ** contradiction.
    * intros.
      apply in_flat_map.
      destruct H.
      exists x.
      unfold optionToList.
      destruct H.
      split.
      - assumption.
      - crush.
  Qed.

  Definition evalOutputPatternElementExpr1 :=  (@evalOutputPatternElementExpr SourceModelElement SourceModelLink
        TargetModelElement TargetModelLink).

  Lemma  tr_instantiateElementOnPattern_leaf:
        forall (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat),
          instantiateElementOnPattern o sm sp iter = evalOutputPatternElementExpr1 sm sp iter o.
  Proof.
    crush.
  Qed.

  Lemma tr_applyPattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
        In tl (applyPattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In tl (applyRuleOnPattern r tr sm sp)).
  Proof.
    intros.
    apply in_flat_map.
  Qed.

  Lemma tr_applyRuleOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
        In tl (applyRuleOnPattern r tr sm sp) <->
        (exists (i: nat),
            In i (indexes (evalIteratorExpr r sm sp)) /\
            In tl (applyIterationOnPattern r tr sm sp i)).
  Proof.
   intros.
   apply in_flat_map.
  Qed.

  Lemma tr_applyIterationOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat),
        In tl (applyIterationOnPattern r tr sm sp i) <->
        (exists (ope: OutputPatternElement),
            In ope (Rule_getOutputPatternElements (SourceModelClass := SourceModelClass) r) /\ 
            In tl (applyElementOnPattern ope tr sm sp i)).
  Proof.
    intros.
    apply in_flat_map.
  Qed.

  Lemma tr_applyElementOnPattern_in : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) 
             (i:nat) (ope: OutputPatternElement),
        In tl (applyElementOnPattern ope tr sm sp i ) <->
        (exists (oper: OutputPatternElementReference) (te: TargetModelElement),
            In oper (OutputPatternElement_getOutputElementReferences ope) /\ 
            (evalOutputPatternElementExpr sm sp i ope) = Some te /\
            applyReferenceOnPattern oper tr sm sp i te = Some tl).
  Proof.
    split.
    * intros.
      apply in_flat_map in H.
      destruct H.
      exists x.
      unfold optionToList in H.
      destruct H.
      destruct (evalOutputPatternElementExpr sm sp i ope) eqn: eval_ca.
      - destruct (applyReferenceOnPattern x tr sm sp i t) eqn: ref_ca.
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

  Lemma tr_applyReferenceOnPattern_leaf : 
          forall (oper: OutputPatternElementReference)
                 (tr: Transformation)
                 (sm: SourceModel)
                 (sp: list SourceModelElement) (iter: nat) (te: TargetModelElement) (tls: list (@TraceLink SourceModelElement TargetModelElement)),
            applyReferenceOnPattern oper tr sm sp iter te  = evalOutputPatternLinkExpr sm sp te iter (trace tr sm) oper.
  Proof.
   crush.
  Qed.


(*TODO
  Lemma maxArity_length:
    forall (sp : list SourceModelElement) (tr: Transformation) (sm: SourceModel), 
    gt (length sp) (maxArity tr) -> In sp (allTuples tr sm) -> False.
  *)

  Lemma allTuples_incl:
    forall (sp : list SourceModelElement) (tr: Transformation) (sm: SourceModel), 
    In sp (allTuples tr sm) -> incl sp (allModelElements sm).
  Proof.
    intros.
    unfold allTuples in H. simpl in H. 
    apply tuples_up_to_n_incl in H.
    assumption.
  Qed.

  Lemma allTuples_incl_length:
    forall (sp : list SourceModelElement) (tr: Transformation) (sm: SourceModel), 
    incl sp (allModelElements sm) -> length sp <= maxArity tr -> In sp (allTuples tr sm).
  Proof.
    intros.
    unfold allTuples.
    apply tuples_up_to_n_incl_length with (n:=maxArity tr) in H.
    - assumption.
    - assumption.
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
      OutputPatternElementReference := OutputPatternElementReference;

      TraceLink := TraceLink;

      Transformation_getRules := Transformation_getRules;

      Rule_getInTypes := Rule_getInTypes;
      Rule_getOutputPatternElements := Rule_getOutputPatternElements;

      OutputPatternElement_getOutputElementReferences := OutputPatternElement_getOutputElementReferences;

      TraceLink_getSourcePattern := TraceLink_getSourcePattern;
      TraceLink_getIterator := TraceLink_getIterator;
      TraceLink_getName := TraceLink_getName;
      TraceLink_getTargetElement := TraceLink_getTargetElement;

      (* semantic functions *)

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
      evalOutputPatternLinkExpr := evalOutputPatternLinkExpr;
      evalGuardExpr := evalGuardExpr;

      trace := trace;

      resolveAll := resolveAllIter;
      resolve := resolveIter;

      (* lemmas *)

      tr_execute_in_elements := tr_execute_in_elements;
      tr_execute_in_links := tr_execute_in_links;

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
      tr_applyReferenceOnPatternTraces_leaf := tr_applyReferenceOnPattern_leaf;

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