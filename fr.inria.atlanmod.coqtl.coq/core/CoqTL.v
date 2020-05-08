Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.
Require Import core.Engine.
Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.
Require Import Coq.Program.Equality.
Section CoqTL.

  Variables (SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type)
            (smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference)
            (TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type)
            (tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference).

  Definition SourceModel := Model SourceModelElement SourceModelLink.
  Definition TargetModel := Model TargetModelElement TargetModelLink.

  (** * Abstract Syntax **)

  (** ** Expression Types **)

  Definition outputReferenceTypes
             (sclasses : list SourceModelClass) (tclass: TargetModelClass)  (tref: TargetModelReference):=
    denoteFunction smm (sclasses) ((denoteModelClass tclass) -> option (denoteModelReference tref)).

  Definition outputPatternElementTypes
             (sclasses : list SourceModelClass) (tclass: TargetModelClass) :=
    denoteFunction smm (sclasses) (denoteModelClass tclass).

  Definition iteratedListTypes
             (sclasses : list SourceModelClass) (itype: Type) :=
    denoteFunction smm (sclasses) (list itype).

  Definition guardTypes (sclasses : list SourceModelClass) :=
    denoteFunction smm (sclasses) bool.

  (** ** Syntax Types **)

  Inductive MatchedOutputPatternElement (InElTypes: list SourceModelClass) (IterType: Type) : Type :=
    BuildMatchedOutputPatternElement :
      string ->
      forall (OutType:TargetModelClass),
       (IterType -> SourceModel -> (outputPatternElementTypes InElTypes OutType)) ->
       MatchedOutputPatternElement InElTypes IterType.

  Inductive MatchedRule : Type :=
    BuildMatchedRule :
      string ->
      forall (InElTypes: list SourceModelClass),
        (SourceModel -> (guardTypes InElTypes))
        -> forall (IterType: Type),
        (SourceModel -> (iteratedListTypes InElTypes IterType))
        -> list (MatchedOutputPatternElement InElTypes IterType)
        -> MatchedRule.

  Inductive MatchedTransformation : Type :=
    BuildMatchedTransformation :
      list MatchedRule ->
      MatchedTransformation.

  Inductive OutputPatternElementReference (InElTypes: list SourceModelClass) (IterType: Type) (OutType:TargetModelClass): Type :=
    BuildOutputPatternElementReference :
      forall (OutRef: TargetModelReference),
        (MatchedTransformation -> IterType -> SourceModel -> (outputReferenceTypes InElTypes OutType OutRef)) ->
        OutputPatternElementReference InElTypes IterType OutType.

  Inductive OutputPatternElement (InElTypes: list SourceModelClass) (IterType: Type) : Type :=
    BuildOutputPatternElement :
      string ->
      forall (OutType:TargetModelClass),
       (IterType -> SourceModel -> (outputPatternElementTypes InElTypes OutType)) ->
       list (OutputPatternElementReference InElTypes IterType OutType)-> OutputPatternElement InElTypes IterType.

  Inductive Rule : Type :=
    BuildRule :
      (* name *) string ->
      (* from *) forall (InElTypes: list SourceModelClass),
                   (SourceModel -> (guardTypes InElTypes))
      (* for *)  -> forall (IterType: Type),
                   (SourceModel -> (iteratedListTypes InElTypes IterType))
      (* to *) -> list (OutputPatternElement InElTypes IterType)
        -> Rule.

  Inductive Transformation : Type :=
    BuildTransformation :
      list Rule ->
      Transformation.

  (** ** Accessors **)

  Definition OutputPatternElementReference_getRefType {InElTypes: list SourceModelClass} {IterType: Type} {OutType:TargetModelClass} (o: OutputPatternElementReference InElTypes IterType OutType) : TargetModelReference :=
    match o with
      BuildOutputPatternElementReference _ _ _ y _ => y
    end.

  Definition OutputPatternElementReference_getOutputReference {InElTypes: list SourceModelClass} {IterType: Type} {OutType:TargetModelClass} (o: OutputPatternElementReference InElTypes IterType OutType) :
    MatchedTransformation -> IterType -> SourceModel -> (outputReferenceTypes InElTypes OutType (OutputPatternElementReference_getRefType o)).
  Proof.
    destruct o eqn:ho.
    exact o0.
  Defined.

  Definition OutputPatternElement_getName {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) : string :=
    match o with
      BuildOutputPatternElement _ _ y _ _ _ => y
    end.

  Definition OutputPatternElement_getOutType {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) : TargetModelClass :=
    match o with
      BuildOutputPatternElement _ _ _ y _ _ => y
    end.

  Definition OutputPatternElement_getOutPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) :
    IterType -> SourceModel -> (outputPatternElementTypes InElTypes (OutputPatternElement_getOutType o)) :=
    match o with
      BuildOutputPatternElement _ _ _ _ y _ => y
    end.

  Definition OutputPatternElement_getOutputElementReferences {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) :
    list (OutputPatternElementReference InElTypes IterType (OutputPatternElement_getOutType o)) :=
    match o with
      BuildOutputPatternElement _ _ _ _ _ y => y
    end.

  Definition Rule_getName (x : Rule) : string :=
    match x with
      BuildRule y _ _ _ _ _ => y
    end.

  Definition Rule_getInTypes (x : Rule) : list SourceModelClass :=
    match x with
      BuildRule _ y _ _ _ _ => y
    end.

  Definition Rule_getGuard (x : Rule) :
    SourceModel -> (guardTypes (Rule_getInTypes x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition Rule_getIteratorType (x : Rule) : Type :=
    match x with
      BuildRule _ _ _ y _ _ => y
    end.

  Definition Rule_getIteratedList (x: Rule) :
    SourceModel -> (iteratedListTypes (Rule_getInTypes x) (Rule_getIteratorType x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition Rule_getOutputPattern (x : Rule) :
    list (OutputPatternElement (Rule_getInTypes x) (Rule_getIteratorType x)) :=
    match x with
      BuildRule _ _ _ _ _ y => y
    end.

  Definition Rule_findOutputPatternElement (r: Rule) (name: string) : option (OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) :=
    find (fun(o:OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) => beq_string name (OutputPatternElement_getName o))
         (Rule_getOutputPattern r).

  Definition Transformation_getRules (x : Transformation) : list Rule :=
    match x with BuildTransformation y => y end.

  Definition MatchedOutputPatternElement_getName {InElTypes: list SourceModelClass} {IterType: Type} (o: MatchedOutputPatternElement InElTypes IterType) : string :=
    match o with
      BuildMatchedOutputPatternElement _ _ y _ _ => y
    end.

  Definition MatchedOutputPatternElement_getOutType {InElTypes: list SourceModelClass} {IterType: Type} (o: MatchedOutputPatternElement InElTypes IterType) : TargetModelClass :=
    match o with
      BuildMatchedOutputPatternElement _ _ _ y _ => y
    end.

  Definition MatchedOutputPatternElement_getOutPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (o: MatchedOutputPatternElement InElTypes IterType) :
    IterType -> SourceModel -> (outputPatternElementTypes InElTypes (MatchedOutputPatternElement_getOutType o)) :=
    match o with
      BuildMatchedOutputPatternElement _ _ _ _ y => y
    end.

  Definition MatchedRule_getName (x : MatchedRule) : string :=
    match x with
      BuildMatchedRule y _ _ _ _ _ => y
    end.

  Definition MatchedRule_getInTypes (x : MatchedRule) : list SourceModelClass :=
    match x with
      BuildMatchedRule _ y _ _ _ _ => y
    end.

  Definition MatchedRule_getGuard (x : MatchedRule) :
    SourceModel -> (guardTypes (MatchedRule_getInTypes x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition MatchedRule_getIteratorType (x : MatchedRule) : Type :=
    match x with
      BuildMatchedRule _ _ _ y _ _ => y
    end.

  Definition MatchedRule_getIteratedList (x: MatchedRule) :
    SourceModel -> (iteratedListTypes (MatchedRule_getInTypes x) (MatchedRule_getIteratorType x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition MatchedRule_getOutputPattern (x : MatchedRule) :
    list (MatchedOutputPatternElement (MatchedRule_getInTypes x) (MatchedRule_getIteratorType x)) :=
    match x with
      BuildMatchedRule _ _ _ _ _ y => y
    end.

  Definition MatchedTransformation_getRules (x : MatchedTransformation) : list MatchedRule :=
    match x with BuildMatchedTransformation y => y end.

  (** ** Copying Matched Transformation *)

  Definition matchOutputPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (x: OutputPatternElement InElTypes IterType)
    : MatchedOutputPatternElement InElTypes IterType :=
    match x with
    | BuildOutputPatternElement _ _ c d e f => BuildMatchedOutputPatternElement InElTypes IterType c d e
    end.

  Definition matchRule (x: Rule) : MatchedRule :=
    match x with
    | BuildRule a b c d e f => BuildMatchedRule a b c d e (map matchOutputPatternElement f)
    end.

  Definition matchTransformation (x: Transformation) : MatchedTransformation :=
    match x with
    | BuildTransformation a => BuildMatchedTransformation (map matchRule a)
    end.

  Definition unmatchOutputPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (x: MatchedOutputPatternElement InElTypes IterType)
    : OutputPatternElement InElTypes IterType :=
    match x with
    | BuildMatchedOutputPatternElement _ _ c d e => BuildOutputPatternElement InElTypes IterType c d e nil
    end.

  Definition unmatchRule (x: MatchedRule) : Rule :=
    match x with
    | BuildMatchedRule a b c d e f => BuildRule a b c d e (map unmatchOutputPatternElement f)
    end.

  Definition unmatchTransformation (x: MatchedTransformation) : Transformation :=
    match x with
    | BuildMatchedTransformation a => BuildTransformation (map unmatchRule a)
    end.

  (** * Semantics **)

  (** ** Expression Evaluation **)

  Definition evalGuard (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
    evalFunction smm sm (Rule_getInTypes r) bool (Rule_getGuard r) sp.

  Definition evalIterator (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) :
    list (Rule_getIteratorType r) :=
    optionListToList
      (evalFunction
         smm sm
         (Rule_getInTypes r) (list (Rule_getIteratorType r)) (Rule_getIteratedList r) sp).

  Definition evalOutputPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (sm: SourceModel) (sp: list SourceModelElement) (iter: IterType) (o: OutputPatternElement InElTypes IterType)
    : option TargetModelElement :=
    let val :=
        evalFunction smm sm InElTypes (denoteModelClass (OutputPatternElement_getOutType o)) ((OutputPatternElement_getOutPatternElement o) iter) sp in
    match val with
    | None => None
    | Some r => Some (toModelElement (OutputPatternElement_getOutType o) r)
    end.

  Definition evalOutputPatternElementReference
             {InElTypes: list SourceModelClass} {IterType: Type} {TargetType: TargetModelClass}
             (sm: SourceModel) (sp: list SourceModelElement) (oe: TargetModelElement) (iter: IterType) (tr: MatchedTransformation)
             (o: OutputPatternElementReference InElTypes IterType TargetType)
    : option TargetModelLink :=
    let val :=
        evalFunction smm sm InElTypes ((denoteModelClass TargetType) -> option (denoteModelReference (OutputPatternElementReference_getRefType o)))
                     ((OutputPatternElementReference_getOutputReference o) tr iter) sp in
    match val with
    | None => None
    | Some r =>
      match toModelClass TargetType oe with
      | None => None
      | Some t =>
        match r t with
        | None => None
        | Some s => Some (toModelLink (OutputPatternElementReference_getRefType o) s)
        end
      end
    end.

  (** ** Rule application **)

  Definition matchRuleOnPattern (r: Rule) (sm : SourceModel) (sp: list SourceModelElement) : option bool :=
    evalGuard r sm sp.

  Definition matchPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list Rule :=
    filter (fun (r:Rule) =>
              match matchRuleOnPattern r sm sp with
              | (Some true) => true
              | _ => false end) (Transformation_getRules tr).

  Definition instantiateElementOnPattern (r: Rule) (o: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat)
    : option TargetModelElement :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (nth_error (evalIterator r sm sp) iter) with
        | Some i => evalOutputPatternElement sm sp i o
        | None => None
        end
      else
        None.

  Definition instantiateIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : option (list TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (flat_map (fun o => optionToList (instantiateElementOnPattern r o sm sp iter))
                              (Rule_getOutputPattern r)) with
        | nil => None
        | l => Some l
        end
      else
        None.

  (*TODO change to:
         match  (indexes (length (evalIterator r sm sp))) with *)
  Definition instantiateRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (flat_map (fun i:nat => optionListToList (instantiateIterationOnPattern r sm sp i))
                       (indexes (length (evalIterator r sm sp)))) with
        | nil => None
        | l => Some l
        end
      else
        None.

  Definition instantiatePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    match matchPattern tr sm sp with
    | nil => None
    | l => match  (flat_map (fun r => optionListToList (instantiateRuleOnPattern r sm sp)) l) with
          | nil => None
          | l => Some l
           end
    end.

  Definition instantiateRuleOnPatternIterName (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (name: string): option (TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (Rule_findOutputPatternElement r name) with
        | Some o =>  instantiateElementOnPattern r o sm sp iter
        | None => None
        end
      else
        None.

  Definition instantiateElementsOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (name: string) : option (list TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (flat_map (fun it : nat => optionToList (instantiateRuleOnPatternIterName r sm sp it name))
                       (indexes (length (evalIterator r sm sp))))
      else
        None.

  Definition applyReferenceOnPattern
             (r: Rule)
             (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r))
             (oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope))
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) : option TargetModelLink :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (nth_error (evalIterator r sm sp) iter) with
        | Some i =>
          match (evalOutputPatternElement sm sp i ope) with
          | Some l => evalOutputPatternElementReference sm sp l i (matchTransformation tr) oper
          | None => None
          end
        | None => None
        end
      else
        None.

  Definition applyElementOnPattern
             (r: Rule)
             (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r))
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) : option (list TargetModelLink):=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (flat_map ( fun oper => optionToList (applyReferenceOnPattern r ope oper tr sm sp iter))
                        (OutputPatternElement_getOutputElementReferences ope)) with
        | nil => None
        | l=> Some l
        end
      else
        None.

  Definition applyIterationOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : option (list TargetModelLink) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (flat_map (fun o => optionListToList (applyElementOnPattern r o tr sm sp iter))
                              (Rule_getOutputPattern r)) with
        | nil => None
        | l => Some l
        end
      else
        None.

  Definition applyRuleOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement): option (list TargetModelLink) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (flat_map (fun i:nat => optionListToList (applyIterationOnPattern r tr sm sp i))
                       (indexes (length (evalIterator r sm sp)))) with
        | nil => None
        | l => Some l
        end
      else
        None.

  Definition applyPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelLink) :=
    match matchPattern tr sm sp with
    | nil => None
    | l => match  (flat_map (fun r => optionListToList (applyRuleOnPattern r tr sm sp)) l) with
          | nil => None
          | l => Some l
           end
    end.


  Definition applyElementsOnPattern (r: Rule) (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) : option (list TargetModelLink) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (concat (flat_map (fun iter => optionToList (applyElementOnPattern r ope tr sm sp iter))
                               (indexes (length (evalIterator r sm sp)))))
      else
        None.

  (** ** Resolution **)
  Definition isMatchedRule
    (sm : SourceModel) (r: Rule) (name: string)
    (sp: list SourceModelElement) (iter: nat) : bool :=
    match matchRuleOnPattern r sm sp with
    | Some true =>
        match nth_error (evalIterator r sm sp) iter with
        | Some x =>
            match Rule_findOutputPatternElement r name with
            | Some x => true
            | None => false
            end
        | None => false
        end
    | _ => false
    end.

  Definition resolveIter (tr: MatchedTransformation) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sp: list SourceModelElement)
             (iter : nat) : option (denoteModelClass type) :=
    let tr := unmatchTransformation tr in
    let matchedRule := find (fun r:Rule => isMatchedRule sm r name sp iter)
                            (Transformation_getRules tr) in
    match matchedRule with
    | Some r => match instantiateRuleOnPatternIterName r sm sp iter name with
               | Some e => toModelClass type e
               | None => None
               end
    | None => None
    end.

  Definition resolve (tr: MatchedTransformation) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sp: list SourceModelElement) : option (denoteModelClass type) :=
    resolveIter tr sm name type sp 0.

  Definition resolveAllIter (tr: MatchedTransformation) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sps: list(list SourceModelElement)) (iter: nat)
    : option (list (denoteModelClass type)) :=
    Some (flat_map (fun l:(list SourceModelElement) => optionToList (resolveIter tr sm name type l iter)) sps).

  Definition resolveAll (tr: MatchedTransformation) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sps: list(list SourceModelElement)) : option (list (denoteModelClass type)) :=
    resolveAllIter tr sm name type sps 0.

  (** ** Rule scheduling **)

  Definition maxArity (tr: Transformation) : nat :=
    max (map (length (A:=SourceModelClass)) (map Rule_getInTypes (Transformation_getRules tr))).

  Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (allModelElements sm) (maxArity tr).

  Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
    Build_Model
      (* elements *) (flat_map (fun t => optionListToList (instantiatePattern tr sm t)) (allTuples tr sm))
      (* links *) (flat_map (fun t => optionListToList (applyPattern tr sm t)) (allTuples tr sm)).


  (** * Certification **)

  Definition matchRuleOnPattern' (r: Rule) (t: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option bool :=
    matchRuleOnPattern r sm sp.

  Definition instantiateRuleOnPattern' (r: Rule) (t: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    instantiateRuleOnPattern r sm sp.

  Definition applyRuleOnPattern' (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement): option (list TargetModelLink) :=
    applyRuleOnPattern r tr sm sp.

  Definition OutputPatternElement_getOutType' (InElTypes: list SourceModelClass) (IterType: Type) (o: OutputPatternElement InElTypes IterType) : TargetModelClass :=
    OutputPatternElement_getOutType o.

  Definition OutputPatternElement_getOutputElementReferences' (InElTypes: list SourceModelClass) (IterType: Type) (o: OutputPatternElement InElTypes IterType) :
    list (OutputPatternElementReference InElTypes IterType (OutputPatternElement_getOutType o)) :=
    OutputPatternElement_getOutputElementReferences o.

  (** ** maxArity **)

  Lemma tr_maxArity_in :
    forall (tr: Transformation) (r: Rule),
      In r (Transformation_getRules tr) ->
      maxArity tr >= length (Rule_getInTypes r).
  Proof.
    intros. apply max_list_upperBound. do 2 apply in_map. exact H.
  Qed.

  (** ** execute **)

  Theorem tr_execute_in_elements :
    forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
      In te (allModelElements (execute tr sm)) <->
      (exists (sp : list SourceModelElement) (tp : list TargetModelElement),
          incl sp (allModelElements sm) /\
          instantiatePattern tr sm sp = Some tp /\
          In te tp).
  Proof.
    intros.
    split.
    - intros.
      simpl in H.
      apply in_flat_map in H.
      destruct H.
      exists x.
      destruct H.
      destruct (instantiatePattern tr sm x) eqn:inst.
      + exists l.
        split.
        unfold allTuples in H.
        apply tuples_up_to_n_incl with (n:=(maxArity tr)). assumption.
        split. reflexivity.
        assumption.
      + contradiction.
    - intros.
      destruct H. destruct H. destruct H. destruct H0.
      unfold execute. simpl.
      apply in_flat_map.
      exists x. split.
      + apply tuples_up_to_n_incl_length.
        * assumption.
        * unfold instantiatePattern in H0.
          destruct (matchPattern tr sm x) eqn:mtch.
          ** crush.
          ** unfold matchPattern in mtch.
             assert (In r (r::l)). { crush. }
             rewrite <- mtch in H2.
             apply filter_In in H2. destruct H2.
             destruct (matchRuleOnPattern r sm x) eqn:mtch2.
             *** destruct b eqn: b_ca.
                  **** unfold matchRuleOnPattern in mtch2.
                       unfold evalGuard in mtch2.
                       unfold evalFunction in mtch2.
                       assert (evalFunctionFix SourceModelElement SourceModelLink SourceModelClass SourceModelReference smm (Rule_getInTypes r) bool (Rule_getGuard r sm) x <> None).
                       { crush. }
                       apply evalFunctionFix_intypes_el_neq_contraposition in H4.
                       apply tr_maxArity_in in H2.
                       crush.
                  **** crush.
          *** crush.
      + crush.
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
    split.
    - intros.
      simpl in H.
      apply in_flat_map in H.
      destruct H.
      exists x.
      destruct H.
      destruct (applyPattern tr sm x) eqn:appl.
      + exists l.
        split.
        unfold allTuples in H.
        apply tuples_up_to_n_incl with (n:=(maxArity tr)). assumption.
        split. reflexivity.
        assumption.
      + contradiction.
    - intros.
      destruct H. destruct H. destruct H. destruct H0.
      unfold execute. simpl.
      apply in_flat_map.
      exists x. split.
      + apply tuples_up_to_n_incl_length.
        * assumption.
        * unfold  applyPattern in H0.
          destruct (matchPattern tr sm x) eqn:mtch.
          ** crush.
          ** unfold matchPattern in mtch.
             assert (In r (r::l)). { crush. }
             rewrite <- mtch in H2.
             apply filter_In in H2. destruct H2.
             destruct (matchRuleOnPattern r sm x) eqn:mtch2.
             *** destruct b eqn: b_ca.
                  **** unfold matchRuleOnPattern in mtch2.
                       unfold evalGuard in mtch2.
                       unfold evalFunction in mtch2.
                       assert (evalFunctionFix SourceModelElement SourceModelLink SourceModelClass SourceModelReference smm (Rule_getInTypes r) bool (Rule_getGuard r sm) x <> None).
                       { crush. }
                       apply evalFunctionFix_intypes_el_neq_contraposition in H4.
                       apply tr_maxArity_in in H2.
                       crush.
                  **** crush.
          *** crush.
      + crush.
  Qed.

  (** ** instantiatePattern **)

  Theorem tr_instantiatePattern_in :
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
      (exists tp: list TargetModelElement, instantiatePattern tr sm sp = Some tp /\
       In te tp) <->
      (exists (r : Rule) (tp1 : list TargetModelElement),
          In r (matchPattern tr sm sp) /\
          instantiateRuleOnPattern r sm sp = Some tp1 /\
          In te tp1).
  Proof.
   split.
    - intros.
      unfold instantiatePattern in H.
      destruct (matchPattern tr sm sp) eqn:mtch.
      + inversion H. inversion H0. inversion H1.
      + remember (r::l) as l1.
        destruct H.
        inversion H. inversion H0.
        destruct (flat_map (fun r : Rule => optionListToList (instantiateRuleOnPattern r sm sp)) l1) eqn: flat_map_res.
        crush.
        inversion H3.
        rewrite <- H4 in H1.
        rewrite <- flat_map_res in H1.
        apply in_flat_map in H1.
        destruct H1.
        exists x0.
        destruct H1.
        destruct (instantiateRuleOnPattern x0 sm sp) eqn:inst.
        exists l2.
        split. assumption.
        split. reflexivity.
        assumption.
        contradiction.
    - intros.
      destruct (instantiatePattern tr sm sp) eqn:inst.
      + exists l. split. reflexivity.
        unfold instantiatePattern in inst.
        destruct (matchPattern tr sm sp) eqn:mtch.
        * inversion inst.
        * Arguments optionListToList : simpl never.
          Arguments flat_map : simpl never.
          destruct (flat_map (fun r : Rule => optionListToList (instantiateRuleOnPattern r sm sp)) (r::l0)) eqn: flat_map_res.
          crush.
          inversion inst.
          rewrite <- flat_map_res.
          apply in_flat_map.
          destruct H. destruct H. destruct H. destruct H0.
          exists x. split. assumption.
          unfold optionListToList.
          rewrite H0.
          assumption.
      + exfalso.
        destruct H. destruct H. destruct H. destruct H0.
        unfold instantiatePattern in inst.
        destruct (matchPattern tr sm sp) eqn:mtch.
        * contradiction.
        * destruct (flat_map (fun r : Rule => optionListToList (instantiateRuleOnPattern r sm sp)) (r::l)) eqn: flat_map_res.
          ** specialize (in_flat_map_nil (fun r : Rule => optionListToList (instantiateRuleOnPattern r sm sp)) (r::l)).
             intros.
             destruct H2.
             specialize (H2 flat_map_res x H).
             rewrite H0 in H2.
             unfold optionListToList in H2.
             crush.
          ** inversion inst.
  Qed.

  Theorem tr_instantiatePattern_non_None :
     forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      instantiatePattern tr sm sp <> None <->
      (exists (r: Rule),
          In r (matchPattern tr sm sp) /\
          instantiateRuleOnPattern' r tr sm sp <> None).
  Proof.
  split.
  - intros.
    specialize (option_res_dec (instantiatePattern tr sm) sp H).
    intro.
    destruct H0.
    unfold instantiatePattern in H.
    destruct (matchPattern tr sm sp) eqn:mtch.
    + crush.
    + destruct (flat_map (fun r : Rule => optionListToList (instantiateRuleOnPattern r sm sp)) (r :: l)) eqn:flat_map_res.
      ++ crush.
      ++ assert (In t (t::l0)). { crush. }
                               rewrite <- flat_map_res in H1. apply  in_flat_map in H1.
         destruct H1. exists x0. destruct H1.
         split.
         +++ assumption.
         +++ unfold instantiateRuleOnPattern'.
             destruct  (instantiateRuleOnPattern x0 sm sp) eqn: inst_res.
      * crush.
      * simpl in H2. crush.
   - intros.
     destruct H.
     destruct H.
     unfold instantiateRuleOnPattern' in H0.
     unfold instantiatePattern.
     destruct  (matchPattern tr sm sp) eqn: mtch.
     + crush.
     + destruct (flat_map (fun r0 : Rule => optionListToList (instantiateRuleOnPattern r0 sm sp)) (r :: l)) eqn: flat_map_res.
       ++ destruct (instantiateRuleOnPattern' x tr sm sp) eqn: inst_res.
          +++ assert (l0 <> nil).
              {             assert (matchRuleOnPattern x sm sp = Some true).
                            {
                              unfold matchPattern in mtch.
                              rewrite <- mtch in H.
                              apply filter_In in H.
                              destruct H.
                              destruct (matchRuleOnPattern x sm sp).
                              destruct b.
                              crush. crush. crush.
                            }
              unfold instantiateRuleOnPattern' in inst_res.
              unfold instantiateRuleOnPattern in inst_res.

              rewrite H1 in inst_res.
              destruct (flat_map
                 (fun i : nat => optionListToList (instantiateIterationOnPattern x sm sp i))
                 (indexes (Datatypes.length (evalIterator x sm sp)))) eqn: inst2_res.
       * crush.
       * crush.

              }
              assert (optionListToList (Some l0) <> nil).
              { crush. }
              specialize (in_flat_map_nil (fun r0 : Rule => optionListToList (instantiateRuleOnPattern r0 sm sp)) (r::l)).
              intros.
              destruct H3.
              specialize (H3 flat_map_res x H).
              rewrite <- inst_res in H2.
              unfold instantiateRuleOnPattern' in H2.
              crush.
          +++ crush.
       ++ crush.
  Qed.

  Theorem tr_instantiatePattern_None :
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      length sp > maxArity tr ->
      instantiatePattern tr sm sp = None.
  Proof.
    intros.
    unfold instantiatePattern.
    destruct (matchPattern tr sm sp ) eqn:mtch.
    - auto.
    - unfold matchPattern in mtch.
      assert (In r (r::l)). { crush. }
      rewrite <- mtch in H0.
      apply filter_In in H0.
      destruct H0.
      destruct ( matchRuleOnPattern r sm sp) eqn:mtchP.
      + destruct b eqn: b_ca.
        * unfold matchRuleOnPattern in mtchP.
          unfold evalGuard in mtchP.
          unfold evalFunction in mtchP.
          assert (maxArity tr >= length (Rule_getInTypes r)). { apply tr_maxArity_in. assumption. }
          assert (length sp > length (Rule_getInTypes r)).  { omega. }
          assert (evalFunctionFix SourceModelElement SourceModelLink SourceModelClass SourceModelReference smm (Rule_getInTypes r) bool (Rule_getGuard r sm) sp = None).
          { apply evalFunctionFix_intypes_el_neq. crush. }
          rewrite H4 in mtchP. inversion mtchP.
        * inversion H1.
      + inversion H1.
  Qed.


  (** ** instantiateRuleOnPattern **)

  Theorem tr_instantiateRuleOnPattern_in :
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
      (exists tp: list TargetModelElement, instantiateRuleOnPattern' r tr sm sp = Some tp /\
       In te tp) <->
      (exists (i: nat) (tp1: list TargetModelElement),
          i < length (evalIterator r sm sp) /\
          instantiateIterationOnPattern r sm sp i = Some tp1 /\
          In te tp1).
  Proof.
    split.
    - intros.
      unfold instantiateRuleOnPattern' in H.
      unfold instantiateRuleOnPattern in H.
      destruct (matchRuleOnPattern r sm sp) eqn:mtch.
      + destruct b.
        * Arguments optionList2List : simpl never.
          Arguments map : simpl never.
          inversion H.
          inversion H0.
          inversion H1.
          destruct (flat_map (fun i : nat => optionListToList (instantiateIterationOnPattern r sm sp i))
                     (indexes (Datatypes.length (evalIterator r sm sp)))) eqn:instI_ca.
          ** inversion H4.
          ** rewrite <- instI_ca in H4.
          inversion H4.
          rewrite <- H5 in H2.
          apply in_flat_map in H2.
          destruct H2.
          destruct H2.
          destruct (instantiateIterationOnPattern r sm sp x0) eqn:inst_ca.
          *** exists x0.
             exists l0.
             split.
             **** apply indexes_nat_upperBound.
                 exact H2.
             **** split; crush.
          *** contradiction.
        * inversion H.
          destruct H0.
          inversion H0.
      + crush.    - intros.
      destruct (instantiateRuleOnPattern' r tr sm sp) eqn:inst.
      + exists l. split. reflexivity.
        unfold instantiateRuleOnPattern' in inst.
        unfold instantiateRuleOnPattern in inst.
        destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        * destruct b.
          ** inversion inst.
             destruct (flat_map (fun i : nat => optionListToList (instantiateIterationOnPattern r sm sp i))
                     (indexes (Datatypes.length (evalIterator r sm sp)))) eqn:instI_ca.
              *** inversion inst.
              *** rewrite <- instI_ca in H1.
                  inversion H1.
                  apply in_flat_map.
                  destruct H. destruct H. destruct H. destruct H0.
                  exists x.
                  split.
                  **** apply indexes_nat_upperBound.
                      assumption.
                  **** unfold optionListToList.
                      rewrite H0.
                      assumption.
          ** inversion inst.
        * inversion inst.
      + exfalso.
        destruct H. destruct H. destruct H. destruct H0.
        unfold instantiateRuleOnPattern' in inst.
        unfold instantiateRuleOnPattern in inst.
        destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        * destruct b.
          ** destruct (flat_map (fun i : nat => optionListToList (instantiateIterationOnPattern r sm sp i))
                     (indexes (Datatypes.length (evalIterator r sm sp)))) eqn:instI_ca.
              *** assert (optionListToList (instantiateIterationOnPattern r sm sp x) = nil). {
                  specialize (in_flat_map_nil
                  (fun i : nat => optionListToList (instantiateIterationOnPattern r sm sp i))
                  (indexes (Datatypes.length (evalIterator r sm sp)))
                  ).
                  intros.
                  destruct H2.
                  specialize (H2 instI_ca).
                  specialize (H2 x).
                  apply H2.
                  apply indexes_nat_upperBound.
                  assumption.
                  }
                  destruct (instantiateIterationOnPattern r sm sp x).
                  **** unfold optionListToList in H2. crush.
                  **** crush.
              *** crush.
          ** unfold instantiateIterationOnPattern in H0.
             rewrite mtch in H0.
             inversion H0.
        * unfold instantiateIterationOnPattern in H0.
          rewrite mtch in H0.
          inversion H0.
  Qed.

  Theorem tr_instantiateRuleOnPattern_non_None :
     forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement),
      instantiateRuleOnPattern' r tr sm sp <> None <->
      (exists (i: nat),
          i < length (evalIterator r sm sp) /\
          instantiateIterationOnPattern r sm sp i <> None).
  Proof.
  intros.
  split.
  {
    intro.
    specialize (option_res_dec (instantiateRuleOnPattern' r tr sm) sp H).
    intro.
    destruct H0.
    unfold instantiateRuleOnPattern' in H.
        unfold instantiateRuleOnPattern in H.
        destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        + destruct b.
          * Arguments optionList2List : simpl never.
            Arguments map : simpl never.
            destruct (flat_map (fun i : nat => optionListToList (instantiateIterationOnPattern r sm sp i))
                       (indexes (Datatypes.length (evalIterator r sm sp)))) eqn:instI_ca.
            - crush.
            - assert (In t (t::l)). { crush. }
              rewrite <- instI_ca in H1.
                          apply in_flat_map in H1.
              destruct H1. destruct H1.
              exists x0.
              split.
              apply indexes_nat_upperBound. crush.
              unfold optionListToList in H2.
              destruct (instantiateIterationOnPattern r sm sp x0).
              -- crush.
              -- crush.
          * crush.
        + crush.
  }
  {
    intros.
    destruct H.
    destruct H.
    unfold instantiateRuleOnPattern'.
    unfold instantiateRuleOnPattern.
    destruct (matchRuleOnPattern r sm sp) eqn: mtch.
     + destruct b eqn:b_ca.
       ++ destruct (flat_map (fun i : nat => optionListToList (instantiateIterationOnPattern r sm sp i))
    (indexes (Datatypes.length (evalIterator r sm sp)))) eqn: inst_res.
          +++ specialize (in_flat_map_nil
                         (fun i : nat => optionListToList (instantiateIterationOnPattern r sm sp i))
                         (indexes (Datatypes.length (evalIterator r sm sp)))).
              intros.
              assert (In x (indexes (Datatypes.length (evalIterator r sm sp)))).
              { specialize indexes_nat_upperBound .
                intros.
                specialize (H2 x (Datatypes.length (evalIterator r sm sp))).
                destruct H2.
                specialize (H3 H). assumption.
              }
              destruct H1.
              specialize (H1 inst_res x H2).
              specialize (option_res_dec (instantiateIterationOnPattern r sm sp) x H0).
              intros.
              destruct H4.
              assert (x0 <> nil).
              {
              unfold instantiateIterationOnPattern in H4.
              rewrite mtch in H4.
              destruct (flat_map
                       (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
                        optionToList (instantiateElementOnPattern r o sm sp x)) (Rule_getOutputPattern r)) eqn: inst2_ca.
              * crush.
              * crush.
              }
              unfold optionListToList in H1.
              rewrite H4 in H1.
              crush.
          +++ crush.
       ++ unfold instantiateIterationOnPattern in H0.
          rewrite mtch in H0. crush.
    + unfold instantiateIterationOnPattern in H0.
      rewrite mtch in H0. crush.
  }
  Qed.

  (** ** instantiateIterationOnPattern **)

  Theorem tr_instantiateIterationOnPattern_in :
    forall (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement) (i:nat),
      (exists tp: list TargetModelElement, instantiateIterationOnPattern r sm sp i = Some tp /\
       In te tp) <->
      (exists (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
          In ope (Rule_getOutputPattern r) /\
          instantiateElementOnPattern r ope sm sp i = Some te).
  Proof.
    split.
    - intros.
      unfold instantiateIterationOnPattern in H.
      destruct (matchRuleOnPattern r sm sp) eqn:mtch.
      + destruct b.
        * Arguments optionList2List : simpl never.
          Arguments map : simpl never.
          destruct (flat_map
            (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
               optionToList (instantiateElementOnPattern r o sm sp i)) (Rule_getOutputPattern r)) eqn: flat_map_res.
          crush.
          inversion H.
          inversion H0.
          inversion H1.
          rewrite <- flat_map_res in H4.
          rewrite <- H4 in H2.
          apply in_flat_map in H2.
          destruct H2.
          destruct H2.
          destruct (instantiateElementOnPattern r x0 sm sp i) eqn:inst_ca.
          ** exists x0.
             split.
             *** assumption.
             *** simpl in H3; crush.
          ** contradiction.
        * inversion H.
          destruct H0.
          inversion H0.
      + crush.
    - intros.
      destruct (instantiateIterationOnPattern r sm sp i) eqn:inst.
      + exists l. split. reflexivity.
        unfold instantiateIterationOnPattern in inst.
        destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        * destruct b.
          ** destruct (flat_map
             (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
                optionToList (instantiateElementOnPattern r o sm sp i)) (Rule_getOutputPattern r)) eqn: flat_map_res.
             crush.
             inversion inst.
             rewrite <- flat_map_res.
             apply in_flat_map.
             destruct H. destruct H.
             exists x.
             split.
             *** assumption.
             *** unfold optionToList.
                 rewrite H0.
                 crush.
          ** inversion inst.
        * inversion inst.
      + exfalso.
        destruct H. destruct H.
        unfold instantiateIterationOnPattern in inst.
        destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        * destruct b.
          ** destruct (flat_map
             (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
                optionToList (instantiateElementOnPattern r o sm sp i)) (Rule_getOutputPattern r)) eqn: flat_map_res.
              specialize (in_flat_map_nil
                  (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
                    optionToList (instantiateElementOnPattern r o sm sp i))
                  (Rule_getOutputPattern r)).
              intros.
              destruct H1.
              specialize (H1 flat_map_res x H).
              rewrite H0 in H1.
              unfold optionToList in H1.
              inversion H1.
              crush.
          ** unfold instantiateElementOnPattern in H0.
             rewrite mtch in H0.
             inversion H0.
        * unfold instantiateElementOnPattern in H0.
          rewrite mtch in H0.
          inversion H0.
  Qed.

  Theorem tr_instantiateIterationOnPattern_non_None :
     forall (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (i:nat),
      instantiateIterationOnPattern r sm sp i <> None <->
      (exists (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
         In ope (Rule_getOutputPattern r) /\
         instantiateElementOnPattern r ope sm sp i <> None).
  Proof.
  intros.
  split.
  {
    intro.
    specialize (option_res_dec (instantiateIterationOnPattern r sm sp) i H).
    intro.
    destruct H0.
    unfold instantiateIterationOnPattern in H.
    destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        + destruct b.
          * Arguments optionList2List : simpl never.
            Arguments map : simpl never.
            destruct (flat_map
        (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
         optionToList (instantiateElementOnPattern r o sm sp i)) (Rule_getOutputPattern r)) eqn:instI_ca.
            - crush.
            - assert (In t (t::l)). { crush. }
              rewrite <- instI_ca in H1.
                          apply in_flat_map in H1.
              destruct H1. destruct H1.
              exists x0.
              unfold optionListToList in H2.
              destruct (instantiateElementOnPattern r x0 sm sp i).
              -- crush.
              -- crush.
          * crush.
        + crush.
  }
  {
    intros.
    destruct H.
    destruct H.
    unfold instantiateIterationOnPattern.
    destruct (matchRuleOnPattern r sm sp) eqn: mtch.
     + destruct b eqn:b_ca.
       ++ destruct (flat_map
    (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
     optionToList (instantiateElementOnPattern r o sm sp i)) (Rule_getOutputPattern r)) eqn: inst_res.
          +++ specialize (in_flat_map_nil
                         (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
              optionToList (instantiateElementOnPattern r o sm sp i))
                         (Rule_getOutputPattern r)).
              intros.
              destruct H1.

              specialize (H1 inst_res x H).
              specialize (option_res_dec (instantiateElementOnPattern r x sm sp) i H0).
              intros.
              destruct H3.
              unfold optionToList in H1.
              rewrite H3 in H1.
              crush.
          +++ crush.
       ++ unfold instantiateElementOnPattern in H0.
          rewrite mtch in H0. crush.
    + unfold instantiateElementOnPattern in H0.
      rewrite mtch in H0. crush.
  }
  Qed.

  (** ** instantiateElementOnPattern **)

  Theorem tr_instantiateElementOnPattern_None_contra :
    forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
      (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
        length sp <> length (Rule_getInTypes r) ->
        instantiateElementOnPattern r ope sm sp i <> None -> False.
  Proof.
    intros.
    assert (exists (te: TargetModelElement), instantiateElementOnPattern r ope sm sp i = Some te).
    { specialize (option_res_dec (instantiateElementOnPattern r ope sm sp)). intros.
      specialize (H1 i H0). destruct H1. exists x. crush. }
    destruct H1.
    unfold instantiateElementOnPattern in H1.
    destruct (matchRuleOnPattern r sm sp) eqn: match_res.
    - destruct b eqn:b_ca.
      -- destruct (nth_error (evalIterator r sm sp) i) eqn: eval_iter_ca.
         --- unfold evalOutputPatternElement in H1.
             destruct (evalFunction smm sm (Rule_getInTypes r)
         (denoteModelClass (OutputPatternElement_getOutType ope))
         (OutputPatternElement_getOutPatternElement ope r0) sp) eqn: eval_fun_ca.
             * unfold evalFunction in eval_fun_ca.
               specialize (evalFunctionFix_intypes_el_neq
                             SourceModelElement SourceModelLink SourceModelClass
                             SourceModelReference smm (Rule_getInTypes r)
                             (denoteModelClass (OutputPatternElement_getOutType ope))
                             (OutputPatternElement_getOutPatternElement ope r0 sm) sp).
               crush.
             * crush.
         --- crush.
      -- crush.
    - crush.
  Qed.

  Theorem tr_instantiateElementOnPattern_None :
    forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
      (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
        length sp <> length (Rule_getInTypes r) ->
        instantiateElementOnPattern r ope sm sp i = None.
  Proof.
    intros.
    destruct (instantiateElementOnPattern r ope sm sp i) eqn: Hins.
    - exfalso.
      apply (tr_instantiateElementOnPattern_None_contra sm r sp i ope).
      -- exact H.
      -- rewrite Hins. discriminate.
    - auto.
  Qed.

  Theorem tr_instantiateElementOnPattern_None_iterator_contra :
    forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
      (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
      i >= length (evalIterator r sm sp) ->
      instantiateElementOnPattern r ope sm sp i <> None -> False.
  Proof.
      intros.
      assert (exists (te: TargetModelElement), instantiateElementOnPattern r ope sm sp i = Some te).
    { specialize (option_res_dec (instantiateElementOnPattern r ope sm sp)). intros.
      specialize (H1 i H0). destruct H1. exists x. crush. }
    destruct H1.
    unfold instantiateElementOnPattern in H1.
    destruct (matchRuleOnPattern r sm sp) eqn: match_res.
    - destruct b eqn:b_ca.
      -- destruct (nth_error (evalIterator r sm sp) i) eqn: eval_iter_ca.
         --- specialize (nth_error_None (evalIterator r sm sp) i).
             crush.
         --- crush.
      -- crush.
    - crush.
  Qed.

  Theorem tr_instantiateElementOnPattern_None_iterator:
    forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
      (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
      i >= length (evalIterator r sm sp) ->
      instantiateElementOnPattern r ope sm sp i = None.
  Proof.
    intros.
    destruct (instantiateElementOnPattern r ope sm sp i) eqn: Hins.
    - exfalso.
      apply (tr_instantiateElementOnPattern_None_iterator_contra sm r sp i ope).
      -- exact H.
      -- rewrite Hins. discriminate.
    - auto.
  Qed.

  (** ** applyPattern **)

  Theorem tr_applyPattern_in :
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
      (exists tpl: list TargetModelLink, applyPattern tr sm sp = Some tpl /\
       In tl tpl) <->
      (exists (r : Rule) (tpl1 : list TargetModelLink),
          In r (matchPattern tr sm sp) /\
          applyRuleOnPattern r tr sm sp = Some tpl1 /\
          In tl tpl1).
  Proof.
   split.
    - intros.
      unfold applyPattern in H.
      destruct (matchPattern tr sm sp) eqn:mtch.
      + inversion H. inversion H0. inversion H1.
      + remember (r::l) as l1.
        destruct H.
        inversion H. inversion H0.
        destruct (flat_map (fun r : Rule => optionListToList (applyRuleOnPattern r tr sm sp)) l1) eqn: flat_map_res.
        ++ crush.
        ++ inversion H3. rewrite <- H4 in H1.
           rewrite <- flat_map_res in H1.
           apply in_flat_map in H1.
           destruct H1.
           exists x0.
           destruct H1.
           destruct (applyRuleOnPattern x0 tr sm sp) eqn:inst.
           exists l2.
           split. assumption.
           split. reflexivity.
           assumption.
           contradiction.
    - intros.
      destruct (applyPattern tr sm sp) eqn:apply.
      + exists l. split. reflexivity.
        unfold applyPattern in apply.
        destruct (matchPattern tr sm sp) eqn:mtch.
        * inversion apply.
        * Arguments optionListToList : simpl never.
          Arguments flat_map : simpl never.
          destruct (flat_map (fun r : Rule => optionListToList (applyRuleOnPattern r tr sm sp)) (r::l0)) eqn: flat_map_res.
          ** specialize (in_flat_map_nil (fun r : Rule => optionListToList (applyRuleOnPattern r tr sm sp)) (r::l0)).
             intros.
             destruct H0.
             specialize (H0 flat_map_res).
             destruct H. destruct H. destruct H.
             specialize (H0 x H).
             destruct H2.
             rewrite H2 in H0.
             unfold optionListToList in H0.
             crush.
          ** inversion apply.
             rewrite <- flat_map_res.
             apply in_flat_map.
             destruct H. destruct H. destruct H. destruct H0.
             exists x. split. assumption.
             unfold optionListToList.
             rewrite H0.
             assumption.
      + exfalso.
        destruct H. destruct H. destruct H. destruct H0.
        unfold applyPattern in apply.
        destruct (matchPattern tr sm sp) eqn:mtch.
        * contradiction.
        * destruct (flat_map (fun r : Rule => optionListToList (applyRuleOnPattern r tr sm sp)) (r::l)) eqn: flat_map_res.
          ** specialize (in_flat_map_nil (fun r : Rule => optionListToList (applyRuleOnPattern r tr sm sp)) (r::l)).
             intros.
             destruct H2.
             specialize (H2 flat_map_res x H).
             rewrite H0 in H2.
             unfold optionListToList in H2.
             crush.
          ** inversion apply.
  Qed.

  Theorem tr_applyPattern_non_None :
     forall  (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) ,
       applyPattern tr sm sp <> None <->
      (exists  (r : Rule),
         In r (matchPattern tr sm sp) /\
         applyRuleOnPattern r tr sm sp <> None).
  Proof.
    split.
  - intros.
    specialize (option_res_dec (applyPattern tr sm) sp H).
    intro.
    destruct H0.
    unfold applyPattern in H.
    destruct (matchPattern tr sm sp) eqn:mtch.
    + crush.
    + destruct (flat_map (fun r : Rule => optionListToList (applyRuleOnPattern r tr sm sp)) (r :: l)) eqn:flat_map_res.
      ++ crush.
      ++ assert (In t (t::l0)). { crush. }
         rewrite <- flat_map_res in H1. apply  in_flat_map in H1.
         destruct H1. exists x0. destruct H1.
         split.
         +++ assumption.
         +++ destruct  (applyRuleOnPattern x0 tr sm sp) eqn: apply_res.
             * crush.
             * unfold optionListToList in H2. simpl in H2. crush.
   - intros.
     destruct H.
     destruct H.
     unfold applyRuleOnPattern in H0.
     unfold applyPattern.
     destruct  (matchPattern tr sm sp) eqn: mtch.
     + crush.
     + destruct (flat_map (fun r0 : Rule => optionListToList (applyRuleOnPattern r0 tr sm sp)) (r :: l)) eqn: flat_map_res.
       ++ destruct (applyRuleOnPattern x tr sm sp) eqn: apply_res.
          +++ assert (l0 <> nil).
              { assert (matchRuleOnPattern x sm sp = Some true).
                {
                   unfold matchPattern in mtch.
                   rewrite <- mtch in H.
                   apply filter_In in H.
                   destruct (matchRuleOnPattern x sm sp).
                   destruct b. crush. crush. crush.
                }
                rewrite H1 in H0.
                unfold applyRuleOnPattern in apply_res.
                rewrite H1 in apply_res.
                destruct (flat_map
                       (fun i : nat => optionListToList (applyIterationOnPattern x tr sm sp i))
                       (indexes (Datatypes.length (evalIterator x sm sp)))) eqn: apply_res2.
                * crush.
                * crush.

              }
              assert (optionListToList (Some l0) <> nil).
              { crush. }
              specialize (in_flat_map_nil (fun r0 : Rule => optionListToList (applyRuleOnPattern r0 tr sm sp)) (r::l)).
              intros.
              destruct H3.
              specialize (H3 flat_map_res x H).
              rewrite <- apply_res in H2.
              crush.
          +++ crush.
       ++ crush.
  Qed.

  Theorem tr_applyPattern_None :
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      length sp > maxArity tr ->
      applyPattern tr sm sp = None.
  Proof.
    intros.
    unfold applyPattern.
    destruct (matchPattern tr sm sp ) eqn:mtch.
    - auto.
    - unfold matchPattern in mtch.
      assert (In r (r::l)). { crush. }
      rewrite <- mtch in H0.
      apply filter_In in H0.
      destruct H0.
      destruct ( matchRuleOnPattern r sm sp) eqn:mtchP.
      + destruct b eqn: b_ca.
        * unfold matchRuleOnPattern in mtchP.
          unfold evalGuard in mtchP.
          unfold evalFunction in mtchP.
          assert (maxArity tr >= length (Rule_getInTypes r)). { apply tr_maxArity_in. assumption. }
          assert (length sp > length (Rule_getInTypes r)).  { omega. }
          assert (evalFunctionFix SourceModelElement SourceModelLink SourceModelClass SourceModelReference smm (Rule_getInTypes r) bool (Rule_getGuard r sm) sp = None).
          { apply evalFunctionFix_intypes_el_neq. crush. }
          rewrite H4 in mtchP. inversion mtchP.
        * inversion H1.
      + inversion H1.
  Qed.

  (** ** applyRuleOnPattern **)

  Theorem tr_applyRuleOnPattern_in :
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
      (exists tpl: list TargetModelLink, applyRuleOnPattern' r tr sm sp = Some tpl /\
       In tl tpl) <->
      (exists (i: nat) (tpl1: list TargetModelLink),
          i < length (evalIterator r sm sp) /\
          applyIterationOnPattern r tr sm sp i = Some tpl1 /\
          In tl tpl1).
  Proof.
    split.
    - intros.
      unfold applyRuleOnPattern' in H.
      unfold applyRuleOnPattern in H.
      destruct (matchRuleOnPattern r sm sp) eqn:mtch.
      + destruct b.
        * Arguments optionList2List : simpl never.
          Arguments map : simpl never.
          inversion H.
          inversion H0.
          inversion H1.
          destruct (flat_map (fun i : nat => optionListToList (applyIterationOnPattern r tr sm sp i))
                     (indexes (Datatypes.length (evalIterator r sm sp)))) eqn:applyI_ca.
          ** inversion H4.
          ** rewrite <- applyI_ca in H4.
          inversion H4.
          rewrite <- H5 in H2.
          apply in_flat_map in H2.
          destruct H2.
          destruct H2.
          destruct (applyIterationOnPattern r tr sm sp x0) eqn:apply_ca.
          *** exists x0.
             exists l0.
             split.
             **** apply indexes_nat_upperBound.
                 exact H2.
             **** split; crush.
          *** contradiction.
        * inversion H.
          destruct H0.
          inversion H0.
      + crush.
    - intros.
      destruct (applyRuleOnPattern' r tr sm sp) eqn:apply.
      + exists l. split. reflexivity.
        unfold applyRuleOnPattern' in apply.
        unfold applyRuleOnPattern in apply.
        destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        * destruct b.
          ** inversion apply. destruct (flat_map (fun i : nat => optionListToList (applyIterationOnPattern r tr sm sp i)) (indexes (Datatypes.length (evalIterator r sm sp)))) eqn:applyI_ca.
              *** inversion apply.
              *** rewrite <- applyI_ca in H1.
                  inversion H1.
                  apply in_flat_map.
                  destruct H. destruct H. destruct H. destruct H0.
                  exists x.
                  split.
                  **** apply indexes_nat_upperBound.
                      assumption.
                  **** unfold optionListToList.
                      rewrite H0.
                      assumption.
          ** inversion apply.
        * inversion apply.
      + exfalso.
        destruct H. destruct H. destruct H. destruct H0.
        unfold applyRuleOnPattern' in apply.
        unfold applyRuleOnPattern in apply.
        destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        * destruct b.
          ** destruct (flat_map (fun i : nat => optionListToList (applyIterationOnPattern r tr sm sp i)) (indexes (Datatypes.length (evalIterator r sm sp)))) eqn:applyI_ca.
              *** assert (optionListToList (applyIterationOnPattern r tr sm sp x) = nil). {
                  specialize (in_flat_map_nil
                  (fun i : nat => optionListToList (applyIterationOnPattern r tr sm sp i))
                  (indexes (Datatypes.length (evalIterator r sm sp)))
                  ).
                  intros.
                  destruct H2.
                  specialize (H2 applyI_ca).
                  specialize (H2 x).
                  apply H2.
                  apply indexes_nat_upperBound.
                  assumption.
                  }
                  destruct (applyIterationOnPattern r tr sm sp x).
                  **** unfold optionListToList in H2. crush.
                  **** crush.
              *** crush.
          ** unfold applyIterationOnPattern in H0.
             rewrite mtch in H0.
             inversion H0.
        * unfold applyIterationOnPattern in H0.
          rewrite mtch in H0.
          inversion H0.
  Qed.

  Theorem tr_applyRuleOnPattern_non_None :
     forall  (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) ,
       applyRuleOnPattern r tr sm sp <> None <->
      (exists (i: nat),
        i < length (evalIterator r sm sp) /\
        applyIterationOnPattern r tr sm sp i <> None ).
  Proof.
  intros.
  split.
  {
    intro.
    specialize (option_res_dec (applyRuleOnPattern r tr sm) sp H).
    intro.
    destruct H0.
    unfold applyRuleOnPattern in H.
        destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        + destruct b.
          * Arguments optionList2List : simpl never.
            Arguments map : simpl never.
            destruct (flat_map (fun i : nat => optionListToList (applyIterationOnPattern r tr sm sp i)) (indexes (Datatypes.length (evalIterator r sm sp)))) eqn:applyI_ca.
            - crush.
            - assert (In t (t::l)). { crush. }
              rewrite <- applyI_ca in H1.
                          apply in_flat_map in H1.
              destruct H1. destruct H1.
              exists x0.
              split.
              apply indexes_nat_upperBound. crush.
              unfold optionListToList in H2.
              destruct (applyIterationOnPattern r tr sm sp x0).
              -- crush.
              -- crush.
          * crush.
        + crush.
  }
  {
    intros.
    destruct H.
    destruct H.
    unfold applyRuleOnPattern.
    destruct (matchRuleOnPattern r sm sp) eqn: mtch.
     + destruct b eqn:b_ca.
       ++ destruct (flat_map (fun i : nat => optionListToList (applyIterationOnPattern r tr sm sp i))
    (indexes (Datatypes.length (evalIterator r sm sp)))) eqn: apply_res.
          +++ specialize (in_flat_map_nil
                         (fun i : nat => optionListToList (applyIterationOnPattern r tr sm sp i))
                         (indexes (Datatypes.length (evalIterator r sm sp)))).
              intros.
              assert (In x (indexes (Datatypes.length (evalIterator r sm sp)))).
              { specialize indexes_nat_upperBound .
                intros.
                specialize (H2 x (Datatypes.length (evalIterator r sm sp))).
                destruct H2.
                specialize (H3 H). assumption.
              }
              destruct H1.
              specialize (H1 apply_res x H2).
              specialize (option_res_dec (applyIterationOnPattern r tr sm sp) x H0).
              intros.
              destruct H4.
              assert (x0 <> nil).
              {
              unfold applyIterationOnPattern in H4.
              rewrite mtch in H4.
              destruct (flat_map
           (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
            optionListToList (applyElementOnPattern r o tr sm sp x))
           (Rule_getOutputPattern r)) eqn: apply2_ca.
              * crush.
              * crush.
              }
              unfold optionListToList in H1.
              rewrite H4 in H1.
              crush.
          +++ crush.
       ++ unfold applyIterationOnPattern in H0.
          rewrite mtch in H0. crush.
    + unfold applyIterationOnPattern in H0.
      rewrite mtch in H0. crush.
  }
  Qed.

  (** ** applyIterationOnPattern **)

  Theorem tr_applyIterationOnPattern_in :
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat),
      (exists tpl: list TargetModelLink, applyIterationOnPattern r tr sm sp i = Some tpl /\
       In tl tpl) <->
      (exists (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) (tpl1: list TargetModelLink),
          In ope (Rule_getOutputPattern r) /\
          applyElementOnPattern r ope tr sm sp i = Some tpl1 /\
          In tl tpl1).
  Proof.
    split.
    - intros.
      unfold applyIterationOnPattern in H.
      destruct (matchRuleOnPattern r sm sp) eqn:mtch.
      + destruct b.
        * Arguments optionList2List : simpl never.
          Arguments map : simpl never.
          destruct (flat_map
            (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
               optionListToList (applyElementOnPattern r o tr sm sp i)) (Rule_getOutputPattern r)) eqn: flat_map_res.
          crush.
          inversion H.
          inversion H0.
          inversion H1.
          rewrite <- flat_map_res in H4.
          rewrite <- H4 in H2.
          apply in_flat_map in H2.
          destruct H2.
          destruct H2.
          destruct (applyElementOnPattern r x0 tr sm sp i) eqn:apply_ca.
          ** exists x0. exists l0.
             split.
             *** assumption.
             *** simpl in H3; crush.
          ** contradiction.
        * inversion H.
          destruct H0.
          inversion H0.
      + crush.
    - intros.
      destruct (applyIterationOnPattern r tr sm sp i) eqn:apply.
      + exists l. split. reflexivity.
        unfold applyIterationOnPattern in apply.
        destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        * destruct b.
          ** destruct (flat_map
             (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
                optionListToList (applyElementOnPattern r o tr sm sp i)) (Rule_getOutputPattern r)) eqn: flat_map_res.
             crush.
             inversion apply.
             rewrite <- flat_map_res.
             apply in_flat_map.
             destruct H. destruct H. destruct H. destruct H0.
             exists x.
             split.
             *** assumption.
             *** unfold optionToList.
                 rewrite H0.
                 crush.
          ** inversion apply.
        * inversion apply.
      + exfalso.
        destruct H. destruct H.
        unfold applyIterationOnPattern in apply.
        destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        * destruct b.
          ** destruct (flat_map
              (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
                optionListToList (applyElementOnPattern r o tr sm sp i)) (Rule_getOutputPattern r)) eqn: flat_map_res.
              *** specialize (in_flat_map_nil
                  (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
                    optionListToList (applyElementOnPattern r o tr sm sp i))
                  (Rule_getOutputPattern r)).
              intros.
              destruct H0. destruct H. destruct H2.
              specialize (H0 flat_map_res x H).
              rewrite H2 in H0.
              unfold optionListToList in H0.
              rewrite H0 in H3.
              inversion H3.
              *** crush.
          ** destruct H. destruct H0. unfold applyElementOnPattern in H0.
             rewrite mtch in H0.
             inversion H0.
        * destruct H. destruct H0. unfold applyElementOnPattern in H0.
          rewrite mtch in H0.
          inversion H0.
  Qed.

  Theorem tr_applyIterationOnPattern_non_None :
     forall  (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (i:nat),
       applyIterationOnPattern r tr sm sp i <> None <->
      (exists (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
            In ope (Rule_getOutputPattern r) /\
            applyElementOnPattern r ope tr sm sp i <> None).
  Proof.
  intros.
  split.
  {
    intro.
    specialize (option_res_dec (applyIterationOnPattern r tr sm sp) i H).
    intro.
    destruct H0.
    unfold applyIterationOnPattern in H.
    destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        + destruct b.
          * Arguments optionList2List : simpl never.
            Arguments map : simpl never.
            destruct (flat_map
        (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
         optionListToList (applyElementOnPattern r o tr sm sp i)) (Rule_getOutputPattern r)) eqn:applyI_ca.
            - crush.
            - assert (In t (t::l)). { crush. }
              rewrite <- applyI_ca in H1.
                          apply in_flat_map in H1.
              destruct H1. destruct H1.
              exists x0.
              unfold optionListToList in H2.
              destruct (applyElementOnPattern r x0 tr sm sp i).
              -- crush.
              -- crush.
          * crush.
        + crush.
  }
  {
    intros.
    destruct H.
    destruct H.
    unfold applyIterationOnPattern.
    destruct (matchRuleOnPattern r sm sp) eqn: mtch.
     + destruct b eqn:b_ca.
       ++ destruct (flat_map
    (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
     optionListToList (applyElementOnPattern r o tr sm sp i)) (Rule_getOutputPattern r)) eqn: apply_res.
          +++ specialize (in_flat_map_nil
                         (fun o : OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r) =>
              optionListToList (applyElementOnPattern r o tr sm sp i))
                         (Rule_getOutputPattern r)).
              intros.

              destruct H1.
              specialize (H1 apply_res x H).
               specialize (option_res_dec (applyElementOnPattern r x tr sm sp) i H0).
              intros.
              destruct H3.
              unfold optionListToList in H1.
              rewrite H3 in H1.

              assert (x0 <> nil).
              {
              unfold applyElementOnPattern in H3.
              rewrite mtch in H3.
              destruct (flat_map
           (fun
              oper : OutputPatternElementReference (Rule_getInTypes r)
                       (Rule_getIteratorType r) (OutputPatternElement_getOutType x) =>
            optionToList (applyReferenceOnPattern r x oper tr sm sp i))
           (OutputPatternElement_getOutputElementReferences x)) eqn: apply2_ca.
              * crush.
              * crush.
              }
              unfold optionListToList in H1.
              crush.
          +++ crush.
       ++ unfold applyElementOnPattern in H0.
          rewrite mtch in H0. crush.
    + unfold applyElementOnPattern in H0.
      rewrite mtch in H0. crush.
  }
  Qed.

  (** ** applyElementOnPattern **)

  Theorem tr_applyElementOnPattern_in :
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat) (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
      (exists tpl: list TargetModelLink, applyElementOnPattern r ope tr sm sp i = Some tpl /\
       In tl tpl) <->
      (exists (oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope)),
          In oper (OutputPatternElement_getOutputElementReferences ope) /\
          applyReferenceOnPattern r ope oper tr sm sp i = Some tl).
  Proof.
    split.
    - intros.
      unfold applyElementOnPattern in H.
      destruct (matchRuleOnPattern r sm sp) eqn:mtch.
      + destruct b.
        * Arguments optionList2List : simpl never.
          Arguments map : simpl never.
          destruct ( flat_map
            (fun
               oper : OutputPatternElementReference (Rule_getInTypes r)
                        (Rule_getIteratorType r) (OutputPatternElement_getOutType ope) =>
             optionToList (applyReferenceOnPattern r ope oper tr sm sp i))
            (OutputPatternElement_getOutputElementReferences ope)) eqn: flat_map_res.
          crush.
          inversion H.
          inversion H0.
          inversion H1.
          rewrite <- flat_map_res in H4.
          rewrite <- H4 in H2.
          apply in_flat_map in H2.
          destruct H2.
          destruct H2.
          destruct (applyReferenceOnPattern r ope x0 tr sm sp i) eqn:apply_ca.
          ** exists x0.
             split.
             *** assumption.
             *** simpl in H3; crush.
          ** contradiction.
        * inversion H.
          destruct H0.
          inversion H0.
      + crush.
    - intros.
      destruct (applyElementOnPattern r ope tr sm sp i) eqn:apply.
      + exists l. split. reflexivity.
        unfold applyElementOnPattern in apply.
        destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        * destruct b.
          ** destruct (flat_map
              (fun
                 oper : OutputPatternElementReference (Rule_getInTypes r)
                          (Rule_getIteratorType r) (OutputPatternElement_getOutType ope) =>
               optionToList (applyReferenceOnPattern r ope oper tr sm sp i))
              (OutputPatternElement_getOutputElementReferences ope)) eqn: flat_map_res.
             crush.
             inversion apply.
             rewrite <- flat_map_res.
             apply in_flat_map.
             destruct H. destruct H.
             exists x.
             split.
             *** assumption.
             *** unfold optionToList.
                 rewrite H0.
                 crush.
          ** inversion apply.
        * inversion apply.
      + exfalso.
        destruct H. destruct H.
        unfold applyElementOnPattern in apply.
        destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        * destruct b.
          ** destruct ( flat_map
              (fun
                 oper : OutputPatternElementReference (Rule_getInTypes r)
                          (Rule_getIteratorType r) (OutputPatternElement_getOutType ope) =>
               optionToList (applyReferenceOnPattern r ope oper tr sm sp i))
              (OutputPatternElement_getOutputElementReferences ope)) eqn: flat_map_res.
              *** specialize (in_flat_map_nil
                  (fun
                      oper : OutputPatternElementReference (Rule_getInTypes r)
                               (Rule_getIteratorType r) (OutputPatternElement_getOutType ope) =>
                    optionToList (applyReferenceOnPattern r ope oper tr sm sp i))
                  (OutputPatternElement_getOutputElementReferences ope)).
              intros.  destruct H1.
              specialize (H1 flat_map_res x H).
              rewrite H0 in H1.
              unfold optionToList in H1.
              crush.
              *** crush.
          ** unfold applyReferenceOnPattern in H0.
             rewrite mtch in H0.
             inversion H0.
        * unfold applyReferenceOnPattern in H0.
          rewrite mtch in H0.
          inversion H0.
  Qed.

  Theorem tr_applyElementOnPattern_non_None :
     forall  (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (i:nat) (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
       applyElementOnPattern r ope tr sm sp i <> None <->
      (exists(oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope)),
          In oper (OutputPatternElement_getOutputElementReferences ope) /\
          applyReferenceOnPattern r ope oper tr sm sp i <> None).
  Proof.
  intros.
  split.
  {
    intro.
    specialize (option_res_dec (applyElementOnPattern r ope tr sm sp) i H).
    intro.
    destruct H0.
    unfold applyElementOnPattern in H.
    destruct (matchRuleOnPattern r sm sp) eqn:mtch.
        + destruct b.
          * Arguments optionList2List : simpl never.
            Arguments map : simpl never.
            destruct (flat_map
          (fun
             oper : OutputPatternElementReference (Rule_getInTypes r)
                      (Rule_getIteratorType r) (OutputPatternElement_getOutType ope) =>
           optionToList (applyReferenceOnPattern r ope oper tr sm sp i))
          (OutputPatternElement_getOutputElementReferences ope)) eqn:applyI_ca.
            - crush.
            - assert (In t (t::l)). { crush. }
              rewrite <- applyI_ca in H1.
                          apply in_flat_map in H1.
              destruct H1. destruct H1.
              exists x0.
              unfold optionToList in H2.
              destruct (applyReferenceOnPattern r ope x0 tr sm sp i).
              -- crush.
              -- crush.
          * crush.
        + crush.
  }
  {
    intros.
    destruct H.
    destruct H.
    unfold applyElementOnPattern.
    destruct (matchRuleOnPattern r sm sp) eqn: mtch.
     + destruct b eqn:b_ca.
       ++ destruct (flat_map
      (fun
         oper : OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r)
                  (OutputPatternElement_getOutType ope) =>
       optionToList (applyReferenceOnPattern r ope oper tr sm sp i))
      (OutputPatternElement_getOutputElementReferences ope)) eqn: apply_res.
          +++ specialize (in_flat_map_nil
                        (fun
                   oper : OutputPatternElementReference (Rule_getInTypes r)
                            (Rule_getIteratorType r) (OutputPatternElement_getOutType ope) =>
                 optionToList (applyReferenceOnPattern r ope oper tr sm sp i))
                        (OutputPatternElement_getOutputElementReferences ope)).
              intros.

              destruct H1.
              specialize (H1 apply_res x H).
               specialize (option_res_dec (applyReferenceOnPattern r ope x tr sm sp) i H0).
              intros.
              destruct H3.
              unfold optionToList in H1.
              rewrite H3 in H1.
              crush.
          +++ crush.
       ++ unfold applyReferenceOnPattern in H0.
          rewrite mtch in H0. crush.
    + unfold applyReferenceOnPattern in H0.
      rewrite mtch in H0. crush.
  }
  Qed.

  (** ** applyReferenceOnPattern **)

  Theorem tr_applyReferenceOnPattern_None_contra :
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r))
        (oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope)),
        length sp <> length (Rule_getInTypes r) ->
        applyReferenceOnPattern r ope oper tr sm sp i <> None -> False.
  Proof.
    intros.
    assert (exists (tl: TargetModelLink), applyReferenceOnPattern r ope oper tr sm sp i  = Some tl).
    { specialize (option_res_dec (applyReferenceOnPattern r ope oper tr sm sp)). intros.
      specialize (H1 i H0). destruct H1. exists x. crush. }
    destruct H1.
    unfold applyReferenceOnPattern in H1.
    destruct (matchRuleOnPattern r sm sp) eqn: match_res.
    - destruct b eqn:b_ca.
      -- destruct (nth_error (evalIterator r sm sp) i) eqn: eval_iter_ca.
         --- unfold evalOutputPatternElement in H1.
             destruct (evalFunction smm sm (Rule_getInTypes r)
         (denoteModelClass (OutputPatternElement_getOutType ope))
         (OutputPatternElement_getOutPatternElement ope r0) sp) eqn: eval_fun_ca.
             * unfold evalFunction in eval_fun_ca.
               specialize (evalFunctionFix_intypes_el_neq
                             SourceModelElement SourceModelLink SourceModelClass
                             SourceModelReference smm (Rule_getInTypes r)
                             (denoteModelClass (OutputPatternElement_getOutType ope))
                             (OutputPatternElement_getOutPatternElement ope r0 sm) sp).
               crush.
             * crush.
         --- crush.
      -- crush.
    - crush.
  Qed.

  Theorem tr_applyReferenceOnPattern_None :
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r))
        (oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope)),
        length sp <> length (Rule_getInTypes r) ->
        applyReferenceOnPattern r ope oper tr sm sp i = None.
  Proof.
    intros.
    destruct (applyReferenceOnPattern r ope oper tr sm sp i) eqn: Ha.
    - exfalso.
      apply (tr_applyReferenceOnPattern_None_contra tr sm r sp i ope oper).
      -- exact H.
      -- rewrite Ha. discriminate.
    - auto.
  Qed.


  Theorem tr_applyReferenceOnPattern_None_iterator_contra :
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
      (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r))
      (oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope)),
      i >= length (evalIterator r sm sp) ->
      applyReferenceOnPattern r ope oper tr sm sp i <> None -> False.
  Proof.
    intros.
    assert (exists (tl: TargetModelLink), applyReferenceOnPattern r ope oper tr sm sp i = Some tl).
    { specialize (option_res_dec (applyReferenceOnPattern r ope oper tr sm sp)). intros.
      specialize (H1 i H0). destruct H1. exists x. crush. }
    destruct H1.
    unfold applyReferenceOnPattern in H1.
    destruct (matchRuleOnPattern r sm sp) eqn: match_res.
    - destruct b eqn:b_ca.
      -- destruct (nth_error (evalIterator r sm sp) i) eqn: eval_iter_ca.
         --- specialize (nth_error_None (evalIterator r sm sp) i).
             crush.
         --- crush.
      -- crush.
    - crush.
  Qed.
  
  Theorem tr_applyReferenceOnPattern_None_iterator :
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
      (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r))
      (oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope)),
      i >= length (evalIterator r sm sp) ->
      applyReferenceOnPattern r ope oper tr sm sp i = None.
  Proof.
    intros.
    destruct (applyReferenceOnPattern r ope oper tr sm sp i) eqn: Ha.
    - exfalso.
      apply (tr_applyReferenceOnPattern_None_iterator_contra tr sm r sp i ope oper).
      -- exact H.
      -- rewrite Ha. discriminate.
    - auto.
  Qed.


  (** ** matchPattern **)

  Theorem tr_matchPattern_in :
    forall (tr: Transformation) (sm : SourceModel),
    forall (sp : list SourceModelElement)(r : Rule),
      In r (matchPattern tr sm sp) <->
      In r (Transformation_getRules tr) /\
      matchRuleOnPattern' r tr sm sp = return true.
  Proof.
    intros.
    split.
    - intros.
      unfold matchRuleOnPattern'.
      unfold matchPattern in H.
      apply filter_In in H.
      destruct H.
      destruct (matchRuleOnPattern r sm sp).
      + destruct b.
        * split. assumption. reflexivity.
        * inversion H0.
      + inversion H0.
    - intros.
      destruct H.
      unfold matchPattern.
      apply <- filter_In.
      split. assumption.
      unfold matchRuleOnPattern' in H0.
      rewrite H0.
      reflexivity.
  Qed.

  Theorem tr_matchPattern_None : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        length sp > maxArity tr ->
        matchPattern tr sm sp = nil.
  Proof.
    intros.
    unfold matchPattern.
    destruct (Transformation_getRules tr) eqn: rs.
    - crush.
    -
      apply filter_nil.
      exact r.
      intros.
      destruct (matchRuleOnPattern a sm sp) eqn: mtch.
      -- unfold matchRuleOnPattern in mtch.
         unfold evalGuard in mtch.
         unfold evalFunction in mtch.

         rewrite <- rs in H0.
         assert (length (Rule_getInTypes a) <> length sp).
         { specialize (tr_maxArity_in tr a H0). crush. }
         assert ( evalFunctionFix SourceModelElement SourceModelLink SourceModelClass SourceModelReference smm (Rule_getInTypes a) bool (Rule_getGuard a sm) sp = None).
         { apply (evalFunctionFix_intypes_el_neq).  crush. }
         crush.
      -- crush.
  Qed.

  (** ** matchRuleOnPattern **)

  Theorem tr_matchRuleOnPattern_eval :
    forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
      matchRuleOnPattern r sm sp =
      evalFunction smm sm (Rule_getInTypes r) bool (Rule_getGuard r) sp.
  Proof.
    crush.
  Qed.

  Theorem tr_matchRuleOnPattern_None :
      forall (tr: Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
        length sp <> length (Rule_getInTypes r) ->
        matchRuleOnPattern r sm sp = None.
  Proof.
    intros.
    unfold matchRuleOnPattern.
    unfold evalGuard.
    unfold evalFunction.
    apply evalFunctionFix_intypes_el_neq.
    crush.
  Qed.

  (** ** Resolve **)

  Theorem tr_resolveIter_some:
    forall (tr:MatchedTransformation) (sm : SourceModel) (name: string) (type: TargetModelClass)
      (sp: list SourceModelElement) (iter: nat) (x: denoteModelClass type),
      resolveIter tr sm name type sp iter = return x <->
       (exists (r: Rule) (e: TargetModelElement),
        (find (fun r:Rule => isMatchedRule sm r name sp iter)
              (Transformation_getRules (unmatchTransformation tr)) = Some r)
        /\ (instantiateRuleOnPatternIterName r sm sp iter name = Some e)
        /\ (toModelClass type e = Some x) ).
  Proof.
    intros.
    split.
    {
      intro.
      unfold resolveIter in H.
      destruct ( find (fun r : Rule => isMatchedRule sm r name sp iter)
                      (Transformation_getRules (unmatchTransformation tr))) eqn: find.
      - destruct (instantiateRuleOnPatternIterName r sm sp iter name) eqn: inst.
        -- exists r, t.
           split.
           auto.
           split.
           auto. auto.
        -- crush.
      - crush.
    }
    {
      intros.
      destruct H. destruct H. destruct H. destruct H0.
      unfold resolveIter.
      rewrite H.
      rewrite H0.
      rewrite H1.
      reflexivity.
    }
  Qed.

  Theorem tr_resolveIter_none:
    forall (tr:MatchedTransformation) (sm : SourceModel) (name: string) (type: TargetModelClass)
      (sp: list SourceModelElement) (iter: nat) (x: denoteModelClass type),
      resolveIter tr sm name type sp iter = None <->
       let matchedRule := (find (fun r:Rule => isMatchedRule sm r name sp iter)
                               (Transformation_getRules (unmatchTransformation tr))) in
       (matchedRule = None \/
        (exists (r: Rule),
          matchedRule = Some r /\
          instantiateRuleOnPatternIterName r sm sp iter name = None) \/
        (exists (r: Rule),
          matchedRule = Some r /\
          exists e, instantiateRuleOnPatternIterName r sm sp iter name = Some e /\
          toModelClass type e = None)

       ).
  Proof.
    intros.
    split.
    {intros. unfold resolveIter in H.
     destruct (find (fun r : Rule => isMatchedRule sm r name sp iter)
                    (Transformation_getRules (unmatchTransformation tr))) eqn: find.
     - destruct (instantiateRuleOnPatternIterName r sm sp iter name) eqn: inst.
       -- right. right. exists r. split.
          --- auto.
          --- exists t. auto.
       -- right. left. exists r. auto.
     - left. auto. }
    {
      intros.
      unfold resolveIter. destruct H.
      -  rewrite H. reflexivity.
      - destruct H.
        -- destruct H. destruct H. rewrite H. rewrite H0. reflexivity.
        --  destruct H. destruct H. destruct H0. destruct H0. rewrite H. rewrite H0. rewrite H1. reflexivity.
    }
  Qed.

  Theorem tr_resolve_unfold:
    forall (tr: MatchedTransformation) (sm: SourceModel) (name: string)
      (type: TargetModelClass) (sp: list SourceModelElement),
      resolve tr sm name type sp = resolveIter tr sm name type sp 0.
  Proof.
    crush.
  Qed.

  Theorem tr_resolveAllIter_in:
    forall (tr: MatchedTransformation) (sm: SourceModel) (name: string)
      (type: TargetModelClass) (sps: list(list SourceModelElement)) (iter: nat)
      (te: denoteModelClass type),
      (exists tes: list (denoteModelClass type),
          resolveAllIter tr sm name type sps iter = Some tes /\ In te tes) <->
      (exists (sp: list SourceModelElement),
          In sp sps /\
          resolveIter tr sm name type sp iter = Some te).
  Proof.
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
      destruct (resolveIter tr sm name type x0 iter).
      -- unfold optionToList in H1. crush.
      -- crush.
    - intros.
      destruct H. destruct H.
      remember (resolveAllIter tr sm name type sps iter) as tes1.
      destruct tes1 eqn: resolveAll.
      -- exists l.
         split. auto.
         unfold resolveAllIter in Heqtes1.
         inversion Heqtes1.
         apply in_flat_map.
         exists x. split. auto.
         destruct (resolveIter tr sm name type x iter).
         --- crush.
         --- crush.
      -- unfold resolveAllIter in Heqtes1.
         crush.
  Qed.

  Theorem tr_resolveAll_unfold:
    forall (tr: MatchedTransformation) (sm: SourceModel) (name: string)
      (type: TargetModelClass) (sps: list(list SourceModelElement)),
      resolveAll tr sm name type sps = resolveAllIter tr sm name type sps 0.
  Proof.
    crush.
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

      execute := execute;
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

End CoqTL.

Arguments MatchedTransformation: default implicits.

Arguments BuildTransformation
          [SourceModelElement] [SourceModelLink] [SourceModelClass] [SourceModelReference] _
          [TargetModelElement] [TargetModelLink] [TargetModelClass] [TargetModelReference] _.
Arguments BuildRule
          [SourceModelElement] [SourceModelLink] [SourceModelClass] [SourceModelReference] _
          [TargetModelElement] [TargetModelLink] [TargetModelClass] [TargetModelReference] _.
Arguments BuildOutputPatternElement
          [SourceModelElement] [SourceModelLink] [SourceModelClass] [SourceModelReference] _
          [TargetModelElement] [TargetModelLink] [TargetModelClass] [TargetModelReference] _
          _ [IterType].
Arguments BuildOutputPatternElementReference
          [SourceModelElement] [SourceModelLink] [SourceModelClass] [SourceModelReference] _
          [TargetModelElement] [TargetModelLink] [TargetModelClass] [TargetModelReference] _
          _ [IterType].

Arguments resolveIter: default implicits.
Arguments resolve: default implicits.
Arguments resolveAllIter: default implicits.
Arguments resolveAll: default implicits.

Arguments execute: default implicits.
Arguments matchPattern: default implicits.
Arguments matchRuleOnPattern': default implicits.
Arguments matchRuleOnPattern : default implicits.

Arguments instantiatePattern: default implicits.
Arguments instantiateRuleOnPattern: default implicits.
Arguments instantiateIterationOnPattern: default implicits.
Arguments instantiateElementOnPattern : default implicits.

Arguments evalGuard: default implicits.
Arguments evalIterator: default implicits.
Arguments evalOutputPatternElement: default implicits.

Arguments applyPattern: default implicits.
Arguments applyRuleOnPattern: default implicits.
Arguments applyIterationOnPattern: default implicits.

Arguments Transformation: default implicits.
Arguments Transformation_getRules: default implicits.
Arguments allTuples: default implicits.
Arguments maxArity: default implicits.

Arguments Rule: default implicits.
Arguments Rule_getInTypes: default implicits.
Arguments Rule_getIteratorType: default implicits.
Arguments Rule_getOutputPattern: default implicits.

Arguments OutputPatternElement: default implicits.
Arguments OutputPatternElement_getOutType: default implicits.
Arguments OutputPatternElement_getOutPatternElement: default implicits.
