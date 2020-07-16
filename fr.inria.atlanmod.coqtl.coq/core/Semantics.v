(**

 Implementation of CoqTL semantic functions

 **)

Require Import String.

Require Import core.utils.TopUtils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.
Require Import core.Syntax.

Section Semantics.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink)
          (Rule := Rule smm tmm)
          (Transformation := Transformation smm tmm)
          (MatchedTransformation := MatchedTransformation smm tmm).

  (** * Semantics *)

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

End Semantics.
