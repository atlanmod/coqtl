Require Import String.

Require Import core.utils.TopUtils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.

Section Semantics.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink)
          (Transformation := @Transformation SourceModelElement SourceModelLink TargetModelElement TargetModelLink).

  Definition evalGuardExpr (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
    (@Rule_getGuardExpr SourceModelElement SourceModelLink TargetModelElement TargetModelLink r) sm sp.

  Definition evalIteratorExpr (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) :
    list IteratorType :=
    (@Rule_getIteratorExpr SourceModelElement SourceModelLink TargetModelElement TargetModelLink r) sm sp.

  Definition evalOutputPatternElementExpr (sm: SourceModel) (sp: list SourceModelElement) (iter: IteratorType) (o: OutputPatternElement)
    : option TargetModelElement := 
    (@OutputPatternElement_getElementExpr SourceModelElement SourceModelLink TargetModelElement TargetModelLink o) iter sm sp.

  Definition evalOutputPatternLinkExpr
             (sm: SourceModel) (sp: list SourceModelElement) (oe: TargetModelElement) (iter: IteratorType) (tr: list TraceLink)
             (o: OutputPatternElementReference)
    : option TargetModelLink :=
  (@OutputPatternElementReference_getLinkExpr SourceModelElement SourceModelLink TargetModelElement TargetModelLink o) tr iter sm sp oe.

  (** * Instantiate **)

  Definition matchRuleOnPattern (r: Rule) (sm : SourceModel) (sp: list SourceModelElement) : bool :=
    match evalGuardExpr r sm sp with Some true => true | _ => false end.

  Definition matchPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list Rule :=
    filter (fun (r:Rule) => matchRuleOnPattern r sm sp) (Transformation_getRules tr).

  Definition instantiateElementOnPattern (r: Rule) (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat)
    : option TargetModelElement :=
    match (nth_error (evalIteratorExpr r sm sp) iter) with
    | Some i => evalOutputPatternElementExpr sm sp iter o
    | None => None
    end.

  Definition instantiateIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) :  list TargetModelElement :=
    flat_map (fun o => optionToList (instantiateElementOnPattern r o sm sp iter))
      (Rule_getOutputPatternElements r).

  Definition instantiateRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) :  list TargetModelElement :=
    flat_map (instantiateIterationOnPattern r sm sp)
      (indexes (length (evalIteratorExpr r sm sp))).

  Definition instantiatePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TargetModelElement :=
    flat_map (fun r => instantiateRuleOnPattern r sm sp) (matchPattern tr sm sp).

  Definition instantiateRuleOnPatternIterName (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (name: string): option (TargetModelElement) :=
    match (Rule_findOutputPatternElement r name) with
    | Some o =>  instantiateElementOnPattern r o sm sp iter
    | None => None
    end.

  (** * Trace **)

  Definition traceElementOnPattern (r: Rule) (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat)
    : option TraceLink :=
    match (instantiateElementOnPattern r o sm sp iter) with
    | Some e => Some (buildTraceLink (sp, iter, OutputPatternElement_getName o) e)
    | None => None
    end.

  Definition traceIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) :  list TraceLink :=
    flat_map (fun o => optionToList (traceElementOnPattern r o sm sp iter))
      (Rule_getOutputPatternElements r).

  Definition traceRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) :  list TraceLink :=
    flat_map (traceIterationOnPattern r sm sp)
      (indexes (length (evalIteratorExpr r sm sp))).

  Definition tracePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TraceLink :=
    flat_map (fun r => traceRuleOnPattern r sm sp) (matchPattern tr sm sp).

  Definition maxArity (tr: Transformation) : nat := 1.

  Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (allModelElements sm) (maxArity tr).

  Definition trace (tr: Transformation) (sm : SourceModel) : list TraceLink :=
    flat_map (tracePattern tr sm) (allTuples tr sm).  

  (* ** Resolve *)

  Definition resolveIter (tls: list TraceLink) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sp: list SourceModelElement)
             (iter : nat) : option (denoteModelClass type) :=
  let tl := find (fun tl: @TraceLink SourceModelElement TargetModelElement => 
    match tl with 
     buildTraceLink (sp', iter', name') _ => 
       (iter' =? iter) && (name =? name')%string (* TODO *)
    end) tls in
  match tl with
    | Some tl' => None (* TODO *)
    | None => None
  end.

 (*  Definition resolveIter (tr: list) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sp: list SourceModelElement)
             (iter : nat) : option (denoteModelClass type) :=
    let matchedRule := find (fun r:Rule => isMatchedRule sm r name sp iter)
                            (Transformation_getRules tr) in
    match matchedRule with
    | Some r => match instantiateRuleOnPatternIterName r sm sp iter name with
               | Some e => toModelClass type e
               | None => None
               end
    | None => None
    end.*)

  Definition resolve (tr: list TraceLink) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sp: list SourceModelElement) : option (denoteModelClass type) :=
    resolveIter tr sm name type sp 0.

  Definition resolveAllIter (tr: list TraceLink) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sps: list(list SourceModelElement)) (iter: nat)
    : option (list (denoteModelClass type)) :=
    Some (flat_map (fun l:(list SourceModelElement) => optionToList (resolveIter tr sm name type l iter)) sps).

  Definition resolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sps: list(list SourceModelElement)) : option (list (denoteModelClass type)) :=
    resolveAllIter tr sm name type sps 0.

  (** * Apply **)

  Definition applyReferenceOnPattern
             (r: Rule)
             (ope: OutputPatternElement)
             (oper: OutputPatternElementReference)
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) : option TargetModelLink :=
    match (nth_error (evalIteratorExpr r sm sp) iter) with
    | Some i =>
      match (evalOutputPatternElementExpr sm sp i ope) with
      | Some l => evalOutputPatternLinkExpr sm sp l i (trace tr sm) oper
      | None => None
      end
    | None => None
    end.

  Definition applyElementOnPattern
             (r: Rule)
             (ope: OutputPatternElement)
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) : list TargetModelLink :=
    flat_map (fun oper => optionToList (applyReferenceOnPattern r ope oper tr sm sp iter))
      (OutputPatternElement_getOutputElementReferences ope).

  Definition applyIterationOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : list TargetModelLink :=
    flat_map (fun o => applyElementOnPattern r o tr sm sp iter)
      (Rule_getOutputPatternElements r).

  Definition applyRuleOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement): list TargetModelLink :=
    flat_map (applyIterationOnPattern r tr sm sp)
      (indexes (length (evalIteratorExpr r sm sp))).

  Definition applyPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TargetModelLink :=
    flat_map (fun r => applyRuleOnPattern r tr sm sp) (matchPattern tr sm sp).

  (** * Execute **)

  Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
    Build_Model
      (* elements *) (flat_map (instantiatePattern tr sm) (allTuples tr sm))
      (* links *) (flat_map (applyPattern tr sm) (allTuples tr sm)).

End Semantics.
