Require Import String.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import Semantics.
Scheme Equality for list.


Section TwoPhaseSemantics.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink)
          (Transformation := @Transformation SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink).

  Definition evalExpr {A B:Type} (f: A -> B) (a: A) := f a. 

  Definition evalGuardExpr (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
    evalExpr (@Rule_getGuardExpr SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink r) sm sp.

  Definition evalIteratorExpr (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) :
    nat :=
    match (evalExpr (@Rule_getIteratorExpr SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink r) sm sp) with
    | Some n => n
    | _ => 0
    end.

  Definition evalOutputPatternElementExpr (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (o: OutputPatternElement)
    : option TargetModelElement := 
    (evalExpr (@OutputPatternElement_getElementExpr SourceModelElement SourceModelLink TargetModelElement TargetModelLink o) iter sm sp).

  Definition evalOutputPatternLinkExpr
             (sm: SourceModel) (sp: list SourceModelElement) (oe: TargetModelElement) (iter: nat) (tr: list TraceLink)
             (o: OutputPatternElementReference)
    : option TargetModelLink :=
    (evalExpr (@OutputPatternElementReference_getLinkExpr SourceModelElement SourceModelLink TargetModelElement TargetModelLink o) tr iter sm sp oe).

  (** * Instantiate **)

  Fixpoint checkTypes (ses: list SourceModelElement) (scs: list SourceModelClass) : bool :=
    match ses, scs with
    | se::ses', sc::scs' => 
      match (toModelClass sc se) with
      | Some c => checkTypes ses' scs'
      | _ => false
      end
    | nil, nil => true
    | _, _ => false
    end.

  Definition matchRuleOnPattern (r: Rule) (sm : SourceModel) (sp: list SourceModelElement) : bool :=
    if (checkTypes sp (Rule_getInTypes r)) then
      match evalGuardExpr r sm sp with Some true => true | _ => false end
    else false.

  Definition matchPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list Rule :=
    filter (fun (r:Rule) => matchRuleOnPattern r sm sp) (Transformation_getRules tr).

  Definition instantiateElementOnPattern (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat)
    : option TargetModelElement :=
    evalOutputPatternElementExpr sm sp iter o.

  Definition instantiateIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) :  list TargetModelElement :=
    flat_map (fun o => optionToList (instantiateElementOnPattern o sm sp iter))
      (Rule_getOutputPatternElements (SourceModelClass := SourceModelClass) r).

  Definition instantiateRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) :  list TargetModelElement :=
    flat_map (instantiateIterationOnPattern r sm sp)
      (indexes (evalIteratorExpr r sm sp)).

  Definition instantiatePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TargetModelElement :=
    flat_map (fun r => instantiateRuleOnPattern r sm sp) (matchPattern tr sm sp).

  Definition instantiateRuleOnPatternIterName (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (name: string): option (TargetModelElement) :=
    match (Rule_findOutputPatternElement (SourceModelClass := SourceModelClass) r name) with
    | Some o =>  instantiateElementOnPattern o sm sp iter
    | None => None
    end.

  (** * Trace **)

  Definition traceElementOnPattern (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat)
    : option TraceLink :=
    match (instantiateElementOnPattern o sm sp iter) with
    | Some e => Some (buildTraceLink (sp, iter, OutputPatternElement_getName o) e)
    | None => None
    end.

  Definition traceIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) :  list TraceLink :=
    flat_map (fun o => optionToList (traceElementOnPattern o sm sp iter))
      (Rule_getOutputPatternElements (SourceModelClass := SourceModelClass) r).

  Definition traceRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) :  list TraceLink :=
    flat_map (traceIterationOnPattern r sm sp)
      (indexes (evalIteratorExpr r sm sp)).

  Definition tracePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TraceLink :=
    flat_map (fun r => traceRuleOnPattern r sm sp) (matchPattern tr sm sp).

  Definition maxArity (tr: Transformation) : nat := 
    max (map (length (A:=SourceModelClass)) (map Rule_getInTypes (Transformation_getRules tr))).

  Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (allModelElements sm) (maxArity tr).

  Definition trace (tr: Transformation) (sm : SourceModel) : list TraceLink :=
    flat_map (tracePattern tr sm) (allTuples tr sm).  

  (* ** Resolve *)

  Definition resolveIter (tls: list TraceLink) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sp: list SourceModelElement)
             (iter : nat) : option (denoteModelClass type) :=
  let tl := find (fun tl: TraceLink => 
    (list_beq SourceModelElement beq_ModelElement (TraceLink_getSourcePattern tl) sp) &&
    ((TraceLink_getIterator tl) =? iter) &&
    ((TraceLink_getName tl) =? name)%string) tls in
  match tl with
    | Some tl' => toModelClass type (TraceLink_getTargetElement tl')
    | None => None
  end.

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
  
  Definition maybeResolve (tr: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sp: option (list SourceModelElement)) : option (denoteModelClass type) :=
    match sp with 
    | Some sp' => resolve tr sm name type sp'
    | None => None
    end.

  Definition maybeResolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sp: option (list (list SourceModelElement))) : option (list (denoteModelClass type)) :=
    match sp with 
    | Some sp' => resolveAll tr sm name type sp'
    | None => None
    end.

  (** * Apply **)

  Definition applyReferenceOnPatternTraces
             (oper: OutputPatternElementReference)
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) (te: TargetModelElement) (tls: list TraceLink): option TargetModelLink :=
    evalOutputPatternLinkExpr sm sp te iter tls oper.

  Definition applyReferenceOnPattern
    (oper: OutputPatternElementReference)
    (tr: Transformation)
    (sm: SourceModel)
    (sp: list SourceModelElement) (iter: nat) (te: TargetModelElement) : option TargetModelLink :=
    evalOutputPatternLinkExpr sm sp te iter (trace tr sm) oper.

  Definition applyElementOnPatternTraces
             (ope: OutputPatternElement)
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) (tls: list TraceLink): list TargetModelLink :=
    flat_map (fun oper => 
      match (evalOutputPatternElementExpr sm sp iter ope) with 
      | Some l => optionToList (applyReferenceOnPatternTraces oper tr sm sp iter l tls)
      | None => nil
      end) (OutputPatternElement_getOutputElementReferences ope).

  Definition applyElementOnPattern
             (ope: OutputPatternElement)
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) : list TargetModelLink :=
    flat_map (fun oper => 
      match (evalOutputPatternElementExpr sm sp iter ope) with 
      | Some l => optionToList (applyReferenceOnPattern oper tr sm sp iter l)
      | None => nil
      end) (OutputPatternElement_getOutputElementReferences ope).

  Definition applyIterationOnPatternTraces (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (tls: list TraceLink): list TargetModelLink :=
    flat_map (fun o => applyElementOnPatternTraces o tr sm sp iter tls)
      (Rule_getOutputPatternElements (SourceModelClass := SourceModelClass) r).

  Definition applyIterationOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : list TargetModelLink :=
    flat_map (fun o => applyElementOnPattern o tr sm sp iter)
      (Rule_getOutputPatternElements (SourceModelClass := SourceModelClass) r).

  Definition applyRuleOnPatternTraces (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (tls: list (@TraceLink SourceModelElement TargetModelElement)): list TargetModelLink :=
    flat_map (fun i => applyIterationOnPatternTraces r tr sm sp i tls)
      (indexes (evalIteratorExpr r sm sp)).
  
  Definition applyRuleOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement): list TargetModelLink :=
    flat_map (applyIterationOnPattern r tr sm sp)
      (indexes (evalIteratorExpr r sm sp)).

  Definition applyPatternTraces (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tls: list TraceLink): list TargetModelLink :=
    flat_map (fun r => applyRuleOnPatternTraces r tr sm sp tls) (matchPattern tr sm sp).

  Definition applyPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TargetModelLink :=
    flat_map (fun r => applyRuleOnPattern r tr sm sp) (matchPattern tr sm sp).

  (** * Execute **)

  Definition instantiateTraces (tr: Transformation) (sm : SourceModel) :=
    let tls := trace tr sm in
      ( map (TraceLink_getTargetElement) tls, tls ).

  Definition instantiate (tr: Transformation) (sm : SourceModel) : list TargetModelElement :=
    flat_map (instantiatePattern tr sm) (allTuples tr sm).

  Definition applyTraces (tr: Transformation) (sm : SourceModel) (tls: list (@TraceLink SourceModelElement TargetModelElement)): list TargetModelLink :=
    flat_map (fun sp => applyPatternTraces tr sm sp tls) (allTuples tr sm).
  
  Definition apply (tr: Transformation) (sm : SourceModel) : list TargetModelLink :=
    flat_map (applyPattern tr sm) (allTuples tr sm).

  Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
    let (elements, tls) := instantiateTraces tr sm in
    let links := applyTraces tr sm tls in
    Build_Model elements links.
  
  Definition execute' (tr: Transformation) (sm : SourceModel) : TargetModel :=
    Build_Model
      (* elements *) (flat_map (instantiatePattern tr sm) (allTuples tr sm))
      (* links *) (flat_map (applyPattern tr sm) (allTuples tr sm)).





End TwoPhaseSemantics.
