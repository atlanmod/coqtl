Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.test.iSyntax.
Require Import core.EqDec. 
Require Import Bool.
Require Import Arith.
Require Import TransformationConfiguration.
Require Import core.test.iExpressions.
Scheme Equality for list.


Section Semantics.

Context {tc: TransformationConfiguration}.

(** * Instantiate **)

Definition matchRuleOnPattern (r: Rule) (sm : SourceModel) (sp: list SourceModelElement) : bool :=
  match evalGuardExpr r sm sp with Some true => true | _ => false end.

Definition matchPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list Rule :=
  filter (fun (r:Rule) => matchRuleOnPattern r sm sp) (Transformation_getRules tr).

Definition instantiateElementOnPattern (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat)
  : option TargetModelElement :=
  evalOutputPatternElementExpr sm sp iter o.

Definition instantiateIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) :  list TargetModelElement :=
  flat_map (fun o => optionToList (instantiateElementOnPattern o sm sp iter))
    (Rule_getOutputPatternElements r).

Definition instantiateRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) :  list TargetModelElement :=
  flat_map (instantiateIterationOnPattern r sm sp)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition instantiatePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TargetModelElement :=
  flat_map (fun r => instantiateRuleOnPattern r sm sp) (matchPattern tr sm sp).

Definition instantiateRuleOnPatternIterName (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (name: string): option (TargetModelElement) :=
  match (Rule_findOutputPatternElement r name) with
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
    (Rule_getOutputPatternElements r).

Definition traceRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) :  list TraceLink :=
  flat_map (traceIterationOnPattern r sm sp)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition tracePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TraceLink :=
  flat_map (fun r => traceRuleOnPattern r sm sp) (matchPattern tr sm sp).

Definition maxArity (tr: Transformation) : nat := Transformation_getArity tr.

Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
  tuples_up_to_n (allModelElements sm) (maxArity tr).

Definition trace (tr: Transformation) (sm : SourceModel) : list TraceLink :=
  flat_map (tracePattern tr sm) (allTuples tr sm).  


(* Fixpoint contains {A:Type} (eq_dec: A->A->bool) (x: A) (l: list A) : bool :=
  match l with
  | nil => false
  | h :: tl => (if (eq_dec h x) then true else (contains eq_dec x tl))
  end.

Fixpoint unique {A:Type} (eq_dec: A->A->bool) (l: list A) :=
  match l with
   | hd :: tl => if contains eq_dec hd tl then unique eq_dec tl else hd :: unique eq_dec tl
   | nil => nil
  end. 

Definition eqb_trace (a b: TraceLink ) : bool :=
  match a, b with
   (buildTraceLink (sp1, it1, n1) te1),  (buildTraceLink (sp2, it2, n2) te2) =>
      (list_beq SourceModelElement SourceElement_eqb sp1 sp2) &&
      (it1 =? it2) &&
      (n1 =? n2)%string
  end. *)

Definition resolveIter (tls: list TraceLink) (sm: SourceModel) (name: string)
            (sp: list SourceModelElement)
            (iter : nat) : option TargetModelElement :=
let tlsf := filter (fun tl: TraceLink => 
  (list_beq SourceModelElement SourceElement_eqb (TraceLink_getSourcePattern tl) sp) &&
  ((TraceLink_getIterator tl) =? iter) &&
  ((TraceLink_getName tl) =? name)%string) tls in
    match length tlsf with
    | 1 => tr <- nth_error tlsf 0; return TraceLink_getTargetElement tr
    | _ => None
    end.

Definition resolve (tr: list TraceLink) (sm: SourceModel) (name: string)
  (sp: list SourceModelElement) : option TargetModelElement :=
  resolveIter tr sm name sp 0.

(* Definition resolveAllIter (tr: list TraceLink) (sm: SourceModel) (name: string)
  (sps: list(list SourceModelElement)) (iter: nat)
  : option (list TargetModelElement) :=
  Some (flat_map (fun l:(list SourceModelElement) => optionToList (resolveIter tr sm name l iter)) sps).

Definition resolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
  (sps: list(list SourceModelElement)) : option (list TargetModelElement) :=
  resolveAllIter tr sm name sps 0.

Definition maybeResolve (tr: list TraceLink) (sm: SourceModel) (name: string)
  (sp: option (list SourceModelElement)) : option TargetModelElement :=
  match sp with 
  | Some sp' => resolve tr sm name sp'
  | None => None
  end.

Definition maybeResolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
  (sp: option (list (list SourceModelElement))) : option (list TargetModelElement) :=
  match sp with 
  | Some sp' => resolveAll tr sm name sp'
  | None => None
  end. *)

(** * Apply **)






Definition applyElementOnPattern
            (ope: OutputPatternElement)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: list SourceModelElement) (iter: nat) : list TargetModelLink :=
  match (evalOutputPatternElementExpr sm sp iter ope) with 
  | Some l => optionListToList (evalOutputPatternLinkExpr sm sp l (resolveIter (trace tr sm)) iter ope)
  | None => nil
  end.

Definition applyIterationOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : list TargetModelLink :=
  flat_map (fun o => applyElementOnPattern o tr sm sp iter)
    (Rule_getOutputPatternElements r).

Definition applyRuleOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement): list TargetModelLink :=
  flat_map (applyIterationOnPattern r tr sm sp)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition applyPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TargetModelLink :=
  flat_map (fun r => applyRuleOnPattern r tr sm sp) (matchPattern tr sm sp).

(** * Execute **)

Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  Build_Model
    (* elements *) (flat_map (instantiatePattern tr sm) (allTuples tr sm))
    (* links *) (flat_map (applyPattern tr sm) (allTuples tr sm)).

End Semantics.
