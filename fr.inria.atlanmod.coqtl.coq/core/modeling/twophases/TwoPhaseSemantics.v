Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import Semantics.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.
Require Import core.Expressions.
Scheme Equality for list.
 

Section TwoPhaseSemantics.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.  

(** * Apply **)

Definition applyLinkOnPatternTraces
            (oper: OutputPatternLink)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: list SourceModelElement) (iter: nat) (te: TargetModelElement) (tls: list TraceLink): option TargetModelLink :=
  evalOutputPatternLinkExpr sm sp te iter tls oper.

Definition applyElementOnPatternTraces
            (ope: OutputPatternElement)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: list SourceModelElement) (iter: nat) (tls: list TraceLink): list TargetModelLink :=
  flat_map (fun oper => 
    match (evalOutputPatternElementExpr sm sp iter ope) with 
    | Some l => optionToList (applyLinkOnPatternTraces oper tr sm sp iter l tls)
    | None => nil
    end) (OutputPatternElement_getOutputLinks ope).

Definition applyIterationOnPatternTraces (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (tls: list TraceLink): list TargetModelLink :=
  flat_map (fun o => applyElementOnPatternTraces o tr sm sp iter tls)
    (Rule_getOutputPatternElements r).

Definition applyRuleOnPatternTraces (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (tls: list TraceLink): list TargetModelLink :=
  flat_map (fun i => applyIterationOnPatternTraces r tr sm sp i tls)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition applyPatternTraces (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tls: list TraceLink): list TargetModelLink :=
  flat_map (fun r => applyRuleOnPatternTraces r tr sm sp tls) (matchPattern tr sm sp).

(** * Execute **)

Definition instantiateTraces (tr: Transformation) (sm : SourceModel) :=
  let tls := trace tr sm in
    ( map (TraceLink_getTargetElement) tls, tls ).

Definition applyTraces (tr: Transformation) (sm : SourceModel) (tls: list TraceLink): list TargetModelLink :=
  flat_map (fun sp => applyPatternTraces tr sm sp tls) (allTuples tr sm).

Definition executeTraces (tr: Transformation) (sm : SourceModel) : TargetModel :=
  let (elements, tls) := instantiateTraces tr sm in
  let links := applyTraces tr sm tls in
  Build_Model elements links.

End TwoPhaseSemantics.
