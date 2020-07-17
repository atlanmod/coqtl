(**

 Improved Implementation of CoqTL semantic functions over [118eefa]

 This implementation refers to commit:
 
 [c7f6526](https://github.com/atlanmod/CoqTL/commit/c7f6526)

 It optimizes [118eefa] by memorization:

  1. reduce recomputation of matchedTuples

 **)

Require Import String.

Require Import core.utils.TopUtils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.
Require Import core.Syntax.

Require Export core.Semantics.

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

  (** ** Rule application **)

  (* actual implementation using precomputed match *)
  Definition instantiatePattern' (tr: Transformation) (sm : SourceModel) (spr: ((list SourceModelElement) * (list Rule))): option (list TargetModelElement) :=
    match spr with
    | (_, nil) => None
    | (sp, l) => match  (flat_map (fun r => optionListToList (instantiateRuleOnPattern r sm sp)) l) with
          | nil => None
          | l => Some l
           end
    end.

  (* adapter for the typeclass *)
  Definition instantiatePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    instantiatePattern' tr sm (sp, (matchPattern tr sm sp)).

  (* actual implementation using precomputed match *)
  Definition applyPattern' (tr: Transformation) (sm : SourceModel) (spr: ((list SourceModelElement) * (list Rule))) : option (list TargetModelLink) :=
    match spr with
    | (_, nil) => None
    | (sp, l) => match  (flat_map (fun r => optionListToList (applyRuleOnPattern r tr sm sp)) l) with
          | nil => None
          | l => Some l
           end
    end.

  (* adapter for the typeclass *)
  Definition applyPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelLink) :=
    applyPattern' tr sm (sp, matchPattern tr sm sp).

  (** ** Rule scheduling **)

  Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
    let matchedTuples :=  map (fun t => (t, (matchPattern tr sm t))) (allTuples tr sm) in
    Build_Model
      (* elements *) (flat_map (fun t => optionListToList (instantiatePattern' tr sm t)) matchedTuples)
      (* links *) (flat_map (fun t => optionListToList (applyPattern' tr sm t)) matchedTuples).

End Semantics.
