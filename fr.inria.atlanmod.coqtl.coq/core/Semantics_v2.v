(*
  CoqTL semantics v2

  Optimize CoqTL by filtering match result, see execute function for more detail.

  As a reminder, this increases performance because:

  1. For each pattern that is matched, the matchPattern function is called 3 times (instead of 2),
  2. For each pattern that is not matched, the matchPattern function is called 1 time (instead of 2).

  In a realistic case the patterns that are matched are much less than the patterns that are not matched.
*)

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

  (** ** Rule scheduling **)

  Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
    let matchedTuples := (filter (fun t => match (matchPattern tr sm t) with nil => false | _ => true end) (allTuples tr sm)) in
    Build_Model
      (* elements *) (flat_map (fun t => optionListToList (instantiatePattern tr sm t)) matchedTuples)
      (* links *) (flat_map (fun t => optionListToList (applyPattern tr sm t)) matchedTuples).

End Semantics.
