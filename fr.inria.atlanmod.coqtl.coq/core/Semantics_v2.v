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
