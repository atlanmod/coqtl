Require Import String.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import Bool.
Require Import core.Syntax.
Require Import Arith.
Require Import Semantics.

Scheme Equality for list.


Section ByRuleSemantics.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}.
  Context {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}.
  Context {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}.
  Context {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}.
  Context (SourceModel := Model SourceModelElement SourceModelLink).
  Context (TargetModel := Model TargetModelElement TargetModelLink).
  Context (Transformation := @Transformation SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink).

    Definition allModelElementsOfType (t: SourceModelClass) (sm: SourceModel) : list SourceModelElement :=
      filter (hasType t) (allModelElements sm).

    Definition allModelElementsOfTypes (l: list SourceModelClass) (sm: SourceModel): list (list SourceModelElement) :=
      map (fun t:SourceModelClass => allModelElementsOfType t sm) l.

    Definition allTuplesOfTypes (l: list SourceModelClass) (sm: SourceModel): list (list SourceModelElement) := 
      fold_right prod_cons [nil] (allModelElementsOfTypes l sm).

    Definition allTuplesByRule (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
      (flat_map (fun (r:Rule) => allTuplesOfTypes (Rule_getInTypes r) sm) (Transformation_getRules tr)).

    Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
      Build_Model
        (* elements *) (flat_map (instantiatePattern tr sm) (allTuplesByRule tr sm))
        (* links *) (flat_map (applyPattern tr sm) (allTuplesByRule tr sm)).

End ByRuleSemantics.
