Require Import String.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import Semantics.
Require Import Certification.

Scheme Equality for list.


Section ByRuleSemantics.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink)
          (Transformation := @Transformation SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink).

    Definition hasType (t: SourceModelClass) (e: SourceModelElement) : bool :=
        match (toModelClass t e) with
        | Some e' => true
        | _ => false
        end.

    Definition allModelElementsOfType (t: SourceModelClass) (sm: SourceModel) : list SourceModelElement :=
      filter (hasType t) (allModelElements sm).

    Definition allModelElementsOfTypes (l: list SourceModelClass) (sm: SourceModel): list (list SourceModelElement) :=
      map (fun t:SourceModelClass => allModelElementsOfType t sm) l.

    Definition allTuplesOfTypes (l: list SourceModelClass) (sm: SourceModel): list (list SourceModelElement) := 
      fold_right prod_cons ([nil]) (allModelElementsOfTypes l sm) .

    Definition allTuplesByRule (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
      flat_map (fun (r:Rule) => allTuplesOfTypes (Rule_getInTypes r) sm) (Transformation_getRules tr).

    Definition executeByRule (tr: Transformation) (sm : SourceModel) : TargetModel :=
      Build_Model
        (* elements *) (flat_map (instantiatePattern tr sm) (allTuplesByRule tr sm))
        (* links *) (flat_map (applyPattern tr sm) (allTuplesByRule tr sm)).

    Lemma In_by_rule : 
      forall (sp: list SourceModelElement) (tr: Transformation) (sm: SourceModel),
      In sp (allTuplesByRule tr sm) -> In sp (allTuples tr sm).
    Proof.
      intros.
      unfold allTuplesByRule in H.
      apply in_flat_map in H.
      destruct H. destruct H.
      apply allTuples_incl_length.
      - unfold incl.
        intros.
        unfold allTuplesOfTypes, prod_cons, allModelElementsOfTypes, allModelElementsOfType in H0.
        Search flat_map.
        Admitted.

    Lemma In_by_rule_instantiate : 
      forall (sp: list SourceModelElement) (tr: Transformation) (sm: SourceModel),
      In sp (allTuples tr sm) /\  instantiatePattern tr sm sp <> nil -> In sp (allTuplesByRule tr sm).
    Admitted.

    Theorem tr_execute_in_elements :
      forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
      In te (allModelElements (executeByRule tr sm)) <->
      (exists (sp : list SourceModelElement),
          In sp (allTuples tr sm) /\
          In te (instantiatePattern tr sm sp)).
    Proof.
      intros.
      unfold executeByRule. simpl.
      rewrite in_flat_map.
      split.
      * intros.
        destruct H. destruct H.
        exists x.
        split.
        + apply In_by_rule. assumption.
        + assumption.
      * intros.
        destruct H. destruct H.
        exists x.
        split.
        + apply In_by_rule_instantiate.
          split.
          - assumption.
          - unfold not. intros. rewrite H1 in H0. contradiction.
        + assumption.
    Qed.

    Theorem tr_execute_in_links :
      forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
        In tl (allModelLinks (executeByRule tr sm)) <->
        (exists (sp : list SourceModelElement),
            In sp (allTuples tr sm) /\
            In tl (applyPattern tr sm sp)).
    Admitted.

End ByRuleSemantics.
