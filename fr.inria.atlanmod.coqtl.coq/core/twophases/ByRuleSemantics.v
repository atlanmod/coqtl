Require Import String.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import Bool.
Require Import core.Syntax.
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
      fold_right prod_cons [nil] (allModelElementsOfTypes l sm).

    Definition allTuplesByRule (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
      (flat_map (fun (r:Rule) => allTuplesOfTypes (Rule_getInTypes r) sm) (Transformation_getRules tr)).

    Definition executeByRule (tr: Transformation) (sm : SourceModel) : TargetModel :=
      Build_Model
        (* elements *) (flat_map (instantiatePattern tr sm) (allTuplesByRule tr sm))
        (* links *) (flat_map (applyPattern tr sm) (allTuplesByRule tr sm)).

    Lemma InAllTuplesOfTypes : 
      forall (a : SourceModelElement) (sp: list SourceModelElement) (s: SourceModelClass) (l : list SourceModelClass) (sm: SourceModel),
      In (a :: sp) (allTuplesOfTypes (s :: l) sm)
      -> In (sp) (allTuplesOfTypes l sm).
    Proof.
      intros.
      unfold allTuplesOfTypes, prod_cons in H.
      simpl in H.
      apply in_flat_map in H. destruct H. destruct H.
      apply in_map_iff in H0.
      crush.
    Qed.

    Lemma allTuplesOfTypesInModel :
      forall (sp : list SourceModelElement) (l: list SourceModelClass) (sm : SourceModel),
      In sp (allTuplesOfTypes l sm) -> incl sp (allModelElements sm).
    Proof.
      intros.
      generalize dependent l.
      induction sp.
      + intros. 
        unfold incl. intros. inversion H0.
      + intros.
        destruct l.
        * simpl in H.
          destruct H. inversion H. contradiction.
        * apply incl_cons.
          2: {
            apply InAllTuplesOfTypes in H.
            apply IHsp in H.
            assumption.
          }
          1: {
            unfold allTuplesOfTypes in H.
            simpl in H.
            apply prod_cons_in with (s1:= (allModelElementsOfType s sm)) (se := a) in H.
            -- destruct H.
              ++ unfold allModelElementsOfType in H.
                apply filter_In in H.
                destruct H. assumption.
              ++ destruct H. destruct H.
                unfold allModelElementsOfTypes in H.
                unfold allModelElementsOfType in H.
                unfold prod_cons in  H.

                simpl in H.
          }
    Admitted.

    Lemma allTuplesByRuleInModel :
      forall (sp : list SourceModelElement) (tr: Transformation) (sm : SourceModel),
      In sp (allTuplesByRule tr sm) -> incl sp (allModelElements sm).
    Proof.
      intros.
      unfold allTuplesByRule in H.
      apply in_flat_map in H. destruct H. destruct H.
      apply allTuplesOfTypesInModel with (l:=(Rule_getInTypes x)).
      assumption.
    Qed.

    Lemma allTuplesOfTypesLength :
      forall (sp: list SourceModelElement) (l : list SourceModelClass) (sm : SourceModel),
      In sp (allTuplesOfTypes l sm) -> Datatypes.length sp = Datatypes.length l.
    Proof.
      intros.
      generalize dependent sp.
      induction l; intros.
      - simpl in H. destruct H. rewrite <- H. reflexivity. contradiction.
      - unfold allTuplesOfTypes in H. simpl in H.
        unfold prod_cons in H. 
        apply in_flat_map in H.
        destruct H. destruct H.
        apply in_map_iff in H0.
        destruct H0. destruct H0.
        unfold allTuplesOfTypes, prod_cons in IHl.
        apply IHl in H1.
        simpl.
        rewrite <- H1.
        rewrite <- H0.
        reflexivity.
    Qed.

    Lemma maxArityLength :
      forall (tr: Transformation) (r: Rule),
      In r (Transformation_getRules tr) -> 
      Datatypes.length (Rule_getInTypes r) <= maxArity tr.
    Proof.
      intros.
      unfold maxArity.
      apply max_list_upperBound.
      apply in_map_iff.
      exists (Rule_getInTypes r).
      split. reflexivity.
      apply in_map_iff.
      exists r.
      split. reflexivity.
      assumption.
    Qed.

    Lemma In_by_rule : 
      forall (sp: list SourceModelElement) (tr: Transformation) (sm: SourceModel),
      In sp (allTuplesByRule tr sm) -> In sp (allTuples tr sm).
    Proof.
      intros.
      apply allTuples_incl_length.
      * apply allTuplesByRuleInModel with (tr:=tr).
        assumption.
      * unfold allTuplesByRule in H.
        apply in_flat_map in H. destruct H. destruct H.
        apply allTuplesOfTypesLength in H0.
        rewrite H0.
        apply maxArityLength.
        assumption.
    Qed.

    Lemma In_by_rule_instantiate : 
      forall (sp: list SourceModelElement) (tr: Transformation) (sm: SourceModel),
      In sp (allTuples tr sm) /\ instantiatePattern tr sm sp <> nil -> In sp (allTuplesByRule tr sm).
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
