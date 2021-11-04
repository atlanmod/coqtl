Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import Expressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ModelingTransformationConfiguration.
Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.Parser.

Section Parallelization.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}. 

Definition allModelElementsOfType   
  (t: SourceModelClass) (sm: SourceModel) : list SourceModelElement :=
  filter (hasType t) (allModelElements sm).

Definition allModelElementsOfTypes 
  (l: list SourceModelClass) (sm: SourceModel): list (list SourceModelElement) :=
  map (fun t:SourceModelClass => allModelElementsOfType  t sm) l.

Definition allTuplesOfTypes
  (l: list SourceModelClass) (sm: SourceModel): list (list SourceModelElement) := 
  fold_right prod_cons [nil] (allModelElementsOfTypes  l sm).

Definition allTuplesByRule (tr: ConcreteTransformation) (sm : SourceModel) :list (list SourceModelElement) :=
  (flat_map (fun (r:ConcreteRule) => allTuplesOfTypes (ConcreteRule_getInTypes r) sm) (ConcreteTransformation_getConcreteRules tr)).


Definition execute (tr: ConcreteTransformation) (sm : SourceModel) : TargetModel :=
  Build_Model
    (* elements *) (flat_map (instantiatePattern (parse tr) sm) (allTuplesByRule tr sm))
    (* links *) (flat_map (applyPattern (parse tr) sm) (allTuplesByRule tr sm)).

Theorem Parallelization_instantiate:
forall (tc: TransformationConfiguration) (tr: ConcreteTransformation) (sm: SourceModel) l l1 l2,
 l = l1 ++ l2 ->
  (flat_map (instantiatePattern (parse tr) sm) l) = 
    flat_map (instantiatePattern (parse tr) sm) l1 ++ flat_map (instantiatePattern (parse tr) sm) l2.
Proof.
 intros.
 rewrite H.
 apply flat_map_app.
Qed.


Theorem Parallelization_apply:
forall (tc: TransformationConfiguration) (tr: ConcreteTransformation) (sm: SourceModel) l l1 l2,
 l = l1 ++ l2 ->
  flat_map (applyPattern (parse tr) sm) l = 
    flat_map (applyPattern (parse tr) sm) l1 ++ flat_map (applyPattern (parse tr) sm) l2.
Proof.
 intros.
 rewrite H.
 apply flat_map_app.
Qed.






(* 




Lemma allModelElementsOfTypeInModel :
  forall (c: SourceModelClass) (sm : SourceModel),
  incl (allModelElementsOfType c sm) (allModelElements sm).
Proof.
  unfold allModelElementsOfType, incl.
  intros.
  apply filter_In in H.
  destruct H.
  assumption.
Qed.

Lemma allModelElementsOfTypesInModel :
  forall (sp : list SourceModelElement) (l: list SourceModelClass) (sm : SourceModel),
  In sp (allModelElementsOfTypes l sm) -> incl sp (allModelElements sm).
Proof.
  intros.
  unfold allModelElementsOfTypes in H.
  apply in_map_iff in H. destruct H. destruct H.
  rewrite <- H.
  apply allModelElementsOfTypeInModel.
Qed.

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
  unfold allTuplesOfTypes in H.
  generalize dependent sp.
  induction l; intros.
  - simpl in H. destruct H.
    + rewrite <- H. unfold incl. intros. inversion H0.
    + contradiction.
  - destruct sp.
    + unfold incl. intros. inversion H0.
    + simpl in H.
      unfold prod_cons in H.
      apply in_flat_map in H. repeat destruct H.
      apply in_map_iff in H0. repeat destruct H0.
      unfold incl.
      intros.
      simpl in H0.
      destruct H0.
      * pose allModelElementsOfTypeInModel.
        unfold incl in i.
        apply i with (c:=a).
        rewrite <- H0.
        assumption.
      * unfold incl in IHl.
        simpl in IHl.
        generalize H0.
        apply IHl.
        assumption.
Qed.

Lemma allTuplesByRuleInModel :
  forall (sp : list SourceModelElement) (tr: ConcreteTransformation) (sm : SourceModel),
  In sp (allTuplesByRule tr sm) -> incl sp (allModelElements sm).
Proof.
  intros.
  unfold allTuplesByRule in H.
  apply in_flat_map in H. destruct H. destruct H.
  apply allTuplesOfTypesInModel with (l:=(ConcreteRule_getInTypes x)).
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
  forall (tr: ConcreteTransformation) (r: ConcreteRule),
  In r (ConcreteTransformation_getConcreteRules tr) -> 
  Datatypes.length (ConcreteRule_getInTypes r) <= maxArity (parse tr).
Proof.
  intros.
  unfold maxArity.
  apply max_list_upperBound.
  apply in_map_iff.
  exists (ConcreteRule_getInTypes r).
  split. reflexivity.
  apply in_map_iff.
  exists r.
  split. reflexivity.
  assumption.
Qed.

Lemma In_by_rule : 
  forall (sp: list SourceModelElement) (tr: ConcreteTransformation) (sm: SourceModel),
  In sp (allTuplesByRule tr sm) -> In sp (allTuples (parse tr) sm).
Proof.
  intros.
Admitted.
(*   apply allTuples_incl_length.
  * apply allTuplesByRuleInModel with (tr:=tr).
    assumption.
  * unfold allTuplesByRule in H.
    apply in_flat_map in H. destruct H. destruct H.
    apply allTuplesOfTypesLength in H0.
    rewrite H0.
    apply maxArityLength.
    assumption.
Qed. *)

Lemma In_allTuplesOfTypes_inv :
  forall (a: SourceModelElement) (sp: list SourceModelElement) 
  (s: SourceModelClass) (l: list SourceModelClass)
  (sm: SourceModel),
  hasType s a = true
  -> In sp (allTuplesOfTypes l sm) 
  -> In a (allModelElements sm)
  -> In (a :: sp) (allTuplesOfTypes (s :: l) sm).
Proof.
  intros.
  unfold allTuplesOfTypes.
  simpl.
  unfold allTuplesOfTypes in H0.
  apply prod_cons_in_inv with (se:=a) (ss:=sp).
  - unfold allModelElementsOfType, hasType.
    apply filter_In.
    split.
    + assumption.
    + apply H.
  - assumption.
Qed.

(* Lemma In_by_rule_match :
  forall (sp: list SourceModelElement) (tr: Transformation) (sm: SourceModel) (r: ConcreteRule),
  In sp (allTuples tr sm) /\ hd_error (matchPattern tr sm sp) = return r    
  -> In sp (allTuplesOfTypes (ConcreteRule_getInTypes r) sm).
Proof.
  intros.
  destruct H.
  apply allTuples_incl in H.
  apply hd_error_In in H0.
  unfold matchPattern in H0.
  apply filter_In in H0.
  destruct H0.
  unfold matchRuleOnPattern in H1.
  destruct (checkTypes sp (Rule_getInTypes r)) eqn:dct.
  2: { inversion H1. }
  1: {
    remember (Rule_getInTypes r) as l.
    clear H1 H0 Heql.
    generalize dependent l.
    induction sp; intros.
    - simpl in dct.
      destruct l.
      + simpl.
        left.
        reflexivity.
      + inversion dct.
    - destruct l.
      + simpl in dct. inversion dct.
      + simpl in dct.
        destruct (toModelClass s a) eqn:dtmc.
        2: { inversion dct. }
        1: {
          apply In_allTuplesOfTypes_inv.
          - unfold hasType.
            rewrite dtmc.
            reflexivity.
          - apply IHsp.
            + apply incl_cons_inv in H.
              destruct H.
              assumption.
            + assumption.
          - apply incl_cons_inv in H.
            destruct H.
            assumption.
        }
  }
Qed. *)

(* Lemma In_by_rule_instantiate : 
  forall (sp: list SourceModelElement) (tr: Transformation) (sm: SourceModel),
  In sp (allTuples tr sm) /\ instantiatePattern tr sm sp <> nil -> In sp (allTuplesByRule tr sm).
Proof.
  intros.
  destruct H.
  unfold allTuplesByRule.
  apply in_flat_map.
  destruct (hd_error (matchPattern tr sm sp)) eqn:dst.
  2: {
    destruct (matchPattern tr sm sp) eqn:hdst.
    - unfold instantiatePattern in H0.
      rewrite hdst in H0.
      simpl in H0. 
      unfold not in H0.
      contradiction H0.
      reflexivity.
    - inversion dst. 
  }
  1: {
    exists r. 
    split.
    + apply hd_error_In in dst.
      apply tr_matchPattern_in in dst.
      destruct dst.
      assumption.
    + apply In_by_rule_match with (tr:=tr).
      split.
      assumption.
      assumption.
  }
Qed. *)

(* Lemma In_by_rule_apply : 
forall (sp: list SourceModelElement) (tr: Transformation) (sm: SourceModel),
In sp (allTuples tr sm) /\ applyPattern tr sm sp <> nil -> In sp (allTuplesByRule tr sm).
Proof.
  intros.
  destruct H.
  unfold allTuplesByRule.
  apply in_flat_map.
  destruct (hd_error (matchPattern tr sm sp)) eqn:dst.
  2: {
    destruct (matchPattern tr sm sp) eqn:hdst.
    - unfold applyPattern in H0.
      rewrite hdst in H0.
      simpl in H0. 
      unfold not in H0.
      contradiction H0.
      reflexivity.
    - inversion dst. 
  }
  1: {
    exists r. 
    split.
    + apply hd_error_In in dst.
      apply tr_matchPattern_in in dst.
      destruct dst.
      assumption.
    + apply In_by_rule_match with (tr:=tr).
      split.
      assumption.
      assumption.
  }
Qed. *)

Theorem tr_execute_in_elements :
  forall (tr: ConcreteTransformation) (sm : SourceModel) (te : TargetModelElement),
  In te (allModelElements (execute tr sm)) <->
  (exists (sp : list SourceModelElement),
      In sp (allTuples (parse tr) sm) /\
      In te (instantiatePattern (parse tr) sm sp)).
Proof.
  intros.
  unfold execute. simpl.
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
    In tl (allModelLinks (execute tr sm)) <->
    (exists (sp : list SourceModelElement),
        In sp (allTuples tr sm) /\
        In tl (applyPattern tr sm sp)).
Proof.
  intros.
  unfold execute. simpl.
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
    + apply In_by_rule_apply.
      split.
      - assumption.
      - unfold not. intros.
        rewrite H1 in H0. contradiction.
    + assumption.
Qed.

Theorem tr_execute_in :
  forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement) (tl : TargetModelLink),
    (In te (allModelElements (execute tr sm)) <-> In te (allModelElements (Semantics.execute tr sm)))
    /\ (In tl (allModelLinks (execute tr sm)) <-> In tl (allModelLinks (Semantics.execute tr sm))).
Proof.
  intros.
  split.
  - rewrite tr_execute_in_elements.
    rewrite Certification.tr_execute_in_elements.
    split. trivial. trivial.
  - rewrite tr_execute_in_links.
    rewrite Certification.tr_execute_in_links.
    split. trivial. trivial.
Qed.  *)


End Parallelization.