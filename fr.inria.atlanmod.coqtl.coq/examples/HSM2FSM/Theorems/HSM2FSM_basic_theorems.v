Require Import String.
Require Import Coq.Logic.Eqdep_dec.

Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.Metamodel.
Require Import core.Model.


Require Import examples.HSM2FSM.HSM.
Require Import examples.HSM2FSM.HSM2FSM.

Theorem All_sm_match :
  forall (cm : HSMModel) (s : StateMachine),
  exists (r : Rule HSMMetamodel HSMMetamodel),
    matchPattern HSM2FSM cm [HSMMetamodel_toEObject s] = [r].
Proof.
  intros.
  eexists _.
  reflexivity.
Qed.

Theorem All_sm_match' :
  forall (cm : HSMModel) (s : StateMachine),
  exists (r : Rule HSMMetamodel HSMMetamodel),
    In r (matchPattern HSM2FSM cm [HSMMetamodel_toEObject s]).
Proof.
  intros.
  eexists.
  apply tr_matchPattern_in.
  split.
  - left. reflexivity.
  - (* rewrite tr_matchRuleOnPattern. *)
    unfold matchRuleOnPattern'.
    unfold matchRuleOnPattern.
    unfold evalGuard.
    unfold Expressions.evalFunction. simpl. reflexivity.
Qed.

Theorem All_sm_instantiate :
  forall (cm : HSMModel) (s : StateMachine),
  exists (t : StateMachine),
    instantiatePattern HSM2FSM cm [HSMMetamodel_toEObject s] = Some [HSMMetamodel_toEObject t].
Proof.
  intros.
  eexists _.
  reflexivity.
Qed.

Theorem All_sm_instantiate' :
  forall (cm : HSMModel) (s: StateMachine),
  exists (t: StateMachine) tp,
    instantiatePattern HSM2FSM cm [HSMMetamodel_toEObject s] = Some tp /\
    In (HSMMetamodel_toEObject t) tp.
Proof.
  intros.
  eexists.
  apply tr_instantiatePattern_in.
  do 2 eexists.
  repeat split.
  - left. reflexivity.
  - reflexivity.
  - left. reflexivity.
Qed.

Theorem RegularState_instantiate :
  forall (cm : HSMModel) (s: AbstractState),
        (AbstractState_instanceOfEClass RegularStateEClass s) = true ->
    exists (t: AbstractState),
      instantiatePattern HSM2FSM cm [HSMMetamodel_toEObject s] = Some [HSMMetamodel_toEObject t].
Proof.
  intros.
  eexists _.
  unfold instantiatePattern. unfold matchPattern. simpl.
  rewrite H. simpl.
  unfold instantiateRuleOnPattern. simpl.
  rewrite H. simpl.
  unfold instantiateIterationOnPattern. simpl.
  rewrite H. simpl.
  unfold instantiateElementOnPattern. simpl.
  rewrite H. simpl.
  destruct ((andb (AbstractState_instanceOfEClass InitialStateEClass s)
                  (isNone CompositeState (AbstractState_getCompositeState s cm)))) eqn: is2is.
  + assert ((AbstractState_instanceOfEClass InitialStateEClass s) = true). 
       { symmetry in is2is. apply Bool.andb_true_eq in is2is. crush. }
       assert (RegularStateEClass = InitialStateEClass).
       { apply HSM_AbstractState_f_equal with (a:=s); crush. }
       crush.
  + destruct ((andb (AbstractState_instanceOfEClass InitialStateEClass s)
                    (negb (isNone CompositeState (AbstractState_getCompositeState s cm))))) eqn: is2rs.
    ++ assert ((AbstractState_instanceOfEClass InitialStateEClass s) = true). 
       { symmetry in is2rs. apply Bool.andb_true_eq in is2rs. crush. }
       assert (RegularStateEClass = InitialStateEClass).
       { apply HSM_AbstractState_f_equal with (a:=s); crush. }
       crush.
    ++ simpl. reflexivity.
Qed.

Theorem RegularState_instantiate' :
  forall (cm : HSMModel) (s: AbstractState),
        (AbstractState_instanceOfEClass RegularStateEClass s) = true ->
    exists (t: AbstractState) tp,
      instantiatePattern HSM2FSM cm [HSMMetamodel_toEObject s] = Some tp /\
      In (HSMMetamodel_toEObject t) tp.
Proof.
  intros.
  eexists.
  apply tr_instantiatePattern_in.
  do 2 eexists.
  repeat split.
  - apply tr_matchPattern_in.
    split.
    + right. left. reflexivity.
    + (* rewrite tr_matchRuleOnPattern. *)
      unfold matchRuleOnPattern'. unfold matchRuleOnPattern. unfold evalGuard.
      unfold Expressions.evalFunction. simpl. rewrite H. auto.
  - (* rewrite tr_instantiateRuleOnPattern. *)
    unfold instantiateRuleOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    unfold instantiateIterationOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    unfold instantiateElementOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    simpl. reflexivity.
  - left. reflexivity.
Qed.


Theorem InitialState_of_NoneCompositeState_instantiate :
  forall (cm : HSMModel) (s: AbstractState),
        (andb (AbstractState_instanceOfEClass InitialStateEClass s)
              (isNone _ (AbstractState_getCompositeState s cm))) = true ->
    exists (t: AbstractState),
      instantiatePattern HSM2FSM cm [HSMMetamodel_toEObject s] = Some [HSMMetamodel_toEObject t].
Proof.
  intros.
  eexists _.
  unfold instantiatePattern. unfold matchPattern. simpl.
  rewrite H. simpl.
  unfold instantiateRuleOnPattern. simpl.
  assert ((AbstractState_instanceOfEClass RegularStateEClass s) = false). { 
    assert ((AbstractState_instanceOfEClass InitialStateEClass s) = true).
    { symmetry in H. apply Bool.andb_true_eq in H. crush. }
    unfold AbstractState_instanceOfEClass in H0.
    destruct (AbstractState_eqEClass_dec (AbstractState_getEClass s) InitialStateEClass).
    + unfold AbstractState_instanceOfEClass. crush.
    + crush.
  }
  rewrite H0. simpl.
  rewrite H.
  unfold instantiateIterationOnPattern. simpl.
  rewrite H. simpl.
  unfold instantiateElementOnPattern. simpl.
  rewrite H. simpl.
  destruct ((andb (AbstractState_instanceOfEClass InitialStateEClass s)
                    (negb (isNone CompositeState (AbstractState_getCompositeState s cm))))) eqn: is2rs.
    ++ assert ((isNone CompositeState (AbstractState_getCompositeState s cm)) = true). 
       { symmetry in H. apply Bool.andb_true_eq in H. crush. }
       assert ((negb (isNone CompositeState (AbstractState_getCompositeState s cm))) = true). 
       { symmetry in is2rs. apply Bool.andb_true_eq in is2rs. crush. }
       rewrite H1 in H2.
       crush.
    ++ simpl. reflexivity.
Qed.

Theorem InitialState_of_NoneCompositeState_instantiate' :
  forall (cm : HSMModel) (s: AbstractState),
        (andb (AbstractState_instanceOfEClass InitialStateEClass s)
              (isNone _ (AbstractState_getCompositeState s cm))) = true ->
    exists (t: AbstractState) tp,
      instantiatePattern HSM2FSM cm [HSMMetamodel_toEObject s] = Some tp /\
      In (HSMMetamodel_toEObject t) tp.
Proof.
  intros.
  eexists.
  apply tr_instantiatePattern_in.
  do 2 eexists.
  repeat split.
  - apply tr_matchPattern_in.
    split.
    + right. right. left. reflexivity.
    + (* rewrite tr_matchRuleOnPattern. *)
      unfold matchRuleOnPattern'. unfold matchRuleOnPattern. unfold evalGuard.
      unfold Expressions.evalFunction. simpl. rewrite H. auto.
  - (* rewrite tr_instantiateRuleOnPattern. *)
    unfold instantiateRuleOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    unfold instantiateIterationOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    unfold instantiateElementOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    simpl. reflexivity.
  - left. reflexivity.
Qed.

Theorem InitialState_of_CompositeState_instantiate :
  forall (cm : HSMModel) (s: AbstractState),
        (andb (AbstractState_instanceOfEClass InitialStateEClass s)
              (negb (isNone _ (AbstractState_getCompositeState s cm)))) = true ->
    exists (t: AbstractState),
      instantiatePattern HSM2FSM cm [HSMMetamodel_toEObject s] = Some [HSMMetamodel_toEObject t].
Proof.
  intros.
  eexists _.
  unfold instantiatePattern. unfold matchPattern. simpl.
  rewrite H. simpl.
  unfold instantiateRuleOnPattern. simpl.
  assert ((AbstractState_instanceOfEClass RegularStateEClass s) = false). { 
    assert ((AbstractState_instanceOfEClass InitialStateEClass s) = true).
    { symmetry in H. apply Bool.andb_true_eq in H. crush. }
    unfold AbstractState_instanceOfEClass in H0.
    destruct (AbstractState_eqEClass_dec (AbstractState_getEClass s) InitialStateEClass).
    + unfold AbstractState_instanceOfEClass. crush.
    + crush.
  }
  rewrite H0. simpl.
  assert ((andb (AbstractState_instanceOfEClass InitialStateEClass s)
              ((isNone _ (AbstractState_getCompositeState s cm)))) = false).
  { assert ((isNone _ (AbstractState_getCompositeState s cm)) = false). 
    { symmetry in H. apply Bool.andb_true_eq in H.
      destruct H. symmetry in H1. apply Bool.negb_true_iff in H1. exact H1. }
      crush. apply Bool.andb_false_r. }
  rewrite H1. unfold matchRuleOnPattern. simpl.
  rewrite H.
  unfold instantiateIterationOnPattern. simpl.
  rewrite H. simpl.
  unfold instantiateElementOnPattern. simpl.
  rewrite H. simpl.
  reflexivity.
Qed.

Theorem InitialState_of_CompositeState_instantiate' :
  forall (cm : HSMModel) (s: AbstractState),
        (andb (AbstractState_instanceOfEClass InitialStateEClass s)
              (negb (isNone _ (AbstractState_getCompositeState s cm)))) = true ->
    exists (t: AbstractState) tp,
      instantiatePattern HSM2FSM cm [HSMMetamodel_toEObject s] = Some tp /\
      In (HSMMetamodel_toEObject t) tp.
Proof.
  intros.
  eexists.
  apply tr_instantiatePattern_in.
  do 2 eexists.
  repeat split.
  - apply tr_matchPattern_in.
    split.
    + right. right. right. left. reflexivity.
    + (* rewrite tr_matchRuleOnPattern. *)
      unfold matchRuleOnPattern'. unfold matchRuleOnPattern. unfold evalGuard.
      unfold Expressions.evalFunction. simpl. rewrite H. auto.
  - (* rewrite tr_instantiateRuleOnPattern. *)
    unfold instantiateRuleOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    unfold instantiateIterationOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    unfold instantiateElementOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    simpl. reflexivity.
  - left. reflexivity.
Qed.

Theorem AbstractState_instantiate :
  forall (cm : HSMModel) (s: AbstractState),
        (negb (AbstractState_instanceOfEClass CompositeStateEClass s)) = true ->
      exists (t: AbstractState),
      instantiatePattern HSM2FSM cm [HSMMetamodel_toEObject s] = Some [HSMMetamodel_toEObject t].
Proof.
  intros.
  specialize (HSM_AbstractState_dec s).
  intro.
  destruct H0.
  + apply RegularState_instantiate. exact H0.
  + destruct H0.
    ++ destruct ((isNone _ (AbstractState_getCompositeState s cm))) eqn: g1.
       +++ apply InitialState_of_NoneCompositeState_instantiate. rewrite H0. rewrite g1. simpl. auto.
       +++ apply InitialState_of_CompositeState_instantiate. rewrite H0. rewrite g1. auto.
    ++ rewrite H0 in H. crush.
Qed.

Theorem AbstractState_instantiate' :
  forall (cm : HSMModel) (s: AbstractState),
        (negb (AbstractState_instanceOfEClass CompositeStateEClass s)) = true ->
    exists (t: AbstractState) tp,
      instantiatePattern HSM2FSM cm [HSMMetamodel_toEObject s] = Some tp /\
      In (HSMMetamodel_toEObject t) tp.
Proof.
  intros.
  specialize (HSM_AbstractState_dec s).
  intro.
  destruct H0.
  + apply RegularState_instantiate'. exact H0.
  + destruct H0.
    ++ destruct ((isNone _ (AbstractState_getCompositeState s cm))) eqn: g1.
       +++ apply InitialState_of_NoneCompositeState_instantiate'. rewrite H0. rewrite g1. simpl. auto.
       +++ apply InitialState_of_CompositeState_instantiate'. rewrite H0. rewrite g1. auto.
    ++ rewrite H0 in H. crush.
Qed.



