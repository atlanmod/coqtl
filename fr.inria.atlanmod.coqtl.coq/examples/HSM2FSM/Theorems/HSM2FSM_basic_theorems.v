Require Import String.

Require Import core.utils.TopUtils.
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


Theorem InitialState_of_NoneCompositeState_instantiate' :
  forall (cm : HSMModel) (s: AbstractState),
        (andb (AbstractState_instanceOfEClass InitialStateEClass s)
              (isNone (AbstractState_getCompositeState s cm))) = true ->
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

Theorem InitialState_of_CompositeState_instantiate' :
  forall (cm : HSMModel) (s: AbstractState),
        (andb (AbstractState_instanceOfEClass InitialStateEClass s)
              (negb (isNone (AbstractState_getCompositeState s cm)))) = true ->
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

