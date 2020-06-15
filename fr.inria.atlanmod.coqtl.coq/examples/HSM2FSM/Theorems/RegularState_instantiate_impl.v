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

Theorem RegularState_instantiate_impl :
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