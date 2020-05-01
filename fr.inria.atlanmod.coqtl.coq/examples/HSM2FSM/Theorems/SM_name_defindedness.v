Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import String.

Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

Require Import core.CoqTL.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.HSM2FSM.HSM.
Require Import examples.HSM2FSM.HSM2FSM.

Open Scope string_scope.


Theorem Table_id_defindedness :
forall (cm : HSMModel) (rm : HSMModel), 
rm = execute HSM2FSM cm (* transformation *) ->
  (forall (s1 : StateMachine), In (HSMMetamodel_toEObjectFromStateMachine s1) (allModelElements cm) -> StateMachine_getName s1 <> "") (* precondition *) ->
    (forall (s2 : StateMachine), In (HSMMetamodel_toEObjectFromStateMachine s2) (allModelElements rm) -> StateMachine_getName s2 <> ""). (* postcondition *)
Proof.
  (** Clean context *)
  intros cm rm H Hpre t1 Hintm.  
  remember H as tr.
  clear Heqtr.
  rewrite tr in Hintm.
  apply tr_execute_in_elements in Hintm.
  destruct Hintm. destruct H0. destruct H0. destruct H1.
  
  (** Unfolding theorem tr_instantiatePattern_in *)
  assert (exists tp : list HSMMetamodel_EObject,
             instantiatePattern HSM2FSM cm x = return tp /\ 
             In (HSMMetamodel_toEObjectFromStateMachine t1) tp).
  { exists x0. split. crush. crush. }
  apply tr_instantiatePattern_in in H3.
  destruct H3. destruct H3. destruct H3.
  rename x1 into r. rename x2 into tp. rename x into sp.
  
  (** Unfolding theorem tr_matchPattern_in *)
  apply tr_matchPattern_in in H3.
  destruct H3.

  (** Unfolding theorem tr_instantiateRuleOnPattern_in *)
  assert (exists tp : list HSMMetamodel_EObject,
          instantiateRuleOnPattern r cm sp = return tp /\ 
          In (HSMMetamodel_toEObjectFromStateMachine t1) tp).
  { exists tp. crush. }
  apply tr_instantiateRuleOnPattern_in with (tr:=HSM2FSM) in H6.
  destruct H6. destruct H6.
  rename x into i.
  rename x1 into tp1.

  (** Unfolding theorem tr_instantiateIterationOnPattern_in *)
  assert  (exists tp : list  HSMMetamodel_EObject,
          instantiateIterationOnPattern r cm sp i = return tp /\ 
          In (HSMMetamodel_toEObjectFromStateMachine t1) tp).
  { exists tp1. crush. }
  apply tr_instantiateIterationOnPattern_in in H7.
  destruct H7. destruct H7.
  unfold instantiateElementOnPattern in H8.
  unfold matchRuleOnPattern' in H5.
  rewrite H5 in H8.
  unfold HSM2FSM in H3.
  simpl in H3.
  destruct H3.
  + destruct (nth_error (evalIterator r cm sp) i).
    ++   generalize dependent x.
         generalize dependent r0.
         rewrite <- H3.
         simpl.
         intros.
         destruct H7.
         +++ rewrite <- H7 in H8.
             unfold evalOutputPatternElement in H8. simpl in H8.
             destruct (Expressions.evalFunction HSMMetamodel cm [StateMachineEClass]
                       StateMachine
                       (fun (_ : HSMModel) (sm1 : StateMachine) =>
                        BuildStateMachine (StateMachine_getName sm1)
                          (StateMachine_getStateMachineID sm1)) sp) eqn: eval_fun.
             ++++ unfold Expressions.evalFunction in eval_fun.
                  unfold Expressions.evalFunctionFix in eval_fun.
                  destruct sp eqn: sp_ca.
                  +++++ inversion eval_fun.
                  +++++ (*destruct s eqn: s_ca.
                        destruct c0 eqn: c0_ca.
                         * simpl in eval_fun.
                           destruct l.
                           **  inversion eval_fun.
                               inversion H8.
                               rewrite <- H10.
                               simpl.
                               specialize (Hpre c).
                               unfold incl in H0.
                               specialize (H0 c). simpl in H0.
                               assert (In c (allModelElements cm)). { crush. }
                               specialize (Hpre H9).
                               unfold ClassMetamodel_getId in Hpre.
                               rewrite c_ca in Hpre. auto.
                           **  inversion eval_fun.
                         * simpl in eval_fun. inversion eval_fun.*) 
                        admit.
             ++++ inversion H8.
         +++ crush.
    ++ crush.
  + destruct H3.
    destruct (nth_error (evalIterator r cm sp) i).
    ++   generalize dependent x.
         generalize dependent r0.        
         rewrite <- H3.
         simpl.
         intros.
         destruct H7.
         +++ rewrite <- H7 in H8.
             unfold evalOutputPatternElement in H8. simpl in H8.
             destruct (Expressions.evalFunction HSMMetamodel cm [AbstractStateEClass]
                       AbstractState
                       (fun (_ : HSMModel) (rs1 : AbstractState) =>
                        BuildAbstractState RegularStateEClass
                          (BuildRegularState (AbstractState_getName rs1)
                             (AbstractState_getAbstractStateID rs1))) sp) eqn: eval_fun.
             ++++ unfold Expressions.evalFunction in eval_fun.
                  unfold Expressions.evalFunctionFix in eval_fun.
                  destruct sp eqn: sp_ca.
                  +++++ inversion eval_fun.
                  +++++ inversion H8.
             ++++ inversion H8.
         +++ inversion H7.
    ++ inversion H8.
    ++ inversion H3.
admit.
admit.
Abort.

