Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import String.

Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

(*Require Import core.Semantics.
Require Import core.Certification.*)
Require Import core.Semantics_v2.
Require Import core.Certification_v2.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.HSM2FSM.HSM.
Require Import examples.HSM2FSM.HSM2FSM.

Open Scope string_scope.

Ltac solve_eq :=
  try reflexivity;
  match goal with
  | |- match ?x with _ => _ end
       = match ?x with _ => _ end =>
    destruct x; auto
  end.

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
  apply tr_instantiateRuleOnPattern_in with (tr0:=HSM2FSM) in H6.
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
                  +++++ destruct (toModelClass StateMachineEClass h) eqn: sm_ca.
                        * destruct l.
                          **  clear H1 H3 H4 H5 H6 H7.
                              (*TODO make a lemma*)
                              assert (s = t1). 
                              {
                                unfold HSMMetamodel_toEObjectFromStateMachine in H8.
                                unfold HSMMetamodel_toEObjectOfEClass in H8.
                                (* must be a bug start *)
                                remember (Build_HSMMetamodel_EObject StateMachineEClass s) as a1.
                                remember (Build_HSMMetamodel_EObject StateMachineEClass t1) as a2.
                                inversion H8.
                                rewrite Heqa1 in H3.
                                rewrite Heqa2 in H3.
                                (* must be a bug end *)
                                apply HSM_invert in H3.
                                auto.
                              }
                              rewrite <- H1.
                              inversion eval_fun.
                              simpl.
                              specialize (Hpre d).
                              assert (In (HSMMetamodel_toEObjectFromStateMachine d) (allModelElements cm)). 
                              { 
                                (*TODO make a lemma*)
                                assert ((HSMMetamodel_toEObjectFromStateMachine d) = h). 
                                { 
                                  destruct h.
                                  simpl in sm_ca.
                                  destruct (HSMMetamodel_eqEClass_dec hsec_arg StateMachineEClass) eqn:tp_ca.
                                  * crush.
                                  * crush.
                                }
                                crush. 
                              }
                              specialize (H0 d). simpl in H0.
                              specialize (Hpre H3).
                              auto.
                          **  inversion eval_fun.
                        * inversion eval_fun.
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
    ++ destruct H3.
       destruct (nth_error (evalIterator r cm sp) i).
        +++  generalize dependent x.
             generalize dependent r0.        
             rewrite <- H3.
             simpl.
             intros.
             destruct H7.
             ++++ rewrite <- H7 in H8.
                 unfold evalOutputPatternElement in H8. simpl in H8.
                 destruct (Expressions.evalFunction HSMMetamodel cm 
            [AbstractStateEClass] AbstractState
            (fun (_ : HSMModel) (is1 : AbstractState) =>
             BuildAbstractState InitialStateEClass
               (BuildInitialState (AbstractState_getName is1)
                  (AbstractState_getAbstractStateID is1))) 
            (sp)) eqn: eval_fun.
                 +++++ unfold Expressions.evalFunction in eval_fun.
                      unfold Expressions.evalFunctionFix in eval_fun.
                      destruct sp eqn: sp_ca.
                      ++++++ inversion eval_fun.
                      ++++++ inversion H8.
                 +++++ inversion H8.
             ++++ inversion H7.
        +++ inversion H8.
        +++  destruct H3.
             destruct (nth_error (evalIterator r cm sp) i).
              ++++  generalize dependent x.
                   generalize dependent r0.        
                   rewrite <- H3.
                   simpl.
                   intros.
                   destruct H7.
                   +++++ rewrite <- H7 in H8.
                       unfold evalOutputPatternElement in H8. simpl in H8.
                       destruct (Expressions.evalFunction HSMMetamodel cm 
                                  [AbstractStateEClass] AbstractState
                                  (fun (_ : HSMModel) (is1 : AbstractState) =>
                                   BuildAbstractState RegularStateEClass
                                     (BuildRegularState (AbstractState_getName is1)
                                        (AbstractState_getAbstractStateID is1))) 
                                  (sp)) eqn: eval_fun.
                       ++++++ unfold Expressions.evalFunction in eval_fun.
                            unfold Expressions.evalFunctionFix in eval_fun.
                            destruct sp eqn: sp_ca.
                            +++++++ inversion eval_fun.
                            +++++++ inversion H8.
                       ++++++ inversion H8.
                   +++++ inversion H7.
              ++++ inversion H8.
              ++++ destruct H3.
                   destruct (nth_error (evalIterator r cm sp) i).
                    *    generalize dependent x.
                         generalize dependent r0.        
                         rewrite <- H3.
                         simpl.
                         intros.
                         destruct H7.
                         **  rewrite <- H7 in H8.
                             unfold evalOutputPatternElement in H8. simpl in H8.
                             destruct (Expressions.evalFunction HSMMetamodel cm [TransitionEClass]
                                       Transition
                                       (fun (_ : HSMModel) (t1 : Transition) =>
                                        BuildTransition (Transition_getLabel t1)
                                          (Transition_getTransitionID t1)) sp) eqn: eval_fun.
                             ***  unfold Expressions.evalFunction in eval_fun.
                                  unfold Expressions.evalFunctionFix in eval_fun.
                                  destruct sp eqn: sp_ca.
                                  **** inversion eval_fun.
                                  **** inversion H8.
                             *** inversion H8.
                         ** inversion H7.
                    * inversion H8.
                    *  destruct H3.
                       destruct (nth_error (evalIterator r cm sp) i).
                        **   generalize dependent x.
                             generalize dependent r0.        
                             rewrite <- H3.
                             simpl.
                             intros.
                             destruct H7.
                             *** rewrite <- H7 in H8.
                                 unfold evalOutputPatternElement in H8. simpl in H8.
                                 destruct (Expressions.evalFunction HSMMetamodel cm
                                 [TransitionEClass; AbstractStateEClass; AbstractStateEClass;
                                 AbstractStateEClass] Transition
                                 (fun (_ : HSMModel) (t1 : Transition) (_ _ _ : AbstractState) =>
                                  BuildTransition (Transition_getLabel t1)
                                    (Transition_getTransitionID t1)) sp) eqn: eval_fun.
                                 ****  unfold Expressions.evalFunction in eval_fun.
                                      unfold Expressions.evalFunctionFix in eval_fun.
                                      destruct sp eqn: sp_ca.
                                      ***** inversion eval_fun.
                                      ***** inversion H8.
                                 **** inversion H8.
                             *** inversion H7.
                        ** inversion H8.
                        ** destruct H3.
                           destruct (nth_error (evalIterator r cm sp) i).
                            ***   generalize dependent x.
                                 generalize dependent r0.        
                                 rewrite <- H3.
                                 simpl.
                                 intros.
                                 destruct H7.
                                 **** rewrite <- H7 in H8.
                                     unfold evalOutputPatternElement in H8. simpl in H8.
                                     destruct (Expressions.evalFunction HSMMetamodel cm
                                     [TransitionEClass; AbstractStateEClass; AbstractStateEClass;
                                     AbstractStateEClass] Transition
                                     (fun (_ : HSMModel) (t1 : Transition) (_ _ _ : AbstractState) =>
                                      BuildTransition (Transition_getLabel t1)
                                        (Transition_getTransitionID t1)) sp) eqn: eval_fun.
                                     *****  unfold Expressions.evalFunction in eval_fun.
                                          unfold Expressions.evalFunctionFix in eval_fun.
                                          destruct sp eqn: sp_ca.
                                          ****** inversion eval_fun.
                                          ****** inversion H8.
                                     ***** inversion H8.
                                 **** inversion H7.
                        *** inversion H8.
                        *** inversion H3.
Qed.

