Require Import Bool.
Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.TopUtils.
Require Import core.Syntax.
(* Require Import core.Semantics. *)
Require Import core.Semantics_v2.
Require Import examples.HSM2FSM.HSM.


Set Implicit Arguments.









Definition HSM2FSM :=
  (BuildTransformation
     HSMMetamodel HSMMetamodel
     [(BuildRule
         HSMMetamodel HSMMetamodel
         "SM2SM"
         [StateMachineEClass] (fun (m: HSMModel) (sm1:StateMachine) => true)
         unit (fun (m: HSMModel) (sm1:StateMachine) => [tt])
         [(BuildOutputPatternElement
             HSMMetamodel HSMMetamodel 
             [StateMachineEClass] "sm2" StateMachineEClass
             (fun _ (m: HSMModel) (sm1:StateMachine) => BuildStateMachine (StateMachine_getName sm1) (StateMachine_getStateMachineID sm1))
             [(BuildOutputPatternElementReference
                 HSMMetamodel HSMMetamodel
                 [StateMachineEClass] StateMachineEClass StateMachineStatesEReference
                 (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                    _ (m: HSMModel) (sm1:StateMachine) (sm2:StateMachine) =>
                    states <- StateMachine_getStates sm1 m;
                    new_states <- resolveAll tr m "as2" AbstractStateEClass
                      (map (fun s: AbstractState => [(HSMMetamodel_toEObject s)] ) states);
                    return BuildStateMachineStates sm2 new_states))])]);
            (BuildRule
              HSMMetamodel HSMMetamodel
              "RS2RS"
              [AbstractStateEClass] (fun (m: HSMModel) (rs1:AbstractState) => (AbstractState_instanceOfEClass RegularStateEClass rs1))
              unit (fun (m: HSMModel) (rs1:AbstractState) => [tt])
              [(BuildOutputPatternElement
                  HSMMetamodel HSMMetamodel 
                  [AbstractStateEClass] "as2" AbstractStateEClass
                  (fun _ (m: HSMModel) (rs1:AbstractState) => BuildAbstractState RegularStateEClass (BuildRegularState (AbstractState_getName rs1) (AbstractState_getAbstractStateID rs1)))
                  [(BuildOutputPatternElementReference
                      HSMMetamodel HSMMetamodel
                      [AbstractStateEClass] AbstractStateEClass AbstractStateStateMachineEReference
                      (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                          _ (m: HSMModel) (rs1:AbstractState) (as2:AbstractState) =>
                       hsm_sm <- (AbstractState_getStateMachine rs1 m);
                       fsm_sm <- resolve tr m "sm2" StateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                       return BuildAbstractStateStateMachine as2 fsm_sm  ))])]);
            (BuildRule
              HSMMetamodel HSMMetamodel
              "IS2IS"
              [AbstractStateEClass] (fun (m: HSMModel) (is1:AbstractState) => (andb (AbstractState_instanceOfEClass InitialStateEClass is1)
                                                                                    (isNone (AbstractState_getCompositeState is1 m))))
              unit (fun (m: HSMModel) (is1:AbstractState) => [tt])
              [(BuildOutputPatternElement
                  HSMMetamodel HSMMetamodel 
                  [AbstractStateEClass] "as2" AbstractStateEClass
                  (fun _ (m: HSMModel) (is1:AbstractState) => BuildAbstractState InitialStateEClass (BuildInitialState (AbstractState_getName is1) (AbstractState_getAbstractStateID is1)))
                  [(BuildOutputPatternElementReference
                      HSMMetamodel HSMMetamodel
                      [AbstractStateEClass] AbstractStateEClass AbstractStateStateMachineEReference
                      (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                          _ (m: HSMModel) (is1:AbstractState) (as2:AbstractState) =>
                       hsm_sm <- (AbstractState_getStateMachine is1 m);
                       fsm_sm <- resolve tr m "sm2" StateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                       return BuildAbstractStateStateMachine as2 fsm_sm   ))])]);
            (BuildRule
              HSMMetamodel HSMMetamodel
              "IS2RS"
              [AbstractStateEClass] (fun (m: HSMModel) (is1:AbstractState) => (andb (AbstractState_instanceOfEClass InitialStateEClass is1)
                                                                                    (negb (isNone (AbstractState_getCompositeState is1 m)))))
              unit (fun (m: HSMModel) (is1:AbstractState) => [tt])
              [(BuildOutputPatternElement
                  HSMMetamodel HSMMetamodel 
                  [AbstractStateEClass] "as2" AbstractStateEClass
                  (fun _ (m: HSMModel) (is1:AbstractState) => BuildAbstractState RegularStateEClass (BuildRegularState (AbstractState_getName is1) (AbstractState_getAbstractStateID is1)))
                  [(BuildOutputPatternElementReference
                      HSMMetamodel HSMMetamodel
                      [AbstractStateEClass] AbstractStateEClass AbstractStateStateMachineEReference
                      (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                          _ (m: HSMModel) (is1:AbstractState) (as2:AbstractState) =>
                       hsm_sm <- (AbstractState_getStateMachine is1 m);
                       fsm_sm <- resolve tr m "sm2" StateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                       return BuildAbstractStateStateMachine as2 fsm_sm    ))])]);
            (BuildRule
              HSMMetamodel HSMMetamodel
              "T2TA"
              [TransitionEClass] (fun (m: HSMModel) (t1:Transition) => andb (negb (AbstractState_instanceOfEClass_optional CompositeStateEClass (Transition_getSource t1 m)))
                                                                           (negb (AbstractState_instanceOfEClass_optional CompositeStateEClass (Transition_getTarget t1 m)))   )
              unit (fun (m: HSMModel) (t1:Transition) => [tt])
              [(BuildOutputPatternElement
                  HSMMetamodel HSMMetamodel 
                  [TransitionEClass] "t2" TransitionEClass
                  (fun _ (m: HSMModel) (t1:Transition) => BuildTransition (Transition_getLabel t1) (Transition_getTransitionID t1))
                  [(BuildOutputPatternElementReference
                      HSMMetamodel HSMMetamodel
                      [TransitionEClass] TransitionEClass TransitionStateMachineEReference
                      (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                          _ (m: HSMModel) (t1:Transition) (t2:Transition) =>
                       hsm_sm <- (Transition_getStateMachine t1 m);
                       fsm_sm <- resolve tr m "sm2" StateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                       return BuildTransitionStateMachine t2 fsm_sm    ));
                   (BuildOutputPatternElementReference
                      HSMMetamodel HSMMetamodel
                      [TransitionEClass] TransitionEClass TransitionSourceEReference
                      (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                          _ (m: HSMModel) (t1:Transition) (t2:Transition)  =>
                       hsm_tr_source <- (Transition_getSource t1 m);
                       fsm_tr_source <- resolve tr m "as2" AbstractStateEClass [HSMMetamodel_toEObject hsm_tr_source];
                       return BuildTransitionSource t2 fsm_tr_source    ));
                   (BuildOutputPatternElementReference
                      HSMMetamodel HSMMetamodel
                      [TransitionEClass] TransitionEClass TransitionTargetEReference
                      (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                          _ (m: HSMModel) (t1:Transition) (t2:Transition) =>
                       hsm_tr_target <- (Transition_getTarget t1 m);
                       fsm_tr_target <- resolve tr m "as2" AbstractStateEClass [HSMMetamodel_toEObject hsm_tr_target];
                       return BuildTransitionTarget t2 fsm_tr_target    ))
                  ])]);
            (BuildRule
              HSMMetamodel HSMMetamodel
              "T2TB"
              [TransitionEClass; AbstractStateEClass; AbstractStateEClass; AbstractStateEClass] 
              (fun (m: HSMModel) (t1:Transition) (src:AbstractState) (trg:AbstractState) (c:AbstractState) => 
                    (AbstractState_instanceOfEClass CompositeStateEClass src) &&
                    (negb (AbstractState_instanceOfEClass CompositeStateEClass trg)) &&
                    (negb (beq_AbstractState c src)) &&
                     beq_AbstractState_option (Transition_getSource t1 m) (Some src) && 
                     beq_AbstractState_option (Transition_getTarget t1 m) (Some trg) &&
                     beq_CompositeState_option (AbstractState_getCompositeState c m) (HSMMetamodel_AbstractState_downcast CompositeStateEClass src)   )
              unit (fun (m: HSMModel) (t1:Transition) (src:AbstractState) (trg:AbstractState) (c:AbstractState)=> [tt])
              [(BuildOutputPatternElement
                  HSMMetamodel HSMMetamodel 
                  [TransitionEClass; AbstractStateEClass; AbstractStateEClass; AbstractStateEClass] "t2" TransitionEClass
                  (fun _ (m: HSMModel) (t1:Transition) (src:AbstractState) (trg: AbstractState) (c: AbstractState) => BuildTransition (Transition_getLabel t1) (Transition_getTransitionID t1))
                  [(BuildOutputPatternElementReference
                      HSMMetamodel HSMMetamodel
                      [TransitionEClass; AbstractStateEClass; AbstractStateEClass; AbstractStateEClass] TransitionEClass TransitionStateMachineEReference
                      (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                          _ (m: HSMModel) (t1:Transition) (src:AbstractState) (trg:AbstractState) (c:AbstractState) (t2:Transition) =>
                       hsm_sm <- (Transition_getStateMachine t1 m);
                       fsm_sm <- resolve tr m "sm2" StateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                       return BuildTransitionStateMachine t2 fsm_sm    ));
                   (BuildOutputPatternElementReference
                      HSMMetamodel HSMMetamodel
                      [TransitionEClass; AbstractStateEClass; AbstractStateEClass; AbstractStateEClass] TransitionEClass TransitionSourceEReference
                      (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                          _ (m: HSMModel) (t1:Transition) (src:AbstractState) (trg:AbstractState) (c:AbstractState) (t2:Transition) =>
                       fsm_tr_source <- resolve tr m "as2" AbstractStateEClass [HSMMetamodel_toEObject c];
                       return BuildTransitionSource t2 fsm_tr_source    ));
                   (BuildOutputPatternElementReference
                      HSMMetamodel HSMMetamodel
                      [TransitionEClass; AbstractStateEClass; AbstractStateEClass; AbstractStateEClass] TransitionEClass TransitionTargetEReference
                      (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                          _ (m: HSMModel) (t1:Transition) (src:AbstractState) (trg:AbstractState) (c:AbstractState) (t2:Transition) =>
                       fsm_tr_target <- resolve tr m "as2" AbstractStateEClass [HSMMetamodel_toEObject trg];
                       return BuildTransitionTarget t2 fsm_tr_target    ))
                  ])]);
            (BuildRule
              HSMMetamodel HSMMetamodel
              "T2TC"
              [TransitionEClass; AbstractStateEClass; AbstractStateEClass; AbstractStateEClass] 
              (fun (m: HSMModel) (t1:Transition) (src:AbstractState) (trg:AbstractState) (c:AbstractState) => 
                    (AbstractState_instanceOfEClass CompositeStateEClass trg) &&
                    (AbstractState_instanceOfEClass InitialStateEClass c) &&
                    (negb (AbstractState_instanceOfEClass CompositeStateEClass src)) &&
                     beq_AbstractState_option (Transition_getSource t1 m) (Some src) && 
                     beq_AbstractState_option (Transition_getTarget t1 m) (Some trg) && 
                     beq_CompositeState_option (AbstractState_getCompositeState c m) (HSMMetamodel_AbstractState_downcast CompositeStateEClass trg)   )
              unit (fun (m: HSMModel) (t1:Transition) (src:AbstractState) (trg:AbstractState) (c:AbstractState)=> [tt])
              [(BuildOutputPatternElement
                  HSMMetamodel HSMMetamodel 
                  [TransitionEClass; AbstractStateEClass; AbstractStateEClass; AbstractStateEClass] "t2" TransitionEClass
                  (fun _ (m: HSMModel) (t1:Transition) (src:AbstractState) (trg: AbstractState) (c: AbstractState) => 
                     BuildTransition (Transition_getLabel t1) (Transition_getTransitionID t1))
                  [(BuildOutputPatternElementReference
                      HSMMetamodel HSMMetamodel
                      [TransitionEClass; AbstractStateEClass; AbstractStateEClass; AbstractStateEClass] TransitionEClass TransitionStateMachineEReference
                      (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                          _ (m: HSMModel) (t1:Transition) (src:AbstractState) (trg:AbstractState) (c:AbstractState) (t2:Transition) =>
                       hsm_sm <- (Transition_getStateMachine t1 m);
                       fsm_sm <- resolve tr m "sm2" StateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                       return BuildTransitionStateMachine t2 fsm_sm   ));
                   (BuildOutputPatternElementReference
                      HSMMetamodel HSMMetamodel
                      [TransitionEClass; AbstractStateEClass; AbstractStateEClass; AbstractStateEClass] TransitionEClass TransitionSourceEReference
                      (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                          _ (m: HSMModel) (t1:Transition) (src:AbstractState) (trg:AbstractState) (c:AbstractState) (t2:Transition) =>
                       fsm_tr_source <- resolve tr m "as2" AbstractStateEClass [HSMMetamodel_toEObject src];
                       return BuildTransitionSource t2 fsm_tr_source    ));
                   (BuildOutputPatternElementReference
                      HSMMetamodel HSMMetamodel
                      [TransitionEClass; AbstractStateEClass; AbstractStateEClass; AbstractStateEClass] TransitionEClass TransitionTargetEReference
                      (fun (tr: MatchedTransformation HSMMetamodel HSMMetamodel)
                          _ (m: HSMModel) (t1:Transition) (src:AbstractState) (trg:AbstractState) (c:AbstractState) (t2:Transition) =>
                       hsm_c_abstract <- Some c;
                       fsm_tr_target <- resolve tr m "as2" AbstractStateEClass [HSMMetamodel_toEObject hsm_c_abstract];
                       return BuildTransitionTarget t2 fsm_tr_target   ))
                  ])])
]).





