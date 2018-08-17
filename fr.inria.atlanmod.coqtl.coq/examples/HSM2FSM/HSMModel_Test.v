Require Import String.
Require Import List.

Require Import core.CoqTL.
Require Import core.utils.tPrint.

Require Import examples.HSM2FSM.HSM.
Require Import examples.HSM2FSM.FSM.
Require Import examples.HSM2FSM.HSM2FSM.
Require Import examples.HSM2FSM.HSMModel.


Compute execute HSM2FSM InputModel.


(*


     = {|
       Model.modelElements := Build_FSMMetamodel_EObject FTransitionEClass (BuildFTransition "t1" "1")
                              :: Build_FSMMetamodel_EObject FTransitionEClass (BuildFTransition "t3" "3")
                                 :: Build_FSMMetamodel_EObject FTransitionEClass (BuildFTransition "t3" "3")
                                    :: Build_FSMMetamodel_EObject FAbstractStateEClass (BuildFAbstractState "C" "3")
                                       :: Build_FSMMetamodel_EObject FAbstractStateEClass (BuildFAbstractState "D" "4")
                                          :: Build_FSMMetamodel_EObject FAbstractStateEClass
                                               (BuildFAbstractState "E" "5")
                                             :: Build_FSMMetamodel_EObject FAbstractStateEClass
                                                  (BuildFAbstractState "A" "1")
                                                :: Build_FSMMetamodel_EObject FAbstractStateEClass
                                                     (BuildFAbstractState "B" "2")
                                                   :: Build_FSMMetamodel_EObject FStateMachineEClass
                                                        (BuildFStateMachine "SM1" "1")
                                                      :: Build_FSMMetamodel_EObject FRegularStateEClass
                                                           (BuildFRegularState (BuildFAbstractState "C" "3") "103")
                                                         :: Build_FSMMetamodel_EObject FTransitionEClass
                                                              (BuildFTransition "t2" "2")
                                                            :: Build_FSMMetamodel_EObject FRegularStateEClass
                                                                 (BuildFRegularState (BuildFAbstractState "E" "5")
                                                                    "105")
                                                               :: Build_FSMMetamodel_EObject FInitialStateEClass
                                                                    (BuildFInitialState (BuildFAbstractState "A" "1")
                                                                       "101")
                                                                  :: Build_FSMMetamodel_EObject FRegularStateEClass
                                                                       (BuildFRegularState
                                                                          (BuildFAbstractState "B" "2") "102") :: nil;
       Model.modelLinks := Build_FSMMetamodel_ELink FTransitionStateMachineEReference
                             (BuildFTransitionStateMachine (BuildFTransition "t1" "1") (BuildFStateMachine "SM1" "1"))
                           :: Build_FSMMetamodel_ELink FTransitionSourceEReference
                                (BuildFTransitionSource (BuildFTransition "t1" "1") (BuildFAbstractState "A" "1"))
                              :: Build_FSMMetamodel_ELink FTransitionTargetEReference
                                   (BuildFTransitionTarget (BuildFTransition "t1" "1") (BuildFAbstractState "B" "2"))
                                 :: Build_FSMMetamodel_ELink FTransitionStateMachineEReference
                                      (BuildFTransitionStateMachine (BuildFTransition "t3" "3")
                                         (BuildFStateMachine "SM1" "1"))
                                    :: Build_FSMMetamodel_ELink FTransitionSourceEReference
                                         (BuildFTransitionSource (BuildFTransition "t3" "3")
                                            (BuildFAbstractState "C" "3"))
                                       :: Build_FSMMetamodel_ELink FTransitionTargetEReference
                                            (BuildFTransitionTarget (BuildFTransition "t3" "3")
                                               (BuildFAbstractState "E" "5"))
                                          :: Build_FSMMetamodel_ELink FTransitionStateMachineEReference
                                               (BuildFTransitionStateMachine (BuildFTransition "t3" "3")
                                                  (BuildFStateMachine "SM1" "1"))
                                             :: Build_FSMMetamodel_ELink FTransitionSourceEReference
                                                  (BuildFTransitionSource (BuildFTransition "t3" "3")
                                                     (BuildFAbstractState "B" "2"))
                                                :: Build_FSMMetamodel_ELink FTransitionTargetEReference
                                                     (BuildFTransitionTarget (BuildFTransition "t3" "3")
                                                        (BuildFAbstractState "E" "5"))
                                                   :: Build_FSMMetamodel_ELink FAbstractStateStateMachineEReference
                                                        (BuildFAbstractStateStateMachine (BuildFAbstractState "C" "3")
                                                           (BuildFStateMachine "SM1" "1"))
                                                      :: Build_FSMMetamodel_ELink FAbstractStateStateMachineEReference
                                                           (BuildFAbstractStateStateMachine
                                                              (BuildFAbstractState "D" "4")
                                                              (BuildFStateMachine "SM1" "1"))
                                                         :: Build_FSMMetamodel_ELink
                                                              FAbstractStateStateMachineEReference
                                                              (BuildFAbstractStateStateMachine
                                                                 (BuildFAbstractState "E" "5")
                                                                 (BuildFStateMachine "SM1" "1"))
                                                            :: Build_FSMMetamodel_ELink
                                                                 FAbstractStateStateMachineEReference
                                                                 (BuildFAbstractStateStateMachine
                                                                    (BuildFAbstractState "A" "1")
                                                                    (BuildFStateMachine "SM1" "1"))
                                                               :: Build_FSMMetamodel_ELink
                                                                    FAbstractStateStateMachineEReference
                                                                    (BuildFAbstractStateStateMachine
                                                                       (BuildFAbstractState "B" "2")
                                                                       (BuildFStateMachine "SM1" "1"))
                                                                  :: Build_FSMMetamodel_ELink
                                                                       FTransitionStateMachineEReference
                                                                       (BuildFTransitionStateMachine
                                                                          (BuildFTransition "t2" "2")
                                                                          (BuildFStateMachine "SM1" "1"))
                                                                     :: Build_FSMMetamodel_ELink
                                                                          FTransitionSourceEReference
                                                                          (BuildFTransitionSource
                                                                             (BuildFTransition "t2" "2")
                                                                             (BuildFAbstractState "B" "2"))
                                                                        :: Build_FSMMetamodel_ELink
                                                                             FTransitionTargetEReference
                                                                             (BuildFTransitionTarget
                                                                                (BuildFTransition "t2" "2")
                                                                                (BuildFAbstractState "C" "3")) :: nil |}
     : TargetModel FSMMetamodel_EObject FSMMetamodel_ELink


*)