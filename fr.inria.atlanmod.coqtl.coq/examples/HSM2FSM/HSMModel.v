(********************************************************************
	@name Coq declarations for model
	@date 2018/08/17 11:47:36
	@description Automatically generated by XMI2Coq transformation.
 ********************************************************************)
		 
Require Import List.
Require Import core.Model.
Require Import HSM.
Require Import String.


Definition InputModel : Model HSMMetamodel_EObject HSMMetamodel_ELink :=
	(Build_Model
		(
		(Build_HSMMetamodel_EObject StateMachineEClass (BuildStateMachine "SM1" "1")) :: 
    (Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "t1" "1")) :: 
		(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "t2" "2")) :: 
    (Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "t3" "3")) :: 
    (Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "C" "3"))) :: 
		(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState CompositeStateEClass (BuildCompositeState "D" "4"))) :: 
		(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E" "5"))) :: 
		(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState InitialStateEClass (BuildInitialState "A" "1"))) :: 
		(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState InitialStateEClass (BuildInitialState "B" "2"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E000" "0"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E001" "1"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E002" "2"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E003" "3"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E004" "4"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E005" "5"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E006" "6"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E007" "7"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E008" "8"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E009" "9"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E010" "10"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E011" "11"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E012" "12"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E013" "13"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E014" "14"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E015" "15"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E016" "16"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E017" "17"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E018" "18"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E019" "19"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E020" "20"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E021" "21"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E022" "22"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E023" "23"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E024" "24"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E025" "25"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E026" "26"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E027" "27"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E028" "28"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E029" "29"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E030" "30"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E031" "31"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E032" "32"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E033" "33"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E034" "34"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E035" "35"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E036" "36"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E037" "37"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E038" "38"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E039" "39"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E040" "40"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E041" "41"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E042" "42"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E043" "43"))) :: 
(Build_HSMMetamodel_EObject AbstractStateEClass (BuildAbstractState RegularStateEClass (BuildRegularState "E044" "44"))) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "t000" "0")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt000" "0")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt001" "1")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt002" "2")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt003" "3")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt004" "4")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt005" "5")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt006" "6")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt007" "7")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt008" "8")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt009" "9")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt010" "10")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt011" "11")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt012" "12")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt013" "13")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt014" "14")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt015" "15")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt016" "16")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt017" "17")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt018" "18")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt019" "19")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt020" "20")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt021" "21")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt022" "22")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt023" "23")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt024" "24")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt025" "25")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt026" "26")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt027" "27")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt028" "28")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt029" "29")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt030" "30")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt031" "31")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt032" "32")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt033" "33")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt034" "34")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt035" "35")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt036" "36")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt037" "37")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt038" "38")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt039" "39")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt040" "40")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt041" "41")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt042" "42")) :: 
(Build_HSMMetamodel_EObject TransitionEClass (BuildTransition "nt043" "43")) :: 

		nil)
		(
    (Build_HSMMetamodel_ELink StateMachineTransitionsEReference (BuildStateMachineTransitions (BuildStateMachine "SM1" "1") ((BuildTransition "t1" "1") :: (BuildTransition "t2" "2") :: (BuildTransition "t3" "3") :: nil ))) ::
    (Build_HSMMetamodel_ELink StateMachineStatesEReference (BuildStateMachineStates (BuildStateMachine "SM1" "1") ((BuildAbstractState InitialStateEClass (BuildInitialState "A" "1")) :: (BuildAbstractState InitialStateEClass (BuildInitialState "B" "2")) :: (BuildAbstractState CompositeStateEClass (BuildCompositeState "D" "4")) :: (BuildAbstractState RegularStateEClass (BuildRegularState "C" "3")) :: (BuildAbstractState RegularStateEClass (BuildRegularState "E" "5")) :: nil ))) ::

    (Build_HSMMetamodel_ELink TransitionStateMachineEReference (BuildTransitionStateMachine (BuildTransition "t2" "2") (BuildStateMachine "SM1" "1"))) ::
    (Build_HSMMetamodel_ELink TransitionStateMachineEReference (BuildTransitionStateMachine (BuildTransition "t3" "3") (BuildStateMachine "SM1" "1"))) ::
    (Build_HSMMetamodel_ELink TransitionStateMachineEReference (BuildTransitionStateMachine (BuildTransition "t1" "1") (BuildStateMachine "SM1" "1"))) ::
		(Build_HSMMetamodel_ELink AbstractStateStateMachineEReference (BuildAbstractStateStateMachine (BuildAbstractState RegularStateEClass (BuildRegularState "C" "3")) (BuildStateMachine "SM1" "1"))) ::
		(Build_HSMMetamodel_ELink AbstractStateStateMachineEReference (BuildAbstractStateStateMachine (BuildAbstractState CompositeStateEClass (BuildCompositeState "D" "4")) (BuildStateMachine "SM1" "1"))) ::
		(Build_HSMMetamodel_ELink AbstractStateStateMachineEReference (BuildAbstractStateStateMachine (BuildAbstractState RegularStateEClass (BuildRegularState "E" "5")) (BuildStateMachine "SM1" "1"))) ::
		(Build_HSMMetamodel_ELink AbstractStateStateMachineEReference (BuildAbstractStateStateMachine (BuildAbstractState InitialStateEClass (BuildInitialState "A" "1")) (BuildStateMachine "SM1" "1"))) ::
		(Build_HSMMetamodel_ELink AbstractStateStateMachineEReference (BuildAbstractStateStateMachine (BuildAbstractState InitialStateEClass (BuildInitialState "B" "2")) (BuildStateMachine "SM1" "1"))) ::

    (Build_HSMMetamodel_ELink AbstractStateCompositeStateEReference (BuildAbstractStateCompositeState (BuildAbstractState RegularStateEClass (BuildRegularState "C" "3")) (BuildCompositeState "D" "4"))) ::
		(Build_HSMMetamodel_ELink AbstractStateCompositeStateEReference (BuildAbstractStateCompositeState (BuildAbstractState InitialStateEClass (BuildInitialState "B" "2")) (BuildCompositeState "D" "4"))) ::
 
		(Build_HSMMetamodel_ELink CompositeStateStatesEReference (BuildCompositeStateStates (BuildCompositeState "D" "4") ((BuildAbstractState InitialStateEClass (BuildInitialState "B" "2")) :: (BuildAbstractState RegularStateEClass (BuildRegularState "C" "3")) :: nil ))) ::
		
		(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "t1" "1") (BuildAbstractState InitialStateEClass (BuildInitialState "A" "1")))) ::
		(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "t1" "1") (BuildAbstractState CompositeStateEClass (BuildCompositeState "D" "4")))) ::
		(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "t2" "2") (BuildAbstractState InitialStateEClass (BuildInitialState "B" "2")))) ::
		(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "t2" "2") (BuildAbstractState RegularStateEClass (BuildRegularState "C" "3")))) ::
		(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "t3" "3") (BuildAbstractState CompositeStateEClass (BuildCompositeState "D" "4")))) ::
		(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "t3" "3") (BuildAbstractState RegularStateEClass (BuildRegularState "E" "5")))) ::

(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "t000" "0") (BuildAbstractState RegularStateEClass (BuildRegularState "E" "5")))) ::
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "t000" "0") (BuildAbstractState RegularStateEClass (BuildRegularState "E000" "0")))) ::
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt000" "0") (BuildAbstractState RegularStateEClass (BuildRegularState "E000" "0")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt000" "0") (BuildAbstractState RegularStateEClass (BuildRegularState "E001" "1")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt001" "1") (BuildAbstractState RegularStateEClass (BuildRegularState "E001" "1")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt001" "1") (BuildAbstractState RegularStateEClass (BuildRegularState "E002" "2")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt002" "2") (BuildAbstractState RegularStateEClass (BuildRegularState "E002" "2")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt002" "2") (BuildAbstractState RegularStateEClass (BuildRegularState "E003" "3")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt003" "3") (BuildAbstractState RegularStateEClass (BuildRegularState "E003" "3")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt003" "3") (BuildAbstractState RegularStateEClass (BuildRegularState "E004" "4")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt004" "4") (BuildAbstractState RegularStateEClass (BuildRegularState "E004" "4")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt004" "4") (BuildAbstractState RegularStateEClass (BuildRegularState "E005" "5")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt005" "5") (BuildAbstractState RegularStateEClass (BuildRegularState "E005" "5")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt005" "5") (BuildAbstractState RegularStateEClass (BuildRegularState "E006" "6")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt006" "6") (BuildAbstractState RegularStateEClass (BuildRegularState "E006" "6")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt006" "6") (BuildAbstractState RegularStateEClass (BuildRegularState "E007" "7")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt007" "7") (BuildAbstractState RegularStateEClass (BuildRegularState "E007" "7")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt007" "7") (BuildAbstractState RegularStateEClass (BuildRegularState "E008" "8")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt008" "8") (BuildAbstractState RegularStateEClass (BuildRegularState "E008" "8")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt008" "8") (BuildAbstractState RegularStateEClass (BuildRegularState "E009" "9")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt009" "9") (BuildAbstractState RegularStateEClass (BuildRegularState "E009" "9")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt009" "9") (BuildAbstractState RegularStateEClass (BuildRegularState "E010" "10")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt010" "10") (BuildAbstractState RegularStateEClass (BuildRegularState "E010" "10")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt010" "10") (BuildAbstractState RegularStateEClass (BuildRegularState "E011" "11")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt011" "11") (BuildAbstractState RegularStateEClass (BuildRegularState "E011" "11")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt011" "11") (BuildAbstractState RegularStateEClass (BuildRegularState "E012" "12")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt012" "12") (BuildAbstractState RegularStateEClass (BuildRegularState "E012" "12")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt012" "12") (BuildAbstractState RegularStateEClass (BuildRegularState "E013" "13")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt013" "13") (BuildAbstractState RegularStateEClass (BuildRegularState "E013" "13")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt013" "13") (BuildAbstractState RegularStateEClass (BuildRegularState "E014" "14")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt014" "14") (BuildAbstractState RegularStateEClass (BuildRegularState "E014" "14")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt014" "14") (BuildAbstractState RegularStateEClass (BuildRegularState "E015" "15")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt015" "15") (BuildAbstractState RegularStateEClass (BuildRegularState "E015" "15")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt015" "15") (BuildAbstractState RegularStateEClass (BuildRegularState "E016" "16")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt016" "16") (BuildAbstractState RegularStateEClass (BuildRegularState "E016" "16")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt016" "16") (BuildAbstractState RegularStateEClass (BuildRegularState "E017" "17")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt017" "17") (BuildAbstractState RegularStateEClass (BuildRegularState "E017" "17")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt017" "17") (BuildAbstractState RegularStateEClass (BuildRegularState "E018" "18")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt018" "18") (BuildAbstractState RegularStateEClass (BuildRegularState "E018" "18")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt018" "18") (BuildAbstractState RegularStateEClass (BuildRegularState "E019" "19")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt019" "19") (BuildAbstractState RegularStateEClass (BuildRegularState "E019" "19")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt019" "19") (BuildAbstractState RegularStateEClass (BuildRegularState "E020" "20")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt020" "20") (BuildAbstractState RegularStateEClass (BuildRegularState "E020" "20")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt020" "20") (BuildAbstractState RegularStateEClass (BuildRegularState "E021" "21")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt021" "21") (BuildAbstractState RegularStateEClass (BuildRegularState "E021" "21")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt021" "21") (BuildAbstractState RegularStateEClass (BuildRegularState "E022" "22")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt022" "22") (BuildAbstractState RegularStateEClass (BuildRegularState "E022" "22")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt022" "22") (BuildAbstractState RegularStateEClass (BuildRegularState "E023" "23")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt023" "23") (BuildAbstractState RegularStateEClass (BuildRegularState "E023" "23")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt023" "23") (BuildAbstractState RegularStateEClass (BuildRegularState "E024" "24")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt024" "24") (BuildAbstractState RegularStateEClass (BuildRegularState "E024" "24")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt024" "24") (BuildAbstractState RegularStateEClass (BuildRegularState "E025" "25")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt025" "25") (BuildAbstractState RegularStateEClass (BuildRegularState "E025" "25")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt025" "25") (BuildAbstractState RegularStateEClass (BuildRegularState "E026" "26")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt026" "26") (BuildAbstractState RegularStateEClass (BuildRegularState "E026" "26")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt026" "26") (BuildAbstractState RegularStateEClass (BuildRegularState "E027" "27")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt027" "27") (BuildAbstractState RegularStateEClass (BuildRegularState "E027" "27")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt027" "27") (BuildAbstractState RegularStateEClass (BuildRegularState "E028" "28")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt028" "28") (BuildAbstractState RegularStateEClass (BuildRegularState "E028" "28")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt028" "28") (BuildAbstractState RegularStateEClass (BuildRegularState "E029" "29")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt029" "29") (BuildAbstractState RegularStateEClass (BuildRegularState "E029" "29")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt029" "29") (BuildAbstractState RegularStateEClass (BuildRegularState "E030" "30")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt030" "30") (BuildAbstractState RegularStateEClass (BuildRegularState "E030" "30")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt030" "30") (BuildAbstractState RegularStateEClass (BuildRegularState "E031" "31")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt031" "31") (BuildAbstractState RegularStateEClass (BuildRegularState "E031" "31")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt031" "31") (BuildAbstractState RegularStateEClass (BuildRegularState "E032" "32")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt032" "32") (BuildAbstractState RegularStateEClass (BuildRegularState "E032" "32")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt032" "32") (BuildAbstractState RegularStateEClass (BuildRegularState "E033" "33")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt033" "33") (BuildAbstractState RegularStateEClass (BuildRegularState "E033" "33")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt033" "33") (BuildAbstractState RegularStateEClass (BuildRegularState "E034" "34")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt034" "34") (BuildAbstractState RegularStateEClass (BuildRegularState "E034" "34")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt034" "34") (BuildAbstractState RegularStateEClass (BuildRegularState "E035" "35")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt035" "35") (BuildAbstractState RegularStateEClass (BuildRegularState "E035" "35")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt035" "35") (BuildAbstractState RegularStateEClass (BuildRegularState "E036" "36")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt036" "36") (BuildAbstractState RegularStateEClass (BuildRegularState "E036" "36")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt036" "36") (BuildAbstractState RegularStateEClass (BuildRegularState "E037" "37")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt037" "37") (BuildAbstractState RegularStateEClass (BuildRegularState "E037" "37")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt037" "37") (BuildAbstractState RegularStateEClass (BuildRegularState "E038" "38")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt038" "38") (BuildAbstractState RegularStateEClass (BuildRegularState "E038" "38")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt038" "38") (BuildAbstractState RegularStateEClass (BuildRegularState "E039" "39")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt039" "39") (BuildAbstractState RegularStateEClass (BuildRegularState "E039" "39")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt039" "39") (BuildAbstractState RegularStateEClass (BuildRegularState "E040" "40")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt040" "40") (BuildAbstractState RegularStateEClass (BuildRegularState "E040" "40")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt040" "40") (BuildAbstractState RegularStateEClass (BuildRegularState "E041" "41")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt041" "41") (BuildAbstractState RegularStateEClass (BuildRegularState "E041" "41")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt041" "41") (BuildAbstractState RegularStateEClass (BuildRegularState "E042" "42")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt042" "42") (BuildAbstractState RegularStateEClass (BuildRegularState "E042" "42")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt042" "42") (BuildAbstractState RegularStateEClass (BuildRegularState "E043" "43")))) :: 
(Build_HSMMetamodel_ELink TransitionSourceEReference (BuildTransitionSource (BuildTransition "nt043" "43") (BuildAbstractState RegularStateEClass (BuildRegularState "E043" "43")))) :: 
(Build_HSMMetamodel_ELink TransitionTargetEReference (BuildTransitionTarget (BuildTransition "nt043" "43") (BuildAbstractState RegularStateEClass (BuildRegularState "E044" "44")))) :: 
		nil)
	).