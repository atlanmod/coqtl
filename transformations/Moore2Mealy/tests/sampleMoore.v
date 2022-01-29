	 
Require Import List.
Require Import core.Model.
Require Import String.
Require Import transformations.Moore2Mealy.Moore.
Open Scope string_scope.


Definition InputModel : Model MooreMetamodel_Object MooreMetamodel_Link :=
	(Build_Model
		(
		(Build_MooreMetamodel_Object StateClass (BuildState "S0" "1")) :: 
		(Build_MooreMetamodel_Object StateClass (BuildState "S1" "0")) ::
		(Build_MooreMetamodel_Object TransitionClass (BuildTransition "1")) ::
		(Build_MooreMetamodel_Object TransitionClass (BuildTransition "0")) :: 
		nil
		)
		(
		(Build_MooreMetamodel_Link TransitionSourceReference (BuildTransitionSource (BuildTransition "1") (BuildState "S1" "0"))) 
		 ::
		(Build_MooreMetamodel_Link TransitionTargetReference (BuildTransitionTarget (BuildTransition "1") (BuildState "S0" "1")))
		 ::
		(Build_MooreMetamodel_Link TransitionSourceReference (BuildTransitionSource (BuildTransition "0") (BuildState "S0" "1"))) 
		 ::
		(Build_MooreMetamodel_Link TransitionTargetReference (BuildTransitionTarget (BuildTransition "0") (BuildState "S1" "0")))
		 ::
		nil)
	).
