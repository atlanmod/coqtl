Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import transformations.Moore2Mealy.Moore.
Require Import transformations.Moore2Mealy.Mealy.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Instance Moore2MealyTransformationConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration MooreMetamodel_Metamodel_Instance MealyMetamodel_Metamodel_Instance.

Instance Moore2MealyModelingTransformationConfiguration : ModelingTransformationConfiguration Moore2MealyTransformationConfiguration :=
 Build_ModelingTransformationConfiguration Moore2MealyTransformationConfiguration MooreMetamodel_ModelingMetamodel_Instance MealyMetamodel_ModelingMetamodel_Instance.

Open Scope coqtl.

Definition MooreTransition_getTargetOutput transition m :=  
  match (Moore.Transition_getTarget transition m) with
  | Some target => (Moore.State_getOutput target)                 
  | None => ""%string
  end.

Definition Moore2Mealy' :=
    transformation
    [
      rule "state"
      from [Moore.StateClass]
      to [
        elem [Moore.StateClass] Mealy.StateClass "s'"
          (fun _ _ s => BuildState (Moore.State_getName s)) nil
      ];
      rule "transition"
      from [Moore.TransitionClass]
      to [
        elem [Moore.TransitionClass] Mealy.TransitionClass "t'"
          (fun _ m t => BuildTransition 
                          (Moore.Transition_getInput t) 
                          (MooreTransition_getTargetOutput t m))
          [
            link [Moore.TransitionClass] Mealy.TransitionClass 
              Mealy.TransitionSourceReference
              (fun tls _ m moore_tr mealy_tr =>
                maybeBuildTransitionSource mealy_tr
                  (maybeResolve tls m "s'" Mealy.StateClass 
                    (maybeSingleton (Moore.Transition_getSourceObject moore_tr m))));
            link [Moore.TransitionClass] Mealy.TransitionClass 
              Mealy.TransitionTargetReference
              (fun tls _ m moore_tr mealy_tr =>
                maybeBuildTransitionTarget mealy_tr
                  (maybeResolve tls m "s'" Mealy.StateClass 
                    (maybeSingleton (Moore.Transition_getTargetObject moore_tr m))))
          ]
      ]
].

Definition Moore2Mealy := parse Moore2Mealy'.

Close Scope coqtl.

