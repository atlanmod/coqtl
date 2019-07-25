

type __ = Obj.t

type bool =
| True
| False

type 'a list =
| Nil
| Cons of 'a * 'a list

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

type ('modelElement, 'modelLink) model = { modelElements : 'modelElement list;
                                           modelLinks : 'modelLink list }

type stateMachine =
| BuildStateMachine of string * string

type transition =
| BuildTransition of string * string

type initialState =
| BuildInitialState of string * string

type regularState =
| BuildRegularState of string * string

type compositeState =
| BuildCompositeState of string * string

type abstractState_EClass =
| InitialStateEClass
| RegularStateEClass
| CompositeStateEClass

type abstractState_getTypeByEClass = __

type abstractState =
| BuildAbstractState of abstractState_EClass * abstractState_getTypeByEClass

type stateMachineTransitions =
| BuildStateMachineTransitions of stateMachine * transition list

type stateMachineStates =
| BuildStateMachineStates of stateMachine * abstractState list

type transitionStateMachine =
| BuildTransitionStateMachine of transition * stateMachine

type transitionSource =
| BuildTransitionSource of transition * abstractState

type transitionTarget =
| BuildTransitionTarget of transition * abstractState

type abstractStateStateMachine =
| BuildAbstractStateStateMachine of abstractState * stateMachine

type abstractStateCompositeState =
| BuildAbstractStateCompositeState of abstractState * compositeState

type compositeStateStates =
| BuildCompositeStateStates of compositeState * abstractState list

type hSMMetamodel_EClass =
| StateMachineEClass
| TransitionEClass
| AbstractStateEClass

type hSMMetamodel_getTypeByEClass = __

type hSMMetamodel_EReference =
| StateMachineTransitionsEReference
| StateMachineStatesEReference
| TransitionStateMachineEReference
| TransitionSourceEReference
| TransitionTargetEReference
| AbstractStateStateMachineEReference
| AbstractStateCompositeStateEReference
| CompositeStateStatesEReference

type hSMMetamodel_getTypeByEReference = __

type hSMMetamodel_EObject =
| Build_HSMMetamodel_EObject of hSMMetamodel_EClass
   * hSMMetamodel_getTypeByEClass

type hSMMetamodel_ELink =
| Build_HSMMetamodel_ELink of hSMMetamodel_EReference
   * hSMMetamodel_getTypeByEReference

(** val inputModel : (hSMMetamodel_EObject, hSMMetamodel_ELink) model **)

let inputModel =
  { modelElements = (Cons ((Build_HSMMetamodel_EObject (StateMachineEClass,
    (Obj.magic (BuildStateMachine ((String ((Ascii (True, True, False, False,
      True, False, True, False)), (String ((Ascii (True, False, True, True,
      False, False, True, False)), (String ((Ascii (True, False, False,
      False, True, True, False, False)), EmptyString)))))), (String ((Ascii
      (True, False, False, False, True, True, False, False)), EmptyString))))))),
    (Cons ((Build_HSMMetamodel_EObject (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))), (String ((Ascii (True,
      False, False, False, True, True, False, False)), EmptyString))))))),
    (Cons ((Build_HSMMetamodel_EObject (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))), (String ((Ascii (False,
      True, False, False, True, True, False, False)), EmptyString))))))),
    (Cons ((Build_HSMMetamodel_EObject (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), EmptyString)))), (String ((Ascii (True,
      True, False, False, True, True, False, False)), EmptyString))))))),
    (Cons ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, True, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))))), (Cons ((Build_HSMMetamodel_EObject
    (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (CompositeStateEClass,
      (Obj.magic (BuildCompositeState ((String ((Ascii (False, False, True,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))))), (Cons ((Build_HSMMetamodel_EObject
    (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))))), (Cons ((Build_HSMMetamodel_EObject
    (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (InitialStateEClass,
      (Obj.magic (BuildInitialState ((String ((Ascii (True, False, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))))), (Cons ((Build_HSMMetamodel_EObject
    (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (InitialStateEClass,
      (Obj.magic (BuildInitialState ((String ((Ascii (False, True, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))))), (Cons ((Build_HSMMetamodel_EObject
    (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, False, False,
        True, True, False, False)), EmptyString)))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), EmptyString)))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), EmptyString)))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), EmptyString)))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), EmptyString)))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, True, False, True,
        True, False, False)), EmptyString)))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, True, False, True,
        True, False, False)), EmptyString)))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, True, False, True,
        True, False, False)), EmptyString)))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, False, True,
        True, True, False, False)), EmptyString)))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, True, True,
        True, False, False)), EmptyString)))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, True, False,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, True, False,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, False, True,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, False, True,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, True, True,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, True, True, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        True, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        True, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, True, False,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, True, False,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, False, True,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, False, True,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, True, True,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, True, True, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        True, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        True, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, False, False, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, False, False, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, True, False, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, True, False, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, False, True, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, False, True, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, True, True, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, True, True, False, True,
        True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, False, False, True,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, False, False, True,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (False, True, False,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (True, True, False,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (AbstractStateEClass,
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (False, False, True,
        False, True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_EObject (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), (String ((Ascii (False, False,
      False, False, True, True, False, False)), EmptyString)))))))), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), (String ((Ascii (False, False,
      False, False, True, True, False, False)), EmptyString)))))))))),
      (String ((Ascii (False, False, False, False, True, True, False,
      False)), EmptyString))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), (String ((Ascii (True, False, False,
      False, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), (String ((Ascii (False, True, False,
      False, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), (String ((Ascii (True, True, False,
      False, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), (String ((Ascii (False, False, True,
      False, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (False, False, True, False, True, True, False, False)),
      EmptyString))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), (String ((Ascii (True, False, True,
      False, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (True, False, True, False, True, True, False, False)),
      EmptyString))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), (String ((Ascii (False, True, True,
      False, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (False, True, True, False, True, True, False, False)),
      EmptyString))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), (String ((Ascii (True, True, True,
      False, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (True, True, True, False, True, True, False, False)),
      EmptyString))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), (String ((Ascii (False, False,
      False, True, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (False, False, False, True, True, True, False, False)),
      EmptyString))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), (String ((Ascii (True, False, False,
      True, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (True, False, False, True, True, True, False, False)),
      EmptyString))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, False, False, False, True, True, False, False)), (String ((Ascii
      (True, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, False, False, False, True, True, False, False)), (String ((Ascii
      (False, True, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, False, False, False, True, True, False, False)), (String ((Ascii
      (True, True, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, True, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, False, False, False, True, True, False, False)), (String ((Ascii
      (False, False, True, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, True, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, False, False, False, True, True, False, False)), (String ((Ascii
      (True, False, True, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, True, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, False, False, False, True, True, False, False)), (String ((Ascii
      (False, True, True, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, True, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, False, False, False, True, True, False, False)), (String ((Ascii
      (True, True, True, False, True, True, False, False)), EmptyString))))))))),
    (Cons ((Build_HSMMetamodel_EObject (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False, True,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, False, False, False, True, True, False, False)), (String ((Ascii
      (False, False, False, True, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, True,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, False, False, False, True, True, False, False)), (String ((Ascii
      (True, False, False, True, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (False, True, False, False, True, True, False, False)), (String ((Ascii
      (True, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (False, True, False, False, True, True, False, False)), (String ((Ascii
      (False, True, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (False, True, False, False, True, True, False, False)), (String ((Ascii
      (True, True, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, False, True, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (False, True, False, False, True, True, False, False)), (String ((Ascii
      (False, False, True, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, False, True, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (False, True, False, False, True, True, False, False)), (String ((Ascii
      (True, False, True, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, True, True, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (False, True, False, False, True, True, False, False)), (String ((Ascii
      (False, True, True, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, True, True, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (False, True, False, False, True, True, False, False)), (String ((Ascii
      (True, True, True, False, True, True, False, False)), EmptyString))))))))),
    (Cons ((Build_HSMMetamodel_EObject (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False, True,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (False, True, False, False, True, True, False, False)), (String ((Ascii
      (False, False, False, True, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, True,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (False, True, False, False, True, True, False, False)), (String ((Ascii
      (True, False, False, True, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, True, False, False, True, True, False, False)), (String ((Ascii
      (True, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, True, False, False, True, True, False, False)), (String ((Ascii
      (False, True, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, True, False, False, True, True, False, False)), (String ((Ascii
      (True, True, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), (String ((Ascii (False, False, True, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, True, False, False, True, True, False, False)), (String ((Ascii
      (False, False, True, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), (String ((Ascii (True, False, True, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, True, False, False, True, True, False, False)), (String ((Ascii
      (True, False, True, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), (String ((Ascii (False, True, True, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, True, False, False, True, True, False, False)), (String ((Ascii
      (False, True, True, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), (String ((Ascii (True, True, True, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, True, False, False, True, True, False, False)), (String ((Ascii
      (True, True, True, False, True, True, False, False)), EmptyString))))))))),
    (Cons ((Build_HSMMetamodel_EObject (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False, True,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, True, False, False, True, True, False, False)), (String ((Ascii
      (False, False, False, True, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, True,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (True, True, False, False, True, True, False, False)), (String ((Ascii
      (True, False, False, True, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, True, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))))))))), (String
      ((Ascii (False, False, True, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, True, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (False, False, True, False, True, True, False, False)), (String ((Ascii
      (True, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, True, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (False, False, True, False, True, True, False, False)), (String ((Ascii
      (False, True, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_EObject
    (TransitionEClass,
    (Obj.magic (BuildTransition ((String ((Ascii (False, True, True, True,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, True, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), EmptyString)))))))))), (String ((Ascii
      (False, False, True, False, True, True, False, False)), (String ((Ascii
      (True, True, False, False, True, True, False, False)),
      EmptyString))))))))),
    Nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    modelLinks = (Cons ((Build_HSMMetamodel_ELink
    (StateMachineTransitionsEReference,
    (Obj.magic (BuildStateMachineTransitions ((BuildStateMachine ((String
      ((Ascii (True, True, False, False, True, False, True, False)), (String
      ((Ascii (True, False, True, True, False, False, True, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))), (String ((Ascii (True, False, False, False, True,
      True, False, False)), EmptyString)))), (Cons ((BuildTransition ((String
      ((Ascii (False, False, True, False, True, True, True, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))), (String ((Ascii (True, False, False, False, True,
      True, False, False)), EmptyString)))), (Cons ((BuildTransition ((String
      ((Ascii (False, False, True, False, True, True, True, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString)))), (String ((Ascii (False, True, False, False, True,
      True, False, False)), EmptyString)))), (Cons ((BuildTransition ((String
      ((Ascii (False, False, True, False, True, True, True, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))), (String ((Ascii (True, True, False, False, True, True,
      False, False)), EmptyString)))), Nil))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (StateMachineStatesEReference,
    (Obj.magic (BuildStateMachineStates ((BuildStateMachine ((String ((Ascii
      (True, True, False, False, True, False, True, False)), (String ((Ascii
      (True, False, True, True, False, False, True, False)), (String ((Ascii
      (True, False, False, False, True, True, False, False)),
      EmptyString)))))), (String ((Ascii (True, False, False, False, True,
      True, False, False)), EmptyString)))), (Cons ((BuildAbstractState
      (InitialStateEClass,
      (Obj.magic (BuildInitialState ((String ((Ascii (True, False, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString))))))), (Cons ((BuildAbstractState (InitialStateEClass,
      (Obj.magic (BuildInitialState ((String ((Ascii (False, True, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString))))))), (Cons ((BuildAbstractState (CompositeStateEClass,
      (Obj.magic (BuildCompositeState ((String ((Ascii (False, False, True,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString))))))), (Cons ((BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, True, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString))))))), (Cons ((BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString))))))), Nil))))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionStateMachineEReference,
    (Obj.magic (BuildTransitionStateMachine ((BuildTransition ((String
      ((Ascii (False, False, True, False, True, True, True, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString)))), (String ((Ascii (False, True, False, False, True,
      True, False, False)), EmptyString)))), (BuildStateMachine ((String
      ((Ascii (True, True, False, False, True, False, True, False)), (String
      ((Ascii (True, False, True, True, False, False, True, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))), (String ((Ascii (True, False, False, False, True,
      True, False, False)), EmptyString))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionStateMachineEReference,
    (Obj.magic (BuildTransitionStateMachine ((BuildTransition ((String
      ((Ascii (False, False, True, False, True, True, True, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))), (String ((Ascii (True, True, False, False, True, True,
      False, False)), EmptyString)))), (BuildStateMachine ((String ((Ascii
      (True, True, False, False, True, False, True, False)), (String ((Ascii
      (True, False, True, True, False, False, True, False)), (String ((Ascii
      (True, False, False, False, True, True, False, False)),
      EmptyString)))))), (String ((Ascii (True, False, False, False, True,
      True, False, False)), EmptyString))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionStateMachineEReference,
    (Obj.magic (BuildTransitionStateMachine ((BuildTransition ((String
      ((Ascii (False, False, True, False, True, True, True, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))), (String ((Ascii (True, False, False, False, True,
      True, False, False)), EmptyString)))), (BuildStateMachine ((String
      ((Ascii (True, True, False, False, True, False, True, False)), (String
      ((Ascii (True, False, True, True, False, False, True, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))), (String ((Ascii (True, False, False, False, True,
      True, False, False)), EmptyString))))))))), (Cons
    ((Build_HSMMetamodel_ELink (AbstractStateStateMachineEReference,
    (Obj.magic (BuildAbstractStateStateMachine ((BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, True, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString))))))), (BuildStateMachine ((String ((Ascii (True, True,
      False, False, True, False, True, False)), (String ((Ascii (True, False,
      True, True, False, False, True, False)), (String ((Ascii (True, False,
      False, False, True, True, False, False)), EmptyString)))))), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_ELink
    (AbstractStateStateMachineEReference,
    (Obj.magic (BuildAbstractStateStateMachine ((BuildAbstractState
      (CompositeStateEClass,
      (Obj.magic (BuildCompositeState ((String ((Ascii (False, False, True,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString))))))), (BuildStateMachine ((String ((Ascii (True, True,
      False, False, True, False, True, False)), (String ((Ascii (True, False,
      True, True, False, False, True, False)), (String ((Ascii (True, False,
      False, False, True, True, False, False)), EmptyString)))))), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_ELink
    (AbstractStateStateMachineEReference,
    (Obj.magic (BuildAbstractStateStateMachine ((BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString))))))), (BuildStateMachine ((String ((Ascii (True, True,
      False, False, True, False, True, False)), (String ((Ascii (True, False,
      True, True, False, False, True, False)), (String ((Ascii (True, False,
      False, False, True, True, False, False)), EmptyString)))))), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_ELink
    (AbstractStateStateMachineEReference,
    (Obj.magic (BuildAbstractStateStateMachine ((BuildAbstractState
      (InitialStateEClass,
      (Obj.magic (BuildInitialState ((String ((Ascii (True, False, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString))))))), (BuildStateMachine ((String ((Ascii (True, True,
      False, False, True, False, True, False)), (String ((Ascii (True, False,
      True, True, False, False, True, False)), (String ((Ascii (True, False,
      False, False, True, True, False, False)), EmptyString)))))), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_ELink
    (AbstractStateStateMachineEReference,
    (Obj.magic (BuildAbstractStateStateMachine ((BuildAbstractState
      (InitialStateEClass,
      (Obj.magic (BuildInitialState ((String ((Ascii (False, True, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString))))))), (BuildStateMachine ((String ((Ascii (True, True,
      False, False, True, False, True, False)), (String ((Ascii (True, False,
      True, True, False, False, True, False)), (String ((Ascii (True, False,
      False, False, True, True, False, False)), EmptyString)))))), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_ELink
    (AbstractStateCompositeStateEReference,
    (Obj.magic (BuildAbstractStateCompositeState ((BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, True, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString))))))), (BuildCompositeState ((String ((Ascii (False,
      False, True, False, False, False, True, False)), EmptyString)), (String
      ((Ascii (False, False, True, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_ELink
    (AbstractStateCompositeStateEReference,
    (Obj.magic (BuildAbstractStateCompositeState ((BuildAbstractState
      (InitialStateEClass,
      (Obj.magic (BuildInitialState ((String ((Ascii (False, True, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString))))))), (BuildCompositeState ((String ((Ascii (False,
      False, True, False, False, False, True, False)), EmptyString)), (String
      ((Ascii (False, False, True, False, True, True, False, False)),
      EmptyString))))))))), (Cons ((Build_HSMMetamodel_ELink
    (CompositeStateStatesEReference,
    (Obj.magic (BuildCompositeStateStates ((BuildCompositeState ((String
      ((Ascii (False, False, True, False, False, False, True, False)),
      EmptyString)), (String ((Ascii (False, False, True, False, True, True,
      False, False)), EmptyString)))), (Cons ((BuildAbstractState
      (InitialStateEClass,
      (Obj.magic (BuildInitialState ((String ((Ascii (False, True, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString))))))), (Cons ((BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, True, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString))))))), Nil))))))))), (Cons ((Build_HSMMetamodel_ELink
    (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (True, False, False, False, True, True, False, False)),
      EmptyString)))), (String ((Ascii (True, False, False, False, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (InitialStateEClass,
      (Obj.magic (BuildInitialState ((String ((Ascii (True, False, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))))))), (Cons ((Build_HSMMetamodel_ELink
    (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (True, False, False, False, True, True, False, False)),
      EmptyString)))), (String ((Ascii (True, False, False, False, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (CompositeStateEClass,
      (Obj.magic (BuildCompositeState ((String ((Ascii (False, False, True,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))))))), (Cons ((Build_HSMMetamodel_ELink
    (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, True, False, False, True, True, False, False)),
      EmptyString)))), (String ((Ascii (False, True, False, False, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (InitialStateEClass,
      (Obj.magic (BuildInitialState ((String ((Ascii (False, True, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))))))), (Cons ((Build_HSMMetamodel_ELink
    (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, True, False, False, True, True, False, False)),
      EmptyString)))), (String ((Ascii (False, True, False, False, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, True, False,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))))))), (Cons ((Build_HSMMetamodel_ELink
    (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (True, True, False, False, True, True, False, False)), EmptyString)))),
      (String ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))), (BuildAbstractState (CompositeStateEClass,
      (Obj.magic (BuildCompositeState ((String ((Ascii (False, False, True,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))))))), (Cons ((Build_HSMMetamodel_ELink
    (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (True, True, False, False, True, True, False, False)), EmptyString)))),
      (String ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))), (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))))))), (Cons ((Build_HSMMetamodel_ELink
    (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (False, False, False, False, True, True, False,
      False)), EmptyString)))))))), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), EmptyString)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))))))), (Cons ((Build_HSMMetamodel_ELink
    (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (False, False, False, False, True, True, False,
      False)), EmptyString)))))))), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, False, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (False, False, False, False, True, True, False,
      False)), EmptyString)))))))))), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, False, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (False, False, False, False, True, True, False,
      False)), EmptyString)))))))))), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (False, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, False, True, False,
      True, True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (False, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, False, True, False,
      True, True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, True, False, True,
        True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (True, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, True, False, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, True, False, True,
        True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (True, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, True, False, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, True, False, True,
        True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (False, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, True, False, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, True, False, True,
        True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (False, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, True, False, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, True, False, True,
        True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (True, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, True, False, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, True, False, True,
        True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (True, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, True, False, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, False, True,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (False, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, False, False, True,
      True, True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, False, True,
        True, True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (False, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, False, False, True,
      True, True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, True, True,
        True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (True, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, True, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, True, True,
        True, False, False)), EmptyString)))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      (String ((Ascii (True, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, True, True,
      True, False, False)), EmptyString)))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))))),
      (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))))),
      (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, True, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, True, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, True, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, True, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, False, True,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, False, True,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, False, True,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, False, True,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, True, True,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, True, True,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, True, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, True, True, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, True, True, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, True, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        True, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False, True,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        True, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False, True,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        True, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, True,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        False, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, False, False, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        True, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, False, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, True,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))))),
      (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))))),
      (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, True, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, True, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, True, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, True, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, False, True,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, False, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, False, True,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, False, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, False, True,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (True, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, False, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, False, True,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (True, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, False, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, True, True,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (False, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, True, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, True, True,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (False, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, True, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, True, True, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (True, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, True, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, True, True, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (True, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, True, True, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        True, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False, True,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        True, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (False, False, False, True,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        True, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, True,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, True, False, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        True, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, True, False, False,
      True, True, False, False)), (String ((Ascii (True, False, False, True,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, False, False, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, False, False, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (False, False, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, False, False, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (True, False, False, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, False, False, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (True, False, False, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, True, False, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (False, True, False, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, True, False, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (False, True, False, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, True, False, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (True, True, False, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, True, False, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (True, True, False, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, False, True, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (False, False, True, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, False, True, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (False, False, True, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, False, True, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (True, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (True, False, True, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, False, True, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (True, False, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (True, False, True, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, True, True, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (False, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (False, True, True, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, True, True, False,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (False, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (False, True, True, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, True, True, False, True,
        True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (True, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (True, True, True, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, True, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, True, True, False, True,
        True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (True, True, True, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (True, True, True, False, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, False, False, True,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (False, False, False, True, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (False, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (False, False, False, True,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (False, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (False, False, False, True, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, False, False, True,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (True, False, False, True, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (True,
        True, False, False, True, True, False, False)), (String ((Ascii
        (True, False, False, True, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (True, True, False, False, True,
        True, False, False)), (String ((Ascii (True, False, False, True,
        True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)), (String
      ((Ascii (True, False, False, True, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (True, True, False, False, True,
      True, False, False)), (String ((Ascii (True, False, False, True, True,
      True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, False, True, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))))),
      (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (False, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (False, False, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)), (String
      ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, False, True, False,
      True, True, False, False)), (String ((Ascii (False, False, False,
      False, True, True, False, False)), EmptyString)))))),
      (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, False, True, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (True, False, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (True, False, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)), (String
      ((Ascii (True, False, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, False, True, False,
      True, True, False, False)), (String ((Ascii (True, False, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (False, True, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, False, True, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (False, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (False, True, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)), (String
      ((Ascii (False, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, False, True, False,
      True, True, False, False)), (String ((Ascii (False, True, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (True, True, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionSourceEReference,
    (Obj.magic (BuildTransitionSource ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, False, True, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (True, True, False, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (True, True, False,
        False, True, True, False, False)), EmptyString)))))))))))))), (Cons
    ((Build_HSMMetamodel_ELink (TransitionTargetEReference,
    (Obj.magic (BuildTransitionTarget ((BuildTransition ((String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, False, False)), (String
      ((Ascii (False, False, True, False, True, True, False, False)), (String
      ((Ascii (True, True, False, False, True, True, False, False)),
      EmptyString)))))))))), (String ((Ascii (False, False, True, False,
      True, True, False, False)), (String ((Ascii (True, True, False, False,
      True, True, False, False)), EmptyString)))))), (BuildAbstractState
      (RegularStateEClass,
      (Obj.magic (BuildRegularState ((String ((Ascii (True, False, True,
        False, False, False, True, False)), (String ((Ascii (False, False,
        False, False, True, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, False, False)), (String ((Ascii
        (False, False, True, False, True, True, False, False)),
        EmptyString)))))))), (String ((Ascii (False, False, True, False,
        True, True, False, False)), (String ((Ascii (False, False, True,
        False, True, True, False, False)), EmptyString)))))))))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

