Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Engine.
Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.


Section CoqTL.

  Variables (SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type)
            (smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference)
            (TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type)
            (tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference).
  
  Definition SourceModel := Model SourceModelElement SourceModelLink.
  Definition TargetModel := Model TargetModelElement TargetModelLink.

  (** ** Abstract Syntax **)

  Fixpoint outputReferenceTypes
            (sclasses : list SourceModelClass) (tclass: TargetModelClass)  (tref: TargetModelReference):=
    match sclasses with
    | nil => (denoteModelClass tclass) -> (option (denoteModelReference tref))
    | cons class classes' => (denoteModelClass class) -> outputReferenceTypes classes' tclass tref
    end.
 
  Fixpoint outputPatternElementTypes
            (sclasses : list SourceModelClass) (tclass: TargetModelClass) :=
    match sclasses with
    | nil => (denoteModelClass tclass)
    | cons class classes' =>
      (denoteModelClass class) ->
      outputPatternElementTypes classes' tclass
    end.

  Fixpoint iteratedListTypes
           (sclasses : list SourceModelClass) (itype: Type) :=
    match sclasses with
    | nil => list itype
    | cons class classes' =>
      (denoteModelClass class) ->
      iteratedListTypes classes' itype
    end.

  Fixpoint guardTypes (classes : list SourceModelClass) :=
    match classes with
    | nil => bool
    | cons class classes' => (denoteModelClass class) -> guardTypes classes'
    end.
    
  Inductive MatchedOutputPatternElement : Type := 
    BuildMatchedOutputPatternElement :
      string ->
      forall (InElTypes: list SourceModelClass),
      forall (t:TargetModelClass),
      forall (IterType: Type),
        (IterType -> SourceModel -> (outputPatternElementTypes InElTypes t))
        -> MatchedOutputPatternElement.
  
  Inductive MatchedRule : Type := 
    BuildMatchedRule :
      string ->
      forall (InElTypes: list SourceModelClass),
        (SourceModel -> (guardTypes InElTypes))
        -> forall (t: Type),
        option (SourceModel -> (iteratedListTypes InElTypes t))
        -> list MatchedOutputPatternElement
        -> MatchedRule.
  
  Inductive MatchedTransformation : Type := 
    BuildMatchedTransformation :
      list MatchedRule ->
      MatchedTransformation.
  
  Inductive OutputPatternElementReference : Type :=
    BuildOutputPatternElementReference :
      forall (InElTypes: list SourceModelClass),
      forall (t:TargetModelClass),
      forall (IterType: Type),
      forall (OutRef: TargetModelReference),
        (MatchedTransformation -> IterType -> SourceModel -> (outputReferenceTypes InElTypes t OutRef)) ->
        OutputPatternElementReference.

  Inductive OutputPatternElement : Type := 
    BuildOutputPatternElement :
      string ->
      forall (InElTypes: list SourceModelClass),
      forall (t:TargetModelClass),
      forall (IterType: Type),
       (IterType -> SourceModel -> (outputPatternElementTypes InElTypes t)) ->
       list OutputPatternElementReference -> OutputPatternElement.   
  
  Inductive Rule : Type := 
    BuildRule :
      string ->
      forall (InElTypes: list SourceModelClass),
        (SourceModel -> (guardTypes InElTypes))
        -> forall (t: Type),
        option (SourceModel -> (iteratedListTypes InElTypes t))
        -> list OutputPatternElement
        -> Rule.
  
  Inductive Transformation : Type := 
    BuildTransformation :
      list Rule ->
      Transformation.

  (** ** Accessors **)
  Definition OutputPatternElement_getName (o: OutputPatternElement) : string :=
    match o with 
      BuildOutputPatternElement y _ _ _ _ _ => y
    end.

  Definition OutputPatternElement_getInTypes (o: OutputPatternElement) : list SourceModelClass :=
    match o with 
      BuildOutputPatternElement _ y _ _ _ _ => y
    end.

  Definition OutputPatternElement_getOutType (o: OutputPatternElement) : TargetModelClass :=
    match o with 
      BuildOutputPatternElement _ _ y _ _ _ => y
    end.  

  Definition OutputPatternElement_getIteratorType (o: OutputPatternElement) : Type :=
    match o with 
      BuildOutputPatternElement _ _ _ y _ _ => y
    end.

  Definition OutputPatternElement_getOutPatternElement (o: OutputPatternElement) :
    ((OutputPatternElement_getIteratorType o) ->
     SourceModel ->
     (outputPatternElementTypes
        (OutputPatternElement_getInTypes o)
        (OutputPatternElement_getOutType o))) :=
    match o with 
      BuildOutputPatternElement _ _ _ _ y _ => y
    end.

  Definition OutputPatternElement_getOutputElementReferences (o: OutputPatternElement) : list OutputPatternElementReference :=
    match o with 
      BuildOutputPatternElement _ _ _ _ _ y => y
    end.

  Definition Rule_getName (x : Rule) : string :=
    match x with 
      BuildRule y _ _ _ _ _ => y
    end.

  Definition Rule_getInTypes (x : Rule) : list SourceModelClass :=
    match x with
      BuildRule _ y _ _ _ _ => y
    end.

  Definition Rule_getGuard (x : Rule) : SourceModel -> (guardTypes (Rule_getInTypes x)).
  Proof.
    destruct x.
    - unfold Rule_getInTypes.
      assumption.
  Defined.

  Definition Rule_getIteratorType (x : Rule) : Type :=
    match x with
      BuildRule _ _ _ y _ _ => y
    end.
  
  Definition Rule_getIteratedList (x: Rule) : option (SourceModel -> (iteratedListTypes (Rule_getInTypes x) (Rule_getIteratorType x))).
  Proof.
    destruct x eqn:hx.
    - unfold Rule_getInTypes.
      unfold Rule_getIteratorType.
      assumption.
  Defined.
  
  Definition Rule_getOutputPattern (x : Rule) : list OutputPatternElement :=
    match x with
      BuildRule _ _ _ _ _ y => y
    end.
  
  Definition Transformation_getRules (x : Transformation) : list Rule :=
    match x with BuildTransformation y => y end.

  (** ** Rule matching **)
  Fixpoint evalGuardFix  (intypes: list SourceModelClass) (f: guardTypes intypes) (el: list SourceModelElement) : option bool.
  Proof.
    destruct intypes eqn:intypes1, el eqn:el1.
    - exact None.
    - exact None.
    - exact None.
    - destruct l eqn:intypes2, l0 eqn:el2.
      + destruct (toModelClass s s0) eqn:tmc.
        * exact (Some (f d)).
        * exact None.
      + exact None.
      + exact None.
      + destruct (toModelClass s s0) eqn:tmc.
        * rewrite <- intypes2 in f.                    
          exact (evalGuardFix l (f d) l0).
        * exact None.
  Defined.

  Definition evalGuard (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
    evalGuardFix (Rule_getInTypes r) ((Rule_getGuard r) sm) sp.

  Fixpoint evalIteratorFix  (intypes: list SourceModelClass) (ot: Type) (f: iteratedListTypes intypes ot) (el: list SourceModelElement) : list ot.
  Proof.
    destruct intypes eqn:intypes1, el eqn:el1.
    - exact nil.
    - exact nil.
    - exact nil.
    - destruct l eqn:intypes2, l0 eqn:el2.
      + destruct (toModelClass s s0) eqn:tmc.
        * exact (f d).
        * exact nil.
      + exact nil.
      + exact nil.
      + destruct (toModelClass s s0) eqn:tmc.
        * rewrite <- intypes2 in f.                    
          exact (evalIteratorFix l ot (f d) l0).
        * exact nil.
  Defined.
  
  Definition evalIterator (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) :
    option (list (Rule_getIteratorType r)).
  Proof.
    destruct r eqn:hr.
    destruct o eqn:ho.
    - exact (Some (evalIteratorFix InElTypes t (i sm) sp)).
    - exact None.
  Defined.

  Fixpoint evalOutputPatternElementFix (intypes: list SourceModelClass) (ot: TargetModelClass) (f: outputPatternElementTypes intypes ot) (el: list SourceModelElement) : option TargetModelElement.
  Proof.
    destruct intypes eqn:intypes1, el eqn:el1.
    - exact None.
    - exact None.
    - exact None.
    - destruct l eqn:intypes2, l0 eqn:el2.
      + destruct (toModelClass s s0) eqn:tmc.
        * exact (Some (toModelElement ot (f d))).
        * exact None.
      + exact None.
      + exact None.
      + destruct (toModelClass s s0) eqn:tmc.
        * rewrite <- intypes2 in f.
          exact (evalOutputPatternElementFix l ot (f d) l0).
        * exact None.
  Defined.

  Definition evalOutputPatternElement (o : OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: OutputPatternElement_getIteratorType o) : option TargetModelElement :=
    evalOutputPatternElementFix (OutputPatternElement_getInTypes o) (OutputPatternElement_getOutType o) ((OutputPatternElement_getOutPatternElement o) iter sm) sp.
  
  Definition matchRuleOnPattern (r: Rule) (sm : SourceModel) (sp: list SourceModelElement) : option bool :=
    evalGuard r sm sp.

  Definition matchPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list Rule :=
    filter (fun (r:Rule) =>
              match matchRuleOnPattern r sm sp with
              | (Some true) => true
              | _ => false end) (Transformation_getRules tr).

  (** TODO **)
  Definition instantiateRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match evalIterator r sm sp with
        | None => None
        | Some x => None
        end
      else
        None.
  
  (** ** Rule scheduling **)
  
  Definition maxArity (tr: Transformation) : nat :=
    max (map (length (A:=SourceModelClass)) (map Rule_getInTypes (Transformation_getRules tr))).
    
  Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (allModelElements sm) (maxArity tr).

  (** TODO **)
  Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
    Build_Model
      (concat (optionList2List nil))
      (concat (optionList2List nil)).

End CoqTL.

Arguments MatchedTransformation: default implicits.

Arguments BuildTransformation [SourceModelElement] [SourceModelLink] [SourceModelClass]
     [SourceModelReference] _ [TargetModelElement] [TargetModelLink] [TargetModelClass]
 [TargetModelReference] _.
Arguments BuildRule [SourceModelElement] [SourceModelLink] [SourceModelClass]
     [SourceModelReference] _ [TargetModelElement] [TargetModelLink] [TargetModelClass]
 [TargetModelReference] _.
Arguments BuildOutputPatternElement [SourceModelElement] [SourceModelLink] [SourceModelClass]
     [SourceModelReference] _ [TargetModelElement] [TargetModelLink] [TargetModelClass]
 [TargetModelReference] _.
Arguments BuildOutputPatternElementReference [SourceModelElement] [SourceModelLink] [SourceModelClass]
     [SourceModelReference] _ [TargetModelElement] [TargetModelLink] [TargetModelClass]
 [TargetModelReference] _.