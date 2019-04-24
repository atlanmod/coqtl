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

  (** * Abstract Syntax **)

  (** ** Expression Types **)
  
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

  (** ** Syntax Types **)
  
  Inductive MatchedOutputPatternElement (InElTypes: list SourceModelClass) (IterType: Type) : Type := 
    BuildMatchedOutputPatternElement :
      string ->
      forall (OutType:TargetModelClass),
       (IterType -> SourceModel -> (outputPatternElementTypes InElTypes OutType)) ->
       MatchedOutputPatternElement InElTypes IterType.
  
  Inductive MatchedRule : Type := 
    BuildMatchedRule :
      string ->
      forall (InElTypes: list SourceModelClass),
        (SourceModel -> (guardTypes InElTypes))
        -> forall (IterType: Type),
        (SourceModel -> (iteratedListTypes InElTypes IterType))
        -> list (MatchedOutputPatternElement InElTypes IterType)
        -> MatchedRule.
  
  Inductive MatchedTransformation : Type := 
    BuildMatchedTransformation :
      list MatchedRule ->
      MatchedTransformation.
  
  Inductive OutputPatternElementReference (InElTypes: list SourceModelClass) (IterType: Type) (OutType:TargetModelClass): Type :=
    BuildOutputPatternElementReference :
      forall (OutRef: TargetModelReference),
        (MatchedTransformation -> IterType -> SourceModel -> (outputReferenceTypes InElTypes OutType OutRef)) ->
        OutputPatternElementReference InElTypes IterType OutType.

  Inductive OutputPatternElement (InElTypes: list SourceModelClass) (IterType: Type) : Type := 
    BuildOutputPatternElement :
      string ->
      forall (OutType:TargetModelClass),
       (IterType -> SourceModel -> (outputPatternElementTypes InElTypes OutType)) ->
       list (OutputPatternElementReference InElTypes IterType OutType)-> OutputPatternElement InElTypes IterType.
  
  Inductive Rule : Type := 
    BuildRule :
      string ->
      forall (InElTypes: list SourceModelClass),
        (SourceModel -> (guardTypes InElTypes))
        -> forall (IterType: Type),
        (SourceModel -> (iteratedListTypes InElTypes IterType))
        -> list (OutputPatternElement InElTypes IterType)
        -> Rule.
  
  Inductive Transformation : Type := 
    BuildTransformation :
      list Rule ->
      Transformation.

  (** ** Accessors **)

  Definition OutputPatternElementReference_getRefType {InElTypes: list SourceModelClass} {IterType: Type} {OutType:TargetModelClass} (o: OutputPatternElementReference InElTypes IterType OutType) : TargetModelReference :=
    match o with 
      BuildOutputPatternElementReference _ _ _ y _ => y
    end.

  Definition OutputPatternElementReference_getOutputReference {InElTypes: list SourceModelClass} {IterType: Type} {OutType:TargetModelClass} (o: OutputPatternElementReference InElTypes IterType OutType) :
    MatchedTransformation -> IterType -> SourceModel -> (outputReferenceTypes InElTypes OutType (OutputPatternElementReference_getRefType o)).
  Proof.
    destruct o eqn:ho.
    exact o0.
  Defined.
  
  Definition OutputPatternElement_getName {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) : string :=
    match o with 
      BuildOutputPatternElement _ _ y _ _ _ => y
    end.

  Definition OutputPatternElement_getOutType {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) : TargetModelClass :=
    match o with 
      BuildOutputPatternElement _ _ _ y _ _ => y
    end.  

  Definition OutputPatternElement_getOutPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) :
    IterType -> SourceModel -> (outputPatternElementTypes InElTypes (OutputPatternElement_getOutType o)) :=
    match o with 
      BuildOutputPatternElement _ _ _ _ y _ => y
    end.

  Definition OutputPatternElement_getOutputElementReferences {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) :
    list (OutputPatternElementReference InElTypes IterType (OutputPatternElement_getOutType o)) :=
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

  Definition Rule_getGuard (x : Rule) :
    SourceModel -> (guardTypes (Rule_getInTypes x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition Rule_getIteratorType (x : Rule) : Type :=
    match x with
      BuildRule _ _ _ y _ _ => y
    end.
  
  Definition Rule_getIteratedList (x: Rule) :
    SourceModel -> (iteratedListTypes (Rule_getInTypes x) (Rule_getIteratorType x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.
  
  Definition Rule_getOutputPattern (x : Rule) :
    list (OutputPatternElement (Rule_getInTypes x) (Rule_getIteratorType x)) :=
    match x with
      BuildRule _ _ _ _ _ y => y
    end.
  
  Definition Transformation_getRules (x : Transformation) : list Rule :=
    match x with BuildTransformation y => y end.
  
  Definition MatchedOutputPatternElement_getName {InElTypes: list SourceModelClass} {IterType: Type} (o: MatchedOutputPatternElement InElTypes IterType) : string :=
    match o with 
      BuildMatchedOutputPatternElement _ _ y _ _ => y
    end.

  Definition MatchedOutputPatternElement_getOutType {InElTypes: list SourceModelClass} {IterType: Type} (o: MatchedOutputPatternElement InElTypes IterType) : TargetModelClass :=
    match o with 
      BuildMatchedOutputPatternElement _ _ _ y _ => y
    end.  

  Definition MatchedOutputPatternElement_getOutPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (o: MatchedOutputPatternElement InElTypes IterType) :
    IterType -> SourceModel -> (outputPatternElementTypes InElTypes (MatchedOutputPatternElement_getOutType o)) :=
    match o with 
      BuildMatchedOutputPatternElement _ _ _ _ y => y
    end.

  Definition MatchedRule_getName (x : MatchedRule) : string :=
    match x with 
      BuildMatchedRule y _ _ _ _ _ => y
    end.

  Definition MatchedRule_getInTypes (x : MatchedRule) : list SourceModelClass :=
    match x with
      BuildMatchedRule _ y _ _ _ _ => y
    end.

  Definition MatchedRule_getGuard (x : MatchedRule) :
    SourceModel -> (guardTypes (MatchedRule_getInTypes x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition MatchedRule_getIteratorType (x : MatchedRule) : Type :=
    match x with
      BuildMatchedRule _ _ _ y _ _ => y
    end.
  
  Definition MatchedRule_getIteratedList (x: MatchedRule) :
    SourceModel -> (iteratedListTypes (MatchedRule_getInTypes x) (MatchedRule_getIteratorType x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.
  
  Definition MatchedRule_getOutputPattern (x : MatchedRule) :
    list (MatchedOutputPatternElement (MatchedRule_getInTypes x) (MatchedRule_getIteratorType x)) :=
    match x with
      BuildMatchedRule _ _ _ _ _ y => y
    end.
  
  Definition MatchedTransformation_getRules (x : MatchedTransformation) : list MatchedRule :=
    match x with BuildMatchedTransformation y => y end.

  (** * Semantics **)
  
  (** ** Expression Evaluation **)
  
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
    list (Rule_getIteratorType r).
  Proof.
    destruct r eqn:hr.
    exact (evalIteratorFix InElTypes IterType (i sm) sp).
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

  Definition evalOutputPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (sm: SourceModel) (sp: list SourceModelElement) (iter: IterType) (o: OutputPatternElement InElTypes IterType) 
    : option TargetModelElement :=
    evalOutputPatternElementFix InElTypes (OutputPatternElement_getOutType o) ((OutputPatternElement_getOutPatternElement o) iter sm) sp.

  Fixpoint evalOutputPatternElementReferenceFix (intypes: list SourceModelClass) (ot: TargetModelClass) (or: TargetModelReference) (oe: TargetModelElement) (f: outputReferenceTypes intypes ot or) (el: list SourceModelElement) : option TargetModelLink.
  Proof.
    destruct intypes eqn:intypes1, el eqn:el1.
    - exact None.
    - exact None.
    - exact None.
    - destruct l eqn:intypes2, l0 eqn:el2.
      + destruct (toModelClass s s0) eqn:tmc.
        * destruct (toModelClass ot oe) eqn:tmct.
          -- destruct ((f d) d0) eqn:tml.
             ++ exact (Some (toModelLink or d1)).
             ++ exact None.
          -- exact None.
        * exact None.
      + exact None.
      + exact None.
      + destruct (toModelClass s s0) eqn:tmc.
        * rewrite <- intypes2 in f.
          exact (evalOutputPatternElementReferenceFix l ot or oe (f d) l0).
        * exact None.
  Defined.

  Definition evalOutputPatternElementReference
             {InElTypes: list SourceModelClass} {IterType: Type} {TargetType: TargetModelClass}
             (sm: SourceModel) (sp: list SourceModelElement) (oe: TargetModelElement) (iter: IterType) (tr: MatchedTransformation)
             (o: OutputPatternElementReference InElTypes IterType TargetType) 
    : option TargetModelLink :=
    evalOutputPatternElementReferenceFix InElTypes TargetType (OutputPatternElementReference_getRefType o) oe ((OutputPatternElementReference_getOutputReference o) tr iter sm) sp.

  (** ** Rule application **)
  
  Definition matchRuleOnPattern (r: Rule) (sm : SourceModel) (sp: list SourceModelElement) : option bool :=
    evalGuard r sm sp.

  Definition matchPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list Rule :=
    filter (fun (r:Rule) =>
              match matchRuleOnPattern r sm sp with
              | (Some true) => true
              | _ => false end) (Transformation_getRules tr).

  Definition instantiateRuleOnPatternIter (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : option (list TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (nth_error (evalIterator r sm sp) iter) with
        | Some i => 
             Some (optionList2List (map (evalOutputPatternElement sm sp i) (Rule_getOutputPattern r)))
        | None => None
        end
      else
        None.
  
  Definition instantiateRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (optionList2List (concat
                (map (fun f => map f (Rule_getOutputPattern r))
                     (map (evalOutputPatternElement sm sp) (evalIterator r sm sp)))))
      else
        None.

  Definition instantiatePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    match matchPattern tr sm sp with
    | nil => None
    | l => Some (concat (optionList2List (map (fun r => instantiateRuleOnPattern r sm sp) l)))
    end.

  Definition applyOutputPatternElementOnPatternIter
             (r: Rule)
             (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r))
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) : option (list TargetModelLink):=             
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (nth_error (evalIterator r sm sp) iter) with
        | Some i =>
          match (evalOutputPatternElement sm sp i ope) with
          | Some l => 
            Some (optionList2List (map ( fun (oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope))
                        => evalOutputPatternElementReference sm sp l i (BuildMatchedTransformation nil) oper
                      )
                      (OutputPatternElement_getOutputElementReferences ope)))
          | None => None
          end
        | None => None
        end
      else
        None.
  
  Definition applyRuleOnPatternIter (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : option (list TargetModelLink) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (nth_error (evalIterator r sm sp) iter) with
        | Some i => 
          Some (concat (optionList2List (map (fun x => applyOutputPatternElementOnPatternIter r x tr sm sp iter) (Rule_getOutputPattern r))))
        | None => None
        end
      else
        None.

  Definition applyRuleOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement): option (list TargetModelLink) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (concat (optionList2List (map (applyRuleOnPatternIter r tr sm sp) (indexes (length (evalIterator r sm sp))))))
      else
        None.

  Definition applyPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelLink) :=
    match matchPattern tr sm sp with
    | nil => None
    | l => Some (concat (optionList2List (map (fun r => applyRuleOnPattern r tr sm sp) l)))
    end.

  (** ** Rule scheduling **)
  
  Definition maxArity (tr: Transformation) : nat :=
    max (map (length (A:=SourceModelClass)) (map Rule_getInTypes (Transformation_getRules tr))).
    
  Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (allModelElements sm) (maxArity tr).

  (** TODO **)
  Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
    Build_Model
      (concat (optionList2List (map (instantiatePattern tr sm) (allTuples tr sm))))
      (concat (optionList2List (map (applyPattern tr sm) (allTuples tr sm)))).

End CoqTL.

Arguments MatchedTransformation: default implicits.

Arguments BuildTransformation
          [SourceModelElement] [SourceModelLink] [SourceModelClass] [SourceModelReference] _
          [TargetModelElement] [TargetModelLink] [TargetModelClass] [TargetModelReference] _.
Arguments BuildRule
          [SourceModelElement] [SourceModelLink] [SourceModelClass] [SourceModelReference] _
          [TargetModelElement] [TargetModelLink] [TargetModelClass] [TargetModelReference] _.
Arguments BuildOutputPatternElement
          [SourceModelElement] [SourceModelLink] [SourceModelClass] [SourceModelReference] _
          [TargetModelElement] [TargetModelLink] [TargetModelClass] [TargetModelReference] _
          _ [IterType].
Arguments BuildOutputPatternElementReference
          [SourceModelElement] [SourceModelLink] [SourceModelClass] [SourceModelReference] _
          [TargetModelElement] [TargetModelLink] [TargetModelClass] [TargetModelReference] _
          _ [IterType].

Arguments execute: default implicits.
