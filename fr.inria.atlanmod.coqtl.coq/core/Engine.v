(************************************************************************)
(*         *   The NaoMod Development Team                              *)
(*  v      *   INRIA, CNRS and contributors - Copyright 2017-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**
 This file is the type class for relational transformation engine.
 
 We give functions signatures that instaniated transformation engines should
    generally have. We also introduce several useful theorems enforced on these 
    functions in order to certify instaniated transformation engines.

 An example instaniated transformation engine is in [core.Certification].        **)


(*********************************************************)
(** * Type Class for relational Transformation Engines   *)
(*********************************************************)

Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.TopUtils.
Require Import core.Model.
Require Import core.Expressions.
Require Import core.utils.CpdtTactics.

Set Implicit Arguments.

Class TransformationEngine :=
  {
    SourceModelElement: Type;
    SourceModelClass: Type;
    SourceModelLink: Type;
    SourceModelReference: Type;
    TargetModelElement: Type;
    TargetModelClass: Type;
    TargetModelLink: Type;
    TargetModelReference: Type;

    SourceModel := Model SourceModelElement SourceModelLink;
    TargetModel := Model TargetModelElement TargetModelLink;
    
    Transformation: Type;
    Rule: Type;
    OutputPatternElement: list SourceModelClass -> Type -> Type;
    OutputPatternElementReference: list SourceModelClass -> Type -> TargetModelClass -> Type;

    (** ** Accessors *)
    
    getRules: Transformation -> list Rule;
    getInTypes: Rule -> list SourceModelClass;
    getIteratorType: Rule -> Type;
    getOutputPattern: forall x:Rule, list (OutputPatternElement (getInTypes x) (getIteratorType x));
    getOutType (InElTypes: list SourceModelClass) (IterType: Type) (o: OutputPatternElement InElTypes IterType) : TargetModelClass;
    getOutputElementReferences: forall (InElTypes:list SourceModelClass) (IterType: Type) (o:OutputPatternElement InElTypes IterType),
        list (OutputPatternElementReference InElTypes IterType (getOutType o));

    maxArity (tr: Transformation) : nat :=
      max (map (length (A:=SourceModelClass)) (map getInTypes (getRules tr)));

    (** ** Functions *)
    
    execute: Transformation -> SourceModel -> TargetModel;
    
    matchPattern: Transformation -> SourceModel -> list SourceModelElement -> list Rule;
    matchRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> option bool;

    instantiatePattern: Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelElement);
    instantiateRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelElement); 
    instantiateIterationOnPattern: Rule -> SourceModel -> list SourceModelElement -> nat -> option (list TargetModelElement);
    instantiateElementOnPattern: forall r:Rule, OutputPatternElement (getInTypes r) (getIteratorType r) -> SourceModel -> list SourceModelElement -> nat -> option TargetModelElement;
    
    applyPattern: Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelLink);
    applyRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelLink);
    applyIterationOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> nat -> option (list TargetModelLink);
    applyElementOnPattern: forall r:Rule, OutputPatternElement (getInTypes r) (getIteratorType r) -> Transformation -> SourceModel -> list SourceModelElement -> nat -> option (list TargetModelLink);
    applyReferenceOnPattern:
      forall (r: Rule)
        (ope: OutputPatternElement (getInTypes r) (getIteratorType r))
        (oper: OutputPatternElementReference (getInTypes r) (getIteratorType r) (getOutType ope)),
        Transformation -> SourceModel -> list SourceModelElement -> nat -> option TargetModelLink;
    
    evalIterator: forall r:Rule, SourceModel -> list SourceModelElement -> list (getIteratorType r); 
    
    (** ** Theorems *)

    tr_execute_in_elements :
      forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
        In te (allModelElements (execute tr sm)) <->
        (exists (sp : list SourceModelElement) (tp : list TargetModelElement),
            incl sp (allModelElements sm) /\
            instantiatePattern tr sm sp = Some tp /\
            In te tp);

    tr_execute_in_links :
      forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
        In tl (allModelLinks (execute tr sm)) <->
        (exists (sp : list SourceModelElement) (tpl : list TargetModelLink),
            incl sp (allModelElements sm) /\
            applyPattern tr sm sp = Some tpl /\
            In tl tpl);

    tr_matchPattern_in :
       forall (tr: Transformation) (sm : SourceModel),
         forall (sp : list SourceModelElement)(r : Rule),
           In r (matchPattern tr sm sp) <->
             In r (getRules tr) /\
             matchRuleOnPattern r tr sm sp = return true;

    tr_matchPattern_None : 
        forall (tr: Transformation) (sm : SourceModel) 
          (sp: list SourceModelElement),
            length sp > maxArity tr ->
              matchPattern tr sm sp = nil;

    tr_matchRuleOnPattern_None :
        forall (tr: Transformation) (sm : SourceModel) 
          (r: Rule) (sp: list SourceModelElement),
           length sp <> length (getInTypes r) ->
            matchRuleOnPattern r tr sm sp = None;

    tr_instantiatePattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
        (exists tp: list TargetModelElement, instantiatePattern tr sm sp = Some tp /\
         In te tp) <->
        (exists (r : Rule) (tp1 : list TargetModelElement),
            In r (matchPattern tr sm sp) /\
            instantiateRuleOnPattern r tr sm sp = Some tp1 /\
            In te tp1);

   tr_instantiatePattern_non_None : 
     forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      instantiatePattern tr sm sp <> None <->
      (exists (r: Rule),
          In r (matchPattern tr sm sp) /\
          instantiateRuleOnPattern r tr sm sp <> None);
       
    tr_instantiatePattern_None : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        length sp > maxArity tr ->
        instantiatePattern tr sm sp = None;

    tr_instantiateRuleOnPattern_in :
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
        (exists tp: list TargetModelElement, instantiateRuleOnPattern r tr sm sp = Some tp /\
         In te tp) <->
        (exists (i: nat) (tp1: list TargetModelElement),
            i < length (evalIterator r sm sp) /\
            instantiateIterationOnPattern r sm sp i = Some tp1 /\
            In te tp1);

     tr_instantiateRuleOnPattern_non_None : 
     forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement),
      instantiateRuleOnPattern r tr sm sp <> None <->
      (exists (i: nat),
          i < length (evalIterator r sm sp) /\
          instantiateIterationOnPattern r sm sp i <> None);
       
    tr_instantiateIterationOnPattern_in : 
      forall (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement) (i:nat),
        (exists tp: list TargetModelElement, instantiateIterationOnPattern r sm sp i = Some tp /\
         In te tp) <->
        (exists (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
            In ope (getOutputPattern r) /\ 
            instantiateElementOnPattern ope sm sp i = Some te);

    tr_instantiateIterationOnPattern_non_None : 
     forall (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (i:nat),
      instantiateIterationOnPattern r sm sp i <> None <->
      (exists (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
          In ope (getOutputPattern r) /\ 
          instantiateElementOnPattern ope sm sp i <> None);
    
    tr_instantiateElementOnPattern_None : 
      forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
        length sp <> length (getInTypes r) ->
        instantiateElementOnPattern ope sm sp i = None;

    tr_instantiateElementOnPattern_None_iterator : 
    forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
      (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
      i >= length (evalIterator r sm sp) ->
      instantiateElementOnPattern ope sm sp i = None;
      
    tr_applyPattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
        (exists tpl: list TargetModelLink, applyPattern tr sm sp = Some tpl /\
         In tl tpl) <->
        (exists (r : Rule) (tpl1 : list TargetModelLink),
            In r (matchPattern tr sm sp) /\
            applyRuleOnPattern r tr sm sp = Some tpl1 /\
            In tl tpl1);

    tr_applyPattern_non_None : 
     forall  (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) ,
       applyPattern tr sm sp <> None <->
      (exists  (r : Rule),
         In r (matchPattern tr sm sp) /\
         applyRuleOnPattern r tr sm sp <> None);
    
    tr_applyPattern_None : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        length sp > maxArity tr ->
        applyPattern tr sm sp = None;

    tr_applyRuleOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
        (exists tpl: list TargetModelLink, applyRuleOnPattern r tr sm sp = Some tpl /\
         In tl tpl) <->
        (exists (i: nat) (tpl1: list TargetModelLink),
            i < length (evalIterator r sm sp) /\
            applyIterationOnPattern r tr sm sp i = Some tpl1 /\
            In tl tpl1);

    tr_applyRuleOnPattern_non_None : 
     forall  (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) ,
       applyRuleOnPattern r tr sm sp <> None <->
      (exists (i: nat),
        i < length (evalIterator r sm sp) /\
        applyIterationOnPattern r tr sm sp i <> None );

    tr_applyIterationOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat),
        (exists tpl: list TargetModelLink, applyIterationOnPattern r tr sm sp i = Some tpl /\
         In tl tpl) <->
        (exists (ope: OutputPatternElement (getInTypes r) (getIteratorType r)) (tpl1: list TargetModelLink),
            In ope (getOutputPattern r) /\ 
            applyElementOnPattern ope tr sm sp i = Some tpl1 /\
            In tl tpl1);

    tr_applyIterationOnPattern_non_None : 
     forall  (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (i:nat),
       applyIterationOnPattern r tr sm sp i <> None <->
      (exists (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
            In ope (getOutputPattern r) /\ 
            applyElementOnPattern ope tr sm sp i <> None);

    tr_applyElementOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat) (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
        (exists tpl: list TargetModelLink, applyElementOnPattern ope tr sm sp i = Some tpl /\
         In tl tpl) <->
        (exists (oper: OutputPatternElementReference (getInTypes r) (getIteratorType r) (getOutType ope)),
            In oper (getOutputElementReferences ope) /\ 
            applyReferenceOnPattern oper tr sm sp i = Some tl);
        
    tr_applyElementOnPattern_non_None : 
     forall  (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (i:nat) (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
       applyElementOnPattern ope tr sm sp i <> None <->
      (exists(oper: OutputPatternElementReference (getInTypes r) (getIteratorType r) (getOutType ope)),
          In oper (getOutputElementReferences ope) /\ 
          applyReferenceOnPattern oper tr sm sp i <> None);

    tr_applyReferenceOnPattern_None : 
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (getInTypes r) (getIteratorType r))
        (oper: OutputPatternElementReference (getInTypes r) (getIteratorType r) (getOutType ope)),
        length sp <> length (getInTypes r) ->
        applyReferenceOnPattern oper tr sm sp i = None;
        
    tr_applyReferenceOnPattern_None_iterator : 
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (getInTypes r) (getIteratorType r))
        (oper: OutputPatternElementReference (getInTypes r) (getIteratorType r) (getOutType ope)),
        i >= length (evalIterator r sm sp) ->
        applyReferenceOnPattern oper tr sm sp i = None;
    
    tr_maxArity_in :
    forall (tr: Transformation) (r: Rule),
      In r (getRules tr) ->
      maxArity tr >= length (getInTypes r);
    
  }.


