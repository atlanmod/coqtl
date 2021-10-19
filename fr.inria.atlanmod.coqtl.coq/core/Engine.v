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
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.EqDec.
Require Import core.TransformationConfiguration.

Scheme Equality for list.

Set Implicit Arguments.

Class TransformationSyntax (tc: TransformationConfiguration) := {
    (** ** Syntax *)
    Transformation: Type;
    Rule: Type;
    OutputPatternElement: Type;
    TraceLink: Type;

    (** ** Accessors *)

    Transformation_getRules: Transformation -> list Rule;
    Transformation_getArity: Transformation -> nat;
  
    Rule_getOutputPatternElements: Rule -> list OutputPatternElement;

    TraceLink_getSourcePattern: TraceLink -> list SourceModelElement;
    TraceLink_getIterator: TraceLink -> nat;
    TraceLink_getName: TraceLink -> string;
    TraceLink_getTargetElement: TraceLink -> TargetModelElement;    

    evalOutputPatternElementExpr: SourceModel -> list SourceModelElement -> nat -> OutputPatternElement -> option TargetModelElement;
    evalIteratorExpr: Rule -> SourceModel -> list SourceModelElement -> nat;
    evalOutputPatternLinkExpr: SourceModel -> list SourceModelElement -> TargetModelElement -> nat -> list TraceLink -> OutputPatternElement -> option (list TargetModelLink);
    evalGuardExpr: Rule->SourceModel->list SourceModelElement->option bool;
}.
  
Class TransformationEngine (tc: TransformationConfiguration) (ts: TransformationSyntax tc) :=
  {
    (** ** allTuples *)

    allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
      tuples_up_to_n (allModelElements sm) (Transformation_getArity tr);

    (** ** Functions *)
    
    execute: Transformation -> SourceModel -> TargetModel;
    
    matchPattern: Transformation -> SourceModel -> list SourceModelElement -> list Rule;
    matchRuleOnPattern: Rule -> SourceModel -> list SourceModelElement -> bool;

    instantiatePattern: Transformation -> SourceModel -> list SourceModelElement -> list TargetModelElement;
    instantiateRuleOnPattern: Rule -> SourceModel -> list SourceModelElement -> list TargetModelElement; 
    instantiateIterationOnPattern: Rule -> SourceModel -> list SourceModelElement -> nat -> list TargetModelElement;
    instantiateElementOnPattern: OutputPatternElement -> SourceModel -> list SourceModelElement -> nat -> option TargetModelElement;
    
    applyPattern: Transformation -> SourceModel -> list SourceModelElement -> list TargetModelLink;
    applyRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> list TargetModelLink;
    applyIterationOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> nat -> list TargetModelLink;
    applyElementOnPattern: OutputPatternElement -> Transformation -> SourceModel -> list SourceModelElement -> nat -> list TargetModelLink;
    
    trace: Transformation -> SourceModel -> list TraceLink; 

    resolveAll: forall (tr: list TraceLink) (sm: SourceModel) (name: string)
             (sps: list(list SourceModelElement)) (iter: nat),
        option (list TargetModelElement);
    resolve: forall (tr: list TraceLink) (sm: SourceModel) (name: string)
             (sp: list SourceModelElement) (iter : nat), option TargetModelElement;

    (** ** Theorems *)

    (** ** allTuples *)

    allTuples_incl:
      forall (sp : list SourceModelElement) (tr: Transformation) (sm: SourceModel), 
        In sp (allTuples tr sm) -> incl sp (allModelElements sm);

    (** ** execute *)

    tr_execute_in_elements :
      forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
      In te (allModelElements (execute tr sm)) <->
      (exists (sp : list SourceModelElement),
          In sp (allTuples tr sm) /\
          In te (instantiatePattern tr sm sp));

    tr_execute_in_links :
      forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
        In tl (allModelLinks (execute tr sm)) <->
        (exists (sp : list SourceModelElement),
            In sp (allTuples tr sm) /\
            In tl (applyPattern tr sm sp));

    (** ** matchPattern *)

    tr_matchPattern_in :
       forall (tr: Transformation) (sm : SourceModel),
         forall (sp : list SourceModelElement)(r : Rule),
           In r (matchPattern tr sm sp) <->
             In r (Transformation_getRules tr) /\
             matchRuleOnPattern r sm sp = true;

    (** ** matchRuleOnPattern *)

    tr_matchRuleOnPattern_leaf :
    forall (tr: Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
      matchRuleOnPattern r sm sp =
       match evalGuardExpr r sm sp with Some true => true | _ => false end;

    (** ** instantiatePattern *)

    tr_instantiatePattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
        In te (instantiatePattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In te (instantiateRuleOnPattern r sm sp));

    (** ** instantiateRuleOnPattern *)

    tr_instantiateRuleOnPattern_in :
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
      In te (instantiateRuleOnPattern r sm sp) <->
      (exists (i: nat),
          In i (seq 0 (evalIteratorExpr r sm sp)) /\
          In te (instantiateIterationOnPattern r sm sp i));

   (** ** instantiateIterationOnPattern *)

    tr_instantiateIterationOnPattern_in : 
      forall (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement) (i:nat),
        In te (instantiateIterationOnPattern r sm sp i)
        <->
        (exists (ope: OutputPatternElement),
            In ope (Rule_getOutputPatternElements r) /\ 
            instantiateElementOnPattern ope sm sp i = Some te);

    (** ** instantiateElementOnPattern *)

    tr_instantiateElementOnPattern_leaf:
        forall (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat),
          instantiateElementOnPattern o sm sp iter = evalOutputPatternElementExpr sm sp iter o;

    (** ** applyPattern *)

    tr_applyPattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
        In tl (applyPattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In tl (applyRuleOnPattern r tr sm sp));

    (** ** applyRuleOnPattern *)

    tr_applyRuleOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
        In tl (applyRuleOnPattern r tr sm sp) <->
        (exists (i: nat),
            In i (seq 0 (evalIteratorExpr r sm sp)) /\
            In tl (applyIterationOnPattern r tr sm sp i));

    (** ** applyIterationOnPattern *)

    tr_applyIterationOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat),
        In tl (applyIterationOnPattern r tr sm sp i) <->
        (exists (ope: OutputPatternElement),
            In ope (Rule_getOutputPatternElements r) /\ 
            In tl (applyElementOnPattern ope tr sm sp i));

    (** ** applyElementOnPattern *)

    tr_applyElementOnPattern_leaf : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (te: TargetModelElement) 
             (i:nat) (ope: OutputPatternElement),
        evalOutputPatternElementExpr sm sp i ope = Some te ->
        applyElementOnPattern ope tr sm sp i = optionListToList (evalOutputPatternLinkExpr sm sp te i (trace tr sm) ope);

    (** ** resolve *)

    tr_resolveAll_in:
    forall (tls: list TraceLink) (sm: SourceModel) (name: string)
           (sps: list(list SourceModelElement)) (iter: nat)
      (te: TargetModelElement),
      (exists tes: list TargetModelElement,
          resolveAll tls sm name sps iter = Some tes /\ In te tes) <->
      (exists (sp: list SourceModelElement),
          In sp sps /\
          resolve tls sm name sp iter = Some te);

    tr_resolve_leaf:
    forall (tls:list TraceLink) (sm : SourceModel) (name: string)
      (sp: list SourceModelElement) (iter: nat) (x: TargetModelElement),
      resolve tls sm name sp iter = return x ->
       (exists (tl : TraceLink),
         In tl tls /\
         Is_true (list_beq SourceModelElement SourceElement_eqb (TraceLink_getSourcePattern tl) sp) /\
         ((TraceLink_getIterator tl) = iter) /\ 
         ((TraceLink_getName tl) = name)%string /\
         (TraceLink_getTargetElement tl) = x);
         
  }.
