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

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.

Set Implicit Arguments.

Class TransformationEngineTrace :=
  {
    SourceModelElement: Type;
    SourceModelClass: Type;
    SourceModelLink: Type;
    SourceModelReference: Type;
    TargetModelElement: Type;
    TargetModelClass: Type;
    TargetModelLink: Type;
    TargetModelReference: Type;

    smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference;
    tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference;

    SourceModel := Model SourceModelElement SourceModelLink;
    TargetModel := Model TargetModelElement TargetModelLink;

    Transformation: Type;
    Rule: Type;
    OutputPatternElement: Type;
    OutputPatternElementReference: Type;

    TraceLink: Type;

    (** ** Accessors *)

    getRules: Transformation -> list Rule;

    getInTypes: Rule -> list SourceModelClass;    
    getGuardExpr: Rule -> (SourceModel -> (list SourceModelElement) -> option bool);
    getOutputPatternElements: Rule -> list OutputPatternElement;

    getName: OutputPatternElement -> string;
    getOutputElementReferences: OutputPatternElement -> list OutputPatternElementReference;

    buildTraceLink: (list SourceModelElement * nat * string) -> TargetModelElement -> TraceLink;
    TraceLink_getSourcePattern: TraceLink -> list SourceModelElement;
    TraceLink_getIterator: TraceLink -> nat;
    TraceLink_getName: TraceLink -> string;
    TraceLink_getTargetElement: TraceLink -> TargetModelElement;

    (** ** maxArity *)

    maxArity (tr: Transformation) : nat :=
      max (map (length (A:=SourceModelClass)) (map getInTypes (getRules tr)));

    allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
      tuples_up_to_n (allModelElements sm) (maxArity tr);

    (** ** Functions *)




    executeTraces: Transformation -> SourceModel -> TargetModel;

    matchPattern: Transformation -> SourceModel -> list SourceModelElement -> list Rule;

    instantiateTraces: Transformation -> SourceModel -> (list TargetModelElement * list TraceLink);
    trace: Transformation -> SourceModel -> list TraceLink; 
    tracePattern: Transformation -> SourceModel -> list SourceModelElement -> list TraceLink;
    traceRuleOnPattern: Rule -> SourceModel -> list SourceModelElement -> list TraceLink;
    traceIterationOnPattern: Rule -> SourceModel -> list SourceModelElement -> nat -> list TraceLink;
    traceElementOnPattern: OutputPatternElement -> SourceModel -> list SourceModelElement -> nat -> option TraceLink;
    instantiateElementOnPattern: OutputPatternElement -> SourceModel -> list SourceModelElement -> nat -> option TargetModelElement;

    applyTraces: Transformation -> SourceModel -> list TraceLink -> list TargetModelLink;
    applyPatternTraces: Transformation -> SourceModel -> list SourceModelElement -> list TraceLink -> list TargetModelLink;
    applyRuleOnPatternTraces: Rule -> Transformation -> SourceModel -> list SourceModelElement -> list TraceLink -> list TargetModelLink;
    applyIterationOnPatternTraces: Rule -> Transformation -> SourceModel -> list SourceModelElement -> nat -> list TraceLink -> list TargetModelLink;
    applyElementOnPatternTraces: OutputPatternElement -> Transformation -> SourceModel -> list SourceModelElement -> nat -> list TraceLink -> list TargetModelLink;
    applyReferenceOnPatternTraces: OutputPatternElementReference -> Transformation -> SourceModel -> list SourceModelElement -> nat -> TargetModelElement -> list TraceLink -> option TargetModelLink;

    evalOutputPatternElementExpr: SourceModel -> list SourceModelElement -> nat -> OutputPatternElement -> option TargetModelElement;
    evalIteratorExpr: Rule -> SourceModel -> list SourceModelElement -> nat;
    evalOutputPatternLinkExpr: SourceModel -> list SourceModelElement -> TargetModelElement -> nat -> list TraceLink -> OutputPatternElementReference -> option TargetModelLink;



    (** ** Theorems *)

    (** ** execute *)

    tr_executeTraces_in_elements :
      forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
        In te (allModelElements (executeTraces tr sm)) <->
        In te (fst (instantiateTraces tr sm));

    tr_executeTraces_in_links :
      forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
        In tl (allModelLinks (executeTraces tr sm)) <->
        In tl (applyTraces tr sm (trace tr sm));

    (** ** instantiate *)

    tr_instantiateTraces_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
        In te (fst (instantiateTraces tr sm)) <->
        (exists (tl : TraceLink),
            In tl (trace tr sm) /\
            te = (TraceLink_getTargetElement tl) );

    tr_trace_in:
      forall (tr: Transformation) (sm : SourceModel) (tl : TraceLink),
        In tl (trace tr sm) <->
        (exists (sp : list SourceModelElement),
            In sp (allTuples tr sm) /\
            In tl (tracePattern tr sm sp));

    tr_tracePattern_in:
      forall (tr: Transformation) (sm : SourceModel) (sp : list SourceModelElement) (tl : TraceLink),
        In tl (tracePattern tr sm sp) <->
        (exists (r:Rule),
            In r (matchPattern tr sm sp) /\
            In tl (traceRuleOnPattern r sm sp));

    tr_traceRuleOnPattern_in:
      forall (r: Rule) (sm : SourceModel) (sp : list SourceModelElement) (tl : TraceLink),
        In tl (traceRuleOnPattern r sm sp) <->
        (exists (iter: nat),
            In iter (indexes (evalIteratorExpr r sm sp)) /\
            In tl (traceIterationOnPattern r sm sp iter));

    tr_traceIterationOnPattern_in:
      forall (r: Rule) (sm : SourceModel) (sp : list SourceModelElement) (iter: nat) (tl : TraceLink),
        In tl (traceIterationOnPattern r sm sp iter) <->
        (exists (o: OutputPatternElement),
            In o (getOutputPatternElements r) /\
            In tl ((fun o => optionToList (traceElementOnPattern o sm sp iter)) o));

    tr_traceElementOnPattern_in:
      forall (o: OutputPatternElement) (sm : SourceModel) (sp : list SourceModelElement) (iter: nat) (o: OutputPatternElement) (tl : TraceLink),
        Some tl = (traceElementOnPattern o sm sp iter) <->
        (exists (e: TargetModelElement),
           Some e = (instantiateElementOnPattern o sm sp iter) /\
           tl = (buildTraceLink (sp, iter, getName o) e));

    tr_instantiateElementOnPattern_leaf:
        forall (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat),
          instantiateElementOnPattern o sm sp iter = evalOutputPatternElementExpr sm sp iter o;


    (** ** applyPattern *)

    tr_applyTraces_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (tls: list TraceLink),
        In tl (applyTraces tr sm tls) <->
        (exists (sp : list SourceModelElement),
            In sp (allTuples tr sm) /\
            In tl (applyPatternTraces tr sm sp tls));

    tr_applyPatternTraces_in:
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (tls: list TraceLink),
        In tl (applyPatternTraces tr sm sp tls) <->
        (exists (r : Rule),
                In r (matchPattern tr sm sp) /\
                In tl (applyRuleOnPatternTraces r tr sm sp tls));

    tr_applyRuleOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (tls: list TraceLink),
          In tl (applyRuleOnPatternTraces r tr sm sp tls) <->
          (exists (i: nat),
              In i (indexes (evalIteratorExpr r sm sp)) /\
              In tl (applyIterationOnPatternTraces r tr sm sp i tls));

    tr_applyIterationOnPattern_in : 
          forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat)  (tls: list TraceLink),
            In tl (applyIterationOnPatternTraces r tr sm sp i tls) <->
            (exists (ope: OutputPatternElement),
                In ope (getOutputPatternElements r) /\ 
                In tl (applyElementOnPatternTraces ope tr sm sp i tls));

    tr_applyElementOnPatternTraces_in : 
          forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) 
                 (i:nat) (ope: OutputPatternElement)  (tls: list TraceLink),
            In tl (applyElementOnPatternTraces ope tr sm sp i tls) <->
            (exists (oper: OutputPatternElementReference) (te: TargetModelElement),
                In oper (getOutputElementReferences ope) /\ 
                (evalOutputPatternElementExpr sm sp i ope) = Some te /\
                applyReferenceOnPatternTraces oper tr sm sp i te tls = Some tl);

    tr_applyReferenceOnPatternTraces_leaf : 
          forall (oper: OutputPatternElementReference)
                 (tr: Transformation)
                 (sm: SourceModel)
                 (sp: list SourceModelElement) (iter: nat) (te: TargetModelElement) (tls: list TraceLink),
            applyReferenceOnPatternTraces oper tr sm sp iter te tls  = evalOutputPatternLinkExpr sm sp te iter tls oper;


  }.
