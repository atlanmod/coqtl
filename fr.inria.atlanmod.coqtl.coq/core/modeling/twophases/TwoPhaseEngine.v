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

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Engine.
Require Import core.TransformationConfiguration.

Set Implicit Arguments.

Class TransformationEngineTrace (tc: TransformationConfiguration) (ts: TransformationSyntax tc)
 (t: TransformationEngine ts) :=
  {

    (** ** Accessors *)

    OutputPatternElement_getName: OutputPatternElement -> string;

    (* getGuardExpr: Rule -> (SourceModel -> (list SourceModelElement) -> option bool); *)

    Trace_buildTraceLink: (list SourceModelElement * nat * string) -> TargetModelElement -> TraceLink;


    (** ** Functions *)

    tracePattern: Transformation -> SourceModel -> list SourceModelElement -> list TraceLink;
    traceRuleOnPattern: Rule -> SourceModel -> list SourceModelElement -> list TraceLink;
    traceIterationOnPattern: Rule -> SourceModel -> list SourceModelElement -> nat -> list TraceLink;
    traceElementOnPattern: OutputPatternElement -> SourceModel -> list SourceModelElement -> nat -> option TraceLink;

    applyPatternTraces: Transformation -> SourceModel -> list SourceModelElement -> list TraceLink -> list TargetModelLink;
    applyRuleOnPatternTraces: Rule -> Transformation -> SourceModel -> list SourceModelElement -> list TraceLink -> list TargetModelLink;
    applyIterationOnPatternTraces: Rule -> Transformation -> SourceModel -> list SourceModelElement -> nat -> list TraceLink -> list TargetModelLink;
    applyElementOnPatternTraces: OutputPatternElement -> Transformation -> SourceModel -> list SourceModelElement -> nat -> list TraceLink -> list TargetModelLink;
    applyLinkOnPatternTraces: OutputPatternLink -> Transformation -> SourceModel -> list SourceModelElement -> nat -> TargetModelElement -> list TraceLink -> option TargetModelLink;

    (** ** Theorems *)

    (** ** execute *)

    tr_executeTraces_in_elements :
      forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
        In te (allModelElements (execute tr sm)) <->
        (exists (tl : TraceLink) (sp : list SourceModelElement),
            In sp (allTuples tr sm) /\
            In tl (tracePattern tr sm sp) /\
            te = TraceLink_getTargetElement tl);

    tr_executeTraces_in_links :
      forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
        In tl (allModelLinks (execute tr sm)) <->
            (exists (sp : list SourceModelElement),
            In sp (allTuples tr sm) /\
            In tl (applyPatternTraces tr sm sp (trace tr sm)));

    (** ** instantiate *)

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
            In iter (seq 0 (evalIteratorExpr r sm sp)) /\
            In tl (traceIterationOnPattern r sm sp iter));

    tr_traceIterationOnPattern_in:
      forall (r: Rule) (sm : SourceModel) (sp : list SourceModelElement) (iter: nat) (tl : TraceLink),
        In tl (traceIterationOnPattern r sm sp iter) <->
        (exists (o: OutputPatternElement),
            In o (Rule_getOutputPatternElements r) /\
            In tl ((fun o => optionToList (traceElementOnPattern o sm sp iter)) o));

    tr_traceElementOnPattern_leaf:
      forall (o: OutputPatternElement) (sm : SourceModel) (sp : list SourceModelElement) (iter: nat) (o: OutputPatternElement) (tl : TraceLink),
        Some tl = (traceElementOnPattern o sm sp iter) <->
        (exists (e: TargetModelElement),
           Some e = (instantiateElementOnPattern o sm sp iter) /\
           tl = (Trace_buildTraceLink (sp, iter, OutputPatternElement_getName o) e));


    (** ** applyPattern *)

    tr_applyPatternTraces_in:
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (tls: list TraceLink),
        In tl (applyPatternTraces tr sm sp tls) <->
        (exists (r : Rule),
                In r (matchPattern tr sm sp) /\
                In tl (applyRuleOnPatternTraces r tr sm sp tls));

    tr_applyRuleOnPatternTraces_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (tls: list TraceLink),
          In tl (applyRuleOnPatternTraces r tr sm sp tls) <->
          (exists (i: nat),
              In i (seq 0 (evalIteratorExpr r sm sp)) /\
              In tl (applyIterationOnPatternTraces r tr sm sp i tls));

    tr_applyIterationOnPatternTraces_in : 
          forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat)  (tls: list TraceLink),
            In tl (applyIterationOnPatternTraces r tr sm sp i tls) <->
            (exists (ope: OutputPatternElement),
                In ope (Rule_getOutputPatternElements r) /\ 
                In tl (applyElementOnPatternTraces ope tr sm sp i tls));

    tr_applyElementOnPatternTraces_in : 
          forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) 
                 (i:nat) (ope: OutputPatternElement)  (tls: list TraceLink),
            In tl (applyElementOnPatternTraces ope tr sm sp i tls) <->
            (exists (oper: OutputPatternLink) (te: TargetModelElement),
                In oper (OutputPatternElement_getOutputLinks ope) /\ 
                (evalOutputPatternElementExpr sm sp i ope) = Some te /\
                applyLinkOnPatternTraces oper tr sm sp i te tls = Some tl);

    tr_applyLinkOnPatternTraces_leaf : 
          forall (oper: OutputPatternLink)
                 (tr: Transformation)
                 (sm: SourceModel)
                 (sp: list SourceModelElement) (iter: nat) (te: TargetModelElement) (tls: list TraceLink),
            applyLinkOnPatternTraces oper tr sm sp iter te tls  = evalOutputPatternLinkExpr sm sp te iter tls oper;

  }.