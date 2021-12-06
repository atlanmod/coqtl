Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.

(** * Syntax

      In this section, we introduce _one possible_ abstract syntax of the CoqTL transformation engine.  
      ---- *)

Section TraceLink.

Context {tc: TransformationConfiguration}.

(** ** Traces 

        We introduce the concept of trace in the syntax to track relationship of a target element and 
        the source pattern that generates it   *)

Inductive TraceLink : Type :=
  buildTraceLink : 
    (list SourceModelElement * nat * string)
    -> TargetModelElement
    -> TraceLink.

Definition TraceLink_getSourcePattern (tl: TraceLink):=
  match tl with 
    buildTraceLink (sp, i, n) te => sp
  end.

Definition TraceLink_getIterator (tl: TraceLink):=
  match tl with 
    buildTraceLink (sp, i, n) te => i
  end.

Definition TraceLink_getName (tl: TraceLink):=
  match tl with 
    buildTraceLink (sp, i, n) te => n
  end.

Definition TraceLink_getTargetElement (tl: TraceLink):=
  match tl with 
    buildTraceLink (sp, i, n) te => te
  end.

End TraceLink.

Arguments TraceLink {_}.
