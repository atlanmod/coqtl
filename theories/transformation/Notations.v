Require Import coqtl.transformation.CoqTL.

(** * Notations **)

(* Module *)
Notation "'transformation' tname 'from' sinstance 'to' tinstance 'with' m 'as' smodel ':=' transformationbody" := (fun (tname: Phase sinstance tinstance)  (m:smodel) => transformationbody ) (right associativity, at level 60).

(* Rules *)
Notation "'[' r1 ; .. ; r2 ']'" := (cons r1 .. (cons r2 nil) ..) (right associativity, at level 9).

(* Rule *)
Notation "'rule' rulename 'from' rbody" := (rbody) (right associativity, at level 60).

(* InputPatternElement *)
Notation "'element' sid 'class' stype ',' sbody" := (BuildMultiElementRule stype (fun sid => sbody)) (right associativity, at level 60).

(* InputPatternElement *)
Notation "'element' sid 'class' stype 'from' sinstance 'when' guard 'to' outputels" := (BuildSingleElementRule sinstance stype (fun sid => (guard, outputels))) (right associativity, at level 60).

(* OutputPatternElement *)
Notation "'output' elid 'element' elname 'class' eltype 'from' tinstance := eldef 'links' refdef" := (BuildOutputPatternElement eltype elid eldef (fun elname => refdef))  (right associativity, at level 60).

(* OutputPatternElementReferenceDefinition *)
Notation "'reference' reftype 'from' tinstance ':=' refends" := (BuildOutputPatternElementReference tinstance reftype refends) (right associativity, at level 60).