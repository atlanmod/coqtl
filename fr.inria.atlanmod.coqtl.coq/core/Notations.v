Require Import core.CoqTL.
Require Import String.
Require Import List.

(** * Notations **)

(* Module *)
Notation "'transformation' tname 'from' sinstance 'to' tinstance 'uses' itinstance 'with' m 'as' smodel ':=' transformationbody" :=
  (fun (tname: Phase sinstance tinstance itinstance) (m:smodel) =>  transformationbody)
    (right associativity,
     tname at next level,
     sinstance at next level,
     tinstance at next level,
     itinstance at next level,
     m at next level,
     smodel at next level,
     at level 60): coqtl.

(* Rules *)
Notation "'[' r1 ; .. ; r2 ']'" :=
  (cons r1 .. (cons r2 nil) ..)
    (right associativity, at level 9): coqtl.

(* Rule *)
Notation "'rule' rulename 'from' rbody" :=
  (""%string, (rbody))
    (right associativity, at level 60): coqtl.

(* InputPatternElement *)
Notation "sid 'class' stype 'from' sinstance ',' sbody" :=
  (BuildMultiElementRule stype (fun sid => sbody))
    (right associativity, at level 60): coqtl.

(* InputPatternElement no guard *)
Notation "sid 'class' stype 'for' forid 'in' forset 'itclass' ftype 'to' outputels" :=
  (BuildSingleElementRule _ _ stype ftype (fun sid => (true, forset)) (fun sid forid => outputels))
    (right associativity, at level 60): coqtl.

(* InputPatternElement *)
Notation "sid 'class' stype 'when' guard 'for' forid 'in' forset 'itclass' ftype 'to' outputels" :=
  (BuildSingleElementRule _ _ stype ftype (fun sid => (guard, forset)) (fun sid forid => outputels))
    (right associativity, at level 60): coqtl.

(* (* InputPatternElement no guard *)
Notation "sid 'class' stype 'to' outputels" :=
  (BuildSingleElementRule _ stype (fun sid => (true, 0::nil)) (fun sid forid => outputels))
    (right associativity, at level 60): coqtl.

(* InputPatternElement *)
Notation "sid 'class' stype 'when' guard 'to' outputels" :=
  (BuildSingleElementRule _ stype (fun sid => (guard, 0::nil)) (fun sid forid => outputels))
    (right associativity, at level 60): coqtl. *)

(* OutputPatternElement *)
Notation "elid ':' elname 'class' eltype := eldef 'with' refdef" :=
  (BuildOutputPatternElement eltype elid eldef (fun elname => refdef))
    (right associativity, at level 60,
     elname at next level,
     eltype at next level,
     eldef at next level,
     refdef at next level): coqtl.

(* OutputPatternElement *)
Notation "elid ':' elname 'class' eltype := eldef" :=
  (BuildOutputPatternElement eltype elid eldef (fun elname => nil))
    (right associativity, at level 60,
     elname at next level,
     eltype at next level,
     eldef at next level): coqtl.

(* OutputPatternElementReferenceDefinition *)
Notation "'ref' reftype ':=' refends" :=
  (BuildOutputPatternElementReference _ reftype refends)
    (right associativity, at level 60,
     reftype at next level): coqtl.