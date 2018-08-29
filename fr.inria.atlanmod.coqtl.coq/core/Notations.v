Require Import core.CoqTL.
Require Import String.


(** * Notations **)

(* Module *)
Notation "'transformation' tname 'from' sinstance 'to' tinstance 'with' m 'as' smodel ':=' transformationbody" :=
  (fun (tname: Phase sinstance tinstance)  (m:smodel) => transformationbody )
    (right associativity,
     tname at next level,
     sinstance at next level,
     tinstance at next level,
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
Notation "sid '!' stype 'from' sinstance ',' sbody" :=
  (BuildMultiElementRule stype (fun sid => sbody))
    (right associativity, at level 60): coqtl.

(* InputPatternElement no guard *)
Notation "sid '!' stype 'for' forid 'in' forset 'to' outputels" :=
  (BuildSingleElementRule _ stype (fun sid => (true, forset)) (fun sid forid => outputels))
  (right associativity, at level 60): coqtl.

(* InputPatternElement *)
Notation "sid '!' stype 'when' guard 'for' forid 'in' forset 'to' outputels" :=
  (BuildSingleElementRule _ stype (fun sid => (true, forset)) (fun sid forid => outputels))
    (right associativity, at level 60): coqtl.

(* OutputPatternElement *)
Notation "elid ':' elname '!' eltype := eldef 'with' refdef" :=
  (BuildOutputPatternElement eltype elid eldef (fun elname => refdef))
    (right associativity, at level 60,
     elname at next level,
     eltype at next level,
     eldef at next level,
     refdef at next level): coqtl.

(* OutputPatternElement *)
Notation "elid ':' elname '!' eltype := eldef" :=
  (BuildOutputPatternElement eltype elid eldef (fun elname => nil))
    (right associativity, at level 60,
     elname at next level,
     eltype at next level,
     eldef at next level): coqtl.

(* OutputPatternElementReferenceDefinition *)
Notation "'!' reftype ':=' refends" :=
  (BuildOutputPatternElementReference _ reftype refends)
    (right associativity, at level 60,
     reftype at next level): coqtl.