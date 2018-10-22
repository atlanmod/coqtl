Require Import core.CoqTL.
Require Import core.DefaultIterator.
Require Import String.
Require Import List.

(** * Notations **)

(* Module *)
Notation "'transformation' tname 'from1' sinstance1 'from2' sinstance2 'to1' tinstance1 'to2' tinstance2 'uses' itinstance 'with' m 'as' smodel ':=' transformationbody" :=
  (fun (tname: Phase sinstance1 sinstance2 tinstance1 tinstance2 itinstance) (m:smodel) =>  transformationbody)
    (right associativity,
     tname at next level,
     sinstance1 at next level,
     sinstance2 at next level,
     tinstance1 at next level,
     tinstance2 at next level,
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
Notation "sid 'class' stype 'for' forid 'of' 'class' ftype 'in' forset 'uses' A 'with' B 'to' outputels" :=
  (BuildSingleElementRule A B stype ftype (fun sid => (true, forset)) (fun sid forid => outputels))
    (right associativity, at level 60): coqtl.

(* InputPatternElement *)
Notation "sid 'class' stype 'when' guard 'for' forid 'of' 'class' ftype 'in' forset 'uses' A 'with' B  'to' outputels" :=
  (BuildSingleElementRule A B stype ftype (fun sid => (guard, forset)) (fun sid forid => outputels))
    (right associativity, at level 60): coqtl.

(* (* TODO InputPatternElement no FOR, guard *)
Notation "sid 'class' stype 'to2' outputels" :=
  (BuildSingleElementRule _ _ stype NatClass (fun sid => (true, 0::nil)) (fun sid forid => outputels))
    (right associativity, at level 60): coqtl.

(* TODO InputPatternElement no FOR *)
Notation "sid 'class' stype 'when2' guard 'to2' outputels" :=
  (BuildSingleElementRule _ _ stype NatClass (fun sid => (guard, 0::nil)) (fun sid forid => outputels))
    (right associativity, at level 60): coqtl.  *)

(* OutputPatternElement *)
Notation "elid ':' elname 'class' eltype 'uses' tp_elem := eldef 'with' refdef" :=
  (BuildOutputPatternElement tp_elem eltype elid eldef (fun elname => refdef))
    (right associativity, at level 60,
     elname at next level,
     eltype at next level,
     eldef at next level,
     refdef at next level): coqtl.

(* OutputPatternElement *)
Notation "elid ':' elname 'class' eltype 'uses' tp_elem := eldef" :=
  (BuildOutputPatternElement tp_elem eltype elid eldef (fun elname => nil))
    (right associativity, at level 60,
     elname at next level,
     eltype at next level,
     eldef at next level): coqtl.

(* OutputPatternElementReferenceDefinition *)
Notation "'ref' reftype 'uses' tp_link ':=' refends" :=
  (BuildOutputPatternElementReference tp_link reftype refends)
    (right associativity, at level 60,
     reftype at next level): coqtl.