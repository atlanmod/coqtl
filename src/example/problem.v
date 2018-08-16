Require Import Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.



Inductive A: Set :=
| mkA: nat -> A.

Definition getNat_A (a: A) :=
  match a with
   | mkA n => n
  end.

Inductive X: Set :=
| r1 : A -> X.

Definition Instantiated_X (x : X) : bool :=
  match x with
  | r1 a => (getNat_A a) > 10
  end.
  
Definition iX : Set := {x:X | (Instantiated_X x)}.

Program Definition r1_rewrite : A -> option iX :=
fun a: A =>
 match (Instantiated_X (r1 a)) with 
  | true => Some (exist _ (r1 a) _)
  | false => None
 end.

Example r1_rewrite_surj: 
forall t : iX,
exists (a : A),
  match (r1_rewrite a) with
   | None => True
   | Some e => eq t e
  end.
Proof.
move=> [[a] Pa]; exists a; rewrite /r1_rewrite.
move: (erefl _). 
rewrite {1 3}Pa.
by move=> e; rewrite (eq_irrelevance (r1_rewrite_obligation_1 _ _) Pa).
Qed.
      
      
(* Other definitions remain the same *)
Definition r1_rewrite' a : option iX := insub (r1 a).

Example r1_rewrite_surj2:
forall t : iX, exists (a : A),
 match (r1_rewrite' a) with
 | None => True
 | Some e => eq t e
 end.
Proof.
move=> [[a] Pa]. exists a. rewrite /r1_rewrite' insubT. done.
Qed.      
