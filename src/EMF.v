Section EMF.

(* Coq libraries *)

Require Import List.      (* sequence *)
Require Import String.
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import ZArith.

Open Scope Z_scope.

(* EMF Definitions *)

Inductive CONTAINMENT : Set := 
	| IsCONTAINMENT : CONTAINMENT
	| OTHER : CONTAINMENT
.

Inductive 
  EAttribute (X: Type) : Type :=
    | BuildEAttribute : X -> EAttribute X
.

Inductive 
  EReference (C: CONTAINMENT) (LOW: Z) (UP: Z) (X: Type) : Type :=
    | BuildEReference : X -> EReference C LOW UP X
.

(* EMF teminologies *)
Definition EClass := Set.

Definition EInt := EAttribute nat.

Definition EBool := EAttribute bool.

Definition EString := EAttribute string.


(* Example *)
Inductive
  ERSchema : EClass :=
  BuildERSchema :
    (*oid*) EInt ->
    (*name*) EInt ->
    (*entities*) EReference IsCONTAINMENT (0) (- 1) (list Entity) -> ERSchema
with
  Entity : EClass :=
  BuildEntity :
    (*oid*) EInt ->  Entity
.

End EMF.