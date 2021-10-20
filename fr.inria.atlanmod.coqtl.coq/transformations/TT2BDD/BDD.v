Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Bool.
Require Import core.Metamodel.
Require Import core.EqDec.

Require Import core.utils.Utils.
Require Import core.Model.

(* Binary Decision Diagram (Tree) *)

Inductive BDDNode := 
  BuildBDDNode :
  (* name *) string ->
  BDDNode.

Inductive BDDEdge := 
  BuildBDDEdge :
  (* child *) BDDNode ->
  (* parent *) BDDNode ->
  BDDEdge.

Definition BDDEq (a b : BDDNode) := 
  match a, b with
  | BuildBDDNode n1, BuildBDDNode n2 => String.eqb n1 n2 
  end.

Instance BDDEqDec : EqDec BDDNode := {
    eq_b := BDDEq
}.

Instance BDDM : Metamodel :=
{
  ModelElement := BDDNode;
  ModelLink := BDDEdge;
}.