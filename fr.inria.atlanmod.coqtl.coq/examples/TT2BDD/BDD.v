Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Omega.
Require Import Bool.

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