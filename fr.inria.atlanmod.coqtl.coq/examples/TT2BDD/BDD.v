Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Omega.
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.

(* Binary Decision Diagram (Tree) *)

Inductive Node := 
  BuildNode :
  (* name *) string ->
  Node.

Inductive Edge := 
  BuildEdge :
  (* Parent *) Node ->
  (* Child *) Node ->
  Edge.