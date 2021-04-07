Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Omega.
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.

(* Truth Table *)

Inductive TTElem := 
| BuildColumn :  
    (* name *) string ->
    (* level *) nat ->
    TTElem
| BuildRow :
    (* inputs *) list nat ->
    (* output *) nat ->
    TTElem.

Inductive TTRef :=
  unit. 