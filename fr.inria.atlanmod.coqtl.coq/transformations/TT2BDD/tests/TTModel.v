Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.

Require Import transformations.TT2BDD.TT.
Require Import transformations.TT2BDD.BDD.

Definition TTable_OR : Model TTElem TTRef :=
  (Build_Model
     (* elements *)
     ((BuildColumn "A" 1) :: 
      (BuildColumn "B" 2) :: 
      (BuildRow (0::0::nil) 0) ::
      (BuildRow (0::1::nil) 1) ::
      (BuildRow (1::0::nil) 1) ::
      (BuildRow (1::1::nil) 1) ::
      nil)
    (* links *)
     nil).