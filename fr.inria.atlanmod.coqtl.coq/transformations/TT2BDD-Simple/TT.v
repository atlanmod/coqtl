Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Bool.
Require Import String.
Open Scope string.

(* Option 1 *)

Inductive Table1:= 
  BuildTable1: list string -> string -> list nat -> Table1.

Definition t1: Table1:=
  BuildTable1
    ("a"::"b"::nil) "c"
    (0::0::1::
     0::1::0::nil).

(* Option 2 *)

Inductive Table2:= 
  BuildTable2 :
     list string -> string -> list (prod (list nat) nat) -> Table2.

Definition t2: Table2:=
  BuildTable2 
    ("a"::"b"::nil) "c"
    (((0::0::nil),1)::
     ((0::1::nil),0)::nil).

(* Option 3 *)

Inductive Cell3 {rtype ctype vtype: Type}:= 
  BuildCell3: 
    (* row *) rtype ->
    (* column *) ctype -> 
    (* value *) vtype -> Cell3.

Definition Table3 (rtype ctype vtype: Type) :=
  list (@Cell3 rtype ctype vtype).

Inductive TT3 := 
  BuildTT3 : 
    (* input ports *) list string ->
    (* output port *) string ->
    (* values *) Table3 nat string bool -> TT3.

Definition t3: TT3 :=
  BuildTT3
    ("a"::"b"::nil) "c"
    ((BuildCell3 0 "a" false)::(BuildCell3 0 "b" false)::(BuildCell3 0 "c" true)::
     (BuildCell3 1 "a" false)::(BuildCell3 1 "b" true)::(BuildCell3 1 "c" false)::nil).

(* Option 4 *)

Inductive Cell4 {vtype: Type}:= 
  BuildCell4: 
    (* row *) nat ->
    (* column *) nat -> 
    (* value *) vtype -> Cell4.

Definition Table4 (vtype: Type):=
  list (@Cell4 vtype).

Inductive TT4:= 
  BuildTT4: 
    (* input ports *) list string ->
    (* output ports *) list string ->
    (* values *) Table4 bool -> TT4.

Definition t4: TT4:=
  BuildTT4
    ("a"::"b"::nil) ("c"::nil)
    ((BuildCell4 0 0 false)::(BuildCell4 0 1 false)::(BuildCell4 0 2 true )::
     (BuildCell4 1 0 false)::(BuildCell4 1 1 true )::(BuildCell4 1 2 false)::nil).

(* Option 5 *)

Inductive Table:= 
  BuildTable :
    (* input ports *) list string -> 
    (* output ports *) list string -> 
    (* values *) list (list (prod string bool)) -> Table.

Definition t: Table:=
  BuildTable
    ("a"::"b"::nil) ("c"::nil)
    ((("a", false)::("b", false)::("c", true )::nil)::
     (("a", false)::("b", true )::("c", false)::nil)::nil).

Require Import core.Model.

Definition tmodel: Model (list (prod string bool)) unit:=
  Build_Model 
  ((("a", false)::("b", false)::("c", true )::nil)::
   (("a", false)::("b", true )::("c", false)::nil)::nil) 
   nil.
