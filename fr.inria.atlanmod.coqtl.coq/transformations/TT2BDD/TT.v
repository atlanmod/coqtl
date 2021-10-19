Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.EqDec.
Require Import core.Metamodel.

Scheme Equality for list.

(* Truth Table *)

Inductive TTElem := 
| BuildColumn :  
    (* name *) string ->
    (* level start at 1 *) nat ->
    TTElem
| BuildRow :
    (* inputs *) list nat ->
    (* output *) nat ->
    TTElem.

Definition TTEq (a b : TTElem) := 
    match a, b with
    | BuildColumn n1 l1, BuildColumn n2 l2 => String.eqb n1 n2 && Nat.eqb l1 l2
    | BuildRow lst1 n1, BuildRow lst2 n2 => list_beq nat Nat.eqb lst1 lst2 && Nat.eqb n1 n2
    | _,_ => false
    end.

Instance TTEqDec : EqDec TTElem := {
    eq_b := TTEq
}.

Definition isColumn (e: TTElem) :=
    match e with
    | BuildColumn _ _ => true
    | _ => false
    end.

Definition isRow (e: TTElem) :=
    match e with
    | BuildRow _ _ => true
    | _ => false
    end.

Definition Column_Name (e : TTElem) := 
    match e with
    | BuildColumn n _ => n
    | _ => ""%string
    end.

Definition Column_Level (e : TTElem) := 
    match e with
    | BuildColumn _ lv => Some lv
    | _ => None
    end.

Definition Row_Input (e : TTElem) := 
    match e with
    | BuildRow input _ => Some input
    | _ => None
    end.

Definition Row_Output (e : TTElem) := 
    match e with
    | BuildRow _ output => Some (natToString output)
    | _ => None
    end.

Inductive TTRef :=
  unit. 

Definition evalTT (tt: Model TTElem TTRef) (ins: list bool) : bool := true.

Instance TTM : Metamodel :=
  Build_Metamodel TTElem TTRef _.