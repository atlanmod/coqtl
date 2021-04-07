Require Import String.
Require Import Bool.
Require Import Nat.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.Utils.

Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Model.
Require Import core.EqDec.

Require Import TT2BDD.TT.
Require Import TT2BDD.BDD.

(* In this example, we try to explore that
   - we can write transformation without reflection
   - 
 *)


  Definition isColumn (e: TTElem) :=
    match e with
    | BuildColumn _ _ => true
    | _ => false
    end.

  Definition guard (sp: list TTElem) := 
      match hd_error sp with
      | Some e => isColumn e
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

  Definition times (lv : nat) := pow 2 lv.

  Definition iter_col (sp: list TTElem) := 
    match hd_error sp with
    | Some e => match (Column_Level e) with
                | None => 0
                | Some lv => lv
                end
    | _ => 0
    end.
    
  Definition oelem_name (sp: list TTElem) (iter: nat) := 
    match hd_error sp with
    | Some e => append (Column_Name e) (natToString iter)
    | _ => ""%string
    end.

  Definition upper_level (sp: list TTElem) := 
    match hd_error sp with
    | Some e => match (Column_Level e) with
                | None => None
                | Some n => Some (n - 1)
                end 
    | _ => None
    end.

  Definition locate (m: Model TTElem TTRef) (lv: nat) := 
    find (fun e => match (Column_Level e) with
            | None => false
            | Some n => Nat.eqb n lv
            end) (allModelElements m).

  Definition div_roundup (a b : nat) :=
    match modulo a b with
    | 0 => a / b
    | _ => (a / b) + 1
    end.

  Definition TTEq (a b : TTElem) := 
    match a, b with
    | BuildColumn n1 l1, BuildColumn n2 l2 => String.eqb n1 n2 && Nat.eqb l1 l2
    | BuildRow lst1 n1, BuildRow lst2 n2 => list_beq nat Nat.eqb lst1 lst2 && Nat.eqb n1 n2
    | _,_ => false
    end.

  Instance TTEqDec : EqDec TTElem := {
    eqb := TTEq
  }.

  Definition isRow (e: TTElem) :=
    match e with
    | BuildRow _ _ => true
    | _ => false
    end.

  Definition guard_row (sp: list TTElem) := 
    match hd_error sp with
    | Some e => isRow e
    | _ => false
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

  Definition output_name (sp: list TTElem) := 
    match hd_error sp with
    | Some e => match (Row_Output e) with
                | None => ""%string
                | Some str => append "S_" str
                end 
    | _ => ""%string
    end.

  Require Import Coq.Lists.List.
  Require Import Coq.Init.Nat.

  Definition list_max (l:list nat) := fold_right max 0 l.

  Definition maxLv (m: Model TTElem TTRef) := list_max (optionList2List (map Column_Level (allModelElements m))).
  
  Fixpoint semantic (input: list nat) : nat :=
    match input with
    | nil => 0
    | a :: r => a * pow 2 ((length input)-1) + semantic r
    end.

  (* Eval compute in semantic (0::0::1::nil). *)

Definition TT2BDD :=
  @buildTransformation 
    TTElem TTRef BDDNode BDDEdge  (* source target elem ref types *)
    1 (* max arity *)
    [ (* rules *)
     (buildRule "Columns2Tree"  
        (fun m col => Some (guard col))  
        (fun m col => Some (iter_col col))
        [buildOutputPatternElement "node"
            (fun i m col => Some (BuildBDDNode (oelem_name col i)))
            [buildOutputPatternElementReference
              (fun tls i m col output => 
                ulv <- (upper_level col);
                ucol <- locate m ulv;
                parent <- resolveIter' tls m "node" [ucol] (div_roundup i 2);
                Some (BuildBDDEdge output parent))]
        ]
      ) ;
      (buildRule "Row2Output"  
        (fun m row => Some (guard_row row))  
        (fun m row => Some 1)
        [buildOutputPatternElement "output"
            (fun i m row => Some (BuildBDDNode (output_name row)))
            [buildOutputPatternElementReference
              (fun tls i m sp output => 
                height <- Some (maxLv m);           (* get depth *)
                col <- locate m height;             (* get node of depth *)
                row <- hd_error sp;
                input <- (Row_Input row);
                parent <- resolveIter' tls m "node" [col] (div_roundup (semantic input) 2);   (* attach output to the corresponding leaf node*)
                Some (BuildBDDEdge output parent) ) ]
        ]
      )
    ]. 
