Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Semantics.

Require Import transformations.TT2BDD.TT.
Require Import transformations.TT2BDD.BDD.
Require Import transformations.TT2BDD.TT2BDDAbstract.
Require Import transformations.TT2BDD.tests.TTModel.

Print TT2BDD.


Definition BDDNode_name (n: BDDNode) := 
    match n with
    | BuildBDDNode name => name
    end.

Definition BDDEq (a b : BDDNode) := 
    match a, b with
    | BuildBDDNode n1, BuildBDDNode n2 => String.eqb n1 n2
    end.

Fixpoint BDDNode_parent (n: BDDNode) (tl: list BDDEdge) : option BDDNode := 
    match tl with
    | nil => None
    | l::r => 
        match l with
        | BuildBDDEdge c p => if BDDEq n c then Some p else BDDNode_parent n r
        end 
    end.

Fixpoint well_defined (e: BDDNode) (tm: Model BDDNode BDDEdge) (leaf: bool):=
    match leaf with
    | true => 
        match (BDDNode_parent e (allModelLinks tm)) with
            | None => false
            | Some p => well_defined p tm false (* p is at the right pos, and p's parent is well defined *)
        end
    | false => true  (* p is at the right pos, and p's parent is well defined *)
    end. 

Theorem semantic_eq:
  forall (sm: Model TTElem TTRef) (se: TTElem), 
    (In se (allModelElements sm)) -> 
      (isRow se) = true ->
        (exists (te:BDDNode),
          (BDDNode_name te) = output_name [se] /\ well_defined te (execute TT2BDD sm) true = true
        )
.