Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.
Require Import DecimalNat.
Require Import DecimalString.


Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.Model.
Require Import core.CoqTL.

Require Import examples.Graph2Tree.GraphMetamodel.
Require Import examples.Graph2Tree.GraphMetamodelPattern.
Require Import examples.Graph2Tree.GraphModel.
Require Import examples.Graph2Tree.GraphModel2.

Open Scope coqtl.


Definition rootNode (m : GraphModel) : Node :=
  hd (GraphMetamodel_defaultInstanceOfEClass NodeEClass)
     (GraphMetamodel_allInstances NodeEClass m).

Definition last' (l: list Node) : option Node := hd_error (rev l).

Fixpoint allPathsFix' (m: GraphModel) (l : nat) (path: list Node) :  list (list Node) :=
  match l with
  | S l' => 
    match (last' path) with
    | None => [ path ]
    | Some leaf =>
      match getNodeEdges leaf m with
      | None => [ path ]
      | Some children =>
              (concat  (map (fun child: Node => 
                        allPathsFix' m l' (path ++ [child]) ) children)) ++
              [ path ]
      end
    end
  | 0 => [ path ]
  end. 

Definition allPaths (m : GraphModel) (l : nat) : list (list Node) :=
  allPathsFix' m l [ rootNode m ].


Definition allPathsTo (m : GraphModel) (l : nat) (o: Node) : list (list Node) :=
  filter (fun p =>
            match (last' p) with
             | Some lastNode => beq_Node lastNode o
             | None => false
            end
         ) (allPaths m l).


Fixpoint indexIters (sm:GraphModel) (sps: list Node) (iters: list (list Node)) : list nat :=
  match sps, iters with 
  | sp :: sps', iter::iters' =>
    match index (list_eq_dec GraphMetamodel_Node_dec) iter (allPathsTo sm 2 sp) with
    | Some nb => nb :: indexIters sm sps' iters'
    | None => indexIters sm sps' iters'
    end
  | nil, _  => nil
  | _ , nil => nil
  end.


(*
Definition Graph2Tree' :=
  transformation Graph2Tree decreases v from GraphMetamodel to GraphMetamodel
    with m as GraphModel := [
      rule Node2Node
        from
          n class NodeEClass
        for
          i in (allPathsTo m 2 n)
        to [
          "n" :
            n' class NodeEClass :=
              BuildNode newId (getNodeName n)
            with [
              ref NodeEdgesEReference :=
                pth <- i; 
                children <- getNodeEdges n m;
                iters <- Some (map (app pth) (singletons children));
                match v with
                  | 0 => None
                  | S v' => children' <- (resolveAllIter (parseTransformation (Graph2Tree v')) m "n" NodeEClass (map (fun sp: Node => [[ sp ]] ) children) ((indexIters m children iters)));
                                  return BuildNodeEdges n' children'
                end

            ]
        ]
    ].
*)

Definition Graph2Tree' :=
  transformation Graph2Tree decreases v from GraphMetamodel to GraphMetamodel
    with m as GraphModel := [
      rule Node2Node
        from
          n class NodeEClass
        for
          i in (allPathsTo m 2 n)
        to [
          "n" :
            n' class NodeEClass :=
              BuildNode newId (getNodeName n)
            with [
              ref NodeEdgesEReference :=
                pth <- i; 
                children <- getNodeEdges n m;
                iters <- Some (map (app pth) (singletons children));
                child <- nth_error children 0;
                iter <- nth_error iters 0;
                res <- resolveIter2 (parseTransformation (Graph2Tree 0)) m "n" NodeEClass [[child]] iter;
                return BuildNodeEdges n' res :: nil
            ]
        ]
    ].



Close Scope coqtl.


Definition Graph2Tree := parseTransformation (Graph2Tree' 2). 


(* Definition test (tr: TransformationA  GraphMetamodel GraphMetamodel)(sp1: Node) (l : list Node) (m: GraphModel) := (resolveIter2 Graph2Tree m "n" NodeEClass [[ sp1 ]] l). *)
