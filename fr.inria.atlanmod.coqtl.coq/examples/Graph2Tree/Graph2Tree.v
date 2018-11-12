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
Require Import examples.Graph2Tree.Graph2TreeIterator.

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


Definition allPathsTo (m : GraphModel) (l : nat) (o: Node) : list (Graph2TreeIterator_Object) :=
  map (Build_Graph2TreeIterator_Object ListNodeClass)
          (filter (fun p =>
            match (last' p) with
             | Some lastNode => beq_Node lastNode o
             | None => false
            end
         ) (allPaths m l)).

Definition Graph2Tree' :=
  transformation Graph2Tree from GraphMetamodel to GraphMetamodel uses Graph2TreeIterator_Object
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
                pth1 <- i;
                pth <- Graph2TreeIterator_toEClass ListNodeClass pth1; 
                children <- getNodeEdges n m;
                iters <- Some (map (app pth) (singletons children));
                children' <- resolveAllWithIter Graph2TreeIterator (parsePhase Graph2Tree) m "n"%string NodeEClass 
                               (map (fun n: Node => [[ n ]]) children) 
                               (map (fun it: list Node => Build_Graph2TreeIterator_Object ListNodeClass it) iters);
                return BuildNodeEdges n' children'

            ]
        ]
    ].


Close Scope coqtl.


Definition Graph2Tree := parseTransformation (Graph2Tree'). 

