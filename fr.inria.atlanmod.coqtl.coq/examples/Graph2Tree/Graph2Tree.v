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


Fixpoint resolveAllIter (tr': Phase GraphMetamodel GraphMetamodel) (sm:GraphModel) (name: string) 
  (type: GraphMetamodel_EClass) (sps: list Node) (path: (list Node)) (depth: nat)
   : option (list (Metamodel.denoteModelClass type)) :=
    let tr := (parsePhase tr') in
      match sps with 
      | sp :: sps' =>
        let extendedPath := path ++ [sp] in
          match index (list Node) (list_eq_dec GraphMetamodel_Node_dec) extendedPath (allPathsTo sm depth sp) with
           | Some nb => 
            match (resolveIter tr sm name type [[ sp ]] nb) with
             | Some res => l <- (resolveAllIter tr' sm name type sps' path depth);
                            return (res :: l)
             | None => (resolveAllIter tr' sm name type sps' path depth)
            end
           | None => (resolveAllIter tr' sm name type sps' path depth)
          end
      | nil  => Some nil
      end.




Definition Graph2Tree' :=
  transformation Graph2Tree from GraphMetamodel to GraphMetamodel
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
                children' <- (resolveAllIter Graph2Tree m "n" NodeEClass children pth 2);
                return BuildNodeEdges n' children'
            ]
        ]
    ].


Close Scope coqtl.



Definition Graph2Tree := parseTransformation Graph2Tree'. 


