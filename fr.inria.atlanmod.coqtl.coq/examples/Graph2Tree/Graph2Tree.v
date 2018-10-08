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



(* Fixpoint allPathsFix (m: GraphModel) (l : nat) (path: list Node) :  list (list Node) :=
  match l with
  | S l' => 
    match (last' path) with
    | None => [ path ]
    | Some leaf =>
      match getNodeEdges leaf m with
      | None => [ path ]
      | Some children =>
       (concat  (map (fun child: Node => 
                        allPathsFix m l' (path ++ [child]) ) children))
      end
    end
  | 0 => [ path ]
  end. *)

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

(* Compute (allPaths testGraphModel2 2).

Compute (allPathsTo testGraphModel2 2 (BuildNode "2" "B")).
 *)

Fixpoint eq_list (l1 l2: list Node): bool :=
  match l1, l2 with 
   | nil, nil => true
   | a::l1', b::l2' => beq_Node a b && eq_list l1' l2'
   | _, _ => false
  end.

Fixpoint index (l : list Node) (ll : list (list Node)) : option nat :=
  match ll with
   | nil => None
   | a :: lll => if eq_list l a then Some 0 else 
     match (index l lll) with
      | None => None
      | Some n => Some (1 + n)
     end
  end.






Fixpoint resolveAllIter (tr: TransformationA GraphMetamodel GraphMetamodel) (sm:GraphModel) (name: string) 
  (type: GraphMetamodel_EClass) (sps: list Node) (path: (list Node)) (depth: nat)
   : (list (Metamodel.denoteModelClass type)) :=
    match sps with 
    | sp :: sps' =>
      let extendedPath := path ++ [sp] in
        match index extendedPath (allPathsTo sm depth sp) with
         | Some nb => 
          match (resolveIter tr sm name type [[ sp ]] nb) with
           | Some res => res :: (resolveAllIter tr sm name type sps' path depth)
           | None => (resolveAllIter tr sm name type sps' path depth)
          end
         | None => (resolveAllIter tr sm name type sps' path depth)
        end
    | nil  => nil
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
              match i with
              | None => BuildNode "Error" "Error"
              | Some path => 
                match index path (allPathsTo m 2 n) with
                 | None => BuildNode "Error" "Error"
                 | Some num => BuildNode ((getNodeId n) ++ "__" ++ (natToString num)) (getNodeName n)
                end
              end
            with [
              ref NodeEdgesEReference :=
                pth <- i; 
                children <- getNodeEdges n m;
                let children' := (resolveAllIter (parsePhase Graph2Tree) m "n" NodeEClass children pth 2) in
                  match length children' with 
                  | 0 => None
                  | S len' => return BuildNodeEdges n' children'
                  end 
            ]
        ]

    ].


Close Scope coqtl.



Definition Graph2Tree := parseTransformation Graph2Tree'. 


