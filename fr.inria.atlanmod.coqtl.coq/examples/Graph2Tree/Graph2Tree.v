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
Require Import core.Metamodel.
Require Import core.Iterator.

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


Definition allPathsTo (m : GraphModel) (l : nat) (o: Node) : list (list Node) :=
  filter (fun p =>
            match (last' p) with
             | Some lastNode => beq_Node lastNode o
             | None => false
            end
         ) (allPaths m l).


(* Definition Graph2Tree' :=
  (fun (Graph2Tree: Phase GraphMetamodel_ELink GraphMetamodel_Reflective_Elem GraphMetamodel_Reflective_Elem GraphMetamodel_Reflective_Link Graph2TreeIterator_Reflective) (m:GraphModel) =>  
  [ ( ""%string,
    (BuildSingleElementRule GraphMetamodel_Reflective_Elem Graph2TreeIterator_Reflective
      NodeEClass ListNodeClass 
      (fun n => (true, (allPathsTo m 2 n)))
      (fun n i => [
        (BuildOutputPatternElement 
            GraphMetamodel_Reflective_Elem 
            NodeEClass 
            "n"%string 
            (BuildNode newId (getNodeName n))
            (fun n' => [
              BuildOutputPatternElementReference GraphMetamodel_Reflective_Link NodeEdgesEReference 
              (pth <- i; 
                children <- getNodeEdges n m;
                iters <- Some (map (app pth) (singletons children));
                children' <- resolveAllWithIter _ _ _ (parsePhase Graph2Tree) m "n"%string NodeEClass 
                               (map (fun n: Node => [[ n ]]) children) 
                               (map (fun it: list Node => Graph2TreeIterator_toEObjectOfEClass ListNodeClass it) iters);
                return BuildNodeEdges n' children')
            ]))
      ])))
  ]

  ).

Check Graph2Tree'.  *)

Definition Graph2Tree' :=
  transformation Graph2Tree 
    from GraphMetamodel
    to GraphMetamodel
    uses Graph2TreeIterator
    with m as GraphModel := [
      rule Node2Node
        from
          n class NodeEClass
        for
          i of class ListNodeClass in (allPathsTo m 2 n)
        uses
          GraphMetamodel_Reflective_Elem
        with
          Graph2TreeIterator_Reflective
        to [
          "n"%string :
            n' class NodeEClass uses GraphMetamodel_Reflective_Elem :=
              BuildNode newId (getNodeName n)
            with [
              ref NodeEdgesEReference uses GraphMetamodel_Reflective_Link :=
                pth <- i; 
                children <- getNodeEdges n m;
                iters <- Some (map (app pth) (singletons children));
                children' <- resolveAllWithIter _ _ _ (parsePhase Graph2Tree) m "n"%string NodeEClass 
                               (map (fun n: Node => [[ n ]]) children) 
                               (map (fun it: list Node => Graph2TreeIterator_toEObjectOfEClass ListNodeClass it) iters);
                return BuildNodeEdges n' children'

            ] 
        ]
    ].


Close Scope coqtl.


Definition Graph2Tree := parseTransformation (Graph2Tree'). 

