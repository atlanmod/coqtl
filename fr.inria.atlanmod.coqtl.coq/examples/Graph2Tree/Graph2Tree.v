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
Open Scope coqtl.


Definition rootNode (m : GraphModel) : Node :=
  hd (GraphMetamodel_defaultInstanceOfEClass NodeEClass)
     (GraphMetamodel_allInstances NodeEClass m).

Definition last' (l: list Node) : option Node := hd_error (rev l).



Fixpoint allPathsFix (m: GraphModel) (l : nat) (path: list Node) :  list (list Node) :=
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
  end.

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
              (concat  (map (fun child: Node => 
                        allPathsFix' m l' ([child]) ) children))
      end
    end
  | 0 => [ path ]
  end.

Definition allPaths (m : GraphModel) (l : nat) : list (list Node) :=
  allPathsFix' m l [ rootNode m ].


Definition allPathsStartWith (m : GraphModel) (l : nat) (o: Node) : list (list Node) :=
  filter (fun p =>
            match p with
            | h :: t => beq_Node h o
            | nil => false
            end
         ) (allPaths m l).

Compute (allPaths PersonModel 2).







(* Definition step (m: ClassModel) (c: Class) : option (list Class) :=
  attrs <- getClassAttributes c m;
  return
  concat
    (map
       (fun a => match getAttributeType a m with
              | Some cls => [ cls ]
              | None => nil
              end
       ) attrs). 


 










Fixpoint eq_Class (c1 c2: Class): bool :=
  match c1, c2 with 
   | BuildClass a1 a2, BuildClass b1 b2 => beq_string a1 b1 && beq_string a2 b2
  end.


Fixpoint eq_list (l1 l2: list Class): bool :=
  match l1, l2 with 
   | nil, nil => true
   | a::l1', b::l2' => eq_Class a b && eq_list l1' l2'
   | _, _ => false
  end.

Fixpoint index (l : list Class) (ll : list (list Class)) : option nat :=
  match ll with
   | nil => None
   | a :: lll => if eq_list l a then Some 0 else 
     match (index l lll) with
      | None => None
      | Some n => Some (1 + n)
     end
  end.


Fixpoint resolveAllIter (tr: TransformationA ClassMetamodel ClassMetamodel) (sm:ClassModel) (name: string) 
  (type: ClassMetamodel_EClass) (sps: list Class) (iters: list (list Class)) (forSection : list (list Class))
   : (list (Metamodel.denoteModelClass type)).
Proof.
destruct sps eqn: sps_ca.
- exact ( nil).
- destruct iters eqn: iters_ca.
  -- exact ( nil).
  -- destruct (index l0 forSection) eqn: id_ca.
     + destruct (resolveIter tr sm name type [[ c ]] n) eqn:it_ca.
       ++ exact ( (d :: (resolveAllIter tr sm name type l l1 forSection))).
       ++ exact (resolveAllIter tr sm name type l l1 forSection).
     + exact (resolveAllIter tr sm name type l l1 forSection).
Defined.

(* id <- index path (allPathsTo m 3 c);  should be id <- index path (getForSection (matchPattern tr m [[c]])); 
   The problem now is that find_OutputPatternElementA did not return any result
 *)
Definition ClassGraph2Tree' :=
  transformation ClassGraph2Tree from ClassMetamodel to ClassMetamodel
    with m as ClassModel := [

      rule Class2Class
        from
          c class ClassEClass
        for
          i in (allPathsTo m 1 c)
        to [
          "att" :
            a' class AttributeEClass :=
              BuildAttribute newId false (getClassName c)
            with [
              ref AttributeTypeEReference :=
                path <- i;
                path_id <- index path (allPathsTo m 1 c); 
                cls <- resolveIter (parsePhase ClassGraph2Tree) m "cl" ClassEClass [[ c ]] path_id;
                return BuildAttributeType a' cls
            ];
          "cl" :
            c' class ClassEClass :=
              BuildClass newId (getClassName c)
            with [
              ref ClassAttributesEReference :=
                path <- i;
                cls <- step m c;
                let attrs := resolveAllIter (parsePhase ClassGraph2Tree) m "att" AttributeEClass cls (nextPaths m path) (allPathsTo m 1 c) in
                  return BuildClassAttributes c' attrs
            ] 
        ]
       
    ].




Close Scope coqtl.

Definition ClassGraph2Tree := parseTransformation ClassGraph2Tree'. *)