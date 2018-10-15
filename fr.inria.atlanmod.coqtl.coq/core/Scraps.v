Require Import List.
Require Import String.



Fixpoint fx (n: nat) : nat :=
  match n with
  | S n =>
    let
      a := (map fx (1::nil)) in 
    fx n
  | _ => 0
  end.

Print fx.


Definition fx' :=
  fix fx (n : nat) : nat := match n with
                          | 0 => 0
                          | S n0 => let a := map fx (1 :: nil) in fx n0
                          end.



Definition out_type (n : nat) : Type :=
  match n with
  | 0 => nat
  | S n => string
  end.

Fixpoint for_type (n : nat) : Type :=
  match n with
  | 0 => nat
  | S (S n) => for_type n
  | _ => string
  end.

Definition rule (n : nat) (f: for_type n) : option (out_type n) :=
  match n, f with
    | 0, 0 => Some 0
    | 0, S n => Some 1
    | S 0, "0"%string => Some "2"%string
    | S 0, _ => Some "3"%string
    | _, _ => None
  end.

Definition resolve (n : nat) (f: for_type n) : option (out_type n) :=
  rule n f.

Compute resolve 0 0.

  
  

  Require Import List.
  

Fixpoint resolveAllIter (sm: GraphModel) (sps: list Node) (iters: list (list Node))
   : option (list Node) :=
      match sps, iters with 
      | sp :: sps', iter::iters' =>
            match (resolveIter2 Graph2Tree sm "n" NodeEClass [[sp]] iter) with
             | Some res => 
                match  (resolveAllIter sm sps' iters' ) with
                | Some l => Some ( res :: l)
                | None => Some (res :: nil)
                end
             | None => (resolveAllIter sm  sps' iters' )
            end
      | nil, _  => None
      | _ , nil => None
      end.


Compute (resolveAllIter testGraphModel2 ((BuildNode "1" "A")::nil) (((BuildNode "1" "A")::(BuildNode "2" "B")::nil) :: nil)  ).

Compute (SourcePattern_getForSectionType Graph2Tree (Build_Model nil nil) "n" NodeEClass sp).



Definition sp := (Build_GraphMetamodel_EObject NodeEClass (BuildNode "1" "A"))::nil.


Definition test (tr: TransformationA  GraphMetamodel GraphMetamodel)(sp1: Node) (l : list Node) (m: GraphModel) := (resolveIter2 Graph2Tree m "n" NodeEClass [[ sp1 ]] l).

Compute (SourcePattern_getForSectionType Graph2Tree testGraphModel2 "n" NodeEClass sp).
Compute (resolveIter2 Graph2Tree testGraphModel2 "n" NodeEClass sp ((BuildNode "1" "A")::nil)).


  Definition tr (t: Type) : Set := nat.

  Inductive listf : Type :=
    | BuildNext: forall t:Type, (tr t-> listf) -> listf
    | BuildLast: forall t:Type, (nat -> t) -> listf.

  Fixpoint getListType (l: listf) (n: list nat) : Type :=
    match l, n with
    | BuildNext T l1,  e::els=> getListType (l1 e) els
    | @BuildLast T t, _ => T
    | _, _ => nat
    end.

  (*Compute (BuildNext (BuildNext (BuildLast (fun n => 5)))).*)

  Fixpoint evalListF (l : listf) (n: list nat) : option (getListType l n) :=
    match l, n with
    | BuildNext T l', e::els => evalListF (l' e) els
    | BuildLast a _, _ => None
    | _, _ => None
    end.

Definition t (n : nat) : string :=  String (ascii_of_nat n) EmptyString .

(* id <- index path (allPathsTo m 3 c);  should be id <- index path (getForSection (matchPattern tr m [[c]])); *)
Definition ClassGraph2Tree' :=
  transformation ClassGraph2Tree from ClassMetamodel to ClassMetamodel
    with m as ClassModel := [

      rule Class2Class
        from
          c class ClassEClass
        when 
          true
        for
          i in (1 :: 2 :: nil)
        to [
          "at" :
            a' class AttributeEClass := 
              match i with
              | None => BuildAttribute newId false (getClassName c)
              | Some n => BuildAttribute newId false ((getClassName c) ++ t n)
              end;
          "cl" :
            c' class ClassEClass :=
              BuildClass newId (getClassName c)
        ]
       
    ].