
  

  Require Import List.
  
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