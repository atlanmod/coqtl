
  

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

Inductive listf : Type :=
    | BuildNext: forall t:SourceModelClass, (denoteModelClass t-> listf) -> listf
    | BuildLast: forall t:Type, (nat -> t) -> listf.

  Fixpoint getListType (l: listf) (n: list SourceModelElement) : Type :=
    match l, n with
    | BuildNext T l1,  e::els=> 
       match  toModelClass T e with 
         | Some e' => getListType (l1 e') els
         | None => Error
       end
    | @BuildLast T t, _ => T
    | _, _ => nat
    end.

  (*Compute (BuildNext (BuildNext (BuildLast (fun n => 5)))).*)

  Fixpoint evalListF (l : listf) (n: list SourceModelElement) : option (getListType l n) :=
    match l, n with
    | BuildNext T l', e::els => 
       match  toModelClass T e with 
         | Some e' => evalListF (l' e') els
         | None => None
       end
    | _, _ => None
    end.