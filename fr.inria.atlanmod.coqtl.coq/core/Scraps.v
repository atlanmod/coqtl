
  
  Inductive listf : Type :=
    | BuildNext: forall t:Type, (nat -> listf) -> listf
    | BuildLast: forall t:Type, (nat -> t) -> listf.

  Fixpoint getListType (l: listf) (n: nat) : Type :=
    match l, n with
    | BuildNext T l1, S n1 => getListType (l1 n1) n1
    | @BuildLast T t, _ => T
    | _, _ => nat
    end.

  (*Compute (BuildNext (BuildNext (BuildLast (fun n => 5)))).*)

  Fixpoint evalListF (l : listf) (n: nat) : option (getListType l n) :=
    match l, n with
    | BuildNext T l', S n1 => evalListF (l' n1) n1
    | BuildLast a _, _ => None
    | _, _ => None
    end.