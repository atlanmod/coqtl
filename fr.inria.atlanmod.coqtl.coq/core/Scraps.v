
  
  Inductive listf : Type :=
    | BuildNext: (nat -> listf) -> listf
    | BuildLast: forall t:Type, (nat -> t) -> listf.

  Fixpoint getListType (l: listf) : Type :=
    match l with
    | BuildNext l1 => getListType (l1 0)
    | @BuildLast T t => T
    end.

  (*Compute (BuildNext (BuildNext (BuildLast (fun n => 5)))).*)

  Fixpoint evalListF (l : listf) : (getListType l) :=
    match l with
    | BuildNext l' => evalListF (l' )
    | BuildLast a => a 0
    end.