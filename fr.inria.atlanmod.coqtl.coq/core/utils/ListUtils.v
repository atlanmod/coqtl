Require Import List Omega.


Definition listToListList {A : Type} (l : list A) : list (list A) :=
  map (fun e:A => e::nil) l.

Definition hasLength {A : Type} (l : list A) (n: nat): bool :=
  beq_nat (Datatypes.length l) n.

Definition optionToList {A:Type} (o: option A) : list A :=
  match o with
  | Some a => a :: nil
  | None => nil
  end.

Definition optionListToList {A:Type} (o: option (list A)) : list A :=
  match o with
  | Some a => a
  | None => nil
  end.

Definition optionList2List {A : Type} (l:list (option A)) : list A :=
  flat_map optionToList l.

Theorem optionList2List_In :
  forall (A:Type) (a: A) (l: list (option A)), (In a (optionList2List l)) -> (In (Some a) l).
Proof.
  intros.
  induction l.
  - inversion H.
  - destruct a0.
    + simpl in H.
      destruct H.
      * rewrite H.
        simpl.
        left.
        reflexivity.
      * simpl.
        right.
        apply IHl.
        assumption.
    + simpl in H.
      apply IHl in H.
      simpl.
      right.
      assumption.
Qed.

Theorem optionList2List_In_inv :
  forall (A:Type) (a: A) (l: list (option A)), (In (Some a) l) -> (In a (optionList2List l)).
Proof.
  intros.
  induction l.
  - inversion H.
  - destruct a0.
    + simpl in H.
      destruct H.
      * rewrite H.
        simpl.
        left.
        reflexivity.
      * simpl.
        right.
        apply IHl.
        assumption.
    + simpl.
      simpl in H.
      destruct H.
      * inversion H.
      * apply IHl.
        assumption.
Qed.

Definition singletons {A: Type} (l : list A) : list (list A) :=
  listToListList l.

Fixpoint mapWithIndex {A : Type} {B : Type} (f: nat -> A -> B) (n : nat) (l: list A) : list B :=
    match l with
      | nil => nil
      | a :: t => (f n a) :: (mapWithIndex f (n + 1) t)
    end.

Fixpoint zipWith {A : Type} {B : Type} {C : Type} (f: A -> B -> C) (la: list A) (lb: list B) : list C :=
  match la, lb with
  | ea::eas, eb::ebs => (f ea eb) :: (zipWith f eas ebs)
  | nil, _ => nil
  | _, nil => nil
  end.

