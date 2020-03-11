Require Import List Omega.
Require Import core.utils.CpdtTactics.

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


Theorem optionListToList_In:
  forall (A:Type) (a: A) (l: option (list A)), (In a (optionListToList l)) -> l <> None.
Proof.
intros.
destruct (l) eqn:l_ca.
- simpl in H. crush.
- simpl in H. omega.
Qed.


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

Theorem in_flat_map_nil:
  forall {A B : Type} (f : A -> list B) (l : list A),
       (flat_map f l) = nil <-> (forall a: A, In a l -> f a = nil).
Proof.
split.
* intros.
  induction l.
  - crush.
  -  apply app_eq_nil in H. destruct H. destruct H0.
    -- simpl in H. rewrite <- H0. assumption.
    -- apply IHl. assumption. assumption.
* intros.
  induction l.
  - crush.
  - simpl.
    assert (f a = nil). { crush. }
    rewrite H0. simpl.
    apply IHl. simpl in H. intros. specialize (H a0). apply H. right. assumption.
Qed.

Theorem in_flat_map_exists: 
  (forall (X Y:Type) (x:X) (y:Y) (f: X -> list Y) (B:Prop),
      (In y (f x) <-> B)) <->
  (forall (X Y:Type) (x:X) (y:Y) (f: X -> list Y) (B:Prop),
      (exists ys:list Y, f x = ys /\ In y ys) <-> B).
Proof.
  split.
  + intros.
    pose (H X Y x y f B).
    destruct i.
    split.
    * intros.
      destruct H2. destruct H2.
      rewrite <- H2 in H3.
      apply H0. assumption.
    * intros.
      apply H1 in H2.
      remember (f x) as ys'.
      exists ys'.
      auto.
  + intros.
    pose (H X Y x y f B).
    destruct i.
    split.
    * intros.
      apply H0.
      exists (f x).
      auto.
    * intros.
      apply H1 in H2.
      destruct H2. destruct H2.
      rewrite <- H2 in H3.
      assumption.
Qed.

Lemma filter_nil:
    forall (A : Type) (f : A -> bool) (x : A) (l : list A),
      (filter f l) = nil <->  (forall a: A, In a l -> f a = false).
Proof.
split.
* intros.
  induction l.
  - crush. 
  - simpl in H0.
    destruct H0.
    -- rewrite H0 in H.
       unfold filter in H.
       destruct (f a).
       --- crush.
       --- crush.
    -- apply IHl.
       --- simpl in H.
           destruct (f a0).
           ---- crush.
           ---- crush.
       --- assumption.
* intros.
  induction l.
  - crush.
  - simpl.
    assert (f a = false). { crush. }
    rewrite H0. simpl.
    apply IHl. simpl in H. intros. specialize (H a0). apply H. right. assumption.
Qed.

