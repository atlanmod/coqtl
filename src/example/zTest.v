Require Import Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssreflect.prime eqtype.




Inductive A :=
 mkA : nat -> A.


(* getter *)
Function getId (a: A) : nat :=
match a with mkA n => n end.

Function filter (a: A) : bool := true.

Definition subsetA : Set := {a : A | is_true (filter a) }.

Definition cast (a: A) : option subsetA.
  destruct (filter a) eqn:Eq.
  - Show Proof. refine (Some (exist _ a _)). Show Proof. rewrite Eq. Show Proof. reflexivity.
  - exact None.
Defined.

(*
Definition cast' (a: A) : option subsetA :=
  match (filter a) as fa return (filter a = fa -> option subsetA) with
  | true => fun prf => Some (exist _ a prf)
  | false => fun _ => None
  end eq_refl.
*)
  
Program Definition cast'' (a: A) : option subsetA :=
  match filter a with
  | true => Some (exist _ a _)
  | false => None
  end.
  

Lemma projection_injective :
  forall t1 t2: subsetA, proj1_sig t1 = proj1_sig t2 -> t1 = t2.
Proof.
destruct t1, t2.
intros.
simpl in H.
revert i.
rewrite -> H.
intro i.
unfold filter in *.
assert (i = i0);

auto;
simpl in i0.

 intros t1 t2.
 apply val_inj.
Qed.

End Y.