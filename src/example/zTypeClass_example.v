(* in this example, showing how the abstraction by type class used in building generic proofs by ltac.
 *)



(* Typeclass to register an enumeration of elements of a type. *)
Class Enumeration (A:Type) := enumerate : list A.
Arguments enumerate A [Enumeration].

(* Typeclass to register decision procedures to determine whether
   a given proposition is true or false. *)
Class Decision (P:Prop) := decide : {P} + {~P}.
Arguments decide P [Decision].

(* Given a Coq list l, execute tactic t on every element ofl until we get a success. *)
Ltac try_list l t :=
match (eval hnf in l) with
| @cons _ ?hd ?tl => (t hd || try_list tl t)
end.

(* here `eval hnf` let it work even l does not syntactically equal to the pattern but does reduce to it. *)
(* also, @cons _ ?hd ?tl is equiv to cons ?hd ?tl, @ symbol attached on functions usually 
   means we want to use all the arguments of function, including type argument
 *)
 
 
(* Tactic for "proof by reflection": use a decision procedure, and
   if it returns "true", then extract the proof from the result. *)
Ltac by_decision :=
match goal with
|- ?X => 
         match (eval hnf in (decide X)) with
         | left ?x => exact x (* the left of a decision is the truth part*)
         end
end.

(* Combination to try to prove an (exists x:A, P) goal by trying
   to prove P by reflection for each element in an enumeration of A. *)
Ltac try_enumerate :=
match goal with
| 
 |- @ex ?A ?P =>
  try_list (enumerate A)
    ltac:(fun x => exists x; by_decision)
end.


Inductive A := X | Y.

(* type A is numeratable *)
Instance A_enum : Enumeration A := cons X (cons Y nil).

Instance bool_eq_dec : forall x y:bool, Decision (x = y).
Proof.
intros. red. decide equality.
Defined.

Definition P (a:A) : bool :=
match a with
| X => false
| Y => true
end.

Goal exists a:A, P a = true.
Proof.
try_enumerate.
Qed.