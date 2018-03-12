


Require Import String List Omega.
Require Export Utils_List.
Require Export Utils_Tuple.
Require Export Utils_Concat.

Definition beq_string (s1 : string) (s2 : string) : bool :=
  if string_dec s1 s2
  then true
  else false.

Lemma lem_beq_string_id:
  forall (s : string),
   beq_string s s = true.
Proof.
intros.
unfold beq_string.
destruct (string_dec s s).
- auto.
- congruence.
Qed. 

Lemma lem_beq_string_eq2:
  forall (s1 s2 : string),
   beq_string s1 s2 = true -> s1 = s2.
Proof.
intros.
unfold beq_string.
destruct (string_dec s1 s2) eqn: ca.
- auto.
- unfold beq_string in H.
  rewrite ca in H.
  congruence.
Qed. 

(* if e1 is successfully evaluated to x, then evaluate e2, otherwise stop *)
Notation "x <- e1 ; e2" :=
  (match e1 with
   | None => None
   | Some x => e2 end)
    (right associativity, at level 60).

    
Notation "'return' x" := ( Some x ) (no associativity, at level 60).

(*Notation "'when' b 'perform' m" := (if b then m else None) (no associativity, at level 60).*)

Fixpoint applyAll {A: Type} {B: Type} (lf : list (A -> B)) (lx : list A) : list B :=
  match lf, lx with
  | f::llf, x::llx => (f x) :: (applyAll llf llx)
  | _, _ => nil
  end.

