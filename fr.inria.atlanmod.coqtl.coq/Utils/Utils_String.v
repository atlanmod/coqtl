Require Import String List Omega.

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