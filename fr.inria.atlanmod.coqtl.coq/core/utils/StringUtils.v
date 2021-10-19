Require Import String List.

Definition beq_string : string -> string -> bool := eqb.

Lemma lem_beq_string_id:
  forall (s : string),
   beq_string s s = true.
Proof.
  exact eqb_refl.
Qed.

Lemma lem_beq_string_eq2:
  forall (s1 s2 : string),
   beq_string s1 s2 = true -> s1 = s2.
Proof.
  apply eqb_eq.
Qed.
