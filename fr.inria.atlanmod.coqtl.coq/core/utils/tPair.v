
(* The very same lemma of surjective_pairing in the standard library. 
   The orignial one is opaque (end in Qed), and will have trouble in reduction.
   See: http://gallium.inria.fr/blog/coq-eval/
   We changed it here to be transparent (end in Defined)
 *)
Lemma surjective_pairing_transparent :
  forall (A B:Type) (p:A * B), p = pair (fst p) (snd p).
  Proof.
    destruct p; reflexivity.
  Defined.