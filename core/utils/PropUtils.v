Require Import core.utils.CpdtTactics.


Theorem contraposition : forall p q:Prop, (p->q)->(~q->~p).
Proof.
  intros p q Hi Hnq Hp. exact (Hnq (Hi Hp)).
Qed.
