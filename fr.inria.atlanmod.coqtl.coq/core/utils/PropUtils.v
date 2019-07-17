Require Import List Omega.
Require Import core.utils.CpdtTactics.

 
Theorem contraposition : forall p q:Prop, (p->q)->(~q->~p).
  Proof. intros. intro. apply H0. apply H. exact H1. Qed.
