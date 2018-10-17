(* Coq libraries *)
Require Import Bool.
Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.
Require Import Coq.Logic.Eqdep_dec.

(* CoqTL libraries *)
Require Import core.utils.tTop.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Iterator.
Require Import core.utils.CpdtTactics.




(* Meta-types *)
Inductive DefaultIterator_Class : Set :=
  | NatClass
.

Definition DefaultIterator_getTypeByClass (grec_arg : DefaultIterator_Class) : Set :=
  match grec_arg with
    | NatClass => (nat)
  end.


Inductive DefaultIterator_Object : Set :=
 | Build_DefaultIterator_Object : 
    forall (grec_arg: DefaultIterator_Class), (DefaultIterator_getTypeByClass grec_arg) -> DefaultIterator_Object.

Lemma DefaultIterator_eqClass_dec : 
 forall (grec_arg1:DefaultIterator_Class) (grec_arg2:DefaultIterator_Class), { grec_arg1 = grec_arg2 } + { grec_arg1 <> grec_arg2 }.
Proof. repeat decide equality. Defined.


Lemma DefaultIterator_Object_invert : 
  forall (grec_arg: DefaultIterator_Class) (t1 t2: DefaultIterator_getTypeByClass grec_arg), Build_DefaultIterator_Object grec_arg t1 = Build_DefaultIterator_Object grec_arg t2 -> t1 = t2.
  Proof.
    intros.
    inversion H.
    apply inj_pair2_eq_dec in H1.
    exact H1.
    apply DefaultIterator_eqClass_dec.
  Defined.



(* TODO: This lemma used non-Defined lemma beq_nat_false, which might cause problem during computation*)
Lemma DefaultIterator_eqObject_dec : 
 forall (grec_arg1:DefaultIterator_Object) (grec_arg2:DefaultIterator_Object), { grec_arg1 = grec_arg2 } + { grec_arg1 <> grec_arg2 }.
  Proof. 
  intros.
  destruct grec_arg1 eqn: arg1_ca.
  destruct grec_arg2 eqn: arg2_ca.
  destruct (DefaultIterator_eqClass_dec grec_arg grec_arg0).
  - destruct grec_arg0.
    destruct grec_arg.
    simpl in d.
    simpl in d0.
    destruct (beq_nat d d0) eqn: d_ca.
    -- left. symmetry in d_ca. apply beq_nat_eq in d_ca. crush.
    -- right. crush. apply beq_nat_false_defined in d_ca. apply DefaultIterator_Object_invert in H. contradiction.
  - right.
    crush.
  Defined.


Definition DefaultIterator_getClass (greo_arg : DefaultIterator_Object) : DefaultIterator_Class :=
   match greo_arg with
  | (Build_DefaultIterator_Object greo_arg _) => greo_arg
   end.

Definition DefaultIterator_instanceOfEClass (grec_arg: DefaultIterator_Class) (greo_arg : DefaultIterator_Object): bool :=
  if DefaultIterator_eqClass_dec (DefaultIterator_getClass greo_arg) grec_arg then true else false.


Definition DefaultIterator_toEClass (grec_arg : DefaultIterator_Class) (greo_arg : DefaultIterator_Object) : option (DefaultIterator_getTypeByClass grec_arg).
Proof.
  destruct greo_arg as [arg1 arg2].
  destruct (DefaultIterator_eqClass_dec arg1 grec_arg) as [e|] eqn:dec_case.
  - rewrite e in arg2.
    exact (Some arg2).
  - exact None.
Defined.


Definition DefaultIterator_toEObjectOfEClass (grec_arg: DefaultIterator_Class) (t: DefaultIterator_getTypeByClass grec_arg) : DefaultIterator_Object :=
  (Build_DefaultIterator_Object grec_arg t).


(* Typeclass Instance *)
Instance DefaultIterator : Iterator DefaultIterator_Object DefaultIterator_Class :=
  {
    denoteIteratorClass := DefaultIterator_getTypeByClass;
    toIteratorClass := DefaultIterator_toEClass;
    toIteratorElement := DefaultIterator_toEObjectOfEClass;
    eqIteratorClass_dec := DefaultIterator_eqClass_dec;
    eqIteratorElement_dec := DefaultIterator_eqObject_dec;
    BuildIteratorElement := Build_DefaultIterator_Object;
  }.

