Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  

Require Import core.Utils_Top.
Require Import core.CoqTL.

Require Import Class2Relational.
Require Import ClassMetamodel.
Require Import RelationalMetamodel.


(* transformation is distributive over model element *)
Lemma tr_distri:
  forall 
(a : ClassMetamodel_EObject)
(l : list ClassMetamodel_EObject)
(l0 : list ClassMetamodel_ELink)
(t1 : RelationalMetamodel_EObject)
,
(allModelElements (execute Class2Relational (BuildModel (a :: l) l0))) =
  (allModelElements (execute Class2Relational (BuildModel ([a]) l0))) ++
  (allModelElements (execute Class2Relational (BuildModel l l0)))
.
Proof.
  intros.
  destruct a eqn:a_ca.
  destruct c eqn:c_ca.
  - (* Class *)
    done.
  - unfold execute. simpl.
    unfold instantiatePattern. simpl.
    destruct (~~ getAttributeDerived c0) eqn: guard.
    + simpl.
      unfold instantiateRuleOnPattern.
      unfold executeRuleOnPattern.
      unfold matchRuleOnPattern.
      simpl.
      rewrite guard.
      simpl.
      done.
    + done.
Qed.

(* a customized version of in_app_or over Lemma tr_distri *)
Lemma in_app_or_tran_distri :
  forall 
(a : ClassMetamodel_EObject)
(l : list ClassMetamodel_EObject)
(l0 : list ClassMetamodel_ELink)
(t1 : RelationalMetamodel_EObject)
,
In t1 (allModelElements (execute Class2Relational (BuildModel (a :: l) l0))) ->
  In t1 (allModelElements (execute Class2Relational (BuildModel ([a]) l0))) 
  \/ In t1 (allModelElements (execute Class2Relational (BuildModel l l0))).
Proof.
intros.
rewrite tr_distri in H.
- remember (allModelElements (execute Class2Relational (BuildModel ([a]) l0))).
  remember (allModelElements (execute Class2Relational (BuildModel l l0))).
  apply in_app_or.
  done.
- done.
Qed.





(* transformation surjectivity and binding outcome *)
(* ps: the trick of doing proof is treating transformation as a blackbox, do not unfold it until there is a 
   concrete model element / link (so that the simplification can work on this concrete instance). *)
Lemma tr_surj :
  forall (cm : Model ClassMetamodel_EObject ClassMetamodel_ELink),
        (forall (t1 : RelationalMetamodel_EObject), 
        In t1 (allModelElements (execute Class2Relational cm)) -> 
          (exists (c1 : ClassMetamodel_EObject), In c1 (allModelElements cm) 
          /\ ClassMetamodel_getId c1 = RelationalMetamodel_getId t1)).
Proof.
intros.
destruct cm.
induction l.
- done.
- apply in_app_or_tran_distri in H.
  destruct H.
  + Focus 2.
    apply IHl in H.
    destruct H.
    eapply ex_intro .
    simpl.
    split.
    right.
    apply H.
    destruct H.
    done.
  + eapply ex_intro .
    simpl.
    split.
    left.
    auto.
    destruct a.
    destruct c eqn: c_case.
    ++  unfold Class2Relational in H.
        simpl in H.
        destruct H.
        - unfold RelationalMetamodel_getId.
          rewrite <- H.
          simpl.
          exact.
        - done.
    ++  unfold execute in H. simpl.
        unfold instantiatePattern in H. simpl.
        destruct (~~ getAttributeDerived c0) eqn: guard.
          * simpl in H.
            unfold instantiateRuleOnPattern in H.
            unfold executeRuleOnPattern in H.
            unfold matchRuleOnPattern in H.
            simpl in H.
            rewrite guard in H.
            simpl in H.
            rewrite guard in H.
            simpl in H.
            destruct H.
            ** unfold RelationalMetamodel_getId.
               rewrite <- H.
               simpl.
               exact.
            ** done.
          * simpl in H.
            rewrite guard in H.
            done.
Qed.
    
  
(* Same as tr_surj, but with explicit reference of target resource *)  
Lemma tr_surj_rewrite :
  forall (cm : ClassModel) 
   (rm : RelationalModel), 
    execute Class2Relational cm = rm (* transformation *) ->
        (forall (t1 : RelationalMetamodel_EObject), In t1 (allModelElements rm) -> 
          (exists (c1 : ClassMetamodel_EObject), In c1 (allModelElements cm) 
          /\ ClassMetamodel_getId c1 = RelationalMetamodel_getId t1)).
Proof.
intros.
apply tr_surj.
rewrite <- H in H0.
done.
Qed.

Theorem Table_id_positive :
  forall (cm : ClassModel) (rm : RelationalModel), 
    execute Class2Relational cm = rm (* transformation *) ->
      (forall (c1 : ClassMetamodel_EObject), In c1 (allModelElements cm) -> ClassMetamodel_getId c1 > 0) (* precondition *) ->
        (forall (t1 : RelationalMetamodel_EObject), In t1 (allModelElements rm) -> RelationalMetamodel_getId t1 > 0). (* postcondition *)
Proof.
(* Book keeping *)
intros.
remember cm as classModel; destruct cm as (srcElems, srcRels).
remember rm as relModel; destruct rm as (trgElems, trgRels).
remember t1 as trgElem; destruct t1.

assert (exists c1 : ClassMetamodel_EObject,
    In c1 (allModelElements classModel) /\
    ClassMetamodel_getId c1 = RelationalMetamodel_getId trgElem).
{ apply tr_surj_rewrite with relModel; done. }

destruct H2;
destruct H2.
assert (ClassMetamodel_getId x > 0).
{ apply H0. done. }

remember c as re; destruct c.

- (* Table *)
  rewrite <- H3;
  done.
- (* Column *)
  rewrite <- H3; 
  done.
Qed.





