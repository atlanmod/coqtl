Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.

Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

Require Import core.CoqTL.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.



Theorem Table_id_defindedness :
  forall (cm : ClassModel) (rm : RelationalModel), 
    rm = execute Class2Relational cm (* transformation *) ->
      (forall (c1 : ClassMetamodel_EObject), In c1 (@allModelElements _ _ cm) -> ClassMetamodel_getId c1 > 0) (* precondition *) ->
        (forall (t1 : RelationalMetamodel_EObject), In t1 (@allModelElements _ _ rm) -> RelationalMetamodel_getId t1 > 0). (* postcondition *)
Proof.
  intros cm rm H Hpre t1 Hintm.  
  remember H as tr.
  clear Heqtr.
  rewrite tr in Hintm.
  apply tr_execute_in_elements in Hintm.
  destruct Hintm. destruct H0. destruct H0. destruct H1.
  assert (exists tp : list RelationalMetamodel_EObject,
             instantiatePattern Class2Relational cm x = return tp /\ In t1 tp).
  { exists x0. split. crush. crush. }
  apply tr_instantiatePattern_in in H3.
  destruct H3. destruct H3. destruct H3.
  rename x1 into r.
  rename x2 into tp.
  rename x into sp.
  apply tr_matchPattern_in in H3.
  destruct H3.
  assert (exists tp : list  RelationalMetamodel_EObject,
          instantiateRuleOnPattern r cm sp = return tp /\ In t1 tp).
  { exists tp. crush. }
  apply tr_instantiateRuleOnPattern_in with (tr:=Class2Relational) in H6.
  destruct H6. destruct H6.
  rename x into i.
  rename x1 into tp1.
  assert  (exists tp : list  RelationalMetamodel_EObject,
          instantiateIterationOnPattern r cm sp i = return tp /\ In t1 tp).
  { exists tp1. crush. }
  apply tr_instantiateIterationOnPattern_in in H7.
  destruct H7. destruct H7.
  (* suggests missing theorem about instantiateElementonpattern and evalOutputpatternelement
     but perhaps this is intended, since at some point, we will have a function interfaces
     to functions defined in Expression.v
   *)
  unfold instantiateElementOnPattern in H8.
  (* suggests missing theorem about adaptor function matchRuleOnpattern' and matchruleonpattern
     although, in my opinion, we should avoid adaptor function in general.
   *)
  unfold matchRuleOnPattern' in H5.
  rewrite H5 in H8.
  unfold Class2Relational in H3.
  simpl in H3.
  destruct H3.
  + destruct (nth_error (evalIterator r cm sp) i).
    ++   generalize dependent x.
         generalize dependent r0.        
         rewrite <- H3.
         simpl.
         intros.
         destruct H7.
         +++ rewrite <- H7 in H8.
             (* suggests missing theorem about evalOutputPatternElement and evalFunction *)
             unfold evalOutputPatternElement in H8. simpl in H8.
             destruct (Expressions.evalFunction ClassMetamodel cm [ClassEClass] Table
                                                (fun (_ : ClassModel) (c : Class) => BuildTable (getClassId c) (getClassName c)) sp) eqn: f.
             ++++ unfold Expressions.evalFunction in f.
                  unfold Expressions.evalFunctionFix in f.
                  destruct sp eqn: sp_ca.
                  +++++ inversion f.
                  +++++ destruct (toModelClass ClassEClass c) eqn: c_ca.
                        destruct l.
                        ++++++ inversion f.
                               inversion H8.
                               rewrite <- H10.
                               simpl.
                               admit.
                        ++++++ inversion f.
                        ++++++ inversion f.
             ++++ inversion H8.
         +++ crush.
    ++ crush.
  + admit.
Admitted.  
