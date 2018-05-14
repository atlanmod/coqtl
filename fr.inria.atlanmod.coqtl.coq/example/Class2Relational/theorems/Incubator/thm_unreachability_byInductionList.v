Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  

Require Import Utils.Utils_Top.
Require Import Utils.CoqTL.

Require Import Class2Relational.
Require Import ClassMetamodel.
Require Import RelationalMetamodel.

Definition reachable_class_step (m: ClassModel) (x y: Class) : Prop :=
  In (ClassMetamodel_toEObject x) (allModelElements m) /\
  In (ClassMetamodel_toEObject y) (allModelElements m) /\ 
  match (getClassAttributes x m) with
   | Some l =>  exists (attr:Attribute), In (ClassMetamodel_toEObject attr) (allModelElements m) /\ 
                                   In attr l /\
                                   getAttributeType attr m = Some y
   | None => False
  end.

Lemma reachable_class_step_cons :
  forall (e:ClassMetamodel_EObject) (le: list ClassMetamodel_EObject) (ll: list ClassMetamodel_ELink)
   (x y: Class),
    reachable_class_step (BuildModel (le) ll) x y -> reachable_class_step (BuildModel (e::le) ll) x y.
  intros e le ll x y H.
  unfold reachable_class_step in H.
  unfold reachable_class_step.
  simpl.
  simpl in H.
  destruct H. destruct H0.
  split.
  - right. exact.
  - split.
    + right. exact.
    + destruct (getClassAttributes x (BuildModel (e :: le) ll)) eqn:attrs.
      * destruct (getClassAttributes x (BuildModel le ll)) eqn:attrs_old.
        ** destruct H1.
           exists x0.
           destruct H1. destruct H2.
           split.
           *** right. exact.
           *** split.
               **** unfold getClassAttributes in attrs.
                    unfold getClassAttributes in attrs_old.
                    simpl in attrs. simpl in attrs_old.
                    rewrite -> attrs in attrs_old.
                    inversion attrs_old.
                    exact.
               **** exact.
        ** contradiction H1.
      * unfold getClassAttributes in attrs.
        simpl in attrs.
        unfold getClassAttributes in H1.
        simpl in H1.
        rewrite attrs in H1.
        contradiction H1.
Qed.

(* try cast x to type t, if succ and results x1, do e1, else do e2 *)
Notation "x1 <= [[ t ]] x | 'SUCC' e1 'FAIL' e2" :=
(match toModelClass t x with
| Some x1 => e1
| None => e2
end)
  (right associativity, at level 70).

Inductive ReachableClass (m : ClassModel) (x: Class): Class -> Prop :=
| reachable_class_refl : ReachableClass m x x
| reachable_class_trans : forall (y z:Class), 
                          reachable_class_step m x y ->
                           ReachableClass m y z -> 
                           ReachableClass m x z.

Lemma ReachableClass_cons :
  forall (e:ClassMetamodel_EObject) (le: list ClassMetamodel_EObject) (ll: list ClassMetamodel_ELink)
   (c1 c2: Class),
    ReachableClass (BuildModel le ll) c1 c2 -> ReachableClass (BuildModel (e :: le) ll) c1 c2.
Proof.
  intros e le ll c1 c2 H.
  induction H.
  + apply reachable_class_refl.
  + apply reachable_class_step_cons with (e:=e) in H.
    apply reachable_class_trans with (y:=y).
    exact.
    exact.
Qed.

Lemma ReachableClass_transitive :
 forall (m: ClassModel) (x y z:Class), 
  ReachableClass m x y ->
   ReachableClass m y z -> 
    ReachableClass m x z.
Proof.
intros.
induction H.
- done.
- pose (IHReachableClass H0) as H2.
  apply (@reachable_class_trans m x y z).
  - done.
  - done.
Qed.


Definition reachable_table_step (m: RelationalModel) (x y: Table) := 
  In (RelationalMetamodel_toEObject x) (allModelElements m) /\ 
  In (RelationalMetamodel_toEObject y) (allModelElements m) /\
  match (getTableColumns x m) with
   | Some l => exists (col: Column), In (RelationalMetamodel_toEObject col) (allModelElements m) /\ 
                                In col l /\ 
                                getColumnReference col m = Some y
   | None => False
  end.

Inductive ReachableTable (m : RelationalModel) (x: Table): Table -> Prop :=
| reachable_table_refl : ReachableTable m x x
| reachable_table_trans : forall (y z:Table), 
                           reachable_table_step m x y ->
                            ReachableTable m y z -> 
                              ReachableTable m x z. 

Lemma ReachableTable_transitive :
 forall (m: RelationalModel) (x y z:Table), 
  ReachableTable m x y ->
   ReachableTable m y z -> 
    ReachableTable m x z.
Proof.
intros.
induction H.
- done.
- pose (IHReachableTable H0) as Hind.
  apply (@reachable_table_trans m x y z).
  - done.
  - done.
Qed.

Definition Trivial := True.

Fixpoint find_Class (l : list ClassMetamodel_EObject) : option Class :=
 match l with
  | x::l' => match ClassMetamodel_instanceOfEClass ClassEClass x with
               | true => ClassMetamodel_toEClass ClassEClass x
               | false => find_Class l'
            end
  | _ => None
 end.

Definition ClassModel_fistClass (cm: ClassModel) := find_Class (allModelElements cm).


Lemma lem_reach:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (t1 t2 : Table) (c1 c2: Class),
     In (ClassMetamodel_toEObject c1) (allModelElements cm) ->
     In (ClassMetamodel_toEObject c2) (allModelElements cm) ->
     In (RelationalMetamodel_toEObject t1) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject c1::nil)) ->
     In (RelationalMetamodel_toEObject t2) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject c2::nil)) ->
     ReachableTable rm t1 t2 ->
     ReachableClass cm c1 c2
 ).
Proof.
  intros cm rm H t1 t2 c1 c2 Hinc_c1_cm Hinc_c2_cm Hinc_t1_sp1 Hinc_t2_sp2 Hreach_t1_t2.
  destruct cm eqn:cm1.
  induction l.
  - inversion Hinc_c1_cm.
  - intros.
    apply ReachableClass_cons.
    simpl in Hinc_c1_cm.
    simpl in IHl.
    destruct Hinc_c1_cm.
Admitted.


(* if none of reachable classes from [firstClass] named "Bad"
   then none of reachable tables from [firstTable] (gen from [firstClass]) named "Bad"
 *)
Theorem Class2Relational_keeps_full_reachability :
  forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
    match (ClassModel_fistClass cm) with
     | Some c1 => 
        (~ (beq_string (getClassName c1) "Bad"))                                                                                                           -> (* pre *)
        (forall (c2 : Class), In (ClassMetamodel_toEObject c2) (allModelElements cm) -> ReachableClass cm c1 c2 -> ~ (beq_string (getClassName c2) "Bad")) -> (* pre *)
         (forall (t: RelationalMetamodel_EObject) (r : Rule ClassMetamodel RelationalMetamodel),
           In r (getRules Class2Relational cm) ->
           In t (allModelElements rm) ->
           In t (instantiateRuleOnPattern r (ClassMetamodel_toEObject c1::nil)) ->
           matchPattern (getRules Class2Relational cm) (ClassMetamodel_toEObject c1::nil) = Some r ->
           (t1 <= [[TableClass]] t  | 
             SUCC (forall (t2 : Table), In (RelationalMetamodel_toEObject t2) (allModelElements rm) -> ReachableTable rm t1 t2 ->
                    ~ (beq_string (getTableName t2) "Bad"))                                                                                                  (* post *)
             FAIL Trivial)
         )
         
     | None => Trivial
    end.  
Proof.
  intros cm rm tr .
  destruct (ClassModel_fistClass cm) eqn: first_Class_ca.
  - intros Hgood_class Hreach_class t rl Hinc_rl Hinc_t Hinc_t_rl Hmatch.
    destruct (toModelClass TableClass t) as [t1|] eqn: cast_ca.
     - intros t2 Hinc_t2 Hreach_t_t2.
       simpl in t1.
       (* important here *)
       induction Hreach_t_t2.
       - (* reachable_table_refl *)
         inversion Hmatch.
         rewrite <- H0 in Hinc_t_rl.
         simpl in Hinc_t_rl.
         destruct Hinc_t_rl.
         - unfold RelationalMetamodel_toEObject in H.
           rewrite <- H in cast_ca.
           simpl in cast_ca. 
           inversion cast_ca.
           done.
         - done.
       - (* reachable_table_trans *)
           (* get corresponding eobject c of Table z *)
         - remember tr as tr'.
           clear  Heqtr' .
           apply tr_surj with (t1:=z) in tr'.  
          + destruct tr' as [sp_z]. destruct H0 as [tp_z]. destruct H0 as [rL_z].
            destruct H0 as [Hinsm_z]. destruct H0 as [Hintp_z]. destruct H0 as [Hexec_z]. 
            destruct H0 as [Hinclsp_z]. destruct H0 as [incltp_z].
            rename H0 into Hmatch_z.
            simpl in Hmatch_z.
            try destruct sp_z eqn:sp_ca; inversion Hmatch_z. 
            try destruct l eqn:l_z_ca; inversion Hmatch_z. 
            destruct c0 as [c0_z] eqn:c0_z_ca; simpl in Hmatch_z.
            destruct c0_z eqn:z_ca; simpl in Hmatch_z.
            (* if c is Class, Important *)
            *  inversion Hmatch_z.
               rewrite <- H3 in Hexec_z.
               rewrite <- Hexec_z in Hintp_z.
               simpl in Hintp_z.
               destruct Hintp_z; auto.
               ** assert (In c0 ([ClassMetamodel_BuildEObject ClassEClass c1])). {
                     simpl. left. symmetry. assumption.
                  }
                  apply Hinclsp_z in H4.
                  rewrite c0_z_ca in H4.
                  apply Hreach_class in H4.
                  - simpl in H.
                    apply rel_invert in H0.
                    rewrite <- H0.
                    done.
                  - clear H1 H2 Hmatch_z.
                    try apply (@lem_reach cm rm tr x z c c1); auto.
                    - admit.
                    - admit.
                    - admit.
                    - apply (@reachable_table_trans rm x y z H Hreach_t_t2).
             (* if c is Attribute, Trivial *)
             * simpl in H1, H2, Hmatch_z.
               try destruct (getAttributeDerived c1) eqn:derived_ca; inversion Hmatch_z.
               rewrite <- H3 in Hexec_z.
               unfold instantiateRuleOnPattern in Hexec_z. 
               unfold executeRuleOnPattern in Hexec_z. 
               simpl in Hexec_z. 
               rewrite derived_ca in Hexec_z.
               simpl in Hexec_z.
               rewrite <- Hexec_z in Hintp_z.
               simpl in Hintp_z.
               destruct Hintp_z; done.
           + done.
     - done.
  - done.
Abort.
