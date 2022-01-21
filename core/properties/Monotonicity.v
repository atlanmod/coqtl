Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import Expressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.


(*************************************************************)
(** * Monotonicity on model elements                         *)
(*************************************************************)

Definition SourceModel_elem_incl {tc: TransformationConfiguration}  (m1 m2: SourceModel) : Prop := 
  incl (allModelElements m1) (allModelElements m2). 

Definition TargetModel_elem_incl {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  incl (allModelElements m1) (allModelElements m2). 

Definition monotonicity_elem (tc: TransformationConfiguration) (t: Transformation) :=
  forall (sm1 sm2: SourceModel),
  SourceModel_elem_incl sm1 sm2 -> TargetModel_elem_incl (execute t sm1) (execute t sm2).

Theorem monotonicity_elem_lifting :
  forall (tc: TransformationConfiguration) 
  (tr: Transformation),
    Forall 
      (fun r => monotonicity_elem tc (buildTransformation (Transformation_getArity tr) [ r ]))
      (Transformation_getRules tr) 
        -> monotonicity_elem tc tr.
Proof.
intros tc tr mono. unfold monotonicity_elem. 
unfold TargetModel_elem_incl.
intros sm1 sm2 sm_incl. 
(* mono_lift_elem *)

(* prove In e (exeucte tr sm1) *)
rewrite Forall_forall in mono. unfold monotonicity_elem in mono. 
unfold execute. simpl. unfold incl. intros e in_sm1.
apply in_flat_map in in_sm1. 
destruct in_sm1 as [sp temp]. destruct temp as [in_sp in_e].
apply in_flat_map in in_e. 
destruct in_e as [r temp]. destruct temp as [in_r in_e].

(* prove In e (exeucte tr sm1) -> In e (exeucte tr_singleton sm1) *)
remember (buildTransformation (Transformation_getArity tr) [r]) as tr_singleton.
assert (In e (flat_map (instantiatePattern tr_singleton sm1)
              (allTuples tr_singleton sm1))) as in_e_single.
{ 
  apply in_flat_map. exists sp. split.
  - unfold allTuples in *. crush.
  - unfold instantiatePattern in *.
    apply in_flat_map. exists r. split.
    -- unfold matchPattern in *. 
      apply filter_In. apply filter_In in in_r. crush.
    -- auto.
}

(* by mono In e (exeucte tr_singleton sm1) -> 
            In e (exeucte tr_singleton sm2) *)
assert (In r (Transformation_getRules tr)) as in_tr.
{ unfold matchPattern in in_r. apply filter_In in in_r. crush. }
specialize (mono r in_tr sm1 sm2 sm_incl).
unfold TargetModel_elem_incl in mono.
rename mono into elem_incl.
unfold incl in elem_incl. specialize (elem_incl e).

(* prove In e (exeucte tr_singleton sm2) -> In e (exeucte tr sm2) *)
rewrite <- Heqtr_singleton in elem_incl.
specialize (elem_incl in_e_single). clear in_e_single.
apply in_flat_map in elem_incl.
destruct elem_incl as [sp2 temp]. destruct temp as [in_sp2 in_e_sm2].
apply in_flat_map. exists sp2.
split.
- unfold allTuples in *. crush.
- unfold instantiatePattern in *.
  apply in_flat_map in in_e_sm2. 
  destruct in_e_sm2 as [r2 temp]. destruct temp as [in_r2 in_e_sm2].
  apply in_flat_map. exists r2. split.
  -- unfold matchPattern in *. 
      apply filter_In. apply filter_In in in_r2. crush.
  -- auto.
Qed.










