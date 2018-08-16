
(* Advantage of this enconding:
    - easy to write by the user.
    - easy to do structural induction on target model.
 *)

(* Disadvantage of this enconding:
    - might be highly coupled with the semantics of 
      transformation language (e.g. ATL).
 *)

Section ER2REL.

(* Coq libraries *)

Require Import Omega.
Require Import List.      (* sequence *)
Require Import String.
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import ER.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Set Implicit Arguments.


(*
Notation "( x | y )" := (exist _ x y ) : fibration_scope. (* _ : Type arg, x: _, y: P x *)
Open Scope fibration_scope.
*)



Variable Entity_Schema: Entity -> ERSchema -> bool.
Hypothesis Entity_Schema_def : forall s e, In e (ERSchemaEntities s) <-> Entity_Schema e s.

Variable Relship_Schema: Relship -> ERSchema -> bool.
Hypothesis Relship_Schema_def : forall s r, In r (ERSchemaRelships s) <-> Relship_Schema r s.

Variable Attribute_Entity: Attribute -> Entity -> bool.
Hypothesis Attribute_Entity_def: forall e a, In a (EntityAttrs e) <-> Attribute_Entity a e.

Variable Attribute_Relship: Attribute -> Relship -> bool.
Hypothesis Attribute_Relship_def : forall r a, In a (RelshipAttrs r) -> Attribute_Relship a r.

Variable RelshipEnd_Entity: RelshipEnd -> Entity -> bool.
Hypothesis RelshipEnd_Entity_def : forall rse e, In rse (EntityEnds e) -> RelshipEnd_Entity rse e.

Variable RelshipEnd_Relship: RelshipEnd -> Relship -> bool.
Hypothesis RelshipEnd_Relship_def : forall rse rs, In rse (RelshipEnds rs) -> RelshipEnd_Relship rse rs.


(** The target model is constructed in terms of  
   a source model, i.e. the transformation.
   This can be seen as a matching phase.
 *)

Inductive 
  RELSchema : EClass :=
    S2S :
      ERSchema -> RELSchema.

Inductive 
  Table : EClass :=
    | E2R : 
       Entity -> Table
    | R2R:
       Relship -> Table.

Inductive
  Column : EClass :=
    | EA2A :
        Attribute -> Entity -> Column
    | RA2A : 
        Attribute -> Relship -> Column
    | RA2AK :
        Attribute -> RelshipEnd -> Entity -> Column.




Definition RELSchemaERSchema (r: RELSchema) : ERSchema :=
 match r with
  | S2S s => s
 end.
  
Definition TableEntity (t: Table) : option Entity :=
 match t with
  | E2R e => Some e
  | R2R _ => None
 end.

Definition TableRelship (t: Table) : option Relship :=
 match t with
  | E2R _ => None
  | R2R r => Some r
 end.




(** Define restricted inductive type to simulate rule guards*)
Fixpoint Instantiated_RELSchema (r : RELSchema) : bool :=
  match r with
  | S2S erschema => true
  end.

Definition iRELSchema : EClass := {r : RELSchema | (Instantiated_RELSchema r)}.


Fixpoint Instantiated_Table (t : Table) : bool :=
  match t with
  | E2R entity => true
  | R2R relship => true
  end.
  

  
Definition iTable : EClass := {t : Table | (Instantiated_Table t)}.



Definition Instantiated_Column (c: Column) : bool :=
  match c with
  | EA2A attr ent => (Attribute_Entity attr ent)
  | RA2A attr rs => (Attribute_Relship attr rs)
  | RA2AK attr rse e => (Attribute_Entity attr e) && (RelshipEnd_Entity rse e)  && AttributeIsKey attr 
  end.

Definition iColumn : EClass := {c: Column | (Instantiated_Column c)}.


Lemma s2s_surj:
  forall r: iRELSchema, 
    exists s: ERSchema, S2S s  = val r /\ True.
Proof.
intros.
destruct r.
simpl.
destruct x.
exists e.
split.
reflexivity.
auto.
Qed.


(** To simulate the applying phase, i.e. customizing the
    accessor functions 
    
    TODO: 
      - Subtype: https://coq.inria.fr/library/Coq.Init.Specif.html
      - need better encoding of resolving phase, since currently 
        it is manually determined.  
 *)

Definition RELSchemaName (r : iRELSchema) : string :=
  match proj1_sig r with (* a matched relschema*)
    | S2S er => ERSchemaName er
  end.

(* possible encoding of resolving *)
Inductive TableSchema : Table -> RELSchema -> Prop :=
 | E2R_bind2  : forall e s, Entity_Schema e s -> Instantiated_Table (E2R e) -> Instantiated_RELSchema (S2S s) -> 
  TableSchema (E2R e) (S2S s)
 | R2R_bind2 : forall r s, Relship_Schema r s -> Instantiated_Table (R2R r) -> Instantiated_RELSchema (S2S s) -> 
  TableSchema (R2R r) (S2S s)
. 

(** another way of writing pattern matching for subtype *)
Definition TableName (t : iTable) : string :=
  match t with 
   | exist (E2R e) _ => 
      EntityName e
   | exist (R2R e) _ =>
      RelshipName e
  end.

Definition ColumnName (c : iColumn) : string :=
  match c with 
   | exist (EA2A attr e) _ => 
      AttributeName attr
   | exist (RA2A attr r) _ =>
      AttributeName attr
   | exist (RA2AK attr ed e) _ =>
      AttributeName attr
  end.

Inductive ColumnTable : Column -> Table -> Prop :=
 | EA2A_bind3 : forall att ent,  Instantiated_Column (EA2A att ent) -> Instantiated_Table (E2R ent) -> 
   ColumnTable (EA2A att ent) (E2R ent)
 | RA2A_bind3 : forall att rs,  Instantiated_Column (RA2A att rs) -> Instantiated_Table (R2R rs) -> 
   ColumnTable (RA2A att rs) (R2R rs)
 | RA2AK_bind3 : forall att rse ent rs, (RelshipEnd_Relship rse rs) -> Instantiated_Column (RA2AK att rse ent) -> Instantiated_Table (R2R rs) -> 
   ColumnTable (RA2AK att rse ent) (R2R rs)
. 


(* Compute target model from the root of the source model, 
   which represents the transformation result.
 *)

(* Proof *)

(* TODO:
  - have precondition, and more accurate postcondition, i.e. schema->tables
 *)
 



Lemma Entity_dec : forall (e1:Entity) (e2:Entity), { e1 = e2 } + { e1 <> e2 }.
Proof. repeat decide equality. Qed.






Lemma projection_iColumn_injective : 
 forall t1 t2: iColumn,  val t1 = val t2 -> t1 = t2 .
Proof. intros;apply val_inj;apply H. Qed.



Lemma projection_iColumn_invert_equiv : 
 forall t1 t2: iColumn,  t1 <> t2 -> val t1 <> val t2.
Proof. red; intros; apply projection_iColumn_injective in H0; contradiction. Qed.



Hypothesis unique_attribute_name :
 forall e : Entity, 
  forall a1 a2 : Attribute,
   Attribute_Entity a1 e /\ Attribute_Entity a2 e /\ a1 <> a2 ->
    AttributeName a1 <> AttributeName a2.
    
    
    
Theorem unique_column_name : 
 forall t : iTable, 
  forall c1 c2 : iColumn,
   ColumnTable (val c1) (val t) /\ ColumnTable (val c2) (val t) /\ c1 <> c2 ->
    ColumnName c1 <> ColumnName c2.
Proof.
intros it' ic1' ic2' H;
remember it' as it eqn: iTableEq; destruct it' as [t'];
remember t' as t eqn: TableEq;
assert (val it = t) as Hit_t. rewrite -> iTableEq; done.
destruct t'.

- (* t : E2R e *)
  remember ic1' as ic1 eqn: iColumnEq1; destruct ic1' as (c1', gc1);
  remember ic2' as ic2 eqn: iColumnEq2; destruct ic2' as (c2', gc2);
  rewrite -> iColumnEq1; rewrite -> iColumnEq2;
  remember c1' as c1; 
  assert (val ic1 = c1) as Hic1_c1. { rewrite iColumnEq1; simpl; reflexivity. }
  remember c2' as c2; 
  assert (val ic2 = c2) as Hic2_c2. { rewrite iColumnEq2; simpl; reflexivity. }
  decompose [and] H; clear H.
  rename H0 into HRel_ic1_it.
  rename H2 into HRel_ic2_it.
  rename H3 into NEq_ic1_ic2.
  
  rewrite Hic1_c1 in HRel_ic1_it.
  rewrite Hic2_c2 in HRel_ic2_it.
  rewrite Hit_t in HRel_ic1_it.
 
  destruct HRel_ic1_it;
  destruct HRel_ic2_it;
  simpl;
  (* reduce impossible cases by using **try** tactic *) 
  try done.
  (* one sub-case to prove *)
  * apply unique_attribute_name with e.
    repeat split;
    unfold Instantiated_Column in H; 
    unfold Instantiated_Column in H1.
    
    + (* Attribute_Entity att e *)
      try by inversion TableEq as [EqinTableEq]; rewrite <- EqinTableEq. 
    + (* Attribute_Entity att0 e *)
      try by inversion TableEq as [EqinTableEq];  inversion Hit_t as [EqinHit_t]; 
      rewrite <- EqinHit_t in EqinTableEq;
      rewrite <- EqinTableEq.  
   
    + (* att <> att0 *)
      apply projection_iColumn_invert_equiv in NEq_ic1_ic2.
      rewrite (Hic1_c1) in NEq_ic1_ic2.
      rewrite Hic2_c2 in NEq_ic1_ic2.
      red in NEq_ic1_ic2.
      red.
      intros.
      apply NEq_ic1_ic2.
      congruence.

- (* t : R2R e *)
  remember ic1' as ic1 eqn: iColumnEq1; destruct ic1' as (c1', gc1);
  remember ic2' as ic2 eqn: iColumnEq2; destruct ic2' as (c2', gc2);
  rewrite -> iColumnEq1; rewrite -> iColumnEq2;
  remember c1' as c1; 
  assert (val ic1 = c1) as Hic1_c1. { rewrite iColumnEq1; simpl; reflexivity. }
  remember c2' as c2; 
  assert (val ic2 = c2) as Hic2_c2. { rewrite iColumnEq2; simpl; reflexivity. }
  decompose [and] H; clear H.
  rename H0 into HRel_ic1_it.
  rename H2 into HRel_ic2_it.
  rename H3 into NEq_ic1_ic2.
  
  (* reduce impossible cases by using **try** tactic *)
  destruct c1';
  destruct c2';
  
  try by
    simpl; rewrite Heqc1; rewrite Heqc2;
    rewrite Hit_t in HRel_ic1_it, HRel_ic2_it;
    rewrite Hic1_c1 in HRel_ic1_it;
    rewrite Hic2_c2 in HRel_ic2_it;
    destruct HRel_ic1_it;
    done.
  
  (* further reduce impossible cases by using sub-goals selector *)
  1,2,3,4,5,6:
  try by
    simpl; rewrite Heqc1; rewrite Heqc2;
    rewrite Hit_t in HRel_ic1_it, HRel_ic2_it;
    rewrite Hic1_c1 in HRel_ic1_it;
    rewrite Hic2_c2 in HRel_ic2_it;
    destruct HRel_ic2_it;
    done.
  
  (* 4 sub-cases to prove *)
  admit.
  admit.
  admit.
  admit.  
Admitted.





(* Interesting Properties *)

(**
Leibniz equality: https://coq.inria.fr/library/Coq.Init.Logic.html

 *)
