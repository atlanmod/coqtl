Require Import Class2Relational.
Require Import ClassMetamodel.
Require Import RelationalMetamodel.
Require Import CoqTL.
Require Import Utils.
Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  


Definition reachable_class_step (m: ClassModel) (x y: Class) := 
  match (getClassAttributes x m) with
   | Some l => exists (attr:Attribute), In (ClassMetamodel_toEObject attr) (allModelElements m) /\ In attr l /\ getAttributeType attr m = Some y
   | None => False
  end.


Inductive ReachableClass (m : ClassModel) (x: Class): Class -> Prop :=
| reachable_class_refl : ReachableClass m x x
| reachable_class_trans : forall (y z:Class), 
                           reachable_class_step m x y ->
                            ReachableClass m y z -> 
                             ReachableClass m x z.


Definition reachable_table_step (m: RelationalModel) (x y: Table) := 
  match (getTableColumns x m) with
   | Some l => exists (col: Column), In (RelationalMetamodel_toEObject col) (allModelElements m)/\ In col l /\ getColumnReference col m = Some y
   | None => False
  end.


Inductive ReachableTable (m : RelationalModel) (x: Table): Table -> Prop :=
| reachable_table_refl : ReachableTable m x x
| reachable_table_trans : forall (y z:Table), 
                           reachable_table_step m x y ->
                            ReachableTable m y z -> 
                             ReachableTable m x z.
                             
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

Theorem Class2Relational_keeps_full_reachability :
  forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
    match (ClassModel_fistClass cm) with
     | Some c1 => 
        (forall (c2 : Class), In (ClassMetamodel_toEObject c2) (allModelElements cm) -> ReachableClass cm c1 c2) -> (* precondition *)
         (exists (t1: Table), In (RelationalMetamodel_toEObject t1) (allModelElements rm) /\ 
                              (forall (t2 : Table), In (RelationalMetamodel_toEObject t2) (allModelElements rm) -> 
                                ReachableTable rm t1 t2 )) (* postcondiiton *)
     | None => Trivial
    end.  
Proof.
  intros cm rm tr.
  destruct (ClassModel_fistClass cm) eqn: first_Class_ca.
  - intros pre.

    - admit.
    - intros.

  - done.
Abort.
  
  
