Require Import String Coq.Strings.Ascii.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.Model.
Require Import core.CoqTL.

Require Import examples.ClassGraph2Tree.ClassMetamodel.
Require Import examples.ClassGraph2Tree.ClassMetamodelPattern.

Open Scope coqtl.

Definition step (m: ClassModel) (c: Class) : option (list Class) :=
  attrs <- getClassAttributes c m;
  return
  concat
    (map
       (fun a => match getAttributeType a m with
              | Some cls => [ cls ]
              | None => nil
              end
       ) attrs).

Definition nextPaths (m: ClassModel) (p: list Class) : list (list Class) :=
  match p with
  | c :: p' =>
    match getClassAttributes c m with
    | Some attrs =>
      map
        (fun a =>
           match getAttributeType a m with
           | Some cls => cls :: p
           | None => nil
           end
        )
        attrs
    | None => nil
    end
  | nil => nil
  end.

Fixpoint allPathsFix (m: ClassModel) (l : nat) (p: list Class) :  list (list Class) :=
  match l with
  | S l' => p :: concat (map (allPathsFix m l') (nextPaths m p))
  | 0 => [ p ]
  end.

Definition rootClass (m : ClassModel) : Class :=
  hd (ClassMetamodel_defaultInstanceOfEClass ClassEClass)
     (ClassMetamodel_allInstances ClassEClass m).

Definition allPaths (m : ClassModel) (l : nat) : list (list Class) :=
  allPathsFix m l [ rootClass m ].

Definition allPathsTo (m : ClassModel) (l : nat) (o: Class) : list (list Class) :=
  filter (fun p =>
            match p with
            | h :: t => beq_Class h o
            | nil => false
            end
         ) (allPaths m l).



Definition path_type_transfer (id: nat) (tr: TransformationA ClassMetamodel ClassMetamodel) (sm: ClassModel) (name: string) (sp: list ClassMetamodel_EObject) 
   : option (matchPattern_getForSectionType tr sm name sp).
Proof.
destruct (find_OutputPatternElementA tr sm sp name) eqn: find_res.
- remember (OutputPatternElementA_getOutputPatternElementExpression o) as ope.
  destruct (nth_error (TransformationA_getRules tr) (OutputPatternElementExpressionA_getRule ope)) eqn: ra.
  -- pose (RuleA_getForExpression r) as fe.
     pose (evalForExpression fe tr sm sp) as fe_res.
     destruct fe_res eqn: fe_res_ca.
     --- pose (nth_error l id) as ret.
         destruct ret eqn: ret_ca.
         * unfold matchPattern_getForSectionType. rewrite find_res.
           pose (ForExpressionA_type_transfer fe ope tr sm f) as fexpr.
           rewrite Heqope in fexpr.
           exact fexpr.
         * exact None.
     --- exact None.
  -- exact None.
- exact None.
Defined.



Fixpoint eq_list (l1 l2: list Class): bool :=
  match l1, l2 with 
   | nil, nil => true
   | a::l1', b::l2' => beq_Class a b && eq_list l1' l2'
   | _, _ => false
  end.

Fixpoint index (l : list Class) (ll : list (list Class)) : option nat :=
  match ll with
   | nil => None
   | a :: lll => if eq_list l a then Some 0 else 
     match (index l lll) with
      | None => None
      | Some n => Some (1 + n)
     end
  end.

Fixpoint resolveAllIter (tr: Phase ClassMetamodel ClassMetamodel) (sm:ClassModel) (name: string) 
  (type: ClassMetamodel_EClass) (sps: list Class) (iters: list (list Class)) (forSection : list (list Class))
   : (list (Metamodel.denoteModelClass type)).
Proof.
destruct sps eqn: sps_ca.
- exact ( nil).
- destruct iters eqn: iters_ca.
  -- exact ( nil).
  -- destruct (index l0 forSection) eqn: id_ca.
     + destruct (path_type_transfer n (parsePhase tr) sm name [[ c ]]) eqn: iter_type.
       ++ destruct (resolveIter tr sm name type [[ c ]] m) eqn:it_ca.
          +++ exact ( (d :: (resolveAllIter tr sm name type l l1 forSection))).
          +++ exact (resolveAllIter tr sm name type l l1 forSection).
       ++ exact (resolveAllIter tr sm name type l l1 forSection).
     + exact (resolveAllIter tr sm name type l l1 forSection).
Defined.

Definition t (n : nat) : string :=  String (ascii_of_nat n) EmptyString .


(* id <- index path (allPathsTo m 3 c);  should be id <- index path (getForSection (matchPattern tr m [[c]])); *)
Definition ClassGraph2Tree' :=
  transformation ClassGraph2Tree from ClassMetamodel to ClassMetamodel
    with m as ClassModel := [

      rule Class2Class
        from
          c class ClassEClass
        when 
          true
        for
          i in (1 :: 2 :: nil)
        to [
          "at" :
            a' class AttributeEClass := 
              match i with
              | None => BuildAttribute newId false (getClassName c)
              | Some n => BuildAttribute newId false ((getClassName c) ++ t n)
              end;
          "cl" :
            c' class ClassEClass :=
              BuildClass newId (getClassName c)
        ]
       
    ].




Close Scope coqtl.

Definition ClassGraph2Tree := parseTransformation ClassGraph2Tree'.
