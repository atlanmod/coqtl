Require Import String.
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

Definition Rule_num_getForSectionType (ruleNo : nat) (tr: TransformationA ClassMetamodel ClassMetamodel) (sm: ClassModel) : Type :=
    match (nth_error ((TransformationA_getTransformation tr) (fun c:ClassModel => nil) sm) ruleNo) with
    | None => Error
    | Some r => parseRule_ForSectionType (snd r)
    end.

Definition getRuleNum_ByForSectionType (path : list Class) : nat := 1.

Definition path_transfer2 (path : list Class) (id: nat)  (tr: TransformationA ClassMetamodel ClassMetamodel) (sm: ClassModel) 
  (fe : ForExpressionA) (sp: list ClassMetamodel_EObject) : option (Rule_num_getForSectionType (getRuleNum_ByForSectionType path) tr sm).
Proof.
destruct (nth_error ((TransformationA_getTransformation tr) (fun c:ClassModel => nil) sm) (getRuleNum_ByForSectionType path)) eqn: nth_r.
- destruct (nth_error (TransformationA_getRules tr) (ForExpressionA_getRule fe)) eqn:nth_ra.
      + remember (evalForExpressionFix (snd p) (RuleA_getInTypes r) sm sp) as ret.
        unfold Rule_num_getForSectionType.
        rewrite nth_r.
        destruct ret eqn: ret_ca.
        ++ destruct (nth_error l id) eqn: rett.
           +++ exact (Some p0).
           +++ exact None.
        ++ exact None.
      + exact None.
- exact None.
Defined.

Definition Rule_num_getForSectionType_transfer (path : list Class) (id: nat) (fe : ForExpressionA) (o : OutputPatternElementExpressionA) (tr: TransformationA ClassMetamodel ClassMetamodel) 
  (sm: ClassModel)  (r: Rule_num_getForSectionType (getRuleNum_ByForSectionType path) tr sm) : option (ForExpressionA_getForSectionType fe tr sm).
  Proof.
  destruct (beq_nat ((getRuleNum_ByForSectionType path))
                    (ForExpressionA_getRule fe)) eqn: ca.
  - unfold Rule_num_getForSectionType in r.
    apply beq_nat_true in ca.
    rewrite ca in r.
    exact (Some r).
  - exact None.
  Defined.

Definition path_transfer (path : list Class) (id: nat) (tr: TransformationA ClassMetamodel ClassMetamodel) (sm: ClassModel) (name: string) (sp: list ClassMetamodel_EObject)
 (o: OutputPatternElementExpressionA) (fe: ForExpressionA) : option (ForExpressionA_getForSectionType fe tr sm).
Proof.
destruct (beq_nat (getRuleNum_ByForSectionType path)
                  (OutputPatternElementExpressionA_getRule o)) eqn: ca.
- destruct (path_transfer2 path id tr sm fe sp) eqn: ca2.
  -- destruct (Rule_num_getForSectionType_transfer path id fe o tr sm r) eqn: ca3.
     --- exact (Some f).
     --- exact None.
  -- exact None.
- exact None.
Defined.

Definition type_transfer (path : list Class) (id: nat) (tr: TransformationA ClassMetamodel ClassMetamodel) (sm: ClassModel) (name: string) (sp: list ClassMetamodel_EObject) 
   : option (matchPattern_getForSectionType tr sm name sp).
Proof.
destruct (find_OutputPatternElementA tr sm sp name) eqn: find_res.
- pose (OutputPatternElementA_getOutputPatternElementExpression o) as ope.
  destruct (nth_error (TransformationA_getRules tr) (OutputPatternElementExpressionA_getRule ope)) eqn: ra.
  -- pose (RuleA_getForExpression r) as f.
     pose (path_transfer path id tr sm name sp ope f) as pth.
     destruct pth eqn: pth_ca.
     --- pose (ForExpressionA_type_transfer f ope tr sm f0).
         unfold matchPattern_getForSectionType. rewrite find_res.
         exact o0.
     --- exact None.
  -- exact None.
- exact None.
Defined.

Fixpoint eq_Class (c1 c2: Class): bool :=
  match c1, c2 with 
   | BuildClass a1 a2, BuildClass b1 b2 => beq_string a1 b1 && beq_string a2 b2
  end.


Fixpoint eq_list (l1 l2: list Class): bool :=
  match l1, l2 with 
   | nil, nil => true
   | a::l1', b::l2' => eq_Class a b && eq_list l1' l2'
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

Definition ClassGraph2Tree' :=
  transformation ClassGraph2Tree from ClassMetamodel to ClassMetamodel
    with m as ClassModel := [

      rule Class2Class
        from
          c class ClassEClass
        for
          i in (allPathsTo m 3 c)
        to [
          "at" :
            a' class AttributeEClass :=
              BuildAttribute newId false (getClassName c)
            with [
              ref AttributeTypeEReference :=
                path <- i;
                id <- index path (allPathsTo m 3 c);
                path' <- type_transfer path id (parsePhase ClassGraph2Tree) m "cl" [[ c ]];
                cls <- resolveIter ClassGraph2Tree m "cl" ClassEClass [[ c ]] path';
                return BuildAttributeType a' cls
            ]
        ]
       
    ].

(* ;
          "cl" :
            c' class ClassEClass :=
              BuildClass newId (getClassName c)
            with [
              ref ClassAttributesEReference :=
                path <- i;
                cls <- step m c;
                paths <- type_transfer (nextPaths m path) (parsePhase ClassGraph2Tree) m "cl" [[ c ]];
                attrs <- (optionList2List (zipWith (resolveIter ClassGraph2Tree m "at" AttributeEClass _ _) (map (fun c:Class => [[ c ]]) cls)) paths);
                return BuildClassAttributes c' attrs
            ] *)


Close Scope coqtl.

Definition ClassGraph2Tree := parseTransformation ClassGraph2Tree'.
