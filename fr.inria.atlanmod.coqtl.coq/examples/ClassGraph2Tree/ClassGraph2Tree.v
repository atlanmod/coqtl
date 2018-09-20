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
                path' <- path_type_transfer id (parsePhase ClassGraph2Tree) m "cl" [[ c ]];
                cls <- resolveIter ClassGraph2Tree m "cl" ClassEClass [[ c ]] path';
                return BuildAttributeType a' cls
            ];
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
            ]
        ]
       
    ].

(*  *)


Close Scope coqtl.

Definition ClassGraph2Tree := parseTransformation ClassGraph2Tree'.
