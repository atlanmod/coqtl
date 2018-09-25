Require Import String.
Require Import List.

Require Import core.CoqTL.
Require Import core.utils.tPrint.
Require Import core.Model.

Require Import examples.ClassGraph2Tree.ClassMetamodel.
Require Import examples.ClassGraph2Tree.ClassGraph2Tree.
Require Import examples.ClassGraph2Tree.PersonModel.

Require Import core.utils.tTop.


Definition getFors  (tr: TransformationA ClassMetamodel ClassMetamodel)  : ForExpressionA :=
match (TransformationA_getRules tr) with
|  r :: _ => (RuleA_getForExpression r)
| _ => BuildForExpressionA 999 nat
end.



Inductive T : Type :=
  | BuildT
  | EmptyT.

Inductive Er (x: nat) : Set := .


Definition t (x: nat) : option (Er x) := None.

Definition dummy : option nat := Some 1.

Definition tst :=
 o <- dummy;
 match dummy return option (Er o) with
  | Some x => t o
  | _ => None
 end.
  



 



Definition sp := (Build_ClassMetamodel_EObject ClassEClass (BuildClass "0" "Person")) :: nil.


Compute 
( let fe := (getFors ClassGraph2Tree) in
  r <- (nth_error (TransformationA_getRules ClassGraph2Tree) (ForExpressionA_getRule fe)); 
it <- nth_error (optionListToList (evalForExpression fe ClassGraph2Tree PersonModel sp)) 0;
return (map (fun ope  => 
      (evalOutputPatternElementExpressionWithIter (OutputPatternElementA_getOutputPatternElementExpression ope) ClassGraph2Tree PersonModel sp fe it )) 
     (RuleA_getOutputPattern r))). 






(* Compute optionListToList (evalForExpression (getFors ClassGraph2Tree) ClassGraph2Tree PersonModel sp). *)

 Compute execute ClassGraph2Tree PersonModel. 