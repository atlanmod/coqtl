Require Import String.
Require Import List.

Require Import core.CoqTL.
Require Import core.utils.tPrint.
Require Import core.Model.

Require Import examples.ClassGraph2Tree.ClassMetamodel.
Require Import examples.ClassGraph2Tree.ClassGraph2Tree.
Require Import examples.ClassGraph2Tree.PersonModel.
Require Import core.utils.tTop.
Compute execute ClassGraph2Tree PersonModel. 



Definition getFors  (tr: TransformationA ClassMetamodel ClassMetamodel)  : ForExpressionA :=
match (TransformationA_getRules tr) with
|  r :: _ => (RuleA_getForExpression r)
| _ => BuildForExpressionA 999
end.


Definition sp := (Build_ClassMetamodel_EObject ClassEClass (BuildClass "0" "Person")) :: nil.
Definition sm := PersonModel.
Definition tr := ClassGraph2Tree.



Compute (applyPattern tr sm sp).

Compute 
( let f := (getFors ClassGraph2Tree) in
  ope <- (find_OutputPatternElementA tr sm sp "cl");
  r <- Some (OutputPatternElementExpressionA_getRule (OutputPatternElementA_getOutputPatternElementExpression ope));
  ra <- (nth_error (TransformationA_getRules tr) r);
  fe_res <- (evalForExpression f tr sm sp);
  fet <- nth_error fe_res 0;
  let  opee := (OutputPatternElementA_getOutputPatternElementExpression ope) in 
   tfe <- ForExpressionA_getForSectionType2OutputPatternElementExpressionA f opee tr sp sm fet;
  (evalOutputPatternElementExpressionWithIter (OutputPatternElementA_getOutputPatternElementExpression ope) tr sm sp tfe)

  ).  