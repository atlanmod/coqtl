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
 


(* Definition getFors  (tr: TransformationA ClassMetamodel ClassMetamodel)  : ForExpressionA :=
match (TransformationA_getRules tr) with
|  r :: _ => (RuleA_getForExpression r)
| _ => BuildForExpressionA 999
end.


Definition sp := (Build_ClassMetamodel_EObject ClassEClass (BuildClass "0" "Person")) :: nil.
Definition sm := PersonModel.
Definition tr := ClassGraph2Tree.

(* Compute (
fets <- (evalForExpression (getFors tr) tr sm sp);
path <- nth_error  fets 1 ;
path_id <- index path (allPathsTo sm 1 (BuildClass "0" "Person")); 
cls <- resolveIter tr sm "cl" ClassEClass sp path_id;
Some cls
). *)



Compute (
match matchPattern tr sm sp with
    | nil => None
    | l => Some (map 
(fun r => 

let outs := (RuleA_getOutputPattern r) in
 out <- nth_error outs 2;
Some (beq_string (OutputPatternElementA_getName out) "cl")



(* return optionList2List (flat_map (fun te => flat_map (fun bind => (map (fun fe => applyOutputPatternReferencesOnPatternIter r tr sm sp fe bind te) fets)) binds) tes)
  *)


)
                l) 
end).

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

  ).   *)