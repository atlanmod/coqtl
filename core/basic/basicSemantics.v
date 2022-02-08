Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.basic.basicSyntax.
Require Import core.EqDec. 
Require Import Bool.
Require Import Arith.
Require Import TransformationConfiguration.
Require Import core.basic.basicExpressions.
Scheme Equality for list.


Section Semantics.

Context {tc: TransformationConfiguration}.

(** * Instantiate **)

Definition matchRuleOnPattern (r: Rule) (sm : SourceModel) (sp: list SourceModelElement) : bool :=
  match evalGuardExpr r sm sp with Some true => true | _ => false end.

Definition matchPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list Rule :=
  filter (fun (r:Rule) => matchRuleOnPattern r sm sp) (Transformation_getRules tr).

Definition instantiateElementOnPattern (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat)
  : option TargetModelElement :=
  evalOutputPatternElementExpr sm sp iter o.

Definition instantiateIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) :  list TargetModelElement :=
  flat_map (fun o => optionToList (instantiateElementOnPattern o sm sp iter))
    (Rule_getOutputPatternElements r).

Definition instantiateRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) :  list TargetModelElement :=
  flat_map (instantiateIterationOnPattern r sm sp)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition instantiatePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TargetModelElement :=
  flat_map (fun r => instantiateRuleOnPattern r sm sp) (matchPattern tr sm sp).

Definition instantiateRuleOnPatternIterName (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (name: string): option (TargetModelElement) :=
  match (Rule_findOutputPatternElement r name) with
  | Some o =>  instantiateElementOnPattern o sm sp iter
  | None => None
  end.

Definition maxArity (tr: Transformation) : nat := Transformation_getArity tr.

Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
  tuples_up_to_n (allModelElements sm) (maxArity tr).

Definition resolveIter (tr: Transformation) (sm: SourceModel) (name: string) (sp: list SourceModelElement) (iter : nat) : option TargetModelElement :=
let matchedRule := find (fun r:Rule => matchRuleOnPattern r sm sp) (Transformation_getRules tr) in
match matchedRule with
  | Some r =>  (instantiateRuleOnPatternIterName r sm sp iter name)
  | None => None
end.

(** * Apply **)

Definition applyElementOnPattern
            (ope: OutputPatternElement)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: list SourceModelElement) (iter: nat) : list TargetModelLink :=
  match (evalOutputPatternElementExpr sm sp iter ope) with 
  | Some l => optionListToList (evalOutputPatternLinkExpr sm sp l (resolveIter tr) iter ope)
  | None => nil
  end.

Definition applyIterationOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : list TargetModelLink :=
  flat_map (fun o => applyElementOnPattern o tr sm sp iter)
    (Rule_getOutputPatternElements r).

Definition applyRuleOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement): list TargetModelLink :=
  flat_map (applyIterationOnPattern r tr sm sp)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition applyPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TargetModelLink :=
  flat_map (fun r => applyRuleOnPattern r tr sm sp) (matchPattern tr sm sp).

(** * Execute **)

Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  Build_Model
    (* elements *) (flat_map (instantiatePattern tr sm) (allTuples tr sm))
    (* links *) (flat_map (applyPattern tr sm) (allTuples tr sm)).

End Semantics.
