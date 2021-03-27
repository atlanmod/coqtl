Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.Metamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import core.modeling.Expressions.
Require Import core.modeling.ConcreteSyntax.

(* parse Concrete syntax into abstract syntax. *)

Section Parser.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}.
  Context {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}.
  Context {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}.
  Context {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}.
  Context (SourceModel := Model SourceModelElement SourceModelLink).
  Context (TargetModel := Model TargetModelElement TargetModelLink).
  Context (Transformation := @Transformation SourceModelElement SourceModelLink TargetModelElement TargetModelLink).
  Context (TraceLink := @TraceLink SourceModelElement TargetModelElement).


  Definition parseOutputPatternElementReference (intypes: list SourceModelClass) (outtype: TargetModelClass)
    (cr: ConcreteOutputPatternElementReference intypes outtype): OutputPatternElementReference :=
    buildOutputPatternElementReference 
      (makeLink intypes outtype (ConcreteOutputPatternElementReference_getRefType cr) (ConcreteOutputPatternElementReference_getOutputReference cr)).

  Definition parseOutputPatternElement (intypes: list SourceModelClass) (co: ConcreteOutputPatternElement intypes) : OutputPatternElement :=
    buildOutputPatternElement
      (ConcreteOutputPatternElement_getName co)
      (makeElement intypes (ConcreteOutputPatternElement_getOutType co) (ConcreteOutputPatternElement_getOutPatternElement co))
      (map (parseOutputPatternElementReference intypes (ConcreteOutputPatternElement_getOutType co)) (ConcreteOutputPatternElement_getOutputElementReferences co)).

  Definition parseRule(cr: ConcreteRule (smm:=smm)) : Rule :=
    buildRule
      (ConcreteRule_getName cr)
      (match ConcreteRule_getGuard cr with
      | Some g => (makeGuard (ConcreteRule_getInTypes cr) g)
      | None => (fun _ _ => Some true)
      end)
      (match ConcreteRule_getIteratedList cr with
      | Some i => (makeIterator (ConcreteRule_getInTypes cr) i)
      | None => (fun _ _ => Some 1)
      end)
      (map (parseOutputPatternElement (ConcreteRule_getInTypes (smm:=smm) cr)) (ConcreteRule_getConcreteOutputPattern cr)).
  
  Definition parse(ct: ConcreteTransformation (smm:=smm)) : Transformation :=
    buildTransformation 
      (max (map (length (A:=SourceModelClass)) (map (ConcreteRule_getInTypes (smm:=smm)) (ConcreteTransformation_getConcreteRules (smm:=smm) ct))   ))
      (map parseRule (ConcreteTransformation_getConcreteRules ct)).

End Parser.

