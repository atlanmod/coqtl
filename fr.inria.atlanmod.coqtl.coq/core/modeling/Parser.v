Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.ConcreteSyntax.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

(* parse Concrete syntax into abstract syntax. *)

Section Parser.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.

Definition parseOutputPatternLink (intypes: list SourceModelClass) (outtype: TargetModelClass)
  (cr: ConcreteOutputPatternLink intypes outtype) := 
    (makeLink intypes outtype (ConcreteOutputPatternLink_getRefType cr) (ConcreteOutputPatternLink_getOutputPatternLink cr)).

Definition parseOutputPatternLinks (intypes: list SourceModelClass) (outtype: TargetModelClass)
  (cr: list (ConcreteOutputPatternLink intypes outtype)) := 
    fun (tls:list TraceLink) (iter:nat) (sm:SourceModel) (sp: list SourceModelElement) (te: TargetModelElement) =>
    Some (flat_map (fun (x: ConcreteOutputPatternLink intypes outtype) => optionListToList (parseOutputPatternLink intypes outtype x tls iter sm sp te)) cr).

Definition parseOutputPatternElement (intypes: list SourceModelClass) (co: ConcreteOutputPatternElement intypes) : OutputPatternElement :=
  buildOutputPatternElement
    (ConcreteOutputPatternElement_getName co)
    (makeElement intypes (ConcreteOutputPatternElement_getOutType co) (ConcreteOutputPatternElement_getOutPatternElement co))
    (parseOutputPatternLinks intypes (ConcreteOutputPatternElement_getOutType co) (ConcreteOutputPatternElement_getOutputLinks co)).

Definition parseRule(cr: ConcreteRule) : Rule :=
  buildRule
    (ConcreteRule_getName cr)
    (match ConcreteRule_getGuard cr with
    | Some g => (makeGuard (ConcreteRule_getInTypes cr) g)
    | None => (makeEmptyGuard (ConcreteRule_getInTypes cr))
    end)
    (match ConcreteRule_getIteratedList cr with
    | Some i => (makeIterator (ConcreteRule_getInTypes cr) i)
    | None => (fun _ _ => Some 1)
    end)
    (map (parseOutputPatternElement (ConcreteRule_getInTypes cr)) (ConcreteRule_getConcreteOutputPattern cr)).

Definition parse(ct: ConcreteTransformation) : Transformation :=
  buildTransformation 
    (max (map (length (A:=SourceModelClass)) (map ConcreteRule_getInTypes (ConcreteTransformation_getConcreteRules ct))   ))
    (map parseRule (ConcreteTransformation_getConcreteRules ct)).

End Parser.

