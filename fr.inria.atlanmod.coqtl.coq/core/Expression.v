Require Import String.

Require Import core.utils.Utils.
Require Import core.Syntax.
Require Import core.modeling.Metamodel.
Require Import core.Model.

Section Expressions.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}.
  Context {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}.
  Context {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}.
  Context {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}.
  Context (SourceModel := Model SourceModelElement SourceModelLink).
  Context (TargetModel := Model TargetModelElement TargetModelLink).

  Definition Expr (A: Type) (B: Type) : Type := A -> B.


  (* we then need mult instance of this type class, e.g.
     one for guard expression, one for outpattern etc.
     how we can choose which Instance's evalExpr to be executed at runtime?
   *)
  Class Expression {A : Type} {B: Type} :=
    { evalExpr : Expr A B -> A -> B ; }.

End Expressions.