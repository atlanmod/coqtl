Require Import String.

Require Import core.utils.Utils.
Require Import core.Syntax.
Require Import core.modeling.Metamodel.
Require Import core.Model.

Section Expressions.

  (*Definition Expr (A: Type) (B: Type) : Type := A -> B.*)


  (* we then need mult instance of this type class, e.g.
     one for guard expression, one for outpattern etc.
     how we can choose which Instance's evalExpr to be executed at runtime?
   *)
  Class Expression :=
    { 
      ExprType : forall (A B: Type), Type;
      evalExpr : forall (A B:Type), ExprType A B -> (A -> B) ; 
    }.

  Instance baseExpression :
    Expression := {
      ExprType (A B: Type) := A -> B;
      evalExpr {A B:Type} (f: A -> B) (a: A) := f a;
    }.

End Expressions.
Check evalExpr.
Arguments ExprType {_ _}.
Arguments evalExpr {_ _}.
