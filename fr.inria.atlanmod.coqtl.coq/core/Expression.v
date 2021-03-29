Require Import String.

Require Import core.utils.Utils.
Require Import core.Syntax.
Require Import core.modeling.Metamodel.
Require Import core.Model.

Section Expressions.

  (* we then need mult instance of this type class, e.g.
     one for guard expression, one for outpattern etc.
     how we can choose which Instance's evalExpr to be executed at runtime?
   *)
  Class Expression :=
    { 
      (*ExprType : forall (A B: Type), Type;*)
      Expr2 (A: Type) (B: Type) (C: Type): Type;
      evalExpr2 (A B C:Type) (f: Expr2 A B C) (a: A) (b: B): C; 
    }.

End Expressions.
