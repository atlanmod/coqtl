Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.test.iSyntax.
Require Import core.EqDec. 
Require Import Bool.
Require Import Arith.
Require Import TransformationConfiguration.
Scheme Equality for list.


Section Expressions.

Context {tc: TransformationConfiguration}.

(*Definition Expr1 (A: Type) (B: Type) : Type := A -> B.
Definition Expr2 (A: Type) (B: Type) (C: Type) : Type := A -> B -> C.
Definition Expr3 (A: Type) (B: Type) (C: Type) (D: Type): Type := A -> B -> C -> D.
Definition Expr4 (A: Type) (B: Type) (C: Type) (D: Type) (E: Type): Type := A -> B -> C -> D -> E.
Definition Expr5 (A: Type) (B: Type) (C: Type) (D: Type) (E: Type) (F: Type): Type := A -> B -> C -> D -> E -> F.

Definition evalExpr1 {A B:Type} (f: Expr1 A B) (a: A) := f a.
Definition evalExpr2 {A B C:Type} (f: Expr2 A B C) (a: A) (b: B):= f a b.
Definition evalExpr3 {A B C D:Type} (f: Expr3 A B C D) (a: A) (b: B) (c: C) := f a b c.
Definition evalExpr4 {A B C D E:Type} (f: Expr4 A B C D E) (a: A) (b: B) (c: C) (d: D):= f a b c d.
Definition evalExpr5 {A B C D E F:Type} (f: Expr5 A B C D E F) (a: A) (b: B) (c: C) (d: D) (e: E):= f a b c d e.*)

(*   Instance baseExpression :
  Expression := {
    Expr2 {A B C: Type} := A -> B -> C;
    evalExpr2 {A B C:Type} (f: A -> B -> C) (a: A) (b: B) := f a b;
  }. *)

Definition Expr (A: Type) (B: Type) : Type := A -> B.
Definition evalExpr {A B:Type} (f: Expr A B) (a: A) := f a.

Definition evalGuardExpr (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
evalExpr (Rule_getGuardExpr r) sm sp.

Definition evalIteratorExpr (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) :
  nat :=
  match (evalExpr (Rule_getIteratorExpr r) sm sp) with
  | Some n => n
  | _ => 0
  end.

Definition evalOutputPatternElementExpr (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (o: OutputPatternElement)
  : option TargetModelElement := 
(evalExpr (OutputPatternElement_getElementExpr o) iter sm sp).

Definition evalOutputPatternLinkExpr
            (sm: SourceModel) (sp: list SourceModelElement) (oe: TargetModelElement) resolve (iter: nat)
            (o: OutputPatternElement)
  : option (list TargetModelLink) :=
(evalExpr (OutputPatternElement_getLinkExpr o) resolve iter sm sp oe).

End Expressions.
