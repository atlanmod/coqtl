Require Import core.Engine.
Require Import core.test.iSyntax.
Require Import core.test.iSemantics.
Require Import core.test.iExpressions.
Require Import core.TransformationConfiguration.

Section SyntaxCertification.

Context {tc: TransformationConfiguration}.

Definition evalOutputPatternLinkExpr_wrapper (sm: SourceModel) (sp: list SourceModelElement) (oe: TargetModelElement) (iter: nat)
            (l: list TraceLink) (o: OutputPatternElement)
  : option (list TargetModelLink) :=
(evalOutputPatternLinkExpr sm sp oe (resolveIter l) iter o).

Instance CoqTLSyntax :
  TransformationSyntax tc :=
  {
      (* syntax and accessors *)

      Transformation := Transformation;
      Rule := Rule;
      OutputPatternElement := OutputPatternElement;

      TraceLink := TraceLink;

      Transformation_getArity := Transformation_getArity;
      Transformation_getRules := Transformation_getRules;

      Rule_getOutputPatternElements := Rule_getOutputPatternElements;

      TraceLink_getSourcePattern := TraceLink_getSourcePattern;
      TraceLink_getIterator := TraceLink_getIterator;
      TraceLink_getName := TraceLink_getName;
      TraceLink_getTargetElement := TraceLink_getTargetElement;    
      
      evalOutputPatternElementExpr := evalOutputPatternElementExpr;
      evalIteratorExpr := evalIteratorExpr;
      evalOutputPatternLinkExpr := evalOutputPatternLinkExpr_wrapper;
      evalGuardExpr := evalGuardExpr;
  }.

End SyntaxCertification.