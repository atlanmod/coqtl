Require Import core.Engine.
Require Import core.Syntax.
Require Import core.TransformationConfiguration.
Require Import core.Expressions.

Section SyntaxCertification.

Context {tc: TransformationConfiguration}.

Instance CoqTLSyntax :
  TransformationSyntax tc :=
  {
      (* syntax and accessors *)

      Transformation := Transformation;
      Rule := Rule;
      OutputPatternElement := OutputPatternElement;
      OutputPatternLink := OutputPatternLink;

      TraceLink := TraceLink;

      Transformation_getArity := Transformation_getArity;
      Transformation_getRules := Transformation_getRules;

      Rule_getOutputPatternElements := Rule_getOutputPatternElements;

      OutputPatternElement_getOutputLinks := OutputPatternElement_getOutputLinks;

      TraceLink_getSourcePattern := TraceLink_getSourcePattern;
      TraceLink_getIterator := TraceLink_getIterator;
      TraceLink_getName := TraceLink_getName;
      TraceLink_getTargetElement := TraceLink_getTargetElement;    
      
      evalOutputPatternElementExpr := evalOutputPatternElementExpr;
      evalIteratorExpr := evalIteratorExpr;
      evalOutputPatternLinkExpr := evalOutputPatternLinkExpr;
      evalGuardExpr := evalGuardExpr;
  }.

End SyntaxCertification.