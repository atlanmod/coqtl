Require Import core.Model.
Require Import core.Metamodel.

Class TransformationConfiguration := {
  SourceMetamodel: Metamodel;
  TargetMetamodel: Metamodel;

  SourceModelElement:= @ModelElement SourceMetamodel;
  SourceModelLink:= @ModelLink SourceMetamodel;

  TargetModelElement:= @ModelElement TargetMetamodel;
  TargetModelLink:= @ModelLink TargetMetamodel;

  SourceModel := @InstanceModel SourceMetamodel;
  TargetModel := @InstanceModel TargetMetamodel;

  SourceElement_eqdec := @elements_eqdec SourceMetamodel;
  TargetElement_eqdec := @elements_eqdec TargetMetamodel;

  SourceElement_eqb := @elements_eqb SourceMetamodel;
  TargetElement_eqb := @elements_eqb TargetMetamodel;
}.