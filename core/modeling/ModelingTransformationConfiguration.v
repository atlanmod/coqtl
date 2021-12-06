Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingMetamodel.

Class ModelingTransformationConfiguration `(tc: TransformationConfiguration):= {

  smm: ModelingMetamodel SourceMetamodel;
  tmm: ModelingMetamodel TargetMetamodel;

  SourceModelClass:= @ModelClass _ smm;
  SourceModelReference:= @ModelReference _ smm;
  TargetModelClass:= @ModelClass _ tmm;
  TargetModelReference:= @ModelReference _ tmm;  

  denoteSourceModelClass:= @denoteModelClass _ smm;
}.