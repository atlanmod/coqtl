Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import RSS2ATOM.ATOM.
Require Import RSS2ATOM.RSS.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

#[export]
Instance R2AConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration RSSMetamodel_Metamodel_Instance ATOMMetamodel_Metamodel_Instance.

#[export]
Instance RSS2ATOMConfiguration : ModelingTransformationConfiguration R2AConfiguration :=
 Build_ModelingTransformationConfiguration R2AConfiguration RSSMetamodel_ModelingMetamodel_Instance ATOMMetamodel_ModelingMetamodel_Instance.

Open Scope coqtl.

Definition RSS2ATOM :=
  transformation nil.

Close Scope coqtl.