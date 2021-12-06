Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.

Require Import core.utils.Utils.
Require Import core.Engine.
Require Import core.TransformationConfiguration.
Require Import core.SyntaxCertification.
Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingEngine.
Require Import core.modeling.ModelingTransformationConfiguration.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.


(* a small example on user proof based on child specification *)

Theorem resolve_trivial:
forall 
  (eng : @TransformationEngine C2RConfiguration CoqTLSyntax)
  (meng: ModelingTransformationEngine Class2RelationalConfiguration eng) 
  (cm : ClassModel) (c: Class) tls o,
  (@resolve _ _ _ _ meng tls cm "tab" TableClass [ClassMetamodel_toObject ClassClass c] 1) = Some o ->
  (exists (tl : TraceLink.TraceLink), In tl tls).
Proof.
intros.
apply tr_resolve_leaf in H.
destruct H.
destruct H.
exists x.
auto.
Qed.