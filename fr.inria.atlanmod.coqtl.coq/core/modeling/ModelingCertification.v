Require Import String.
Require Import Omega.
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.Engine.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.Syntax.
Require Import core.modeling.ModelingEngine.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingTransformationConfiguration.


Section IterateTracesCertification.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}. 

(** * Resolve *)

(* Theorem tr_resolveAll_in:
  forall (tls: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sps: list(list SourceModelElement)),
    resolveAll tls sm name type sps = resolveAllIter tls sm name type sps 0.
Proof.
  crush.
Qed. *)

Theorem tr_resolveAllIter_in:
  forall (tls: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sps: list(list SourceModelElement)) (iter: nat)
    (te: denoteModelClass type),
    (exists tes: list (denoteModelClass type),
        resolveAllIter tls sm name type sps iter = Some tes /\ In te tes) <->
    (exists (sp: list SourceModelElement),
        In sp sps /\
        resolveIter tls sm name type sp iter = Some te).
Proof.
  intros.
      intros.
  split.
  - intros.
    destruct H. destruct H.
    unfold resolveAllIter in H.
    inversion H.
    rewrite <- H2 in H0.
    apply in_flat_map in H0.
    destruct H0. destruct H0.
    destruct ((toModelClass type x0)) eqn: type_cast_ca; simpl in H1.
    + destruct H1.
      ++ apply in_flat_map in H0.
         destruct H0. destruct H0.
         exists x1.
         split.
         * exact H0.
         * unfold resolveIter.
           destruct (Semantics.resolveIter tls sm name x1 iter); crush.
      ++ contradiction.
    + contradiction.
  - intro.
    destruct H. destruct H.
    destruct (resolveAllIter tls sm name type sps iter) eqn: resolveAll.
    --  exists l. split. auto.
        unfold resolveAllIter in resolveAll.
        inversion resolveAll.
        apply in_flat_map.
        unfold resolveIter in H0.
        destruct (Semantics.resolveIter tls sm name x iter) eqn: resolve_ca; simpl in H0.
        * exists t. 
          split.
          ** apply in_flat_map.
             exists x.
             split.
             *** auto.
             *** rewrite resolve_ca. simpl. auto.
          ** rewrite H0. simpl. left. auto. 
        * simpl in H0. inversion H0.
    --  unfold resolveAllIter in resolveAll.
        crush.
Qed.

(* Theorem tr_resolve_in:
  forall (tls: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sp: list SourceModelElement),
    resolve tls sm name type sp = resolveIter tls sm name type sp 0.
Proof.
  crush.
Qed. *)

(* this one direction, the other one is not true since exists cannot gurantee uniqueness in find *)
Theorem tr_resolveIter_leaf:
  forall (tls:list TraceLink) (sm : SourceModel) (name: string) (type: TargetModelClass)
    (sp: list SourceModelElement) (iter: nat) (x: denoteModelClass type),
    resolveIter tls sm name type sp iter = return x ->
      (exists (tl : TraceLink),
        In tl tls /\
        Is_true (list_beq SourceModelElement SourceElement_eqb (TraceLink_getSourcePattern tl) sp) /\
        ((TraceLink_getIterator tl) = iter) /\ 
        ((TraceLink_getName tl) = name)%string /\
        (toModelClass type (TraceLink_getTargetElement tl) = Some x)). 
Proof.
intros.
unfold resolveIter in H.
destruct (Semantics.resolveIter tls sm name sp iter) eqn: resolve_ca.
- simpl in H.
  unfold Semantics.resolveIter in resolve_ca.
  destruct ( find
               (fun tl : TraceLink =>
                Semantics.list_beq SourceModelElement SourceElement_eqb
                  (TraceLink_getSourcePattern tl) sp &&
                (TraceLink_getIterator tl =? iter) &&
                (TraceLink_getName tl =? name)%string)) eqn: find_ca.
  -- apply find_some in find_ca.
     destruct find_ca.
     exists t0.
     symmetry in H1.
     apply andb_true_eq in H1.
     destruct H1.
     apply andb_true_eq in H1.
     destruct H1.
     crush.
     --- apply beq_nat_true. crush.
     --- apply String.eqb_eq. crush.
  -- inversion resolve_ca.
- simpl in H. inversion H.
Qed.


Instance ModelingCoqTLEngine :
  ModelingTransformationEngine tc mtc:=
  {
    SourceModelClass := SourceModelClass;
    SourceModelReference := SourceModelReference;
    TargetModelClass := TargetModelClass;
    TargetModelReference := TargetModelReference;

    resolveAll := resolveAllIter;
    resolve := resolveIter;

    (* lemmas *)

    tr_resolveAll_in := tr_resolveAllIter_in;
    tr_resolve_Leaf := tr_resolveIter_leaf;
  }. 

End IterateTracesCertification.