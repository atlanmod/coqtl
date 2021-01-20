Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.
Require Import core.Engine.
Require Import core.Syntax.
Require Import core.Certification.

Scheme Equality for list.

Set Implicit Arguments.

(* class TransformationSystem ts where
    apply :: ts -> ts
    getFromTarget :: ts -> Element -> (SetOf Element,ts)
    getRootFromTarget :: ts -> Element
    addElementToSource :: Element -> ts -> ts
    deleteElementFromSource :: Element -> ts -> ts
    addLinkToSource :: Link -> ts -> ts
        *)

Section TransformationSystem.

    Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
    {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
    {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
    {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
    (SourceModel := Model SourceModelElement SourceModelLink)
    (TargetModel := Model TargetModelElement TargetModelLink)
    (Transformation := @Transformation SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink).

    Class TransformationSystemClass :=
    {
        TransformationSystem: Type;

        apply: TransformationSystem -> TransformationSystem;

        (* navigating an outgoing link in the target*)
        getFromTarget: TransformationSystem -> TargetModelElement -> TargetModelReference -> (list TargetModelElement * TransformationSystem);
        
        getRootFromTarget: TransformationSystem -> TargetModelElement;
        addElementToSource: SourceModelElement -> TransformationSystem -> TransformationSystem;
        deleteElementFromSource: SourceModelElement -> TransformationSystem -> TransformationSystem;
        addLinkToSource: SourceModelLink -> TransformationSystem -> TransformationSystem
    }.

    Inductive StrictTransformation :=
    | buildStrictTransformation: SourceModel -> Transformation -> TransformationEngine -> TargetModel -> StrictTransformation.

    (*Require Import examples.Class2Relational.Class2RelationalAbstract.
    Require Import examples.Class2Relational.tests.PersonTest.
    Require Import examples.Class2Relational.tests.PersonModel.

    Definition c2r: StrictTransformation :=
        buildStrictTransformation (Build_Model nil nil) Class2Relational CoqTLEngine (Build_Model nil).
    *)

    Instance StrictTransformationSystem : TransformationSystemClass.
    Admitted.
    (*eexists.
    * exact (fun ts:StrictTransformation => 
        match ts with
        buildStrictTransformation sm tr tre tm => buildStrictTransformation sm tr tre (execute tr sm)
        end
      ).*)

    (*  Example of program with output:
        {
            getRootFromTarget ts;      -> te
            addElementToSource se ts;
            getFromTarget ts te tmr;   -> list te
            getRootFromTarget ts;      -> te
            addLinkToSource sml;
        }
    *)

End TransformationSystem.
