(** * Metamodel **)
Require Import core.Model.

Class Sum (SumType: Type) (SubTypeName: Type):=
  {
    denoteSubType: SubTypeName -> Set;
    eqSubTypeName_dec: forall (c1:SubTypeName) (c2:SubTypeName), { c1 = c2 } + { c1 <> c2 };
    toSubType: forall (t: SubTypeName), SumType -> option (denoteSubType t);
    toSumType: forall (t: SubTypeName), (denoteSubType t) -> SumType;
    beq_SumType:  SumType -> SumType -> bool;
  }.

Class Metamodel (ModelElement: Type) (ModelLink: Type) (ModelClass: Type) (ModelReference: Type) :=
{
    elements: Sum ModelElement ModelClass;
    links: Sum ModelLink ModelReference;
    (* Denotation *)
    denoteModelClass: ModelClass -> Set := denoteSubType;
    denoteModelReference: ModelReference -> Set := denoteSubType;

    (* Decidability of equality for classes *)
    eqModelClass_dec: forall (c1:ModelClass) (c2:ModelClass), { c1 = c2 } + { c1 <> c2 } := eqSubTypeName_dec;
    eqModelReference_dec: forall (c1:ModelReference) (c2:ModelReference), { c1 = c2 } + { c1 <> c2 } := eqSubTypeName_dec;
  
    (* Downcasting *)
    toModelClass: forall (t:ModelClass), ModelElement -> option (denoteModelClass t) := toSubType;
    toModelReference: forall (t:ModelReference), ModelLink -> option (denoteModelReference t) := toSubType;
  
    (* Upcasting *)
    toModelElement: forall (t: ModelClass), (denoteModelClass t) -> ModelElement := toSumType;
    toModelLink: forall (t: ModelReference), (denoteModelReference t) -> ModelLink := toSumType;
    
    (* Decidable equality for objects *)
    beq_ModelElement:  ModelElement -> ModelElement -> bool := beq_SumType;
}.

Definition hasType {ModelElement ModelLink ModelClass ModelReference: Type} {mm: Metamodel ModelElement ModelLink ModelClass ModelReference}  (t: ModelClass) (e: ModelElement) : bool :=
  match (toModelClass t e) with
  | Some e' => true
  | _ => false
  end.