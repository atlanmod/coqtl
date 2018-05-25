(** * Metamodel **)

Class Metamodel (ModelElement: Type) (ModelLink: Type) (ModelClass: Type) (ModelReference: Type) :=
  {
    (* Denotation *)
    denoteModelClass: ModelClass -> Set;
    denoteModelReference: ModelReference -> Set;

    (* Downcasting *)
    toModelClass: forall (t:ModelClass), ModelElement -> option (denoteModelClass t);
    toModelReference: forall (t:ModelReference), ModelLink -> option (denoteModelReference t);

    (* Default object of that class *)
    bottomModelClass: forall (c:ModelClass), (denoteModelClass c);

    (* Upcasting *)
    toModelElement: forall (t: ModelClass), (denoteModelClass t) -> ModelElement;
    toModelLink: forall (t: ModelReference), (denoteModelReference t) -> ModelLink;
    
    (* Decidability of equality *)
    eqModelClass_dec: forall (c1:ModelClass) (c2:ModelClass), { c1 = c2 } + { c1 <> c2 };
    eqModelReference_dec: forall (c1:ModelReference) (c2:ModelReference), { c1 = c2 } + { c1 <> c2 };

    (* Constructors *)
    BuildModelElement: forall (r: ModelClass), (denoteModelClass r) -> ModelElement;
    BuildModelLink:  forall (r: ModelReference), (denoteModelReference r) -> ModelLink;
  }.
