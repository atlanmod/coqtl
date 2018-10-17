(** * Metamodel **)
Require Import String.


Class Iterator (IteratorElement: Type) (IteratorClass: Type) :=
  {
    (* Denotation *)
    denoteIteratorClass: IteratorClass -> Set;

    (* Downcasting *)
    toIteratorClass: forall (t:IteratorClass), IteratorElement -> option (denoteIteratorClass t);

    (* Upcasting *)
    toIteratorElement: forall (t: IteratorClass), (denoteIteratorClass t) -> IteratorElement;
    
    (* Decidability of equality *)
    eqIteratorClass_dec: forall (c1:IteratorClass) (c2:IteratorClass), { c1 = c2 } + { c1 <> c2 };

    (* Constructors *)
    BuildIteratorElement: forall (r: IteratorClass), (denoteIteratorClass r) -> IteratorElement;

  }.
