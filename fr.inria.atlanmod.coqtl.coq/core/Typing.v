(** * Typing Class **)

Class Typing (Element: Type) (Class: Type) :=
  {
    (* Denotation to concrete type *)
    denoteClass: Class -> Set;

    (* Downcasting from Root Class *)
    toSubElement: forall (c: Class), Element -> option (denoteClass c);

    (* Upcasting to Element of Top Class *)
    toTopElement: forall (c: Class), (denoteClass c) -> Element;

    (* Default object of each class *)
    DefaultElements: forall (c: Class), (denoteClass c);
  }.
