

type __ = Obj.t

type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type sumbool =
| Left
| Right

type uint =
| Nil0
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

module Little =
 struct
  (** val succ : uint -> uint **)

  let rec succ = function
  | Nil0 -> D1 Nil0
  | D0 d0 -> D1 d0
  | D1 d0 -> D2 d0
  | D2 d0 -> D3 d0
  | D3 d0 -> D4 d0
  | D4 d0 -> D5 d0
  | D5 d0 -> D6 d0
  | D6 d0 -> D7 d0
  | D7 d0 -> D8 d0
  | D8 d0 -> D9 d0
  | D9 d0 -> D0 (succ d0)
 end

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> Left
             | False -> Right)
  | False -> (match b2 with
              | True -> Right
              | False -> Left)

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')
 end

(** val nth_error : 'a1 list -> nat -> 'a1 option **)

let rec nth_error l = function
| O -> (match l with
        | Nil -> None
        | Cons (x, _) -> Some x)
| S n0 -> (match l with
           | Nil -> None
           | Cons (_, l0) -> nth_error l0 n0)

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| Nil -> Nil
| Cons (x, l0) -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f a), (map f t))

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| Nil -> Nil
| Cons (x, t) -> app (f x) (flat_map f t)

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| Nil -> None
| Cons (x, tl) -> (match f x with
                   | True -> Some x
                   | False -> find f tl)

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val ascii_dec : ascii -> ascii -> sumbool **)

let ascii_dec a b =
  let Ascii (x, x0, x1, x2, x3, x4, x5, x6) = a in
  let Ascii (b8, b9, b10, b11, b12, b13, b14, b15) = b in
  (match bool_dec x b8 with
   | Left ->
     (match bool_dec x0 b9 with
      | Left ->
        (match bool_dec x1 b10 with
         | Left ->
           (match bool_dec x2 b11 with
            | Left ->
              (match bool_dec x3 b12 with
               | Left ->
                 (match bool_dec x4 b13 with
                  | Left ->
                    (match bool_dec x5 b14 with
                     | Left -> bool_dec x6 b15
                     | Right -> Right)
                  | Right -> Right)
               | Right -> Right)
            | Right -> Right)
         | Right -> Right)
      | Right -> Right)
   | Right -> Right)

type string =
| EmptyString
| String of ascii * string

(** val string_dec : string -> string -> sumbool **)

let rec string_dec s x =
  match s with
  | EmptyString -> (match x with
                    | EmptyString -> Left
                    | String (_, _) -> Right)
  | String (a, s0) ->
    (match x with
     | EmptyString -> Right
     | String (a0, s1) ->
       (match ascii_dec a a0 with
        | Left -> string_dec s0 s1
        | Right -> Right))

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

module Unsigned =
 struct
  (** val to_lu : nat -> uint **)

  let rec to_lu = function
  | O -> D0 Nil0
  | S n0 -> Little.succ (to_lu n0)
 end

module NilEmpty =
 struct
  (** val string_of_uint : uint -> string **)

  let rec string_of_uint = function
  | Nil0 -> EmptyString
  | D0 d0 ->
    String ((Ascii (False, False, False, False, True, True, False, False)),
      (string_of_uint d0))
  | D1 d0 ->
    String ((Ascii (True, False, False, False, True, True, False, False)),
      (string_of_uint d0))
  | D2 d0 ->
    String ((Ascii (False, True, False, False, True, True, False, False)),
      (string_of_uint d0))
  | D3 d0 ->
    String ((Ascii (True, True, False, False, True, True, False, False)),
      (string_of_uint d0))
  | D4 d0 ->
    String ((Ascii (False, False, True, False, True, True, False, False)),
      (string_of_uint d0))
  | D5 d0 ->
    String ((Ascii (True, False, True, False, True, True, False, False)),
      (string_of_uint d0))
  | D6 d0 ->
    String ((Ascii (False, True, True, False, True, True, False, False)),
      (string_of_uint d0))
  | D7 d0 ->
    String ((Ascii (True, True, True, False, True, True, False, False)),
      (string_of_uint d0))
  | D8 d0 ->
    String ((Ascii (False, False, False, True, True, True, False, False)),
      (string_of_uint d0))
  | D9 d0 ->
    String ((Ascii (True, False, False, True, True, True, False, False)),
      (string_of_uint d0))
 end

module NilZero =
 struct
  (** val string_of_uint : uint -> string **)

  let string_of_uint d = match d with
  | Nil0 ->
    String ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString)
  | _ -> NilEmpty.string_of_uint d
 end

type ('modelElement, 'modelLink) model = { modelElements : 'modelElement list;
                                           modelLinks : 'modelLink list }

(** val modelElements : ('a1, 'a2) model -> 'a1 list **)

let modelElements x = x.modelElements

(** val allModelElements : ('a1, 'a2) model -> 'a1 list **)

let allModelElements =
  modelElements

type ('modelElement, 'modelLink, 'modelClass, 'modelReference) metamodel = { 
toModelClass : ('modelClass -> 'modelElement -> __ option);
toModelReference : ('modelReference -> 'modelLink -> __ option);
bottomModelClass : ('modelClass -> __);
toModelElement : ('modelClass -> __ -> 'modelElement);
toModelLink : ('modelReference -> __ -> 'modelLink);
eqModelClass_dec : ('modelClass -> 'modelClass -> sumbool);
eqModelReference_dec : ('modelReference -> 'modelReference -> sumbool);
buildModelElement : ('modelClass -> __ -> 'modelElement);
buildModelLink : ('modelReference -> __ -> 'modelLink);
getId : ('modelElement -> string);
setId : ('modelElement -> string -> 'modelElement) }

type ('modelElement, 'modelLink, 'modelClass, 'modelReference) denoteModelClass =
  __

type ('modelElement, 'modelLink, 'modelClass, 'modelReference) denoteModelReference =
  __

(** val toModelClass :
    ('a1, 'a2, 'a3, 'a4) metamodel -> 'a3 -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    denoteModelClass option **)

let toModelClass x = x.toModelClass

(** val toModelElement :
    ('a1, 'a2, 'a3, 'a4) metamodel -> 'a3 -> ('a1, 'a2, 'a3, 'a4)
    denoteModelClass -> 'a1 **)

let toModelElement x = x.toModelElement

(** val toModelLink :
    ('a1, 'a2, 'a3, 'a4) metamodel -> 'a4 -> ('a1, 'a2, 'a3, 'a4)
    denoteModelReference -> 'a2 **)

let toModelLink x = x.toModelLink

(** val getId : ('a1, 'a2, 'a3, 'a4) metamodel -> 'a1 -> string **)

let getId x = x.getId

(** val setId : ('a1, 'a2, 'a3, 'a4) metamodel -> 'a1 -> string -> 'a1 **)

let setId x = x.setId

(** val ble_nat : nat -> nat -> bool **)

let rec ble_nat n m =
  match n with
  | O -> True
  | S n' -> (match m with
             | O -> False
             | S m' -> ble_nat n' m')

(** val optionToList : 'a1 option -> 'a1 list **)

let optionToList = function
| Some a -> Cons (a, Nil)
| None -> Nil

(** val optionList2List : 'a1 option list -> 'a1 list **)

let optionList2List l =
  flat_map optionToList l

(** val zipWith : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec zipWith f la lb =
  match la with
  | Nil -> Nil
  | Cons (ea, eas) ->
    (match lb with
     | Nil -> Nil
     | Cons (eb, ebs) -> Cons ((f ea eb), (zipWith f eas ebs)))

(** val prod_cons : 'a1 list -> 'a1 list list -> 'a1 list list **)

let rec prod_cons s1 s2 =
  match s1 with
  | Nil -> Nil
  | Cons (x1, xs1) -> app (map (fun l -> Cons (x1, l)) s2) (prod_cons xs1 s2)

(** val tuples_of_length_n : 'a1 list -> nat -> 'a1 list list **)

let rec tuples_of_length_n s1 = function
| O -> Cons (Nil, Nil)
| S n0 -> prod_cons s1 (tuples_of_length_n s1 n0)

(** val tuples_up_to_n : 'a1 list -> nat -> 'a1 list list **)

let rec tuples_up_to_n s1 = function
| O -> tuples_of_length_n s1 O
| S n0 -> app (tuples_of_length_n s1 (S n0)) (tuples_up_to_n s1 n0)

(** val beq_string : string -> string -> bool **)

let beq_string s1 s2 =
  match string_dec s1 s2 with
  | Left -> True
  | Right -> False

type ('sourceModelElement, 'sourceModelLink) sourceModel =
  ('sourceModelElement, 'sourceModelLink) model

type ('targetModelElement, 'targetModelLink) targetModel =
  ('targetModelElement, 'targetModelLink) model

type ('targetModelElement, 'targetModelLink, 'targetModelClass,
      'targetModelReference) outputPatternElementReference =
| BuildOutputPatternElementReference of 'targetModelReference
   * ('targetModelElement, 'targetModelLink, 'targetModelClass,
     'targetModelReference) denoteModelReference option

(** val outputPatternElementReferenceLink :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a1, 'a2, 'a3, 'a4)
    outputPatternElementReference -> 'a2 option **)

let outputPatternElementReferenceLink tmm = function
| BuildOutputPatternElementReference (type0, link) ->
  (match link with
   | Some ml -> Some (tmm.toModelLink type0 ml)
   | None -> None)

type ('targetModelElement, 'targetModelLink, 'targetModelClass,
      'targetModelReference) outputPatternElement =
| BuildOutputPatternElement of 'targetModelClass * string
   * ('targetModelElement, 'targetModelLink, 'targetModelClass,
     'targetModelReference) denoteModelClass
   * (('targetModelElement, 'targetModelLink, 'targetModelClass,
     'targetModelReference) denoteModelClass -> ('targetModelElement,
     'targetModelLink, 'targetModelClass, 'targetModelReference)
     outputPatternElementReference list)

(** val getOutputPatternElementType :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a1, 'a2, 'a3, 'a4)
    outputPatternElement -> 'a3 **)

let getOutputPatternElementType _ = function
| BuildOutputPatternElement (type0, _, _, _) -> type0

(** val getOutputPatternElementBindings :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a1, 'a2, 'a3, 'a4)
    outputPatternElement -> ('a1, 'a2, 'a3, 'a4) denoteModelClass -> ('a1,
    'a2, 'a3, 'a4) outputPatternElementReference list **)

let getOutputPatternElementBindings _ = function
| BuildOutputPatternElement (_, _, _, refs) -> refs

(** val getOutputPatternElementTargetModelElement :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a1, 'a2, 'a3, 'a4)
    outputPatternElement -> 'a1 **)

let getOutputPatternElementTargetModelElement tmm = function
| BuildOutputPatternElement (outElType, _, x0, _) ->
  tmm.toModelElement outElType x0

type ('sourceModelElement, 'sourceModelLink, 'sourceModelClass,
      'sourceModelReference, 'targetModelElement, 'targetModelLink,
      'targetModelClass, 'targetModelReference) rule =
| BuildMultiElementRule of 'sourceModelClass
   * (('sourceModelElement, 'sourceModelLink, 'sourceModelClass,
     'sourceModelReference) denoteModelClass -> ('sourceModelElement,
     'sourceModelLink, 'sourceModelClass, 'sourceModelReference,
     'targetModelElement, 'targetModelLink, 'targetModelClass,
     'targetModelReference) rule)
| BuildSingleElementRule of 'sourceModelClass
   * (('sourceModelElement, 'sourceModelLink, 'sourceModelClass,
     'sourceModelReference) denoteModelClass -> (bool, ('targetModelElement,
     'targetModelLink, 'targetModelClass, 'targetModelReference)
     outputPatternElement list) prod)

type ('sourceModelElement, 'sourceModelLink, 'sourceModelClass,
      'sourceModelReference, 'targetModelElement, 'targetModelLink,
      'targetModelClass, 'targetModelReference) phase =
  ('sourceModelElement, 'sourceModelLink) sourceModel -> (string,
  ('sourceModelElement, 'sourceModelLink, 'sourceModelClass,
  'sourceModelReference, 'targetModelElement, 'targetModelLink,
  'targetModelClass, 'targetModelReference) rule) prod list

type ('sourceModelElement, 'sourceModelLink, 'sourceModelClass,
      'sourceModelReference, 'targetModelElement, 'targetModelLink,
      'targetModelClass, 'targetModelReference) transformation =
  ('sourceModelElement, 'sourceModelLink, 'sourceModelClass,
  'sourceModelReference, 'targetModelElement, 'targetModelLink,
  'targetModelClass, 'targetModelReference) phase -> ('sourceModelElement,
  'sourceModelLink, 'sourceModelClass, 'sourceModelReference,
  'targetModelElement, 'targetModelLink, 'targetModelClass,
  'targetModelReference) phase

type outputBindingExpressionA =
| BuildOutputBindingExpressionA of nat * nat * nat

(** val outputBindingExpressionA_getRule : outputBindingExpressionA -> nat **)

let outputBindingExpressionA_getRule = function
| BuildOutputBindingExpressionA (y, _, _) -> y

(** val outputBindingExpressionA_getOutputPatternElement :
    outputBindingExpressionA -> nat **)

let outputBindingExpressionA_getOutputPatternElement = function
| BuildOutputBindingExpressionA (_, y, _) -> y

(** val outputBindingExpressionA_getOutputBinding :
    outputBindingExpressionA -> nat **)

let outputBindingExpressionA_getOutputBinding = function
| BuildOutputBindingExpressionA (_, _, y) -> y

type 'targetModelReference outputPatternElementReferenceA =
| BuildOutputPatternElementReferenceA of 'targetModelReference
   * outputBindingExpressionA

(** val outputPatternElementReferenceA_getOutputBindingExpression :
    'a1 outputPatternElementReferenceA -> outputBindingExpressionA **)

let outputPatternElementReferenceA_getOutputBindingExpression = function
| BuildOutputPatternElementReferenceA (_, y) -> y

type outputPatternElementExpressionA =
| BuildOutputPatternElementExpressionA of nat * nat

(** val outputPatternElementExpressionA_getRule :
    outputPatternElementExpressionA -> nat **)

let outputPatternElementExpressionA_getRule = function
| BuildOutputPatternElementExpressionA (y, _) -> y

(** val outputPatternElementExpressionA_getOutputPatternElement :
    outputPatternElementExpressionA -> nat **)

let outputPatternElementExpressionA_getOutputPatternElement = function
| BuildOutputPatternElementExpressionA (_, y) -> y

type ('targetModelClass, 'targetModelReference) outputPatternElementA =
| BuildOutputPatternElementA of string * 'targetModelClass
   * outputPatternElementExpressionA
   * 'targetModelReference outputPatternElementReferenceA list

(** val outputPatternElementA_getOutputPatternElementExpression :
    ('a1, 'a2) outputPatternElementA -> outputPatternElementExpressionA **)

let outputPatternElementA_getOutputPatternElementExpression = function
| BuildOutputPatternElementA (_, _, y, _) -> y

(** val outputPatternElementA_getOutputPatternElementReferences :
    ('a1, 'a2) outputPatternElementA -> 'a2 outputPatternElementReferenceA
    list **)

let outputPatternElementA_getOutputPatternElementReferences = function
| BuildOutputPatternElementA (_, _, _, y) -> y

type guardExpressionA =
  nat
  (* singleton inductive, whose constructor was BuildGuardExpressionA *)

(** val guardExpressionA_getRule : guardExpressionA -> nat **)

let guardExpressionA_getRule x =
  x

type ('sourceModelClass, 'targetModelClass, 'targetModelReference) ruleA =
| BuildRuleA of string * 'sourceModelClass list * guardExpressionA
   * ('targetModelClass, 'targetModelReference) outputPatternElementA list

(** val ruleA_getInTypes : ('a1, 'a2, 'a3) ruleA -> 'a1 list **)

let ruleA_getInTypes = function
| BuildRuleA (_, y, _, _) -> y

(** val ruleA_getGuard : ('a1, 'a2, 'a3) ruleA -> guardExpressionA **)

let ruleA_getGuard = function
| BuildRuleA (_, _, y, _) -> y

(** val ruleA_getOutputPattern :
    ('a1, 'a2, 'a3) ruleA -> ('a2, 'a3) outputPatternElementA list **)

let ruleA_getOutputPattern = function
| BuildRuleA (_, _, _, y) -> y

type ('sourceModelElement, 'sourceModelLink, 'sourceModelClass,
      'sourceModelReference, 'targetModelElement, 'targetModelLink,
      'targetModelClass, 'targetModelReference) transformationA =
| BuildTransformationA of ('sourceModelClass, 'targetModelClass,
                          'targetModelReference) ruleA list
   * ('sourceModelElement, 'sourceModelLink, 'sourceModelClass,
     'sourceModelReference, 'targetModelElement, 'targetModelLink,
     'targetModelClass, 'targetModelReference) transformation

(** val transformationA_getTransformation :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformationA -> ('a1, 'a2, 'a3,
    'a4, 'a5, 'a6, 'a7, 'a8) transformation **)

let transformationA_getTransformation _ _ = function
| BuildTransformationA (_, y) -> y

(** val transformationA_getRules :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformationA -> ('a3, 'a7, 'a8)
    ruleA list **)

let transformationA_getRules _ _ = function
| BuildTransformationA (y, _) -> y

(** val evalOutputBindingExpressionFix :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel ->
    outputBindingExpressionA -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) rule
    -> 'a3 list -> ('a1, 'a2) sourceModel -> 'a1 list -> 'a5 -> 'a6 option **)

let rec evalOutputBindingExpressionFix smm tmm o r intypes sm el te =
  match r with
  | BuildMultiElementRule (s, f) ->
    (match intypes with
     | Nil -> None
     | Cons (_, ts) ->
       (match el with
        | Nil -> None
        | Cons (e, els) ->
          (match smm.toModelClass s e with
           | Some e' ->
             evalOutputBindingExpressionFix smm tmm o (f e') ts sm els te
           | None -> None)))
  | BuildSingleElementRule (s, f) ->
    (match intypes with
     | Nil -> None
     | Cons (_, l) ->
       (match l with
        | Nil ->
          (match el with
           | Nil -> None
           | Cons (e, l0) ->
             (match l0 with
              | Nil ->
                (match smm.toModelClass s e with
                 | Some e' ->
                   (match nth_error (snd (f e'))
                            (outputBindingExpressionA_getOutputPatternElement
                              o) with
                    | Some ope ->
                      (match tmm.toModelClass
                               (getOutputPatternElementType tmm ope) te with
                       | Some te' ->
                         (match nth_error
                                  (getOutputPatternElementBindings tmm ope
                                    te')
                                  (outputBindingExpressionA_getOutputBinding
                                    o) with
                          | Some oper ->
                            outputPatternElementReferenceLink tmm oper
                          | None -> None)
                       | None -> None)
                    | None -> None)
                 | None -> None)
              | Cons (_, _) -> None))
        | Cons (_, _) -> None))

(** val evalOutputBindingExpression :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformationA -> ('a1, 'a2)
    sourceModel -> 'a1 list -> 'a5 -> outputBindingExpressionA -> 'a6 option **)

let evalOutputBindingExpression smm tmm tr sm sp te o =
  match nth_error
          (transformationA_getTransformation smm tmm tr
            (transformationA_getTransformation smm tmm tr (fun _ -> Nil)) sm)
          (outputBindingExpressionA_getRule o) with
  | Some r ->
    (match nth_error (transformationA_getRules smm tmm tr)
             (outputBindingExpressionA_getRule o) with
     | Some ra ->
       evalOutputBindingExpressionFix smm tmm o (snd r) (ruleA_getInTypes ra)
         sm sp te
     | None -> None)
  | None -> None

(** val evalOutputPatternElementExpressionFix :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel ->
    outputPatternElementExpressionA -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7,
    'a8) rule -> 'a3 list -> ('a1, 'a2) sourceModel -> 'a1 list -> 'a5 option **)

let rec evalOutputPatternElementExpressionFix smm tmm o r intypes sm el =
  match r with
  | BuildMultiElementRule (s, f) ->
    (match intypes with
     | Nil -> None
     | Cons (_, ts) ->
       (match el with
        | Nil -> None
        | Cons (e, els) ->
          (match smm.toModelClass s e with
           | Some e' ->
             evalOutputPatternElementExpressionFix smm tmm o (f e') ts sm els
           | None -> None)))
  | BuildSingleElementRule (s, f) ->
    (match intypes with
     | Nil -> None
     | Cons (_, l) ->
       (match l with
        | Nil ->
          (match el with
           | Nil -> None
           | Cons (e, l0) ->
             (match l0 with
              | Nil ->
                (match smm.toModelClass s e with
                 | Some e' ->
                   (match nth_error (snd (f e'))
                            (outputPatternElementExpressionA_getOutputPatternElement
                              o) with
                    | Some ope ->
                      Some (getOutputPatternElementTargetModelElement tmm ope)
                    | None -> None)
                 | None -> None)
              | Cons (_, _) -> None))
        | Cons (_, _) -> None))

(** val evalOutputPatternElementExpression :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformationA -> ('a1, 'a2)
    sourceModel -> 'a1 list -> outputPatternElementExpressionA -> 'a5 option **)

let evalOutputPatternElementExpression smm tmm tr sm sp o =
  match nth_error
          (transformationA_getTransformation smm tmm tr (fun _ -> Nil) sm)
          (outputPatternElementExpressionA_getRule o) with
  | Some r ->
    (match nth_error (transformationA_getRules smm tmm tr)
             (outputPatternElementExpressionA_getRule o) with
     | Some ra ->
       evalOutputPatternElementExpressionFix smm tmm o (snd r)
         (ruleA_getInTypes ra) sm sp
     | None -> None)
  | None -> None

(** val evalGuardExpressionPre :
    ('a2, 'a3, 'a4) ruleA -> 'a1 list -> bool option **)

let evalGuardExpressionPre r sp =
  let lenInTypes = length (ruleA_getInTypes r) in
  let lenSp = length sp in
  (match Nat.eqb lenInTypes lenSp with
   | True -> Some True
   | False -> None)

(** val evalGuardExpressionFix :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) rule -> 'a3 list -> ('a1, 'a2)
    sourceModel -> 'a1 list -> bool option **)

let rec evalGuardExpressionFix smm tmm r intypes sm el =
  match r with
  | BuildMultiElementRule (s, f) ->
    (match intypes with
     | Nil -> None
     | Cons (_, ts) ->
       (match el with
        | Nil -> None
        | Cons (e, els) ->
          (match smm.toModelClass s e with
           | Some e' -> evalGuardExpressionFix smm tmm (f e') ts sm els
           | None -> None)))
  | BuildSingleElementRule (s, f) ->
    (match intypes with
     | Nil -> None
     | Cons (_, l) ->
       (match l with
        | Nil ->
          (match el with
           | Nil -> None
           | Cons (e, l0) ->
             (match l0 with
              | Nil ->
                (match smm.toModelClass s e with
                 | Some e' -> Some (fst (f e'))
                 | None -> None)
              | Cons (_, _) -> None))
        | Cons (_, _) -> None))

(** val evalGuardExpression :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel ->
    guardExpressionA -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8)
    transformationA -> ('a1, 'a2) sourceModel -> 'a1 list -> bool option **)

let evalGuardExpression smm tmm o tr sm sp =
  match nth_error
          (transformationA_getTransformation smm tmm tr (fun _ -> Nil) sm)
          (guardExpressionA_getRule o) with
  | Some r ->
    (match nth_error (transformationA_getRules smm tmm tr)
             (guardExpressionA_getRule o) with
     | Some ra ->
       evalGuardExpressionFix smm tmm (snd r) (ruleA_getInTypes ra) sm sp
     | None -> None)
  | None -> None

(** val getSourcePatternId :
    ('a1, 'a2, 'a3, 'a4) metamodel -> 'a1 list -> string **)

let rec getSourcePatternId smm = function
| Nil ->
  String ((Ascii (True, True, True, True, True, False, True, False)),
    EmptyString)
| Cons (se, ses) ->
  append (smm.getId se)
    (append (String ((Ascii (True, True, True, True, True, False, True,
      False)), EmptyString)) (getSourcePatternId smm ses))

(** val setTargetElementId :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> 'a5
    -> ('a3, 'a7, 'a8) ruleA -> ('a7, 'a8) outputPatternElementA -> 'a1 list
    -> 'a5 **)

let setTargetElementId smm tmm te _ ope sp =
  match beq_string (tmm.getId te) EmptyString with
  | True ->
    let BuildOutputPatternElementExpressionA (a, b) =
      outputPatternElementA_getOutputPatternElementExpression ope
    in
    tmm.setId te
      (append (getSourcePatternId smm sp)
        (append (NilZero.string_of_uint (Unsigned.to_lu a))
          (append (String ((Ascii (True, True, True, True, True, False, True,
            False)), EmptyString))
            (NilZero.string_of_uint (Unsigned.to_lu b)))))
  | False -> te

(** val instantiateRuleOnPattern :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a3,
    'a7, 'a8) ruleA -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8)
    transformationA -> ('a1, 'a2) sourceModel -> 'a1 list -> 'a5 list option **)

let instantiateRuleOnPattern smm tmm r tr sm sp =
  match evalGuardExpressionPre r sp with
  | Some _ ->
    (match evalGuardExpression smm tmm (ruleA_getGuard r) tr sm sp with
     | Some m ->
       (match m with
        | True ->
          Some
            (optionList2List
              (map (fun ope ->
                match evalOutputPatternElementExpression smm tmm tr sm sp
                        (outputPatternElementA_getOutputPatternElementExpression
                          ope) with
                | Some te -> Some (setTargetElementId smm tmm te r ope sp)
                | None -> None) (ruleA_getOutputPattern r)))
        | False -> None)
     | None -> None)
  | None -> None

(** val applyOutputPatternReferencesOnPattern :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformationA -> ('a1, 'a2)
    sourceModel -> 'a1 list -> 'a8 outputPatternElementReferenceA list -> 'a5
    -> 'a6 list **)

let applyOutputPatternReferencesOnPattern smm tmm tr sm sp l te =
  optionList2List
    (map (evalOutputBindingExpression smm tmm tr sm sp te)
      (map outputPatternElementReferenceA_getOutputBindingExpression l))

(** val applyRuleOnPattern :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a3,
    'a7, 'a8) ruleA -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8)
    transformationA -> ('a1, 'a2) sourceModel -> 'a1 list -> 'a5 list -> 'a6
    list option **)

let applyRuleOnPattern smm tmm r tr sm sp tes =
  Some
    (concat
      (zipWith (applyOutputPatternReferencesOnPattern smm tmm tr sm sp)
        (map outputPatternElementA_getOutputPatternElementReferences
          (ruleA_getOutputPattern r)) tes))

(** val matchRuleOnPattern :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a3,
    'a7, 'a8) ruleA -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8)
    transformationA -> ('a1, 'a2) sourceModel -> 'a1 list -> bool option **)

let matchRuleOnPattern smm tmm r tr sm sp =
  evalGuardExpression smm tmm (ruleA_getGuard r) tr sm sp

(** val matchPattern :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformationA -> ('a1, 'a2)
    sourceModel -> 'a1 list -> ('a3, 'a7, 'a8) ruleA option **)

let matchPattern smm tmm tr sm sp =
  find (fun r ->
    match matchRuleOnPattern smm tmm r tr sm sp with
    | Some b -> b
    | None -> False) (transformationA_getRules smm tmm tr)

(** val instantiatePattern :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformationA -> ('a1, 'a2)
    sourceModel -> 'a1 list -> 'a5 list option **)

let instantiatePattern smm tmm tr sm sp =
  match matchPattern smm tmm tr sm sp with
  | Some r -> instantiateRuleOnPattern smm tmm r tr sm sp
  | None -> None

(** val applyPattern :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformationA -> ('a1, 'a2)
    sourceModel -> 'a1 list -> 'a6 list option **)

let applyPattern smm tmm tr sm sp =
  match matchPattern smm tmm tr sm sp with
  | Some r ->
    (match instantiateRuleOnPattern smm tmm r tr sm sp with
     | Some tes -> applyRuleOnPattern smm tmm r tr sm sp tes
     | None -> None)
  | None -> None

(** val max : nat list -> nat **)

let rec max = function
| Nil -> O
| Cons (a, m) ->
  (match m with
   | Nil -> a
   | Cons (_, _) ->
     let b = max m in (match ble_nat a b with
                       | True -> b
                       | False -> a))

(** val maxArity :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformationA -> nat **)

let maxArity smm tmm tr =
  max
    (map length (map ruleA_getInTypes (transformationA_getRules smm tmm tr)))

(** val allTuples :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformationA -> ('a1, 'a2)
    sourceModel -> 'a1 list list **)

let allTuples smm tmm tr sm =
  tuples_up_to_n (allModelElements sm) (maxArity smm tmm tr)

(** val execute :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformationA -> ('a1, 'a2)
    sourceModel -> ('a5, 'a6) targetModel **)

let execute smm tmm tr sm =
  { modelElements =
    (concat
      (optionList2List
        (map (instantiatePattern smm tmm tr sm) (allTuples smm tmm tr sm))));
    modelLinks =
    (concat
      (optionList2List
        (map (applyPattern smm tmm tr sm) (allTuples smm tmm tr sm)))) }

