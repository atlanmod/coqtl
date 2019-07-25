

type __ = Obj.t

type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

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

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> Left
             | False -> Right)
  | False -> (match b2 with
              | True -> Right
              | False -> Left)

(** val nth_error : 'a1 list -> nat -> 'a1 option **)

let rec nth_error l = function
| O -> (match l with
        | Nil -> None
        | Cons (x, _) -> Some x)
| S n0 -> (match l with
           | Nil -> None
           | Cons (_, l0) -> nth_error l0 n0)

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

(** val modelLinks : ('a1, 'a2) model -> 'a2 list **)

let modelLinks x = x.modelLinks

(** val allModelLinks : ('a1, 'a2) model -> 'a2 list **)

let allModelLinks =
  modelLinks

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

(** val bottomModelClass :
    ('a1, 'a2, 'a3, 'a4) metamodel -> 'a3 -> ('a1, 'a2, 'a3, 'a4)
    denoteModelClass **)

let bottomModelClass x = x.bottomModelClass

(** val toModelElement :
    ('a1, 'a2, 'a3, 'a4) metamodel -> 'a3 -> ('a1, 'a2, 'a3, 'a4)
    denoteModelClass -> 'a1 **)

let toModelElement x = x.toModelElement

(** val getId : ('a1, 'a2, 'a3, 'a4) metamodel -> 'a1 -> string **)

let getId x = x.getId

(** val setId : ('a1, 'a2, 'a3, 'a4) metamodel -> 'a1 -> string -> 'a1 **)

let setId x = x.setId

(** val optionToList : 'a1 option -> 'a1 list **)

let optionToList = function
| Some a -> Cons (a, Nil)
| None -> Nil

(** val optionList2List : 'a1 option list -> 'a1 list **)

let optionList2List l =
  flat_map optionToList l

(** val mapWithIndex : (nat -> 'a1 -> 'a2) -> nat -> 'a1 list -> 'a2 list **)

let rec mapWithIndex f n = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f n a), (mapWithIndex f (add n (S O)) t))

(** val beq_string : string -> string -> bool **)

let beq_string s1 s2 =
  match string_dec s1 s2 with
  | Left -> True
  | Right -> False

type ('sourceModelElement, 'sourceModelLink) sourceModel =
  ('sourceModelElement, 'sourceModelLink) model

type ('targetModelElement, 'targetModelLink, 'targetModelClass,
      'targetModelReference) outputPatternElementReference =
| BuildOutputPatternElementReference of 'targetModelReference
   * ('targetModelElement, 'targetModelLink, 'targetModelClass,
     'targetModelReference) denoteModelReference option

type ('targetModelElement, 'targetModelLink, 'targetModelClass,
      'targetModelReference) outputPatternElement =
| BuildOutputPatternElement of 'targetModelClass * string
   * ('targetModelElement, 'targetModelLink, 'targetModelClass,
     'targetModelReference) denoteModelClass
   * (('targetModelElement, 'targetModelLink, 'targetModelClass,
     'targetModelReference) denoteModelClass -> ('targetModelElement,
     'targetModelLink, 'targetModelClass, 'targetModelReference)
     outputPatternElementReference list)

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

type 'targetModelReference outputPatternElementReferenceA =
| BuildOutputPatternElementReferenceA of 'targetModelReference
   * outputBindingExpressionA

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

(** val outputPatternElementA_getName :
    ('a1, 'a2) outputPatternElementA -> string **)

let outputPatternElementA_getName = function
| BuildOutputPatternElementA (y, _, _, _) -> y

(** val outputPatternElementA_getOutputPatternElementExpression :
    ('a1, 'a2) outputPatternElementA -> outputPatternElementExpressionA **)

let outputPatternElementA_getOutputPatternElementExpression = function
| BuildOutputPatternElementA (_, _, y, _) -> y

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

(** val parseOutputPatternElementReference :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformation -> nat -> nat -> nat ->
    ('a5, 'a6, 'a7, 'a8) outputPatternElementReference -> 'a8
    outputPatternElementReferenceA **)

let parseOutputPatternElementReference _ _ _ r ope oper = function
| BuildOutputPatternElementReference (t, _) ->
  BuildOutputPatternElementReferenceA (t, (BuildOutputBindingExpressionA (r,
    ope, oper)))

(** val parseOutputPatternElement :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformation -> nat -> nat -> ('a5,
    'a6, 'a7, 'a8) outputPatternElement -> ('a7, 'a8) outputPatternElementA **)

let parseOutputPatternElement smm tmm tr r ope = function
| BuildOutputPatternElement (t, n, _, f) ->
  BuildOutputPatternElementA (n, t, (BuildOutputPatternElementExpressionA (r,
    ope)),
    (mapWithIndex (parseOutputPatternElementReference smm tmm tr r ope) O
      (f (tmm.bottomModelClass t))))

(** val parseRuleOutput :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformation -> nat -> ('a1, 'a2,
    'a3, 'a4, 'a5, 'a6, 'a7, 'a8) rule -> ('a7, 'a8) outputPatternElementA
    list **)

let rec parseRuleOutput smm tmm tr n = function
| BuildMultiElementRule (iet, f) ->
  parseRuleOutput smm tmm tr n (f (smm.bottomModelClass iet))
| BuildSingleElementRule (iet, f) ->
  mapWithIndex (parseOutputPatternElement smm tmm tr n) O
    (snd (f (smm.bottomModelClass iet)))

(** val parseRuleTypes :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) rule -> 'a3 list **)

let rec parseRuleTypes smm tmm = function
| BuildMultiElementRule (iet, f) ->
  Cons (iet, (parseRuleTypes smm tmm (f (smm.bottomModelClass iet))))
| BuildSingleElementRule (iet, _) -> Cons (iet, Nil)

(** val parseRuleDeclaration :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformation -> nat -> (string,
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) rule) prod -> ('a3, 'a7, 'a8)
    ruleA **)

let parseRuleDeclaration smm tmm tr n r =
  BuildRuleA ((fst r), (parseRuleTypes smm tmm (snd r)), n,
    (parseRuleOutput smm tmm tr n (snd r)))

(** val parseTransformation :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) transformation -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7, 'a8) transformationA **)

let parseTransformation smm tmm tr =
  BuildTransformationA
    ((mapWithIndex (parseRuleDeclaration smm tmm tr) O
       (tr (fun _ -> Nil) { modelElements = Nil; modelLinks = Nil })), tr)

(** val parsePhase :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) phase -> ('a1, 'a2, 'a3, 'a4, 'a5,
    'a6, 'a7, 'a8) transformationA **)

let parsePhase smm tmm tr =
  parseTransformation smm tmm (fun _ -> tr)

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

(** val resolveFix :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a3,
    'a7, 'a8) ruleA list -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8)
    transformationA -> ('a1, 'a2) sourceModel -> string -> 'a7 -> 'a1 list ->
    ('a5, 'a6, 'a7, 'a8) denoteModelClass option **)

let resolveFix smm tmm _ tr sm name type0 sp =
  match matchPattern smm tmm tr sm sp with
  | Some r ->
    (match find (fun oel ->
             beq_string (outputPatternElementA_getName oel) name)
             (ruleA_getOutputPattern r) with
     | Some ope ->
       (match evalOutputPatternElementExpression smm tmm tr sm sp
                (outputPatternElementA_getOutputPatternElementExpression ope) with
        | Some te ->
          tmm.toModelClass type0 (setTargetElementId smm tmm te r ope sp)
        | None -> None)
     | None -> None)
  | None -> None

(** val resolve :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) phase -> ('a1, 'a2) sourceModel ->
    string -> 'a7 -> 'a1 list -> ('a5, 'a6, 'a7, 'a8) denoteModelClass option **)

let resolve smm tmm tr sm name type0 sp =
  resolveFix smm tmm
    (transformationA_getRules smm tmm (parsePhase smm tmm tr))
    (parsePhase smm tmm tr) sm name type0 sp

(** val resolveAll :
    ('a1, 'a2, 'a3, 'a4) metamodel -> ('a5, 'a6, 'a7, 'a8) metamodel -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8) phase -> ('a1, 'a2) sourceModel ->
    string -> 'a7 -> 'a1 list list -> ('a5, 'a6, 'a7, 'a8) denoteModelClass
    list option **)

let resolveAll smm tmm tr sm name type0 sps =
  Some (optionList2List (map (resolve smm tmm tr sm name type0) sps))

type stateMachine =
| BuildStateMachine of string * string

type transition =
| BuildTransition of string * string

type initialState =
| BuildInitialState of string * string

type regularState =
| BuildRegularState of string * string

type compositeState =
| BuildCompositeState of string * string

type abstractState_EClass =
| InitialStateEClass
| RegularStateEClass
| CompositeStateEClass

type abstractState_getTypeByEClass = __

type abstractState =
| BuildAbstractState of abstractState_EClass * abstractState_getTypeByEClass

type stateMachineStates =
| BuildStateMachineStates of stateMachine * abstractState list

type transitionStateMachine =
| BuildTransitionStateMachine of transition * stateMachine

type transitionSource =
| BuildTransitionSource of transition * abstractState

type transitionTarget =
| BuildTransitionTarget of transition * abstractState

type abstractStateStateMachine =
| BuildAbstractStateStateMachine of abstractState * stateMachine

type abstractStateCompositeState =
| BuildAbstractStateCompositeState of abstractState * compositeState

(** val stateMachine_getName : stateMachine -> string **)

let stateMachine_getName = function
| BuildStateMachine (name, _) -> name

(** val stateMachine_getStateMachineID : stateMachine -> string **)

let stateMachine_getStateMachineID = function
| BuildStateMachine (_, stateMachineID) -> stateMachineID

(** val transition_getLabel : transition -> string **)

let transition_getLabel = function
| BuildTransition (label, _) -> label

(** val transition_getTransitionID : transition -> string **)

let transition_getTransitionID = function
| BuildTransition (_, transitionID) -> transitionID

(** val abstractState_getName : abstractState -> string **)

let abstractState_getName = function
| BuildAbstractState (hsec_arg, a0) ->
  (match hsec_arg with
   | InitialStateEClass ->
     let BuildInitialState (name, _) = Obj.magic a0 in name
   | RegularStateEClass ->
     let BuildRegularState (name, _) = Obj.magic a0 in name
   | CompositeStateEClass ->
     let BuildCompositeState (name, _) = Obj.magic a0 in name)

(** val abstractState_getAbstractStateID : abstractState -> string **)

let abstractState_getAbstractStateID = function
| BuildAbstractState (hsec_arg, a0) ->
  (match hsec_arg with
   | InitialStateEClass -> let BuildInitialState (_, id) = Obj.magic a0 in id
   | RegularStateEClass -> let BuildRegularState (_, id) = Obj.magic a0 in id
   | CompositeStateEClass ->
     let BuildCompositeState (_, id) = Obj.magic a0 in id)

(** val initialState_getName : initialState -> string **)

let initialState_getName = function
| BuildInitialState (name, _) -> name

(** val initialState_getInitialStateID : initialState -> string **)

let initialState_getInitialStateID = function
| BuildInitialState (_, initialStateID) -> initialStateID

(** val regularState_getName : regularState -> string **)

let regularState_getName = function
| BuildRegularState (name, _) -> name

(** val regularState_getRegularStateID : regularState -> string **)

let regularState_getRegularStateID = function
| BuildRegularState (_, regularStateID) -> regularStateID

(** val compositeState_getName : compositeState -> string **)

let compositeState_getName = function
| BuildCompositeState (name, _) -> name

(** val compositeState_getCompositeStateID : compositeState -> string **)

let compositeState_getCompositeStateID = function
| BuildCompositeState (_, compositeStateID) -> compositeStateID

type hSMMetamodel_EClass =
| StateMachineEClass
| TransitionEClass
| AbstractStateEClass

type hSMMetamodel_getTypeByEClass = __

type hSMMetamodel_EReference =
| StateMachineTransitionsEReference
| StateMachineStatesEReference
| TransitionStateMachineEReference
| TransitionSourceEReference
| TransitionTargetEReference
| AbstractStateStateMachineEReference
| AbstractStateCompositeStateEReference
| CompositeStateStatesEReference

type hSMMetamodel_getTypeByEReference = __

type hSMMetamodel_EObject =
| Build_HSMMetamodel_EObject of hSMMetamodel_EClass
   * hSMMetamodel_getTypeByEClass

type hSMMetamodel_ELink =
| Build_HSMMetamodel_ELink of hSMMetamodel_EReference
   * hSMMetamodel_getTypeByEReference

(** val hSMMetamodel_eqEClass_dec :
    hSMMetamodel_EClass -> hSMMetamodel_EClass -> sumbool **)

let hSMMetamodel_eqEClass_dec hsec_arg1 hsec_arg2 =
  match hsec_arg1 with
  | StateMachineEClass ->
    (match hsec_arg2 with
     | StateMachineEClass -> Left
     | _ -> Right)
  | TransitionEClass ->
    (match hsec_arg2 with
     | TransitionEClass -> Left
     | _ -> Right)
  | AbstractStateEClass ->
    (match hsec_arg2 with
     | AbstractStateEClass -> Left
     | _ -> Right)

(** val hSMMetamodel_eqEReference_dec :
    hSMMetamodel_EReference -> hSMMetamodel_EReference -> sumbool **)

let hSMMetamodel_eqEReference_dec hser_arg1 hser_arg2 =
  match hser_arg1 with
  | StateMachineTransitionsEReference ->
    (match hser_arg2 with
     | StateMachineTransitionsEReference -> Left
     | _ -> Right)
  | StateMachineStatesEReference ->
    (match hser_arg2 with
     | StateMachineStatesEReference -> Left
     | _ -> Right)
  | TransitionStateMachineEReference ->
    (match hser_arg2 with
     | TransitionStateMachineEReference -> Left
     | _ -> Right)
  | TransitionSourceEReference ->
    (match hser_arg2 with
     | TransitionSourceEReference -> Left
     | _ -> Right)
  | TransitionTargetEReference ->
    (match hser_arg2 with
     | TransitionTargetEReference -> Left
     | _ -> Right)
  | AbstractStateStateMachineEReference ->
    (match hser_arg2 with
     | AbstractStateStateMachineEReference -> Left
     | _ -> Right)
  | AbstractStateCompositeStateEReference ->
    (match hser_arg2 with
     | AbstractStateCompositeStateEReference -> Left
     | _ -> Right)
  | CompositeStateStatesEReference ->
    (match hser_arg2 with
     | CompositeStateStatesEReference -> Left
     | _ -> Right)

(** val abstractState_eqEClass_dec :
    abstractState_EClass -> abstractState_EClass -> sumbool **)

let abstractState_eqEClass_dec hsec_arg1 hsec_arg2 =
  match hsec_arg1 with
  | InitialStateEClass ->
    (match hsec_arg2 with
     | InitialStateEClass -> Left
     | _ -> Right)
  | RegularStateEClass ->
    (match hsec_arg2 with
     | RegularStateEClass -> Left
     | _ -> Right)
  | CompositeStateEClass ->
    (match hsec_arg2 with
     | CompositeStateEClass -> Left
     | _ -> Right)

(** val abstractState_getEClass : abstractState -> abstractState_EClass **)

let abstractState_getEClass = function
| BuildAbstractState (hseo_arg0, _) -> hseo_arg0

(** val abstractState_instanceOfEClass :
    abstractState_EClass -> abstractState -> bool **)

let abstractState_instanceOfEClass hsec_arg hseo_arg =
  match abstractState_eqEClass_dec (abstractState_getEClass hseo_arg) hsec_arg with
  | Left -> True
  | Right -> False

(** val hSMMetamodel_toEClass :
    hSMMetamodel_EClass -> hSMMetamodel_EObject ->
    hSMMetamodel_getTypeByEClass option **)

let hSMMetamodel_toEClass hsec_arg = function
| Build_HSMMetamodel_EObject (arg1, arg2) ->
  let s = hSMMetamodel_eqEClass_dec arg1 hsec_arg in
  (match s with
   | Left -> Some arg2
   | Right -> None)

(** val hSMMetamodel_AbstractState_downcast :
    abstractState_EClass -> abstractState -> abstractState_getTypeByEClass
    option **)

let hSMMetamodel_AbstractState_downcast t = function
| BuildAbstractState (arg1, arg2) ->
  let s = abstractState_eqEClass_dec arg1 t in
  (match s with
   | Left -> Some arg2
   | Right -> None)

(** val hSMMetamodel_toEReference :
    hSMMetamodel_EReference -> hSMMetamodel_ELink ->
    hSMMetamodel_getTypeByEReference option **)

let hSMMetamodel_toEReference hser_arg = function
| Build_HSMMetamodel_ELink (arg1, arg2) ->
  let s = hSMMetamodel_eqEReference_dec arg1 hser_arg in
  (match s with
   | Left -> Some arg2
   | Right -> None)

(** val hSMMetamodel_toEObjectFromStateMachine :
    stateMachine -> hSMMetamodel_EObject **)

let hSMMetamodel_toEObjectFromStateMachine st_arg =
  Build_HSMMetamodel_EObject (StateMachineEClass, (Obj.magic st_arg))

(** val hSMMetamodel_toEObjectFromTransition :
    transition -> hSMMetamodel_EObject **)

let hSMMetamodel_toEObjectFromTransition tr_arg =
  Build_HSMMetamodel_EObject (TransitionEClass, (Obj.magic tr_arg))

(** val hSMMetamodel_toEObjectFromAbstractState :
    abstractState -> hSMMetamodel_EObject **)

let hSMMetamodel_toEObjectFromAbstractState ab_arg =
  Build_HSMMetamodel_EObject (AbstractStateEClass, (Obj.magic ab_arg))

(** val hSMMetamodel_toEObject :
    hSMMetamodel_EObject -> hSMMetamodel_EObject **)

let hSMMetamodel_toEObject hseo_arg =
  hseo_arg

type hSMModel = (hSMMetamodel_EObject, hSMMetamodel_ELink) model

(** val hSMMetamodel_toEObjectOfEClass :
    hSMMetamodel_EClass -> hSMMetamodel_getTypeByEClass ->
    hSMMetamodel_EObject **)

let hSMMetamodel_toEObjectOfEClass hsec_arg t =
  Build_HSMMetamodel_EObject (hsec_arg, t)

(** val hSMMetamodel_toELinkOfEReference :
    hSMMetamodel_EReference -> hSMMetamodel_getTypeByEReference ->
    hSMMetamodel_ELink **)

let hSMMetamodel_toELinkOfEReference hser_arg t =
  Build_HSMMetamodel_ELink (hser_arg, t)

(** val beq_StateMachine : stateMachine -> stateMachine -> bool **)

let beq_StateMachine st_arg1 st_arg2 =
  match beq_string (stateMachine_getName st_arg1)
          (stateMachine_getName st_arg2) with
  | True ->
    beq_string (stateMachine_getStateMachineID st_arg1)
      (stateMachine_getStateMachineID st_arg2)
  | False -> False

(** val beq_Transition : transition -> transition -> bool **)

let beq_Transition tr_arg1 tr_arg2 =
  match beq_string (transition_getLabel tr_arg1) (transition_getLabel tr_arg2) with
  | True ->
    beq_string (transition_getTransitionID tr_arg1)
      (transition_getTransitionID tr_arg2)
  | False -> False

(** val beq_InitialState : initialState -> initialState -> bool **)

let beq_InitialState in_arg1 in_arg2 =
  match beq_string (initialState_getName in_arg1)
          (initialState_getName in_arg2) with
  | True ->
    beq_string (initialState_getInitialStateID in_arg1)
      (initialState_getInitialStateID in_arg2)
  | False -> False

(** val beq_RegularState : regularState -> regularState -> bool **)

let beq_RegularState re_arg1 re_arg2 =
  match beq_string (regularState_getName re_arg1)
          (regularState_getName re_arg2) with
  | True ->
    beq_string (regularState_getRegularStateID re_arg1)
      (regularState_getRegularStateID re_arg2)
  | False -> False

(** val beq_CompositeState : compositeState -> compositeState -> bool **)

let beq_CompositeState co_arg1 co_arg2 =
  match beq_string (compositeState_getName co_arg1)
          (compositeState_getName co_arg2) with
  | True ->
    beq_string (compositeState_getCompositeStateID co_arg1)
      (compositeState_getCompositeStateID co_arg2)
  | False -> False

(** val beq_AbstractState : abstractState -> abstractState -> bool **)

let beq_AbstractState ab_arg1 ab_arg2 =
  let BuildAbstractState (hsec_arg, e1) = ab_arg1 in
  (match hsec_arg with
   | InitialStateEClass ->
     let BuildAbstractState (hsec_arg0, e2) = ab_arg2 in
     (match hsec_arg0 with
      | InitialStateEClass -> beq_InitialState (Obj.magic e1) (Obj.magic e2)
      | _ -> False)
   | RegularStateEClass ->
     let BuildAbstractState (hsec_arg0, e2) = ab_arg2 in
     (match hsec_arg0 with
      | RegularStateEClass -> beq_RegularState (Obj.magic e1) (Obj.magic e2)
      | _ -> False)
   | CompositeStateEClass ->
     let BuildAbstractState (hsec_arg0, e2) = ab_arg2 in
     (match hsec_arg0 with
      | CompositeStateEClass ->
        beq_CompositeState (Obj.magic e1) (Obj.magic e2)
      | _ -> False))

(** val stateMachine_getStatesOnLinks :
    stateMachine -> hSMMetamodel_ELink list -> abstractState list option **)

let rec stateMachine_getStatesOnLinks st_arg = function
| Nil -> None
| Cons (h, l') ->
  let Build_HSMMetamodel_ELink (hser_arg, h0) = h in
  (match hser_arg with
   | StateMachineStatesEReference ->
     let BuildStateMachineStates (stateMachine_ctr, states_ctr) = Obj.magic h0
     in
     (match beq_StateMachine stateMachine_ctr st_arg with
      | True -> Some states_ctr
      | False -> stateMachine_getStatesOnLinks st_arg l')
   | _ -> stateMachine_getStatesOnLinks st_arg l')

(** val stateMachine_getStates :
    stateMachine -> hSMModel -> abstractState list option **)

let stateMachine_getStates st_arg m =
  stateMachine_getStatesOnLinks st_arg (allModelLinks m)

(** val transition_getStateMachineOnLinks :
    transition -> hSMMetamodel_ELink list -> stateMachine option **)

let rec transition_getStateMachineOnLinks tr_arg = function
| Nil -> None
| Cons (h, l') ->
  let Build_HSMMetamodel_ELink (hser_arg, h0) = h in
  (match hser_arg with
   | TransitionStateMachineEReference ->
     let BuildTransitionStateMachine (transition_ctr, stateMachine_ctr) =
       Obj.magic h0
     in
     (match beq_Transition transition_ctr tr_arg with
      | True -> Some stateMachine_ctr
      | False -> transition_getStateMachineOnLinks tr_arg l')
   | _ -> transition_getStateMachineOnLinks tr_arg l')

(** val transition_getStateMachine :
    transition -> hSMModel -> stateMachine option **)

let transition_getStateMachine tr_arg m =
  transition_getStateMachineOnLinks tr_arg (allModelLinks m)

(** val transition_getSourceOnLinks :
    transition -> hSMMetamodel_ELink list -> abstractState option **)

let rec transition_getSourceOnLinks tr_arg = function
| Nil -> None
| Cons (h, l') ->
  let Build_HSMMetamodel_ELink (hser_arg, h0) = h in
  (match hser_arg with
   | TransitionSourceEReference ->
     let BuildTransitionSource (transition_ctr, source_ctr) = Obj.magic h0 in
     (match beq_Transition transition_ctr tr_arg with
      | True -> Some source_ctr
      | False -> transition_getSourceOnLinks tr_arg l')
   | _ -> transition_getSourceOnLinks tr_arg l')

(** val transition_getSource :
    transition -> hSMModel -> abstractState option **)

let transition_getSource tr_arg m =
  transition_getSourceOnLinks tr_arg (allModelLinks m)

(** val transition_getTargetOnLinks :
    transition -> hSMMetamodel_ELink list -> abstractState option **)

let rec transition_getTargetOnLinks tr_arg = function
| Nil -> None
| Cons (h, l') ->
  let Build_HSMMetamodel_ELink (hser_arg, h0) = h in
  (match hser_arg with
   | TransitionTargetEReference ->
     let BuildTransitionTarget (transition_ctr, target_ctr) = Obj.magic h0 in
     (match beq_Transition transition_ctr tr_arg with
      | True -> Some target_ctr
      | False -> transition_getTargetOnLinks tr_arg l')
   | _ -> transition_getTargetOnLinks tr_arg l')

(** val transition_getTarget :
    transition -> hSMModel -> abstractState option **)

let transition_getTarget tr_arg m =
  transition_getTargetOnLinks tr_arg (allModelLinks m)

(** val abstractState_getStateMachineOnLinks :
    abstractState -> hSMMetamodel_ELink list -> stateMachine option **)

let rec abstractState_getStateMachineOnLinks ab_arg = function
| Nil -> None
| Cons (h, l') ->
  let Build_HSMMetamodel_ELink (hser_arg, h0) = h in
  (match hser_arg with
   | AbstractStateStateMachineEReference ->
     let BuildAbstractStateStateMachine (abstractState_ctr, stateMachine_ctr) =
       Obj.magic h0
     in
     (match beq_AbstractState abstractState_ctr ab_arg with
      | True -> Some stateMachine_ctr
      | False -> abstractState_getStateMachineOnLinks ab_arg l')
   | _ -> abstractState_getStateMachineOnLinks ab_arg l')

(** val abstractState_getStateMachine :
    abstractState -> hSMModel -> stateMachine option **)

let abstractState_getStateMachine ab_arg m =
  abstractState_getStateMachineOnLinks ab_arg (allModelLinks m)

(** val abstractState_getCompositeStateOnLinks :
    abstractState -> hSMMetamodel_ELink list -> compositeState option **)

let rec abstractState_getCompositeStateOnLinks ab_arg = function
| Nil -> None
| Cons (h, l') ->
  let Build_HSMMetamodel_ELink (hser_arg, h0) = h in
  (match hser_arg with
   | AbstractStateCompositeStateEReference ->
     let BuildAbstractStateCompositeState (abstractState_ctr,
                                           compositeState_ctr) = Obj.magic h0
     in
     (match beq_AbstractState abstractState_ctr ab_arg with
      | True -> Some compositeState_ctr
      | False -> abstractState_getCompositeStateOnLinks ab_arg l')
   | _ -> abstractState_getCompositeStateOnLinks ab_arg l')

(** val abstractState_getCompositeState :
    abstractState -> hSMModel -> compositeState option **)

let abstractState_getCompositeState ab_arg m =
  abstractState_getCompositeStateOnLinks ab_arg (allModelLinks m)

(** val hSMMetamodel_defaultInstanceOfEClass :
    hSMMetamodel_EClass -> hSMMetamodel_getTypeByEClass **)

let hSMMetamodel_defaultInstanceOfEClass = function
| StateMachineEClass ->
  Obj.magic (BuildStateMachine (EmptyString, EmptyString))
| TransitionEClass -> Obj.magic (BuildTransition (EmptyString, EmptyString))
| AbstractStateEClass ->
  Obj.magic (BuildAbstractState (InitialStateEClass,
    (Obj.magic (BuildInitialState (EmptyString, EmptyString)))))

(** val hSMMetamodel_getId : hSMMetamodel_EObject -> string **)

let hSMMetamodel_getId = function
| Build_HSMMetamodel_EObject (hsec_arg, h) ->
  (match hsec_arg with
   | StateMachineEClass -> stateMachine_getStateMachineID (Obj.magic h)
   | TransitionEClass -> transition_getTransitionID (Obj.magic h)
   | AbstractStateEClass -> abstractState_getAbstractStateID (Obj.magic h))

(** val hSMMetamodel_setId :
    hSMMetamodel_EObject -> string -> hSMMetamodel_EObject **)

let hSMMetamodel_setId a s =
  let Build_HSMMetamodel_EObject (hsec_arg, h) = a in
  (match hsec_arg with
   | StateMachineEClass ->
     hSMMetamodel_toEObjectFromStateMachine (BuildStateMachine (s,
       (stateMachine_getStateMachineID (Obj.magic h))))
   | TransitionEClass ->
     hSMMetamodel_toEObjectFromTransition (BuildTransition (s,
       (transition_getTransitionID (Obj.magic h))))
   | AbstractStateEClass ->
     hSMMetamodel_toEObjectFromStateMachine (BuildStateMachine (s, (String
       ((Ascii (False, False, True, False, True, False, True, False)),
       (String ((Ascii (True, True, True, True, False, False, True, False)),
       (String ((Ascii (False, False, True, False, False, False, True,
       False)), (String ((Ascii (True, True, True, True, False, False, True,
       False)), EmptyString)))))))))))

(** val hSMMetamodel :
    (hSMMetamodel_EObject, hSMMetamodel_ELink, hSMMetamodel_EClass,
    hSMMetamodel_EReference) metamodel **)

let hSMMetamodel =
  { toModelClass = hSMMetamodel_toEClass; toModelReference =
    hSMMetamodel_toEReference; bottomModelClass =
    hSMMetamodel_defaultInstanceOfEClass; toModelElement =
    hSMMetamodel_toEObjectOfEClass; toModelLink =
    hSMMetamodel_toELinkOfEReference; eqModelClass_dec =
    hSMMetamodel_eqEClass_dec; eqModelReference_dec =
    hSMMetamodel_eqEReference_dec; buildModelElement = (fun x x0 ->
    Build_HSMMetamodel_EObject (x, x0)); buildModelLink = (fun x x0 ->
    Build_HSMMetamodel_ELink (x, x0)); getId = hSMMetamodel_getId; setId =
    hSMMetamodel_setId }

(** val isNone : 'a1 option -> bool **)

let isNone = function
| Some _ -> False
| None -> True

(** val abstractState_instanceOfEClass_optional :
    abstractState_EClass -> abstractState option -> bool **)

let abstractState_instanceOfEClass_optional hsec_arg = function
| Some e -> abstractState_instanceOfEClass hsec_arg e
| None -> False

(** val beq_AbstractState_option :
    abstractState option -> abstractState option -> bool **)

let beq_AbstractState_option tr_arg1 tr_arg2 =
  match tr_arg1 with
  | Some a1 ->
    (match tr_arg2 with
     | Some a2 -> beq_AbstractState a1 a2
     | None -> False)
  | None -> False

(** val beq_CompositeState_option :
    compositeState option -> compositeState option -> bool **)

let beq_CompositeState_option tr_arg1 tr_arg2 =
  match tr_arg1 with
  | Some a1 ->
    (match tr_arg2 with
     | Some a2 -> beq_CompositeState a1 a2
     | None -> False)
  | None -> False

(** val hSM2FSMConcrete :
    (hSMMetamodel_EObject, hSMMetamodel_ELink, hSMMetamodel_EClass,
    hSMMetamodel_EReference, hSMMetamodel_EObject, hSMMetamodel_ELink,
    hSMMetamodel_EClass, hSMMetamodel_EReference) phase -> hSMModel ->
    (string, (hSMMetamodel_EObject, hSMMetamodel_ELink, hSMMetamodel_EClass,
    hSMMetamodel_EReference, hSMMetamodel_EObject, hSMMetamodel_ELink,
    hSMMetamodel_EClass, hSMMetamodel_EReference) rule) prod list **)

let hSM2FSMConcrete hSM2FSM m =
  Cons ((Pair (EmptyString, (BuildSingleElementRule (StateMachineEClass,
    (fun sm1 -> Pair (True, (Cons ((BuildOutputPatternElement
    (StateMachineEClass, (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (True, False, True, True, False,
    True, True, False)), (String ((Ascii (False, True, False, False, True,
    True, False, False)), EmptyString)))))),
    (Obj.magic (BuildStateMachine ((stateMachine_getName (Obj.magic sm1)),
      (stateMachine_getStateMachineID (Obj.magic sm1))))), (fun sm2 -> Cons
    ((BuildOutputPatternElementReference (StateMachineStatesEReference,
    (match stateMachine_getStates (Obj.magic sm1) m with
     | Some states ->
       (match resolveAll hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii
                (True, False, False, False, False, True, True, False)),
                (String ((Ascii (True, True, False, False, True, True, True,
                False)), (String ((Ascii (False, True, False, False, True,
                True, False, False)), EmptyString)))))) AbstractStateEClass
                (map (fun s -> Cons
                  ((hSMMetamodel_toEObject
                     (hSMMetamodel_toEObjectFromAbstractState s)), Nil))
                  states) with
        | Some new_states ->
          Some
            (Obj.magic (BuildStateMachineStates ((Obj.magic sm2),
              (Obj.magic new_states))))
        | None -> None)
     | None -> None))), Nil)))), Nil)))))))), (Cons ((Pair (EmptyString,
    (BuildSingleElementRule (AbstractStateEClass, (fun rs1 -> Pair
    ((abstractState_instanceOfEClass RegularStateEClass (Obj.magic rs1)),
    (Cons ((BuildOutputPatternElement (AbstractStateEClass, (String ((Ascii
    (True, False, False, False, False, True, True, False)), (String ((Ascii
    (True, True, False, False, True, True, True, False)), (String ((Ascii
    (False, True, False, False, True, True, False, False)),
    EmptyString)))))),
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((abstractState_getName (Obj.magic rs1)),
        (abstractState_getAbstractStateID (Obj.magic rs1)))))))), (fun as2 ->
    Cons ((BuildOutputPatternElementReference
    (AbstractStateStateMachineEReference,
    (match abstractState_getStateMachine (Obj.magic rs1) m with
     | Some hsm_sm ->
       (match resolve hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii
                (True, True, False, False, True, True, True, False)), (String
                ((Ascii (True, False, True, True, False, True, True, False)),
                (String ((Ascii (False, True, False, False, True, True,
                False, False)), EmptyString)))))) StateMachineEClass (Cons
                ((hSMMetamodel_toEObject
                   (hSMMetamodel_toEObjectFromStateMachine hsm_sm)), Nil)) with
        | Some fsm_sm ->
          Some
            (Obj.magic (BuildAbstractStateStateMachine ((Obj.magic as2),
              (Obj.magic fsm_sm))))
        | None -> None)
     | None -> None))), Nil)))), Nil)))))))), (Cons ((Pair (EmptyString,
    (BuildSingleElementRule (AbstractStateEClass, (fun is1 -> Pair
    ((match abstractState_instanceOfEClass InitialStateEClass (Obj.magic is1) with
      | True -> isNone (abstractState_getCompositeState (Obj.magic is1) m)
      | False -> False), (Cons ((BuildOutputPatternElement
    (AbstractStateEClass, (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (False, True, False, False, True,
    True, False, False)), EmptyString)))))),
    (Obj.magic (BuildAbstractState (InitialStateEClass,
      (Obj.magic (BuildInitialState ((abstractState_getName (Obj.magic is1)),
        (abstractState_getAbstractStateID (Obj.magic is1)))))))), (fun as2 ->
    Cons ((BuildOutputPatternElementReference
    (AbstractStateStateMachineEReference,
    (match abstractState_getStateMachine (Obj.magic is1) m with
     | Some hsm_sm ->
       (match resolve hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii
                (True, True, False, False, True, True, True, False)), (String
                ((Ascii (True, False, True, True, False, True, True, False)),
                (String ((Ascii (False, True, False, False, True, True,
                False, False)), EmptyString)))))) StateMachineEClass (Cons
                ((hSMMetamodel_toEObject
                   (hSMMetamodel_toEObjectFromStateMachine hsm_sm)), Nil)) with
        | Some fsm_sm ->
          Some
            (Obj.magic (BuildAbstractStateStateMachine ((Obj.magic as2),
              (Obj.magic fsm_sm))))
        | None -> None)
     | None -> None))), Nil)))), Nil)))))))), (Cons ((Pair (EmptyString,
    (BuildSingleElementRule (AbstractStateEClass, (fun is1 -> Pair
    ((match abstractState_instanceOfEClass InitialStateEClass (Obj.magic is1) with
      | True ->
        negb (isNone (abstractState_getCompositeState (Obj.magic is1) m))
      | False -> False), (Cons ((BuildOutputPatternElement
    (AbstractStateEClass, (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (False, True, False, False, True,
    True, False, False)), EmptyString)))))),
    (Obj.magic (BuildAbstractState (RegularStateEClass,
      (Obj.magic (BuildRegularState ((abstractState_getName (Obj.magic is1)),
        (abstractState_getAbstractStateID (Obj.magic is1)))))))), (fun as2 ->
    Cons ((BuildOutputPatternElementReference
    (AbstractStateStateMachineEReference,
    (match abstractState_getStateMachine (Obj.magic is1) m with
     | Some hsm_sm ->
       (match resolve hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii
                (True, True, False, False, True, True, True, False)), (String
                ((Ascii (True, False, True, True, False, True, True, False)),
                (String ((Ascii (False, True, False, False, True, True,
                False, False)), EmptyString)))))) StateMachineEClass (Cons
                ((hSMMetamodel_toEObject
                   (hSMMetamodel_toEObjectFromStateMachine hsm_sm)), Nil)) with
        | Some fsm_sm ->
          Some
            (Obj.magic (BuildAbstractStateStateMachine ((Obj.magic as2),
              (Obj.magic fsm_sm))))
        | None -> None)
     | None -> None))), Nil)))), Nil)))))))), (Cons ((Pair (EmptyString,
    (BuildSingleElementRule (TransitionEClass, (fun t1 -> Pair
    ((match negb
              (abstractState_instanceOfEClass_optional CompositeStateEClass
                (transition_getSource (Obj.magic t1) m)) with
      | True ->
        negb
          (abstractState_instanceOfEClass_optional CompositeStateEClass
            (transition_getTarget (Obj.magic t1) m))
      | False -> False), (Cons ((BuildOutputPatternElement (TransitionEClass,
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, False, False)),
    EmptyString)))),
    (Obj.magic (BuildTransition ((transition_getLabel (Obj.magic t1)),
      (transition_getTransitionID (Obj.magic t1))))), (fun t2 -> Cons
    ((BuildOutputPatternElementReference (TransitionStateMachineEReference,
    (match transition_getStateMachine (Obj.magic t1) m with
     | Some hsm_sm ->
       (match resolve hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii
                (True, True, False, False, True, True, True, False)), (String
                ((Ascii (True, False, True, True, False, True, True, False)),
                (String ((Ascii (False, True, False, False, True, True,
                False, False)), EmptyString)))))) StateMachineEClass (Cons
                ((hSMMetamodel_toEObject
                   (hSMMetamodel_toEObjectFromStateMachine hsm_sm)), Nil)) with
        | Some fsm_sm ->
          Some
            (Obj.magic (BuildTransitionStateMachine ((Obj.magic t2),
              (Obj.magic fsm_sm))))
        | None -> None)
     | None -> None))), (Cons ((BuildOutputPatternElementReference
    (TransitionSourceEReference,
    (match transition_getSource (Obj.magic t1) m with
     | Some hsm_tr_source ->
       (match resolve hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii
                (True, False, False, False, False, True, True, False)),
                (String ((Ascii (True, True, False, False, True, True, True,
                False)), (String ((Ascii (False, True, False, False, True,
                True, False, False)), EmptyString)))))) AbstractStateEClass
                (Cons
                ((hSMMetamodel_toEObject
                   (hSMMetamodel_toEObjectFromAbstractState hsm_tr_source)),
                Nil)) with
        | Some fsm_tr_source ->
          Some
            (Obj.magic (BuildTransitionSource ((Obj.magic t2),
              (Obj.magic fsm_tr_source))))
        | None -> None)
     | None -> None))), (Cons ((BuildOutputPatternElementReference
    (TransitionTargetEReference,
    (match transition_getTarget (Obj.magic t1) m with
     | Some hsm_tr_target ->
       (match resolve hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii
                (True, False, False, False, False, True, True, False)),
                (String ((Ascii (True, True, False, False, True, True, True,
                False)), (String ((Ascii (False, True, False, False, True,
                True, False, False)), EmptyString)))))) AbstractStateEClass
                (Cons
                ((hSMMetamodel_toEObject
                   (hSMMetamodel_toEObjectFromAbstractState hsm_tr_target)),
                Nil)) with
        | Some fsm_tr_target ->
          Some
            (Obj.magic (BuildTransitionTarget ((Obj.magic t2),
              (Obj.magic fsm_tr_target))))
        | None -> None)
     | None -> None))), Nil)))))))), Nil)))))))), (Cons ((Pair (EmptyString,
    (BuildMultiElementRule (TransitionEClass, (fun t1 ->
    BuildMultiElementRule (AbstractStateEClass, (fun src ->
    BuildMultiElementRule (AbstractStateEClass, (fun trg ->
    BuildSingleElementRule (AbstractStateEClass, (fun c -> Pair
    ((match match match match match abstractState_instanceOfEClass
                                      CompositeStateEClass (Obj.magic src) with
                              | True ->
                                negb
                                  (abstractState_instanceOfEClass
                                    CompositeStateEClass (Obj.magic trg))
                              | False -> False with
                        | True ->
                          negb
                            (beq_AbstractState (Obj.magic c) (Obj.magic src))
                        | False -> False with
                  | True ->
                    beq_AbstractState_option
                      (transition_getSource (Obj.magic t1) m) (Some
                      (Obj.magic src))
                  | False -> False with
            | True ->
              beq_AbstractState_option
                (transition_getTarget (Obj.magic t1) m) (Some (Obj.magic trg))
            | False -> False with
      | True ->
        beq_CompositeState_option
          (abstractState_getCompositeState (Obj.magic c) m)
          (Obj.magic hSMMetamodel_AbstractState_downcast CompositeStateEClass
            src)
      | False -> False), (Cons ((BuildOutputPatternElement (TransitionEClass,
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, False, False)),
    EmptyString)))),
    (Obj.magic (BuildTransition
      ((append (transition_getLabel (Obj.magic t1))
         (append (String ((Ascii (True, True, True, True, True, False, True,
           False)), (String ((Ascii (False, True, True, False, False, True,
           True, False)), (String ((Ascii (False, True, False, False, True,
           True, True, False)), (String ((Ascii (True, True, True, True,
           False, True, True, False)), (String ((Ascii (True, False, True,
           True, False, True, True, False)), (String ((Ascii (True, True,
           True, True, True, False, True, False)), EmptyString))))))))))))
           (append (abstractState_getName (Obj.magic c))
             (append (String ((Ascii (True, True, True, True, True, False,
               True, False)), (String ((Ascii (False, False, True, False,
               True, True, True, False)), (String ((Ascii (True, True, True,
               True, False, True, True, False)), (String ((Ascii (True, True,
               True, True, True, False, True, False)), EmptyString))))))))
               (abstractState_getName (Obj.magic trg)))))),
      (transition_getTransitionID (Obj.magic t1))))), (fun t2 -> Cons
    ((BuildOutputPatternElementReference (TransitionStateMachineEReference,
    (match transition_getStateMachine (Obj.magic t1) m with
     | Some hsm_sm ->
       (match resolve hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii
                (True, True, False, False, True, True, True, False)), (String
                ((Ascii (True, False, True, True, False, True, True, False)),
                (String ((Ascii (False, True, False, False, True, True,
                False, False)), EmptyString)))))) StateMachineEClass (Cons
                ((hSMMetamodel_toEObject
                   (hSMMetamodel_toEObjectFromStateMachine hsm_sm)), Nil)) with
        | Some fsm_sm ->
          Some
            (Obj.magic (BuildTransitionStateMachine ((Obj.magic t2),
              (Obj.magic fsm_sm))))
        | None -> None)
     | None -> None))), (Cons ((BuildOutputPatternElementReference
    (TransitionSourceEReference,
    (match resolve hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii (True,
             False, False, False, False, True, True, False)), (String ((Ascii
             (True, True, False, False, True, True, True, False)), (String
             ((Ascii (False, True, False, False, True, True, False, False)),
             EmptyString)))))) AbstractStateEClass (Cons
             ((hSMMetamodel_toEObject
                (hSMMetamodel_toEObjectFromAbstractState (Obj.magic c))),
             Nil)) with
     | Some fsm_tr_source ->
       Some
         (Obj.magic (BuildTransitionSource ((Obj.magic t2),
           (Obj.magic fsm_tr_source))))
     | None -> None))), (Cons ((BuildOutputPatternElementReference
    (TransitionTargetEReference,
    (match resolve hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii (True,
             False, False, False, False, True, True, False)), (String ((Ascii
             (True, True, False, False, True, True, True, False)), (String
             ((Ascii (False, True, False, False, True, True, False, False)),
             EmptyString)))))) AbstractStateEClass (Cons
             ((hSMMetamodel_toEObject
                (hSMMetamodel_toEObjectFromAbstractState (Obj.magic trg))),
             Nil)) with
     | Some fsm_tr_target ->
       Some
         (Obj.magic (BuildTransitionTarget ((Obj.magic t2),
           (Obj.magic fsm_tr_target))))
     | None -> None))), Nil)))))))), Nil)))))))))))))), (Cons ((Pair
    (EmptyString, (BuildMultiElementRule (TransitionEClass, (fun t1 ->
    BuildMultiElementRule (AbstractStateEClass, (fun src ->
    BuildMultiElementRule (AbstractStateEClass, (fun trg ->
    BuildSingleElementRule (AbstractStateEClass, (fun c -> Pair
    ((match match match match match abstractState_instanceOfEClass
                                      CompositeStateEClass (Obj.magic trg) with
                              | True ->
                                abstractState_instanceOfEClass
                                  InitialStateEClass (Obj.magic c)
                              | False -> False with
                        | True ->
                          negb
                            (abstractState_instanceOfEClass
                              CompositeStateEClass (Obj.magic src))
                        | False -> False with
                  | True ->
                    beq_AbstractState_option
                      (transition_getSource (Obj.magic t1) m) (Some
                      (Obj.magic src))
                  | False -> False with
            | True ->
              beq_AbstractState_option
                (transition_getTarget (Obj.magic t1) m) (Some (Obj.magic trg))
            | False -> False with
      | True ->
        beq_CompositeState_option
          (abstractState_getCompositeState (Obj.magic c) m)
          (Obj.magic hSMMetamodel_AbstractState_downcast CompositeStateEClass
            trg)
      | False -> False), (Cons ((BuildOutputPatternElement (TransitionEClass,
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, False, False)),
    EmptyString)))),
    (Obj.magic (BuildTransition
      ((append (transition_getLabel (Obj.magic t1))
         (append (String ((Ascii (True, True, True, True, True, False, True,
           False)), (String ((Ascii (False, True, True, False, False, True,
           True, False)), (String ((Ascii (False, True, False, False, True,
           True, True, False)), (String ((Ascii (True, True, True, True,
           False, True, True, False)), (String ((Ascii (True, False, True,
           True, False, True, True, False)), (String ((Ascii (True, True,
           True, True, True, False, True, False)), EmptyString))))))))))))
           (append (abstractState_getName (Obj.magic src))
             (append (String ((Ascii (True, True, True, True, True, False,
               True, False)), (String ((Ascii (False, False, True, False,
               True, True, True, False)), (String ((Ascii (True, True, True,
               True, False, True, True, False)), (String ((Ascii (True, True,
               True, True, True, False, True, False)), EmptyString))))))))
               (abstractState_getName (Obj.magic c)))))),
      (transition_getTransitionID (Obj.magic t1))))), (fun t2 -> Cons
    ((BuildOutputPatternElementReference (TransitionStateMachineEReference,
    (match transition_getStateMachine (Obj.magic t1) m with
     | Some hsm_sm ->
       (match resolve hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii
                (True, True, False, False, True, True, True, False)), (String
                ((Ascii (True, False, True, True, False, True, True, False)),
                (String ((Ascii (False, True, False, False, True, True,
                False, False)), EmptyString)))))) StateMachineEClass (Cons
                ((hSMMetamodel_toEObject
                   (hSMMetamodel_toEObjectFromStateMachine hsm_sm)), Nil)) with
        | Some fsm_sm ->
          Some
            (Obj.magic (BuildTransitionStateMachine ((Obj.magic t2),
              (Obj.magic fsm_sm))))
        | None -> None)
     | None -> None))), (Cons ((BuildOutputPatternElementReference
    (TransitionSourceEReference,
    (match resolve hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii (True,
             False, False, False, False, True, True, False)), (String ((Ascii
             (True, True, False, False, True, True, True, False)), (String
             ((Ascii (False, True, False, False, True, True, False, False)),
             EmptyString)))))) AbstractStateEClass (Cons
             ((hSMMetamodel_toEObject
                (hSMMetamodel_toEObjectFromAbstractState (Obj.magic src))),
             Nil)) with
     | Some fsm_tr_source ->
       Some
         (Obj.magic (BuildTransitionSource ((Obj.magic t2),
           (Obj.magic fsm_tr_source))))
     | None -> None))), (Cons ((BuildOutputPatternElementReference
    (TransitionTargetEReference,
    (match resolve hSMMetamodel hSMMetamodel hSM2FSM m (String ((Ascii (True,
             False, False, False, False, True, True, False)), (String ((Ascii
             (True, True, False, False, True, True, True, False)), (String
             ((Ascii (False, True, False, False, True, True, False, False)),
             EmptyString)))))) AbstractStateEClass (Cons
             ((hSMMetamodel_toEObject
                (hSMMetamodel_toEObjectFromAbstractState (Obj.magic c))),
             Nil)) with
     | Some fsm_tr_target ->
       Some
         (Obj.magic (BuildTransitionTarget ((Obj.magic t2),
           (Obj.magic fsm_tr_target))))
     | None -> None))), Nil)))))))), Nil)))))))))))))), Nil)))))))))))))

(** val hSM2FSM1 :
    (hSMMetamodel_EObject, hSMMetamodel_ELink, hSMMetamodel_EClass,
    hSMMetamodel_EReference, hSMMetamodel_EObject, hSMMetamodel_ELink,
    hSMMetamodel_EClass, hSMMetamodel_EReference) transformationA **)

let hSM2FSM1 =
  parseTransformation hSMMetamodel hSMMetamodel hSM2FSMConcrete

