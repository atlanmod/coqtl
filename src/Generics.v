Require Import Omega.
Require Import List.      (* sequence *)
Require Import String.
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Coq.Bool.Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(* to have more generic theorems about MT, we define these type classes, 
   so that type inference works when apply the theorem on specific instance 
   of these type class *)
   
(* A transformation type class gives :
  - a generic interface that allows different encoding to be compared.
  - a two way bridge, that stuck on one end, we can try the other end. 
 *)
    
(* TODO
  - r1;r2 <=> r2;r1
  - allinstance
  - rule guards
  - EMF terminology conformance
 *)
 
 

  

(* general *)   
Class Enum (A:Type) := 
{
  enum : list A
}.


Class Eq A := 
{
  eqb: A -> A -> bool;
}.

Arguments enum A [Enum]. 

Class cast A B : Type := 
{
  upcast : A -> B;
  downcast : B -> option A
}.


Instance eqBool : Eq bool :=
  {
    eqb := fun (b c : bool) => 
       match b, c with
         | true, true => true
         | true, false => false
         | false, true => false
         | false, false => true
       end
  }.

Instance eqNat : Eq nat :=
  {
    eqb := beq_nat
  }.





Fixpoint eqListAux {A : Type} (f : A->A-> bool) (l1 l2 : list A) : bool :=
  match l1,l2 with
        | nil,nil => true
        | cons h1 nil, cons h2 nil => f h1 h2
        | cons h1 t1, cons h2 t2 => andb (f h1 h2) (eqListAux f t1 t2)
        | _, _ => false
  end.
  
Instance eqList {A : Type} `{Eq A} : Eq (list A) :=
  {
    eqb l1 l2 := eqListAux eqb l1 l2 
  }.

(* Removed Properties:

  (* rules are partial functional *)
  tr_fun: forall `{Eq (list S)} `{Eq (list T)} 
                     (sp: list S) (r: list S->list T),
                     In r R -> eqb sp1 sp2 -> eqb (r sp1) (r sp2); 
                      
  (* Tr is a partial function *)                   
  tr_free_conflict: forall `{Eq (list S->list T)} 
                           (sp: list S) (r1 r2: list S->list T),
                           r1 sp <> nil /\ r2 sp <> nil -> eqb r1 r2;
                           
  (* inj between target element and target pattern *)
  tr_inj3: forall `{Eq (list S)} `{Eq (list T)}
                  (t: T) (sp1 sp2: list S) (r1 r2: list S->list T), 
                  In r1 R /\ In r2 R -> (In t (r1 sp1) /\ In t (r2 sp2)) -> (eqb sp1 sp2 /\ eqb r1 r2);
                  
    
  
 *)
Class Transformation  S T `{Eq S} `{Eq T} : Type   :=
{
  (* a list of rules R *)
  R : list (list S->list T);


  (* surj between target pattern and source pattern over a rule function *)
  tr_surj : forall (t: T),  exists (sp: list S) (r: list S->list T), In r R /\ In t (r sp);


  (* rules are injective *)
  (* two things about backtick notation:
     - first, it is essentially just another argument
     - second, the backtick notation ask the coq system to do implicit generalization,
   *)
  tr_inj: (forall (sp1 sp2: list S) (r: list S->list T),
                In r R -> (r sp1) <> nil -> (r sp2) <> nil -> 
                  eqb (r sp1) (r sp2) -> eqb sp1 sp2);

  (* inj between target element and target pattern *)
  tr_inj2: (forall (t: T) (sp1 sp2: list S) (r: list S->list T), 
                In r R -> (In t (r sp1) /\ In t (r sp2)) -> eqb (r sp1) (r sp2));

  
  (* inj between target element and target pattern *)
  tr_inj3: (forall (t: T) (sp1 sp2: list S) (r: list S->list T), 
                In r R -> (In t (r sp1) /\ In t (r sp2)) -> eqb (sp1) (sp2));

}.


Inductive A: Set :=
| mkA.

Instance eqA : Eq (A) := {
 eqb a1 a2 := match a1,a2 with
  | mkA, mkA => true
 end
}.

Inductive B: Set := 
| mkB.

Instance eqB : Eq (B) := {
 eqb b1 b2 := match b1,b2 with
  | mkB, mkB => true
 end
}.

Inductive SrcModel : Set :=
| fromA : A -> SrcModel
| fromB : B -> SrcModel.

Instance eqSrcModel : Eq (SrcModel) := {
 eqb s1 s2 := match s1,s2 with
  | fromA a1, fromA a2 => true
  | fromB b1, fromB b2 => true
  | _,_ => false
 end
}.


Definition downA (sm: SrcModel) : option A :=
match sm with
| fromA a => Some a
| _ => None
end.

Definition downB (sm: SrcModel) : option B :=
match sm with
| fromB b => Some b
| _ => None
end.


Instance castA : cast A SrcModel :={
 upcast := fromA;
 downcast := downA
}.

Instance castB : cast B SrcModel :={
 upcast := fromB;
 downcast := downB
}.

Inductive X: Set :=
| r1 : A -> X.

Instance eqX `{Eq A} : Eq (X) := {
 eqb x1 x2 := match x1,x2 with
  | r1 a1, r1 a2 => eqb a1 a2
 end
}.



Inductive Y : Set :=
| r2 : B -> Y.

Instance eqY `{Eq B} : Eq (Y) := {
 eqb y1 y2 := match y1,y2 with
  | r2 b1, r2 b2 => eqb b1 b2
 end
}.

Inductive TrgModel: Set :=
| fromX: X -> TrgModel
| fromY: Y -> TrgModel.

Instance eqTrgModel : Eq (TrgModel) := {
 eqb s1 s2 := match s1,s2 with
  | fromX x1, fromX x2 => eqb x1 x2
  | fromY y1, fromY y2 => eqb y1 y2
  | _,_ => false
 end
}.

Definition downX (tm: TrgModel) : option X :=
match tm with
| fromX x => Some x
| _ => None
end.

Definition downY (tm: TrgModel) : option Y :=
match tm with
| fromY y => Some y
| _ => None
end.

Instance castX : cast X TrgModel :={
 upcast := fromX;
 downcast := downX
}.

Instance castY : cast Y TrgModel :={
 upcast := fromY;
 downcast := downY
}.


Definition toRuleArityOne''' {A B : Type} `{cast A SrcModel} `{cast B TrgModel} (f: A->B) : list SrcModel -> list TrgModel :=
fun l: list SrcModel => 
 match l with
  | e :: nil => match downcast e with
    | Some a => upcast (f a) :: nil
    | None => nil
    end
  | _ => nil
 end.
 
Definition Src2TrgRules := (toRuleArityOne''' r1::(toRuleArityOne''' r2::nil)).


Example ex_inj: 
exists `{Eq X}, 
 forall (sp1 sp2 : A),
 eqb (r1 sp1) (r1 sp2) -> eqb sp1 sp2.
Proof.
  intros.
  exists eqX.
  intros.
  unfold eqb in H.
  unfold eqX in H.
  auto.
Qed.



Instance Src2Trg : Transformation SrcModel TrgModel := {}.
Proof.
(* Tr witness *)
- exact Src2TrgRules.

(* tr_surj *)
- intros.
  destruct t eqn: caseTrg.
  destruct x eqn: caseX.
  exists (fromA a::nil).
(*   exists (fun a: list SrcModel => t::nil). this does not hold anymore since it is not belongs Src2TrgRules*)
  exists (toRuleArityOne''' r1). 
  simpl.
  auto.
  destruct y eqn: caseY.
  exists (fromB b::nil).
  exists (toRuleArityOne''' r2).
  simpl.
  auto.
(* tr_inj *)
- intros.
  destruct H.
  (* r = r1 *)
  - destruct sp1 eqn:sp1_cases; destruct sp2 eqn:sp2_cases.
      (* sp1 = nil, sp2 = nil *)
    - rewrite <- H in H0.
      unfold toRuleArityOne''' in H0.
      done.
      (* sp1 = nil, sp2 = s:l *)
    - rewrite <- H in H0.
      unfold toRuleArityOne''' in H0.
      simpl in H0.
      done.
      (* sp1 = s:l, sp2 = nil *)
    - rewrite <- H in H1.
      unfold toRuleArityOne''' in H1.
      simpl in H0.
      done.
      (* sp1 = s:l, sp2 = s:l *)
    - rewrite <- H in H2.
      destruct l; destruct l0.
      - simpl in H2.
        simpl.
        try  destruct s; destruct s0; done.
      - rewrite <- H in H1.
        simpl in H1.
        done.
      - rewrite <- H in H0.
        simpl in H1.
        done.
      - rewrite <- H in H0.
        simpl in H0.
        done.
    (* r = r2 *)
    destruct H.
  - destruct sp1 eqn:sp1_cases; destruct sp2 eqn:sp2_cases.
      (* sp1 = nil, sp2 = nil *)
    - rewrite <- H in H0.
      unfold toRuleArityOne''' in H0.
      done.
      (* sp1 = nil, sp2 = s:l *)
    - rewrite <- H in H0.
      unfold toRuleArityOne''' in H0.
      simpl in H0.
      done.
      (* sp1 = s:l, sp2 = nil *)
    - rewrite <- H in H1.
      unfold toRuleArityOne''' in H1.
      simpl in H0.
      done.
      (* sp1 = s:l, sp2 = s:l *)
    - rewrite <- H in H2.
      destruct l; destruct l0.
      - simpl in H2.
        simpl.
        try  destruct s; destruct s0; done.
      - rewrite <- H in H1.
        simpl in H1.
        done.
      - rewrite <- H in H0.
        simpl in H1.
        done.
      - rewrite <- H in H0.
        simpl in H0.
        done.
  - done.  
(* tr_inj2 *)
- intros.
  destruct H.      
    (* r = r1 *)
  - destruct sp1 eqn:sp1_cases; destruct sp2 eqn:sp2_cases.
      (* sp1 = nil, sp2 = nil *)
    - rewrite <- H in H0.
      simpl in H0.
      destruct H0.
      done.
      (* sp1 = nil, sp2 = s:l *)
    - rewrite <- H in H0.
      simpl in H0.
      destruct H0.
      done.
      (* sp1 = s:l, sp2 = nil *)
    - rewrite <- H in H0.
      simpl in H0.
      destruct H0.
      done.
      (* sp1 = s:l, sp2 = s:l *)
    - rewrite <- H in H0.
      rewrite <- H.
      simpl.
      destruct H0.
      simpl in H0.
      simpl in H1.
      try destruct l; destruct l0; simpl;
          destruct (downA s) eqn: down_case_s; destruct (downA s0) eqn: down_case_s0; 
          simpl; auto.
      try destruct H0; simpl in H0; 
          destruct H1; simpl in H1;
          auto.
      rewrite <- H0 in H1.
      inversion H1.
      destruct a.
      auto.
    (* r = r2 *)
    destruct H.
  - destruct sp1 eqn:sp1_cases; destruct sp2 eqn:sp2_cases.
      (* sp1 = nil, sp2 = nil *)
    - rewrite <- H in H0.
      simpl in H0.
      destruct H0.
      done.
      (* sp1 = nil, sp2 = s:l *)
    - rewrite <- H in H0.
      simpl in H0.
      destruct H0.
      done.
      (* sp1 = s:l, sp2 = nil *)
    - rewrite <- H in H0.
      simpl in H0.
      destruct H0.
      done.
      (* sp1 = s:l, sp2 = s:l *)
    - rewrite <- H in H0.
      rewrite <- H.
      simpl.
      destruct H0.
      simpl in H0.
      simpl in H1.
      try destruct l; destruct l0; simpl;
          destruct (downB s) eqn: down_case_s; destruct (downB s0) eqn: down_case_s0; 
          simpl; auto.
      try destruct H0; simpl in H0; 
          destruct H1; simpl in H1;
          auto.
      rewrite <- H0 in H1.
      inversion H1.
      destruct b.
      auto.
  - done.
Defined.






Class Resource S : Type := 
{
  edges : S -> list (S -> S);
  nodes : S -> list S;
}.




(* 
Definition toRuleArityOne (A B :Type) (f: A->B) : list A -> list B :=
fun l: list A => 
 match l with
  | nil => nil
  | a :: l'=> f a :: nil
 end. 

Definition toRuleArityTwo (A B :Type) (f: A->A->B) : list A -> list B :=
fun l: list A => 
 match l with
  | a :: b :: l'=> f a b :: nil
  | _ => nil
 end. 

Definition toRuleArityThree (A B :Type) (f: A->A->A->B) : list A -> list B :=
fun l: list A => 
 match l with
  | a :: b :: c :: l'=> f a b c :: nil
  | _ => nil
 end. 
 
 
Definition toRuleArityOne' (f: A->X) : list SrcModel -> list TrgModel :=
fun l: list SrcModel => 
 match l with
  | nil => nil
  | e :: l'=> match e with
    | fromA a => fromX (f a) :: nil
    | fromB b => nil
    end
 end. 
 
Definition toRuleArityOne'' (f: B->Y) : list SrcModel -> list TrgModel :=
fun l: list SrcModel => 
 match l with
  | nil => nil
  | e :: l'=> match e with
    | fromA a => nil
    | fromB b => fromY (f b) :: nil
    end
 end.       

 *)









