Require Import Omega.
Require Import List.      (* sequence *)
Require Import String.
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Coq.Bool.Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Eqdep_dec Arith.

(* Add subtype support *)

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


Class Transformation  S T `{Eq S} `{Eq T} : Type   :=
{
  (* a list of rules R *)
  R : list (list S->list T);


  (* surj between target pattern and source pattern over a rule function *)
  tr_surj : forall (t: T),  exists (sp: list S) (r: list S->list T), In r R /\ In t (r sp);


  (* inj between target element and target pattern *)
  tr_inj: (forall (t: T) (sp1 sp2: list S) (r: list S->list T), 
                In r R -> (In t (r sp1) /\ In t (r sp2)) -> eqb sp1 sp2);
}.


Inductive A: Set :=
| mkA: nat -> A.

Instance eqA : Eq (A) := {
 eqb a1 a2 := match a1,a2 with
  | mkA n1, mkA n2 => beq_nat n1 n2
 end
}.

Definition getNat_A (a: A) :=
  match a with
   | mkA n => n
  end.

Inductive B: Set := 
| mkB: nat -> B.

Instance eqB : Eq (B) := {
 eqb b1 b2 := match b1,b2 with
  | mkB n1, mkB n2 => beq_nat n1 n2
 end
}.

Definition getNat_B (b: B) :=
  match b with
   | mkB n => n
  end.

Inductive SrcModel : Set :=
| fromA : A -> SrcModel
| fromB : B -> SrcModel.

Instance eqSrcModel : Eq (SrcModel) := {
 eqb s1 s2 := match s1,s2 with
  | fromA a1, fromA a2 => eqb a1 a2
  | fromB b1, fromB b2 => eqb b1 b2
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

Definition Instantiated_X (x : X) : bool :=
  match x with
  | r1 a => (getNat_A a) > 10
  end.
  
Definition iX : Set := {x:X | (Instantiated_X x)}.

Instance eqX `{Eq A} : Eq (X) := {
 eqb x1 x2 := match x1,x2 with
  | r1 a1, r1 a2 => eqb a1 a2
 end
}.

Inductive Y : Set :=
| r2 : B -> Y.

Definition Instantiated_Y (y : Y) : bool :=
  match y with
  | r2 b => (getNat_B b) > 5
  end.
  
Definition iY : Set := {y:Y | (Instantiated_Y y)}.

Instance eqY `{Eq B} : Eq (Y) := {
 eqb y1 y2 := match y1,y2 with
  | r2 b1, r2 b2 => eqb b1 b2
 end
}.


Inductive TrgModel: Set :=
| fromX: iX -> TrgModel
| fromY: iY -> TrgModel.

(*TODO  is it ok here to not check the proof of subtypes? *)
Instance eqTrgModel : Eq (TrgModel) := {
 eqb s1 s2 := match s1,s2 with
  | fromX x1, fromX x2 => eqb (sval x1) (sval x2)
  | fromY y1, fromY y2 => eqb (sval y1) (sval y2)
  | _,_ => false
 end
}.



Definition downX (tm: TrgModel) : option iX :=
match tm with
| fromX x => Some x
| _ => None
end.

Definition downY (tm: TrgModel) : option iY :=
match tm with
| fromY y => Some y
| _ => None
end.

Instance castX : cast iX TrgModel :={
 upcast := fromX;
 downcast := downX
}.

Instance castY : cast iY TrgModel :={
 upcast := fromY;
 downcast := downY
}.


Definition r1_rewrite a : option iX := insub (r1 a).

Definition r2_rewrite b : option iY := insub (r2 b).

Definition toRuleArityOne''' {A B : Type} `{cast A SrcModel} `{cast B TrgModel} (f: A -> option B): list SrcModel -> list TrgModel :=
fun l: list SrcModel => 
 match l with
  | e :: nil => match downcast e with
    | Some a => match (f a) with
      | Some b => upcast b :: nil
      | None => nil
      end
    | None => nil
    end
  | _ => nil
 end.
 
Definition Src2TrgRules := (toRuleArityOne''' r1_rewrite  :: toRuleArityOne''' r2_rewrite :: nil).





Instance Src2Trg : Transformation SrcModel TrgModel := {}.
Proof.
(* Tr witness *)
- exact Src2TrgRules.

(* tr_surj *)
- intros.
  destruct t eqn: caseTrg.
  (* t = fromX i *)
  - destruct i eqn: caseiX.
    destruct x eqn: caseX.
    exists (fromA a::nil).
    exists (toRuleArityOne''' r1_rewrite).
    split.
    - simpl.
      left.
      done.
    - rewrite <- caseiX.
      simpl.
      rewrite /r1_rewrite insubT.
      simpl.
      left.
      rewrite caseiX.
      done.
   (* t = fromY i *)
  - destruct i eqn: caseiY.
    destruct x eqn: caseY.
    exists (fromB b::nil).
    exists (toRuleArityOne''' r2_rewrite).
    split.
    - simpl.
      right.
      left.
      done.
    - rewrite <- caseiY.
      simpl.
      rewrite /r2_rewrite insubT.
      simpl.
      left.
      rewrite caseiY.
      done. 
(* tr_inj *)
- intros.
  destruct H0.
  destruct H.
  (* r = r1 *)
  - destruct sp1 eqn:sp1_cases; destruct sp2 eqn:sp2_cases.
      (* sp1 = nil, sp2 = nil *)
    - rewrite <- H in H0.
      simpl in H0.
      done.
      (* sp1 = nil, sp2 = s:l *)
    - rewrite <- H in H0.
      simpl in H0.
      done.
      (* sp1 = s:l, sp2 = nil *)
    - rewrite <- H in H1.
      simpl in H0.
      done.
      (* sp1 = s:l, sp2 = s:l *)
    - rewrite <- H in H0; simpl in H0.
      rewrite <- H in H1; simpl in H1.
    
      try destruct l; destruct l0; 
          destruct (downA s) eqn: down_case_s; destruct (downA s0) eqn: down_case_s0; 
          auto.
      try destruct (r1_rewrite a) eqn: rewrite_a;
      destruct (r1_rewrite a0) eqn: rewrite_a0;
      auto.
      destruct i eqn:caseiX.
      destruct x eqn: caseX.
      destruct i0 eqn:caseiX0.
      destruct x0 eqn:caseX0.
      simpl in H0.
      simpl in H1.
      try destruct H0;
          destruct H1;
          auto.
      rewrite <- H0 in H1.
      inversion H1.
      
      destruct (Instantiated_X (r1 a)) eqn: guardA; destruct (Instantiated_X (r1 a0)) eqn: guardA0.
      - rewrite /r1_rewrite insubT in rewrite_a. 
        rewrite /r1_rewrite insubT in rewrite_a0.   
        simpl in rewrite_a.
        simpl in rewrite_a0.
        inversion rewrite_a.
        inversion rewrite_a0.
        inversion H1.
        rewrite H6 in H5.
        rewrite <- H4 in H5.
        rewrite H5 in down_case_s0.
        rewrite <- down_case_s in down_case_s0.
        assert (s0 = s).
        {
          destruct s;
          destruct s0.
          - inversion down_case_s.
            inversion down_case_s0.
            rewrite H7.
            done.
          - done.
          - done.
          - done.
        }
        - rewrite H2.
          simpl.
          destruct s.
          destruct a3.
          rewrite <- beq_nat_refl.
          done.
        - done.
      - rewrite /r1_rewrite insubT in rewrite_a. 
        rewrite /r1_rewrite insubF in rewrite_a0.
        done.
        done.
      - rewrite /r1_rewrite insubF in rewrite_a. 
        rewrite /r1_rewrite insubT in rewrite_a0.
        done.
        done.
      - rewrite /r1_rewrite insubF in rewrite_a. 
        rewrite /r1_rewrite insubF in rewrite_a0.
        done.
        done.
        done. 
  (* r = r2 *)
  simpl in H.
  destruct H. 
  - destruct sp1 eqn:sp1_cases; destruct sp2 eqn:sp2_cases.
      (* sp1 = nil, sp2 = nil *)
    - done.
      (* sp1 = nil, sp2 = s:l *)
    - rewrite <- H in H0.
      simpl in H0.
      done.
      (* sp1 = s:l, sp2 = nil *)
    - rewrite <- H in H1.
      simpl in H0.
      done.
      (* sp1 = s:l, sp2 = s:l *)
    - rewrite <- H in H0; simpl in H0.
      rewrite <- H in H1; simpl in H1.
    
      try destruct l; destruct l0; 
          destruct (downB s) eqn: down_case_s; destruct (downB s0) eqn: down_case_s0; 
          auto.
      try destruct (r2_rewrite b) eqn: rewrite_b;
      destruct (r2_rewrite b0) eqn: rewrite_b0;
      auto.
      destruct i eqn:caseiY.
      destruct x eqn: caseY.
      destruct i0 eqn:caseiY0.
      destruct x0 eqn:caseY0.
      simpl in H0.
      simpl in H1.
      try destruct H0;
          destruct H1;
          auto.
      rewrite <- H0 in H1.
      inversion H1.
      
      destruct (Instantiated_Y (r2 b)) eqn: guardB; destruct (Instantiated_Y (r2 b0)) eqn: guardB0.
      - rewrite /r2_rewrite insubT in rewrite_b. 
        rewrite /r2_rewrite insubT in rewrite_b0.   
        simpl in rewrite_b.
        simpl in rewrite_b0.
        inversion rewrite_b.
        inversion rewrite_b0.
        inversion H1.
        rewrite H6 in H5.
        rewrite <- H4 in H5.
        rewrite H5 in down_case_s0.
        rewrite <- down_case_s in down_case_s0.
        assert (s0 = s).
        {
          destruct s;
          destruct s0.
          - done.
          - done.
          - done.
          - inversion down_case_s.
            inversion down_case_s0.
            rewrite H7.
            done.
        }
        - rewrite H2.
          simpl.
          destruct s.
          destruct a.
          rewrite <- beq_nat_refl.
          done.
        - destruct b3.
          rewrite <- beq_nat_refl.
          done.
      - rewrite /r2_rewrite insubT in rewrite_b. 
        rewrite /r2_rewrite insubF in rewrite_b0.
        done.
        done.
      - rewrite /r2_rewrite insubF in rewrite_b. 
        rewrite /r2_rewrite insubT in rewrite_b0.
        done.
        done.
      - rewrite /r2_rewrite insubF in rewrite_b. 
        rewrite /r2_rewrite insubF in rewrite_b0.
        done.
        done.
        done. 
  - done. 
Defined.






Class Resource S : Type := 
{
  edges : S -> list (S -> S);
  nodes : S -> list S;
}.




(* 
Test

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









