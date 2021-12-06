(**
 CoqTL user theorem: Relational_name_definedness
 Def: if all objects in the source model have name defined,
      then the target objects generated in the target model
      have name defined. 
 **)

Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.

Require Import core.utils.Utils.
Require Import core.SyntaxCertification.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import core.Engine.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

(*Ltac unfoldTransformationIn Tr Ht := 
  unfold Tr in Ht;
  unfold ConcreteSyntax.parse in Ht; 
  unfold ConcreteSyntax.parseRule in Ht;
  unfold ConcreteSyntax.parseOutputPatternElement in Ht;
  unfold ConcreteSyntax.parseOutputPatternLink in Ht;
  unfold Expressions.makeGuard in Ht;
  unfold Expressions.makeElement in Ht;
  unfold Expressions.makeIterator in Ht;
  unfold Expressions.makeLink in Ht;
  repeat (unfold Expressions.wrapOptionElement in Ht);
  repeat (unfold Expressions.wrapOptionLink in Ht);
  repeat (unfold Expressions.wrapOption in Ht);
  simpl in Ht.

Ltac unfoldTransformation Tr := 
  unfold Tr;
  unfold ConcreteSyntax.parse; 
  unfold ConcreteSyntax.parseRule;
  unfold ConcreteSyntax.parseOutputPatternElement;
  unfold ConcreteSyntax.parseOutputPatternLink;
  unfold Expressions.makeGuard;
  unfold Expressions.makeElement;
  unfold Expressions.makeIterator;
  unfold Expressions.makeLink;
  repeat (unfold Expressions.wrapOptionElement);
  repeat (unfold Expressions.wrapOptionLink);
  repeat (unfold Expressions.wrapOption);
  simpl.*)

Theorem Relational_name_definedness:
forall (te: TransformationEngine CoqTLSyntax) (cm : ClassModel) (rm : RelationalModel),
  (* transformation *) rm = @execute _ _ te Class2Relational cm ->
  (* precondition *)   (forall (c1 : ClassMetamodel_Object), In c1 (allModelElements cm) -> (ClassMetamodel_getName c1 <> ""%string)) ->
  (* postcondition *)  (forall (t1 : RelationalMetamodel_Object), In t1 (allModelElements rm) -> (RelationalMetamodel_getName t1 <> ""%string)). 
Proof.
  intros.
  rewrite H in H1.
  rewrite (@tr_execute_in_elements _ _ te Class2Relational) in H1.
  do 2 destruct H1.
  destruct x as [| c]. (* Case analysis on source pattern *)
  - rewrite (@tr_instantiatePattern_in _ _ te Class2Relational) in H2.
    do 2 destruct H2.
    rewrite (@tr_matchPattern_in _ _ te Class2Relational) in H2.
    destruct H2.
    rewrite (@tr_matchRuleOnPattern_leaf _ _ te Class2Relational) in H4.
    simpl in H2.
    destruct H2.
    + rewrite <- H2 in H4.
      simpl in H4.
      inversion H4.
    + destruct H2.
      rewrite <- H2 in H4.
      simpl in H4.
      inversion H4.
      contradiction H2.
  - destruct x as [| c0].
    + (* Singleton *) specialize (H0 c). 
      apply allTuples_incl in H1.
      unfold incl in H1.
      specialize (H1 c).
      assert (In c [c]). { left. reflexivity. }
      specialize (H0 (H1 H3)).
      do 2 destruct c. (* Case analysis on source element type *)
      * (* [Class] *) 
        rewrite (@tr_instantiatePattern_in _ _ te Class2Relational) in H2.
        do 2 destruct H2.
        rewrite (@tr_matchPattern_in _ _ te Class2Relational) in H2.
        destruct H2.
        rewrite (@tr_matchRuleOnPattern_leaf _ _ te Class2Relational) in H5.
        simpl in H2.
        rewrite (@tr_instantiateRuleOnPattern_in _ _ te Class2Relational) in H4.
        do 2 destruct H4.
        apply tr_instantiateIterationOnPattern_in in H6.
        do 2 destruct H6.
        rewrite tr_instantiateElementOnPattern_leaf in H7.
        destruct H2.
        ** (* Class2Table *) 
           rewrite <- H2 in H6.
           simpl in H6.
           destruct H6.
           *** rewrite <- H6 in H7.
               simpl in H7.
               inversion H7.
               simpl. 
               apply H0.
           *** contradiction H6.
        ** destruct H2.
           ***  (* Attribute2Column contradict *)
                rewrite <- H2 in H6.
                simpl in H6.
                destruct H6.
                **** rewrite <- H6 in H7. simpl in H7. 
                     inversion H7.
                **** contradiction H6.
           *** contradiction H2.
      * (* [Attribute] *) destruct c0.
        destruct b.
        -- (* derived *) 
           rewrite (@tr_instantiatePattern_in _ _ te Class2Relational) in H2.
           do 2 destruct H2.
           rewrite (@tr_matchPattern_in _ _ te Class2Relational) in H2.
           destruct H2.
           rewrite (@tr_matchRuleOnPattern_leaf _ _ te Class2Relational) in H5.
           simpl in H2. 
           destruct H2.
           ** rewrite <- H2 in H5.
              simpl in H5.
              inversion H5.
           ** destruct H2.
              *** rewrite <- H2 in H5.
                  simpl in H5.
                  inversion H5.
              *** contradiction H2.
        -- (* not derived *) 
            rewrite (@tr_instantiatePattern_in _ _ te Class2Relational) in H2.
            do 2 destruct H2.
            rewrite (@tr_matchPattern_in _ _ te Class2Relational) in H2.
            destruct H2.
            rewrite (@tr_matchRuleOnPattern_leaf _ _ te Class2Relational) in H5.
            simpl in H2.
            rewrite (@tr_instantiateRuleOnPattern_in _ _ te Class2Relational) in H4.
            do 2 destruct H4.
            apply tr_instantiateIterationOnPattern_in in H6.
            do 2 destruct H6.
            rewrite tr_instantiateElementOnPattern_leaf in H7.
            destruct H2.
            **  (* Class2Table contradict *)
                 rewrite <- H2 in H6.
                 simpl in H6.
                 destruct H6.
                 *** rewrite <- H6 in H7. simpl in H7. 
                      inversion H7.
                 *** contradiction H6.
            ** (* Attribute2Column *) 
               destruct H2.
               *** rewrite <- H2 in H6.
                   simpl in H6.
                   destruct H6.
                   **** rewrite <- H6 in H7.
                        simpl in H7.
                        inversion H7.
                        simpl. 
                        apply H0.
                   **** contradiction H6.
               *** contradiction H2.
    + (* Other patterns *) do 2 destruct c.
      * destruct c0. 
        rewrite (@tr_instantiatePattern_in _ _ te Class2Relational) in H2.
        do 2 destruct H2.
        rewrite (@tr_matchPattern_in _ _ te Class2Relational) in H2.
        destruct H2.
        rewrite (@tr_matchRuleOnPattern_leaf _ _ te Class2Relational) in H4.
        simpl in H2.
        destruct H2.
        ** rewrite <- H2 in H4.
          simpl in H4.
          inversion H4.
        ** destruct H2.
          rewrite <- H2 in H4.
          simpl in H4.
          inversion H4.
          contradiction H2.
      * destruct c0. 
        rewrite (@tr_instantiatePattern_in _ _ te Class2Relational) in H2.
        do 2 destruct H2.
        rewrite (@tr_matchPattern_in _ _ te Class2Relational) in H2.
        destruct H2.
        rewrite (@tr_matchRuleOnPattern_leaf _ _ te Class2Relational) in H4.
        simpl in H2.
        destruct H2.
        ** rewrite <- H2 in H4.
          simpl in H4.
          inversion H4.
        ** destruct H2.
          rewrite <- H2 in H4.
          simpl in H4.
          inversion H4.
          contradiction H2.
Qed.

(* Alternative for (* [Attribute] *):
      unfold instantiatePattern in H2. 
      unfold matchPattern in H2.
      unfold matchRuleOnPattern in H2. simpl in H2.
      destruct (negb (getAttributeDerived c0)). 
      -- simpl in H2. destruct H2. 
        ++ rewrite <- H2. simpl. simpl in H0. assumption.
        ++ contradiction H2. 
      --  contradiction H2.*)

(* Alternative for (* Other patterns *): 
      apply maxArity_length with (sp:=c::c0::x) (tr:=Class2Relational) (sm:=cm).
      * unfold maxArity. simpl. omega.
      * assumption. *)

(*Ltac destructPattern sp tr sm h := 
  destruct sp;
  [> contradiction | 
     repeat
      destruct sp;
       [> 
          | exfalso;
            apply maxArity_length with (sp:=c::c0::x) (tr:=tr) (sm:=sm);
            [> 
              parseTransformationInGoal tr; unfold maxArity; simpl; omega |
              assumption 
            ]
            +
            destruct sp;
       ]  
  ].*)
  

Ltac destruct_execute Hexecute sp Hin Hinstantiate :=
  apply tr_execute_in_elements in Hexecute;
  destruct Hexecute as [sp [Hin Hinstantiate]].

Ltac destruct_instantiatePattern Hinstantiate rule Hrule HinstRule :=
  apply tr_instantiatePattern_in in Hinstantiate;
  destruct Hinstantiate as [rule [Hrule HinstRule]].

Ltac destruct_matchPattern Hrule Hr Hmatch :=
  apply tr_matchPattern_in in Hrule;
  destruct Hrule as [Hr Hmatch].

Ltac destruct_rule Hrule :=
  repeat (destruct Hrule as [Hrule | Hrule]; try contradiction Hrule); destruct Hrule.

Ltac destruct_pattern Hinst sp :=
  repeat (let se := fresh "se" in
          destruct sp as [ | se sp ];
          [ | destruct se as [[] ?] eqn:?];
          try contradiction Hinst);
  destruct Hinst as [Hinst | []]; simpl in Hinst.

(* 

Theorem Relational_name_definedness':
forall (cm : ClassModel) (rm : RelationalModel),
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)   (forall (c1 : ClassMetamodel_Object), In c1 (allModelElements cm) -> (ClassMetamodel_getName c1 <> ""%string)) ->
  (* postcondition *)  (forall (t1 : RelationalMetamodel_Object), In t1 (allModelElements rm) -> (RelationalMetamodel_getName t1 <> ""%string)).
Proof.
  intros. subst rm.
  destruct_execute H1 sp Hin Hinst. (* t1 comes from a pattern sp *)
  apply allTuples_incl in Hin. (* sp is made of source model elements *)
  destruct_instantiatePattern Hinst r Hr Hinst. (* sp matches a rule r *)
  destruct_matchPattern Hr Hr Hmatch. (* r comes from the transformation *)
  clear Hmatch. (* Hmatch is not used for this proof *)
  destruct_rule Hr; (* case analysis on rules *)
    destruct_pattern Hinst sp. (* retrieve the source pattern for each rule *)
  - (* Class2Table *) specialize (H0 se). crush.
  - (* Attribute2Column *) specialize (H0 se). crush.
Qed.

*)