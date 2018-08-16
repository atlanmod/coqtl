
(* Functionalized BackReferences *)
Fixpoint EntitySchema (e : Entity) (schemas: list ERSchema) : option ERSchema :=
  (find 
		(fun s => existsb 
			(fun e2 => 
				beq_nat 
					(EntityOid e2) 
					(EntityOid e))
			(ERSchemaEntities s))
		schemas).

Fixpoint RelshipSchema (r : Relship) (schemas: list ERSchema) : option ERSchema :=
  (find 
		(fun s => existsb 
			(fun r2 => 
				beq_nat 
					(RelshipOid r2) 
					(RelshipOid r))
			(ERSchemaRelships s))
		schemas).

Fixpoint AttributeEntity (a : Attribute) (entities: list Entity) : option Entity :=
  (find 
		(fun e => existsb 
			(fun a2 => 
				beq_nat 
					(AttributeOid a2) 
					(AttributeOid a))
			(EntityAttrs e))
		entities).

Fixpoint AttributeRelship (a : Attribute) (relships: list Relship) : option Relship :=
  (find 
		(fun r => existsb 
			(fun a2 => 
				beq_nat 
					(AttributeOid a2) 
					(AttributeOid a))
			(RelshipAttrs r))
		relships).

Fixpoint RelshipEndEntity (ed : RelshipEnd) (entities: list Entity) : option Entity :=
  (find 
		(fun e => existsb 
			(fun ed2 => 
				beq_nat 
					(RelshipEndOid ed2) 
					(RelshipEndOid ed))
			(EntityEnds e))
		entities).

Fixpoint RelshipEndRelship (ed : RelshipEnd) (relships: list Relship) : option Relship :=
  (find 
		(fun r => existsb 
			(fun ed2 => 
				beq_nat 
					(RelshipEndOid ed2) 
					(RelshipEndOid ed))
			(RelshipEnds r))
		relships).
		
(* Axiomatized BackReferences *)
Axiom EntitySchema : Entity -> ERSchema.

Axiom Containment_EntitySchema : 
 forall e: Entity, 
  In e (ERSchemaEntities (EntitySchema e)). 


Axiom Functional_EntitySchema :
 forall (e : Entity) (s1 s2: ERSchema),
   EntitySchema e = s1 /\ EntitySchema e = s2 -> s1 = s2.


Axiom RelshipSchema : Relship -> ERSchema.

Axiom Containment_RelshipSchema : 
 forall r: Relship, 
  In r (ERSchemaRelships (RelshipSchema r)). 

Axiom Functional_RelshipSchema :
 forall (r: Relship) (s1 s2: ERSchema),
   RelshipSchema r = s1 /\ RelshipSchema r = s2 -> s1 = s2.

Axiom AttributeEntity : Attribute -> Entity.

Axiom Containment_AttributeEntity : 
 forall a: Attribute, 
  In a (EntityAttrs (AttributeEntity a)).

Axiom AttributeRelship : Attribute -> Relship.

Axiom Containment_AttributeRelship : 
 forall a: Attribute, 
  In a (RelshipAttrs (AttributeRelship a)).

Axiom RelshipEndEntity : RelshipEnd -> Entity.

Axiom Containment_RelshipEndEntity : 
 forall re: RelshipEnd, 
  In re (EntityEnds (RelshipEndEntity re)).


Axiom RelshipEndRelship : RelshipEnd -> Relship.

Axiom Containment_RelshipEndRelship : 
 forall re: RelshipEnd, 
  In re (RelshipEnds (RelshipEndRelship re)).