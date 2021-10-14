
/**
 * Removed

		Definition «mm»_getEAttributeTypesByEClass («mm_eclass_qarg» : «ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEClass») : Set :=
		  match «mm_eclass_qarg» with
		    «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
		    | «eClass.name»«Keywords.PostfixEClass» => 
		    «IF eClass.ESuperTypes.size > 0 »
		    	«IF eClass.EAttributes.size > 0»
		    	(«eClass.ESuperTypes.get(0).name» * «FOR eAttributeCtr : eClass.EAttributes SEPARATOR " * "»«AttributeType2Coq(eAttributeCtr)»«ENDFOR»)
		    	«ELSE»
		    	(«eClass.ESuperTypes.get(0).name»)
		    	«ENDIF»
		    «ELSE»
		    	«IF eClass.EAttributes.size > 0»
		    	(«FOR eAttributeCtr : eClass.EAttributes SEPARATOR " * "»«AttributeType2Coq(eAttributeCtr)»«ENDFOR»)
		    	«ELSE»
		    	(Empty_set)
		    	«ENDIF»
		    «ENDIF»
			«ENDFOR»
		  end.
		  * 
		Definition «mm»_toEObject («mm_eobject_qarg» : «mm_eobject») : «mm_eobject» := «mm_eobject_qarg».
		Definition «mm»_toELink («mm_elink_qarg» : «mm_elink») : «mm_elink» := «mm_elink_qarg».

		«FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
			Definition «mm»_toEObjectFrom«eClass.name» («arg(eClass.name)» :«eClass.name») : «mm_eobject» :=
			  (Build_«mm_eobject» «eClass.name»«Keywords.PostfixEClass» «arg(eClass.name)»).
			Coercion «mm»_toEObjectFrom«eClass.name» : «eClass.name» >-> «mm_eobject».

		«ENDFOR»
  
        Definition «mm»_defaultInstanceOfEClass («mm_eclass_qarg»: «mm_eclass») : («mm»_getTypeByEClass «mm_eclass_qarg») :=
		  match «mm_eclass_qarg» with
		  «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
		   | «eClass.name»«Keywords.PostfixEClass» => 
		   «EMFUtil.PrintDefaultValue(eClass)»
		  «ENDFOR»
		  end.
		  
	get id of every eobject:
		Definition «mm»_getId («mm_eobject_qarg» : «mm_eobject») : nat :=
		  match «mm_eobject_qarg» with
		«FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
		  | (Build_«mm_eobject» «eClass.name»EClass «mm_eobject_qarg») => «IF eClass.EAllAttributes.size > 0»«val fstAttr = eClass.EAllAttributes.get(0)»(get«eClass.name»«fstAttr.name.toFirstUpper» «mm_eobject_qarg») «ENDIF» 
  		«ENDFOR»
		  end.

    
		(** Helper of building EObject for model **)
		Definition «ePackage.name»«Keywords.PostfixMetamodel»_getEObjectFromEAttributeValues («farg_getEAttributeTypesByEClass» : «ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEClass») : («mm»_getEAttributeTypesByEClass «farg_getEAttributeTypesByEClass») -> «mm_eobject» :=
		  match «farg_getEAttributeTypesByEClass» with
		    «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
		    | «eClass.name»«Keywords.PostfixEClass» => 
		    «IF eClass.ESuperTypes.size > 0 »
		    	«IF eClass.EAttributes.size > 0»
		    	(fun («larg»: («eClass.ESuperTypes.get(0).name» * «FOR eAttributeCtr : eClass.EAttributes SEPARATOR " * "»«AttributeType2Coq(eAttributeCtr)»«ENDFOR»)) => (Build_«mm_eobject» «eClass.name»«Keywords.PostfixEClass» (Build«eClass.name» «PrintCtrArgsByPair(eClass.EAttributes.size+1, larg)»)))
		    	«ELSE»
		    	(fun («larg»: («eClass.ESuperTypes.get(0).name»)) => (Build_«mm_eobject» «eClass.name»«Keywords.PostfixEClass» (Build«eClass.name» «PrintCtrArgsByPair(1, larg)»)))
		    	«ENDIF»
		    «ELSE»
		    	«IF eClass.EAttributes.size > 0»
		    	(fun («larg»: («FOR eAttributeCtr : eClass.EAttributes SEPARATOR " * "»«AttributeType2Coq(eAttributeCtr)»«ENDFOR»)) => (Build_«mm_eobject» «eClass.name»«Keywords.PostfixEClass» (Build«eClass.name» «PrintCtrArgsByPair(eClass.EAttributes.size, larg)»)))
		    	«ELSE»
		    	(fun («larg»: Empty_set) => (Build_«mm_eobject» «eClass.name»«Keywords.PostfixEClass» (Build«eClass.name»)))
		    	«ENDIF»
		    «ENDIF»
			«ENDFOR»
		  end.
		
		(** Helper of building ELink for model **)
		Definition «ePackage.name»«Keywords.PostfixMetamodel»_getELinkFromERoleValues («farg_getERoleTypesByEReference» : «ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEReference») : («mm»_getERoleTypesByEReference «farg_getERoleTypesByEReference») -> «mm_elink» :=
		  match «farg_getERoleTypesByEReference» with
		    «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
				«FOR eReference : eClass.EReferences
		    	»| «eClass.name»«eReference.name.toFirstUpper»«Keywords.PostfixEReference» => (fun («larg»: («eClass.name» * «ReferenceType2Coq(eReference)»)) => (Build_«mm_elink» «eClass.name»«eReference.name.toFirstUpper»«Keywords.PostfixEReference» (Build«eClass.name»«eReference.name.toFirstUpper» «PrintCtrArgsByPair(2, larg)»)))
		    	«ENDFOR»
		    «ENDFOR»
		  end.
	eq check for super class:	
	
 */