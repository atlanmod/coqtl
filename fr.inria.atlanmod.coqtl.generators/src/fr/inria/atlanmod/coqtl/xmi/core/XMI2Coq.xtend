package fr.inria.atlanmod.coqtl.xmi.core

import java.util.HashSet
import java.util.Set
import org.eclipse.emf.common.util.EList
import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.impl.DynamicEObjectImpl
import org.eclipse.emf.ecore.EReference
import fr.inria.atlanmod.coqtl.util.Keywords
import org.eclipse.emf.ecore.EAttribute
import org.eclipse.emf.ecore.EStructuralFeature
import fr.inria.atlanmod.coqtl.util.EMFUtil

class XMI2Coq {
  
	Set<Object> lookup;
	
  	new() {
    	lookup = new HashSet<Object>
  	}
	
	
	/* 
	 * Entry point of model to Boogie transformation
	 * */ 
	def mapEObjects(EList<EObject> eobjects) '''
		«var allEObjects = new HashSet»
		«val root = eobjects.get(0)»
		«val mm = root.eClass.EPackage.name+Keywords.PostfixMetamodel»
		«val mm_eobject = '''«mm»_«Keywords.PostfixEObject»'''»
		«val mm_elink = '''«mm»_«Keywords.PostfixELink»'''»
		
		«FOR eobject: eobjects.filter(typeof(EObject))»		
			«val ignore = allEObjects.addAll(getAllEObjects(eobject))»		
		«ENDFOR»
		Definition InputModel : Model «mm_eobject» «mm_elink» :=
			(BuildModel
				(«FOR eobject : allEObjects SEPARATOR " :: "»(Build_«mm_eobject» «eobject.eClass.name»«Keywords.PostfixEClass» «BuildEObject(eobject)»)«ENDFOR» :: nil)
				(«FOR eobject : allEObjects SEPARATOR " :: \n"»«FOR sf : eobject.eClass.EStructuralFeatures.filter(typeof(EReference)) SEPARATOR " :: \n"»(Build_«mm_elink» «eobject.eClass.name»«sf.name.toFirstUpper»«Keywords.PostfixEReference» «BuildELink(eobject, sf)»)«ENDFOR»«ENDFOR» :: nil)
			).
	'''
	
	def BuildEObject(EObject eobject) '''
		(Build«eobject.eClass.name» «
			FOR sf: eobject.eClass.EStructuralFeatures.filter(typeof(EAttribute)) SEPARATOR " "
			»«EMFUtil.PrintValue(eobject.eGet(sf))»«
			ENDFOR»)'''
	
	def BuildELink(EObject eobject, EStructuralFeature sf)'''
		«val sf_value = eobject.eGet(sf)»
		(Build«eobject.eClass.name»«sf.name.toFirstUpper» «BuildEObject(eobject)» «BuildEReference(sf_value)»)'''
	
	def BuildEReference(Object sf_value) '''
		«IF sf_value instanceof EList 
		»(«FOR v : sf_value.filter(typeof(EObject)) SEPARATOR " :: "»«BuildEObject(v)»«ENDFOR» :: nil )«
		ELSEIF sf_value instanceof EObject
		»«BuildEObject(sf_value as EObject)»«
		ENDIF»'''
	
	def HashSet<EObject> getAllEObjects(EObject o) {
		var rtn = new HashSet
		
		if(!this.lookup.contains(o) && o instanceof DynamicEObjectImpl){
			val eobject = o as DynamicEObjectImpl
			rtn.add(eobject)
			this.lookup.add(eobject)
				
			for(sf : eobject.eClass.EStructuralFeatures.filter(typeof(EReference))){
				val sf_value = eobject.eGet(sf)
				
				if(sf_value instanceof EList){
					for(v : sf_value.filter(typeof(EObject))){
						rtn.addAll(getAllEObjects(v))
					}
				}else if(sf_value instanceof EObject){
					rtn.addAll(getAllEObjects(sf_value))
				}
			}
		}
		
		return rtn
	}
	
}
