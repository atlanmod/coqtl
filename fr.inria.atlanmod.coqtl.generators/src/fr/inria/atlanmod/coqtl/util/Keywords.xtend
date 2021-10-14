package fr.inria.atlanmod.coqtl.util

import org.eclipse.emf.ecore.EReference

class Keywords {
	
	// naming convensions
	
	public static final String PostfixMetamodel = "Metamodel";
	
	public static final String PostfixEClass = "Class";
	public static final String PostfixEReference = "Reference";
	public static final String PostfixEObject = "Object";
	public static final String PostfixELink = "Link";
	public static final String Inherit = "Is";
	
	// (* Generic functions *)
	
	def static getRefOnLinks_FunName(String eElass, String eRef) { return String::format("%s_get%sOnLinks", eElass, eRef.toFirstUpper)}
	def static getRefOnModel_FunName(String eElass, String eRef) { return String::format("%s_get%s", eElass, eRef.toFirstUpper)}
	def static getRefOnModelObject_FunName(EReference ref, String eElass, String eRef) { 
		if (ref.upperBound == -1)
			return String::format("%s_get%sObjects", eElass, eRef.toFirstUpper)
		else
			return String::format("%s_get%sObject", eElass, eRef.toFirstUpper)
	}
	
	// (* Typeclass Instances *)	
	
	public static final String ElementSum = "ElementSum";
	public static  final String LinkSum = "LinkSum"
	public static final String MetamodelTypeClassName = "Metamodel";
	public static final String ModelingMetamodelTypeClassName = "ModelingMetamodel";
	
	def static Elem_toSubType_FunName (String mm) { return String::format("%s_to%s", mm, PostfixEClass)}
	def static Elem_toSumType_FunName (String mm) { return String::format("%s_to%s", mm, PostfixEObject)}
	def static Elem_denoteSubType_FunName (String mm) { return String::format("%s_getTypeBy%s", mm, PostfixEClass)}
	def static Link_toSubType_FunName (String mm) { return String::format("%s_to%s", mm, PostfixEReference)}
	def static Link_toSumType_FunName (String mm) { return String::format("%s_to%s", mm, PostfixELink)}
	def static Link_denoteSubType_FunName (String mm) { return String::format("%s_getTypeBy%s", mm, PostfixEReference)}
	
	
	
	
}