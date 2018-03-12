package fr.inria.atlanmod.coqtl.xmi.core

import fr.inria.atlanmod.coqtl.util.EMFUtil
import fr.inria.atlanmod.coqtl.util.URIUtil
import org.eclipse.emf.common.util.URI

class XMIGeneratorDriver {
	
	def static doGeneration(URI mm_path, URI model, URI output_uri){
		
		val resource_set = EMFUtil.loadEcore(mm_path)
		val resource = resource_set.getResource(model, true)
		
		var content = ""
		val compiler = new XMI2Coq
		content += compiler.mapEObjects(resource.contents)	
		URIUtil.write(output_uri, content)
	}
	
	def static void main(String[] args) {
		val m_path = "./resources/Class.xmi"
		val mm_path = "./resources/Class.ecore"
		//val mm_path = "./resources/Relational.ecore"
		val m_uri = URI.createFileURI(m_path);
		val mm_uri = URI.createFileURI(mm_path)
		val output_path = "./resources/output_xmi.v"
		val output_uri = URI.createFileURI(output_path);
		
		
        doGeneration(mm_uri, m_uri, output_uri)

    }
    

}
