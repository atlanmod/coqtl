package fr.inria.atlanmod.coqtl.xmi.core

import fr.inria.atlanmod.coqtl.util.EMFUtil
import fr.inria.atlanmod.coqtl.util.URIUtil
import org.eclipse.emf.common.util.URI

class XMIGeneratorDriver {
	
	def static doGeneration(URI mm_path, URI model, URI output_uri, String exname, String mmname){
		
		val resource_set = EMFUtil.loadEcore(mm_path)
		val resource = resource_set.getResource(model, true)
		
		var content = ""
		val compiler = new XMI2Coq
		
		content += compiler.mapEObjects(resource.contents, exname, mmname)	
		
		URIUtil.write(output_uri, content)
	}
	
	def static void main(String[] args) {
		
		if(args.length < 5){
			println("Input of XMI2Coq:");
			println("1. example name, e.g. TT2BDD");
			println("2. metamodel name, e.g. TT");
			println("3. metamodel relative path, e.g. /./resources/TT2BDD/TT.ecore");
			println("4. model relative path, e.g. /./resources/TT2BDD/tt.xor.xmi");
			println("5. output path, e.g. /./resources/model.v");
			System.exit(0)
		}
		
		val exname = args.get(0)
		val mmname = args.get(1)
		val mm_path = args.get(2)
		val m_path = args.get(3)
		val output_path = args.get(4)
		
		//val m_path = "./resources/TT2BDD/tt.xor.xmi"
		//val mm_path = "./resources/TT2BDD/TT.ecore"
		//val output_path = "./resources/model.v"
		//val exname = "TT2BDD"
		//val mmname = "TT"
		
		val m_uri = URI.createFileURI(m_path);
		val mm_uri = URI.createFileURI(mm_path)
		val output_uri = URI.createFileURI(output_path);
			
        doGeneration(mm_uri, m_uri, output_uri, exname, mmname)

    }
	
    

}
