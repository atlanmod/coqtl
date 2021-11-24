package fr.inria.atlanmod.coqtl.xmi.core

import fr.inria.atlanmod.coqtl.util.EMFUtil
import fr.inria.atlanmod.coqtl.util.URIUtil
import org.eclipse.emf.common.util.URI
import java.io.File

class XMIGeneratorDriver {
	
	def static doGeneration(URI mm_path, URI model, URI output_uri, String exname, String mmname, String filename){
		
		val resource_set = EMFUtil.loadEcore(mm_path)
		val resource = resource_set.getResource(model, true)
		
		var content = ""
		val compiler = new XMI2Coq
		
		content += compiler.mapEObjects(resource.contents, exname, mmname, filename)	
		
		URIUtil.write(output_uri, content)
	}
	
	
	def static getFileName(URI m_path, int level){
		var f = m_path.trimFileExtension().segment(level)
		return f.toString
	}
	
	def static void main(String[] args) {
		
		if(args.length < 2){
			println("Input of xmi2v:");
			println("1. model relative path, e.g. /./resources/TT2BDD/tt.xor.xmi");
			println("2. metamodel relative path, e.g. /./resources/TT2BDD/TT.ecore");
			println("3. (optional) output path, e.g. /./resources/TT2BDD/tt.xor.v");
			System.exit(0)
		}
		
		val m_path = args.get(0)
		val mm_path = args.get(1)
		var output_path = ""

		if(args.length == 3)
		  	output_path = args.get(2)
		else
			output_path = args.get(0).substring(0, args.get(0).length() - 3)+"v"
		
		//val m_path = "./resources/TT2BDD/tt.xor.xmi"
		//val mm_path = "./resources/TT2BDD/TT.ecore"
		//val output_path = "./resources/model.v"
		//val exname = "TT2BDD"
		//val mmname = "TT"
		
		val m_uri = URI.createFileURI(m_path);
		val mm_uri = URI.createFileURI(mm_path)
		val output_uri = URI.createFileURI(output_path);
		
		val exname = getFileName(mm_uri, mm_uri.segmentCount-2)
		val mmname = getFileName(mm_uri, mm_uri.segmentCount-1)
		val filename = getFileName(m_uri, m_uri.segmentCount-1)
		
        doGeneration(mm_uri, m_uri, output_uri, exname, mmname, filename)

    }
	
    

}
