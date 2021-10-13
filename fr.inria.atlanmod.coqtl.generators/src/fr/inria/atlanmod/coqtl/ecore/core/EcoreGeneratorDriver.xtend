package fr.inria.atlanmod.coqtl.ecore.core

import fr.inria.atlanmod.coqtl.util.EMFUtil
import fr.inria.atlanmod.coqtl.util.URIUtil
import org.eclipse.emf.common.util.URI
import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl
import org.eclipse.emf.ecore.xmi.impl.EcoreResourceFactoryImpl

class EcoreGeneratorDriver {
	
	/** 
	 * Setup EMF factories, precondition to load ecore resources into memory.
	 * */
	def static doEMFSetup() {
		// register resource processors
		Resource.Factory.Registry.INSTANCE.extensionToFactoryMap.put("ecore", new EcoreResourceFactoryImpl());
	}
	
	def static doGeneration(URI metamodel, URI output_uri){
		val resource_set = new ResourceSetImpl
		val resource = resource_set.getResource(metamodel, true)
		val epackage = EMFUtil.getEPackage(resource)
		
		var content = ""
		content += Ecore2Coq.mapEPackage(epackage)	
		URIUtil.write(output_uri, content)
	}
	
	def static void main(String[] args) {

		if(args.length < 1){
			println("Input of ecore2v:");
			println("1. metamodel relative path, e.g. ./resources/TT2BDD/TT.ecore");
			println("2. (optional) output file path, e.g. ./resources/TT2BDD/TT.v");
			System.exit(0)
		}

		val mm_path = args.get(0)

		var output_path = ""

		if(args.length == 2)
		  	output_path = args.get(1)
		else
			output_path = args.get(0).substring(0, args.get(0).length() - 5)+"v"

		val mm_uri = URI.createFileURI(mm_path);
		val output_uri = URI.createFileURI(output_path);
		
		doEMFSetup
        doGeneration(mm_uri, output_uri)

    }
    

}