package cs6235;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import soot.Body;
import soot.Local;
import soot.Modifier;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.VoidType;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.Stmt;
import soot.util.Chain;
import soot.util.HashChain;

public class MtpTransformation extends SceneTransformer{

	@Override
	protected synchronized void internalTransform(String phaseName, Map<String, String> options) {
		
		System.out.println("----------------------internalTransform---------------------");
		
		Scene.v().addClass(new SootClass("APL"));

		List <SootClass> allClasses = findAllClasses(); 
		List <SootMethod> allMethods = findAllMethods(allClasses);
		
	
//		for(SootMethod sootMethod:allMethods){
//			if(!sootMethod.getName().equals("<init>"))
//			System.out.println(sootMethod+"  "+sootMethod.getName());
//		}
		
//		for(SootClass sootClass: allClasses) {
//			System.out.println(sootClass+"  "+sootClass.getName());
//			if(sootClass.getName().equals("Test")) {
//	    		if(!isJDKClass(sootClass)) {
//			    	for (SootMethod method : sootClass.getMethods()) {
//			            Body body = method.retrieveActiveBody();
//			            System.out.println(body);
//			    	}
//	    		}
//			}
//		}
		
		
		SootClass dclass = Scene.v().loadClassAndSupport("Demographics");
//		System.out.println(dclass);
		Chain<SootField> allFields = new HashChain<>(dclass.getFields());
		
		
//		for(SootField it:allFields)
//		{
//			System.out.println(it);
//		}
//		System.out.println(dclass.getName());
//		System.out.println(dclass.getMethods());
		
		addStaticFieldInClass("Demographics");


	}
	
public static synchronized void addStaticFieldInClass(String className) {
	System.out.println("----------------------addStaticFieldClass---------------------");
		SootClass sootClass = Scene.v().loadClassAndSupport(className);

        RefType hashMapType = RefType.v("java.util.HashMap");
        RefType refTypeClass = RefType.v(sootClass);
        RefType refTypeInteger = RefType.v("java.lang.Integer");
        
//        System.out.println(sootClass);
//        System.out.println(hashMapType);
//        System.out.println(refTypeClass);
//        System.out.println(refTypeInteger);
        
        if (!sootClass.declaresFieldByName("object_pool")) {
        	
	        //generic HashMap
	        SootField staticHashMapField = new SootField("object_pool", hashMapType, Modifier.STATIC | Modifier.PUBLIC);
	        sootClass.addField(staticHashMapField);
	        
//			Chain<SootField> allFields = new HashChain<>(sootClass.getFields());
//			for(SootField it:allFields)
//			{
//				System.out.println(it);
//			}
	        
	        
//	        //<clinit> static initializer of class
	        SootMethod clinit = sootClass.getMethodByNameUnsafe("<clinit>");
//	
//		     // If <clinit> method doesn't exist yet, create it
	        
		     if (clinit == null) {
		    	 
		         clinit = new SootMethod("<clinit>", Collections.emptyList(), VoidType.v(), Modifier.STATIC);
		         sootClass.addMethod(clinit);
		         
		     }
//		     for (SootMethod method : sootClass.getMethods()) {
//		            //Body body = method.retrieveActiveBody();
//		            System.out.println(method);
//		    	}
		     
//	
		     JimpleBody body = Jimple.v().newBody(clinit);
		     clinit.setActiveBody(body);
//		     System.out.println(clinit);
		     PatchingChain<Unit> units = body.getUnits();
		     for(Unit x:units)
		     {
		    	 System.out.println(x);
		     }
	
		     // Create a local for the HashMap
		     
		     //Shouldn't be in Local-- its a object field therefore not adding to locals
		     Local object_pool = Jimple.v().newLocal("object_pool", hashMapType);
		     
		     body.getLocals().add(object_pool);
	
		     // Create an assignment statement to initialize the HashMap
		     Stmt stmt = Jimple.v().newAssignStmt(object_pool, Jimple.v().newNewExpr(hashMapType));
		     units.add(stmt);
	
		     stmt = Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(object_pool, Scene.v().getMethod("<java.util.HashMap: void <init>()>").makeRef(), Collections.<Value>emptyList()));
		     units.add(stmt);
	
		     // Add the HashMap to the static field
		     stmt = Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(staticHashMapField.makeRef()), object_pool);
		     units.add(stmt);
		    
		     // Add the return void statement
		     stmt = Jimple.v().newReturnVoidStmt();
		     units.add(stmt);
		     
		     
		     
//		     System.out.println(body);
		     body.validate();
        }
        
  
      
	}
	












	public static List<SootClass>findAllClasses(){
		
		System.out.println("----------------------findAllClasses---------------------");
    	Chain <SootClass> classes = Scene.v().getApplicationClasses(); // Get the Chain of classes		
	    List <SootClass> listClasses = new ArrayList <>(classes); // Convert Chain to ArrayList
	    List<SootClass> nonLibraryClasses = new ArrayList<>();
	    for(SootClass c: listClasses) {
	    	if(!c.isLibraryClass() && !isJDKClass(c)) {
	    		nonLibraryClasses.add(c);
	    	}
	    }
	    return nonLibraryClasses;
  }
	
	public List<SootMethod> findAllMethods(List<SootClass>classes) {
		System.out.println("----------------------findAllMethods---------------------");
        List<SootMethod>methods = new ArrayList<>();

        for(SootClass c: classes) {
        	if(!isJDKClass(c)) {
	             for(SootMethod method: c.getMethods()) {
	                 methods.add(method);
	             }
        	}
        }
        return methods;

    }
	
	public static boolean isJDKClass(SootClass sootClass) {
		 //System.out.println("----------------------isJDKClass---------------------");
	     String packageName = sootClass.getPackageName();
	     return packageName.startsWith("java.") || packageName.startsWith("javax.") || sootClass.toString().startsWith("jdk");
	 }

}
