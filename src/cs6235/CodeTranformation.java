package cs6235;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import org.jf.dexlib2.writer.pool.StringTypeBasePool;

import soot.ArrayType;
import soot.Body;
import soot.BooleanType;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.PackManager;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.jimple.AbstractExprSwitch;
import soot.jimple.AbstractStmtSwitch;
import soot.jimple.AssignStmt;
import soot.jimple.EqExpr;
import soot.jimple.FieldRef;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.NewExpr;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThisRef;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewExpr;
import soot.util.Chain;
import soot.util.HashChain;

public class CodeTranformation extends SceneTransformer{

	@Override
	protected synchronized void internalTransform(String phaseName, Map<String, String> options) {

		Scene.v().addClass(new SootClass("APL"));

		List <SootClass> allClasses = findAllClasses(); // Find all class present in the input file
		List <SootMethod> allMethods = findAllMethods(allClasses); // find all method present in the input file
		
		System.out.println("INITIAL BODY");
		for(SootClass sootClass: allClasses) { // sootClass is the name of the class
			//replace "Demographics with sootClass"
			
			if(sootClass.getName().equals("Demographics")) { // class name equal to Demographics 
	    		if(!isJDKClass(sootClass)) {
			    	for (SootMethod method : sootClass.getMethods()) { // printing the body of all the method present in the DEmographic Class
			            Body body = method.retrieveActiveBody();
			            System.out.println(body);
			    	}
	    		}
			}
		}
		SootClass dclass = Scene.v().loadClassAndSupport("Demographics"); // Storing all the information of the DEmographics class
		Chain<SootField> allFields = new HashChain<>(dclass.getFields());
		
		addStaticFieldInClass("Demographics");
		
		overwriteEqualsMethod("Demographics");
		
		addFactoryMethodCreateObject("Demographics",allMethods, allFields);

		replaceNewStatements("Demographics", allClasses);
		
		

	}
	
	public static synchronized void replaceNewStatements(String className, List <SootClass> allClasses) {
		
		
		for(SootClass c: allClasses) {
        	if(!isJDKClass(c)) {
	             for(SootMethod method: c.getMethods()) {
	            	 if(!method.getName().equals("create_object2")) {
	     			if(method.hasActiveBody()) {
	    				Body body = method.getActiveBody();
	    				PatchingChain<Unit> units = body.getUnits();
	    				PatchingChain<Unit> newChain = new PatchingChain<>(units);
						Iterator<Unit> iter = newChain.snapshotIterator();
	                    while (iter.hasNext()) {
	                        Unit unit = iter.next();
	                        
//	    				for (Unit unit : body.getUnits()) {
	    					if (unit instanceof AssignStmt) {
	    						AssignStmt assignStmt = (AssignStmt) unit;
	    		                Value rightOp = ((AssignStmt) unit).getRightOp();
	    		                // Check if the statement is an object creation
	    		                if (rightOp instanceof NewExpr) {
	    		                	
	    		                	NewExpr newExpr = (NewExpr)rightOp;
	    		                    // Get the class type being instantiated
	    		                    String instantiatedClass = newExpr.getBaseType().toString();
	    		                    
	    		                    //todo- replace with contains in set of classes to be interned
	    		                    if(instantiatedClass.equals(className)) {
	    		                    	units.remove(unit);
	    		                    	if(iter.hasNext()) {
	    		                    	Unit unitNext = iter.next();
	    		                    	unit.redirectJumpsToThisTo(unitNext);
	    		                    	Stmt stmt = (Stmt) unitNext;
	    		 	                    if (stmt.containsInvokeExpr()) {
	    		 	                        InvokeExpr invokeExpr = stmt.getInvokeExpr();
		    		 	                    
		    		                    	List<Value> constructorArgs = new ArrayList<>(invokeExpr.getArgs());
//		    		                    	
//		    		                    	System.out.println("getargs");
//		    		                    	System.out.println(invokeExpr.getMethod());
//		    		                    	
		    		                    	
		    		                    	//methodArgs --- no use --delete
		    		                    	List<Value> methodArgs = new ArrayList<>();
		    		                    	for (Value arg : constructorArgs) {
		    		                            if (arg instanceof IntConstant) {
		    		                                methodArgs.add(arg); // Assuming integer values are passed as arguments
		    		                            } else if (arg instanceof StringConstant) {
		    		                                methodArgs.add(StringConstant.v(((StringConstant) arg).value));
		    		                            } else {
		    		                                // Handle other types of arguments as needed
		    		                            }
		    		                        }
	    		                    	SootClass sootClass = Scene.v().loadClassAndSupport(className);
	    		                    	
	    		                    	String factoryMethodUtilName = "create_object_util"+ invokeExpr.getArgCount();
	    		                    	SootMethod sm = sootClass.getMethodByName(factoryMethodUtilName);
	    		                    	InvokeExpr createObjectExpr = Jimple.v().newStaticInvokeExpr(
	    		                                 sm.makeRef(),
	    		                                 constructorArgs
	    		                         );
	    		                    
	    		                        
	    		                        Stmt assignmentStmt = Jimple.v().newAssignStmt(
	    		                                assignStmt.getLeftOp(),
	    		                                createObjectExpr
	    		                        );
	    		                        
	    		                       
//	    		                        // Replace the old statement with the new one
	    		                        units.swapWith(unitNext, assignmentStmt);
	    		                        unitNext.redirectJumpsToThisTo(assignmentStmt);
//	    		                        staticinvoke <Demographics: Demographics create_object2(int,java.lang.String)>(600006, "Chennai");
	    		                        
	    		                    	}
	    		                    }
	    		                    }
	    		                }
	    		            
	                        }
	    				}
//	                  //print new method body
//		     			System.out.println("print new method body");
//		     			System.out.println(method.getActiveBody());
	                    
	                   
	                    body.validate();
	                    
	    			}
	            	 }
	     			
	             }
        	}
        }
		
		
      System.out.println("__________________NEW BODY_TADDAAA___________________________________");
      
		for(SootClass c: allClasses) {
	  		if(!isJDKClass(c)) {
			    	for (SootMethod method : c.getMethods()) {
	
				            Body body = method.retrieveActiveBody();
				            System.out.println(body);
			    	}
	  		}
		}
		
		
	}
	
	public static synchronized void addStaticFieldInClass(String className) {
		
		SootClass sootClass = Scene.v().loadClassAndSupport(className);

        RefType hashMapType = RefType.v("java.util.HashMap");
        RefType refTypeClass = RefType.v(sootClass);
        RefType refTypeInteger = RefType.v("java.lang.Integer");
        
        if (!sootClass.declaresFieldByName("object_pool")) {
        	
	        //generic HashMap
	        SootField staticHashMapField = new SootField("object_pool", hashMapType, Modifier.STATIC | Modifier.PUBLIC);
	        sootClass.addField(staticHashMapField);
	        
	        //<clinit> static initializer of class
	        SootMethod clinit = sootClass.getMethodByNameUnsafe("<clinit>");
	
		     // If <clinit> method doesn't exist yet, create it
		     if (clinit == null) {
		    	 
		         clinit = new SootMethod("<clinit>", Collections.emptyList(), VoidType.v(), Modifier.STATIC);
		         sootClass.addMethod(clinit);
		         
		     }
	
		     JimpleBody body = Jimple.v().newBody(clinit);
		     clinit.setActiveBody(body);
		     PatchingChain<Unit> units = body.getUnits();
	
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
	
//		     __________________________________________
		     
//		     Local temp0 = Jimple.v().newLocal("$temp0", RefType.v("java.io.PrintStream"));
//             body.getLocals().add(temp0);
//
//             // Assign value to temp$0
//             Stmt assignStmt = Jimple.v().newAssignStmt(
//                     temp0,
//                     Jimple.v().newStaticFieldRef(Scene.v().getField("<java.lang.System: java.io.PrintStream out>").makeRef())
//             );
//
//             // Invoke println method on temp$0
//             Stmt printlnStmt = Jimple.v().newInvokeStmt(
//                     Jimple.v().newVirtualInvokeExpr(
//                             temp0,
//                             Scene.v().getMethod("<java.io.PrintStream: void println(java.lang.String)>").makeRef(),
//                             object_pool
//                     )
//             );
//
//             // Add the statements to the body
//             body.getUnits().add(assignStmt);
//             body.getUnits().add(printlnStmt);

		     
//		     __________________________________________
		     // Add the return void statement
		     stmt = Jimple.v().newReturnVoidStmt();
		     units.add(stmt);
		     
		     body.validate();
        }
        
        
//
//        System.out.println("__________________NEW BODY After adding Static HashMap____________________________________");
//        List <SootClass> allClasses = findAllClasses(); 
//		for(SootClass c: allClasses) {
//    		if(!isJDKClass(c)) {
//		    	for (SootMethod method : c.getMethods()) {
//
//			            Body body = method.retrieveActiveBody();
//			            System.out.println(body);
//		    	}
//    		}
//		}
	}
	
	
	public static synchronized void overwriteEqualsMethod(String className){
		
		SootClass sootClass = Scene.v().loadClassAndSupport(className);
		
		SootMethod equalsMethod = null;
        for (SootMethod method : sootClass.getMethods()) {
            if (method.getName().equals("equals") && method.getParameterCount() == 1 &&
                    method.getParameterType(0).equals(RefType.v("java.lang.Object"))) {
                equalsMethod = method;
                break;
            }
        }
        
        if(equalsMethod == null) {
//        	List<> parameters = new ArrayList<>();
        	equalsMethod = new SootMethod("equals", new ArrayList<>(), BooleanType.v(), Modifier.PUBLIC);
            sootClass.addMethod(equalsMethod);
            
            Type objectType = RefType.v("java.lang.Object");
            // Create a list of parameter types
            ArrayList<Type> parameterTypes = new ArrayList<>();
            parameterTypes.add(objectType);

            // Set parameter types for the method
            equalsMethod.setParameterTypes(parameterTypes);
        } 
	
            // Generate new body for equals method
            JimpleBody body = Jimple.v().newBody(equalsMethod);
            equalsMethod.setActiveBody(body);

            // Add code to equals method
            PatchingChain<Unit> units = body.getUnits();
            
            Local thisLocal = Jimple.v().newLocal("this", sootClass.getType());
            Local oLocal = Jimple.v().newLocal("o", RefType.v("java.lang.Object"));
            Local temp0 = Jimple.v().newLocal("temp$0", BooleanType.v());
            Local temp1 = Jimple.v().newLocal("temp$1", BooleanType.v());
            
            body.getLocals().add(thisLocal);
            body.getLocals().add(oLocal);
            body.getLocals().add(temp0);
            body.getLocals().add(temp1);
            
            Stmt stmt = Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(sootClass.getType()));
            units.add(stmt);
            
            stmt = Jimple.v().newIdentityStmt(oLocal, Jimple.v().newParameterRef(RefType.v("java.lang.Object"), 0));
            units.add(stmt);
          ///////////////////////////////////////////////

          /////////////////////////////////////////////////
            Stmt targetStmt1 = Jimple.v().newAssignStmt(temp0, IntConstant.v(1));
            
            EqExpr referenceEqualityExpr = Jimple.v().newEqExpr(thisLocal, oLocal);
            //doubt in target and referenceCheck
            IfStmt ifStmt = Jimple.v().newIfStmt(referenceEqualityExpr, targetStmt1);
            units.add(ifStmt);

            //else condition label 2:
            Stmt targetStmt2 = Jimple.v().newAssignStmt(temp1, IntConstant.v(0));
            units.add(targetStmt2);
            stmt = Jimple.v().newReturnStmt(temp1);

            units.add(stmt);
            
            //label 1: 
            units.add(targetStmt1);
            stmt = Jimple.v().newReturnStmt(temp0);

            units.add(stmt);
            body.validate();
	}
	

	public static synchronized void addZeroArgumentConstructor(SootMethod constructor) {
		System.out.println(constructor.getActiveBody());
	}
	
	public static void mapParametersToFields(SootMethod constructor, String className, HashMap<SootField, String> parameterMapping) {
		

		Body body = constructor.retrieveActiveBody();
        System.out.println(body);
        for (Unit unit : body.getUnits()) {
            if (unit instanceof Stmt) {
                Stmt stmt = (Stmt) unit;
                // Check if the statement is an assignment to a field
                if (stmt.containsFieldRef()) {
                    // This statement involves a field assignment in the constructor
                    System.out.println("Field Assignment in Constructor: " + stmt);
                    
                    FieldRef fieldRef = stmt.getFieldRef();
                    SootField field = fieldRef.getField();

                    Value rhsValue = null;
                    if (stmt instanceof AssignStmt) {
                        rhsValue = ((AssignStmt) stmt).getRightOp();
                    }
                    System.out.println("Field Assignment in Constructor: " + field + " "+rhsValue.toString());
                    parameterMapping.put(field, rhsValue.toString());
                }
            }
        }
        

	}
	
	public static synchronized void addMultipleArgumentConstructor(String className, Chain<SootField> allFields) {

		SootClass sootClass = Scene.v().loadClassAndSupport(className);
		
        List<Type> parameterTypesList = new ArrayList<>();
        for(SootField field: allFields) {
        	parameterTypesList.add(field.getType());
        }
//-------------------------------------------------------------------------------------------------------       
     
        /* DEFINING METHOD*/
        
        //public static void create_object(String city_, int pincode_)
        String createObjectMethodName = "create_object"+ parameterTypesList.size();

        SootMethod createObjectMethod = new SootMethod(createObjectMethodName, parameterTypesList, sootClass.getType() , Modifier.PUBLIC | Modifier.STATIC);


        //Set parameter types for the method
//        createObjectMethod.setParameterTypes(parameterTypesList);
        
        /* END- DEFINING METHOD*/
        
//-------------------------------------------------------------------------------------------------------       
        
        sootClass.addMethod(createObjectMethod);
        
        JimpleBody body = Jimple.v().newBody(createObjectMethod);
        createObjectMethod.setActiveBody(body);
        
//        Body bodyConstructor = constructor.retrieveActiveBody();

        PatchingChain<Unit> units = body.getUnits();

        //Extra -- to be removed
//        HashMap<SootField, String> parameterMapping = new HashMap<SootField, String>();
//        mapParametersToFields(constructor, className, parameterMapping);
      //end-  Extra -- to be removed
    

//-------------------------------------------------------------------------------------------------------       
        
        /* ADDING LOCALS FOR PARAMETERS*/  
        
//        List<Local> parameterList = new ArrayList<>(bodyConstructor.getParameterLocals());
        List<Local> parameterListToUse = new ArrayList<>();
        
//        for(int i=0; i<parameterList.size(); i++) {
//        	
//        	 Local local = parameterList.get(i);
//        	 Local parameterLocal = Jimple.v().newLocal(local.getName(), local.getType());
//        	 body.getLocals().add(parameterLocal);
//        	 parameterListToUse.add(parameterLocal);
//	   		 Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(local.getType(), i));
//	   		 units.add(stmt);	
//        	 
//        }
        int k=0;
        for(SootField field: allFields) {
        	
       	 Local parameterLocal = Jimple.v().newLocal(field.getName(), field.getType());
       	 body.getLocals().add(parameterLocal);
       	 parameterListToUse.add(parameterLocal);
   		 Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(field.getType(), k++));
   		 units.add(stmt);	
       	 
       }
        /* END - ADDING LOCALS FOR PARAMETERS*/
        
//-------------------------------------------------------------------------------------------------------       
        
        /* DEFINING OBJECT ARRAY for giving parameter to Objects.hash()*/
//        Local temp$0 = Jimple.v().newLocal("temp$0", ArrayType.v(RefType.v("java.lang.Object"), 1));
//        body.getLocals().add(temp$0);
//        
//        Stmt newArrayStmt = Jimple.v().newAssignStmt(temp$0,Jimple.v().newNewArrayExpr(RefType.v("java.lang.Object"), IntConstant.v(parameterList.size())));
//        units.add(newArrayStmt);
        
        /* END- DEFINING OBJECT ARRAY for giving parameter to Objects.hash()*/

//-------------------------------------------------------------------------------------------------------       
          
        //simpler way
//        Local hashvalue = Jimple.v().newLocal("hashvalue", IntType.v());
//        body.getLocals().add(hashvalue);
//        Stmt hashStmt = Jimple.v().newAssignStmt(
//                hashvalue,
//                Jimple.v().newStaticInvokeExpr(
//                        Scene.v().getMethod("<java.util.Objects: int hash(java.lang.Object[])>").makeRef(),
//                        parameterListToUse
//                )
//        );
//        units.add(hashStmt);
        //END- simple way
        
        
        
//        Local temp$0 = Jimple.v().newLocal("temp$0", RefType.v("java.lang.Object[]"));
//        body.getLocals().add(temp$0);
//        Stmt newArrayStmt = Jimple.v().newAssignStmt(
//                temp$0,
//                Jimple.v().newNewArrayExpr(RefType.v("java.lang.Object"), IntConstant.v(2))
//        );
//        units.add(newArrayStmt);
//        
//        Local temp$1 = Jimple.v().newLocal("temp$1", IntType.v());
//        body.getLocals().add(temp$1);
//        Stmt valueOfStmt = Jimple.v().newAssignStmt(
//                temp$1,
//                Jimple.v().newStaticInvokeExpr(Scene.v().getMethod("<java.lang.Integer: java.lang.Integer valueOf(int)>").makeRef(), parameterList.get(0))
//        );
//        units.add(valueOfStmt);
//        
//        Stmt assignStmt1 = Jimple.v().newAssignStmt(
//                Jimple.v().newArrayRef(temp$0, IntConstant.v(0)),
//                temp$1
//        );
//        units.add(assignStmt1);
//        Stmt assignStmt2 = Jimple.v().newAssignStmt(
//                Jimple.v().newArrayRef(temp$0, IntConstant.v(1)),
//                parameterList.get(1)
//        );
//        units.add(assignStmt2);
//-------------------------------------------------------------------------------------
        
        Local hashvalue = Jimple.v().newLocal("hashvalue", IntType.v());
        body.getLocals().add(hashvalue);
        
        Stmt hashStmt = Jimple.v().newAssignStmt(
              hashvalue, IntConstant.v(10));
//        
        units.add(hashStmt);
        
        /*IF condition(contains.key()) EXPR*/
        
        SootField objectPoolField = Scene.v().getSootClass(className).getFieldByName("object_pool");
        Local temp$3 = Jimple.v().newLocal("temp$3", objectPoolField.getType());
        body.getLocals().add(temp$3);
        
        Stmt stmt = Jimple.v().newAssignStmt(temp$3, Jimple.v().newStaticFieldRef(objectPoolField.makeRef()));
        units.add(stmt);
        
        Local temp$4 = Jimple.v().newLocal("temp$4", Scene.v().getSootClass("java.lang.Integer").getType());
        body.getLocals().add(temp$4);
        
        SootClass _IntegerClass = Scene.v().getSootClass("java.lang.Integer");
        SootMethodRef _IntegerValueOf = Scene.v().makeMethodRef(_IntegerClass, "valueOf", Arrays.asList(IntType.v()), RefType.v("java.lang.Integer"), true);
        List<Local> list = new ArrayList<>();
        list.add(hashvalue);
        Value _Integerrvalue = Jimple.v().newStaticInvokeExpr(_IntegerValueOf, list);
        stmt = Jimple.v().newAssignStmt(temp$4, _Integerrvalue);
        units.add(stmt);
        
        
        Local temp$5 = Jimple.v().newLocal("temp$5", BooleanType.v());
		body.getLocals().add(temp$5);
		
        SootMethodRef _MapContainsKey = Scene.v().makeMethodRef(Scene.v().getSootClass("java.util.HashMap"),"containsKey",Arrays.asList(RefType.v("java.lang.Object")), BooleanType.v(), false);
        Value rvalueMapContainsKey = Jimple.v().newVirtualInvokeExpr(temp$3, _MapContainsKey, temp$4);
        Stmt mapContainsKeyStmt = Jimple.v().newAssignStmt(temp$5, rvalueMapContainsKey);
        units.add(mapContainsKeyStmt);
        
        /*END - IF condition(contains.key()) EXPR*/
        
 /*target stmt --> remaining stmts are in Label 1 - this is also a stmt of label 1*/
        
        Local temp$20 = Jimple.v().newLocal("temp$20",Scene.v().getSootClass(className).getType());
        body.getLocals().add(temp$20);
        Stmt newObjStmt = Jimple.v().newAssignStmt(temp$20,Jimple.v().newNewExpr(Scene.v().getSootClass(className).getType()));
        /*END- target stmts*/
        
        
        /*ACTUAL IF STMT*/
        EqExpr eqExpr = Jimple.v().newEqExpr(temp$5, IntConstant.v(0));

        IfStmt ifStmt = Jimple.v().newIfStmt(eqExpr, newObjStmt);
        units.add(ifStmt);
        /*END- ACTUAL IF STMT*/
        
        /*INSIDE IF BLOCK*/
        
        //APL firstAplNode = object_pool.get(hashvalue);
        objectPoolField = Scene.v().getSootClass(className).getFieldByName("object_pool");
        Local temp$6 = Jimple.v().newLocal("temp$6", objectPoolField.getType());
        body.getLocals().add(temp$6);
        
        
      //Target Stmt
        //Label 2
        Stmt getMapStmt = Jimple.v().newAssignStmt(temp$6, Jimple.v().newStaticFieldRef(objectPoolField.makeRef()));
        units.add(getMapStmt);
        
        Local temp$7 = Jimple.v().newLocal("temp$7", Scene.v().getSootClass("java.lang.Integer").getType());
        body.getLocals().add(temp$7);
        
        _IntegerClass = Scene.v().getSootClass("java.lang.Integer");
        _IntegerValueOf = Scene.v().makeMethodRef(_IntegerClass, "valueOf", Arrays.asList(IntType.v()), RefType.v("java.lang.Integer"), true);
        list = new ArrayList<>();
        list.add(hashvalue);
        _Integerrvalue = Jimple.v().newStaticInvokeExpr(_IntegerValueOf, list);
        stmt = Jimple.v().newAssignStmt(temp$7, _Integerrvalue);
        units.add(stmt);
        
        
//      Value rvalueMapGet = Jimple.v().newVirtualInvokeExpr(temp$6, Scene.v().makeMethodRef(Scene.v().getSootClass("java.util.HashMap"), "get", Arrays.asList(RefType.v("java.lang.Object")), RefType.v("java.lang.Object"), false));
      Local temp$8 = Jimple.v().newLocal("temp$8", Scene.v().getSootClass("java.lang.Object").getType());
      body.getLocals().add(temp$8);
      
      SootMethodRef _MapGet = Scene.v().makeMethodRef(Scene.v().getSootClass("java.util.HashMap"),"get",Arrays.asList(RefType.v("java.lang.Object")), RefType.v("java.lang.Object"), false);
      Value rvalueMapGet = Jimple.v().newVirtualInvokeExpr(temp$6, _MapGet, temp$7);
      Stmt mapGetStmt = Jimple.v().newAssignStmt(temp$8, rvalueMapGet);
      units.add(mapGetStmt);
      
      Local temp$9 = Jimple.v().newLocal("temp$9", Scene.v().getSootClass("APL").getType());
      body.getLocals().add(temp$9);
      
      Stmt castStmt = Jimple.v().newAssignStmt(temp$9, Jimple.v().newCastExpr(temp$8, Scene.v().getSootClass("APL").getType()));
      units.add(castStmt);
      
      //ADD STMTS for new APL Node Linked List
      Local firstAplNode = Jimple.v().newLocal("firstAplNode", Scene.v().getSootClass("APL").getType());
      body.getLocals().add(firstAplNode);
      stmt  = Jimple.v().newAssignStmt(firstAplNode, temp$9);
      units.add(stmt);
      
      Local temp$10 = Jimple.v().newLocal("temp$10", Scene.v().getSootClass(className).getType());
      body.getLocals().add(temp$10);
      
      NewExpr newExpr = Jimple.v().newNewExpr(RefType.v(className));
      Stmt assignmentStmt = Jimple.v().newAssignStmt(temp$10, newExpr);
      units.add(assignmentStmt);
      
      Local d = Jimple.v().newLocal("d", Scene.v().getSootClass(className).getType());
      body.getLocals().add(d);

      
      SootMethodRef initMethodRef = Scene.v().makeConstructorRef(Scene.v().getSootClass(className), parameterTypesList);
      Stmt invokeInitStmt = Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(temp$10, initMethodRef, parameterListToUse));
      units.add(invokeInitStmt);
      
      assignmentStmt = Jimple.v().newAssignStmt(d, temp$10);
      units.add(assignmentStmt);
      
      Local temp$11 = Jimple.v().newLocal("temp$11", Scene.v().getSootClass("java.lang.Class").getType());
      body.getLocals().add(temp$11);

      SootMethodRef _getClassMethod = Scene.v().makeMethodRef(Scene.v().getSootClass(className),"getClass", null , RefType.v("java.lang.Class"), false);

      Value rvalueGetClass = Jimple.v().newVirtualInvokeExpr(d, _getClassMethod);
 
      Stmt getClassAssignmtStmt = Jimple.v().newAssignStmt(temp$11, rvalueGetClass);
      units.add(getClassAssignmtStmt);
      
      Local temp$12 = Jimple.v().newLocal("temp$12", RefType.v("java.lang.String"));
      body.getLocals().add(temp$12);

      SootMethodRef _getNameMethod = Scene.v().makeMethodRef(Scene.v().getSootClass("java.lang.Class"),"getName", null , RefType.v("java.lang.String"), false);

      Value rvalueGetName = Jimple.v().newVirtualInvokeExpr(temp$11, _getNameMethod);
 
      Stmt getNameAssignmtStmt = Jimple.v().newAssignStmt(temp$12, rvalueGetName);
      units.add(getNameAssignmtStmt);

      Local temp$13 = Jimple.v().newLocal("temp$13", Scene.v().getSootClass("java.lang.Object").getType());
      body.getLocals().add(temp$13);
      
      _IntegerClass = Scene.v().getSootClass("java.lang.Integer");
      SootMethodRef _AplSearchRef = Scene.v().makeMethodRef(Scene.v().getSootClass("APL"), "search", Arrays.asList(RefType.v("APL"), RefType.v("java.lang.Object"), RefType.v("java.lang.String")), RefType.v("java.lang.Object"), true);
      list = new ArrayList<>();
      list.add(firstAplNode);
      list.add(d);
      list.add(temp$12);
      Value _AplSearchrvalue = Jimple.v().newStaticInvokeExpr(_AplSearchRef, list);
      stmt = Jimple.v().newAssignStmt(temp$13, _AplSearchrvalue);
      units.add(stmt);
      
      Local obj = Jimple.v().newLocal("obj", Scene.v().getSootClass("java.lang.Object").getType());
      body.getLocals().add(obj);
      
      stmt = Jimple.v().newAssignStmt(obj, temp$13);
      units.add(stmt);
      
      /*target stmt --> remaining stmts are in Label 22 - this is also a stmt of label 22*/
      
      Local temp$14 = Jimple.v().newLocal("temp$14",Scene.v().getSootClass(className).getType());
      body.getLocals().add(temp$14);
      Stmt newObjStmtLabel22 = Jimple.v().newAssignStmt(temp$14,Jimple.v().newNewExpr(Scene.v().getSootClass(className).getType()));
      /*END- target stmts*/
      
      /*ACTUAL IF STMT*/
      eqExpr = Jimple.v().newEqExpr(obj, NullConstant.v());

      ifStmt = Jimple.v().newIfStmt(eqExpr, newObjStmtLabel22);
      units.add(ifStmt);
      /*END- ACTUAL IF STMT*/
      
      //LABEL-3 Else stmt
      Local demo = Jimple.v().newLocal("demo",Scene.v().getSootClass(className).getType());
      body.getLocals().add(demo);
      
      castStmt = Jimple.v().newAssignStmt(demo, Jimple.v().newCastExpr(obj, RefType.v(className)));
      units.add(castStmt);
      
      Stmt returnStmt = Jimple.v().newReturnStmt(demo);
      units.add(returnStmt);
      //END_LABEL 3
      
      //LABEl-22 START
      
      /* OUTSIDE IF(INNER) BLOCK */
      //target stmt of if(INNER)
      units.add(newObjStmtLabel22);
      
      Local new_obj = Jimple.v().newLocal("new_obj",Scene.v().getSootClass(className).getType());
      body.getLocals().add(new_obj);

      initMethodRef = Scene.v().makeConstructorRef(Scene.v().getSootClass(className), parameterTypesList);
      invokeInitStmt = Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(temp$14, initMethodRef, parameterListToUse));
      units.add(invokeInitStmt);
      
      assignmentStmt = Jimple.v().newAssignStmt(new_obj, temp$14);
      units.add(assignmentStmt);
      
    ///Add APL Node stmt
      
      //Doubt package- specification
      Local temp$15 = Jimple.v().newLocal("temp$15", RefType.v("APL"));
      body.getLocals().add(temp$15);
      
      Local newAplNode = Jimple.v().newLocal("newAplNode", RefType.v("APL"));
      body.getLocals().add(newAplNode); 
      
	     NewExpr newAplExpr = Jimple.v().newNewExpr(RefType.v("APL"));
	     
	     AssignStmt assignStmt = Jimple.v().newAssignStmt(temp$15, newAplExpr);
	     
	     body.getUnits().add(assignStmt);
	     
	     SootMethodRef constructorRef = Scene.v().makeConstructorRef(
	             Scene.v().getSootClass("APL"),
	             Collections.singletonList( Scene.v().getSootClass("java.lang.Object").getType())); 

	     InvokeStmt aplConstructorInvoke = Jimple.v().newInvokeStmt(
	             Jimple.v().newSpecialInvokeExpr(temp$15, constructorRef, Collections.singletonList(new_obj)));

	     body.getUnits().add(aplConstructorInvoke);
      
	     assignStmt = Jimple.v().newAssignStmt(newAplNode, temp$15);
	     body.getUnits().add(assignStmt);

	      SootMethodRef _APLInsert = Scene.v().makeMethodRef(Scene.v().getSootClass("APL"), "insert", Arrays.asList(RefType.v("APL"), RefType.v("APL")), VoidType.v(), true);
	        list = new ArrayList<>();
	        list.add(firstAplNode);
	        list.add(newAplNode);
	        InvokeStmt insertInvokeStmt = Jimple.v().newInvokeStmt(
	                Jimple.v().newStaticInvokeExpr(_APLInsert, list));

	        units.add(insertInvokeStmt);
	       
	        //put in map
	        objectPoolField = Scene.v().getSootClass(className).getFieldByName("object_pool");
	        Local temp$16 = Jimple.v().newLocal("temp$16", objectPoolField.getType());
	        body.getLocals().add(temp$16);
	        
	        stmt = Jimple.v().newAssignStmt(temp$16, Jimple.v().newStaticFieldRef(objectPoolField.makeRef()));
	        units.add(stmt);
	        
	        Local temp$17 = Jimple.v().newLocal("temp$17", Scene.v().getSootClass("java.lang.Integer").getType());
	        body.getLocals().add(temp$17);
	        
	        _IntegerClass = Scene.v().getSootClass("java.lang.Integer");
	        _IntegerValueOf = Scene.v().makeMethodRef(_IntegerClass, "valueOf", Arrays.asList(IntType.v()), RefType.v("java.lang.Integer"), true);
	        list = new ArrayList<>();
	        list.add(hashvalue);
	        _Integerrvalue = Jimple.v().newStaticInvokeExpr(_IntegerValueOf, list);
	        stmt = Jimple.v().newAssignStmt(temp$17, _Integerrvalue);
	        units.add(stmt);
	        
	        
	        Local temp$18 = Jimple.v().newLocal("temp$18", Scene.v().getSootClass("java.lang.Object").getType());
			body.getLocals().add(temp$18);
			
	        SootMethodRef _MapPut = Scene.v().makeMethodRef(Scene.v().getSootClass("java.util.HashMap"),"put",Arrays.asList(RefType.v("java.lang.Object"), RefType.v("java.lang.Object")), RefType.v("java.lang.Object"), false);
	        List<Value> values = new ArrayList<>();
	        values.add(temp$17);
	        values.add(newAplNode);
	        Value rvalueMapPut = Jimple.v().newVirtualInvokeExpr(temp$16, _MapPut, values);
	   
	        Stmt mapPutStmt = Jimple.v().newAssignStmt(temp$18, rvalueMapPut);
	        units.add(mapPutStmt);
	     
	        
	        //type cast STMT
	        Local temp$19 = Jimple.v().newLocal("temp$19", RefType.v("APL"));
	        body.getLocals().add(temp$19);
	        
	        castStmt = Jimple.v().newAssignStmt(temp$19, Jimple.v().newCastExpr(temp$18, RefType.v("APL")));
	        units.add(castStmt);
	        //end typecast
	        
	        returnStmt  = Jimple.v().newReturnStmt(new_obj);
	        units.add(returnStmt);
	        /* END OUTSIDE IF BLOCK */

	        
        /* OUTSIDE IF BLOCK */
        //target stmt of if
        //Label 1
        units.add(newObjStmt);
        new_obj = Jimple.v().newLocal("new_obj",Scene.v().getSootClass(className).getType());

        body.getLocals().add(new_obj);

        initMethodRef = Scene.v().makeConstructorRef(Scene.v().getSootClass(className), parameterTypesList);
        invokeInitStmt = Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(temp$20, initMethodRef, parameterListToUse));
        units.add(invokeInitStmt);
        
        assignmentStmt = Jimple.v().newAssignStmt(new_obj, temp$20);
        units.add(assignmentStmt);
        
///Add APL Node stmt
        
        //Doubt package- specification
        Local temp$21 = Jimple.v().newLocal("temp$21", RefType.v("APL"));
        body.getLocals().add(temp$21);
        
        newAplNode = Jimple.v().newLocal("newAplNode", RefType.v("APL"));
        body.getLocals().add(newAplNode);
        
	     newAplExpr = Jimple.v().newNewExpr(RefType.v("APL"));
	     
	     constructorRef = Scene.v().makeConstructorRef(
	             Scene.v().getSootClass("APL"),
	             Collections.singletonList( Scene.v().getSootClass("java.lang.Object").getType())); 
	     
	      aplConstructorInvoke = Jimple.v().newInvokeStmt(
	             Jimple.v().newSpecialInvokeExpr(temp$21, constructorRef, Collections.singletonList(new_obj)));
	     
	      assignStmt = Jimple.v().newAssignStmt(temp$21, newAplExpr);
	     
	     
	     body.getUnits().add(assignStmt);
	     body.getUnits().add(aplConstructorInvoke);
        
	     assignStmt = Jimple.v().newAssignStmt(newAplNode, temp$21);
	     body.getUnits().add(assignStmt);
	     
        //ENd- Add APL Node stmt
        
	   //put in map
	        objectPoolField = Scene.v().getSootClass(className).getFieldByName("object_pool");
	        Local temp$22 = Jimple.v().newLocal("temp$22", objectPoolField.getType());
	        body.getLocals().add(temp$22);
	        
	        stmt = Jimple.v().newAssignStmt(temp$22, Jimple.v().newStaticFieldRef(objectPoolField.makeRef()));
	        units.add(stmt);
	        
	        Local temp$23 = Jimple.v().newLocal("temp$23", Scene.v().getSootClass("java.lang.Integer").getType());
	        body.getLocals().add(temp$23);
	        
	        _IntegerClass = Scene.v().getSootClass("java.lang.Integer");
	        _IntegerValueOf = Scene.v().makeMethodRef(_IntegerClass, "valueOf", Arrays.asList(IntType.v()), RefType.v("java.lang.Integer"), true);
	        list = new ArrayList<>();
	        list.add(hashvalue);
	        _Integerrvalue = Jimple.v().newStaticInvokeExpr(_IntegerValueOf, list);
	        stmt = Jimple.v().newAssignStmt(temp$23, _Integerrvalue);
	        units.add(stmt);
	        
			Local temp$24 = Jimple.v().newLocal("temp$24", Scene.v().getSootClass("java.lang.Object").getType());
			body.getLocals().add(temp$24);
			
	        _MapPut = Scene.v().makeMethodRef(Scene.v().getSootClass("java.util.HashMap"),"put",Arrays.asList(RefType.v("java.lang.Object"), RefType.v("java.lang.Object")), RefType.v("java.lang.Object"), false);
	        values = new ArrayList<>();
	        values.add(temp$23);
	        values.add(newAplNode);
	        rvalueMapPut = Jimple.v().newVirtualInvokeExpr(temp$22, _MapPut, values);
	   
	        mapPutStmt = Jimple.v().newAssignStmt(temp$24, rvalueMapPut);
	        units.add(mapPutStmt);
	        
	        //type cast STMT
	        Local temp$25 = Jimple.v().newLocal("temp$25", RefType.v("APL"));
	        body.getLocals().add(temp$25);

	        castStmt = Jimple.v().newAssignStmt(temp$25, Jimple.v().newCastExpr(temp$24, RefType.v("APL")));
	        units.add(castStmt);
	        //end typecast

	        returnStmt  = Jimple.v().newReturnStmt(new_obj);
	        units.add(returnStmt);
	        /* END OUTSIDE IF BLOCK */
//	        units.add(returnStmt);

	     
//        
        System.out.println("CREATE OBJECT BODY: ");
        System.out.println(body);
        
	}
	

	
	private static Body cloneBody(Body originalBody) {
	    Body clonedBody = Jimple.v().newBody(originalBody.getMethod());
	    PatchingChain<Unit> clonedUnits = clonedBody.getUnits();

	    // Mapping for original locals to cloned locals
	    Map<Local, Local> localMap = new HashMap<>();

	    // Clone locals and update the mapping
	    for (Local originalLocal : originalBody.getLocals()) {
	        Local clonedLocal = Jimple.v().newLocal(originalLocal.getName(), originalLocal.getType());
	        clonedBody.getLocals().add(clonedLocal);
	        localMap.put(originalLocal, clonedLocal);
	    }

	    // Clone units and update references to local variables
	    for (Unit unit : originalBody.getUnits()) {
	        Unit clonedUnit = (Unit) unit.clone();
	        
	        clonedUnit.apply(new AbstractStmtSwitch() {
	        	
	        	@Override
	        	public void caseIdentityStmt(IdentityStmt stmt) {
	        		Value leftOp = stmt.getLeftOp();
	                if (leftOp instanceof Local) {
	                    Local originalLocal = (Local) leftOp;
	                    if (localMap.containsKey(originalLocal)) {
	                    	System.out.println("caseIdentityStmt - "+ unit);
	                        Local clonedLocal = localMap.get(originalLocal);
	                        stmt.setLeftOp(clonedLocal);
	                    }
	                }
	                super.caseIdentityStmt(stmt);
	        	}
	        	
	        	 @Override
	             public void caseAssignStmt(AssignStmt stmt) {
	                 // Update references to local variables in assign statements
	                 Value leftOp = stmt.getLeftOp();
	                 if (leftOp instanceof Local) {
	                     Local originalLocal = (Local) leftOp;
	                     if (localMap.containsKey(originalLocal)) {
	                    	 System.out.println("caseAssignStmt - "+ unit);
	                         Local clonedLocal = localMap.get(originalLocal);
	                         stmt.setLeftOp(clonedLocal);
	                     }
	                 }else if(leftOp instanceof InstanceFieldRef) {
	                	 InstanceFieldRef instanceFieldRef = (InstanceFieldRef) leftOp;
	                	 Local originalLocal = (Local)instanceFieldRef.getBase();
	                	 if (localMap.containsKey(originalLocal)) {
	                    	 System.out.println("caseAssignStmt InstanceFieldRef - "+ unit);
	                         Local clonedLocal = localMap.get(originalLocal);
	                         instanceFieldRef.setBase(clonedLocal);
//	                         instanceFieldRef.setFieldRef(instanceFieldRef.getFieldRef());
//	                         stmt.setLeftOp(instanceFieldRef);
	                     }
	                 }
	                 
	                 Value rightOp = stmt.getRightOp();
	                 if (rightOp instanceof Local) {
	                     Local originalLocal = (Local) rightOp;
	                     if (localMap.containsKey(originalLocal)) {
	                    	 System.out.println("caseAssignStmt rightlocal- "+ unit);
	                         Local clonedLocal = localMap.get(originalLocal);
	                         stmt.setRightOp(clonedLocal);
	                     }
	                 }else if(rightOp instanceof InstanceFieldRef) {
	                	 InstanceFieldRef instanceFieldRef = (InstanceFieldRef) rightOp;
	                	 Local originalLocal = (Local)instanceFieldRef.getBase();
	                	 if (localMap.containsKey(originalLocal)) {
	                    	 System.out.println("caseAssignStmt InstanceFieldRef right- "+ unit);
	                         Local clonedLocal = localMap.get(originalLocal);
	                         instanceFieldRef.setBase(clonedLocal);
//	                         instanceFieldRef.setFieldRef(instanceFieldRef.getFieldRef());
//	                         stmt.setRightOp(instanceFieldRef);
	                     }
	                 }
	                 super.caseAssignStmt(stmt);
	             }
	        	 
	        	 @Override
	             public void caseInvokeStmt(InvokeStmt stmt) {
	        		 
	        		    // Update references to local variables in invoke statements
	        		    InvokeExpr invokeExpr = stmt.getInvokeExpr();
	        		    List<ValueBox> useBoxes = invokeExpr.getUseBoxes();
	        		    for (int i = 0; i < useBoxes.size(); i++) {
	        		        ValueBox useBox = useBoxes.get(i);
	        		        if (useBox.getValue() instanceof Local) {
	        		            Local originalLocal = (Local) useBox.getValue();
	        		            if (localMap.containsKey(originalLocal)) {
	        		            	System.out.println("caseInvokeStmt - "+ unit);
	        		                Local clonedLocal = localMap.get(originalLocal);
	        		                // Create a new ValueBox with the cloned local
	        		                useBoxes.set(i, Jimple.v().newImmediateBox(clonedLocal));
	        		            }
	        		        }
	        		    }
	        		    super.caseInvokeStmt(stmt);
	        		}
	        	
	        });
	        clonedUnits.add(clonedUnit);
	    }

	    return clonedBody;
	}

	
	
	public static synchronized void addFactoryMethodUtil(SootMethod constructor, String className, Chain<SootField> allFields) {

		SootClass sootClass = Scene.v().loadClassAndSupport(className);

        String createObjectMethodName = "create_object_util"+ constructor.getParameterCount();
        
        List<Type> parameterTypeList = new ArrayList<>(constructor.getParameterTypes());

        SootMethod createObjectUtil = new SootMethod(createObjectMethodName, parameterTypeList, sootClass.getType()  , Modifier.PUBLIC | Modifier.STATIC);

        sootClass.addMethod(createObjectUtil);

        // Clone the constructor's body
        Body body = cloneBody(constructor.getActiveBody());
        createObjectUtil.setActiveBody(body);

        System.out.println("CLONED CONSTRUCTOR");
        System.out.println(body);
        
        
	//add locals for formal parameters of constructor
	 Body constructorBody = (Body)constructor.getActiveBody();
    
	List<Local> parameterListToUse = new ArrayList<>();
    HashMap<String, Local> fieldsToUseMap = new HashMap<>();

	PatchingChain<Unit> units = body.getUnits();
	PatchingChain<Unit> chain = new PatchingChain<>(units);
	Iterator<Unit> iterator = chain.snapshotIterator();
	int once=1;
	
	 while (iterator.hasNext()) {
		 Unit unit = iterator.next();
	     if (unit instanceof IdentityStmt) {
	    	 IdentityStmt identityStmt = (IdentityStmt) unit;
	         if (identityStmt.getRightOp() instanceof ThisRef) {
	             body.getUnits().remove(unit);
	         }
	         
	     }else {
	    	 	if(once==1) {
	    	 		//initialize all fields of class
	    	 	    int k=0;
	    	 		
	    	 		for(SootField field: allFields) {

	    	 	       	 Local local1 = Jimple.v().newLocal(field.getName(), field.getType());
	    	 	       	 body.getLocals().add(local1);
	    	 	       	 fieldsToUseMap.put(field.getName(), local1);
	    	 	       	 parameterListToUse.add(local1);
//	    	 	         Stmt stmt = null;
	    	 	         Type localType = field.getType();
	    	 	         String localName = "l"+k++;
	    	 	         if (localType instanceof IntType || localType instanceof BooleanType) {
	    	 	        	 	
	    	 	        	 	Local l0 = Jimple.v().newLocal(localName, localType);
	    	 	        	 	body.getLocals().add(l0);
	    	 	        	 	Stmt stmt = Jimple.v().newAssignStmt(l0, IntConstant.v(0));
	    	 	        	 	body.getUnits().insertBefore(stmt, unit);
	    	 	        	    Stmt stmt1 = Jimple.v().newAssignStmt(local1, l0);
	    	 	        	    body.getUnits().insertAfter(stmt1, stmt);	
	    	 	        	    
	    	 	        } else if (localType instanceof RefType) {
	    	 	        	
	    	 	        	Local l0 = Jimple.v().newLocal(localName, localType);
	    	 	    	 	body.getLocals().add(l0);
	    	 	        	Stmt stmt = Jimple.v().newAssignStmt(l0, NullConstant.v());
	    	 	        	body.getUnits().insertBefore(stmt, unit);	
	    	 	        	Stmt stmt1 = Jimple.v().newAssignStmt(local1, l0);
	    	 	    	    body.getUnits().insertAfter(stmt1, stmt);	
	    	 	        }	 
	    	 		}
	    	 	}
	    	 	
	    	 	once=0;

		    	 if (unit instanceof InvokeStmt) {
		    	 
		             InvokeStmt invokeStmt = (InvokeStmt) unit;
		             InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
		             if (invokeExpr instanceof SpecialInvokeExpr) {
		                 SpecialInvokeExpr specialInvokeExpr = (SpecialInvokeExpr) invokeExpr;
		                 SootMethodRef methodRef = specialInvokeExpr.getMethodRef();
		                 if (specialInvokeExpr.getBase().toString().equals("this") && methodRef.getName().equals("<init>") && methodRef.getParameterTypes().isEmpty()) {
		                     System.out.println("Found specialinvoke to the default constructor: " + unit);
		                     body.getUnits().remove(unit);
		                 }
		
		             }
		    	 }
         }
	   
	 }

	 
	PatchingChain<Unit> newChain = new PatchingChain<>(body.getUnits());
	Iterator<Unit> iter = newChain.snapshotIterator();
	
    while (iter.hasNext()) {
    	
        Unit unit = iter.next();
        if (unit instanceof IdentityStmt) {
            IdentityStmt identityStmt = (IdentityStmt) unit;

            // Check if the right-hand side is a ParameterRef
            Value rightValue = identityStmt.getRightOp();
            if (rightValue instanceof ParameterRef) {
//                ParameterRef parameterRef = (ParameterRef) rightValue;
//                body.getUnits().add(identityStmt);
            }
        
       }else if (unit instanceof AssignStmt) {
    	   
			AssignStmt assignStmt = (AssignStmt) unit;
			Value leftOp = assignStmt.getLeftOp();
            if (leftOp instanceof InstanceFieldRef) {
            	
            	InstanceFieldRef instanceFieldRef = (InstanceFieldRef) leftOp;

            	if (instanceFieldRef.getBase().toString().equals("this")) {
                    System.out.println("Statement of interest: " + assignStmt);

//                    Local lhsLocal = Jimple.v().newLocal(instanceFieldRef.getField().getName(), instanceFieldRef.getField().getType());
////                        Local rhsLocal = (Local) assignStmt.getRightOp();
////                        constructorBody.getLocals().add(lhsLocal);
//                    body.getLocals().add(lhsLocal);
//                    parameterListToUse.add(lhsLocal);
                    Local local = fieldsToUseMap.get(instanceFieldRef.getField().getName());
                    AssignStmt newAssignStmt = Jimple.v().newAssignStmt(local, assignStmt.getRightOp());
                    System.out.println("newAssi "+newAssignStmt);
                        body.getUnits().swapWith(unit, newAssignStmt);
                        unit.redirectJumpsToThisTo(newAssignStmt);
//                    body.getUnits().add(newAssignStmt);
                }
            	    
            }
			
		}else if(unit instanceof ReturnVoidStmt) {
			body.getUnits().remove(unit);
		}
    }
    
    String factoryMethodName = "create_object"+allFields.size();

	SootMethod sm = sootClass.getMethodByName(factoryMethodName);
	InvokeExpr createObjectExpr = Jimple.v().newStaticInvokeExpr(
             sm.makeRef(),
             parameterListToUse
     );

    Local obj = Jimple.v().newLocal("obj",sootClass.getType());
    body.getLocals().add(obj);
    Stmt assignmentStmt = Jimple.v().newAssignStmt(obj, createObjectExpr);
    
//    Unit lastUnit = body.getUnits().getLast();
//    body.getUnits().insertBefore(assignmentStmt, lastUnit);
    body.getUnits().add(assignmentStmt);
    body.getUnits().add(Jimple.v().newReturnStmt(obj));
   

	System.out.println("-----------create_object_util_body--------------------");
	System.out.println(body);
	
	System.out.println("-----------Constructor_body--------------------");
	System.out.println(constructorBody);
	}
	
	
	public static synchronized void addFactoryMethodCreateObjectUtil(SootMethod constructor, String className, Chain<SootField> allFields) {
		
		
		addFactoryMethodUtil(constructor, className, allFields);

	}
	public static synchronized void addOurOwnConstructor(String className, Chain<SootField> allFields) {
		
		SootClass sc = Scene.v().loadClassAndSupport(className);

		List<Type> parameterTypesList = new ArrayList<>();
	        for(SootField field: allFields) {
	        	parameterTypesList.add(field.getType());
	    }

        int modifiers = Modifier.PUBLIC; 

        SootMethod constructor = new SootMethod("<init>", parameterTypesList, VoidType.v(), modifiers);

        JimpleBody body = Jimple.v().newBody(constructor);
        constructor.setActiveBody(body);
        
        boolean constructorExists = false;
        for (SootMethod method : sc.getMethods()) {
            if (method.getName().equals("<init>") && method.getParameterTypes().equals(parameterTypesList)) {
                sc.removeMethod(method);
            }
        }
        
        if(constructorExists == false)
        	sc.addMethod(constructor);
        
        //set body of constructor
        PatchingChain<Unit> units = body.getUnits();
        
        HashMap<SootField, Local> mapFieldsToLocal = new HashMap<>();
    	for(SootField field: allFields) {
    		 Local local1 = Jimple.v().newLocal(field.getName(), field.getType());
    		 body.getLocals().add(local1);
    		 mapFieldsToLocal.put(field, local1);
    	}
    	
    	Local thisLocal = Jimple.v().newLocal("this", RefType.v(className));
    	body.getLocals().add(thisLocal);
    	
    	//add stmt for this
    	Stmt stmt = Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(sc.getType()));
    	units.add(stmt);
    	
    	int i=0;
    	for(SootField field: allFields) {
    		Local originalLocal = mapFieldsToLocal.get(field);
    		stmt = Jimple.v().newIdentityStmt(originalLocal, Jimple.v().newParameterRef(parameterTypesList.get(i), i));
    		units.add(stmt);
    		i++;
    	}
    	
    	//invoke construtor
    	stmt = Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(thisLocal, Scene.v().makeConstructorRef(RefType.v("java.lang.Object").getSootClass(),  java.util.Collections.emptyList())));
    	units.add(stmt);
    	
    	//initialize all fields
    	for(SootField field: allFields) {
    		Local originalLocal = mapFieldsToLocal.get(field);
    		stmt = Jimple.v().newAssignStmt(Jimple.v().newInstanceFieldRef(thisLocal, field.makeRef()), originalLocal);
            units.add(stmt);
    	}
    	
    	units.add(Jimple.v().newReturnVoidStmt());

    	 System.out.println("------------Our own constructor's body------- ");
     	System.out.println(body);
     	 body.validate();
	}
	

	public static synchronized void modifyConstructorAccessModifier(String className) {

	        SootClass sootClass = Scene.v().loadClassAndSupport(className);
			List <SootMethod> allMethodsOfClassName = new ArrayList <SootMethod>(sootClass.getMethods());

	        for (SootMethod method : allMethodsOfClassName) {
	        	
	            if (method.isConstructor() && method.hasActiveBody()) {
	            	System.out.println("acc--" + method);
	            	System.out.println(method.getModifiers());
	            	
	            	int modifiers = method.getModifiers();

	                // Set the private access modifier using bitwise operations
	                modifiers = Modifier.PRIVATE;

	                // Update the modifiers of the method
	                method.setModifiers(modifiers);
	            	
	    	        System.out.println(method.getModifiers());
	            	}
	        }
	       
	}
	
	public static synchronized void addFactoryMethodCreateObject(String className, List <SootMethod> allMethods, Chain<SootField> allFields) {
		
		SootClass sootClass = Scene.v().loadClassAndSupport(className);
		List <SootMethod> allMethodsOfClassName = new ArrayList <SootMethod>(sootClass.getMethods());
		
		//add factory method corresponding to all fields
		
		addMultipleArgumentConstructor(className, allFields);
		
        for (SootMethod method : allMethodsOfClassName) {
            if (method.isConstructor() && method.hasActiveBody()) {
            	System.out.println("Method:" + method);
            	System.out.println(method.getActiveBody());
            	addFactoryMethodCreateObjectUtil(method, className, allFields);
            	System.out.println("Method END:" + method);
            }
        }
        
        
        modifyConstructorAccessModifier(className);
        addOurOwnConstructor(className, allFields);
        
        
	}

	
	 public static List<SootClass>findAllClasses(){
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
	    
     
	 public static boolean isJDKClass(SootClass sootClass) {
	     String packageName = sootClass.getPackageName();
	     return packageName.startsWith("java.") || packageName.startsWith("javax.") || sootClass.toString().startsWith("jdk");
	 }

	 public List<SootMethod> findAllMethods(List<SootClass>classes) {
			
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

}

	

