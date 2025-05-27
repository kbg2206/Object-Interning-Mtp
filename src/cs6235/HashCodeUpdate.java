package cs6235;


import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Vector;
import org.jf.dexlib2.writer.pool.StringTypeBasePool;
import soot.ArrayType;
import soot.Body;
import soot.BooleanType;
import soot.ByteType;
import soot.CharType;
import soot.DoubleType;
import soot.FloatType;
import soot.IntType;
import soot.IntegerType;
import soot.Local;
import soot.LongType;
import soot.Modifier;
import soot.NormalUnitPrinter;
import soot.PackManager;
import soot.PatchingChain;
import soot.RefLikeType;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.ShortType;
import soot.SootClass;
import soot.SootField;
import soot.SootFieldRef;
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
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.DoubleConstant;
import soot.jimple.EqExpr;
import soot.jimple.FieldRef;
import soot.jimple.FloatConstant;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.LongConstant;
import soot.jimple.NewExpr;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThisRef;
import soot.jimple.UnopExpr;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewExpr;
import soot.tagkit.Tag;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.scalar.SimpleLocalDefs;
import soot.util.Chain;
import soot.util.HashChain;


public class HashCodeUpdate extends SceneTransformer{
	private Map<String, List<String>> adjacencyList = new HashMap<>();
//	private final Map<String, List<String>> adjacencyList2 = new HashMap<>();
	List<SootClass> allClasses = new ArrayList<>();
	HashSet<SootClass> constantClass = new HashSet<>();
	HashSet<SootClass> notAConstantClass = new HashSet<>();
	HashMap<SootClass,HashMap<SootMethod,String>> constructorMapping = new HashMap<>();
	HashSet<SootClass> goodClasses = new HashSet<>();
	private List<String> targetClasses;
	int count=0;
	int invokeCount = 0;
	
	public HashCodeUpdate(List<String> targetClasses) {
        this.targetClasses = targetClasses;
        
		System.out.println(this.targetClasses);
        
    }
	
	@Override
	protected synchronized void internalTransform(String phaseName, Map<String, String> options) {
		
//		List<SootClass> classes = new ArrayList<>(Scene.v().getClasses());
//
//		for (SootClass sc : classes) {
//		    if (!sc.isPhantom()) {
//		        for (SootMethod method : sc.getMethods()) {
//		            if (!method.isConcrete()) continue;
//
//		            try {
//		            	if(method.hasActiveBody()==false) continue;
//		                method.retrieveActiveBody(); // force body creation
//		            } catch (Exception e) {
//		                System.err.println("Skipping method: " + method.getSignature());
//		                e.printStackTrace();
//		            }
//		        }
//		    }
//		}
		
		
//		Scene.v().loadNecessaryClasses();
//		for (SootClass c : Scene.v().getClasses()) {
//		    if (c.isPhantom()) {
////		    	c.setApplicationClass();
//		        System.out.println("Phantom class: " + c.getName());
//		    }
//		}

		
		
		Boolean flag = false;
		
		if(flag==true) {
			findAllClasses();
			SootClass dummyClass = new SootClass("Dummy", Modifier.PUBLIC);
			Scene.v().addClass(dummyClass);  

			dummyClass.setApplicationClass(); 

			System.out.println(allClasses.size()+" Classes based on hierarchy " + allClasses);
			findAllConstantClasses(allClasses);

			System.out.println(constantClass.size()+" Constant classes " + constantClass);
			
			
			
			for(SootClass sootClass: allClasses) {
				
//				if(sootClass.isPhantom()) continue;
				
				SootMethod method = new SootMethod(
				        "SuperHashCode",
				        new ArrayList<>(),         // No parameters
				        IntType.v(),              // Return type: int
				        Modifier.PUBLIC           // Public, non-static
				    );
				
				sootClass.addMethod(method);
				// Create method body
			    JimpleBody body = Jimple.v().newBody(method);
			    method.setActiveBody(body);

			    Local thisLocal = Jimple.v().newLocal("this", RefType.v(sootClass.getName()));
			    body.getLocals().add(thisLocal);

			    // this = @this
			    body.getUnits().add(Jimple.v().newIdentityStmt(
			        thisLocal, Jimple.v().newThisRef(RefType.v(sootClass.getName()))
			    ));

			    // return 42;
			    body.getUnits().add(Jimple.v().newReturnStmt(IntConstant.v(42)));
			}

			for(SootClass sootClass : allClasses){
				
//				createHashVfunction(sootClass);
				
				if(constantClass.contains(sootClass) ){
					Scene.v().loadClassAndSupport(sootClass.toString());
					sootClass.setApplicationClass();
					overwriteEqualsMethod(sootClass.toString());
					addStaticFieldInClass(sootClass.toString());
					createGenerateCustomHashMethod(sootClass);
					createHashVfunction(sootClass);
				}
			}


			for(SootClass sootClass:constantClass) {
				String[] classList = sootClass.toString().split("\\.");
				String className = classList[classList.length-1];
				ProgramCreation(sootClass,className);
//				printStmtV2(sootClass);
			}


			for(SootClass sootClass : allClasses){
				transformConstructorCalls(sootClass);
			}

			System.out.println(count);
			System.out.println(invokeCount);


		}
		else {
			
			findAllClasses();
			for(SootClass sootClass:allClasses) {
				goodClasses.add(sootClass);			
			}
			allClasses.clear();
			System.out.println(allClasses);
			
			adjacencyList.clear();
			findAllParentGoodClasses();
			SootClass dummyClass = new SootClass("Dummy", Modifier.PUBLIC);
			Scene.v().addClass(dummyClass);  

			dummyClass.setApplicationClass(); 
			
			Collections.reverse(allClasses);
			
			for(SootClass sootClass : allClasses) {
				constantClass.add(sootClass);
			}
			
			
			for(SootClass sootClass: allClasses) {

				//				if(sootClass.isPhantom()) continue;

				SootMethod method = new SootMethod(
						"SuperHashCode",
						new ArrayList<>(),         // No parameters
						IntType.v(),              // Return type: int
						Modifier.PUBLIC           // Public, non-static
						);

				sootClass.addMethod(method);
				// Create method body
				JimpleBody body = Jimple.v().newBody(method);
				method.setActiveBody(body);

				Local thisLocal = Jimple.v().newLocal("this", RefType.v(sootClass.getName()));
				body.getLocals().add(thisLocal);

				// this = @this
				body.getUnits().add(Jimple.v().newIdentityStmt(
						thisLocal, Jimple.v().newThisRef(RefType.v(sootClass.getName()))
						));

				// return 42;
				body.getUnits().add(Jimple.v().newReturnStmt(IntConstant.v(42)));
			}
			
			System.out.println(allClasses);
			System.out.println(goodClasses.size());
			for(SootClass sootClass : allClasses){
				if(constantClass.contains(sootClass) ){
					Scene.v().loadClassAndSupport(sootClass.toString());
					sootClass.setApplicationClass();
					
					System.out.println(sootClass+" "+sootClass.getSuperclass());
					overwriteEqualsMethod(sootClass.toString());
					addStaticFieldInClass(sootClass.toString());
					createGenerateCustomHashMethod(sootClass);
					createHashVfunction(sootClass);
				}
			}


			for(SootClass sootClass:constantClass) {
				String[] classList = sootClass.toString().split("\\.");
				String className = classList[classList.length-1];
				ProgramCreation(sootClass,className);
//				System.out.println(sootClass+" "+sootClass.getSuperclass());
//				printStmtV2(sootClass);
			}


			for(SootClass sootClass : goodClasses){
				transformConstructorCalls(sootClass);
			}

			System.out.println(count);
			System.out.println(invokeCount);
			
			
//			SootClass sotClass = Scene.v().loadClassAndSupport(targetClasses.get(0));
			for(SootClass sootClass:constantClass) {
				System.out.println(sootClass+" ++++++++++++++++++++++++++++");
				for(SootMethod sootMethod:sootClass.getMethods()) {
					
					
					if(sootClass.toString().equals("org.jaxen.expr.IdentitySet$IdentityWrapper"))
					System.out.println(sootMethod.retrieveActiveBody());
				}
			}
		}


	}
	
	private void findAllParentGoodClasses() {
		
		Chain <SootClass> classes = Scene.v().getApplicationClasses(); 	
		List <SootClass> listClasses = new ArrayList <>(classes); 
		List<SootClass> nonLibraryClasses = new ArrayList<>();
		for(SootClass c: listClasses) {
			if(!c.isLibraryClass() && !isJDKClass(c) && !c.isInterface() && !c.isAbstract()) {
				nonLibraryClasses.add(c);
//				goodClasses.add(c);
			}
		}
		
		
		for (SootClass sootClass : nonLibraryClasses) {
            addClass(sootClass.getName());

            if (sootClass.hasSuperclass()) {
                SootClass parent = sootClass.getSuperclass();
                if(!parent.isLibraryClass() && !isJDKClass(parent) && !parent.isInterface())
                addRelationship(sootClass.getName(),parent.getName());
            }
		}
		
		
		HashSet<String> visited = new HashSet<>();
        for(String node:targetClasses){
        	dfs(node,visited);
        }
		
		
	}

	public void avoidCollisionGetMethod(SootField field, String cName, SootClass sootClass) {
	    // Create a unique method name like "getClassNameFieldName"
	    String methodName = "get" + cName + field.getName();
	    SootMethod getMethod = new SootMethod(
	        methodName,
	        new ArrayList<>(),         // No parameters
	        field.getType(),          // Return type is the field's type
	        Modifier.PUBLIC           // Public non-static method
	    );

	    // Add the method to the class
	    sootClass.addMethod(getMethod);

	    // Create the method body
	    JimpleBody body = Jimple.v().newBody(getMethod);
	    getMethod.setActiveBody(body);
	    Chain<Unit> units = body.getUnits();
	    Chain<Local> locals = body.getLocals();

	    // 1. Define a local variable for 'this'
	    Local thisLocal = Jimple.v().newLocal("r0", sootClass.getType());
	    locals.add(thisLocal);
	    units.add(Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(sootClass.getType())));

	    // 2. Define a temporary local to hold the field value
	    Local fieldValue = Jimple.v().newLocal("fieldValue", field.getType());
	    locals.add(fieldValue);

	    // 3. Access the instance field and assign it to the temporary local
	    FieldRef fieldRef = Jimple.v().newInstanceFieldRef(thisLocal, field.makeRef());
	    AssignStmt assignField = Jimple.v().newAssignStmt(fieldValue, fieldRef);
	    units.add(assignField);

	    // 4. Return the temporary local
	    ReturnStmt returnStmt = Jimple.v().newReturnStmt(fieldValue);
	    units.add(returnStmt);

	    // Validate the body
//	    System.out.println("Generated body:\n" + body);
	    body.validate();
	}

	public void printStmtV2(SootClass sootClass) {
	    for (SootMethod method : sootClass.getMethods()) {
	        if (method.getName().startsWith("equals")) {
	            
	        JimpleBody body = (JimpleBody) method.retrieveActiveBody();
	        Chain<Unit> units = body.getUnits();
	        Unit start = units.getFirst();
	        for (Unit unit : units) {
	            Stmt stmt = (Stmt) unit;
	            if (stmt instanceof IdentityStmt) {
	                continue;
	            } else {
	                start = unit;
	                break;
	            }
	        }
//	        System.out.println(units.getFirst()); // Keeping this as-is for now (optional)

	        // --- Adding logic to write to a custom file ---
	        String outputFile = "/home/kushagra/MTP/mtp/Log/equalsunflow.log"; // Change this to your desired file path
	        String outputText = "equal";

	        // Create a local to hold the PrintWriter
	        Local writerLocal = Jimple.v().newLocal("writerLocal", RefType.v("java.io.PrintWriter"));
	        body.getLocals().add(writerLocal);

	        // Create FileWriter and PrintWriter instances
	        SootClass fileWriterClass = Scene.v().getSootClass("java.io.FileWriter");
	        SootMethodRef fileWriterConstructor = fileWriterClass.getMethod("void <init>(java.lang.String,boolean)").makeRef();
	        SootClass printWriterClass = Scene.v().getSootClass("java.io.PrintWriter");
	        SootMethodRef printWriterConstructor = printWriterClass.getMethod("void <init>(java.io.Writer)").makeRef();

	        // FileWriter with append mode (true)
	        Local fileWriterLocal = Jimple.v().newLocal("fileWriterLocal", RefType.v("java.io.FileWriter"));
	        body.getLocals().add(fileWriterLocal);
	        NewExpr fileWriterNew = Jimple.v().newNewExpr(RefType.v("java.io.FileWriter"));
	        AssignStmt fileWriterAssign = Jimple.v().newAssignStmt(fileWriterLocal, fileWriterNew);
	        InvokeExpr fileWriterInit = Jimple.v().newSpecialInvokeExpr(fileWriterLocal, fileWriterConstructor, 
	            StringConstant.v(outputFile), IntConstant.v(1)); // 1 = true for append
	        Stmt fileWriterInvoke = Jimple.v().newInvokeStmt(fileWriterInit);

	        // PrintWriter instantiation
	        NewExpr printWriterNew = Jimple.v().newNewExpr(RefType.v("java.io.PrintWriter"));
	        AssignStmt printWriterAssign = Jimple.v().newAssignStmt(writerLocal, printWriterNew);
	        InvokeExpr printWriterInit = Jimple.v().newSpecialInvokeExpr(writerLocal, printWriterConstructor, fileWriterLocal);
	        Stmt printWriterInvoke = Jimple.v().newInvokeStmt(printWriterInit);

	        // Call PrintWriter.println(String)
	        SootMethodRef printlnMethodRef = printWriterClass.getMethod("void println(java.lang.String)").makeRef();
	        InvokeExpr printlnExpr = Jimple.v().newVirtualInvokeExpr(writerLocal, printlnMethodRef, StringConstant.v(outputText));
	        Stmt printlnStmt = Jimple.v().newInvokeStmt(printlnExpr);

	        // Close the PrintWriter
	        SootMethodRef closeMethodRef = printWriterClass.getMethod("void close()").makeRef();
	        InvokeExpr closeExpr = Jimple.v().newVirtualInvokeExpr(writerLocal, closeMethodRef);
	        Stmt closeStmt = Jimple.v().newInvokeStmt(closeExpr);

	        // Insert statements before the start unit
	        units.insertBefore(fileWriterAssign, start);
	        units.insertBefore(fileWriterInvoke, start);
	        units.insertBefore(printWriterAssign, start);
	        units.insertBefore(printWriterInvoke, start);
	        units.insertBefore(printlnStmt, start);
	        units.insertBefore(closeStmt, start);
	    }
	   }
	}
	
	public void transformConstructorCalls(SootClass sootClass) {
	    for (SootMethod method : sootClass.getMethods()) {
	    	int flag=0;
	    	
	    	
	        if (!method.isConcrete()  ||
	            method.getName().contains("createObject") ||
	            method.getName().startsWith("SuperHashCode") ||
	            method.getName().startsWith("generateCustomHash") ||
	            method.getName().startsWith("<clinit>") ||
	            method.getName().startsWith("equals")) {
	            continue;
	        }
	        
	        
//	        if(method.hasActiveBody()==false) continue;
	        Body body =  method.retrieveActiveBody();
	        Chain<Unit> units = body.getUnits();
	        List<Object[]> insertions = new ArrayList<>(); // [stmt, insertBeforeUnit]
	        List<Unit> removals = new ArrayList<>();

	        for (Unit unit : new ArrayList<>(units)) {
	            if (!(unit instanceof InvokeStmt)) continue;
	            
	            InvokeStmt invokeStmt = (InvokeStmt) unit;
	            InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
	            
	            if (!(invokeExpr instanceof SpecialInvokeExpr)) continue;
	            
	            SpecialInvokeExpr specialInvokeExpr = (SpecialInvokeExpr) invokeExpr;
	            SootMethod calledMethod = specialInvokeExpr.getMethod();
	            SootClass declaringClass = calledMethod.getDeclaringClass();
	            Value base = specialInvokeExpr.getBase();
	            
	            if(constantClass.contains(declaringClass) && calledMethod.getName().equals("<init>")) {
	            	invokeCount++;
	            }

	            if (!calledMethod.getName().equals("<init>") || 
	                !constantClass.contains(declaringClass) || 
	                base.toString().equals("this")) {
	                continue;
	            }
	            count++;
	            flag=1;
	            Local instanceLocal = (Local) base;
	            List<Type> paramTypes = calledMethod.getParameterTypes();
	            String dummyCons = constructorMapping.get(declaringClass).get(calledMethod);

	            // Create static invoke expression
	            StaticInvokeExpr staticInvokeExpr = Jimple.v().newStaticInvokeExpr(
	                Scene.v().getSootClass(declaringClass.getName())
	                    .getMethod(dummyCons, paramTypes).makeRef(),
	                specialInvokeExpr.getArgs()
	            );
	            AssignStmt staticAssign = Jimple.v().newAssignStmt(instanceLocal, staticInvokeExpr);

	            // Find the corresponding NewExpr
	            Unit newExprUnit = findNewExprUnit(units, invokeStmt, instanceLocal);
	            if (newExprUnit == null) {
//	                System.err.println("Error: No NewExpr found for " + invokeStmt + " in " + method);
	                continue;
	            }

	            // Find dependent statements between NewExpr and constructor call
	            List<Unit> dependentStmts = findDependentStmts(units, newExprUnit, invokeStmt, instanceLocal);

	            // Insert static invoke at the position of the constructor call
	            Unit insertPoint = invokeStmt; // This will be replaced, so it's safe for the first insertion
	            insertions.add(new Object[]{staticAssign, insertPoint});
	            removals.add(newExprUnit);  // Remove NewExpr
	            removals.add(invokeStmt);   // Remove constructor call

	            // Apply the first transformation (static invoke insertion and removals)
	            applyTransformations(units, insertions, removals);

	            // Clear lists for the next phase
	            insertions.clear();
	            removals.clear();

	            // Now insert dependent statements AFTER the static invoke
	            Unit staticInvokeUnit = staticAssign; // The newly inserted static invoke statement
	            Unit nextUnit = units.getSuccOf(staticInvokeUnit); // Point after static invoke
	            if (nextUnit == null) nextUnit = units.getLast(); // If last unit, use it as reference
	            
	            for (Unit dependentStmt : dependentStmts) {
	                units.remove(dependentStmt); // Remove from original position
	                insertions.add(new Object[]{dependentStmt, nextUnit});
	            }

	            // Apply dependent statement insertions
	            applyTransformations(units, insertions, removals);

//	            System.out.println("Transformed " + method + ":\n" + body);
	            body.validate();
//	            if(flag==1)
//	            System.out.println(body);      
	           }
	    }
	}

	private Unit findNewExprUnit(Chain<Unit> units, Unit invokeStmt, Local instanceLocal) {
	    Unit currentUnit = units.getPredOf(invokeStmt);
	    while (currentUnit != null) {
	        if (currentUnit instanceof AssignStmt) {
	            AssignStmt assign = (AssignStmt) currentUnit;
	            if (assign.getRightOp() instanceof NewExpr && assign.getLeftOp().equals(instanceLocal)) {
	                return currentUnit;
	            }
	        }
	        currentUnit = units.getPredOf(currentUnit);
	    }
	    return null;
	}

	private List<Unit> findDependentStmts(Chain<Unit> units, Unit newExprUnit, Unit invokeStmt, Local instanceLocal) {
	    List<Unit> dependentStmts = new ArrayList<>();
	    Unit currentUnit = units.getSuccOf(newExprUnit);
	    
	    while (currentUnit != null && currentUnit != invokeStmt) {
	        if (currentUnit instanceof AssignStmt) {
	            AssignStmt assign = (AssignStmt) currentUnit;
	            if (assign.getRightOp().equals(instanceLocal)) {
	                dependentStmts.add(currentUnit);
	            }
	        }
	        currentUnit = units.getSuccOf(currentUnit);
	    }
	    return dependentStmts;
	}

	private void applyTransformations(Chain<Unit> units, List<Object[]> insertions, List<Unit> removals) {
	    // Apply insertions
	    for (Object[] insertion : insertions) {
	        if (!units.contains((Unit) insertion[0])) {
	            units.insertBefore((Unit) insertion[0], (Unit) insertion[1]);
	        }
	    }
	    
	    // Apply removals in reverse order
	    List<Unit> reversedRemovals = new ArrayList<>(removals);
	    Collections.reverse(reversedRemovals);
	    for (Unit unit : reversedRemovals) {
	        units.remove(unit);
	    }
	}
	
	public void overwriteEqualsMethod(String className){


		SootClass sootClass = Scene.v().loadClassAndSupport(className); // load the content of the class

		SootMethod equalsMethod = null;
		for (SootMethod method : sootClass.getMethods()) {
			if (method.getName().equals("equals") && method.getParameterCount() == 1 &&
					method.getParameterType(0).equals(RefType.v("java.lang.Object"))) {
//				System.out.println(method.retrieveActiveBody());
				equalsMethod = method;
				break;
			}
		}
		
		
		
		if(equalsMethod == null) {
			//    	List<> parameters = new ArrayList<>();
			equalsMethod = new SootMethod("equals", new ArrayList<>(), BooleanType.v(), Modifier.PUBLIC);
			sootClass.addMethod(equalsMethod);

			Type objectType = RefType.v("java.lang.Object");
			// Create a list of parameter types
			ArrayList<Type> parameterTypes = new ArrayList<>();
			parameterTypes.add(objectType);

			// Set parameter types for the method
			equalsMethod.setParameterTypes(parameterTypes);
		} 
		
		
//		if(equalsMethod.isConcrete()==false) return ;
		
		

		// Generate new body for equals method
		JimpleBody body = Jimple.v().newBody(equalsMethod);
		equalsMethod.setActiveBody(body);

		// Add code to equals method
		PatchingChain<Unit> units = body.getUnits();
		//        System.out.println(sootClass.getType()); // name of class
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
		
		
//		
//		
//		// --- Adding logic to write to a custom file ---
//        String outputFile = "/home/kushagra/MTP/mtp/Log/equal.log"; // Change this to your desired file path
//        String outputText = sootClass.toString()+" reuse";
//
//        // Create a local to hold the PrintWriter
//        Local writerLocal = Jimple.v().newLocal("writerLocal", RefType.v("java.io.PrintWriter"));
//        body.getLocals().add(writerLocal);
//
//        // Create FileWriter and PrintWriter instances
//        SootClass fileWriterClass = Scene.v().getSootClass("java.io.FileWriter");
//        SootMethodRef fileWriterConstructor = fileWriterClass.getMethod("void <init>(java.lang.String,boolean)").makeRef();
//        SootClass printWriterClass = Scene.v().getSootClass("java.io.PrintWriter");
//        SootMethodRef printWriterConstructor = printWriterClass.getMethod("void <init>(java.io.Writer)").makeRef();
//
//        // FileWriter with append mode (true)
//        Local fileWriterLocal = Jimple.v().newLocal("fileWriterLocal", RefType.v("java.io.FileWriter"));
//        body.getLocals().add(fileWriterLocal);
//        NewExpr fileWriterNew = Jimple.v().newNewExpr(RefType.v("java.io.FileWriter"));
//        AssignStmt fileWriterAssign = Jimple.v().newAssignStmt(fileWriterLocal, fileWriterNew);
//        InvokeExpr fileWriterInit = Jimple.v().newSpecialInvokeExpr(fileWriterLocal, fileWriterConstructor, 
//            StringConstant.v(outputFile), IntConstant.v(1)); // 1 = true for append
//        Stmt fileWriterInvoke = Jimple.v().newInvokeStmt(fileWriterInit);
//
//        // PrintWriter instantiation
//        NewExpr printWriterNew = Jimple.v().newNewExpr(RefType.v("java.io.PrintWriter"));
//        AssignStmt printWriterAssign = Jimple.v().newAssignStmt(writerLocal, printWriterNew);
//        InvokeExpr printWriterInit = Jimple.v().newSpecialInvokeExpr(writerLocal, printWriterConstructor, fileWriterLocal);
//        Stmt printWriterInvoke = Jimple.v().newInvokeStmt(printWriterInit);
//
//        // Call PrintWriter.println(String)
//        SootMethodRef printlnMethodRef = printWriterClass.getMethod("void println(java.lang.String)").makeRef();
//        InvokeExpr printlnExpr = Jimple.v().newVirtualInvokeExpr(writerLocal, printlnMethodRef, StringConstant.v(outputText));
//        Stmt printlnStmt = Jimple.v().newInvokeStmt(printlnExpr);
//
//        // Close the PrintWriter
//        SootMethodRef closeMethodRef = printWriterClass.getMethod("void close()").makeRef();
//        InvokeExpr closeExpr = Jimple.v().newVirtualInvokeExpr(writerLocal, closeMethodRef);
//        Stmt closeStmt = Jimple.v().newInvokeStmt(closeExpr);
//
//        // Insert statements before the start unit
//        units.add(fileWriterAssign);
//        units.add(fileWriterInvoke);
//        units.add(printWriterAssign);
//        units.add(printWriterInvoke);
//        units.add(printlnStmt);
//        units.add(closeStmt);
//		
		
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
		
//		System.out.println(body);
	}
		
	

	
	private void ProgramCreation(SootClass sootClass,String className)
	{
		int constructorCount = 1;
		
		HashMap<SootMethod,String> dummyMap = new HashMap<>();
//		System.out.println(sootClass);
		List<SootMethod> methods = new ArrayList<>();
//		System.out.println(methods);
		for(SootMethod sootMethod : sootClass.getMethods()){
			if(sootMethod.isConstructor()){
				methods.add(sootMethod);
			}
		}
		for(SootMethod sootMethod:methods){
			
			if(sootMethod.isConstructor()){
//				System.out.println(sootMethod.retrieveActiveBody());
				createDummyConstructor(sootMethod,sootClass,constructorCount,className);
				dummyMap.put(sootMethod,className+"dummyConstructor"+String.valueOf(constructorCount));
				constructorCount++;
//				System.out.println("creation");
			}
		}
		constructorMapping.put(sootClass, dummyMap);
		
	}

	private void createDummyConstructor(SootMethod sootMethod,SootClass sootClass,int constructorCount,String cName) {
		List<Type> parameterTypes = new ArrayList<>(sootMethod.getParameterTypes());
		
		SootMethod dummyConstructor = new SootMethod(
				cName+"dummyConstructor"+String.valueOf(constructorCount),
		        parameterTypes,
		        sootClass.getType(),
		        Modifier.PUBLIC | Modifier.STATIC
		);
		
		sootClass.addMethod(dummyConstructor);
		
		JimpleBody dummyConstructorBody = (JimpleBody)sootMethod.retrieveActiveBody().clone();
		dummyConstructor.setActiveBody(dummyConstructorBody);
		
		PatchingChain<Unit> dummyConstructorUnits = dummyConstructorBody.getUnits();
		
		HashSet<Local> localToThisRefMap = new HashSet<>();
		for(Unit unit:dummyConstructorBody.getUnits()) {
			Stmt stmt = (Stmt) unit;
			if (stmt instanceof IdentityStmt) { // Look for `l0 := @this: Entity;`
                IdentityStmt identityStmt = (IdentityStmt) stmt;
                if (identityStmt.getRightOp() instanceof ThisRef) {
                    localToThisRefMap.add((Local) identityStmt.getLeftOp());
                }
            }
			else if(stmt instanceof AssignStmt) {
				AssignStmt assignStmt = (AssignStmt) stmt;
				if(assignStmt.getRightOp() instanceof Local && localToThisRefMap.contains((Local)assignStmt.getRightOp())) {
					localToThisRefMap.add((Local) assignStmt.getLeftOp());
				}
			}
		}
		
		
		
//		System.out.println(dummyConstructor.retrieveActiveBody());
		
		List<Value> arguments = new ArrayList<>();
	    List<Type> argumentsType = new ArrayList<>();
	    HashMap<String,Local> LocalInfo = new HashMap<>();
	    
	    for(SootField sootfield:sootClass.getFields())
	    {
	    	if(sootfield.isStatic()) continue;
	    	
			Local temp = Jimple.v().newLocal("this_"+sootfield.getName(), sootfield.getType());
			arguments.add((Value)temp);
			argumentsType.add(sootfield.getType());
            dummyConstructorBody.getLocals().add(temp);
            LocalInfo.put("this_"+sootfield.getName(),temp);
	    }
	    
	    
	    Local hashV = Jimple.v().newLocal("hashV", IntType.v());
	    dummyConstructorBody.getLocals().add(hashV);
	    arguments.add((Value)hashV);
    	argumentsType.add(IntType.v());
    	
    	
    	
    	int x=1000;
    	
    	List<Unit> toReplace = new ArrayList<>();
    	Iterator<Unit> iterator = dummyConstructorUnits.snapshotIterator();
    	
    	 while (iterator.hasNext()) {
	        Unit unit = iterator.next();
    		Stmt stmt = (Stmt) unit;
    		
    		if(stmt instanceof AssignStmt) {
    			AssignStmt assignStmt = (AssignStmt) stmt;
	    		Value lhs = assignStmt.getLeftOp();
	    		Value rhs = assignStmt.getRightOp();
	    		
	    		if (lhs instanceof InstanceFieldRef ) {
	    			InstanceFieldRef instanceFieldRef = (InstanceFieldRef) lhs;
	    			String fieldName = instanceFieldRef.getField().getName();
	    			SootClass declaringClass = instanceFieldRef.getField().getDeclaringClass();
	    			if(declaringClass.equals(sootClass)) {
	    				Local temp = LocalInfo.get("this_"+fieldName);
	    				Stmt newAssignStmt = Jimple.v().newAssignStmt(temp,rhs );
	    				dummyConstructorUnits.insertBefore(newAssignStmt, unit);
	    				toReplace.add(unit);
	    			}
	    		}
	    		else if (rhs instanceof InstanceFieldRef ) {
	    			InstanceFieldRef instanceFieldRef = (InstanceFieldRef) rhs;
	    			String fieldName = instanceFieldRef.getField().getName();
	    			SootClass declaringClass = instanceFieldRef.getField().getDeclaringClass();
	    			if(declaringClass.equals(sootClass)){
	    				Local temp = LocalInfo.get("this_"+fieldName);
	    				Stmt newAssignStmt = Jimple.v().newAssignStmt(lhs,temp );
	    				dummyConstructorUnits.insertBefore(newAssignStmt, unit);
	    				toReplace.add(unit);
	    			}
	    		}
	    		
    		}
    		else if(stmt instanceof IdentityStmt) {
	    		IdentityStmt identityStmt = (IdentityStmt) unit;
	    		
	    		if(identityStmt.getLeftOp() instanceof Local && identityStmt.getRightOp() instanceof ThisRef) {
	    			toReplace.add(unit);
	    		}
	    		
	    	}
    		else if(stmt instanceof ReturnVoidStmt) {
    			
//    			// --- Adding logic to write to a custom file ---
//    			String outputFile = "/home/kushagra/MTP/mtp/Log/equal.log"; // Change this to your desired file path
//    			Local thisContents = LocalInfo.get("this_contents"); // Get the Local for this_contents (HashSet)
//
//    			// Create locals for identity hash code and its String representation
//    			Local hashCodeLocal = Jimple.v().newLocal("hashCodeLocal", IntType.v());
//    			dummyConstructorBody.getLocals().add(hashCodeLocal);
//    			Local stringLocal = Jimple.v().newLocal("stringLocal", RefType.v("java.lang.String"));
//    			dummyConstructorBody.getLocals().add(stringLocal);
//
//    			// Call System.identityHashCode(this_contents)
//    			SootClass systemClass = Scene.v().getSootClass("java.lang.System");
//    			SootMethodRef identityHashCodeRef = systemClass.getMethod("int identityHashCode(java.lang.Object)").makeRef();
//    			InvokeExpr hashCodeExpr = Jimple.v().newStaticInvokeExpr(identityHashCodeRef, thisContents);
//    			AssignStmt hashCodeAssign = Jimple.v().newAssignStmt(hashCodeLocal, hashCodeExpr);
//
//    			// Convert int to String using String.valueOf(int)
//    			SootClass stringClass = Scene.v().getSootClass("java.lang.String");
//    			SootMethodRef valueOfMethodRef = stringClass.getMethod("java.lang.String valueOf(int)").makeRef();
//    			InvokeExpr valueOfExpr = Jimple.v().newStaticInvokeExpr(valueOfMethodRef, hashCodeLocal);
//    			AssignStmt stringAssign = Jimple.v().newAssignStmt(stringLocal, valueOfExpr);
//
//    			// Create a local to hold the PrintWriter
//    			Local writerLocal = Jimple.v().newLocal("writerLocal", RefType.v("java.io.PrintWriter"));
//    			dummyConstructorBody.getLocals().add(writerLocal);
//
//    			// Create FileWriter and PrintWriter instances
//    			SootClass fileWriterClass = Scene.v().getSootClass("java.io.FileWriter");
//    			SootMethodRef fileWriterConstructor = fileWriterClass.getMethod("void <init>(java.lang.String,boolean)").makeRef();
//    			SootClass printWriterClass = Scene.v().getSootClass("java.io.PrintWriter");
//    			SootMethodRef printWriterConstructor = printWriterClass.getMethod("void <init>(java.io.Writer)").makeRef();
//
//    			// FileWriter with append mode (true)
//    			Local fileWriterLocal = Jimple.v().newLocal("fileWriterLocal", RefType.v("java.io.FileWriter"));
//    			dummyConstructorBody.getLocals().add(fileWriterLocal);
//    			NewExpr fileWriterNew = Jimple.v().newNewExpr(RefType.v("java.io.FileWriter"));
//    			AssignStmt fileWriterAssign = Jimple.v().newAssignStmt(fileWriterLocal, fileWriterNew);
//    			InvokeExpr fileWriterInit = Jimple.v().newSpecialInvokeExpr(fileWriterLocal, fileWriterConstructor, 
//    			    StringConstant.v(outputFile), IntConstant.v(1)); // 1 = true for append
//    			Stmt fileWriterInvoke = Jimple.v().newInvokeStmt(fileWriterInit);
//
//    			// PrintWriter instantiation
//    			NewExpr printWriterNew = Jimple.v().newNewExpr(RefType.v("java.io.PrintWriter"));
//    			AssignStmt printWriterAssign = Jimple.v().newAssignStmt(writerLocal, printWriterNew);
//    			InvokeExpr printWriterInit = Jimple.v().newSpecialInvokeExpr(writerLocal, printWriterConstructor, fileWriterLocal);
//    			Stmt printWriterInvoke = Jimple.v().newInvokeStmt(printWriterInit);
//
//    			// Call PrintWriter.println(String) with the identity hash code as a String
//    			SootMethodRef printlnMethodRef = printWriterClass.getMethod("void println(java.lang.String)").makeRef();
//    			InvokeExpr printlnExpr = Jimple.v().newVirtualInvokeExpr(writerLocal, printlnMethodRef, stringLocal);
//    			Stmt printlnStmt = Jimple.v().newInvokeStmt(printlnExpr);
//
//    			// Close the PrintWriter
//    			SootMethodRef closeMethodRef = printWriterClass.getMethod("void close()").makeRef();
//    			InvokeExpr closeExpr = Jimple.v().newVirtualInvokeExpr(writerLocal, closeMethodRef);
//    			Stmt closeStmt = Jimple.v().newInvokeStmt(closeExpr);
//
//    			// Insert statements before the specified unit
//    			dummyConstructorUnits.insertBefore(hashCodeAssign, unit); // Get identity hash code
//    			dummyConstructorUnits.insertBefore(stringAssign, unit);   // Convert to String
//    			dummyConstructorUnits.insertBefore(fileWriterAssign, unit);
//    			dummyConstructorUnits.insertBefore(fileWriterInvoke, unit);
//    			dummyConstructorUnits.insertBefore(printWriterAssign, unit);
//    			dummyConstructorUnits.insertBefore(printWriterInvoke, unit);
//    			dummyConstructorUnits.insertBefore(printlnStmt, unit);
//    			dummyConstructorUnits.insertBefore(closeStmt, unit);
    			createCreateObject(sootMethod,sootClass,constructorCount,argumentsType,cName);
    			SootMethodRef createObjectRef = Scene.v()
	    				.getSootClass(sootClass.toString())
	    				.getMethod(cName+"createObject"+String.valueOf(constructorCount), argumentsType)
	    				.makeRef();
    			
    			InvokeExpr invokeExpr = Jimple.v().newStaticInvokeExpr(createObjectRef, arguments);
    			
    			
    			Local temp = Jimple.v().newLocal("temp$"+x++, sootClass.getType());
	    		dummyConstructorBody.getLocals().add(temp);
	    		Local temp1 = Jimple.v().newLocal("ansObject", sootClass.getType());
	    		dummyConstructorBody.getLocals().add(temp1);
	    		AssignStmt newAssignStmt = Jimple.v().newAssignStmt(temp, invokeExpr);
	    		dummyConstructorUnits.insertBefore(newAssignStmt, unit);
	    		newAssignStmt = Jimple.v().newAssignStmt(temp1, temp);
	    		dummyConstructorUnits.insertBefore(newAssignStmt, unit);
	    		
	    		
	    		
	    	    
	    		
	    		
	    		ReturnStmt returnStmt = Jimple.v().newReturnStmt(temp1);
	    		dummyConstructorUnits.insertBefore(returnStmt, unit);
	    		toReplace.add(unit);
	    		
    		}
    		else if(stmt instanceof InvokeStmt) {
    			InvokeExpr invokeExpr = ((InvokeStmt) unit).getInvokeExpr();
    			
    			if(invokeExpr instanceof SpecialInvokeExpr){
    				
    				SpecialInvokeExpr specialInvoke = (SpecialInvokeExpr) invokeExpr;
	    			SootMethod invokedMethod = specialInvoke.getMethod();
                    SootClass declaringClass = invokedMethod.getDeclaringClass();
                    SootClass pClass = sootClass.getSuperclass();
                    Value base = specialInvoke.getBase();
                    if(invokedMethod.isConstructor()) {
//                    	System.out.println(stmt);
//                    	System.out.println(sootClass+"   +   "+pClass+"    +   "+declaringClass);
                    	
                    	if(localToThisRefMap.contains((Local)base)) {
                    		
                    		if(specialInvoke.getMethod().getSignature().equals("<java.lang.Object: void <init>()>")) {
                    			AssignStmt AssStmt = Jimple.v().newAssignStmt(hashV, IntConstant.v(0));
                        		dummyConstructorUnits.insertBefore(AssStmt, unit);
                        		toReplace.add(unit);
                    		}
                    		else {
                    			Local temp = Jimple.v().newLocal("obj", declaringClass.getType());
                        		dummyConstructorBody.getLocals().add(temp);
                        		Local temp1 = Jimple.v().newLocal("temp$"+x++, declaringClass.getType());
                                dummyConstructorBody.getLocals().add(temp1);
                                Stmt newObjStmt = Jimple.v().newAssignStmt(temp1,Jimple.v().newNewExpr(declaringClass.getType()));
                                dummyConstructorUnits.insertBefore(newObjStmt, unit);
                                
                                List<Value> dummyargu = new ArrayList<>(specialInvoke.getArgs());
                                List<Type> dummyType = new ArrayList<>(invokedMethod.getParameterTypes());
                                for(Type type:dummyType) {
                                	argumentsType.add(type);
                                }
                                
                                for(Value value:dummyargu){
                                	arguments.add(value);
                                }
                                
                                SpecialInvokeExpr specialInvokeExpr1 = Jimple.v().newSpecialInvokeExpr(temp1, invokedMethod.makeRef(), dummyargu);
                                InvokeStmt invokeStmt1 = Jimple.v().newInvokeStmt(specialInvokeExpr1);
                                dummyConstructorUnits.insertBefore(invokeStmt1,unit);
                                
                                AssignStmt assignStmt = Jimple.v().newAssignStmt(temp, temp1);
                                dummyConstructorUnits.insertBefore(assignStmt, unit);
                                
                                Local temp2 = Jimple.v().newLocal("temp$"+x++,IntType.v());
                                dummyConstructorBody.getLocals().add(temp2);
                                
                                SootMethodRef dummyConstRef = declaringClass.getMethod("int SuperHashCode()").makeRef();
                                InvokeExpr InvokeExpr = Jimple.v().newVirtualInvokeExpr(temp,dummyConstRef);
                                AssignStmt AssStmt = Jimple.v().newAssignStmt(temp2,InvokeExpr);
                                
                                dummyConstructorUnits.insertBefore(AssStmt, unit);
                                AssStmt = Jimple.v().newAssignStmt(hashV,temp2);
                                dummyConstructorUnits.insertBefore(AssStmt, unit);
                                toReplace.add(unit);
                    		}
                    	}
                    }
    			}
    		}
    	}
    	
    	for(int i=0;i<toReplace.size();++i)
        {
        	Unit oldStmt = toReplace.get(i);
        	dummyConstructorUnits.remove(oldStmt);
        }
    	
    	iterator = dummyConstructorUnits.snapshotIterator();

    	while (iterator.hasNext()) {
    		Unit unit = iterator.next();
    		Stmt stmt = (Stmt) unit;
    		if(stmt instanceof IdentityStmt) {
    			continue;
    		}
    		else {
    			for(SootField sootfield:sootClass.getFields())
    		    {
    		    	if(sootfield.isStatic()) continue;
    		    	
    				Local temp = LocalInfo.get("this_"+sootfield.getName());
    				AssignStmt aStmt;
    				if(isPrimitiveArray(temp.getType())) {
    					Type elementType = temp.getType();
    					if(elementType.equals(IntType.v())) aStmt = Jimple.v().newAssignStmt(temp, IntConstant.v(0));
    					else if(elementType.equals(FloatType.v())) aStmt = Jimple.v().newAssignStmt(temp, FloatConstant.v(0));
    					else if(elementType.equals(DoubleType.v())) aStmt = Jimple.v().newAssignStmt(temp, DoubleConstant.v(0));
    					else if(elementType.equals(BooleanType.v())) aStmt = Jimple.v().newAssignStmt(temp, IntConstant.v(0));
    					else if(elementType.equals(ByteType.v())) aStmt = Jimple.v().newAssignStmt(temp, IntConstant.v(0));
    					else if(elementType.equals(CharType.v())) aStmt = Jimple.v().newAssignStmt(temp, IntConstant.v(0));
    					else if(elementType.equals(LongType.v())) aStmt = Jimple.v().newAssignStmt(temp, LongConstant.v(0));
    					else aStmt = Jimple.v().newAssignStmt(temp, IntConstant.v(0));
    					
    				}
    				else {
    					 aStmt = Jimple.v().newAssignStmt(temp, NullConstant.v());
    				}
    				dummyConstructorUnits.insertBefore(aStmt, unit);
    		    }
    			break;
    		}
    	}
    	
    	
    	
//    	if(cName.equals("LegacyRegister")){
//    		
//    	}
//    	System.out.println(dummyConstructorBody);
    	
    	dummyConstructorBody.validate();
    	
    	
		
		
	}
	
	private void createCreateObjectV2(SootMethod sootMethod, SootClass sootClass, int constructorCount, List<Type> listOfParameter, String cName) {
	        SootClass Dummy = Scene.v().getSootClass("Dummy");
	        List<Type> HashFunctionParameterType = new ArrayList<>();
	        List<Local> HashFunParameter = new ArrayList<>();
	        List<Local> newConstparameter = new ArrayList<>();
	        List<Type> newConstInvokationType = new ArrayList<>();

	        String createObjectMethodName = cName + "createObject" + String.valueOf(constructorCount);
	        SootMethod createObjectMethod = new SootMethod(createObjectMethodName, listOfParameter, sootClass.getType(), Modifier.PUBLIC | Modifier.STATIC);
	        sootClass.addMethod(createObjectMethod);

	        JimpleBody body = Jimple.v().newBody(createObjectMethod);
	        createObjectMethod.setActiveBody(body);
	        PatchingChain<Unit> units = body.getUnits();

	        int k = 0;
	        for (SootField field : sootClass.getFields()) {
	            if (field.isStatic()) {
	                continue;
	            }
	            Local parameterLocal = Jimple.v().newLocal("this_" + field.getName(), listOfParameter.get(k));
	            body.getLocals().add(parameterLocal);
	            Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(listOfParameter.get(k), k));

	            HashFunctionParameterType.add(listOfParameter.get(k));
	            HashFunParameter.add(parameterLocal);
	            newConstparameter.add(parameterLocal);
	            newConstInvokationType.add(listOfParameter.get(k));

	            k++;
	            units.add(stmt);
	        }

	        SootClass parentClass = sootClass.getSuperclass();

	        if (true) {
	            Local parameterLocal = Jimple.v().newLocal("hashV", listOfParameter.get(k));
	            body.getLocals().add(parameterLocal);
	            Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(listOfParameter.get(k), k));

	            HashFunctionParameterType.add(listOfParameter.get(k));
	            HashFunParameter.add(parameterLocal);

	            k++;
	            units.add(stmt);
	        }

	        int x = 0;
	        while (k != listOfParameter.size()) {
	            Local parameterLocal = Jimple.v().newLocal("exp" + String.valueOf(x++), listOfParameter.get(k));
	            body.getLocals().add(parameterLocal);
	            Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(listOfParameter.get(k), k));

	            newConstparameter.add(parameterLocal);
	            newConstInvokationType.add(listOfParameter.get(k));

	            k++;
	            units.add(stmt);
	        }

	        for (int i = 0; i < constructorCount; ++i) {
	            Local temp = Jimple.v().newLocal("temp$10" + String.valueOf(i), Dummy.getType());
	            body.getLocals().add(temp);
	            AssignStmt assignStmt = Jimple.v().newAssignStmt(temp, NullConstant.v());
	            units.add(assignStmt);
	            newConstparameter.add(0, temp);
	            newConstInvokationType.add(0, Dummy.getType());
	        }

	        Local temp$0 = Jimple.v().newLocal("temp$0", IntType.v());
	        body.getLocals().add(temp$0);
	        SootMethodRef generateCustomHashRef = sootClass.getMethod("generateCustomHash", HashFunctionParameterType).makeRef();
	        InvokeExpr invokeExpr = Jimple.v().newStaticInvokeExpr(generateCustomHashRef, HashFunParameter);
	        AssignStmt assStmt = Jimple.v().newAssignStmt(temp$0, invokeExpr);
	        units.add(assStmt);

	        Local hashvalue = Jimple.v().newLocal("hashvalue", IntType.v());
	        body.getLocals().add(hashvalue);
	        assStmt = Jimple.v().newAssignStmt(hashvalue, temp$0);
	        units.add(assStmt);

	        SootField objectPoolField = sootClass.getFieldByName("object_pool");
	        Local temp$1 = Jimple.v().newLocal("temp$1", objectPoolField.getType());
	        body.getLocals().add(temp$1);
	        Stmt stmt = Jimple.v().newAssignStmt(temp$1, Jimple.v().newStaticFieldRef(objectPoolField.makeRef()));
	        units.add(stmt);

	        Local temp$2 = Jimple.v().newLocal("temp$2", Scene.v().getSootClass("java.lang.Integer").getType());
	        body.getLocals().add(temp$2);
	        SootClass _IntegerClass = Scene.v().getSootClass("java.lang.Integer");
	        SootMethodRef _IntegerValueOf = Scene.v().makeMethodRef(_IntegerClass, "valueOf", Arrays.asList(IntType.v()), RefType.v("java.lang.Integer"), true);
	        List<Local> list = new ArrayList<>();
	        list.add(hashvalue);
	        Value _Integerrvalue = Jimple.v().newStaticInvokeExpr(_IntegerValueOf, list);
	        stmt = Jimple.v().newAssignStmt(temp$2, _Integerrvalue);
	        units.add(stmt);

	        Local temp$3 = Jimple.v().newLocal("temp$3", BooleanType.v());
	        body.getLocals().add(temp$3);
	        SootMethodRef _MapContainsKey = Scene.v().makeMethodRef(
	            Scene.v().getSootClass("java.util.HashMap"), 
	            "containsKey", 
	            Arrays.asList(RefType.v("java.lang.Object")), 
	            BooleanType.v(), 
	            false
	        );
	        Value rvalueMapContainsKey = Jimple.v().newVirtualInvokeExpr(temp$1, _MapContainsKey, temp$2);
	        Stmt mapContainsKeyStmt = Jimple.v().newAssignStmt(temp$3, rvalueMapContainsKey);
	        units.add(mapContainsKeyStmt);

	        // --- Adding logic to write to custom.log ---
	        // Define the target for the GotoStmt (next statement after Reuse)
	        Local temp$8 = Jimple.v().newLocal("temp$8", sootClass.getType());
	        body.getLocals().add(temp$8);
	        Stmt newObjStmt = Jimple.v().newAssignStmt(temp$8, Jimple.v().newNewExpr(sootClass.getType()));

	        // File writing setup for custom.log
	        String outputFile = "/home/kushagra/MTP/mtp/Log/custom.log"; // Custom file path
	        SootClass fileWriterClass = Scene.v().getSootClass("java.io.FileWriter");
	        SootMethodRef fileWriterConstructor = fileWriterClass.getMethod("void <init>(java.lang.String,boolean)").makeRef();
	        SootClass printWriterClass = Scene.v().getSootClass("java.io.PrintWriter");
	        SootMethodRef printWriterConstructor = printWriterClass.getMethod("void <init>(java.io.Writer)").makeRef();
	        SootMethodRef printlnMethodRef = printWriterClass.getMethod("void println(java.lang.String)").makeRef();
	        SootMethodRef closeMethodRef = printWriterClass.getMethod("void close()").makeRef();

	        // Locals for "Reuse" branch
	        Local reuseFileWriterLocal = Jimple.v().newLocal("reuseFileWriter", RefType.v("java.io.FileWriter"));
	        Local reusePrintWriterLocal = Jimple.v().newLocal("reusePrintWriter", RefType.v("java.io.PrintWriter"));
	        body.getLocals().add(reuseFileWriterLocal);
	        body.getLocals().add(reusePrintWriterLocal);

	        // FileWriter and PrintWriter for "Reuse"
	        NewExpr reuseFileWriterNew = Jimple.v().newNewExpr(RefType.v("java.io.FileWriter"));
	        AssignStmt reuseFileWriterAssign = Jimple.v().newAssignStmt(reuseFileWriterLocal, reuseFileWriterNew);
	        InvokeExpr reuseFileWriterInit = Jimple.v().newSpecialInvokeExpr(reuseFileWriterLocal, fileWriterConstructor, 
	            StringConstant.v(outputFile), IntConstant.v(1)); // Append mode
	        Stmt reuseFileWriterInvoke = Jimple.v().newInvokeStmt(reuseFileWriterInit);

	        NewExpr reusePrintWriterNew = Jimple.v().newNewExpr(RefType.v("java.io.PrintWriter"));
	        AssignStmt reusePrintWriterAssign = Jimple.v().newAssignStmt(reusePrintWriterLocal, reusePrintWriterNew);
	        InvokeExpr reusePrintWriterInit = Jimple.v().newSpecialInvokeExpr(reusePrintWriterLocal, printWriterConstructor, reuseFileWriterLocal);
	        Stmt reusePrintWriterInvoke = Jimple.v().newInvokeStmt(reusePrintWriterInit);

	        InvokeExpr reusePrintlnExpr = Jimple.v().newVirtualInvokeExpr(reusePrintWriterLocal, printlnMethodRef, StringConstant.v(sootClass.toString()+" Reuse"));
	        Stmt reusePrintlnStmt = Jimple.v().newInvokeStmt(reusePrintlnExpr);
	        InvokeExpr reuseCloseExpr = Jimple.v().newVirtualInvokeExpr(reusePrintWriterLocal, closeMethodRef);
	        Stmt reuseCloseStmt = Jimple.v().newInvokeStmt(reuseCloseExpr);

	        // Locals for "Different" branch
	        Local diffFileWriterLocal = Jimple.v().newLocal("diffFileWriter", RefType.v("java.io.FileWriter"));
	        Local diffPrintWriterLocal = Jimple.v().newLocal("diffPrintWriter", RefType.v("java.io.PrintWriter"));
	        body.getLocals().add(diffFileWriterLocal);
	        body.getLocals().add(diffPrintWriterLocal);

	        // FileWriter and PrintWriter for "Different"
	        NewExpr diffFileWriterNew = Jimple.v().newNewExpr(RefType.v("java.io.FileWriter"));
	        AssignStmt diffFileWriterAssign = Jimple.v().newAssignStmt(diffFileWriterLocal, diffFileWriterNew);
	        InvokeExpr diffFileWriterInit = Jimple.v().newSpecialInvokeExpr(diffFileWriterLocal, fileWriterConstructor, 
	            StringConstant.v(outputFile), IntConstant.v(1)); // Append mode
	        Stmt diffFileWriterInvoke = Jimple.v().newInvokeStmt(diffFileWriterInit);

	        NewExpr diffPrintWriterNew = Jimple.v().newNewExpr(RefType.v("java.io.PrintWriter"));
	        AssignStmt diffPrintWriterAssign = Jimple.v().newAssignStmt(diffPrintWriterLocal, diffPrintWriterNew);
	        InvokeExpr diffPrintWriterInit = Jimple.v().newSpecialInvokeExpr(diffPrintWriterLocal, printWriterConstructor, diffFileWriterLocal);
	        Stmt diffPrintWriterInvoke = Jimple.v().newInvokeStmt(diffPrintWriterInit);

	        InvokeExpr diffPrintlnExpr = Jimple.v().newVirtualInvokeExpr(diffPrintWriterLocal, printlnMethodRef, StringConstant.v(sootClass.toString()+" Different"));
	        Stmt diffPrintlnStmt = Jimple.v().newInvokeStmt(diffPrintlnExpr);
	        InvokeExpr diffCloseExpr = Jimple.v().newVirtualInvokeExpr(diffPrintWriterLocal, closeMethodRef);
	        Stmt diffCloseStmt = Jimple.v().newInvokeStmt(diffCloseExpr);

	        // Add conditional logic: if temp$3 == true, write "Reuse", else write "Different"
	        EqExpr eqExprPrint = Jimple.v().newEqExpr(temp$3, IntConstant.v(1)); // temp$3 is true if containsKey returns true
	        IfStmt ifStmtForPrint = Jimple.v().newIfStmt(eqExprPrint, reuseFileWriterAssign);

	        // Insert the logic
	        units.add(ifStmtForPrint);           // If temp$3 == true, jump to reuseFileWriterAssign
	        // "Different" branch
	        units.add(diffFileWriterAssign);
	        units.add(diffFileWriterInvoke);
	        units.add(diffPrintWriterAssign);
	        units.add(diffPrintWriterInvoke);
	        units.add(diffPrintlnStmt);
	        units.add(diffCloseStmt);
	        units.add(Jimple.v().newGotoStmt(newObjStmt)); // Skip "Reuse" and go to newObjStmt
	        // "Reuse" branch
	        units.add(reuseFileWriterAssign);
	        units.add(reuseFileWriterInvoke);
	        units.add(reusePrintWriterAssign);
	        units.add(reusePrintWriterInvoke);
	        units.add(reusePrintlnStmt);
	        units.add(reuseCloseStmt);
	        // --- End of file writing logic ---

	        EqExpr eqExpr = Jimple.v().newEqExpr(temp$3, IntConstant.v(0));
	        IfStmt ifStmt = Jimple.v().newIfStmt(eqExpr, newObjStmt);
	        units.add(ifStmt);

	        Local temp$4 = Jimple.v().newLocal("temp$4", objectPoolField.getType());
	        body.getLocals().add(temp$4);
	        stmt = Jimple.v().newAssignStmt(temp$4, Jimple.v().newStaticFieldRef(objectPoolField.makeRef()));
	        units.add(stmt);

	        Local temp$5 = Jimple.v().newLocal("temp$5", Scene.v().getSootClass("java.lang.Integer").getType());
	        body.getLocals().add(temp$5);
	        _IntegerClass = Scene.v().getSootClass("java.lang.Integer");
	        _IntegerValueOf = Scene.v().makeMethodRef(_IntegerClass, "valueOf", Arrays.asList(IntType.v()), RefType.v("java.lang.Integer"), true);
	        list = new ArrayList<>();
	        list.add(hashvalue);
	        _Integerrvalue = Jimple.v().newStaticInvokeExpr(_IntegerValueOf, list);
	        stmt = Jimple.v().newAssignStmt(temp$5, _Integerrvalue);
	        units.add(stmt);

	        Local temp$6 = Jimple.v().newLocal("temp$6", Scene.v().getSootClass("java.lang.Object").getType());
	        body.getLocals().add(temp$6);
	        SootMethodRef _MapGet = Scene.v().makeMethodRef(
	            Scene.v().getSootClass("java.util.HashMap"), 
	            "get", 
	            Arrays.asList(RefType.v("java.lang.Object")), 
	            RefType.v("java.lang.Object"), 
	            false
	        );
	        Value rvalueMapGet = Jimple.v().newVirtualInvokeExpr(temp$4, _MapGet, temp$5);
	        Stmt mapGetStmt = Jimple.v().newAssignStmt(temp$6, rvalueMapGet);
	        units.add(mapGetStmt);

	        Local temp$7 = Jimple.v().newLocal("temp$7", RefType.v(sootClass.toString()));
	        body.getLocals().add(temp$7);
	        units.add(Jimple.v().newAssignStmt(temp$7, Jimple.v().newCastExpr(temp$6, RefType.v(sootClass.toString()))));

	        Local ansObject = Jimple.v().newLocal("ansObject", Scene.v().getSootClass(sootClass.toString()).getType());
	        body.getLocals().add(ansObject);
	        AssignStmt assignStmt = Jimple.v().newAssignStmt(ansObject, temp$7);
	        units.add(assignStmt);

	        Stmt returnStmt = Jimple.v().newReturnStmt(ansObject);
	        units.add(returnStmt);

	        units.add(newObjStmt);

	        createNewConstructor(sootClass, newConstInvokationType, constructorCount);

	        SootMethodRef initMethodRef = Scene.v().makeConstructorRef(sootClass, newConstInvokationType);
	        Stmt invokeInitStmt = Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(temp$8, initMethodRef, newConstparameter));
	        units.add(invokeInitStmt);

	        assignStmt = Jimple.v().newAssignStmt(ansObject, temp$8);
	        units.add(assignStmt);

	        Local temp$9 = Jimple.v().newLocal("temp$9", objectPoolField.getType());
	        body.getLocals().add(temp$9);
	        stmt = Jimple.v().newAssignStmt(temp$9, Jimple.v().newStaticFieldRef(objectPoolField.makeRef()));
	        units.add(stmt);

	        Local temp$10 = Jimple.v().newLocal("temp$10", Scene.v().getSootClass("java.lang.Integer").getType());
	        body.getLocals().add(temp$10);
	        _IntegerClass = Scene.v().getSootClass("java.lang.Integer");
	        _IntegerValueOf = Scene.v().makeMethodRef(_IntegerClass, "valueOf", Arrays.asList(IntType.v()), RefType.v("java.lang.Integer"), true);
	        list = new ArrayList<>();
	        list.add(hashvalue);
	        _Integerrvalue = Jimple.v().newStaticInvokeExpr(_IntegerValueOf, list);
	        stmt = Jimple.v().newAssignStmt(temp$10, _Integerrvalue);
	        units.add(stmt);

	        Local temp$11 = Jimple.v().newLocal("temp$11", Scene.v().getSootClass("java.lang.Object").getType());
	        body.getLocals().add(temp$11);

	        SootMethodRef _MapPut = Scene.v().makeMethodRef(
	            Scene.v().getSootClass("java.util.HashMap"), 
	            "put", 
	            Arrays.asList(RefType.v("java.lang.Object"), RefType.v("java.lang.Object")), 
	            RefType.v("java.lang.Object"), 
	            false
	        );
	        ArrayList<Value> values = new ArrayList<>();
	        values.add(temp$10);
	        values.add(ansObject);
	        VirtualInvokeExpr rvalueMapPut = Jimple.v().newVirtualInvokeExpr(temp$9, _MapPut, values);

	        AssignStmt mapPutStmt = Jimple.v().newAssignStmt(temp$11, rvalueMapPut);
	        units.add(mapPutStmt);

	        returnStmt = Jimple.v().newReturnStmt(ansObject);
	        units.add(returnStmt);

	        body.validate();
	        
	        // System.out.println(body); // Commented out as in your original code
	    }
	


	private void createCreateObject(SootMethod sootMethod,SootClass sootClass,int constructorCount, List<Type> listOfParameter,String cName)
{
	SootClass Dummy = Scene.v().getSootClass("Dummy");
	List<Type> HashFunctionParameterType = new ArrayList<>();
	List<Local> HashFunParameter = new ArrayList<>();
	List<Local> newConstparameter = new ArrayList<>();
	List<Type> newConstInvokationType = new ArrayList<>();




	String createObjectMethodName = cName+"createObject"+String.valueOf(constructorCount);
	SootMethod createObjectMethod = new SootMethod(createObjectMethodName, listOfParameter, sootClass.getType() , Modifier.PUBLIC | Modifier.STATIC);
	sootClass.addMethod(createObjectMethod);


	JimpleBody body = Jimple.v().newBody(createObjectMethod);
	createObjectMethod.setActiveBody(body);
	PatchingChain<Unit> units = body.getUnits();


	int k = 0;
	for(SootField field: sootClass.getFields()) {
		if (field.isStatic()) {
			continue;
		}
		Local parameterLocal = Jimple.v().newLocal("this_"+field.getName(), listOfParameter.get(k));
		body.getLocals().add(parameterLocal);
		Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(listOfParameter.get(k), k));

		HashFunctionParameterType.add(listOfParameter.get(k));
		HashFunParameter.add(parameterLocal);
		newConstparameter.add(parameterLocal);
		newConstInvokationType.add(listOfParameter.get(k));

		k++;
		units.add(stmt);	
	}


	SootClass parentClass = sootClass.getSuperclass();

	if(true)
	{
		Local parameterLocal = Jimple.v().newLocal("hashV", listOfParameter.get(k));
		body.getLocals().add(parameterLocal);
		Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(listOfParameter.get(k), k));

		HashFunctionParameterType.add(listOfParameter.get(k));
		HashFunParameter.add(parameterLocal);

		k++;
		units.add(stmt);	
	}

	int x = 0;
	while(k!=listOfParameter.size())
	{
		Local parameterLocal = Jimple.v().newLocal("exp"+String.valueOf(x++), listOfParameter.get(k));
		body.getLocals().add(parameterLocal);
		Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(listOfParameter.get(k), k));

		newConstparameter.add(parameterLocal);
		newConstInvokationType.add(listOfParameter.get(k));

		k++;
		units.add(stmt);
	}


	for(int i=0;i<constructorCount;++i)
	{
		Local temp = Jimple.v().newLocal("temp$10"+String.valueOf(i), Dummy.getType());
		body.getLocals().add(temp);
		AssignStmt assignStmt = Jimple.v().newAssignStmt(temp, NullConstant.v());
		units.add(assignStmt);
		newConstparameter.add(0,temp);
		newConstInvokationType.add(0,Dummy.getType());
	}


	Local temp$0 = Jimple.v().newLocal("temp$0", IntType.v());
	body.getLocals().add(temp$0);
	SootMethodRef generateCustomHashRef = sootClass.getMethod("generateCustomHash", HashFunctionParameterType).makeRef();
	InvokeExpr invokeExpr = Jimple.v().newStaticInvokeExpr(generateCustomHashRef, HashFunParameter);
	AssignStmt assStmt = Jimple.v().newAssignStmt(temp$0, invokeExpr);
	units.add(assStmt); 

	// Define hashvalue and assign its value
	Local hashvalue = Jimple.v().newLocal("hashvalue", IntType.v());
	body.getLocals().add(hashvalue);
	assStmt = Jimple.v().newAssignStmt(hashvalue, temp$0); // Assuming temp$0 is defined elsewhere
	units.add(assStmt);

//	// --- Adding logic to write to a custom file ---
//	String outputFile = "/home/kushagra/MTP/mtp/Log/HashValue.log"; // Change this to your desired file path
//
//	// Create a local to hold the String representation of hashvalue
//	Local stringLocal = Jimple.v().newLocal("stringLocal", RefType.v("java.lang.String"));
//	body.getLocals().add(stringLocal);
//
//	// Convert hashvalue (int) to String using String.valueOf(int)
//	SootClass stringClass = Scene.v().getSootClass("java.lang.String");
//	SootMethodRef valueOfMethodRef = stringClass.getMethod("java.lang.String valueOf(int)").makeRef();
//	InvokeExpr valueOfExpr = Jimple.v().newStaticInvokeExpr(valueOfMethodRef, hashvalue);
//	AssignStmt stringAssign = Jimple.v().newAssignStmt(stringLocal, valueOfExpr);
//
//	// Create a local to hold the PrintWriter
//	Local writerLocal = Jimple.v().newLocal("writerLocal", RefType.v("java.io.PrintWriter"));
//	body.getLocals().add(writerLocal);
//
//	// Create FileWriter and PrintWriter instances
//	SootClass fileWriterClass = Scene.v().getSootClass("java.io.FileWriter");
//	SootMethodRef fileWriterConstructor = fileWriterClass.getMethod("void <init>(java.lang.String,boolean)").makeRef();
//	SootClass printWriterClass = Scene.v().getSootClass("java.io.PrintWriter");
//	SootMethodRef printWriterConstructor = printWriterClass.getMethod("void <init>(java.io.Writer)").makeRef();
//
//	// FileWriter with append mode (true)
//	Local fileWriterLocal = Jimple.v().newLocal("fileWriterLocal", RefType.v("java.io.FileWriter"));
//	body.getLocals().add(fileWriterLocal);
//	NewExpr fileWriterNew = Jimple.v().newNewExpr(RefType.v("java.io.FileWriter"));
//	AssignStmt fileWriterAssign = Jimple.v().newAssignStmt(fileWriterLocal, fileWriterNew);
//	InvokeExpr fileWriterInit = Jimple.v().newSpecialInvokeExpr(fileWriterLocal, fileWriterConstructor, 
//	    StringConstant.v(outputFile), IntConstant.v(1)); // 1 = true for append
//	Stmt fileWriterInvoke = Jimple.v().newInvokeStmt(fileWriterInit);
//
//	// PrintWriter instantiation
//	NewExpr printWriterNew = Jimple.v().newNewExpr(RefType.v("java.io.PrintWriter"));
//	AssignStmt printWriterAssign = Jimple.v().newAssignStmt(writerLocal, printWriterNew);
//	InvokeExpr printWriterInit = Jimple.v().newSpecialInvokeExpr(writerLocal, printWriterConstructor, fileWriterLocal);
//	Stmt printWriterInvoke = Jimple.v().newInvokeStmt(printWriterInit);
//
//	// Call PrintWriter.println(String) with the String representation of hashvalue
//	SootMethodRef printlnMethodRef = printWriterClass.getMethod("void println(java.lang.String)").makeRef();
//	InvokeExpr printlnExpr = Jimple.v().newVirtualInvokeExpr(writerLocal, printlnMethodRef, stringLocal); // Use stringLocal, not a StringConstant
//	Stmt printlnStmt = Jimple.v().newInvokeStmt(printlnExpr);
//
//	// Close the PrintWriter
//	SootMethodRef closeMethodRef = printWriterClass.getMethod("void close()").makeRef();
//	InvokeExpr closeExpr = Jimple.v().newVirtualInvokeExpr(writerLocal, closeMethodRef);
//	Stmt closeStmt = Jimple.v().newInvokeStmt(closeExpr);
//
//	// Insert statements into the units chain
//	units.add(stringAssign); // Convert hashvalue to String
//	units.add(fileWriterAssign);
//	units.add(fileWriterInvoke);
//	units.add(printWriterAssign);
//	units.add(printWriterInvoke);
//	units.add(printlnStmt);
//	units.add(closeStmt);
	
	
	
	

	SootField objectPoolField = sootClass.getFieldByName("object_pool");
	Local temp$1 = Jimple.v().newLocal("temp$1", objectPoolField.getType());
	body.getLocals().add(temp$1);
	Stmt stmt = Jimple.v().newAssignStmt(temp$1, Jimple.v().newStaticFieldRef(objectPoolField.makeRef()));
	units.add(stmt);

	Local temp$2 = Jimple.v().newLocal("temp$2", Scene.v().getSootClass("java.lang.Integer").getType());
	body.getLocals().add(temp$2);
	SootClass _IntegerClass = Scene.v().getSootClass("java.lang.Integer");
	SootMethodRef _IntegerValueOf = Scene.v().makeMethodRef(_IntegerClass, "valueOf", Arrays.asList(IntType.v()), RefType.v("java.lang.Integer"), true);
	List<Local> list = new ArrayList<>();
	list.add(hashvalue);
	Value _Integerrvalue = Jimple.v().newStaticInvokeExpr(_IntegerValueOf, list);
	stmt = Jimple.v().newAssignStmt(temp$2, _Integerrvalue);
	units.add(stmt);

	Local temp$3 = Jimple.v().newLocal("temp$3", BooleanType.v());
	body.getLocals().add(temp$3);
	SootMethodRef _MapContainsKey = Scene.v().makeMethodRef(Scene.v().getSootClass("java.util.HashMap"),"containsKey",Arrays.asList(RefType.v("java.lang.Object")), BooleanType.v(), false);
	Value rvalueMapContainsKey = Jimple.v().newVirtualInvokeExpr(temp$1, _MapContainsKey, temp$2);
	Stmt mapContainsKeyStmt = Jimple.v().newAssignStmt(temp$3, rvalueMapContainsKey);
	units.add(mapContainsKeyStmt);

	Local temp$8 = Jimple.v().newLocal("temp$8",sootClass.getType());
	body.getLocals().add(temp$8);
	Stmt newObjStmt = Jimple.v().newAssignStmt(temp$8,Jimple.v().newNewExpr(sootClass.getType()));

	EqExpr eqExpr = Jimple.v().newEqExpr(temp$3, IntConstant.v(0));
	IfStmt ifStmt = Jimple.v().newIfStmt(eqExpr, newObjStmt);
	units.add(ifStmt);


	Local temp$4 = Jimple.v().newLocal("temp$4", objectPoolField.getType());
	body.getLocals().add(temp$4);
	stmt = Jimple.v().newAssignStmt(temp$4, Jimple.v().newStaticFieldRef(objectPoolField.makeRef()));
	units.add(stmt);

	Local temp$5 = Jimple.v().newLocal("temp$5", Scene.v().getSootClass("java.lang.Integer").getType());
	body.getLocals().add(temp$5);
	_IntegerClass = Scene.v().getSootClass("java.lang.Integer");
	_IntegerValueOf = Scene.v().makeMethodRef(_IntegerClass, "valueOf", Arrays.asList(IntType.v()), RefType.v("java.lang.Integer"), true);
	list = new ArrayList<>();
	list.add(hashvalue);
	_Integerrvalue = Jimple.v().newStaticInvokeExpr(_IntegerValueOf, list);
	stmt = Jimple.v().newAssignStmt(temp$5, _Integerrvalue);
	units.add(stmt);

	Local temp$6 = Jimple.v().newLocal("temp$6", Scene.v().getSootClass("java.lang.Object").getType());
	body.getLocals().add(temp$6);
	SootMethodRef _MapGet = Scene.v().makeMethodRef(Scene.v().getSootClass("java.util.HashMap"),"get",Arrays.asList(RefType.v("java.lang.Object")), RefType.v("java.lang.Object"), false);
	Value rvalueMapGet = Jimple.v().newVirtualInvokeExpr(temp$4, _MapGet, temp$5);
	Stmt mapGetStmt = Jimple.v().newAssignStmt(temp$6, rvalueMapGet);
	units.add(mapGetStmt);

	Local temp$7 = Jimple.v().newLocal("temp$7", RefType.v(sootClass.toString()));
	body.getLocals().add(temp$7);
	units.add(Jimple.v().newAssignStmt(temp$7, Jimple.v().newCastExpr(temp$6, RefType.v(sootClass.toString()))));


	Local ansObject = Jimple.v().newLocal("ansObject",Scene.v().getSootClass(sootClass.toString()).getType());
	body.getLocals().add(ansObject);
	AssignStmt assignStmt = Jimple.v().newAssignStmt(ansObject, temp$7);
	units.add(assignStmt);

	Stmt returnStmt  = Jimple.v().newReturnStmt(ansObject);
	units.add(returnStmt);


	units.add(newObjStmt);


	//System.out.println(sootClass.getFieldCount());
	createNewConstructor(sootClass,newConstInvokationType,constructorCount);

	SootMethodRef initMethodRef = Scene.v().makeConstructorRef(sootClass, newConstInvokationType);
	Stmt invokeInitStmt = Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(temp$8, initMethodRef, newConstparameter));
	units.add(invokeInitStmt);


	assignStmt = Jimple.v().newAssignStmt(ansObject, temp$8);
	units.add(assignStmt);

	Local temp$9 = Jimple.v().newLocal("temp$9", objectPoolField.getType());
	body.getLocals().add(temp$9);
	stmt = Jimple.v().newAssignStmt(temp$9, Jimple.v().newStaticFieldRef(objectPoolField.makeRef()));
	units.add(stmt);

	Local temp$10 = Jimple.v().newLocal("temp$10", Scene.v().getSootClass("java.lang.Integer").getType());
	body.getLocals().add(temp$10);
	_IntegerClass = Scene.v().getSootClass("java.lang.Integer");
	_IntegerValueOf = Scene.v().makeMethodRef(_IntegerClass, "valueOf", Arrays.asList(IntType.v()), RefType.v("java.lang.Integer"), true);
	list = new ArrayList<>();
	list.add(hashvalue);
	_Integerrvalue = Jimple.v().newStaticInvokeExpr(_IntegerValueOf, list);
	stmt = Jimple.v().newAssignStmt(temp$10, _Integerrvalue);
	units.add(stmt);


	Local temp$11 = Jimple.v().newLocal("temp$11", Scene.v().getSootClass("java.lang.Object").getType());
	body.getLocals().add(temp$11);

	SootMethodRef _MapPut = Scene.v().makeMethodRef(Scene.v().getSootClass("java.util.HashMap"),"put",Arrays.asList(RefType.v("java.lang.Object"), RefType.v("java.lang.Object")), RefType.v("java.lang.Object"), false);
	ArrayList values = new ArrayList<>();
	values.add(temp$10);
	values.add(ansObject);
	VirtualInvokeExpr rvalueMapPut = Jimple.v().newVirtualInvokeExpr(temp$9, _MapPut, values);

	AssignStmt mapPutStmt = Jimple.v().newAssignStmt(temp$11, rvalueMapPut);
	units.add(mapPutStmt);




	returnStmt  = Jimple.v().newReturnStmt(ansObject);
	units.add(returnStmt);
	//if(cName.equals("LegacyRegister")){
	//System.out.println(body);
	//
	//}

	body.validate();
}
	

	private void createNewConstructor(SootClass sootClass,List<Type> argumentType,int constructorCount) {
//		System.out.println("-------------------------------------------");
		String MethodName = "<init>";
		SootMethod createObjectMethod = new SootMethod(MethodName, argumentType, VoidType.v() , Modifier.PUBLIC );
		sootClass.addMethod(createObjectMethod);
		
		JimpleBody body = Jimple.v().newBody(createObjectMethod);
		createObjectMethod.setActiveBody(body);
		PatchingChain<Unit> units = body.getUnits();
		
		Local thisLocal = Jimple.v().newLocal("this", sootClass.getType());
	    body.getLocals().add(thisLocal);
	    units.add(Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(sootClass.getType())));
		
		int k = 0;
		for(k=0;k<constructorCount;++k)
		{
			Local parameterLocal = Jimple.v().newLocal("dummy"+String.valueOf(k+1), argumentType.get(k));
			body.getLocals().add(parameterLocal);
			Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(argumentType.get(k), k));
			units.add(stmt);
		}
		for(SootField field: sootClass.getFields()) {
			if (field.isStatic()) {
				continue;
			}
			Local parameterLocal = Jimple.v().newLocal("this_"+field.getName(), argumentType.get(k));
			body.getLocals().add(parameterLocal);
			Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(argumentType.get(k), k));
			k++;
			units.add(stmt);	
		}
		
		SootClass parentClass = sootClass.getSuperclass();

		List<Type> superType = new ArrayList<>();
		List<Local> superArgs = new ArrayList<>();
		int idx=1;
		if(!isJDKClass(parentClass))
		{
			while(k!=argumentType.size())
			{
				superType.add(argumentType.get(k));
				Local parameterLocal = Jimple.v().newLocal("exp"+String.valueOf(idx), argumentType.get(k));
				body.getLocals().add(parameterLocal);
				Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(argumentType.get(k), k));
				k++;
				idx++;
				superArgs.add(parameterLocal);
				units.add(stmt);
			}
		}
		
		
		
		
		
//	    System.out.println(superType+" "+superArgs + " "+sootClass+" "+parentClass);
		if(!isJDKClass(parentClass) && superType.size()>0)
		{
	        SootMethodRef generateCustomHashRef = parentClass.getMethod("<init>", superType).makeRef();
			InvokeExpr invokeExpr = Jimple.v().newSpecialInvokeExpr(thisLocal,generateCustomHashRef,superArgs);
//			System.out.println(superType+" "+superArgs + " "+generateCustomHashRef);
			InvokeStmt invokeStmt = Jimple.v().newInvokeStmt(invokeExpr);
			units.add(invokeStmt);
		}
		else if(!isJDKClass(parentClass) && superType.size()==0)
		{
			SootMethodRef generateCustomHashRef = parentClass.getMethod("<init>", Collections.emptyList()).makeRef();
			InvokeExpr invokeExpr = Jimple.v().newSpecialInvokeExpr(thisLocal,generateCustomHashRef,Collections.emptyList());
//			System.out.println(superType+" "+superArgs + " "+generateCustomHashRef);
			InvokeStmt invokeStmt = Jimple.v().newInvokeStmt(invokeExpr);
			units.add(invokeStmt);
		}
		else
		{
			SootClass objectClass = Scene.v().getSootClass("java.lang.Object");
	        SootMethod objectInit = objectClass.getMethod("void <init>()");
	        SpecialInvokeExpr specialInvokeExpr = Jimple.v().newSpecialInvokeExpr(thisLocal, objectInit.makeRef());
	        InvokeStmt invokeStmt = Jimple.v().newInvokeStmt(specialInvokeExpr);
	        units.add(invokeStmt);
		}
		
		k = constructorCount;
		for(SootField field: sootClass.getFields()) {
			if (field.isStatic()) {
				continue;
			}
			InstanceFieldRef fieldRef = Jimple.v().newInstanceFieldRef(thisLocal, field.makeRef());
			AssignStmt assignStmt = Jimple.v().newAssignStmt(fieldRef, body.getParameterLocal(k));
			k++;
			units.add(assignStmt);
		}
		
		ReturnVoidStmt returnStmt =  Jimple.v().newReturnVoidStmt();	
		units.add(returnStmt);
		
		
		
		
		
//		System.out.println(body);
		body.validate();
		
		
	}
	
	private SootMethod createHashVfunction(SootClass targetClass) {
	    // Create SuperHashCode as an instance method (remove STATIC)
//	    SootMethod method = new SootMethod(
//	        "SuperHashCode",
//	        new ArrayList<>(),         // No parameters
//	        IntType.v(),              // Return type: int
//	        Modifier.PUBLIC           // Public, non-static
//	    );
		
		
		SootMethod method = targetClass.getMethod("int SuperHashCode()");

	    JimpleBody body = Jimple.v().newBody(method);
	    method.setActiveBody(body);
	    Chain<Unit> units = body.getUnits();

	    // Count non-static fields and check superclass
	    int ctr = 0;
	    for (SootField f : targetClass.getFields()) {
	        if (!f.isStatic()) ctr++;
	    }

	    SootClass parentClass = targetClass.getSuperclass();
	    if (!isJDKClass(parentClass)) {
	        ctr++;
	    }

	    int arrayIndex = 0;
	    if (ctr == 0) {
	        // No fields or superclass contribution, return 0
	    	
	    	Local thisLocal = Jimple.v().newLocal("this", targetClass.getType());
	        body.getLocals().add(thisLocal);
	        units.add(Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(targetClass.getType())));
	        
	        Local temp0 = Jimple.v().newLocal("temp$" + String.valueOf(arrayIndex++), IntType.v());
	        body.getLocals().add(temp0);
	        AssignStmt assignStmt = Jimple.v().newAssignStmt(temp0, IntConstant.v(0));
	        units.add(assignStmt);
	        units.add(Jimple.v().newReturnStmt(temp0));
	    } else {
	        // Instance method: declare 'this'
	        Local thisLocal = Jimple.v().newLocal("this", targetClass.getType());
	        body.getLocals().add(thisLocal);
	        Stmt stmt = Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(targetClass.getType()));
	        units.add(stmt);

	        // Create array to hold hash components
	        Local temp0 = Jimple.v().newLocal("temp$" + String.valueOf(arrayIndex++), ArrayType.v(RefType.v("java.lang.Object"), 1));
	        body.getLocals().add(temp0);
	        units.add(Jimple.v().newAssignStmt(temp0, Jimple.v().newNewArrayExpr(RefType.v("java.lang.Object"), IntConstant.v(ctr))));

	        int Index = 0;
	        if (!isJDKClass(parentClass)) {
	            Local temp1 = Jimple.v().newLocal("temp$" + String.valueOf(arrayIndex++), IntType.v());
	            body.getLocals().add(temp1);
	            SootMethod hashCodeMethod = parentClass.getMethod("int SuperHashCode()");
	            SpecialInvokeExpr specialInvokeExpr = Jimple.v().newSpecialInvokeExpr(thisLocal, hashCodeMethod.makeRef());
	            AssignStmt assignStmt = Jimple.v().newAssignStmt(temp1, specialInvokeExpr);
	            units.add(assignStmt);

	            Local temp2 = Jimple.v().newLocal("temp$" + (arrayIndex++), RefType.v("java.lang.Integer"));
	            body.getLocals().add(temp2);
	            units.add(Jimple.v().newAssignStmt(temp2, Jimple.v().newStaticInvokeExpr(
	                Scene.v().getMethod("<java.lang.Integer: java.lang.Integer valueOf(int)>").makeRef(), temp1
	            )));
	            units.add(Jimple.v().newAssignStmt(Jimple.v().newArrayRef(temp0, IntConstant.v(Index++)), temp2));
	        }

	        for (SootField field : targetClass.getFields()) {
	            if (field.isStatic()) continue;

	            Local tempLocal = Jimple.v().newLocal("temp$" + String.valueOf(arrayIndex++), field.getType());
	            body.getLocals().add(tempLocal);
	            FieldRef fieldRef = Jimple.v().newInstanceFieldRef(thisLocal, field.makeRef());
	            AssignStmt assignStmt = Jimple.v().newAssignStmt(tempLocal, fieldRef);
	            units.add(assignStmt);

	            Local temp;
	            if (tempLocal.getType() instanceof IntType) {
	                temp = Jimple.v().newLocal("temp$" + String.valueOf(arrayIndex++), RefType.v("java.lang.Integer"));
	                body.getLocals().add(temp);
	                units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
	                    Scene.v().getMethod("<java.lang.Integer: java.lang.Integer valueOf(int)>").makeRef(), tempLocal
	                )));
	            } else if (tempLocal.getType() instanceof DoubleType) {
	                temp = Jimple.v().newLocal("temp$" + String.valueOf(arrayIndex++), RefType.v("java.lang.Double"));
	                body.getLocals().add(temp);
	                units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
	                    Scene.v().getMethod("<java.lang.Double: java.lang.Double valueOf(double)>").makeRef(), tempLocal
	                )));
	            } else if (tempLocal.getType() instanceof FloatType) {
	                temp = Jimple.v().newLocal("temp$" + String.valueOf(arrayIndex++), RefType.v("java.lang.Float"));
	                body.getLocals().add(temp);
	                units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
	                    Scene.v().getMethod("<java.lang.Float: java.lang.Float valueOf(float)>").makeRef(), tempLocal
	                )));
	            } else if (tempLocal.getType() instanceof LongType) {
	                temp = Jimple.v().newLocal("temp$" + (arrayIndex++), RefType.v("java.lang.Long"));
	                body.getLocals().add(temp);
	                units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
	                    Scene.v().getMethod("<java.lang.Long: java.lang.Long valueOf(long)>").makeRef(), tempLocal
	                )));
	            } else if (tempLocal.getType() instanceof ByteType) {
	                temp = Jimple.v().newLocal("temp$" + (arrayIndex++), RefType.v("java.lang.Byte"));
	                body.getLocals().add(temp);
	                units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
	                    Scene.v().getMethod("<java.lang.Byte: java.lang.Byte valueOf(byte)>").makeRef(), tempLocal
	                )));
	            } else if (tempLocal.getType() instanceof CharType) {
	                temp = Jimple.v().newLocal("temp$" + (arrayIndex++), RefType.v("java.lang.Character"));
	                body.getLocals().add(temp);
	                units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
	                    Scene.v().getMethod("<java.lang.Character: java.lang.Character valueOf(char)>").makeRef(), tempLocal
	                )));
	            } else if (tempLocal.getType() instanceof BooleanType) {
	                temp = Jimple.v().newLocal("temp$" + (arrayIndex++), RefType.v("java.lang.Boolean"));
	                body.getLocals().add(temp);
	                units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
	                    Scene.v().getMethod("<java.lang.Boolean: java.lang.Boolean valueOf(boolean)>").makeRef(), tempLocal
	                )));
	            } else if (tempLocal.getType() instanceof ShortType) {
	                temp = Jimple.v().newLocal("temp$" + (arrayIndex++), RefType.v("java.lang.Short"));
	                body.getLocals().add(temp);
	                units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
	                    Scene.v().getMethod("<java.lang.Short: java.lang.Short valueOf(short)>").makeRef(), tempLocal
	                )));
	            } else if (tempLocal.getType() instanceof RefType) {
	                temp = tempLocal; // No boxing needed
	            } else if (tempLocal.getType() instanceof ArrayType) {
	                ArrayType arrayType = (ArrayType) tempLocal.getType();
	                int dimensions = arrayType.numDimensions;
	                Type elementType = arrayType.getElementType();

	                Local temp1 = Jimple.v().newLocal("temp$" + (arrayIndex++), IntType.v());
	                body.getLocals().add(temp1);

	                List<Type> arguments = new ArrayList<>();
	                arguments.add(tempLocal.getType());

	                SootClass arraysClass = Scene.v().getSootClass("java.util.Arrays");
	                SootMethod hashCodeMethod;
	                if (dimensions == 1) {
	                    if (isPrimitiveArray(elementType)) {
	                        hashCodeMethod = arraysClass.getMethod("hashCode", arguments);
	                    } else {
	                        hashCodeMethod = arraysClass.getMethod("int deepHashCode(java.lang.Object[])");
	                    }
	                } else {
	                    hashCodeMethod = arraysClass.getMethod("int deepHashCode(java.lang.Object[])");
	                }

	                StaticInvokeExpr hashCodeExpr = Jimple.v().newStaticInvokeExpr(hashCodeMethod.makeRef(), tempLocal);
	                AssignStmt assignStmt2 = Jimple.v().newAssignStmt(temp1, hashCodeExpr);
	                units.add(assignStmt2);

	                temp = Jimple.v().newLocal("temp$" + (arrayIndex++), RefType.v("java.lang.Integer"));
	                body.getLocals().add(temp);
	                units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
	                    Scene.v().getMethod("<java.lang.Integer: java.lang.Integer valueOf(int)>").makeRef(), temp1
	                )));
	            } else {
	                throw new RuntimeException("Unsupported parameter type: " + tempLocal.getType());
	            }

	            units.add(Jimple.v().newAssignStmt(Jimple.v().newArrayRef(temp0, IntConstant.v(Index++)), temp));
	        }

	        Local temp = Jimple.v().newLocal("temp$" + String.valueOf(arrayIndex++), IntType.v());
	        body.getLocals().add(temp);
	        units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
	            Scene.v().getMethod("<java.util.Objects: int hash(java.lang.Object[])>").makeRef(), temp0
	        )));

	        units.add(Jimple.v().newReturnStmt(temp));
	    }

	    // Add the method to targetClass before returning
//	    targetClass.addMethod(method);

//	    System.out.println(body);
	    body.validate();
	    return method;
	}
	
	private static boolean isPrimitiveArray(Type elementType) {
	    return elementType.equals(IntType.v()) ||
	           elementType.equals(DoubleType.v()) ||
	           elementType.equals(BooleanType.v()) ||
	           elementType.equals(ByteType.v()) ||
	           elementType.equals(CharType.v()) ||
	           elementType.equals(ShortType.v()) ||
	           elementType.equals(LongType.v()) ||
	           elementType.equals(FloatType.v());
	}
	
	private SootMethod createGenerateCustomHashMethod(SootClass targetClass) {
//		List<SootField> fields = new ArrayList<>();
		List<Type> parameterTypes = new ArrayList<>();
		
		

		for(SootField field: targetClass.getFields()) {
			if (field.isStatic()) {
				continue;
			}
			parameterTypes.add(field.getType());
		}
		
//		SootClass parentClass = targetClass.getSuperclass();
		
		parameterTypes.add(IntType.v());

		// Define the method signature: generateCustomHash with appropriate parameters
		SootMethod method = new SootMethod(
				"generateCustomHash",
				parameterTypes,
				IntType.v(),
				Modifier.PUBLIC | Modifier.STATIC
				);

		// Create the method body
		JimpleBody body = Jimple.v().newBody(method);
		method.setActiveBody(body);
		Chain<Unit> units = body.getUnits();

		// Prepare locals for each parameter and identity statements
		List<Local> parameterLocals = new ArrayList<>();
		
		for (int i=0;i<parameterTypes.size();++i) {
			
			Local parameterLocal = Jimple.v().newLocal("hash"+String.valueOf(i), parameterTypes.get(i));
			body.getLocals().add(parameterLocal);
			parameterLocals.add(parameterLocal);
			Stmt identityStmt = Jimple.v().newIdentityStmt(
					parameterLocal, Jimple.v().newParameterRef(parameterTypes.get(i), i)
					);
			units.add(identityStmt);
		}

		// Create locals for intermediate calculations
		Local temp0 = Jimple.v().newLocal("temp$0", ArrayType.v(RefType.v("java.lang.Object"), 1));
		body.getLocals().add(temp0);

		// Adjust the array size to match the number of fields
		units.add(Jimple.v().newAssignStmt(temp0, Jimple.v().newNewArrayExpr(RefType.v("java.lang.Object"), IntConstant.v(parameterLocals.size()))));

		// Iterate over parameters to box them and store in the array
		int arrayIndex = 0;
		int Index = 0;
		for (Local parameterLocal : parameterLocals) {
			Local temp;

			if (parameterLocal.getType() instanceof IntType) {
				// Handle int type by boxing into Integer
				temp = Jimple.v().newLocal("temp$" + (arrayIndex + 1), RefType.v("java.lang.Integer"));
				body.getLocals().add(temp);

				units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
						Scene.v().getMethod("<java.lang.Integer: java.lang.Integer valueOf(int)>").makeRef(), parameterLocal
						)));
			} else if (parameterLocal.getType() instanceof DoubleType) {
				// Handle double type by boxing into Double
				temp = Jimple.v().newLocal("temp$" + (arrayIndex + 1), RefType.v("java.lang.Double"));
				body.getLocals().add(temp);

				units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
						Scene.v().getMethod("<java.lang.Double: java.lang.Double valueOf(double)>").makeRef(), parameterLocal
						)));
			} else if (parameterLocal.getType() instanceof FloatType) {
				// Handle float type by boxing into Float
				temp = Jimple.v().newLocal("temp$" + (arrayIndex + 1), RefType.v("java.lang.Float"));
				body.getLocals().add(temp);

				units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
						Scene.v().getMethod("<java.lang.Float: java.lang.Float valueOf(float)>").makeRef(), parameterLocal
						)));
			} else if (parameterLocal.getType() instanceof LongType) {
		        // Handle long type by boxing into Long
		        temp = Jimple.v().newLocal("temp$" + (arrayIndex + 1), RefType.v("java.lang.Long"));
		        body.getLocals().add(temp);

		        units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
		                Scene.v().getMethod("<java.lang.Long: java.lang.Long valueOf(long)>").makeRef(), parameterLocal
		        )));
		    }else if (parameterLocal.getType() instanceof ByteType) {
		        // Handle byte type by boxing into Byte
		        temp = Jimple.v().newLocal("temp$" + (arrayIndex + 1), RefType.v("java.lang.Byte"));
		        body.getLocals().add(temp);

		        units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
		                Scene.v().getMethod("<java.lang.Byte: java.lang.Byte valueOf(byte)>").makeRef(), parameterLocal
		        )));
		    }
		    else if (parameterLocal.getType() instanceof CharType) {
		        // Handle char type by boxing into Character
		        temp = Jimple.v().newLocal("temp$" + (arrayIndex + 1), RefType.v("java.lang.Character"));
		        body.getLocals().add(temp);

		        units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
		                Scene.v().getMethod("<java.lang.Character: java.lang.Character valueOf(char)>").makeRef(), parameterLocal
		        )));
		    }
		    else if (parameterLocal.getType() instanceof BooleanType) {
		        // Handle boolean type by boxing into Boolean
		        temp = Jimple.v().newLocal("temp$" + (arrayIndex + 1), RefType.v("java.lang.Boolean"));
		        body.getLocals().add(temp);

		        units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
		                Scene.v().getMethod("<java.lang.Boolean: java.lang.Boolean valueOf(boolean)>").makeRef(), parameterLocal
		        )));
		    }
		    else if (parameterLocal.getType() instanceof ShortType) {
		        // Handle short type by boxing into Short
		        temp = Jimple.v().newLocal("temp$" + (arrayIndex + 1), RefType.v("java.lang.Short"));
		        body.getLocals().add(temp);

		        units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
		                Scene.v().getMethod("<java.lang.Short: java.lang.Short valueOf(short)>").makeRef(), parameterLocal
		        )));
		    }
			else if (parameterLocal.getType() instanceof RefType) {
				// For reference types (e.g., String), directly use the parameter
				temp = parameterLocal; // No need for boxing
			} 
			else if (parameterLocal.getType() instanceof ArrayType) {
		        // Handle array types
//				System.out.println("hello");
		        ArrayType arrayType = (ArrayType) parameterLocal.getType();
		        int dimensions = arrayType.numDimensions;
		        Type elementType = arrayType.getElementType();
		        
//		        System.out.println(dimensions);
//		        // Create a reference for the array
		        Local temp1 = Jimple.v().newLocal("temp$" + (arrayIndex + 1), IntType.v());
		        body.getLocals().add(temp1);
		        arrayIndex++;
		        
		        List<Type> arguments = new ArrayList<>();
		        arguments.add(parameterLocal.getType());
		        
		        SootClass arraysClass = Scene.v().getSootClass("java.util.Arrays");
		        SootMethod hashCodeMethod;
		        if (dimensions == 1) {
		            // Convert Soot Type to Java Class
		            // hashCodeMethod = arraysClass.getMethod("hashCode", arguments);
		            
		            if (isPrimitiveArray(elementType)) {
		                hashCodeMethod = arraysClass.getMethod("hashCode", arguments);
		            } else {
		            	hashCodeMethod = arraysClass.getMethod("int deepHashCode(java.lang.Object[])");
		            }
		            
		            
		        } else {
		        	hashCodeMethod = arraysClass.getMethod("int deepHashCode(java.lang.Object[])"); 
		        }
		        
		        Local arrLocal = parameterLocal;
		        
		        StaticInvokeExpr hashCodeExpr = Jimple.v().newStaticInvokeExpr(hashCodeMethod.makeRef(), arrLocal);
		        AssignStmt assignStmt = Jimple.v().newAssignStmt(temp1, hashCodeExpr);
		        units.add(assignStmt);
		        
		        temp = Jimple.v().newLocal("temp$" + (arrayIndex + 1), RefType.v("java.lang.Integer"));
				body.getLocals().add(temp);

				units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
						Scene.v().getMethod("<java.lang.Integer: java.lang.Integer valueOf(int)>").makeRef(), temp1
						)));
		        
		        

		    }
			else {
				throw new RuntimeException("Unsupported parameter type: " + parameterLocal.getType());
			}

			// Assign the boxed or reference value to temp$0[arrayIndex]
			units.add(Jimple.v().newAssignStmt(Jimple.v().newArrayRef(temp0, IntConstant.v(Index)), temp));
			Index++;
			arrayIndex++;
		}

//		else if(parameterLocal.getType() instanceof LongType) {
//			temp = Jimple.v().newLocal("temp$" + (arrayIndex + 1), RefType.v("java.lang.Long"));
//			body.getLocals().add(temp);
//
//			units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
//					Scene.v().getMethod("<java.lang.Long: java.lang.Long valueOf(long)>").makeRef(), parameterLocal
//					)));
//		}

		// Create the local for the result of the hash computation
		Local temp = Jimple.v().newLocal("temp$" + (arrayIndex+1), IntType.v());
		body.getLocals().add(temp);

		// Call Objects.hash on temp$0 and store the result in temp$3
		units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
				Scene.v().getMethod("<java.util.Objects: int hash(java.lang.Object[])>").makeRef(), temp0
				)));

		// Return the hash result
		units.add(Jimple.v().newReturnStmt(temp));
		
		
//		System.out.println(method.retrieveActiveBody());
		targetClass.addMethod(method);
		body.validate();
		return method;
	}

	public static synchronized void addStaticFieldInClass(String className) {
	    SootClass sootClass = Scene.v().loadClassAndSupport(className);

	    // Define the field object_pool if not already present
	    SootField objectPoolField;
	    if (!sootClass.declaresFieldByName("object_pool")) {
	        objectPoolField = new SootField(
	                "object_pool",
	                RefType.v("java.util.HashMap"),
	                Modifier.PUBLIC | Modifier.STATIC
	        );
	        sootClass.addField(objectPoolField);
	    } else {
	        objectPoolField = sootClass.getFieldByName("object_pool");
	    }

	    // Handle <clinit> method creation if it doesn't exist
	    SootMethod clinitMethod;
	    if (sootClass.declaresMethodByName("<clinit>")) {
	        clinitMethod = sootClass.getMethodByName("<clinit>");
	    } else {
	        clinitMethod = new SootMethod("<clinit>", Collections.emptyList(), VoidType.v(), Modifier.STATIC);
	        sootClass.addMethod(clinitMethod);
	        JimpleBody clinitBody = Jimple.v().newBody(clinitMethod);
	        clinitMethod.setActiveBody(clinitBody);
	        PatchingChain<Unit> units = clinitBody.getUnits();

	        // Ensure return statement is in place
	        units.add(Jimple.v().newReturnVoidStmt());
	    }

	    // Retrieve and manipulate <clinit> method body
	    JimpleBody bodyClinit = (JimpleBody) clinitMethod.retrieveActiveBody();
	    PatchingChain<Unit> units = bodyClinit.getUnits();

	    // Create the new HashMap and assign to the static field
	    Local newHashMap = Jimple.v().newLocal("tmpMap", RefType.v("java.util.HashMap"));
	    bodyClinit.getLocals().add(newHashMap);
	    AssignStmt createHashMap = Jimple.v().newAssignStmt(
	            newHashMap,
	            Jimple.v().newNewExpr(RefType.v("java.util.HashMap"))
	    );
	    
	    // Invoke the constructor to initialize the HashMap
	    SootMethod initMethod = Scene.v().getMethod("<java.util.HashMap: void <init>()>");
	    InvokeStmt invokeInit = Jimple.v().newInvokeStmt(
	            Jimple.v().newSpecialInvokeExpr(newHashMap, initMethod.makeRef())
	    );

	    // Assign the created HashMap to the static field
	    AssignStmt assignToField = Jimple.v().newAssignStmt(
	            Jimple.v().newStaticFieldRef(objectPoolField.makeRef()),
	            newHashMap
	    );

	    // Insert units before the return statement
//	    Unit retStmt = units.getLast();
	    Unit firstStmt = units.getFirst();
	    units.insertBefore(createHashMap, firstStmt);
	    units.insertBefore(invokeInit, firstStmt);
	    units.insertBefore(assignToField, firstStmt);
	    
	    
//	    if(className.equals("avrora.arch.legacy.LegacyRegister")) {
//	    	System.out.println(bodyClinit);
//	    }
	    bodyClinit.validate();
	    
	}

	public void findAllConstantClasses(List<SootClass> allClasses){
		
		
		
		for(SootClass sootclass : allClasses){
			solve(sootclass);
		}
		
		
		for(SootClass sootClass:allClasses) {
			JdkClassObject(sootClass);
		}
		

		for(SootClass sootClass : allClasses)
		{
			if(!isJDKClass(sootClass)) {
				if(notAConstantClass.contains(sootClass) == false)
				{	
					
					constantClass.add(sootClass);
				}
			}
		}
	}
	
	public void JdkClassObject(SootClass sootClass) {
		SootClass parentClass = sootClass.getSuperclass();
//		System.out.println(parentClass.toString().equals("java.lang.Object"));
		
		if(parentClass==null) return;
		
		
		if(parentClass.toString().equals("java.lang.Object")==false && isJDKClass(parentClass) || parentClass.isAbstract()) {
			constantClassDfs(sootClass);
		}
		
	}

	public void solve(SootClass className) {
		
//		System.out.println(className.toString() + " = = ");
		
		int flag = 0;
		
		for(SootMethod method:className.getMethods()) {

			if (method.isJavaLibraryMethod() || method.isStaticInitializer() || method.isNative() || method.isAbstract()) {
				continue;
			}
			
			
			if(method.isConstructor()){
				Body body = method.retrieveActiveBody();
				
				
				
				HashSet<Local> localToThisRefMap = new HashSet<>();
				for(Unit unit:body.getUnits()) {
//					System.out.println(unit);
					Stmt stmt = (Stmt) unit;
					if (stmt instanceof IdentityStmt) { // Look for `l0 := @this: Entity;`
		                IdentityStmt identityStmt = (IdentityStmt) stmt;
		                if (identityStmt.getRightOp() instanceof ThisRef) {
		                    localToThisRefMap.add((Local) identityStmt.getLeftOp());
		                }
		            }
					else if(stmt instanceof AssignStmt) {
						AssignStmt assignStmt = (AssignStmt) stmt;
						

						
						
						
						if((assignStmt.getRightOp() instanceof Local && localToThisRefMap.contains((Local)assignStmt.getRightOp())) 
								|| (assignStmt.getRightOp() instanceof CastExpr)) {
							

							if(assignStmt.getRightOp() instanceof CastExpr) {
								CastExpr castExpr = (CastExpr) assignStmt.getRightOp() ;
								Value operand = castExpr.getOp();
								if(operand instanceof Local && localToThisRefMap.contains((Local)operand)) {
									
									constantClassDfs(className);
								}


							}else {
								constantClassDfs(className);
							}
							
							
//							if(assignStmt.getLeftOp() instanceof StaticFieldRef) {
//								flag = 1;
//							}
//							else
//							{
//								System.out.println(className+"    "+stmt);
//								localToThisRefMap.add((Local) assignStmt.getLeftOp());
//							}
						}
					}
					
				}
				
				
				
				
				for(Unit unit:body.getUnits()) {
					Stmt stmt = (Stmt) unit;
					if (stmt.containsInvokeExpr() ) { 
						
						InvokeExpr invokeExpr = stmt.getInvokeExpr();
						
						
				    	if (invokeExpr instanceof InstanceInvokeExpr || invokeExpr instanceof StaticInvokeExpr) {
				    		
				    		
				    		InstanceInvokeExpr instanceInvokeExpr;
				    		StaticInvokeExpr staticInvokeExpr;
				    		List<Value> args ;
				    				
				    				
				    		if(invokeExpr instanceof InstanceInvokeExpr) {		
				    			instanceInvokeExpr = (InstanceInvokeExpr) invokeExpr;
				    			args = instanceInvokeExpr.getArgs();;
				    			Value base = instanceInvokeExpr.getBase(); // Get the object on which method is called    	
				    			if (base instanceof ThisRef || (base instanceof Local && localToThisRefMap.contains((Local) base))) {
				    				SootMethod calledMethod = invokeExpr.getMethod();
				    				String declaringName = calledMethod.getDeclaringClass().getName();

				    				if(calledMethod.isConstructor())
				    				{

				    					if(className.toString().equals(declaringName)) {
				    						constantClassDfs(className);
				    					}

				    				}
				    				else
				    				{
				    					constantClassDfs(className);
				    				}
				    			}
				    		}
				    		else {
				    			staticInvokeExpr = (StaticInvokeExpr) invokeExpr;
				    			args = staticInvokeExpr.getArgs();
				    		}
				    		
				    		
				    				
				    		
				    		
				    		
				    		
				    		
				    		for(int i=0;i<args.size();++i) {
				    			if(args.get(i) instanceof Local) {
				    				Local var = (Local)args.get(i);
				    				if(var instanceof ThisRef || (localToThisRefMap.contains(var))) {
				    					constantClassDfs(className);
				    				}
				    			}
				    		}
				    	}
				    	
				    	
		            }
					
				}
				
				    
				

			}
			else {
				if(method.hasActiveBody()==false) continue;
				Body body = method.retrieveActiveBody();
				for (Unit unit : body.getUnits()) {
					Stmt stmt = (Stmt) unit;
					InvokeExpr invokeExpr;
					if (stmt instanceof AssignStmt) {
						AssignStmt assignStmt = (AssignStmt) stmt;

						if (assignStmt.getLeftOp() instanceof FieldRef) {
							FieldRef fieldRef = (FieldRef) assignStmt.getLeftOp();
							SootField field = fieldRef.getField();
							SootClass declaringClass = field.getDeclaringClass();
							String NameOfClass = declaringClass.getName();
//							System.out.println(declaringClass);
							if(!isJDKClass(declaringClass) && !notAConstantClass.contains(declaringClass) && allClasses.contains(declaringClass))
								constantClassDfs(declaringClass);
						}
						
					}
					
				}
			}
		}
		
		
		if(flag==1) {
			constantClassDfs(className);
		}
		
		
	}
	
	public void constantClassDfs(SootClass sootClass)
	{
		
		
		
		notAConstantClass.add(sootClass);
//		System.out.println(sootClass);
		for(String it : adjacencyList.get(sootClass.toString()))
		{
			SootClass Node = Scene.v().getSootClass(it);
			if(!notAConstantClass.contains(Node)) {
//				System.out.println(sootClass+" ++++ "+Node);
				constantClassDfs(Node);
			}
					
		}
	}
	
	public static boolean isJDKClass(SootClass sootClass) {
	    // Define a list of known library package prefixes
		String[] libraryPrefixes = {
			    "java.", 
			    "javax.", 
			    "jdk.",
			    "com.sun.",
			    "sun.",                     // <- Optional, for core internal classes
			    "org.apache",              // Covers Xerces, Commons, etc.
			    "org.springframework.",
			    "org.slf4j.",
			    "org.w3c.",                 // W3C DOM APIs
			    "org.xml.",                 // XML APIs
			    "org.objectweb.",           // ASM and other bytecode libs
			    "org.junit.",               // JUnit 4
			    "org.junit.jupiter.",       // JUnit 5
			    "org.testng.",              // TestNG
			    "org.gradle.",              // Gradle APIs
			    "com.google.common.",       // Guava
			    "com.google.gson.",         // Gson
			    "com.fasterxml.jackson.",   // Jackson JSON parser
			    "com.ibm.",                 // IBM SDK-specific or WALA
			    "com.oracle.",              // Oracle libraries
			    "com.fasterxml.",           // Broader Jackson
			    "org.checkerframework.",    // Checker framework
			    "org.hibernate.",           // Hibernate ORM
			    "org.reactivestreams.",     // Reactive Stream APIs
			    "reactor.",                 // Project Reactor
			    "io.reactivex.",            // RxJava
			    "io.vertx.",                // Vert.x
			    "kotlin.",                  // Kotlin standard libs
			    "soot.",
			    "scala.",
			    "scopt.",
			    "io.jenetics"
			};


	    String packageName = sootClass.getPackageName();
	    
	    // Check if the package name starts with any of the known library prefixes
	    for (String prefix : libraryPrefixes) {
	        if (packageName.startsWith(prefix) || sootClass.toString().startsWith(prefix)) {
	            return true;
	        }
	    }
	    return false;
	}

	public void findAllClasses(){
		Chain <SootClass> classes = Scene.v().getApplicationClasses(); // Get the Chain of classes		
		List <SootClass> listClasses = new ArrayList <>(classes); // Convert Chain to ArrayList
		//	    System.out.println(listClasses);
		List<SootClass> nonLibraryClasses = new ArrayList<>();
		for(SootClass c: listClasses) {
//			System.out.println(c);
			if(!c.isLibraryClass() && !isJDKClass(c) && !c.isInterface() && !c.isAbstract()) {
				nonLibraryClasses.add(c);
			}
		}
		
		
		for (SootClass sootClass : nonLibraryClasses) {
			
//			System.out.println(sootClass);
            addClass(sootClass.getName());

            if (sootClass.hasSuperclass()) {
                SootClass parent = sootClass.getSuperclass();
                if(!parent.isLibraryClass() && !isJDKClass(parent) && !parent.isInterface())
                addRelationship(parent.getName(), sootClass.getName());
            }

//            for (SootClass iface : sootClass.getInterfaces()) {
//                addRelationship(iface.getName(), sootClass.getName());
//            }
        }
		
//		displayGraph();
		
		List<String> roots = findRoots();
        System.out.println("Root(s) of the graph: " + roots);
        
        
        HashSet<String> visited = new HashSet<>();
        for(String node:roots){
        	dfs(node,visited);
        }
        
	}
	
	public void addClass(String className) {
        adjacencyList.putIfAbsent(className, new ArrayList<>());
    }

	public void addRelationship(String parent, String child) {
        adjacencyList.putIfAbsent(parent, new ArrayList<>());
        adjacencyList.putIfAbsent(child, new ArrayList<>());
        adjacencyList.get(parent).add(child);
    }
    
	public void displayGraph() {
        for (Map.Entry<String, List<String>> entry : adjacencyList.entrySet()) {
            System.out.println(entry.getKey() + " -> " + entry.getValue());
        }
    }
    
	public List<String> findRoots() {
        HashSet<String> potentialRoots = new HashSet<>(adjacencyList.keySet());
        for (List<String> children : adjacencyList.values()) {
            potentialRoots.removeAll(children);
        }
        return new ArrayList<>(potentialRoots);
    }
	
	private void dfs(String node,HashSet<String> visited)
    {
    	
    	if(visited.contains(node)==false)
    	allClasses.add(Scene.v().getSootClass(node));
    	
    	visited.add(node);
    	
    	for(String it : adjacencyList.get(node))
    	{
    		if(!visited.contains(it))
    		{
    			
    			dfs(it,visited);
    		}
    		else
    		{
    			SootClass existingClass = Scene.v().getSootClass(it);
//    			System.out.println("hello");
    			allClasses.remove(existingClass); 
                allClasses.add(existingClass); 
    		}
    	}
    }
	
}