package cs6235;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

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

public class ConstantClass extends SceneTransformer{
	public static Map<String, HashSet<String>> finalClassesWithFields = new HashMap<>();
	
	@Override
	protected synchronized void internalTransform(String phaseName, Map<String, String> options) {

		List<SootClass> allClasses = findAllClasses();
		HashSet<SootClass> constantClasses = findAllConstantClasses(allClasses);
		System.out.println(constantClasses);

	}
	
public static void injectCustomHashMethod(String className) {
	    
	    SootClass sootClass = Scene.v().loadClassAndSupport(className);
	    
	    
	    List<SootField> allFields = new ArrayList<>();
	    SootClass currentClass = sootClass;

	    while (currentClass != null && !isJDKClass(currentClass)) {
	        allFields.addAll(currentClass.getFields());
	        currentClass = currentClass.getSuperclass();
	    }

	    SootMethod customHashMethod = new SootMethod("generateCustomHash", Collections.emptyList(), IntType.v(), Modifier.PUBLIC);
	    sootClass.addMethod(customHashMethod);
	    JimpleBody body = Jimple.v().newBody(customHashMethod);
	    customHashMethod.setActiveBody(body);
	    

	    PatchingChain<Unit> units = body.getUnits();
	    
	 // Step 1: Create the local variable for 'this'
	    Local thisLocal = Jimple.v().newLocal("this", sootClass.getType());
	    body.getLocals().add(thisLocal);
	    
	    // Step 2: Add 'this := @this' to the body
	    units.add(Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(sootClass.getType())));

	    // Step 3: Create an Object array to hold the fields
//	    ArrayType objectArrayType = ArrayType.v((Type)RefType.v("java.lang.Object"), 1);
	    Local tempArrayLocal = Jimple.v().newLocal("temp$0", RefType.v("java.lang.Object"));
	    body.getLocals().add(tempArrayLocal);
	    
	    // Create an array with the size equal to the number of fields
	    units.add(Jimple.v().newAssignStmt(
	        tempArrayLocal, 
	        Jimple.v().newNewArrayExpr(RefType.v("java.lang.Object"), IntConstant.v(allFields.size()))
	    ));

	    // Step 4: Iterate through fields, load them, and store them in the array
	    for (int i = 0; i < allFields.size(); i++) {
	        SootField field = allFields.get(i);
	        Type fieldType = field.getType();

	        Local fieldLocal;
	        if (fieldType instanceof PrimType) {
	            // If it's a primitive, we need to box it (e.g., int to Integer)
	            fieldLocal = Jimple.v().newLocal("tempField" + i, fieldType);
	            body.getLocals().add(fieldLocal);
	            units.add(Jimple.v().newAssignStmt(
	                fieldLocal, 
	                Jimple.v().newInstanceFieldRef(thisLocal, field.makeRef())
	            ));
	            
	            Local boxedLocal = Jimple.v().newLocal("boxedField" + i, (getBoxedType(fieldType)));
	            body.getLocals().add(boxedLocal);

	            // Box the primitive value
	            units.add(Jimple.v().newAssignStmt(
	                boxedLocal,
	                Jimple.v().newStaticInvokeExpr(Scene.v().getMethod("<java.lang.Integer: java.lang.Integer valueOf(int)>").makeRef(), fieldLocal)
	            ));

	            // Assign the boxed value to the array
	            units.add(Jimple.v().newAssignStmt(
	                Jimple.v().newArrayRef(tempArrayLocal, IntConstant.v(i)),
	                boxedLocal
	            ));

	        } else {
	            // If it's an Object (non-primitive)
	            fieldLocal = Jimple.v().newLocal("tempField" + i, fieldType);
	            body.getLocals().add(fieldLocal);
	            units.add(Jimple.v().newAssignStmt(
	                fieldLocal, 
	                Jimple.v().newInstanceFieldRef(thisLocal, field.makeRef())
	            ));

	            // Directly assign to the array
	            units.add(Jimple.v().newAssignStmt(
	                Jimple.v().newArrayRef(tempArrayLocal, IntConstant.v(i)),
	                fieldLocal
	            ));
	        }
	    }

	    // Step 5: Call `Objects.hash` with the array
	    Local resultLocal = Jimple.v().newLocal("temp$4", IntType.v());
	    body.getLocals().add(resultLocal);
	    SootMethod hashMethod = Scene.v().getMethod("<java.util.Objects: int hash(java.lang.Object[])>");
	    units.add(Jimple.v().newAssignStmt(
	        resultLocal, 
	        Jimple.v().newStaticInvokeExpr(hashMethod.makeRef(), tempArrayLocal)
	    ));

	    // Step 6: Return the result
	    units.add(Jimple.v().newReturnStmt(resultLocal));
	    
	}
	
	private static RefType getBoxedType(Type type) {
	    if (type instanceof IntType) {
	        return RefType.v("java.lang.Integer");
	    } else if (type instanceof BooleanType) {
	        return RefType.v("java.lang.Boolean");
	    } else if (type instanceof CharType) {
	        return RefType.v("java.lang.Character");
	    } else if (type instanceof LongType) {
	        return RefType.v("java.lang.Long");
	    } else if (type instanceof FloatType) {
	        return RefType.v("java.lang.Float");
	    } else if (type instanceof DoubleType) {
	        return RefType.v("java.lang.Double");
	    } else if (type instanceof ShortType) {
	        return RefType.v("java.lang.Short");
	    } else if (type instanceof ByteType) {
	        return RefType.v("java.lang.Byte");
	    } else {
	        throw new IllegalArgumentException("Unsupported primitive type: " + type);
	    }
	}

	
	public synchronized HashSet<SootClass> findAllConstantClasses(List<SootClass> allClasses){
    	
    	HashSet<SootClass> finalClasses = findAllClassesWithFinalFields(allClasses);
//    	System.out.println("final Class "+finalClasses);
    	
    	Map<SootClass, HashSet<String>> fieldAssignmentsOutsideConstructor = findFieldAssignmentsOutsideConstructor(allClasses);
//    	System.out.println(fieldAssignmentsOutsideConstructor);
    	Map<SootClass, HashSet<String>> fieldAssignmentsInConstructor = findFieldAssignmentsInConstructor(allClasses);
//    	System.out.println(fieldAssignmentsInConstructor);
        
    	

        for (Map.Entry<SootClass, HashSet<String>> entry : fieldAssignmentsInConstructor.entrySet()) {
        	
        	if(!fieldAssignmentsOutsideConstructor.containsKey(entry.getKey())) {
        		finalClasses.add(entry.getKey());
        		finalClassesWithFields.put(entry.getKey().toString(), entry.getValue());
        	}
        }
        
        return finalClasses;
        
    }
	
	
	public synchronized Map<SootClass, HashSet<String>> findFieldAssignmentsOutsideConstructor(List <SootClass> allClasses){
    	
    	Map<SootClass, HashSet<String>> fieldAssignmentsOutsideConstructor = new HashMap<>();
    	
    	for(SootClass sootClass: allClasses) {
    		if(!isJDKClass(sootClass)) {
		    	for (SootMethod method : sootClass.getMethods()) {
		    		
		    		try {
		    			
			            Body body = method.retrieveActiveBody();

			            // Skip constructors and static initializers
			            if (method.isJavaLibraryMethod() || method.isConstructor() ) {
			            	continue;
			            }
			           
			            for (Unit unit : body.getUnits()) {
			            	
			                Stmt stmt = (Stmt) unit;
			                System.out.println(stmt);
			                
			               
			                if (stmt instanceof AssignStmt && stmt.containsFieldRef()) {

			                    FieldRef fieldRef = stmt.getFieldRef();
			                    
			                    String fieldName = fieldRef.getField().getName();
			                    //System.out.println(fieldName);
		                    
			                    SootFieldRef fieldClass = fieldRef.getFieldRef();
		                        if(fieldAssignmentsOutsideConstructor.containsKey(fieldClass.declaringClass())) {
			                    	fieldAssignmentsOutsideConstructor.get(fieldClass.declaringClass()).add(fieldName);
			                    }else {
			                    	fieldAssignmentsOutsideConstructor.put(fieldClass.declaringClass(), new HashSet<>());
			                    	fieldAssignmentsOutsideConstructor.get(fieldClass.declaringClass()).add(fieldName);
			                    }
			
			                }
			            }
		    		}catch(Exception e){
//						System.out.println("Can't retrive body Exception: "+e);
					}
		    	}
	    	}
    	}
    	return fieldAssignmentsOutsideConstructor;
    }
    
	public synchronized Map<SootClass, HashSet<String>> findFieldAssignmentsInConstructor(List <SootClass> allClasses){
		
		Map<SootClass, HashSet<String>> fieldAssignmentsInConstructor = new HashMap<>();
		
		for (SootClass sootClass : allClasses) {
			
			SootClass currentClass = sootClass;
			HashSet<String> classField = new HashSet<>();
			boolean flag = true;
			while(currentClass == sootClass) {
				HashSet<String> allField = new HashSet<>();
				for (SootField field : currentClass.getFields()) {
					allField.add(field.getName());
					//System.out.println(field.getName());
				}
				if(!isJDKClass(currentClass)) {
					
					for(SootMethod method: currentClass.getMethods()) {
						if (method.isJavaLibraryMethod() || !method.isConstructor() || method.isStaticInitializer() || method.getParameterCount()>0) {
			                continue;
			            }
						
						Body body = method.retrieveActiveBody();
			            HashSet<String> assignedFields = new HashSet<>();
			            for (Unit unit : body.getUnits()) {
//			            	System.out.println(unit);
			                Stmt stmt = (Stmt) unit;
			                //System.out.println(stmt);
			
			               
			                if (stmt instanceof AssignStmt && stmt.containsFieldRef()) {
			                	
			                    FieldRef fieldRef = stmt.getFieldRef();
//			                    String variableName = fieldRef.getField().getName();
//			                    if(sootClass.declaresFieldByName(variableName)) {
//			                    	assignedFields.add(fieldRef.getField().getName());
//			                    }
			                    
			                    assignedFields.add(fieldRef.getField().getName());
			                }
			            }
			            
			            //here
			            
			            if(sootClass.equals(currentClass))
			            {
			            	classField = allField;
			            }
			            
			            if (!(!assignedFields.isEmpty() && assignedFields.size() == allField.size())) {
			            	flag = false;
	                    }
			            
			           
					}
					
				}
				
				
				if (currentClass.hasSuperclass()) {
	                currentClass = currentClass.getSuperclass();
	            } else {
	                break;
	            }
				
			}
			
			if(flag)
			{
				fieldAssignmentsInConstructor.putIfAbsent(sootClass, classField);
			}
		}
			
			
			
			
			
		return fieldAssignmentsInConstructor;
		
	}
	
    public synchronized HashSet<SootClass> findAllClassesWithFinalFields(List<SootClass> allClasses){
    	HashSet<SootClass> finalClasses = new HashSet<>();
    	
    	for (SootClass sootClass : allClasses) {
    		if (!isJDKClass(sootClass)) {
    			int flag = 0;
    			HashSet<String> allFields = new HashSet<>();
    			
    			
    			SootClass currentClass = sootClass;
    			while (currentClass == sootClass) {
    				for (SootField field : currentClass.getFields()) {
    					if(currentClass.equals(sootClass)) {
    						allFields.add(field.getName());
//    						System.out.println(field.getName());
    					}

                        // If the field is not final, set the flag and break
                        if (!field.isFinal()) {
                            flag = 1;
                            break;
                        }
                    }
    				
    				if (flag == 1) {
                        break;
                    }
    				
    				if (currentClass.hasSuperclass()) {
                        currentClass = currentClass.getSuperclass();
                    } else {
                        currentClass = null;
                    }
    			}
    			
    			if (flag == 0 && !allFields.isEmpty()) {
                    finalClasses.add(sootClass);
                    finalClassesWithFields.put(sootClass.toString(), allFields);
                }
    		}
    	}
    		
    	return finalClasses;
    }
    

	public static List<SootClass>findAllClasses(){
	    	Chain <SootClass> classes = Scene.v().getApplicationClasses(); // Get the Chain of classes		
		    List <SootClass> listClasses = new ArrayList <>(classes); // Convert Chain to ArrayList
//		    System.out.println(listClasses);
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

	   
}
