package cs6235;

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
import soot.DoubleType;
import soot.FloatType;
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
import soot.jimple.ReturnStmt;
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

public class Solution1 extends SceneTransformer{
	HashSet<SootClass> constantClass = new HashSet<>();
	HashSet<SootClass> notAConstantClass = new HashSet<>();
	public static Map<String, HashSet<String>> finalClassesWithFields = new HashMap<>();
	HashMap<SootMethod,String> constructorMapping = new HashMap<>();
	
	@Override
	protected synchronized void internalTransform(String phaseName, Map<String, String> options) {

		List<SootClass> allClasses = findAllClasses();
		findAllConstantClasses(allClasses);
		System.out.println(constantClass);
		
		
//		Scene.v().addClass(new SootClass("APL"));
		Chain<SootField> allClassFields = new HashChain<>();
		for(SootClass sootClass: allClasses) {
			if(!sootClass.isInterface()) {
				SootClass dclass = Scene.v().loadClassAndSupport(sootClass.toString());
				allClassFields.addAll(dclass.getFields());
			}
		}
		
		for(SootClass sootClass : constantClass){
//			addStaticFieldInClass(sootClass.toString());
//			SootMethod generateCustomHashMethod = createGenerateCustomHashMethod(sootClass);
//	        sootClass.addMethod(generateCustomHashMethod);
//			addFactoryMethodCreateObject(sootClass.toString(), allClassFields);
//			ConstructorAnalysis();
//			createConstructorWithAllParameter(sootClass);
	
			
//			analyzeConstructorCall(sootClass);
		}
		
//		printBody(allClasses);
	}
	
	public static void createConstructorWithAllParameter(SootClass sootClass)
	{
		List<SootField> fields = new ArrayList<>();
		List<Type> fieldType = new ArrayList<>();
		
		
		
		SootClass currentClass = sootClass;
		
		while(currentClass != null)
		{
			
			for(SootField field: currentClass.getFields())
			{
				if(field.isStatic()) continue;
				
				fields.add(field);
				fieldType.add(field.getType());
			}
			
			if(currentClass.hasSuperclass())
			{
				currentClass = currentClass.getSuperclass();
				if(isJDKClass(currentClass))
				{
					currentClass = null;
				}
			}
			else
			{
				currentClass = null;
			}
				
		}
		
		
		
		
		SootMethod Constructor = new SootMethod(
		        "<init>",
		        fieldType,
		        VoidType.v(),
		        Modifier.PUBLIC 
		    );
		
		sootClass.addMethod(Constructor);
		
		JimpleBody body = Jimple.v().newBody(Constructor);
		Constructor.setActiveBody(body);
		PatchingChain<Unit> units = body.getUnits();
		
		Local thisLocal = Jimple.v().newLocal("this", sootClass.getType());
	    body.getLocals().add(thisLocal);
	    units.add(Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(sootClass.getType())));
	    
	    for (int i = 0; i < fieldType.size(); ++i) {

	    	Local parameterLocal = Jimple.v().newLocal("this_"+fields.get(i).getName(), fieldType.get(i));
	    	body.getLocals().add(parameterLocal);
	    	Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(fieldType.get(i), i));
	    	units.add(stmt);
	    }
	    
	    for(int i = 0; i < fieldType.size(); ++i) {
	    	InstanceFieldRef fieldRef = Jimple.v().newInstanceFieldRef(thisLocal, fields.get(i).makeRef());
	    	AssignStmt assignStmt = Jimple.v().newAssignStmt(fieldRef,body.getParameterLocal(i));
	    	units.add(assignStmt);

	    }
	    
	    ReturnVoidStmt returnStmt = Jimple.v().newReturnVoidStmt();
	    units.add(returnStmt);
	}

	public void ConstructorAnalysis()
	{
		
		int i=0;
		for(SootClass sootClass:constantClass)
		{
			List<SootMethod> methods = new ArrayList<>();
			for(SootMethod sootMethod : sootClass.getMethods())
			{
				if(sootMethod.isConstructor())
				{
					methods.add(sootMethod);
				}
			}
			for(SootMethod sootMethod : methods)
			{
				createDummyConstructor(sootClass,sootMethod,i);
				constructorMapping.put(sootMethod, "dummyConstructor"+String.valueOf(i));
				sootClass.removeMethod(sootMethod);
				i++;
			}
		}
	}
 	
	public void createDummyConstructor(SootClass sootClass, SootMethod sootMethod,int abc) {
	    // Retrieve the parameter types of the original method
	    List<Type> parameterTypes = sootMethod.getParameterTypes();
	    System.out.println(parameterTypes);

	    // Define the dummy constructor with the same parameter types
	    SootMethod dummyConstructor = new SootMethod(
	        "dummyConstructor"+String.valueOf(abc),
	        parameterTypes,
	        sootClass.getType(),
	        Modifier.PUBLIC | Modifier.STATIC
	    );
	    
	    sootClass.addMethod(dummyConstructor);

	    JimpleBody dummyConstructorBody = Jimple.v().newBody(dummyConstructor);
	    dummyConstructor.setActiveBody(dummyConstructorBody);
	    PatchingChain<Unit> dummyConstructorUnits = dummyConstructorBody.getUnits();

	    JimpleBody mainConstructorBody = (JimpleBody) sootMethod.retrieveActiveBody();
	    PatchingChain<Unit> mainConstructorUnits = mainConstructorBody.getUnits();

	    Local thisLocal = Jimple.v().newLocal("this", sootClass.getType());
	    dummyConstructorBody.getLocals().add(thisLocal);
	    dummyConstructorUnits.add(Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(sootClass.getType())));
	    
	    
	    for (int i = 0; i < parameterTypes.size(); ++i) {
	        
	        Local parameterLocal = Jimple.v().newLocal(mainConstructorBody.getParameterLocal(i).toString(), parameterTypes.get(i));
	        dummyConstructorBody.getLocals().add(parameterLocal);
	        Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(parameterTypes.get(i), i));
	        dummyConstructorUnits.add(stmt);
	    }
	    
	    
	    
	    int x = 0;
	    
	    List<Value> arguments = new ArrayList<>();
	    List<Type> argumentsType = new ArrayList<>();
	    HashMap<String,Local> LocalInfo = new HashMap<>();
	    
	    
	    
	    SootClass currentClass = sootClass;
	    while(currentClass!=null)
	    {
	    	for(SootField sootfield:currentClass.getFields())
		    {
		    	if(sootfield.isStatic()) continue;
		    	
				Local temp = Jimple.v().newLocal("this_"+sootfield.getName(), sootfield.getType());
				arguments.add((Value)temp);
				argumentsType.add(sootfield.getType());
	            dummyConstructorBody.getLocals().add(temp);
	            LocalInfo.put("this_"+sootfield.getName(),temp);
		    }
	    	
	    	if(currentClass.hasSuperclass())
			{
				currentClass = currentClass.getSuperclass();
				if(isJDKClass(currentClass))
				{
					currentClass = null;
				}
			}
			else
			{
				currentClass = null;
			}
	    }
	    
	    
	    
	    for(Unit unit:mainConstructorUnits)
	    {
	    	Stmt stmt = (Stmt) unit;
	    	if (stmt instanceof AssignStmt) {
	    		AssignStmt assignStmt = (AssignStmt) stmt;
	    		Value lhs = assignStmt.getLeftOp();
	    		Value rhs = assignStmt.getRightOp();
	    		
	    		if (lhs instanceof InstanceFieldRef ) {
	    			InstanceFieldRef instanceFieldRef = (InstanceFieldRef) lhs;
	    			String fieldName = instanceFieldRef.getField().getName();
	    			Local temp = LocalInfo.get("this_"+fieldName);
	                Stmt newAssignStmt = Jimple.v().newAssignStmt(temp, rhs);
	                dummyConstructorUnits.add(newAssignStmt);
	    		}
	    		else
		    	{
	    			Local temp = Jimple.v().newLocal("temp$"+x++, rhs.getType());
	                dummyConstructorBody.getLocals().add(temp);
	    			Stmt newAssignStmt = Jimple.v().newAssignStmt(temp, rhs);
	    			dummyConstructorUnits.add(newAssignStmt);
		    	}
	    	}
	    	else
	    	{
	    		if(stmt instanceof ReturnVoidStmt)
	    		{
	    			System.out.println(sootClass);
	    			System.out.println("return "+stmt);
	    			SootMethodRef createObjectRef = Scene.v()
                            .getSootClass(sootClass.toString())
                            .getMethod("create_object", argumentsType)
                            .makeRef();
	    			
	    			
	    			InvokeExpr invokeExpr = Jimple.v().newStaticInvokeExpr(createObjectRef, arguments);
	    			
	    			Local temp = Jimple.v().newLocal("temp$"+x++, sootClass.getType());
	                dummyConstructorBody.getLocals().add(temp);
                    AssignStmt newAssignStmt = Jimple.v().newAssignStmt(temp, invokeExpr);
                    dummyConstructorUnits.add(newAssignStmt);
                    
                    ReturnStmt returnStmt = Jimple.v().newReturnStmt(temp);
            	    dummyConstructorUnits.add(returnStmt);
	    			
	    			
	    		}
	    		else if(stmt instanceof IdentityStmt)
	    		{
	    			continue;
	    		}
	    		else
	    		{
	    			dummyConstructorUnits.add(stmt);
	    			
	    		}
	    	}
	    	
	    	
	    	
	    	
	    	
	    }
	    
	    System.out.println(dummyConstructorBody);

	    
	    
	    
	    
	    
	    
	    
	    
	    
	    
	    
	    
	    
	    
	    
	    
	    

//	    // Create a new local 'ansObject' of the type of the SootClass
//	    Local ansObject = Jimple.v().newLocal("ansObject", sootClass.getType());
//	    dummyConstructorBody.getLocals().add(ansObject);
//
//	    // Create a new instance of the SootClass and assign it to 'ansObject'
//	    Stmt newStmt = Jimple.v().newAssignStmt(
//	        ansObject,
//	        Jimple.v().newNewExpr(sootClass.getType())
//	    );
//	    dummyConstructorUnits.add(newStmt);
//
//	    // Add a return statement returning 'ansObject'
//	    ReturnStmt returnStmt = Jimple.v().newReturnStmt(ansObject);
//	    dummyConstructorUnits.add(returnStmt);
	}

	public void analyzeConstructorCall(SootClass sootClass) {
	    // Iterate over all methods to find methods where new instances are created
	    for (SootMethod method : sootClass.getMethods()) {
	        if (!method.isConcrete()) continue;

	        if (method.getName().equals("create_object")) continue;

	        JimpleBody body = (JimpleBody) method.retrieveActiveBody();
	        PatchingChain<Unit> units = body.getUnits();

	        // Use a list to collect statements to modify (to avoid iterator issues)
	        List<Unit> toReplace = new ArrayList<>();

	        for (Unit unit : units) {
	            Stmt stmt = (Stmt) unit;

	            // Look for "new" statements (instance creation)
	            if (stmt instanceof AssignStmt) {
	                AssignStmt assignStmt = (AssignStmt) stmt;
	                if (assignStmt.getRightOp() instanceof NewExpr) {
	                    NewExpr newExpr = (NewExpr) assignStmt.getRightOp();
	                    SootClass newClass = newExpr.getBaseType().getSootClass();

	                    if (constantClass.contains(newClass)) {
	                        // Collect non-static fields
	                        Chain<SootField> fields = new HashChain<>();
	                        for (SootField field : newClass.getFields()) {
	                            if (!field.isStatic()) {
	                                fields.add(field);
	                            }
	                        }

	                        Value leftOp = assignStmt.getLeftOp();
	                        List<Value> constructorArgs = new ArrayList<>();

	                        // Iterate over following units to find the constructor call
	                        Iterator<Unit> iter = units.iterator(stmt);
	                        boolean flag = true;
	                        HashMap<String, Value> fieldMapping = new HashMap<>();
	                        while (iter.hasNext() && flag) {
	                            Unit nextUnit = iter.next();
	                            if (nextUnit instanceof InvokeStmt) {
	                                InvokeExpr invokeExpr = ((InvokeStmt) nextUnit).getInvokeExpr();

	                                if (invokeExpr instanceof SpecialInvokeExpr) {
	                                    SpecialInvokeExpr specialInvoke = (SpecialInvokeExpr) invokeExpr;

	                                    if (specialInvoke.getMethod().getName().equals("<init>") &&
	                                            specialInvoke.getMethod().getDeclaringClass().equals(newClass)) {
	                                        constructorArgs = specialInvoke.getArgs();
	                                        flag = false;

	                                        // Analyze the constructor to see how parameters are used
	                                        fieldMapping = analyzeConstructorBody(specialInvoke.getMethod(), constructorArgs, newClass);
	                                    }
	                                }
	                            }
	                        }

	                        // Prepare arguments for the staticinvoke `create_object`
	                        List<Value> arguments = new ArrayList<>();
	                        for (SootField f : fields) {
	                            String field = f.getName();
	                            arguments.add(fieldMapping.get(field));
	                        }

	                        // Create a method reference for `create_object`
	                        List<Type> createObjectParameter = new ArrayList<>();
	                        for (SootField f : fields) {
	                            createObjectParameter.add(f.getType());
	                        }

	                        SootMethodRef createObjectRef = Scene.v()
	                                .getSootClass(newClass.toString())
	                                .getMethod("create_object", createObjectParameter)
	                                .makeRef();

	                        // Create the staticinvoke expression for `create_object`
	                        InvokeExpr invokeExpr = Jimple.v().newStaticInvokeExpr(createObjectRef, arguments);
	                        AssignStmt newAssignStmt = Jimple.v().newAssignStmt(leftOp, invokeExpr);

	                        // Store the statement to replace and the corresponding constructor call to remove later
	                        toReplace.add(unit);
	                        toReplace.add(newAssignStmt);
	                    }
	                }
	            }
	        }

	        // Apply the collected modifications outside of iteration
	        for (int i = 0; i < toReplace.size(); i += 2) {
	            Unit oldStmt = toReplace.get(i);
	            AssignStmt newStmt = (AssignStmt) toReplace.get(i + 1);

	            // Replace the old "new" statement with the static invoke
	            units.insertAfter(newStmt, oldStmt);
	            units.remove(oldStmt);

	            // Optionally, remove the constructor call statement
	            Iterator<Unit> iter = units.iterator(newStmt);
	            while (iter.hasNext()) {
	                Unit nextUnit = iter.next();
	                if (nextUnit instanceof InvokeStmt &&
	                        ((InvokeStmt) nextUnit).getInvokeExpr() instanceof SpecialInvokeExpr) {
	                    SpecialInvokeExpr invokeExpr = (SpecialInvokeExpr) ((InvokeStmt) nextUnit).getInvokeExpr();
	                    if (invokeExpr.getMethod().getName().equals("<init>")) {
	                        units.remove(nextUnit);
	                        break;
	                    }
	                }
	            }
	        }
	    }
	}

	public HashMap<String,Value> analyzeConstructorBody(SootMethod constructor,List<Value> constructorArgs,SootClass targetClass) {
		Chain<SootField> fields = new HashChain<>();
		for(SootField field : targetClass.getFields())
		{
			if (field.isStatic()) {
				continue;
			}
			fields.add(field);
		}
		HashMap<String,Local> FieldMapping = new HashMap<>();
		HashMap<Local,Value> ArgsMapping = new HashMap<>();
		HashMap<Local,Value> TempMapping = new HashMap<>();
		HashMap<String,Value> FieldValueMapping = new HashMap<>();
		
		
	    JimpleBody body = (JimpleBody) constructor.retrieveActiveBody();
	    
	    
	    for(int i=0;i<constructorArgs.size();++i)
	    {
	    	Local x = body.getParameterLocal(i);
	    	ArgsMapping.put(x,constructorArgs.get(i));
	    }

	    for (Unit unit : body.getUnits()) {
	        Stmt stmt = (Stmt) unit;

	        // Look for assignment statements
	        if (stmt instanceof AssignStmt) {
	            AssignStmt assignStmt = (AssignStmt) stmt;

	            // Check if it's assigning a parameter to a field
	            if (assignStmt.getLeftOp() instanceof InstanceFieldRef) {
	                InstanceFieldRef fieldRef = (InstanceFieldRef) assignStmt.getLeftOp();
	                Local rightOp = (Local)assignStmt.getRightOp();

//	                System.out.println("Field " + fieldRef.getField().getName() + " is assigned value: " + rightOp);
	                FieldMapping.put(fieldRef.getField().getName(), rightOp);
	            }
	            else if(assignStmt.getLeftOp().toString().startsWith("temp$"))
	            {
	            	Value rightOp = assignStmt.getRightOp();
	            	Local leftOp = (Local)assignStmt.getLeftOp();
	            	TempMapping.put(leftOp, rightOp);
	            }
	        }
	    }
	    
	    
	    for(String k1 : FieldMapping.keySet())
	    {
	    	Local x = FieldMapping.get(k1);
	    	
	    	if(ArgsMapping.containsKey(x))
	    	{
	    		FieldValueMapping.put(k1, ArgsMapping.get(x));
	    	}
	    	else
	    	{
	    		FieldValueMapping.put(k1, TempMapping.get(x));
	    	}
	    }
	    
	    
	    for(String k : FieldValueMapping.keySet())
	    {
	    	System.out.println(k+" "+FieldValueMapping.get(k));
	    }
//	    for(Local k1 : ArgsMapping.keySet())
//	    {
//	    	System.out.println(k1 + "  " +ArgsMapping.get(k1));
//	    }
//	    
//	    for(Local k1 : TempMapping.keySet())
//	    {
//	    	System.out.println(k1 + "  " +TempMapping.get(k1));
//	    }
	    
	    return FieldValueMapping;
	}
	
	private static SootMethod createGenerateCustomHashMethod(SootClass targetClass) {
		// Get all non-static fields from the class
//		Chain<SootField> fields = new HashChain<>(targetClass.getFields());
		List<SootField> fields = new ArrayList<>();
		List<Type> parameterTypes = new ArrayList<>();
		
		SootClass currentclass = targetClass;
		while(currentclass!=null) {

			for(SootField field: currentclass.getFields()) {
				if (field.isStatic()) {
					continue;
				}
				parameterTypes.add(field.getType());
				fields.add(field);
			}

			if(currentclass.hasSuperclass())
			{
				currentclass = currentclass.getSuperclass();
				if(isJDKClass(currentclass))
				{
					currentclass = null;
				}
			}
			else
			{
				currentclass = null;
			}

		}

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
		int index = 0;
		for (SootField field : fields) {
			if (field.isStatic()) {
				continue;
			}
			Local parameterLocal = Jimple.v().newLocal(field.getName(), field.getType());
			body.getLocals().add(parameterLocal);
			parameterLocals.add(parameterLocal);
			Stmt identityStmt = Jimple.v().newIdentityStmt(
					parameterLocal, Jimple.v().newParameterRef(field.getType(), index++)
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
			} else if (parameterLocal.getType() instanceof RefType) {
				// For reference types (e.g., String), directly use the parameter
				temp = parameterLocal; // No need for boxing
			} else {
				throw new RuntimeException("Unsupported parameter type: " + parameterLocal.getType());
			}

			// Assign the boxed or reference value to temp$0[arrayIndex]
			units.add(Jimple.v().newAssignStmt(Jimple.v().newArrayRef(temp0, IntConstant.v(arrayIndex)), temp));
			arrayIndex++;
		}


		// Create the local for the result of the hash computation
		Local temp = Jimple.v().newLocal("temp$" + (arrayIndex), IntType.v());
		body.getLocals().add(temp);

		// Call Objects.hash on temp$0 and store the result in temp$3
		units.add(Jimple.v().newAssignStmt(temp, Jimple.v().newStaticInvokeExpr(
				Scene.v().getMethod("<java.util.Objects: int hash(java.lang.Object[])>").makeRef(), temp0
				)));

		// Return the hash result
		units.add(Jimple.v().newReturnStmt(temp));

		return method;
	}
	
	
	public static synchronized void addFactoryMethodCreateObject(String className, Chain<SootField> allClassFields) {

		SootClass sootClass = Scene.v().loadClassAndSupport(className);
//		List <SootMethod> Methods = new ArrayList <SootMethod>(sootClass.getMethods());
//		Chain<SootField> Fields = new HashChain<>(sootClass.getFields());


		addMultipleArgumentConstructor(className);

		//		for (SootMethod method : Methods) {
		//			if (method.isConstructor() && method.hasActiveBody()) {
		//
		//				addFactoryMethodCreateObjectUtil(method, className, Fields, allClassFields);
		//
		//			}
		//		}
		//
		//
		//		modifyConstructorAccessModifier(className);
		//		addOurOwnConstructor(className, Fields, Methods);


	}

	public static synchronized void addMultipleArgumentConstructor(String className) { 

		SootClass sootClass = Scene.v().loadClassAndSupport(className);


		//		Method Creation and assigning parameter
		List<Type> parameterTypesList = new ArrayList<>();
		List<SootField> Fields = new ArrayList<>();
		SootClass currentclass = sootClass;
		while(currentclass!=null) {
			
			for(SootField field: currentclass.getFields()) {
				if (field.isStatic()) {
					continue;
				}
				parameterTypesList.add(field.getType());
				Fields.add(field);
			}
			
			if(currentclass.hasSuperclass())
			{
				currentclass = currentclass.getSuperclass();
				if(isJDKClass(currentclass))
				{
					currentclass = null;
				}
			}
			else
			{
				currentclass = null;
			}
			
		}





		String createObjectMethodName = "create_object";
		SootMethod createObjectMethod = new SootMethod(createObjectMethodName, parameterTypesList, sootClass.getType() , Modifier.PUBLIC | Modifier.STATIC);
		sootClass.addMethod(createObjectMethod);

		// Body Initialize
		JimpleBody body = Jimple.v().newBody(createObjectMethod);
		createObjectMethod.setActiveBody(body);
		PatchingChain<Unit> units = body.getUnits();

		// Assign Local variable for the Method 
		List<Local> parameterListToUse = new ArrayList<>();

		int k=0;
		for(SootField field: Fields) {
			if (field.isStatic()) {
				continue;
			}
			Local parameterLocal = Jimple.v().newLocal(field.getName(), field.getType());
			body.getLocals().add(parameterLocal);
			parameterListToUse.add(parameterLocal);
			Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(field.getType(), k++));
			units.add(stmt);	

		}



		List<Local> HashFunParameter = new ArrayList<>();
		List<Type> HashFunParameterType = new ArrayList<>();
		for(int i=0;i<k;++i)
		{
			Local x = body.getParameterLocal(i);
			Type y = body.getParameterLocal(i).getType();
			HashFunParameterType.add(y);
			HashFunParameter.add(x);
		}



		Local temp$0 = Jimple.v().newLocal("temp$0", IntType.v());
		body.getLocals().add(temp$0); 
		Local hashvalue = Jimple.v().newLocal("hashvalue", IntType.v());
		body.getLocals().add(hashvalue); 
		SootMethodRef generateCustomHashRef = Scene.v().getSootClass(className).getMethod("generateCustomHash", HashFunParameterType).makeRef();
		InvokeExpr invokeExpr = Jimple.v().newStaticInvokeExpr(generateCustomHashRef, HashFunParameter);
		AssignStmt assStmt = Jimple.v().newAssignStmt(temp$0, invokeExpr);
		units.add(assStmt); 
		assStmt = Jimple.v().newAssignStmt(hashvalue,temp$0);
		units.add(assStmt);





		SootField objectPoolField = Scene.v().getSootClass(className).getFieldByName("object_pool");
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


		Local temp$8 = Jimple.v().newLocal("temp$8",Scene.v().getSootClass(className).getType());
		body.getLocals().add(temp$8);
		Stmt newObjStmt = Jimple.v().newAssignStmt(temp$8,Jimple.v().newNewExpr(Scene.v().getSootClass(className).getType()));



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

		Local temp$7 = Jimple.v().newLocal("temp$7", RefType.v(className));
		body.getLocals().add(temp$7);
		units.add(Jimple.v().newAssignStmt(temp$7, Jimple.v().newCastExpr(temp$6, RefType.v(className))));


		Local ansObject = Jimple.v().newLocal("ansObject",Scene.v().getSootClass(className).getType());
		body.getLocals().add(ansObject);
		AssignStmt assignStmt = Jimple.v().newAssignStmt(ansObject, temp$7);
		units.add(assignStmt);

		Stmt returnStmt  = Jimple.v().newReturnStmt(ansObject);
		units.add(returnStmt);





		units.add(newObjStmt);
		SootMethodRef initMethodRef = Scene.v().makeConstructorRef(Scene.v().getSootClass(className), parameterTypesList);
		Stmt invokeInitStmt = Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(temp$8, initMethodRef, parameterListToUse));
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


	}

	public static synchronized void overwriteEqualsMethod(String className) {
		// Load the specified class
		SootClass sootClass = Scene.v().loadClassAndSupport(className); 

		// Look for the existing equals method
		SootMethod equalsMethod = null;
		for (SootMethod method : sootClass.getMethods()) {
			if (method.getName().equals("equals") && method.getParameterCount() == 1 &&
					method.getParameterType(0).equals(RefType.v("java.lang.Object"))) {
				equalsMethod = method;
				break;
			}
		}

		if (equalsMethod == null) {
			// Create the equals method if it doesn't exist
			equalsMethod = new SootMethod("equals", Collections.singletonList(RefType.v("java.lang.Object")), BooleanType.v(), Modifier.PUBLIC);
			sootClass.addMethod(equalsMethod);
		}

		// Get the existing body of the equals method or create a new one if necessary
		JimpleBody body;
		if (equalsMethod.hasActiveBody()) {
			body = (JimpleBody) equalsMethod.getActiveBody();
		} else {
			body = Jimple.v().newBody(equalsMethod);
			equalsMethod.setActiveBody(body);
		}

		// Get the PatchingChain for modifying the units
		PatchingChain<Unit> units = body.getUnits();

		// Create local variables
		Local thisLocal = Jimple.v().newLocal("this", sootClass.getType());
		Local oLocal = Jimple.v().newLocal("o", RefType.v("java.lang.Object"));
		Local temp0 = Jimple.v().newLocal("temp$0", BooleanType.v());
		Local temp1 = Jimple.v().newLocal("temp$1", BooleanType.v());

		// Add local variables to the body
		body.getLocals().add(thisLocal);
		body.getLocals().add(oLocal);
		body.getLocals().add(temp0);
		body.getLocals().add(temp1);

		// Create and add identity statements for "this" and "o"
		Stmt stmt = Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(sootClass.getType()));
		units.add(stmt);

		stmt = Jimple.v().newIdentityStmt(oLocal, Jimple.v().newParameterRef(RefType.v("java.lang.Object"), 0));
		units.add(stmt);

		// Create a reference equality expression
		EqExpr referenceEqualityExpr = Jimple.v().newEqExpr(thisLocal, oLocal);

		// Create an if statement
		Stmt targetStmt1 = Jimple.v().newAssignStmt(temp0, IntConstant.v(1));
		IfStmt ifStmt = Jimple.v().newIfStmt(referenceEqualityExpr, targetStmt1);
		units.add(ifStmt);

		// Add statements for the case when objects are not equal
		Stmt targetStmt2 = Jimple.v().newAssignStmt(temp1, IntConstant.v(0));
		units.add(targetStmt2);

		stmt = Jimple.v().newReturnStmt(temp1);
		units.add(stmt);

		// Add statements for the case when objects are equal
		units.add(targetStmt1);
		stmt = Jimple.v().newReturnStmt(temp0);
		units.add(stmt);

		// Validate the body after modifications
		body.validate();
	}

	public static synchronized void addStaticFieldInClass(String className) {
		SootClass sootClass = Scene.v().loadClassAndSupport(className);
		RefType hashMapType = RefType.v("java.util.HashMap");

		if (!sootClass.declaresFieldByName("object_pool")) {

			SootField staticHashMapField = new SootField("object_pool", hashMapType, Modifier.STATIC | Modifier.PUBLIC);
			sootClass.addField(staticHashMapField);

			SootMethod clinit = sootClass.getMethodByNameUnsafe("<clinit>");
			Boolean flag = true;
			if (clinit == null) {
				clinit = new SootMethod("<clinit>", Collections.emptyList(), VoidType.v(), Modifier.STATIC);
				sootClass.addMethod(clinit);
				JimpleBody body = Jimple.v().newBody(clinit);
				clinit.setActiveBody(body);
				flag = false;
			}

			JimpleBody body = (JimpleBody) clinit.getActiveBody();
			PatchingChain<Unit> units = body.getUnits();

			if(flag)
				units.removeLast();

			Local object_pool = Jimple.v().newLocal("temp$0", hashMapType);

			body.getLocals().add(object_pool);

			Stmt stmt = Jimple.v().newAssignStmt(object_pool, Jimple.v().newNewExpr(hashMapType));
			units.add(stmt);
			//			System.out.println(units);

			stmt = Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(object_pool, Scene.v().getMethod("<java.util.HashMap: void <init>()>").makeRef(), Collections.<Value>emptyList()));
			units.add(stmt);

			stmt = Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(staticHashMapField.makeRef()), object_pool);
			units.add(stmt);

			Stmt returnStmt = Jimple.v().newReturnVoidStmt();
			units.add(returnStmt);

			body.validate();
		}
	}

	public static void printBody(List<SootClass> allClasses)
	{
		for(SootClass sootClass:allClasses)
		{
			if(!isJDKClass(sootClass))
			{
				for(SootMethod method:sootClass.getMethods())
				{
					System.out.println(sootClass+" --------------------------- "+method+"\n");
					Body body = method.retrieveActiveBody();
					for (Unit unit : body.getUnits()) {
						Stmt stmt = (Stmt) unit;
						System.out.println(stmt);
					}
					System.out.println();
				}
				System.out.println("\n\n");
			}
		}
	}

	public void findAllConstantClasses(List<SootClass> allClasses){
		for(SootClass sootclass : allClasses){
			if(!isJDKClass(sootclass)) {
				solve(sootclass);
			}
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

	public boolean solve(SootClass className){

		if(isJDKClass(className)) return true;



		if(notAConstantClass.contains(className)){
			return false;
		}

		if(className.hasSuperclass()){
			if(solve(className.getSuperclass())==false){
				notAConstantClass.add(className);
				return false;
			}
		}

		boolean flag = true;

		for (SootMethod method : className.getMethods()) {
			if (method.isJavaLibraryMethod() || method.isConstructor() || method.isStaticInitializer()) {
				continue;
			}

			Body body = method.retrieveActiveBody();
			for (Unit unit : body.getUnits()) {
				Stmt stmt = (Stmt) unit;
				if (stmt instanceof AssignStmt) {
					AssignStmt assignStmt = (AssignStmt) stmt;
					if (assignStmt.getLeftOp() instanceof FieldRef) {
						FieldRef fieldRef = (FieldRef) assignStmt.getLeftOp();
						SootField field = fieldRef.getField();
						SootClass declaringClass = field.getDeclaringClass();
						String NameOfClass = declaringClass.getName();
						notAConstantClass.add(className);
						flag = false;
					}
				}

			}
		}

		return flag;
	}

	public static boolean isJDKClass(SootClass sootClass) {

		String packageName = sootClass.getPackageName();
		return packageName.startsWith("java.") || packageName.startsWith("javax.") || sootClass.toString().startsWith("jdk");
	}

	public static List<SootClass> findAllClasses(){
		Chain <SootClass> classes = Scene.v().getApplicationClasses(); // Get the Chain of classes		
		List <SootClass> listClasses = new ArrayList <>(classes); // Convert Chain to ArrayList
		//	    System.out.println(listClasses);
		List<SootClass> nonLibraryClasses = new ArrayList<>();
		for(SootClass c: listClasses) {
			if(!c.isLibraryClass() && !isJDKClass(c)) {
				nonLibraryClasses.add(c);
			}
		}
		return nonLibraryClasses;
	}


}