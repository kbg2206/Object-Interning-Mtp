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
import soot.IntegerType;
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

public class SuperImplement extends SceneTransformer{
	HashSet<SootClass> constantClass = new HashSet<>();
	HashSet<SootClass> notAConstantClass = new HashSet<>();
	HashMap<SootMethod,String> constructorMapping = new HashMap<>();
	
	@Override
	protected synchronized void internalTransform(String phaseName, Map<String, String> options) {
//		Scene.v().addClass(new SootClass("Dummy"));
		List<SootClass> allClasses = findAllClasses();
		findAllConstantClasses(allClasses);
		System.out.println(constantClass);

		
		for(SootClass sootClass : allClasses){
			if(constantClass.contains(sootClass)){
//		        sootClass.addMethod(createGenerateCustomHashMethod(sootClass));
//				sootClass.addMethod(createHashVfunction(sootClass));
//				addStaticFieldInClass(sootClass.toString());
//				ProgramCreation(sootClass);
//				analyzeConstructorCall(sootClass);
			}
		}
		
		System.out.println(constructorMapping);
		
		
	}
	
	public void analyzeConstructorCall(SootClass sootClass) {
	    
	    for (SootMethod method : sootClass.getMethods()) {
	        if (!method.isConcrete()) continue;

	        if (method.getName().startsWith("createObject")) continue;
	        if (method.getName().startsWith("dummyConstructor")) continue;

	        JimpleBody body = (JimpleBody) method.retrieveActiveBody();
	        PatchingChain<Unit> units = body.getUnits();

	        // Use a list to collect statements to modify (to avoid iterator issues)
	        List<Unit> toReplace = new ArrayList<>();

	        for (Unit unit : units) {
	            Stmt stmt = (Stmt) unit;

	            // Look for "new" statements (instance creation)
	            if (stmt instanceof AssignStmt) {
	                AssignStmt assignStmt = (AssignStmt) stmt;
	                SootMethod constMethod = method;
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
	                        List<Type> constructorType = new ArrayList<>();
	                        

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
	                                    	SootMethod invokedMethod = specialInvoke.getMethod();
	                                        constructorArgs = specialInvoke.getArgs();
	                                        constructorType = invokedMethod.getParameterTypes();
	                                        constMethod = invokedMethod;
	                                        flag = false;

	                                        
	                                    }
	                                }
	                            }
	                        }

	                       
	                        String methodName = constructorMapping.get(constMethod);
	                        SootMethodRef createObjectRef = Scene.v()
	                                .getSootClass(newClass.toString())
	                                .getMethod(methodName, constructorType)
	                                .makeRef();

	                        // Create the staticinvoke expression for `create_object`
	                        InvokeExpr invokeExpr = Jimple.v().newStaticInvokeExpr(createObjectRef, constructorArgs);
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

	private SootMethod createGenerateCustomHashMethod(SootClass targetClass) {
//		List<SootField> fields = new ArrayList<>();
		List<Type> parameterTypes = new ArrayList<>();
		
		

		for(SootField field: targetClass.getFields()) {
			if (field.isStatic()) {
				continue;
			}
			parameterTypes.add(field.getType());
		}
		
		SootClass parentClass = targetClass.getSuperclass();
		if(!isJDKClass(parentClass))
		{
			parameterTypes.add(parentClass.getType());
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
	
	private SootMethod createHashVfunction(SootClass targetClass)
	{
		List<Type> parameterTypes = new ArrayList<>();
		SootClass parentClass = targetClass.getSuperclass();
		
		
		SootMethod method = new SootMethod(
				"hashCode",
				Collections.emptyList(),
				IntType.v(),
				Modifier.PUBLIC 
				);

		
		JimpleBody body = Jimple.v().newBody(method);
		method.setActiveBody(body);
		Chain<Unit> units = body.getUnits();

		
		List<Local> parameterLocals = new ArrayList<>();
		
		Local thisRef = Jimple.v().newLocal("thisRef", targetClass.getType());
        body.getLocals().add(thisRef);
        Stmt stmt = Jimple.v().newIdentityStmt(
                thisRef,
                Jimple.v().newThisRef(targetClass.getType())
        );
        units.add(stmt);
        
        
        Local tempSuperHashCode = Jimple.v().newLocal("tempSuperHashCode", IntType.v());
        body.getLocals().add(tempSuperHashCode);
        units.add(Jimple.v().newAssignStmt(
                tempSuperHashCode,
                Jimple.v().newVirtualInvokeExpr(
                        thisRef,
                        Scene.v().getMethod("<java.lang.Object: int hashCode()>").makeRef()
                )
        ));
		
		int k=0;
		for(SootField field:targetClass.getFields()) {
			if(field.isStatic()) continue;
			
			Local parameterLocal = Jimple.v().newLocal("temp$"+String.valueOf(k++), field.getType());
			body.getLocals().add(parameterLocal);
			parameterLocals.add(parameterLocal);
			Stmt identityStmt = Jimple.v().newIdentityStmt(
	                thisRef,
	                Jimple.v().newThisRef(targetClass.getType())
	        )
			units.add(identityStmt);
			
		}
		
		Local temp0 = Jimple.v().newLocal("temp$0", ArrayType.v(RefType.v("java.lang.Object"), 1));
		body.getLocals().add(temp0);

		
		units.add(Jimple.v().newAssignStmt(temp0, Jimple.v().newNewArrayExpr(RefType.v("java.lang.Object"), IntConstant.v(parameterLocals.size()))));

		return method;
	}
	
 	private void ProgramCreation(SootClass sootClass)
	{
		int constructorCount = 1;
		
		List<SootMethod> methods = new ArrayList<>();
		for(SootMethod sootMethod : sootClass.getMethods()){
			if(sootMethod.isConstructor()){
				methods.add(sootMethod);
			}
		}
		for(SootMethod sootMethod:methods){
			
			if(sootMethod.isConstructor()){
				createDummyConstructor(sootMethod,sootClass,constructorCount);
				constructorMapping.put(sootMethod, "dummyConstructor"+sootClass.toString()+String.valueOf(constructorCount));
				constructorCount++;
				if(constructorCount==3) break;
			}
		}
	}

	private void createDummyConstructor(SootMethod sootMethod,SootClass sootClass,int constructorCount)
	{
		List<Type> parameterTypes = new ArrayList<>(sootMethod.getParameterTypes());
		List<Value> newArgs = new ArrayList<>();

        parameterTypes.add(BooleanType.v());
		
		SootMethod dummyConstructor = new SootMethod(
		        "dummyConstructor"+sootClass.toString()+String.valueOf(constructorCount),
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
	    
	    
	    for (int i = 0; i < parameterTypes.size()-1; ++i) {
	        
	        Local parameterLocal = Jimple.v().newLocal(mainConstructorBody.getParameterLocal(i).toString(), parameterTypes.get(i));
	        dummyConstructorBody.getLocals().add(parameterLocal);
	        newArgs.add((Value)parameterLocal);
	        Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(parameterTypes.get(i), i));
	        dummyConstructorUnits.add(stmt);
	    }
	    
	    Local flag = Jimple.v().newLocal("flag", BooleanType.v());
	    dummyConstructorBody.getLocals().add(flag);
	    Stmt stmtflag = Jimple.v().newIdentityStmt(flag, Jimple.v().newParameterRef(BooleanType.v(), parameterTypes.size()-1));
        dummyConstructorUnits.add(stmtflag);
        
        Local temp$8 = Jimple.v().newLocal("temp$8",sootClass.getType());
        dummyConstructorBody.getLocals().add(temp$8);
		Stmt newObjStmt = Jimple.v().newAssignStmt(temp$8,Jimple.v().newNewExpr(sootClass.getType()));



		EqExpr eqExpr = Jimple.v().newEqExpr(flag, IntConstant.v(0));
		IfStmt ifStmt = Jimple.v().newIfStmt(eqExpr, newObjStmt);
		dummyConstructorUnits.add(ifStmt);
        
        
	    
	    HashMap<String,Local> LocalInfo = new HashMap<>();
	    List<Value> arguments = new ArrayList<>();
	    List<Type> argumentsType = new ArrayList<>();
	    int x = 0;
	    
	    for(SootField sootfield:sootClass.getFields())
	    {
	    	if(sootfield.isStatic()) continue;
	    	
			Local temp = Jimple.v().newLocal("this_"+sootfield.getName(), sootfield.getType());
			arguments.add((Value)temp);
			argumentsType.add(sootfield.getType());
            dummyConstructorBody.getLocals().add(temp);
            LocalInfo.put("this_"+sootfield.getName(),temp);
	    }
	    
	    
	    
	    
	    
//	    Local thisLocal = Jimple.v().newLocal("this", sootClass.getType());
//	    dummyConstructorBody.getLocals().add(thisLocal);
//	    dummyConstructorUnits.add(Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(sootClass.getType())));
        
	    
	    for(Unit unit:mainConstructorUnits){
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
	    	else if(stmt instanceof ReturnVoidStmt)
    		{
//        	    createCreateObject(sootMethod,sootClass,constructorCount);
        	    
        	    SootMethodRef createObjectRef = Scene.v()
                        .getSootClass(sootClass.toString())
                        .getMethod("createObject"+sootClass.toString()+String.valueOf(constructorCount), argumentsType)
                        .makeRef();
    			
    			InvokeExpr invokeExpr = Jimple.v().newStaticInvokeExpr(createObjectRef, arguments);
    			
    			Local temp = Jimple.v().newLocal("temp$"+x++, sootClass.getType());
                dummyConstructorBody.getLocals().add(temp);
                Local temp1 = Jimple.v().newLocal("ans", sootClass.getType());
                dummyConstructorBody.getLocals().add(temp1);
                AssignStmt newAssignStmt = Jimple.v().newAssignStmt(temp, invokeExpr);
                dummyConstructorUnits.add(newAssignStmt);
                
                newAssignStmt = Jimple.v().newAssignStmt(temp1, temp);
                dummyConstructorUnits.add(newAssignStmt);
                ReturnStmt returnStmt = Jimple.v().newReturnStmt(temp1);
        	    dummyConstructorUnits.add(returnStmt);
    			
    		}
	    	else if(stmt instanceof IdentityStmt)
	    	{
	    		continue;
	    	}
	    	else if(stmt instanceof InvokeStmt)
	    	{
	    		InvokeExpr invokeExpr = ((InvokeStmt) unit).getInvokeExpr();
	    		if(invokeExpr instanceof SpecialInvokeExpr){
                	SpecialInvokeExpr specialInvoke = (SpecialInvokeExpr) invokeExpr;
                	
                	
                    SootMethod invokedMethod = specialInvoke.getMethod();
                    
                    if (invokedMethod.getSignature().equals("<java.lang.Object: void <init>()>")) {
                        continue;
                    }
                    
                    
                    List<Type> parametersTypeCons = new ArrayList<>();
                    for(Type type:invokedMethod.getParameterTypes())
                    {
                    	parametersTypeCons.add(type);
                    }
                    
                    parametersTypeCons.add(BooleanType.v());
                    
                    
                    SootClass parentClass = sootClass.getSuperclass();
                    Local temp = Jimple.v().newLocal("obj", parentClass.getType());
        	    	dummyConstructorBody.getLocals().add(temp);
        	    	
        	    	Local temp1 = Jimple.v().newLocal("temp$"+x++, parentClass.getType());
                    dummyConstructorBody.getLocals().add(temp1);
        	    	
        	    	arguments.add((Value)temp);
        	    	argumentsType.add(parentClass.getType());
        	    	
        	    	List<Value> dummyargu = new ArrayList<>();
                     
                    for(int i=0;i<parametersTypeCons.size()-1;++i)
                    {
                    	Value arg = specialInvoke.getArg(i);
                    	dummyargu.add(arg);
                    	argumentsType.add(invokedMethod.getParameterType(i));
                    	arguments.add(arg);
                    }
                    
                    Local temp2 = Jimple.v().newLocal("temp$"+x++,BooleanType.v());
                    dummyConstructorBody.getLocals().add(temp2);
                    AssignStmt AssStmt = Jimple.v().newAssignStmt(temp2,IntConstant.v(0));
                    dummyConstructorUnits.add(AssStmt);
                    
                    dummyargu.add((Value)temp2);
                    
                    String parentDummyConstName = constructorMapping.get(invokedMethod);
                    
                    SootMethodRef dummyConstRef = parentClass
                            .getMethod(parentDummyConstName, parametersTypeCons)
                            .makeRef();
        			
        			InvokeExpr InvokeExpr = Jimple.v().newStaticInvokeExpr(dummyConstRef, dummyargu);
        			AssignStmt newAssignStmt = Jimple.v().newAssignStmt(temp1, InvokeExpr);
                    dummyConstructorUnits.add(newAssignStmt);
                    
                    newAssignStmt = Jimple.v().newAssignStmt(temp, temp1);
                    dummyConstructorUnits.add(newAssignStmt);
                    
                    
                    Local hashV = Jimple.v().newLocal("hashV", IntType.v());
                    dummyConstructorBody.getLocals().add(hashV);
                    
                    temp2 = Jimple.v().newLocal("temp$"+x++,IntType.v());
                    dummyConstructorBody.getLocals().add(temp2);
                    
                    dummyConstRef = parentClass
                            .getMethod("hashVFunction"+parentClass.toString())
                            .makeRef();
                    InvokeExpr = Jimple.v().newStaticInvokeExpr(dummyConstRef, temp);
            		AssStmt = Jimple.v().newAssignStmt(temp2,InvokeExpr);
            		dummyConstructorUnits.add(AssStmt);
            		
            		AssStmt = Jimple.v().newAssignStmt(hashV,temp2);
            		dummyConstructorUnits.add(AssStmt);
                    
                    
                    
                }
	    	}
	    }
	    
	    
	    
	    dummyConstructorUnits.add(newObjStmt);
	    SpecialInvokeExpr specialInvokeExpr1 = Jimple.v().newSpecialInvokeExpr(temp$8, sootMethod.makeRef(), newArgs);
	    InvokeStmt invokeStmt1 = Jimple.v().newInvokeStmt(specialInvokeExpr1);
	    dummyConstructorUnits.add(invokeStmt1);
	    
	    ReturnStmt returnStmt = Jimple.v().newReturnStmt(temp$8);
	    dummyConstructorUnits.add(returnStmt);
	    System.out.println(dummyConstructorUnits);
	    
	    
	    
	    
	}
	
	private void createCreateObject(SootMethod sootMethod,SootClass sootClass,int constructorCount)
	{
		SootClass Dummy = Scene.v().getSootClass("Dummy");
		List<Local> parameterListToUse = new ArrayList<>();
		List<Type> newConstInvokationType = new ArrayList<>();
		for(int i=1;i<=constructorCount;++i) {
			newConstInvokationType.add(Dummy.getType());
		}
		
		List<Type> parameterTypesList = new ArrayList<>();
		List<Type> HashFunctionParameterType = new ArrayList<>();
		List<SootField> Fields = new ArrayList<>();
		
		
		
		for(SootField field: sootClass.getFields()) {
			if (field.isStatic()) {
				continue;
			}
			parameterTypesList.add(field.getType());
			HashFunctionParameterType.add(field.getType());
			newConstInvokationType.add(field.getType());
			Fields.add(field);
		}
		
		List<Type> superParaTypeList = new ArrayList<>();
		Body consBody = sootMethod.retrieveActiveBody();
        Chain<Unit> consUnits = consBody.getUnits();
		for(Unit unit: consUnits) {
			if (unit instanceof InvokeStmt) {
                InvokeExpr invokeExpr = ((InvokeStmt) unit).getInvokeExpr();
                
                if(invokeExpr instanceof SpecialInvokeExpr){
                	SpecialInvokeExpr specialInvoke = (SpecialInvokeExpr) invokeExpr;

                    
                    SootMethod invokedMethod = specialInvoke.getMethod();
                    
                    if (invokedMethod.getSignature().equals("<java.lang.Object: void <init>()>")) {
                        continue;
                    }
                    superParaTypeList = invokedMethod.getParameterTypes();
                }
			}
		}
		
		if(superParaTypeList.size()!=0){
			SootClass parentClass = sootClass.getSuperclass();
			parameterTypesList.add(parentClass.getType());
			HashFunctionParameterType.add(parentClass.getType());
			for(Type type:superParaTypeList) {
				newConstInvokationType.add(type);
				parameterTypesList.add(type);
			}
		}
		
		String createObjectMethodName = "createObject"+sootClass.toString()+String.valueOf(constructorCount);
		SootMethod createObjectMethod = new SootMethod(createObjectMethodName, parameterTypesList, sootClass.getType() , Modifier.PUBLIC | Modifier.STATIC);
		sootClass.addMethod(createObjectMethod);
		
		JimpleBody body = Jimple.v().newBody(createObjectMethod);
		createObjectMethod.setActiveBody(body);
		PatchingChain<Unit> units = body.getUnits();
		
		int k = 0;
		for(SootField field: Fields) {
			if (field.isStatic()) {
				continue;
			}
			Local parameterLocal = Jimple.v().newLocal("this_"+field.getName(), parameterTypesList.get(k));
			body.getLocals().add(parameterLocal);
			parameterListToUse.add(parameterLocal);
			Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(parameterTypesList.get(k), k));
			k++;
			units.add(stmt);	

		}
		
		
		if(superParaTypeList.size()!=0){
			Local parameterLocal = Jimple.v().newLocal("obj", parameterTypesList.get(k));
			body.getLocals().add(parameterLocal);
			
			Stmt stmt = Jimple.v().newIdentityStmt(parameterLocal, Jimple.v().newParameterRef(parameterTypesList.get(k), k));
			units.add(stmt);
			k++;
			
			int x = 1;
			while(k!=parameterTypesList.size())
			{
				Local parameterLocalexp = Jimple.v().newLocal("exp"+String.valueOf(x), parameterTypesList.get(k));
				x++;
				body.getLocals().add(parameterLocalexp);
				parameterListToUse.add(parameterLocalexp);
				Stmt stmtexp = Jimple.v().newIdentityStmt(parameterLocalexp, Jimple.v().newParameterRef(parameterTypesList.get(k), k));
				units.add(stmtexp);
				k++;
			}
		}
		
		
		for(int i=0;i<constructorCount;++i)
		{
			Local temp = Jimple.v().newLocal("temp$10"+String.valueOf(i), Dummy.getType());
			body.getLocals().add(temp);
			AssignStmt assignStmt = Jimple.v().newAssignStmt(temp, NullConstant.v());
			units.add(assignStmt);
			parameterListToUse.add(0,temp);
		}
		
		List<Local> HashFunParameter = new ArrayList<>();
		for(int i=0;i<HashFunctionParameterType.size();++i)
		{
			Local x = body.getParameterLocal(i);
			HashFunParameter.add(x);
		}
		
		Local temp$0 = Jimple.v().newLocal("temp$0", IntType.v());
		body.getLocals().add(temp$0);
		SootMethodRef generateCustomHashRef = sootClass.getMethod("generateCustomHash", HashFunctionParameterType).makeRef();
		InvokeExpr invokeExpr = Jimple.v().newStaticInvokeExpr(generateCustomHashRef, HashFunParameter);
		AssignStmt assStmt = Jimple.v().newAssignStmt(temp$0, invokeExpr);
		units.add(assStmt); 
		
		Local hashvalue = Jimple.v().newLocal("hashvalue", IntType.v());
		body.getLocals().add(hashvalue);
		assStmt = Jimple.v().newAssignStmt(hashvalue,temp$0);
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
		
		
		createNewConstructor(sootClass,newConstInvokationType,constructorCount);
		
			
	
		SootMethodRef initMethodRef = Scene.v().makeConstructorRef(sootClass, newConstInvokationType);
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
	
	private void createNewConstructor(SootClass sootClass,List<Type> argumentType,int constructorCount) {
		String MethodName = "<init>";
		SootMethod createObjectMethod = new SootMethod(MethodName, argumentType, VoidType.v() , Modifier.PUBLIC );
		sootClass.addMethod(createObjectMethod);
		
		JimpleBody body = Jimple.v().newBody(createObjectMethod);
		createObjectMethod.setActiveBody(body);
		PatchingChain<Unit> units = body.getUnits();
		
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
		
		
		Local thisLocal = Jimple.v().newLocal("this", sootClass.getType());
	    body.getLocals().add(thisLocal);
	    units.add(Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(sootClass.getType())));
		
		
		
		if(!isJDKClass(parentClass))
		{
			
	        SootMethodRef generateCustomHashRef = parentClass.getMethod("<init>", superType).makeRef();
			InvokeExpr invokeExpr = Jimple.v().newSpecialInvokeExpr(thisLocal,generateCustomHashRef,superArgs);
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
		
		ReturnStmt returnStmt = Jimple.v().newReturnStmt(NullConstant.v());
		units.add(returnStmt);
		
		
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
