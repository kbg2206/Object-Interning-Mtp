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


public class InterningClass extends SceneTransformer{
	List<SootClass> allClasses = new ArrayList<>();
	HashSet<SootClass> constantClass = new HashSet<>();
	HashSet<SootClass> notAConstantClass = new HashSet<>();
	private Map<String, List<String>> adjacencyList = new HashMap<>();
	
	
	@Override
	protected synchronized void internalTransform(String phaseName, Map<String, String> options) {
		findAllClasses();
		SootClass dummyClass = new SootClass("Dummy", Modifier.PUBLIC);
		Scene.v().addClass(dummyClass);  

		dummyClass.setApplicationClass(); 

		System.out.println(allClasses.size()+" Classes based on hierarchy " + allClasses);
		findAllConstantClasses(allClasses);

		System.out.println(constantClass.size()+" Constant classes " + constantClass);
		
		for(SootClass sootClass: allClasses) {
			
			SootMethod method = new SootMethod(
			        "SuperHashCode",
			        new ArrayList<>(),         // No parameters
			        IntType.v(),              // Return type: int
			        Modifier.PUBLIC           // Public, non-static
			    );
			
			sootClass.addMethod(method);
			
		    JimpleBody body = Jimple.v().newBody(method);
		    method.setActiveBody(body);

		    Local thisLocal = Jimple.v().newLocal("this", RefType.v(sootClass.getName()));
		    body.getLocals().add(thisLocal);

		   
		    body.getUnits().add(Jimple.v().newIdentityStmt(
		        thisLocal, Jimple.v().newThisRef(RefType.v(sootClass.getName()))
		    ));

		    body.getUnits().add(Jimple.v().newReturnStmt(IntConstant.v(42)));
		}
		
		
		for(SootClass sootClass : constantClass){
			Scene.v().loadClassAndSupport(sootClass.toString());
			sootClass.setApplicationClass();
			String[] classList = sootClass.toString().split("\\.");
			String className = classList[classList.length-1];
			overwriteEqualsMethod(sootClass.toString());
			addStaticFieldInClass(sootClass.toString());
			createGenerateCustomHashMethod(sootClass);
			createHashVfunction(sootClass);
			//				ProgramCreation(sootClass,className);
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
		
		SootClass parentClass = targetClass.getSuperclass();
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

	public void findAllClasses(){
		Chain <SootClass> classes = Scene.v().getApplicationClasses(); 	
		List <SootClass> listClasses = new ArrayList <>(classes); 
		
		for(SootClass c: listClasses) {
			if(!c.isLibraryClass() && !isJDKClass(c) && !c.isInterface() && !c.isAbstract()) {
				allClasses.add(c);
			}
		}
		
		
		for (SootClass sootClass : allClasses) {
			
            addClass(sootClass.getName());

            if (sootClass.hasSuperclass()) {
                SootClass parent = sootClass.getSuperclass();
                if(!parent.isLibraryClass() && !isJDKClass(parent) && !parent.isInterface())
                addRelationship(parent.getName(), sootClass.getName());
            }

        }
		
        
        
        
        
	}
	
	public static boolean isJDKClass(SootClass sootClass) {
	    String[] libraryPrefixes = {
	        "java.", 
	        "javax.", 
	        "jdk.", 
	        "org.apache.", 
	        "org.dacapo.",
	        "com.google.", 
	        "com.typesafe", 
	        "org.springframework.", 
	        "com.fasterxml.", 
	        "org.hibernate.",
	        "soot",
	        "sun",
	        "cck",
	        "scala",
	        "scopt"
	        
	    };
	    
	    String packageName = sootClass.getPackageName();

	    for (String prefix : libraryPrefixes) {
	    	if (packageName.startsWith(prefix) || sootClass.toString().startsWith(prefix)) {
	    		return true;
	    	}
	    }
	    return false;

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
		if(parentClass.toString().equals("java.lang.Object")==false && isJDKClass(parentClass) || parentClass.isAbstract()) {
			constantClassDfs(sootClass);
		}
		
	}

	public void solve(SootClass className) {
		
		if(isJDKClass(className)) return ;
		
		for(SootMethod method :className.getMethods()) {
			
			
			if(!method.hasActiveBody()) continue;
			
			if(method.isStaticInitializer()) continue;
			
			if(method.isAbstract()) continue;
			
			
			
			if(method.isConstructor()) {
				
				Body body = method.retrieveActiveBody();
				HashSet<Local> localToThisRefMap = new HashSet<>();
				for(Unit unit:body.getUnits()) {
					Stmt stmt = (Stmt) unit;
					if (stmt instanceof IdentityStmt) { 
		                IdentityStmt identityStmt = (IdentityStmt) stmt;
		                if (identityStmt.getRightOp() instanceof ThisRef) {
		                    localToThisRefMap.add((Local) identityStmt.getLeftOp());
		                }
		            }
				}
				
				
				
				
				for(Unit unit:body.getUnits()) {
					Stmt stmt = (Stmt) unit;
					if(stmt instanceof AssignStmt) {
						AssignStmt assignStmt = (AssignStmt) stmt;
						
					}
				}
			}
			else {
				Body body = method.retrieveActiveBody();
				for(Unit unit:body.getUnits()) {
					Stmt stmt = (Stmt) unit;
					if(stmt instanceof AssignStmt) {
						AssignStmt assignStmt = (AssignStmt) stmt;
						
						if (assignStmt.getLeftOp() instanceof FieldRef) {
							FieldRef fieldRef = (FieldRef) assignStmt.getLeftOp();
							SootField field = fieldRef.getField();
							SootClass declaringClass = field.getDeclaringClass();
							
							if(!isJDKClass(declaringClass) && !notAConstantClass.contains(declaringClass)&& allClasses.contains(declaringClass)) {
								constantClassDfs(declaringClass);
							}
							
						}
					}
				}
			}
			
			
			
			
		}
		
	}
	
	public void constantClassDfs(SootClass sootClass)
	{
		notAConstantClass.add(sootClass);
		for(String it : adjacencyList.get(sootClass.toString()))
		{
			SootClass Node = Scene.v().getSootClass(it);
			if(!notAConstantClass.contains(Node)) {

				constantClassDfs(Node);
			}
					
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
}
