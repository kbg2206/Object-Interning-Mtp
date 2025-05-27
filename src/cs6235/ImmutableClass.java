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


public class ImmutableClass extends SceneTransformer{
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
		
		
		for(SootMethod method:className.getMethods()) {

			if (method.isJavaLibraryMethod() || method.isStaticInitializer() || method.isNative() || method.isAbstract()) {
				continue;
			}
			
			
			if(method.isConstructor()){
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
					if (stmt.containsInvokeExpr() ) { 
						
						InvokeExpr invokeExpr = stmt.getInvokeExpr();
						
						
				    	if (invokeExpr instanceof InstanceInvokeExpr || invokeExpr instanceof StaticInvokeExpr) {
				    		
				    		
				    		InstanceInvokeExpr instanceInvokeExpr;
				    		StaticInvokeExpr staticInvokeExpr;
				    		List<Value> args ;
				    				
				    				
				    		if(invokeExpr instanceof InstanceInvokeExpr) {		
				    			instanceInvokeExpr = (InstanceInvokeExpr) invokeExpr;
				    			args = instanceInvokeExpr.getArgs();;
				    			Value base = instanceInvokeExpr.getBase();  	
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
							if(!isJDKClass(declaringClass) && !notAConstantClass.contains(declaringClass) && allClasses.contains(declaringClass))
								constantClassDfs(declaringClass);
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
