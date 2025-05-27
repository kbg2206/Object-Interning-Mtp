package cs6235;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import soot.Body;
import soot.Local;
import soot.RefLikeType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.BlockGraph;
import soot.toolkits.graph.BriefBlockGraph;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;

public class DummyAnalysis extends SceneTransformer {

	@Override
	protected void internalTransform(String arg0, Map<String, String> arg1) {
		System.out.println("hello from Dummy Analysis");
		
		
		SootClass mainClass = Scene.v().getMainClass();
		SootMethod mainMethod = mainClass.getMethodByName("main");
		
		//System.out.println(mainMethod);
		//System.out.println("************************");

		System.out.println(mainMethod.getActiveBody());
		System.out.println("************************");

		//System.out.println(mainMethod.getActiveBody().getLocals());
		
		System.out.println("************************");
		//iterating over the "units" of the main method's body in some naive order
		for(Unit unit : mainMethod.getActiveBody().getUnits()) {
			System.out.println("now processing :" +unit);
			
			Stmt stmt = (Stmt) unit;
			
			if(stmt instanceof DefinitionStmt) {
				DefinitionStmt ds = (DefinitionStmt) stmt;
				Value lhs = ds.getLeftOp();
				Value rhs = ds.getRightOp();
				System.out.println("lhs " + lhs + " rhs " + rhs);
				
				if(lhs.getType() instanceof RefLikeType) {
					
					if(lhs instanceof InstanceFieldRef || lhs instanceof ArrayRef) {
						//Q1. if control is here, what can you say about rhs?
						//rhs HAS to be a ref type
						//rhs HAS to be either a local or a constant
						if(rhs instanceof Local) {
							//if control is inside here
							//ex: x.f = y
							//also called a store statement
							System.out.println("we know how to handle a store statement");
							InstanceFieldRef i = (InstanceFieldRef) lhs;
							
							System.out.println("Receiver is " + i.getBase() + " and field is " + i.getField());
							
							
							
							
						} else if (rhs instanceof Constant) {
							// something similar;
						}
					}
					
					
				} else {
					//lhs is a scalar, do something
				}
				
				
			} else if (stmt instanceof InvokeStmt) {
				
			} else if (stmt instanceof ReturnStmt) {
				
			} else {
				System.out.println("I do not care about this statement");
			}
			
			
		}
		
		System.out.println("************************");
		
		System.out.println("printing statements of the method in program order (or a naive order)");
		for(Unit unit : mainMethod.getActiveBody().getUnits()) {
			System.out.println(unit);
		}

		System.out.println("************************");
		
		//exercise - explore what other forms/kinds of CFGs are available via Soot
		//obtain the CFG
		UnitGraph cfg = new BriefUnitGraph(mainMethod.getActiveBody());
		
		//obtain the head(s) of the method
		List<Unit> heads = cfg.getHeads();
		
		Unit head = heads.get(0);
		
		Stack<Unit> stack = new Stack<Unit>();
		
		//'visited' array
		
		//add the entry node to the stack
		stack.add(head);
		
		while(!stack.isEmpty()) {
			Unit unitToProcess = stack.pop();
			//handle/process/apply-transfer-function
			System.out.println(unitToProcess);
			
			//if required - mark node as visited
			//if NOT current result same as previous iteration result
			
			//obtain the Control-Flow successors of unitToProcess
			List<Unit> successors = cfg.getSuccsOf(unitToProcess);
			List<Unit> predecessors = cfg.getPredsOf(unitToProcess);
			System.out.println("\t" + unitToProcess + " has " + successors.size() + " successors");
			System.out.println("\t" + unitToProcess + " has " + predecessors.size() + " predecessors");
			
			
			
			
			Stmt stmt = (Stmt) unitToProcess;
			if(stmt instanceof InvokeStmt) {
				//we want to find the possible targets for the method invocation
				CallGraph cg = Scene.v().getCallGraph();
				//where is this method defined? answer is not needed
				//what are the 'targets' of this invocation?
				Iterator<Edge> targetEdges = cg.edgesOutOf(unitToProcess);
				//in the call graph, if you have an edge of the form src->tgt
				
				int targetsCount = 0;
				while(targetEdges.hasNext()) {
					Edge targetEdge = targetEdges.next();
					System.out.println(targetEdge.getTgt());
					targetsCount++;
					
				}
				
				System.out.println(unitToProcess + " has " + targetsCount + " targets");
				
				
			}
			
			
			
			
			
			
			
			//add these successors to the stack
			stack.addAll(successors);
		}
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		System.out.println("************************");
		
		
	}
}