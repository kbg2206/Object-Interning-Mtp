package cs6235;

import java.io.File;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import soot.*;
import soot.jimple.Stmt;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;


public class TestDominatorFinder extends BodyTransformer{
	public static void main(String[] args)	{

		String classPath = "tests";
		String mainClass = "GCD";
		
		String [] sootArgs = {
				"-v",
				"-cp", classPath,
				"-pp",
				"-w", /*"-app",*/
				"-p", "jb", "use-original-names:true",
				"-p", "cg.cha", "enabled:true",
				"-p", "cg.spark", "enabled:false",
				"-f", "J",
				//"-d", "output",
				mainClass
				
		};



	    TestDominatorFinder analysis = new TestDominatorFinder();
		PackManager.v().getPack("jtp").add(new Transform("jtp.A1TestDataFlowAnalysis", analysis));
		soot.Main.main(sootArgs);
		

	  
	}
	@Override
	protected void internalTransform(Body b, String phaseName,
		Map<String, String> options) {

	    UnitGraph g = new ExceptionalUnitGraph(b);
	    System.out.println(g);
	    DominatorFinder analysis = new DominatorFinder(g);
        Iterator it = b.getUnits().iterator();
        while (it.hasNext()){
            Stmt s = (Stmt)it.next();
            List dominators = analysis.getDominators(s);
            Iterator dIt = dominators.iterator();
            while (dIt.hasNext()){
                Stmt ds = (Stmt)dIt.next();
                String info = s+" is dominated by "+ds;
                System.out.println(info);

            }
        }
	}
}
