package cs6235;

import java.util.Iterator;
import java.util.Map;

import soot.*;
import soot.jimple.Stmt;

public class TestSoot extends BodyTransformer {
	public static void main(String[] args)	{

		
		String classPath = "tests";
		String mainClass = "HelloThread";
		
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

		
		
		TestSoot analysis = new TestSoot();
	    PackManager.v().getPack("jtp").add(new Transform("jtp.TestSoot", analysis));
	    soot.Main.main(sootArgs);
	    //PackManager.v().runPacks();
	}

	@Override
	protected void internalTransform(Body b, String phaseName,
		Map<String, String> options) {

		Iterator<Unit> it = b.getUnits().snapshotIterator();
	    while(it.hasNext()){
	    	Stmt stmt = (Stmt)it.next();

	    	System.out.println(stmt);
	    }
	}
}