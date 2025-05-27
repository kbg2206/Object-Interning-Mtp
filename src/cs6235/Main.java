package cs6235;

import java.util.Arrays;
import soot.Body;
import soot.PackManager;
import soot.Scene;
import soot.SootMethod;
import soot.Transform;

public class Main {
	public static void main (String [] args) {
		String classPath = "tests";
		String mainClass = "Main";
		
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


		
		System.out.println("The soot arguments are " + Arrays.toString(sootArgs));
		//System.setProperty("java.class.path", classPath);
		DummyAnalysis da = new DummyAnalysis();
		PackManager.v().getPack("wjtp").add(new Transform("wjtp.da", da));
		
		soot.Main.main(sootArgs);
		
		
	}
}
