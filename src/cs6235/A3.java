package cs6235;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import soot.PackManager;
import soot.Transform;
import soot.options.Options;

public class A3 {
    public static void main(String[] args) throws IOException {
        // Step 1: Read the class names from GoodClasses.txt
    	
    	
//    	System.out.println("Current working directory: " + System.getProperty("user.dir"));
        List<String> targetClasses = readClassNamesFromFile("/home/kushagra/MTP/mtp/Object-Interning-Mtp-main/src/GoodClasses.txt");

        if (targetClasses.isEmpty()) {
            System.out.println("No classes found in GoodClasses.txt.");
//            return;
        }

        String[] mainArgs = getOptions(args);

        try {
        	PackManager.v().getPack("wjtp").add(new Transform("wjtp.mymhp", new HashCodeUpdate(targetClasses)));
//        	PackManager.v().getPack("wjtp").add(new Transform("wjtp.mymhp", new InterningClass()));
        }
        catch(ArrayIndexOutOfBoundsException e){
        	System.out.println("Error during output generation.");
        	e.printStackTrace();
        }
        soot.Main.main(mainArgs);
    }

    private static List<String> readClassNamesFromFile(String filePath) {
        List<String> classNames = new ArrayList<>();
        try (BufferedReader br = new BufferedReader(new FileReader(filePath))) {
            String line;
            while ((line = br.readLine()) != null) {
                line = line.trim();
                if (!line.isEmpty()) {
                    classNames.add(line);
                }
            }
        } catch (IOException e) {
            System.err.println("Error reading GoodClasses.txt: " + e.getMessage());
        }
        return classNames;
    }

    static String[] getOptions(String args[]) {
        String classPath = "benchmark/h2_in";
        String argumentClass = "Harness";
        
//        Options.v().set_full_resolver(true);
//        Options.v().set_num_threads(1);



        String[] mainArgs = { 
        	    "-pp", 
        	    "-cp", classPath,
        	    "-process-dir", classPath,
        	    "-w",
        	    "-app",
        	    "-p", "jb", "use-original-names:true",         
        	    "-p", "jb.ule", "enabled:false",               
        	    "-p", "jb.uce", "enabled:false",               
        	    "-p", "jb.dae", "enabled:false",               
        	    "-p", "cg.spark", "enabled:true,on-fly-cg:true,apponly:true",
        	    "-src-prec", "class",
        	    "-allow-phantom-refs",
        	    "-debug",
        	    "-verbose", 
        	    "-f", "class",
        	    argumentClass  
        	};



        return mainArgs;
    }

}