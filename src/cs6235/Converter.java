
package cs6235;

import soot.*;
import soot.options.Options;
import soot.util.Chain;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.List;

public class Converter {

    public static void main(String[] args) throws IOException {

        // Set up the Soot options
        String[] mainArgs = getOptions(args);

        // Add a transform to analyze and print out classes
        PackManager.v().getPack("wjtp").add(new Transform("wjtp.myTransform", new SceneTransformer() {
            @Override
            protected void internalTransform(String phaseName, java.util.Map<String, String> options) {
                for (SootClass sootClass : Scene.v().getApplicationClasses()) {
                    try {
                        // Print the Java-like representation to a file
                        printSootClass(sootClass, "generatedJavaCode/" + sootClass.getName() + ".txt");
                    } catch (Exception e) {
                        e.printStackTrace();
                    }
                }
            }
        }));

        // Run Soot
        soot.Main.main(mainArgs);
    }

    // Function to get Soot options
    static String[] getOptions(String args[]) {
        String classPath = "tests";
        String argumentClass = "Input9";

        String[] mainArgs = {
                "-pp",
                "-cp", classPath,
                "-w",
                "-app",
                "-p", "jb", "use-original-names:true",
                "-p", "cg.spark", "enabled:true,on-fly-cg:true,apponly:true",
                "-src-prec", "jimple",
                "-f", "jimple",
                argumentClass
        };
        return mainArgs;
    }

    // Function to print SootClass to file
    static void printSootClass(SootClass sootClass, String filePath) throws IOException {
        File outputDir = new File("generatedJavaCode");
        if (!outputDir.exists()) {
            outputDir.mkdirs();
        }
        File outputFile = new File(filePath);

        // Create a PrintWriter to write to the file
        try (PrintWriter writer = new PrintWriter(new FileWriter(outputFile))) {
            // Print the class declaration
            writer.println("Class: " + sootClass.getName());

            // Print the fields of the class
            Chain<SootField> fields = sootClass.getFields();
            for (SootField field : fields) {
                writer.println("Field: " + field.getName() + " " + field.getType());
            }

            // Print the methods of the class
            List<SootMethod> methods = sootClass.getMethods();
            for (SootMethod method : methods) {
                writer.println("Method: " + method.getName());
                try {
                    writer.println(method.retrieveActiveBody().toString());
                } catch (RuntimeException e) {
                    writer.println("Unable to retrieve body for method: " + method.getName());
                }
            }
        }

        System.out.println("Class written to: " + outputFile.getAbsolutePath());
    }
}
