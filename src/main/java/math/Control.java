package math;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static math.Parse.parseFile;
import static math.Util.*;

/*
 *    Front end to display data from Rest endpoint for FXXXX in list. 
 */

public class Control {

    static boolean LINKED_INSTANCES = true;
    static long START = time();
    static String focus__debug = "";
    static int DEBUG_LEVEL = 0; //0 weak debug, 1 strong debug

    static String name = "GRPXX";
    static int numInstances = 2;
    static String executionBlock = "api";
    static Map<String, ExecutionControl> executionControls = createExecutionBlocks();

    static Map<String, ExecutionControl> createExecutionBlocks() {
        Map<String, ExecutionControl> blocks = new HashMap<>();
        blocks.put("s", new SingleX(name, numInstances));
        blocks.put("all", new AllX(numInstances));
        blocks.put("api", new APIX());
        return blocks;
    }

    public record SingleX (String name, int numInstances) implements ExecutionControl {
        public void execute() throws Exception {
            runDefinition(name, numInstances);
        }
    }

    public record APIX() implements ExecutionControl {
        public void execute() throws Exception {
            new ApiServer().run();
        }
    }

    public record AllX(int numInstances) implements ExecutionControl {
        public void execute() throws Exception {
            List<Def> defs = parseFile("pre.axiom");
            List<String> topLevelNames = defs.stream().filter(d -> d.name.endsWith("X")).map(d -> d.name()).toList();
            List<String> failedNames = new ArrayList<>();
            for (String name : topLevelNames) {
                try {
                    START = time();
                    runDefinition(name, numInstances);
                } catch (Exception e){
                    System.out.println("EXCEPTION RAISED FOR : " +  name);
                    e.printStackTrace();
                    failedNames.add(name);
                }
            }
            for (String failedName : failedNames) {
                System.out.println("EXCEPTION RAISED FOR : " +  failedName);
            }
        }
    }

    private static void runDefinition(String name, int numInstances) throws IOException {
        Def definition = new Compiler().compile(name, numInstances);
        while (definition.size() < V && time() - START < V) {
            Logic.run(definition);
            Build.run(definition);
        }
        Theorem.run(definition);
    }


    public interface ExecutionControl {
        void execute() throws Exception;
    }

    public static void main(String[] args) throws Exception {
        executionControls.get(executionBlock).execute();
        System.exit(0);
    }

}