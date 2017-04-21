package toy_test;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import equivalence.PairDAG;
import soot.Body;
import soot.BodyTransformer;
import soot.PackManager;
import soot.SootMethod;
import soot.Transform;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;

public class test10 {
	static Map<String,Body> stores=new HashMap<String,Body>();
	public static void main(String[] args) throws IOException {
		Options.v().set_src_prec(Options.src_prec_c);
		Options.v().set_output_format(Options.output_format_jimple);
		Options.v().set_allow_phantom_refs(true);
		String input=args[0];
		String output=args[1];
		String[] sootArgs = new String[] {
				"-process-dir",
				input,
				"-output-dir", output };
		PackManager.v().getPack("jtp").add(new Transform("jtp.sim-itps1", 
				new BodyTransformer(){

					@Override
					protected void internalTransform(Body body,
							String phaseName, Map<String, String> options) {
						// hack here
						SootMethod method = body.getMethod();
						String methodSig = method.getSignature();
						System.out.println(methodSig);
						/* System.out.println(method.getName()); */
						stores.put(methodSig, body);

					}
				}));
		soot.Main.main(sootArgs); 
		System.out.println(stores.size());
		ExceptionalUnitGraph cfgLeft=new ExceptionalUnitGraph(stores.get("<toy_benchmark.Test2: int main(int)>"));
		ExceptionalUnitGraph cfgRight=new ExceptionalUnitGraph(stores.get("<toy_benchmark.Test2: int main2(int)>"));
		PairDAG theSolver=new PairDAG(cfgLeft,cfgRight,output);
		if(theSolver.isEquivalent()){
			System.out.println("this two program are equivalent");
		}
		else{
			System.out.println("this two program are not equivalent");
		}
		System.out.println("this two program should not be equivalent");
	}
}
