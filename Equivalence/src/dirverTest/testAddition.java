package dirverTest;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.InterpolationContext;
import com.microsoft.z3.Model;

import equivalence.PairDAG;
import soot.Body;
import soot.BodyTransformer;
import soot.PackManager;
import soot.SootMethod;
import soot.Transform;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;

public class testAddition {
	static Map<String, Body> stores = new HashMap<String, Body>();

	public static void main(String[] args) throws IOException {
		Options.v().set_src_prec(Options.src_prec_c);
		Options.v().set_output_format(Options.output_format_jimple);
		Options.v().set_allow_phantom_refs(true);
		String[] sootArgs = new String[] { "-process-dir", "/Users/qizhou/Documents/workspace/toy_benchmark/bin",
				"-output-dir", "src/output/toy_benchmark" };
		PackManager.v().getPack("jtp").add(new Transform("jtp.sim-itps1", new BodyTransformer() {

			@Override
			protected void internalTransform(Body body, String phaseName, Map<String, String> options) {
				// hack here
				SootMethod method = body.getMethod();
				String methodSig = method.getSignature();
				System.out.println(methodSig);
				/* System.out.println(method.getName()); */
				if (!methodSig.contains("<init>")) {
					stores.put(methodSig, body);
				}

			}
		}));
		soot.Main.main(sootArgs);
		System.out.println(stores.size());
		ExceptionalUnitGraph cfgLeft = new ExceptionalUnitGraph(
				stores.get("<toy_benchmark.add: void main(java.lang.String[])>"));
		ExceptionalUnitGraph cfgRight = new ExceptionalUnitGraph(
				stores.get("<toy_benchmark.add: void main(java.lang.String[])>"));
		PairDAG theSolver = new PairDAG(cfgLeft, cfgRight, "test");
		if (theSolver.isEquivalent()) {
			System.out.println("this two program are equivalent");
		} else {
			Model notCorrectModel = theSolver.getWrongModel();
			System.out.println(notCorrectModel);
			System.out.println("this two program are not equivalent");
		}
		System.out.println("this two program should be equivalent");
	}
}
