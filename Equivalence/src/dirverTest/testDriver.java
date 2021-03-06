package dirverTest;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Map;

import com.microsoft.z3.InterpolationContext;

import equivalence.PairDAG;
import soot.Body;
import soot.BodyTransformer;
import soot.PackManager;
import soot.SootMethod;
import soot.Transform;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;

public class TestDriver {
	static Map<String, Body> stores = new HashMap<String, Body>();
	static Body reference;
	static Body rightBody;
	public static void main(String[] args) throws IOException, InterruptedException {
		Options.v().set_src_prec(Options.src_prec_c);
		Options.v().set_output_format(Options.output_format_jimple);
		Options.v().set_allow_phantom_refs(true);
		String input=args[0];
		String referenceSignature=args[1];
		String bodySignature=args[2];
		String outputFolder=input+"/output";
		String[] sootArgs = new String[] { "-process-dir", input, "-output-dir", outputFolder };
		PackManager.v().getPack("jtp").add(new Transform("jtp.sim-itps1", new BodyTransformer() {

			@Override
			protected void internalTransform(Body body, String phaseName, Map<String, String> options) {
				// hack here
				SootMethod method = body.getMethod();
				String methodSig = method.getSignature();
				System.out.println(methodSig);
				if ((!methodSig.contains("<init>")) && (!methodSig.contains("<clinit>"))) {
					if(methodSig.contains(bodySignature)){
						rightBody=body;
					}
					stores.put(methodSig, body);
				}
				if (methodSig.contains(referenceSignature)||methodSig.equals(referenceSignature)) {
					reference = body;
				}

			}
		}));
		soot.Main.main(sootArgs);
		ExceptionalUnitGraph cfgLeft = new ExceptionalUnitGraph(reference);
		ExceptionalUnitGraph cfgRight = new ExceptionalUnitGraph(rightBody);
		PairDAG theSolver = new PairDAG(cfgLeft, cfgRight, "test",true);
		try {
			if (theSolver.isEquivalent()) {
				System.out.println("These two programs are equivalent");
			} else {
				System.out.println("These two programs are not equivalent");
			}
		} catch (IOException e) {
			System.out.println("Unexpected Errors");
			System.exit(0);
		}
	}
}
