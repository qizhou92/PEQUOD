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

public class directTest {
	static Map<String, Body> stores = new HashMap<String, Body>();
	static Body reference;
	static Body rightBody;
	public static void main(String[] args) throws IOException, InterruptedException {
		Options.v().set_src_prec(Options.src_prec_c);
		Options.v().set_output_format(Options.output_format_jimple);
		Options.v().set_allow_phantom_refs(true);
		String input=args[0];
		String output=args[1];
		String referenceSignature=args[2];
		String bodySignature=args[3];
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
		String outputEquivalent = output + "/equivalence.txt";
		String outputNotEquivalent = output + "/NotEquivalence.txt";
		FileWriter fw_equivalent = new FileWriter(outputEquivalent, true);
		PrintWriter pw_equivalent = new PrintWriter(fw_equivalent);
		FileWriter fw_notEquivalent = new FileWriter(outputNotEquivalent, true);
		PrintWriter pw_notEquivalent = new PrintWriter(fw_notEquivalent);
		long startTime = System.currentTimeMillis();
		ExceptionalUnitGraph cfgLeft = new ExceptionalUnitGraph(reference);
		ExceptionalUnitGraph cfgRight = new ExceptionalUnitGraph(rightBody);
		PairDAG theSolver = new PairDAG(cfgLeft, cfgRight, "test",true);
		try {
			if (theSolver.isEquivalent()) {
				long endTime = System.currentTimeMillis();
				long totalTime = endTime - startTime;
				pw_equivalent.println(referenceSignature + ";" + bodySignature + ";" + totalTime);
				pw_equivalent.flush();
				InterpolationContext ictx = theSolver.getIctx();
				ictx.dispose();
			} else {
				long endTime = System.currentTimeMillis();
				long totalTime = endTime - startTime;
				pw_notEquivalent.println(referenceSignature + ";" + bodySignature + ";" + totalTime);
				pw_notEquivalent.flush();
				InterpolationContext ictx = theSolver.getIctx();
				ictx.dispose();
			}
		} catch (IOException e) {
			System.exit(0);
		}
		pw_equivalent.close();
		pw_notEquivalent.close();
	}
}
