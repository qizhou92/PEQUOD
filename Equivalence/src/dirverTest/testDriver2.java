package dirverTest;

import java.io.FileWriter;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.PackManager;
import soot.SootMethod;
import soot.Transform;
import soot.options.Options;

public class testDriver2 {
	static Map<String, Body> stores = new HashMap<String, Body>();
	static Body reference;
	static Body rightBody;
	public static void main(String[] args) throws IOException, InterruptedException {
		String Name=args[1];
		Options.v().set_src_prec(Options.src_prec_c);
		Options.v().set_output_format(Options.output_format_jimple);
		Options.v().set_allow_phantom_refs(true);
		String output = args[0];
		String[] sootArgs = new String[] { "-process-dir", "abc", "-output-dir", output };
		PackManager.v().getPack("jtp").add(new Transform("jtp.sim-itps1", new BodyTransformer() {

			@Override
			protected void internalTransform(Body body, String phaseName, Map<String, String> options) {
				// hack here
				SootMethod method = body.getMethod();
				String methodSig = method.getSignature();
				System.out.println(methodSig);
				if ((!methodSig.contains("<init>")) && (!methodSig.contains("<clinit>"))) {
					if(methodSig.contains(Name)){
						rightBody=body;
					}
					stores.put(methodSig, body);
				}
				if (methodSig.equals("<add: void main(java.lang.String[])>")) {
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
		System.out.println(Name);
		try {
			Test at = new Test(reference, rightBody, Name, pw_equivalent, pw_notEquivalent);
			at.start();
			at.join(400000);
			if (at.isAlive()) {
				at.stop();
				at.destroy();
			}
			Thread.sleep(20);
		} finally {
		}
		pw_equivalent.close();
		pw_notEquivalent.close();
	}
}
