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

public class mapFileToSignature {
	static Map<String, Body> stores = new HashMap<String, Body>();
	static String signature;
	public static void main(String[] args) throws IOException, InterruptedException {
		Options.v().set_src_prec(Options.src_prec_c);
		Options.v().set_output_format(Options.output_format_jimple);
		Options.v().set_allow_phantom_refs(true);
		String input=args[0];
		String outputfile=args[1];
		String foldername=args[2];
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
					signature=methodSig;
				}
			}
		}));
		soot.Main.main(sootArgs);
		FileWriter fw_write = new FileWriter(outputfile, true);
		PrintWriter pw_write = new PrintWriter(fw_write);
		pw_write.println(signature);
		pw_write.println(foldername);
		pw_write.close();
	}
}
