package dirverTest;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import soot.Body;
import soot.BodyTransformer;
import soot.PackManager;
import soot.SootMethod;
import soot.Transform;
import soot.options.Options;

public class convert {
	static Map<String, Body> stores = new HashMap<String, Body>();
	public static void main(String[] args) throws IOException {
		Options.v().set_src_prec(Options.src_prec_c);
		Options.v().set_output_format(Options.output_format_jimple);
		Options.v().set_allow_phantom_refs(true);
		String input=args[0];
		String outputFolder=input+"/output";
		String[] sootArgs = new String[] { "-process-dir", input,
				"-output-dir",outputFolder };
		PackManager.v().getPack("jtp").add(new Transform("jtp.sim-itps1", new BodyTransformer() {

			@Override
			protected void internalTransform(Body body, String phaseName, Map<String, String> options) {
				// hack here
				SootMethod method = body.getMethod();
				String methodSig = method.getSignature();
				System.out.println(methodSig);
				if ((!methodSig.contains("<init>"))&&(!methodSig.contains("<clinit>"))) {
					stores.put(methodSig, body);
				}

			}
		}));
		soot.Main.main(sootArgs);
		String output=args[1];
		FileWriter fw_equivalent = new FileWriter(output, true);
		PrintWriter pw_equivalent = new PrintWriter(fw_equivalent);
		for(Entry<String,Body> e :stores.entrySet()){
			String signature=e.getKey();
			pw_equivalent.println(signature);
		}
		pw_equivalent.close();
	}
}
