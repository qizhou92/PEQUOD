package playWithSoot;

import java.io.FileNotFoundException;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import equivalence.Node;
import soot.Body;
import soot.BodyTransformer;
import soot.PackManager;
import soot.SootMethod;
import soot.Transform;
import soot.Unit;
import soot.jimple.InvokeStmt;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;

public class TestObject {
	static Map<String, Body> stores = new HashMap<String, Body>();

	public static void main(String[] args) throws FileNotFoundException,
			UnsupportedEncodingException {
		Options.v().set_src_prec(Options.src_prec_c);
		Options.v().set_output_format(Options.output_format_shimple);
		Options.v().set_allow_phantom_refs(true);
		String[] sootArgs = new String[] { "-process-dir",
				"C:/Users/qizhou/workspace/toy_benchmark/bin", "-output-dir",
				"src/output" };
		PackManager.v().getPack("stp")
				.add(new Transform("stp.test", new BodyTransformer() {

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
		ExceptionalUnitGraph cfg=new ExceptionalUnitGraph(stores.get("<toy_benchmark.ToyBenchmark2: void test1()>"));
		List<Unit> heads =cfg.getHeads();
		List<Unit> next=cfg.getUnexceptionalSuccsOf(heads.get(0));
		Unit invok=next.get(0);
		System.out.println(invok);
		InvokeStmt a=(InvokeStmt) invok;
		int count=a.getInvokeExpr().getArgCount();
	}
}