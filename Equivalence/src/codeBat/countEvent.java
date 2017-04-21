package codeBat;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.InterpolationContext;

import equivalence.PairDAG;
import soot.Body;
import soot.BodyTransformer;
import soot.PackManager;
import soot.SootMethod;
import soot.Transform;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;

public class countEvent {
	static Map<String,Body> stores=new HashMap<String,Body>();
	public static void main(String[] args) throws IOException {
		Options.v().set_src_prec(Options.src_prec_c);
		Options.v().set_output_format(Options.output_format_jimple);
		Options.v().set_allow_phantom_refs(true);
		String[] sootArgs = new String[] {
				"-process-dir",
				"/Users/qizhou/Documents/workspace/toy_benchmark/bin",
				"-output-dir", "src/output/toy_benchmark" };
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
		ExceptionalUnitGraph cfgLeft=new ExceptionalUnitGraph(stores.get("<toy_benchmark.countEvent: int countEvens1(int[])>"));
		ExceptionalUnitGraph cfgRight=new ExceptionalUnitGraph(stores.get("<toy_benchmark.countEvent: int countEvens2(int[])>"));
		PairDAG theSolver=new PairDAG(cfgLeft,cfgRight,"test");
		InterpolationContext ictx=theSolver.getIctx();
		BoolExpr extraPolicy=ictx.mkGe(ictx.mkIntConst("i0Path0Copy1Level0index0"), ictx.mkInt("2"));
		theSolver.addExtraPrePolicy(extraPolicy);
		if(theSolver.isEquivalent()){
			System.out.println("this two program are equivalent");
		}
		else{
			System.out.println("this two program are not equivalent");
		}
		System.out.println("this two program should be equivalent");
	}
}
