package playWithSoot;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.InterpolationContext;

import equivalence.PairDAG;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PackManager;
import soot.PrimType;
import soot.RefLikeType;
import soot.RefType;
import soot.SootMethod;
import soot.Transform;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.baf.WordType;
import soot.jimple.AssignStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.StringConstant;
import soot.jimple.internal.JimpleLocal;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;

public class testString {
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
				stores.put(methodSig, body);

			}
		}));
		soot.Main.main(sootArgs);
		ExceptionalUnitGraph cfg=new ExceptionalUnitGraph(stores.get("<toy_benchmark.testString: void main(java.lang.String[])>"));
		List<Unit> heads =cfg.getHeads();
		List<Unit> next=cfg.getUnexceptionalSuccsOf(heads.get(0));
		next=cfg.getUnexceptionalSuccsOf(next.get(0));
		Unit printString=next.get(0);
		InvokeStmt iStmt=(InvokeStmt) printString;
		Value returnValue=iStmt.getInvokeExpr().getArg(0);
		Type valueType=returnValue.getType();
		if (valueType instanceof PrimType) {
			System.out.println("PrimType");
		}
		if (valueType instanceof RefLikeType) {
			System.out.println("RefLikeType");
		}
	}

}
