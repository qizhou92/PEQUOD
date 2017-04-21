package z3_helper;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import com.microsoft.z3.ApplyResult;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Goal;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.InterpolationContext;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;
import com.microsoft.z3.Tactic;

public class Z3Utility {
	// Check if f1 entails f2.Since if f1 entails f2, it means that all T
	// satisfy f1 that
	// satisfy f2 ,which means no T satisfy f1 and not satisfy f2. In other
	// words,
	// f1 and ~f2 is unsatisfiable.
	public static boolean checkEntail(BoolExpr f1, BoolExpr f2, InterpolationContext ictx) {
		BoolExpr notF2 = ictx.mkNot(f2);
		BoolExpr f1EntailF2 = ictx.mkAnd(f1, notF2);
		Solver s = ictx.mkSolver();
		s.reset();
		s.add(f1EntailF2);
		Status result = s.check();
		if (result == Status.UNSATISFIABLE) {
			return true;
		} else {
			return false;
		}
	}

	// pairing function is a bijective function that map n*n -> n
	public static int pairingFunction(int a, int b) {
		int k1 = 0;
		int k2 = 0;
		if (a < b) {
			k1 = b;
			k2 = a;
		} else {
			k1 = a;
			k2 = b;
		}
		int sum1 = k1 + k2;
		int sum2 = k1 + k2 + 1;
		if ((sum1 % 2) == 0) {
			sum1 = sum1 / 2;
		} else {
			sum2 = sum2 / 2;
		}
		int result = sum1 * sum2 + k2;
		return result;
	}

	public static BoolExpr getSimplify(BoolExpr e, InterpolationContext ictx) {
		/*
		 * Tactic first=ictx.mkTactic("eq2ineq"); Goal g1=ictx.mkGoal(true,
		 * false, false); g1.add(e); ApplyResult c = first.apply(g1); Goal[]
		 * goals=c.getSubgoals(); BoolExpr e1=goals[0].AsBoolExpr();
		 */
		Params p = ictx.mkParams();
		p.add("eq2ineq", true);
		Expr afterSimplfy = e.simplify(p);
		p = ictx.mkParams();
		p.add("propagate-ineqs", true);
		afterSimplfy = afterSimplfy.simplify(p);
		Tactic tac2 = ictx.mkTactic("ctx-solver-simplify");
		Goal g2 = ictx.mkGoal(true, false, false);
		g2.add((BoolExpr) afterSimplfy);
		ApplyResult c = tac2.apply(g2);
		Goal[] goals = c.getSubgoals();
		BoolExpr e1 = goals[0].AsBoolExpr();
		Tactic tac3 = ictx.mkTactic("propagate-ineqs");
		g2 = ictx.mkGoal(true, false, false);
		g2.add(e1);
		c = tac3.apply(g2);
		goals = c.getSubgoals();
		BoolExpr e3= goals[0].AsBoolExpr();
		Tactic tactic3 = ictx.mkTactic("ctx-simplify");
		Goal g4 = ictx.mkGoal(true, false, false);
		g4.add((BoolExpr) e3);
		c = tactic3.apply(g4);
		goals = c.getSubgoals();
		return goals[0].AsBoolExpr();
	}
	public static boolean ifFalse(BoolExpr e,InterpolationContext ictx){
		Solver s=ictx.mkSolver();
		s.add(e);
		Status result=s.check();
		if(result==Status.UNSATISFIABLE){
			return true;
		}
		else{
			return false;
		}
	}
	//To do 
	public static boolean checkIfNonLinear(BoolExpr e){
		return true;
	}
}
