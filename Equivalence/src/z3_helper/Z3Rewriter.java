package z3_helper;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Map.Entry;
import java.util.Set;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.InterpolationContext;

import equivalence.Node;
import equivalence.PairDAG;
import equivalence.PairStep;

public class Z3Rewriter {
	private Set<Expr> terms;
	private Set<Expr> constantValues;
	private BoolExpr originalInterpolant;
	private BoolExpr currentInterpolant;
	private InterpolationContext ictx;
	private Map<Expr, ArrayList<Expr>> constantToTerm;
	private Set<Expr> visitedExpr;
	private boolean ifChanged;
	private PairDAG thePairDAG;
	private PairStep thisPairStep;
	private Set<PairStep> infeasibleFrontier;
	private boolean ifHasZero;
	private BoolExpr theSATformula;
	private Map<BoolExpr, Map<PairStep, BoolExpr>> correspondInterpolantResult;

	public Z3Rewriter(BoolExpr interpolant, PairDAG pDAG, PairStep p, Set<PairStep> infeasibleFrontier,
			BoolExpr theSatFormula) {
		this.theSATformula = theSatFormula;
		this.ifHasZero = false;
		this.thePairDAG = pDAG;
		this.thisPairStep = p;
		this.infeasibleFrontier = infeasibleFrontier;
		this.ifChanged = false;
		this.ictx = this.thePairDAG.getIctx();
		this.correspondInterpolantResult = new HashMap<BoolExpr, Map<PairStep, BoolExpr>>();
		BoolExpr theSimplifyInterpolants = Z3Utility.getSimplify(interpolant, this.ictx);
		this.originalInterpolant = theSimplifyInterpolants;
		this.originalInterpolant = (BoolExpr) this.normalizeExpr(theSimplifyInterpolants);
		//System.out.println("start collecting");
		this.visitedExpr = new HashSet<Expr>();
		this.terms = this.getAllVariable(this.originalInterpolant);
		this.visitedExpr = new HashSet<Expr>();
		this.constantValues = this.getAllIntConst(this.originalInterpolant);
		//System.out.println("finish collecting");
		this.originalInterpolant = this.elimiantedZero(this.originalInterpolant);
		this.currentInterpolant = this.originalInterpolant;
		//System.out.println("start collecting");
		this.visitedExpr = new HashSet<Expr>();
		this.terms = this.getAllVariable(this.originalInterpolant);
		this.visitedExpr = new HashSet<Expr>();
		//System.out.println("finish collecting");
		this.constantValues = this.getAllIntConst(interpolant);
		Map<Expr, Set<Expr>> constantValueToTerm = this.CalculateExprRelation();
		this.constantToTerm = new HashMap<Expr, ArrayList<Expr>>();
		for (Entry<Expr, Set<Expr>> constant : constantValueToTerm.entrySet()) {
			ArrayList<Expr> terms = new ArrayList<Expr>(constant.getValue());
			this.constantToTerm.put(constant.getKey(), terms);
		}
		/*
		 * Set<Expr> usedConstants=this.aggressiveSubstitution(); for(Expr
		 * usedConstant:usedConstants){
		 * this.constantToTerm.remove(usedConstant); }
		 */
		this.buildRelation();
	}

	public void buildRelation() {
		BoolExpr oldInterpolants = this.currentInterpolant;
		for (Entry<Expr, ArrayList<Expr>> constant : this.constantToTerm.entrySet()) {
			Expr value = constant.getKey();
			ArrayList<Expr> terms = constant.getValue();
			PriorityQueue<Set<Integer>> potentialEqualQueue = getAllPossibleSet(terms.size());
			while (!potentialEqualQueue.isEmpty()) {
				Set<Integer> allTermIndex = potentialEqualQueue.remove();
				Expr oneTerm = null;
				Set<Expr> allTerms = new HashSet<Expr>();
				for (Integer index : allTermIndex) {
					Expr term = terms.get(index);
					oneTerm = term;
					allTerms.add(term);
				}
				BoolExpr removeExprConstrains = (BoolExpr) this.removeExtraConstrains(oldInterpolants, allTerms, value);
				BoolExpr[] equalConstrains = new BoolExpr[allTerms.size()];
				int i = 0;
				for (Expr term : allTerms) {
					equalConstrains[i] = this.ictx.mkEq(oneTerm, term);
					i++;
				}
				BoolExpr allTermEqual = this.ictx.mkAnd(equalConstrains);
				BoolExpr newInterpolants = this.ictx.mkAnd(allTermEqual, removeExprConstrains);
				if (this.isNewInterpolantsValid(newInterpolants)) {
					this.ifChanged = true;
					oldInterpolants = newInterpolants;
					break;
				}

			}
		}
		this.currentInterpolant = oldInterpolants;
	}

	public boolean isCompareExpr(Expr e) {
		if (e.isEq()) {
			return true;
		}
		if (e.isGE()) {
			return true;
		}
		if (e.isGT()) {
			return true;
		}
		if (e.isLE()) {
			return true;
		}
		if (e.isLT()) {
			return true;
		}
		return false;
	}

	public Expr removeExtraConstrains(Expr e, Set<Expr> terms, Expr value) {
		if (this.isCompareExpr(e)) {
			Expr[] args = e.getArgs();
			Expr arg1 = args[0];
			Expr arg2 = args[1];
			if ((terms.contains(arg1)) && (arg2.equals(value))) {
				return ictx.mkTrue();
			}
			if ((terms.contains(arg2)) && (arg1.equals(value))) {
				return ictx.mkTrue();
			}
			return e;
		}
		int numberOfArgs = e.getNumArgs();
		if (numberOfArgs > 0) {
			if (e.isNot()) {
				Expr[] args = e.getArgs();
				Expr arg1 = args[0];
				Expr newExpr = this.removeExtraConstrains(arg1, terms, value);
				return this.ictx.mkNot((BoolExpr) newExpr);
			}
			if (e.isAnd()) {
				Expr[] args = e.getArgs();
				BoolExpr[] newArgs = new BoolExpr[args.length];
				for (int i = 0; i < args.length; i++) {
					Expr arg = args[i];
					newArgs[i] = (BoolExpr) this.removeExtraConstrains(arg, terms, value);
				}
				return this.ictx.mkAnd(newArgs);
			}
			if (e.isOr()) {
				Expr[] args = e.getArgs();
				BoolExpr[] newArgs = new BoolExpr[args.length];
				for (int i = 0; i < args.length; i++) {
					Expr arg = args[i];
					newArgs[i] = (BoolExpr) this.removeExtraConstrains(arg, terms, value);
				}
				return this.ictx.mkOr(newArgs);
			}
		}
		return e;
	}

	public static PriorityQueue<Set<Integer>> getAllPossibleSet(int bound) {
		Set<Integer> emptySet = new HashSet<Integer>();
		Comparator<Set<Integer>> setSizeComparator = new SetSizeComparator();
		PriorityQueue<Set<Integer>> possibleEqualTerm = new PriorityQueue<Set<Integer>>(100, setSizeComparator);
		Set<Set<Integer>> results = generatePermuateSet(0, bound, emptySet);
		for (Set<Integer> result : results) {
			if (result.size() > 1) {
				possibleEqualTerm.add(result);
			}
		}
		return possibleEqualTerm;
	}

	public static Set<Set<Integer>> generatePermuateSet(int next, int bound, Set<Integer> previousSet) {
		if (next >= bound) {
			Set<Set<Integer>> result = new HashSet<Set<Integer>>();
			result.add(previousSet);
			return result;
		} else {
			Set<Set<Integer>> result = new HashSet<Set<Integer>>();
			Set<Integer> newInSet = new HashSet<Integer>();
			newInSet.addAll(previousSet);
			newInSet.add(next);
			Set<Integer> newNotInSet = new HashSet<Integer>();
			newNotInSet.addAll(previousSet);
			Set<Set<Integer>> result1 = generatePermuateSet(next + 1, bound, newInSet);
			Set<Set<Integer>> result2 = generatePermuateSet(next + 1, bound, newNotInSet);
			result.addAll(result1);
			result.addAll(result2);
			return result;
		}
	}

	public Set<Expr> aggressiveSubstitution() {
		BoolExpr oldInterpolants = this.originalInterpolant;
		Set<Expr> usedConstant = new HashSet<Expr>();
		for (Entry<Expr, ArrayList<Expr>> constantValue : this.constantToTerm.entrySet()) {
			ArrayList<Expr> allTerms = constantValue.getValue();
			boolean thisConstantUsed = false;
			Expr value = constantValue.getKey();
			for (int i = 0; i < allTerms.size(); i++) {
				Expr term = allTerms.get(i);
				BoolExpr newInterpolants = (BoolExpr) oldInterpolants.substitute(value, term);
				if (this.isNewInterpolantsValid(newInterpolants)) {
					this.ifChanged = true;
					thisConstantUsed = true;
					oldInterpolants = newInterpolants;
					break;
				}
			}
			if (thisConstantUsed) {
				usedConstant.add(value);
			}
		}
		this.currentInterpolant = oldInterpolants;
		return usedConstant;
	}

	public boolean isNewInterpolantsValid(BoolExpr newInterpolants) {
		if (!Z3Utility.checkEntail(this.theSATformula, newInterpolants, this.ictx)) {
			return false;
		}
		return this.thePairDAG.IsInvariantValid(newInterpolants, this.thisPairStep, this.infeasibleFrontier);

	}

	public Map<Expr, Set<Expr>> CalculateExprRelation() {
		Map<Expr, Set<Expr>> result = new HashMap<Expr, Set<Expr>>();
		for (Expr constantValue : this.constantValues) {
			for (Expr term : this.terms) {
				BoolExpr variableEqualConstant = ictx.mkEq(constantValue, term);
				if (Z3Utility.checkEntail(this.theSATformula, variableEqualConstant, this.ictx)) {
					if (result.containsKey(constantValue)) {
						Set<Expr> equalVariables = result.remove(constantValue);
						if (!equalVariables.contains(term)) {
							equalVariables.add(term);
						}
						result.put(constantValue, equalVariables);
					} else {
						Set<Expr> equalVariables = new HashSet<Expr>();
						equalVariables.add(term);
						result.put(constantValue, equalVariables);
					}
				}
			}
		}
		return result;
	}

	public boolean ifNumberOperation(Expr e) {
		if ((e.getSort() instanceof IntSort) && (!e.isIntNum())) {
			return true;
		}
		return false;
	}

	public Set<Expr> getAllVariable(Expr e) {
		this.visitedExpr.add(e);
		Set<Expr> result = new HashSet<Expr>();
		if (e.getNumArgs() > 0 && (!e.isSelect())) {
			Expr args[] = e.getArgs();
			for (int i = 0; i < args.length; i++) {
				Expr subExpr = args[i];
				if (visitedExpr.contains(subExpr)) {
					continue;
				}
				Set<Expr> subResults = getAllVariable(subExpr);
				for (Expr subResult : subResults) {
					if (!result.contains(subResult)) {
						result.add(subResult);
					}
				}
			}
		}
		else if(e.isSelect()){
			Expr args[] = e.getArgs();
			Expr subExpr=args[1];
			if(!visitedExpr.contains(subExpr)){
				Set<Expr> subResults = getAllVariable(subExpr);
				for (Expr subResult : subResults) {
					if (!result.contains(subResult)) {
						result.add(subResult);
					}
				}
			}
		}
		if (ifNumberOperation(e)) {
			if (!result.contains(e)) {
				result.add(e);
			}
		}
		return result;
	}

	public Set<Expr> getAllIntConst(Expr e) {
		this.visitedExpr.add(e);
		Set<Expr> result = new HashSet<Expr>();
		if ((e.getNumArgs()) > 0 && (!e.isSelect())) {
			Expr args[] = e.getArgs();
			for (int i = 0; i < args.length; i++) {
				Expr subExpr = args[i];
				if (this.visitedExpr.contains(subExpr)) {
					continue;
				}
				Set<Expr> subResults = getAllIntConst(subExpr);
				for (Expr subResult : subResults) {
					if (!result.contains(subResult)) {
						result.add(subResult);
					}
				}
			}
		} else if (e.isSelect()) {
			Expr args[] = e.getArgs();
			Expr subExpr = args[1];
			if (!this.visitedExpr.contains(subExpr)) {

				Set<Expr> subResults = getAllIntConst(subExpr);
				for (Expr subResult : subResults) {
					if (!result.contains(subResult)) {
						result.add(subResult);
					}
				}
			}
		}
		if (e instanceof IntNum) {
			BigInteger bigInteger=((IntNum) e).getBigInteger();
			int value=bigInteger.intValue();
			if (value == 0) {
				this.ifHasZero = true;
			}
			if (!result.contains(e)) {
				result.add(e);
			}
		}
		return result;
	}

	public boolean isChanged() {
		return this.ifChanged;
	}

	public BoolExpr getNewInterpolants() {
		return this.currentInterpolant;
	}

	public Expr normalizeExpr(Expr e) {
		if (e.isEq()) {
			Expr[] args = e.getArgs();
			Expr arg1 = args[0];
			Expr arg2 = args[1];
			int arg1Type = typeOfNegative(arg1);
			int arg2Type = typeOfNegative(arg2);
			if ((arg1Type != 0) && (arg2.isIntNum())) {
				Expr newExpr = this.removeNegativeForBinary(arg1, arg1Type);
				if (arg1Type == 1) {
					int value = ((IntNum) arg2).getInt();
					return this.ictx.mkEq(newExpr, ictx.mkInt(-value));
				} else {
					return this.ictx.mkEq(newExpr, arg2);
				}
			}
			if ((arg2Type != 0) && (arg1.isIntNum())) {
				Expr newExpr = this.removeNegativeForBinary(arg2, arg2Type);
				if (arg2Type == 1) {
					int value = ((IntNum) arg1).getInt();
					return this.ictx.mkEq(newExpr, ictx.mkInt(-value));
				} else {
					return this.ictx.mkEq(newExpr, arg1);
				}
			}
			return e;
		}
		if (e.isGE()) {
			Expr[] args = e.getArgs();
			Expr arg1 = args[0];
			Expr arg2 = args[1];
			int arg1Type = typeOfNegative(arg1);
			int arg2Type = typeOfNegative(arg2);
			if ((arg1Type != 0) && (arg2.isIntNum())) {
				Expr newExpr = this.removeNegativeForBinary(arg1, arg1Type);
				if (arg1Type == 1) {
					int value = ((IntNum) arg2).getInt();
					return this.ictx.mkLe((ArithExpr) newExpr, ictx.mkInt(-value));
				} else {
					return this.ictx.mkGe((ArithExpr) newExpr, (ArithExpr) arg2);
				}
			}
			if ((arg2Type != 0) && (arg1.isIntNum())) {
				Expr newExpr = this.removeNegativeForBinary(arg2, arg2Type);
				if (arg2Type == 1) {
					int value = ((IntNum) arg1).getInt();
					return this.ictx.mkLe((ArithExpr) newExpr, ictx.mkInt(-value));
				} else {
					return this.ictx.mkGe((ArithExpr) newExpr, (ArithExpr) arg1);
				}
			}
			return e;
		}
		if (e.isGT()) {
			Expr[] args = e.getArgs();
			Expr arg1 = args[0];
			Expr arg2 = args[1];
			int arg1Type = typeOfNegative(arg1);
			int arg2Type = typeOfNegative(arg2);
			if ((arg1Type != 0) && (arg2.isIntNum())) {
				Expr newExpr = this.removeNegativeForBinary(arg1, arg1Type);
				if (arg1Type == 1) {
					int value = ((IntNum) arg2).getInt();
					return this.ictx.mkLt((ArithExpr) newExpr, (ArithExpr) ictx.mkInt(-value));
				} else {
					return this.ictx.mkGt((ArithExpr) newExpr, (ArithExpr) arg2);
				}
			}
			if ((arg2Type != 0) && (arg1.isIntNum())) {
				Expr newExpr = this.removeNegativeForBinary(arg2, arg2Type);
				if (arg2Type == 1) {
					int value = ((IntNum) arg1).getInt();
					return this.ictx.mkLt((ArithExpr) newExpr, (ArithExpr) ictx.mkInt(-value));
				} else {
					return this.ictx.mkGt((ArithExpr) newExpr, (ArithExpr) arg1);
				}
			}
			return e;
		}
		if (e.isLE()) {
			Expr[] args = e.getArgs();
			Expr arg1 = args[0];
			Expr arg2 = args[1];
			int arg1Type = typeOfNegative(arg1);
			int arg2Type = typeOfNegative(arg2);
			if ((arg1Type != 0) && (arg2.isIntNum())) {
				Expr newExpr = this.removeNegativeForBinary(arg1, arg1Type);
				if (arg1Type == 1) {
					int value = ((IntNum) arg2).getInt();
					return this.ictx.mkGe((ArithExpr) newExpr, (ArithExpr) ictx.mkInt(-value));
				} else {
					return this.ictx.mkLe((ArithExpr) newExpr, (ArithExpr) arg2);
				}
			}
			if ((arg2Type != 0) && (arg1.isIntNum())) {
				Expr newExpr = this.removeNegativeForBinary(arg2, arg2Type);
				if (arg2Type == 1) {
					int value = ((IntNum) arg1).getInt();
					return this.ictx.mkGe((ArithExpr) newExpr, (ArithExpr) ictx.mkInt(-value));
				} else {
					return this.ictx.mkLe((ArithExpr) newExpr, (ArithExpr) arg1);
				}
			}
			return e;
		}
		if (e.isLT()) {
			Expr[] args = e.getArgs();
			Expr arg1 = args[0];
			Expr arg2 = args[1];
			int arg1Type = typeOfNegative(arg1);
			int arg2Type = typeOfNegative(arg2);
			if ((arg1Type != 0) && (arg2.isIntNum())) {
				Expr newExpr = this.removeNegativeForBinary(arg1, arg1Type);
				if (arg1Type == 1) {
					int value = ((IntNum) arg2).getInt();
					return this.ictx.mkGt((ArithExpr) newExpr, (ArithExpr) ictx.mkInt(-value));
				} else {
					return this.ictx.mkLt((ArithExpr) newExpr, (ArithExpr) arg2);
				}
			}
			if ((arg2Type != 0) && (arg1.isIntNum())) {
				Expr newExpr = this.removeNegativeForBinary(arg2, arg2Type);
				if (arg2Type == 1) {
					int value = ((IntNum) arg1).getInt();
					return this.ictx.mkGt((ArithExpr) newExpr, (ArithExpr) ictx.mkInt(-value));
				} else {
					return this.ictx.mkLt((ArithExpr) newExpr, (ArithExpr) arg1);
				}
			}
			return e;
		}
		if (e.isOr()) {
			Expr[] args = e.getArgs();
			BoolExpr[] newArgs = new BoolExpr[args.length];
			for (int i = 0; i < args.length; i++) {
				newArgs[i] = (BoolExpr) this.normalizeExpr(args[i]);
			}
			return this.ictx.mkOr(newArgs);
		}
		if (e.isAnd()) {
			Expr[] args = e.getArgs();
			BoolExpr[] newArgs = new BoolExpr[args.length];
			for (int i = 0; i < args.length; i++) {
				newArgs[i] = (BoolExpr) this.normalizeExpr(args[i]);
			}
			return this.ictx.mkAnd(newArgs);
		}
		if (e.isNot()) {
			Expr[] args = e.getArgs();
			Expr theExpr = args[0];
			BoolExpr newExpr = (BoolExpr) this.normalizeExpr(theExpr);
			return this.ictx.mkNot(newExpr);
		}
		return e;
	}

	public int typeOfNegative(Expr e) {
		if (e.isAdd() && (e.getNumArgs() == 2)) {
			Expr[] args = e.getArgs();
			Expr arg1 = args[0];
			Expr arg2 = args[1];
			if (this.negativeExpr(arg1) && this.negativeExpr(arg2)) {
				return 1;
			}
			if (this.negativeExpr(arg1) && (!this.negativeExpr(arg2))) {
				return 2;
			}
			if ((!this.negativeExpr(arg1)) && (this.negativeExpr(arg2))) {
				return 3;
			} else {
				return 0;
			}
		}
		/*
		 * if(e.isSub()){ Expr[] args=e.getArgs(); Expr arg1=args[0]; Expr
		 * arg2=args[1]; if(this.negativeExpr(arg1)&&this.negativeExpr(arg2)){
		 * return 5; } if(this.negativeExpr(arg1)&&(!this.negativeExpr(arg2))){
		 * return 6; }
		 * if((!this.negativeExpr(arg1))&&(this.negativeExpr(arg2))){ return 7;
		 * } else{ return 0; } }
		 */
		return 0;
	}

	public Expr removeNegativeForBinary(Expr e, int code) {
		if (code == 1) {
			Expr[] args = e.getArgs();
			Expr arg1 = args[0];
			Expr arg2 = args[1];
			Expr newArg1 = this.removeNegative(arg1);
			Expr newArg2 = this.removeNegative(arg2);
			return this.ictx.mkAdd((ArithExpr) newArg1, (ArithExpr) newArg2);
		}
		if (code == 2) {
			Expr[] args = e.getArgs();
			Expr arg1 = args[0];
			Expr arg2 = args[1];
			Expr newArg1 = this.removeNegative(arg1);
			return this.ictx.mkSub((ArithExpr) arg2, (ArithExpr) newArg1);
		}
		if (code == 3) {
			Expr[] args = e.getArgs();
			Expr arg1 = args[0];
			Expr arg2 = args[1];
			Expr newArg2 = this.removeNegative(arg2);
			return this.ictx.mkSub((ArithExpr) arg1, (ArithExpr) newArg2);
		}
		System.err.println("there is an error in Z3Rewriter remove NegativeForBinary");
		return null;
	}

	public boolean negativeExpr(Expr e) {
		if (e.isMul()) {
			Expr[] args = e.getArgs();
			Expr arg1 = args[0];
			Expr arg2 = args[1];
			if ((arg1.isIntNum()) && (this.ifNumberOperation(arg2))) {
				int value = ((IntNum) arg1).getInt();
				if (value < 0) {
					return true;
				}
			}
			if ((arg2.isIntNum()) && (this.ifNumberOperation(arg1))) {
				int value = ((IntNum) arg2).getInt();
				if (value < 0) {
					return true;
				}
			}
		}
		return false;
	}

	public Expr removeNegative(Expr e) {
		if (e.isMul()) {
			Expr[] args = e.getArgs();
			Expr arg1 = args[0];
			Expr arg2 = args[1];
			if ((arg1.isIntNum()) && (this.ifNumberOperation(arg2))) {
				int value = ((IntNum) arg1).getInt();
				if (value < -1) {
					return this.ictx.mkMul(this.ictx.mkInt(-value), (ArithExpr) arg2);
				}
				if (value == -1) {
					return arg2;
				}
			}
			if ((arg2.isIntNum()) && (this.ifNumberOperation(arg1))) {
				int value = ((IntNum) arg2).getInt();
				if (value < -1) {
					return this.ictx.mkMul(this.ictx.mkInt(-value), (ArithExpr) arg1);
				}
				if (value == -1) {
					return arg1;
				}
			}
		}
		return e;
	}

	public BoolExpr getOriginalInterpolants() {
		return this.originalInterpolant;
	}

	public BoolExpr elimiantedZero(BoolExpr e) {
		if (this.ifHasZero) {
			Set<Expr> allTerms = this.terms;
			Set<Expr> equalZeroTerms = new HashSet<Expr>();
			Expr zero = this.ictx.mkInt(0);
			for (Expr term : allTerms) {
				if (term.isSub() && (term.getNumArgs() == 2)) {
					BoolExpr equalZero = this.ictx.mkEq(term, zero);
					if (Z3Utility.checkEntail(e, equalZero, ictx)) {
						equalZeroTerms.add(term);
					}
				}
			}
			BoolExpr newExpr = (BoolExpr) this.removeExtraConstrains(e, equalZeroTerms, zero);
			BoolExpr equalConstrains = this.generateEqualConstrains(equalZeroTerms);
			return this.ictx.mkAnd(newExpr, equalConstrains);
		}
		return e;
	}

	public BoolExpr generateEqualConstrains(Set<Expr> terms) {
		BoolExpr constrains = this.ictx.mkTrue();
		for (Expr term : terms) {
			Expr[] args = term.getArgs();
			BoolExpr newEqual = this.ictx.mkEq(args[0], args[1]);
			constrains = this.ictx.mkAnd(constrains, newEqual);
		}
		return constrains;
	}
}
