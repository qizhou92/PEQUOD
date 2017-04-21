package equivalence;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import org.jgraph.graph.DefaultEdge;
import org.jgrapht.ext.ComponentAttributeProvider;
import org.jgrapht.ext.DOTExporter;
import org.jgrapht.ext.IntegerNameProvider;
import org.jgrapht.ext.VertexNameProvider;
import org.jgrapht.graph.SimpleDirectedGraph;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.InterpolationContext;
import com.microsoft.z3.InterpolationContext.ComputeInterpolantResult;
import com.microsoft.z3.Model;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.enumerations.Z3_lbool;

import dot_output.edgeAttribute;
import dot_output.vertexAttribute;
import dot_output.vertexID;
import dot_output.vertexName2;
import dot_output.vertextName;
import soot.toolkits.graph.ExceptionalUnitGraph;
import z3_helper.PathCoverter;
import z3_helper.PathHelper;
import z3_helper.Z3Rewriter;
import z3_helper.Z3Utility;

public class PairDAG {
	private Queue<HyperEdge> currentHyperEdges;
	private PriorityQueue<HyperEdge> potentialHyperEdges;
	private PairStep EntryStep;
	private Node leftMost;
	private Node rightMost;
	private Node leftRoot;
	private Node rightRoot;
	private ExceptionalUnitGraph leftCFG;
	private ExceptionalUnitGraph rightCFG;
	private boolean isEquivalent;
	private PairStep root;
	private InterpolationContext ictx;
	private Map<Node, BoolExpr> leftPathZ3;
	private Map<Node, BoolExpr> rightPathZ3;
	private BoolExpr policy;
	private BoolExpr pre_policy;
	private Map<String, Set<PairStep>> UnitMapPairStep;
	private PathCoverter rightCoverter;
	private PathCoverter leftCoverter;
	private Set<HyperEdge> coveredEdge;
	private int outputNumber;
	private String outputDir;
	private Map<PairStep, Set<PairStep>> implication;
	private Map<PairStep, Boolean> safeResult;
	private Set<PairStep> updatedStep;
	private BoolExpr extraPrePolicy;
	private Model notCorrectModel;
	private Set<PairStep> allCreatedStep;

	public PairDAG(ExceptionalUnitGraph leftCFG, ExceptionalUnitGraph rightCFG, String outputDir) {
		this.allCreatedStep = new HashSet<PairStep>();
		this.outputDir = outputDir;
		this.ictx = new InterpolationContext();
		this.UnitMapPairStep = new HashMap<String, Set<PairStep>>();
		this.leftCFG = leftCFG;
		this.rightCFG = rightCFG;
		HelpTree leftHelpTree = new HelpTree(this.leftCFG);
		Node leftR = Node.getNewNode(leftHelpTree.getRoot(), null, leftHelpTree, this.leftCFG, true);
		leftR.setPoint();
		this.leftRoot = leftR;
		this.leftMost = leftR;
		HelpTree rightHelpTree = new HelpTree(this.rightCFG);
		Node rightR = Node.getNewNode(rightHelpTree.getRoot(), null, rightHelpTree, this.rightCFG, false);
		rightR.setPoint();
		this.rightRoot = rightR;
		this.rightMost = rightR;
		this.isEquivalent = true;
		this.currentHyperEdges = new LinkedList<HyperEdge>();
		PairStep r = PairStep.getNewPairStep(null, leftR, rightR, this);
		this.root = r;
		HyperEdge startHyperEdge = new HyperEdge(null);
		startHyperEdge.addLeftMain(r);
		startHyperEdge.addRightMain(r);
		Comparator<HyperEdge> HyperEdgeComparator = new HyperEdgeComparator();
		this.potentialHyperEdges = new PriorityQueue<HyperEdge>(100, HyperEdgeComparator);
		this.potentialHyperEdges.add(startHyperEdge);
		this.coveredEdge = new HashSet<HyperEdge>();
		this.implication = new HashMap<PairStep, Set<PairStep>>();
		this.outputNumber = 1;
		this.implication = new HashMap<PairStep, Set<PairStep>>();
	}

	public void insertNewGroupOfSteps(Set<HyperEdge> gSteps, PairStep parent) {
		this.updateLeftAndRightMost();
		for (HyperEdge gStep : gSteps) {
			if (isNextChoice(gStep, parent)) {
				if (!this.currentHyperEdges.contains(gStep)) {
					this.currentHyperEdges.add(gStep);
				}
			} else {
				if (!this.potentialHyperEdges.contains(gStep)) {
					this.potentialHyperEdges.add(gStep);
				}
			}
		}
	}

	public void addUnitMap(PairStep pStep) {
		String UnitId = pStep.getUnitId();
		if (this.UnitMapPairStep.containsKey(UnitId)) {
			Set<PairStep> SameUnitPairStep = this.UnitMapPairStep.remove(UnitId);
			SameUnitPairStep.add(pStep);
			this.UnitMapPairStep.put(UnitId, SameUnitPairStep);
		} else {
			Set<PairStep> SameUnitPairStep = new HashSet<PairStep>();
			SameUnitPairStep.add(pStep);
			this.UnitMapPairStep.put(UnitId, SameUnitPairStep);
		}
	}

	private boolean isNextChoice(HyperEdge gStep, PairStep parent) {
		int type = parent.getType();
		if (type == 1) {
			this.updateLeftAndRightMost();
			Set<Node> leftPath = leftMost.getPathSet();
			Set<Node> rightPath = rightMost.getPathSet();
			return gStep.isInPath(leftPath, rightPath);
		}
		return true;
	}

	private void updateLeftAndRightMost() {
		while (this.leftMost.isUnwind() && (!this.leftMost.isEntry())) {
			this.leftMost = this.leftMost.getShortestSuccessor();
		}
		while (this.rightMost.isUnwind() && (!this.rightMost.isEntry())) {
			this.rightMost = this.rightMost.getShortestSuccessor();
		}
	}

	// pre-condition: currentQueue is not empty
	private void unwindCurrent() {
		HyperEdge HyperEdge = this.currentHyperEdges.poll();
		/*
		 * if(HyperEdge.isCovered()){ System.out.println(
		 * "there are something error"); }
		 */
		HyperEdge.Unwind();
	}

	private void covertToZ3() {
		ArrayList<Node> leftPath = this.leftMost.getPath();
		PathCoverter LeftCoverter = new PathCoverter(0, 1, this.ictx, leftPath);
		PathHelper LeftHelper = new PathHelper(LeftCoverter, leftPath);
		ArrayList<BoolExpr> LeftPathZ3 = LeftHelper.ConvertToZ3();
		this.leftPathZ3 = new HashMap<Node, BoolExpr>();
		for (int i = 0; i < leftPath.size(); i++) {
			this.leftPathZ3.put(leftPath.get(i), LeftPathZ3.get(i));
			/*
			 * System.out.println("statment");
			 * System.out.println(leftPath.get(i).getStmt().toString());
			 * System.out.println("constrains");
			 * System.out.println(LeftPathZ3.get(i).toString());
			 */
		}
		ArrayList<Node> rightPath = this.rightMost.getPath();
		PathCoverter rightCoverter = new PathCoverter(1, 2, this.ictx, rightPath);
		PathHelper RightHelper = new PathHelper(rightCoverter, rightPath);
		ArrayList<BoolExpr> rightPathZ3 = RightHelper.ConvertToZ3();
		this.rightPathZ3 = new HashMap<Node, BoolExpr>();
		/*
		 * System.out.println("the right path"); for(int
		 * i=0;i<rightPath.size();i++){
		 * System.out.println(rightPath.get(i).getStmt().toString()); }
		 * System.out.println("right constrains");
		 */
		for (int i = 0; i < rightPath.size(); i++) {
			this.rightPathZ3.put(rightPath.get(i), rightPathZ3.get(i));
			// System.out.println(rightPathZ3.get(i).toString());
		}

		this.leftCoverter = LeftCoverter;
		this.leftCoverter.generateRename(true);
		this.rightCoverter = rightCoverter;
		this.rightCoverter.generateRename(false);
	}

	public void setEntryStep(PairStep pStep) {
		this.EntryStep = pStep;
	}

	public boolean refine() throws IOException {
		System.out.println("doing a refine");
		this.covertToZ3();
		this.generatePolicy();
		Map<BoolExpr, BoolExpr> NameToFormula = new HashMap<BoolExpr, BoolExpr>();
		int formulaCount = 1;
		for (Entry<Node, BoolExpr> e : this.leftPathZ3.entrySet()) {
			BoolExpr formula = e.getValue();
			if (!formula.isTrue()) {
				BoolExpr name = ictx.mkBoolConst("formula" + formulaCount);
				NameToFormula.put(name, formula);
				formulaCount++;
			}
		}
		for (Entry<Node, BoolExpr> e : this.rightPathZ3.entrySet()) {
			BoolExpr formula = e.getValue();
			if (!formula.isTrue()) {
				BoolExpr name = ictx.mkBoolConst("formula" + formulaCount);
				NameToFormula.put(name, formula);
				formulaCount++;
			}
		}
		int sizeOfFormula = NameToFormula.size();
		BoolExpr[] allFormula = new BoolExpr[sizeOfFormula+2];
		BoolExpr[] allName = new BoolExpr[sizeOfFormula+2];
		int count = 0;
		for (Entry<BoolExpr, BoolExpr> e : NameToFormula.entrySet()) {
			allFormula[count] = e.getValue();
			allName[count] = e.getKey();
			count++;
		}
		allFormula[count]=this.pre_policy;
		allName[count]=this.ictx.mkBoolConst("PrePolicy");
		count++;
		allFormula[count]=this.policy;
		allName[count]=this.ictx.mkBoolConst("PostPolicy");
		Solver s=ictx.mkSolver();
		s.reset();
		s.assertAndTrack(allFormula, allName);
		Status SolverResult =s.check();
		Set<BoolExpr> UnSatCoreFormula = new HashSet<BoolExpr>();
		if (SolverResult == Status.UNSATISFIABLE) {
			BoolExpr[] UnsatCoreName = s.getUnsatCore();
			for (int i = 0; i < UnsatCoreName.length; i++) {
				BoolExpr name = UnsatCoreName[i];
				UnSatCoreFormula.add(NameToFormula.get(name));
			}
		} else {
			System.out.println("there is a false");
			return false;
		}
		Map<Node, BoolExpr> LeftNewNodeToPath = new HashMap<Node, BoolExpr>();
		for (Entry<Node, BoolExpr> leftPathE : this.leftPathZ3.entrySet()) {
			BoolExpr formula = leftPathE.getValue();
			if (UnSatCoreFormula.contains(formula)) {
				LeftNewNodeToPath.put(leftPathE.getKey(), formula);
			} else {
				LeftNewNodeToPath.put(leftPathE.getKey(), this.ictx.mkTrue());
			}
		}
		this.leftPathZ3 = LeftNewNodeToPath;
		Map<Node, BoolExpr> RightNewNodeToPath = new HashMap<Node, BoolExpr>();
		for (Entry<Node, BoolExpr> rightPathE : this.rightPathZ3.entrySet()) {
			BoolExpr formula = rightPathE.getValue();
			if (UnSatCoreFormula.contains(formula)) {
				RightNewNodeToPath.put(rightPathE.getKey(), formula);
			} else {
				RightNewNodeToPath.put(rightPathE.getKey(), this.ictx.mkTrue());
			}
		}
		this.rightPathZ3 = RightNewNodeToPath;
		Set<PairStep> infeasibleSteps = calculateInfeasibleStep(this.EntryStep);
		// System.out.println("the size of infeasible
		// set:"+infeasibleSteps.size());
		Map<PairStep, BoolExpr> interpolantResult = new HashMap<PairStep, BoolExpr>();
		Queue<PairStep> refineStep = new LinkedList<PairStep>();
		refineStep.add(this.root);
		Set<PairStep> allStepsInDAG = this.EntryStep.CollecttParents();
		allStepsInDAG.add(this.EntryStep);
		// this.EntryStep.SetIsRefine();
		Set<PairStep> haveRefined = new HashSet<PairStep>();
		while (!refineStep.isEmpty()) {

			PairStep currentPairStep = refineStep.poll();
			currentPairStep.SetIsRefine();
			Set<PairStep> successors = currentPairStep.getSuccessors();
			for (PairStep successor : successors) {
				if ((!haveRefined.contains(successor)) && (allStepsInDAG.contains(successor))) {
					haveRefined.add(successor);
					refineStep.add(successor);
				}
			}
			if (infeasibleSteps.contains(currentPairStep)) {
				interpolantResult.put(currentPairStep, this.ictx.mkFalse());
				continue;
			}
			if (currentPairStep == this.root) {
				currentPairStep.SetIsRefine();
				BoolExpr sat_formula = this.pre_policy;
				ArrayList<Node> leftPath = currentPairStep.getLeftNode().getPath();
				ArrayList<Node> rightPath = currentPairStep.getRightNode().getPath();
				for (int i = 0; i < (leftPath.size() - 1); i++) {
					Node currentLeftNode = leftPath.get(i);
					BoolExpr leftConstrain = this.leftPathZ3.get(currentLeftNode);
					sat_formula = this.ictx.mkAnd(sat_formula, leftConstrain);
				}
				for (int i = 0; i < (rightPath.size() - 1); i++) {
					Node currentRightNode = rightPath.get(i);
					BoolExpr rightConstrain = this.rightPathZ3.get(currentRightNode);
					sat_formula = this.ictx.mkAnd(sat_formula, rightConstrain);
				}
				BoolExpr addInterpolant = this.ictx.MkInterpolant(sat_formula);
				BoolExpr allDescendConstrains = getAllDescendConstrains(currentPairStep, infeasibleSteps);
				BoolExpr unSatFormula = this.ictx.mkAnd(addInterpolant, allDescendConstrains);
				// System.out.println(allDescendConstrains);
				// System.out.println(unSatFormula);
				Params params = this.ictx.mkParams();
				ComputeInterpolantResult result = this.ictx.ComputeInterpolant(unSatFormula, params);
				Z3_lbool status = result.status;
				if (status == Z3_lbool.Z3_L_FALSE) {
					BoolExpr thisInterpolant = result.interp[0];
					Solver s2=this.ictx.mkSolver();
					BoolExpr shouldUnsat=this.ictx.mkAnd(thisInterpolant,allDescendConstrains);
					s2.reset();
					s2.add(shouldUnsat);
					Status result2=s2.check();
					if(result2 != Status.UNSATISFIABLE){
						System.out.println("it is not my fault");
					}
					thisInterpolant = Z3Utility.getSimplify(thisInterpolant, ictx);
					interpolantResult.put(currentPairStep, thisInterpolant);
				} else {
				    System.out.println("there are some error1");
					this.notCorrectModel = result.model;
					System.out.println(status);
					return false;
				}
				continue;
			}
			ArrayList<PairStep> parents = currentPairStep.getParents();
			BoolExpr[] successorInterPolants = new BoolExpr[parents.size()];
			int index = 0;
			BoolExpr allDescendConstrains = getAllDescendConstrains(currentPairStep, infeasibleSteps);
			for (PairStep parent : parents) {
				BoolExpr interpolantOfSuccessor = interpolantResult.get(parent);
				Node currentLeftNode = currentPairStep.getLeftNode();
				Node currentRightNode = currentPairStep.getRightNode();
				Node leftNode = parent.getLeftNode();
				Node rightNode = parent.getRightNode();
				if (currentLeftNode != leftNode) {
					BoolExpr constrains = interpolantOfSuccessor;
					while (currentLeftNode != leftNode) {
						currentLeftNode = currentLeftNode.getParent();
						BoolExpr nextConstrains = this.leftPathZ3.get(currentLeftNode);
						constrains = ictx.mkAnd(constrains, nextConstrains);
					}
					successorInterPolants[index] = constrains;

				} else {
					BoolExpr constrains = interpolantOfSuccessor;
					while (currentRightNode != rightNode) {
						currentRightNode = currentRightNode.getParent();
						BoolExpr nextConstrains = this.rightPathZ3.get(currentRightNode);
						constrains = ictx.mkAnd(constrains, nextConstrains);
					}
					successorInterPolants[index] = constrains;
				}
				index++;
			}
			// for interpolants is represent as A /\ B ,A is the formula that
			// interpolants need to consistent,and B is inconsistent
			BoolExpr A = null;
			if (successorInterPolants.length > 1) {
				A = this.ictx.mkOr(successorInterPolants);
			} else {
				A = successorInterPolants[0];
			}
			BoolExpr addInterpolant = this.ictx.MkInterpolant(A);
			BoolExpr unSatFormula = this.ictx.mkAnd(addInterpolant, allDescendConstrains);
			Params params = this.ictx.mkParams();
			ComputeInterpolantResult result = this.ictx.ComputeInterpolant(unSatFormula, params);
			Z3_lbool status = result.status;
			if (status == Z3_lbool.Z3_L_FALSE) {
				BoolExpr thisInterpolant = result.interp[0];
				Solver s2=this.ictx.mkSolver();
				BoolExpr shouldUnsat=this.ictx.mkAnd(thisInterpolant,allDescendConstrains);
				s2.reset();
				s2.add(shouldUnsat);
				Status result2=s2.check();
				if(result2 != Status.UNSATISFIABLE){
					System.out.println("it is not my fault");
				}
				thisInterpolant = Z3Utility.getSimplify(thisInterpolant, ictx);
				interpolantResult.put(currentPairStep, thisInterpolant);
			} else {
				System.out.println("there are some error2");
				this.notCorrectModel = result.model;
				System.out.println(status);
				return false;
			}
		}
		System.out.println("finish a refine1");
		DAGinterpolants theDAGinterpolants = new DAGinterpolants(allStepsInDAG, interpolantResult, this,
				infeasibleSteps);
		interpolantResult = theDAGinterpolants.getResult();
		for (Map.Entry<PairStep, BoolExpr> E : interpolantResult.entrySet()) {
			BoolExpr rightCovertBackInterpolant = (BoolExpr) this.rightCoverter.convertInterPolants(E.getValue());
			BoolExpr CovertBackInterpolant = (BoolExpr) this.leftCoverter
					.convertInterPolants(rightCovertBackInterpolant);
			PairStep pStep = E.getKey();
			pStep.addInterpolants(CovertBackInterpolant);
		}

		// help to quickly calculate implication
		Set<PairStep> updatedStep = new HashSet<PairStep>();
		for (Map.Entry<PairStep, BoolExpr> E : interpolantResult.entrySet()) {
			if (updatedStep.contains(E.getKey())) {
				System.out.println("This should be an error,in refine");
			}
			updatedStep.add(E.getKey());
		}
		this.updatedStep = updatedStep;
		System.out.println("finish a refine2");
		return true;
	}

	public BoolExpr getAllDescendConstrains(PairStep pStep, Set<PairStep> infeasibleSteps) {
		if (infeasibleSteps.isEmpty()) {
			Node leftNode = pStep.getLeftNode();
			Node rightNode = pStep.getRightNode();
			Node currentLeftNode = this.EntryStep.getLeftNode();
			Node currentRightNode = this.EntryStep.getRightNode();
			BoolExpr result = this.policy;
			while (currentLeftNode != leftNode) {
				BoolExpr leftConstrain = this.leftPathZ3.get(currentLeftNode);
				result = this.ictx.mkAnd(result, leftConstrain);
				currentLeftNode = currentLeftNode.getParent();
			}
			while (currentRightNode != rightNode) {
				BoolExpr rightConstrain = this.rightPathZ3.get(currentRightNode);
				result = this.ictx.mkAnd(result, rightConstrain);
				currentRightNode = currentRightNode.getParent();
			}
			BoolExpr leftConstrain = this.leftPathZ3.get(leftNode);
			BoolExpr rightConstrain = this.rightPathZ3.get(rightNode);
			result = this.ictx.mkAnd(result, leftConstrain, rightConstrain);
			return result;
		} else {
			Set<PairStep> infeasibleStepsFrontiers = calculateInfeasibleFrontier(infeasibleSteps, pStep);
			BoolExpr[] allConstrainsArray = new BoolExpr[infeasibleStepsFrontiers.size()];
			int i = 0;
			for (PairStep infeasibleStep : infeasibleStepsFrontiers) {
				Node leftNode = infeasibleStep.getLeftNode();
				Node rightNode = infeasibleStep.getRightNode();
				Node currentLeftNode = pStep.getLeftNode();
				Node currentRightNode = pStep.getRightNode();
				BoolExpr constrains = this.ictx.mkTrue();
				while (leftNode != currentLeftNode) {
					leftNode = leftNode.getParent();
					BoolExpr constrain = this.leftPathZ3.get(leftNode);
					constrains = this.ictx.mkAnd(constrains, constrain);
				}
				while (rightNode != currentRightNode) {
					rightNode = rightNode.getParent();
					BoolExpr constrain = this.rightPathZ3.get(rightNode);
					constrains = this.ictx.mkAnd(constrains, constrain);
				}
				allConstrainsArray[i] = constrains;
				i++;
			}
			return this.ictx.mkOr(allConstrainsArray);
		}
	}

	private void generatePolicy() {
		Stack<Expr> leftStack = this.leftCoverter.getReturnValue();
		Stack<Expr> rightStack = this.rightCoverter.getReturnValue();
		BoolExpr result = this.ictx.mkTrue();
		while ((!leftStack.isEmpty()) && (!rightStack.isEmpty())) {
			Expr leftExpr = leftStack.pop();
			Expr rightExpr = rightStack.pop();
			BoolExpr leftEqRight = this.ictx.mkEq(leftExpr, rightExpr);
			result = ictx.mkAnd(result, leftEqRight);
		}
		this.policy = this.ictx.mkNot(result);
		Map<Integer, Expr> constantValues = this.leftCoverter.getConstantValue();
		for (Entry<Integer, Expr> constantValue : this.rightCoverter.getConstantValue().entrySet()) {
			int key = constantValue.getKey();
			if (!constantValues.containsKey(key)) {
				constantValues.put(key, constantValue.getValue());
			}
		}
		for (Entry<Integer, Expr> constantValue : constantValues.entrySet()) {
			int value = constantValue.getKey();
			BoolExpr assignValue = this.ictx.mkEq(this.ictx.mkInt(value), constantValue.getValue());
			this.policy = this.ictx.mkAnd(this.policy, assignValue);
		}
		// if output result number is different, then can terminate means
		// inequivalent
		if ((!leftStack.isEmpty()) || (!rightStack.isEmpty())) {
			this.policy = this.ictx.mkTrue();
		}
		BoolExpr parameter = this.ictx.mkTrue();
		leftStack = this.leftCoverter.getParameterValue();
		rightStack = this.rightCoverter.getParameterValue();
		while ((!leftStack.isEmpty()) && (!rightStack.isEmpty())) {
			Expr leftExpr = leftStack.pop();
			Expr rightExpr = rightStack.pop();
			BoolExpr leftEqRight = this.ictx.mkEq(leftExpr, rightExpr);
			parameter = ictx.mkAnd(parameter, leftEqRight);
		}
		this.pre_policy = parameter;
		if (this.extraPrePolicy != null) {
			this.pre_policy = this.ictx.mkAnd(this.pre_policy, this.extraPrePolicy);
		}
		//System.out.println(this.pre_policy);
		// System.out.println("b");
		// System.out.println("the policy");
		// System.out.println(this.policy.toString());
	}

	public void Calculateimplication() {
		// System.out.println("doing implication");
		Set<PairStep> changedSteps = this.updatedStep;
		// System.out.println("changed size" + changedSteps.size());
		for (PairStep changedStep : changedSteps) {
			String unitId = changedStep.getUnitId();
			Set<PairStep> sameLocationSteps = this.UnitMapPairStep.get(unitId);
			for (PairStep sameLocationStep : sameLocationSteps) {
				if (!sameLocationStep.IfRefine()) {
					continue;
				}
				if (sameLocationStep == changedStep) {
					continue;
				}
				if (Z3Utility.checkEntail(changedStep.getInterpolants(), sameLocationStep.getInterpolants(),
						this.ictx)) {
					if (this.implication.containsKey(changedStep)) {
						Set<PairStep> coverBy = this.implication.remove(changedStep);
						if (!coverBy.contains(sameLocationStep)) {
							coverBy.add(sameLocationStep);
						}
						this.implication.put(changedStep, coverBy);
					} else {
						Set<PairStep> coverBy = new HashSet<PairStep>();
						coverBy.add(sameLocationStep);
						this.implication.put(changedStep, coverBy);
					}
				} else {
					if (this.implication.containsKey(changedStep)) {
						Set<PairStep> coverBy = this.implication.remove(changedStep);
						if (coverBy.contains(sameLocationStep)) {
							coverBy.remove(sameLocationStep);
						}
						this.implication.put(sameLocationStep, coverBy);
					}
				}
				if (Z3Utility.checkEntail(sameLocationStep.getInterpolants(), changedStep.getInterpolants(),
						this.ictx)) {
					if (this.implication.containsKey(sameLocationStep)) {
						Set<PairStep> coverBy = this.implication.get(sameLocationStep);
						if (!coverBy.contains(changedStep)) {
							coverBy.add(changedStep);
						}
						this.implication.put(sameLocationStep, coverBy);
					} else {
						Set<PairStep> coverBy = new HashSet<PairStep>();
						coverBy.add(changedStep);
						this.implication.put(sameLocationStep, coverBy);
					}
				} else {
					if (this.implication.containsKey(sameLocationStep)) {
						Set<PairStep> coverBy = this.implication.get(sameLocationStep);
						if (coverBy.contains(changedStep)) {
							coverBy.remove(changedStep);
						}
						this.implication.put(sameLocationStep, coverBy);
					}
				}
				// System.out.println("finish check");
			}
		}
		/**
		 * for(Entry<PairStep,Set<PairStep>>
		 * relation:this.implication.entrySet()){ PairStep
		 * theV=relation.getKey(); Set<PairStep> allCovered=relation.getValue();
		 * System.out.println(theV.getCount()+"is be covered by"); for(PairStep
		 * pStep:allCovered){ System.out.println(pStep.getCount()); }
		 * 
		 * }
		 **/
	}

	public boolean checkSafe() {
		this.Calculateimplication();
		this.clearSafe();
		this.safeResult = new HashMap<PairStep, Boolean>();
		Set<PairStep> visited = new HashSet<PairStep>();
		boolean result = this.ifSafe(visited, this.root);
		/*
		 * for(Entry<PairStep,Boolean> e:this.safeResult.entrySet()){
		 * System.out.println(e.getKey().getId()); if(e.getValue()){
		 * System.out.println("is safe"); } else{
		 * System.out.println("is not safe"); } }
		 */
		return result;
	}

	public boolean ifSafe(Set<PairStep> visited, PairStep p) {
		if (this.safeResult.containsKey(p)) {
			return this.safeResult.get(p);
		}
		if (p.isEntry() && p.IfRefine()) {
			this.safeResult.put(p, true);
			p.setSafe();
			return true;
		}
		if (p.isFalse()) {
			this.safeResult.put(p, true);
			p.setSafe();
			return true;
		}
		if (this.implication.containsKey(p)) {
			Set<PairStep> coveredBy = this.implication.get(p);
			for (PairStep coveredByStep : coveredBy) {
				if (visited.contains(coveredByStep)) {
					this.safeResult.put(p, true);
					p.setSafe();
					return true;
				}
			}
		}
		Set<PairStep> leftProgram = p.getLeftProgram();
		Set<PairStep> rightProgram = p.getRightProgram();
		if (leftProgram.isEmpty() && rightProgram.isEmpty()) {
			this.safeResult.put(p, false);
			return false;
		}
		if ((leftProgram.isEmpty()) && (!rightProgram.isEmpty())) {
			boolean isSafe = true;
			for (PairStep rightStep : rightProgram) {
				if (visited.contains(rightStep)) {
					continue;
				}
				Set<PairStep> newVisited = new HashSet<PairStep>();
				for (PairStep pStep : visited) {
					if (!newVisited.contains(pStep)) {
						newVisited.add(pStep);
					} else {
						// System.out.println("there is an error in PairDAG
						// check safe");
					}
				}
				if (!newVisited.contains(p)) {
					newVisited.add(p);
				} else {
					// System.out.println("there is an error");
				}
				if (!this.ifSafe(newVisited, rightStep)) {
					isSafe = false;
				}
			}
			if (isSafe) {
				// System.out.println("check "+p.getCount()+" is safe");
				// System.out.println("check right program");
				this.safeResult.put(p, true);
				p.setSafe();
				return true;
			}
		}
		if ((rightProgram.isEmpty()) && (!leftProgram.isEmpty())) {
			boolean isSafe = true;
			for (PairStep leftStep : leftProgram) {
				if (visited.contains(leftStep)) {
					continue;
				}
				Set<PairStep> newVisited = new HashSet<PairStep>();
				for (PairStep pStep : visited) {
					if (!newVisited.contains(pStep)) {
						newVisited.add(pStep);
					} else {
						// System.out.println("there is an error in PairDAG
						// check safe");
					}
				}
				if (!newVisited.contains(p)) {
					newVisited.add(p);
				} else {
					// System.out.println("there an error");
				}
				if (!this.ifSafe(newVisited, leftStep)) {
					isSafe = false;
				}
			}
			if (isSafe) {
				// System.out.println("check "+p.getCount()+" is safe");
				// System.out.println("check left program");
				this.safeResult.put(p, true);
				p.setSafe();
				return true;
			}
		}
		if ((!rightProgram.isEmpty()) && (!leftProgram.isEmpty())) {
			boolean isSafe = true;
			for (PairStep leftStep : leftProgram) {
				if (visited.contains(leftStep)) {
					continue;
				}
				Set<PairStep> newVisited = new HashSet<PairStep>();
				for (PairStep pStep : visited) {
					if (!newVisited.contains(pStep)) {
						newVisited.add(pStep);
					} else {
						// System.out.println("there is an error in PairDAG
						// check safe");
					}
				}
				if (!newVisited.contains(p)) {
					newVisited.add(p);
				} else {
					// System.out.println("there is an error");
				}
				if (!this.ifSafe(newVisited, leftStep)) {
					isSafe = false;
				}
			}
			if (isSafe) {
				// System.out.println("check "+p.getCount()+" is safe");
				// System.out.println("check left program");
				this.safeResult.put(p, true);
				p.setSafe();
				return true;
			} else {
				isSafe = true;
				for (PairStep rightStep : rightProgram) {
					if (visited.contains(rightStep)) {
						continue;
					}
					Set<PairStep> newVisited = new HashSet<PairStep>();
					for (PairStep pStep : visited) {
						if (!newVisited.contains(pStep)) {
							newVisited.add(pStep);
						} else {
							// System.out.println("there is an error in PairDAG
							// check safe");
						}
					}
					if (!newVisited.contains(p)) {
						newVisited.add(p);
					} else {
						// System.out.println("there is an error");
					}
					if (!this.ifSafe(newVisited, rightStep)) {
						isSafe = false;
					}
				}
				if (isSafe) {
					// System.out.println("check "+p.getCount()+" is safe");
					// System.out.println("check right program");
					this.safeResult.put(p, true);
					p.setSafe();
					return true;
				}
			}
		}
		// System.out.println(p.getCount()+"is fail");
		this.safeResult.put(p, false);
		return false;
	}

	public boolean isEquivalent() throws IOException {
		int i = 0;
		while (!this.potentialHyperEdges.isEmpty()) {
			// System.out.println("a");
			HyperEdge start = this.potentialHyperEdges.poll();
			if (start.isUnwind()) {
				continue;
			}
			if (start.isCovered()) {
				if (!this.coveredEdge.contains(start)) {
					this.coveredEdge.add(start);
				}
				continue;
			}
			this.getNextUnwind(start);
			while (!this.currentHyperEdges.isEmpty()) {
				this.unwindCurrent();
			}
			System.out.println("doing " + i + " refine");
			System.out.println(this.EntryStep.getId());
			boolean isEquivalent = this.refine();
			if (!isEquivalent) {
				this.isEquivalent = false;
				break;
			}
			boolean isSafe = this.checkSafe();
			Set<PairStep> entryStep = new HashSet<PairStep>();
			entryStep.add(this.EntryStep);
			this.outputInvariants(this.outputDir, entryStep);
			if (isSafe) {
				System.out.println("we get safe");
				return true;
			}
			i++;
			/*
			 * if (i == 4) { //System.exit(0); }
			 */
			Set<HyperEdge> removeSet = new HashSet<HyperEdge>();
			for (HyperEdge hEdge : this.coveredEdge) {
				if (!hEdge.isCovered()) {
					removeSet.add(hEdge);
				}
			}
			for (HyperEdge removeEdge : removeSet) {
				this.potentialHyperEdges.add(removeEdge);
				this.coveredEdge.remove(removeEdge);
			}
		}
		return this.isEquivalent;
	}

	public void getNextUnwind(HyperEdge start) {
		this.currentHyperEdges.add(start);
		if (start.getLeftMain() != null) {
			this.leftMost = start.getLeftMain().getLeftNode();
		} else {
			this.leftMost = start.getRightMain().getLeftNode();
		}
		if (start.getRightMain() != null) {
			this.rightMost = start.getRightMain().getRightNode();
		} else {
			this.rightMost = start.getLeftMain().getRightNode();
		}
		this.updateLeftAndRightMost();
		Set<Node> leftPath = leftMost.getPathSet();
		Set<Node> rightPath = rightMost.getPathSet();
		Comparator<HyperEdge> HyperEdgeComparator = new HyperEdgeComparator();
		PriorityQueue<HyperEdge> newPotentialHyperEdges = new PriorityQueue<HyperEdge>(100, HyperEdgeComparator);
		for (HyperEdge hEdge : this.potentialHyperEdges) {
			if (hEdge.isInPath(leftPath, rightPath)) {
				this.currentHyperEdges.add(hEdge);
			} else {
				newPotentialHyperEdges.add(hEdge);
			}
		}
		this.potentialHyperEdges = newPotentialHyperEdges;
	}

	public InterpolationContext getIctx() {
		return this.ictx;
	}

	public void outputInvariants(String outputdir, Set<PairStep> entrySet) {
		SimpleDirectedGraph<PairStep, DefaultEdge> graph = new SimpleDirectedGraph<PairStep, DefaultEdge>(
				DefaultEdge.class);
		PairStep.addVertexAndEdge(graph);
		SimpleDirectedGraph<PairStep, DefaultEdge> graph2 = new SimpleDirectedGraph<PairStep, DefaultEdge>(
				DefaultEdge.class);
		PairStep.addSpecialVertexAndEdge(graph2, entrySet);
		ComponentAttributeProvider<DefaultEdge> dash = new edgeAttribute(graph);
		VertexNameProvider<PairStep> name1 = new vertextName();
		DOTExporter<PairStep, DefaultEdge> outputDot = new DOTExporter<PairStep, DefaultEdge>(new IntegerNameProvider(),
				name1, null, new vertexAttribute(), dash);
		dash = new edgeAttribute(graph2);
		VertexNameProvider<PairStep> name2 = new vertexName2();
		DOTExporter<PairStep, DefaultEdge> outputDot2 = new DOTExporter<PairStep, DefaultEdge>(
				new IntegerNameProvider(), name2, null, new vertexAttribute(), dash);
		try {
			if (outputdir.equals("test")) {
				if (!this.EntryStep.isFalse()) {
					FileWriter writer = new FileWriter("output" + this.outputNumber + "Feasible" + ".dot");
					outputDot.export(writer, graph);
					writer.close();
					FileWriter writer2 = new FileWriter("output" + this.outputNumber + "FeasibleSingle" + ".dot");
					outputDot2.export(writer2, graph2);
					writer2.close();

				} else {
					FileWriter writer = new FileWriter("output" + this.outputNumber + ".dot");
					outputDot.export(writer, graph);
					writer.close();
					FileWriter writer2 = new FileWriter("output" + this.outputNumber + "Single" + ".dot");
					outputDot2.export(writer2, graph2);
					writer2.close();
				}
			} else {
				if (!this.EntryStep.isFalse()) {
					FileWriter writer = new FileWriter(outputdir + "/output" + this.outputNumber + "Feasible" + ".dot");
					outputDot.export(writer, graph);
					writer.close();
					FileWriter writer2 = new FileWriter("output" + this.outputNumber + "FeasibleSingle" + ".dot");
					outputDot2.export(writer2, graph2);
					writer2.close();
				} else {
					FileWriter writer = new FileWriter(outputdir + "/output" + this.outputNumber + ".dot");
					outputDot.export(writer, graph);
					writer.close();
					FileWriter writer2 = new FileWriter("output" + this.outputNumber + "Single" + ".dot");
					outputDot2.export(writer2, graph2);
					writer2.close();
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		this.outputNumber++;
	}

	public boolean IsInvariantValid(BoolExpr e, PairStep p, Set<PairStep> infeasibleFrontier) {
		BoolExpr allDescentConstrains = getAllDescendConstrains(p, infeasibleFrontier);
		Solver s = this.ictx.mkSolver();
		BoolExpr unSat = this.ictx.mkAnd(e, allDescentConstrains);
		s.add(unSat);
		Status result = s.check();
		if (result == Status.UNSATISFIABLE) {
			return true;
		} else {
			return false;
		}
	}

	public Set<PairStep> calculateInfeasibleFrontier(Set<PairStep> infeasibleStep, PairStep pStep) {
		Set<PairStep> frontier = new HashSet<PairStep>();
		Set<PairStep> stepsInDAG = this.EntryStep.CollecttParents();
		stepsInDAG.add(this.EntryStep);
		Queue<PairStep> checkSteps = new LinkedList<PairStep>();
		checkSteps.add(pStep);
		Set<PairStep> visited = new HashSet<PairStep>();
		visited.add(pStep);
		while (!checkSteps.isEmpty()) {
			PairStep currentCheckStep = checkSteps.remove();
			if (infeasibleStep.contains(currentCheckStep)) {
				if (!frontier.contains(currentCheckStep)) {
					frontier.add(currentCheckStep);
				}
			} else {
				Set<PairStep> successors = currentCheckStep.getSuccessors();
				for (PairStep successor : successors) {
					if ((!visited.contains(successor)) && (stepsInDAG.contains(successor))) {
						checkSteps.add(successor);
						visited.add(successor);
					}
				}
			}
		}
		return frontier;
	}

	public Set<PairStep> calculateInfeasibleStep(PairStep entryStep) {
		Set<PairStep> allStepsInDAG = entryStep.CollecttParents();
		allStepsInDAG.add(entryStep);
		Set<PairStep> InfeasibleStep = new HashSet<PairStep>();
		Queue<PairStep> checkSteps = new LinkedList<PairStep>();
		checkSteps.add(this.root);
		Set<PairStep> visited = new HashSet<PairStep>();
		visited.add(this.root);
		while (!checkSteps.isEmpty()) {
			PairStep currentCheckStep = checkSteps.remove();
			if (checkIfPathFeasible(currentCheckStep)) {
				Set<PairStep> successors = currentCheckStep.getSuccessors();
				for (PairStep successor : successors) {
					if ((!visited.contains(successor)) && (allStepsInDAG.contains(successor))) {
						visited.add(successor);
						checkSteps.add(successor);
					}
				}
			} else {
				Set<PairStep> allSuccessors = currentCheckStep.getAllSuccessors();
				allSuccessors.add(currentCheckStep);
				for (PairStep p : allSuccessors) {
					if ((allStepsInDAG.contains(p)) && (!InfeasibleStep.contains(p))) {
						InfeasibleStep.add(p);
					}
				}
			}
		}
		return InfeasibleStep;
	}

	public boolean checkIfPathFeasible(PairStep p) {
		Node leftNode = p.getLeftNode();
		Node rightNode = p.getRightNode();
		BoolExpr constrains = this.pre_policy;
		ArrayList<Node> leftPath = leftNode.getPath();
		ArrayList<Node> rightPath = rightNode.getPath();
		for (int i = 0; i < (leftPath.size() - 1); i++) {
			Node currentLeftNode = leftPath.get(i);
			BoolExpr leftConstrains = this.leftPathZ3.get(currentLeftNode);
			constrains = this.ictx.mkAnd(constrains, leftConstrains);
		}
		for (int i = 0; i < (rightPath.size() - 1); i++) {
			Node currentRightNode = rightPath.get(i);
			BoolExpr rightConstrains = this.rightPathZ3.get(currentRightNode);
			constrains = this.ictx.mkAnd(constrains, rightConstrains);
		}
		Solver s = this.ictx.mkSolver();
		s.add(constrains);
		Status result = s.check();
		if (result == Status.UNSATISFIABLE) {
			// System.out.println("there are something work");
			return false;
		} else {
			return true;
		}
	}

	public void addExtraPrePolicy(BoolExpr e) {
		this.extraPrePolicy = e;
	}

	public PairStep getRoot() {
		return this.root;
	}

	public PairStep getEntryStep() {
		return this.EntryStep;
	}

	public Map<Node, BoolExpr> getLeftPathZ3() {
		return this.leftPathZ3;
	}

	public Map<Node, BoolExpr> getRightPathZ3() {
		return this.rightPathZ3;
	}

	public BoolExpr getPrePolicy() {
		return this.pre_policy;
	}

	public BoolExpr getPostPolicy() {
		return this.policy;
	}

	public Model getWrongModel() {
		return this.notCorrectModel;
	}

	public void addPairStep(PairStep p) {
		this.allCreatedStep.add(p);
	}

	public void clearSafe() {
		for (PairStep p : this.allCreatedStep) {
			p.resetSafe();
		}
	}

}
