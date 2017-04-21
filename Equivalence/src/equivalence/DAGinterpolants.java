package equivalence;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.InterpolationContext;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.InterpolationContext.ComputeInterpolantResult;
import com.microsoft.z3.enumerations.Z3_lbool;

import z3_helper.Z3Rewriter;
import z3_helper.Z3Utility;

public class DAGinterpolants {
	private Set<PairStep> stepsInDAG;
	private Map<PairStep, BoolExpr> currentInterpolants;
	private PairDAG pDAG;
	private InterpolationContext ictx;
	private PairStep root;
	private Map<Node, BoolExpr> leftPathZ3;
	private Map<Node, BoolExpr> rightPathZ3;
	private BoolExpr prePolicy;
	private Set<PairStep> infeasibleSteps;
	private Map<PairStep, BoolExpr> convincedInterpolants;
	private Set<PairStep> potentialConvincedPairSteps;

	public DAGinterpolants(Set<PairStep> stepsInDAG, Map<PairStep, BoolExpr> currentInterpolant, PairDAG pDAG,
			Set<PairStep> infeasibleSteps) {
		this.stepsInDAG = stepsInDAG;
		this.currentInterpolants = currentInterpolant;
		this.pDAG = pDAG;
		this.ictx = this.pDAG.getIctx();
		this.root = this.pDAG.getRoot();
		this.leftPathZ3 = this.pDAG.getLeftPathZ3();
		this.rightPathZ3 = this.pDAG.getRightPathZ3();
		this.prePolicy = this.pDAG.getPrePolicy();
		this.infeasibleSteps = infeasibleSteps;
		this.convincedInterpolants = new HashMap<PairStep, BoolExpr>();
		this.updateInterpolants();

	}

	public void updateInterpolants() {
		Queue<PairStep> worklist = new LinkedList<PairStep>();
		worklist.add(this.root);
		Set<PairStep> visitedStep = new HashSet<PairStep>();
		visitedStep.add(this.root);
		while (!worklist.isEmpty()) {
			PairStep theCurrentStep = worklist.remove();
			if (infeasibleSteps.contains(theCurrentStep)) {
				continue;
			}
			Set<PairStep> successors = theCurrentStep.getSuccessors();
			for (PairStep successor : successors) {
				if ((!visitedStep.contains(successor)) && (this.stepsInDAG.contains(successor))) {
					worklist.add(successor);
					visitedStep.add(successor);
				}
			}
			BoolExpr currentInterpolant = this.currentInterpolants.get(theCurrentStep);
			BoolExpr theSatFormula = this.calculateSatFormula(theCurrentStep);
			Z3Rewriter theRewriter = new Z3Rewriter(currentInterpolant, this.pDAG, theCurrentStep, this.infeasibleSteps,
					theSatFormula);
			if (theRewriter.isChanged()) {
				BoolExpr newInterpolant = theRewriter.getNewInterpolants();
				// System.out.println(newInterpolant);
				Map<PairStep, BoolExpr> newInterpolantsResult = this.updateRefine(theCurrentStep, newInterpolant);
				// System.out.println("the size
				// of"+newInterpolantsResult.size());
				// doing metric comparison
				boolean isBetter = true;
				if (isBetter) {
					this.currentInterpolants = newInterpolantsResult;
					for (PairStep pStep : this.potentialConvincedPairSteps) {
						if (!this.convincedInterpolants.containsKey(pStep)) {
							BoolExpr convincedInterpolant = this.currentInterpolants.get(pStep);
							this.convincedInterpolants.put(pStep, convincedInterpolant);
						}
					}
				}
			}
		}
	}

	public Map<PairStep, BoolExpr> getResult() {
		return this.currentInterpolants;
	}

	public BoolExpr calculateSatFormula(PairStep p) {
		if (this.convincedInterpolants.isEmpty()) {
			Node leftNode = p.getLeftNode();
			Node rightNode = p.getRightNode();
			BoolExpr theSatFormula = this.prePolicy;
			ArrayList<Node> leftPath = leftNode.getPath();
			ArrayList<Node> rightPath = rightNode.getPath();
			for (int j = 0; j < (leftPath.size() - 1); j++) {
				BoolExpr leftConstrain = this.leftPathZ3.get(leftPath.get(j));
				theSatFormula = this.ictx.mkAnd(theSatFormula, leftConstrain);
			}
			for (int j = 0; j < (rightPath.size() - 1); j++) {
				BoolExpr rightConstrain = this.rightPathZ3.get(rightPath.get(j));
				theSatFormula = this.ictx.mkAnd(theSatFormula, rightConstrain);
			}
			return theSatFormula;
		} else {
			Set<PairStep> frontiers = this.convincedPairStepFrontier(p);
			BoolExpr[] theSatFormulas = new BoolExpr[frontiers.size()];
			int i = 0;
			for (PairStep convincedPairStep : frontiers) {
				BoolExpr theSatFormula = this.convincedInterpolants.get(convincedPairStep);
				Node leftNode = convincedPairStep.getLeftNode();
				Node rightNode = convincedPairStep.getRightNode();
				Node currentLeftNode = p.getLeftNode();
				Node currentRightNode = p.getRightNode();
				while (currentLeftNode != leftNode) {
					currentLeftNode = currentLeftNode.getParent();
					BoolExpr leftConstrain = this.leftPathZ3.get(currentLeftNode);
					theSatFormula = this.ictx.mkAnd(theSatFormula, leftConstrain);
				}
				while (currentRightNode != rightNode) {
					currentRightNode = currentRightNode.getParent();
					BoolExpr rightConstrain = this.rightPathZ3.get(currentRightNode);
					theSatFormula = this.ictx.mkAnd(theSatFormula, rightConstrain);
				}
				theSatFormulas[i] = theSatFormula;
				i++;
			}
			return this.ictx.mkOr(theSatFormulas);
		}
	}

	public Set<PairStep> convincedPairStepFrontier(PairStep p) {
		Queue<PairStep> worklist = new LinkedList<PairStep>();
		worklist.add(p);
		Set<PairStep> visitedPairStep = new HashSet<PairStep>();
		visitedPairStep.add(p);
		Set<PairStep> frontier = new HashSet<PairStep>();
		while (!worklist.isEmpty()) {
			PairStep theStep = worklist.remove();
			if (this.convincedInterpolants.containsKey(theStep)) {
				frontier.add(theStep);
			} else {
				ArrayList<PairStep> parents = theStep.getParents();
				for (PairStep parent : parents) {
					if (!visitedPairStep.contains(parent)) {
						worklist.add(parent);
						visitedPairStep.add(parent);
					}
				}
			}
		}
		return frontier;
	}

	public Map<PairStep, BoolExpr> updateRefine(PairStep p, BoolExpr pInterpolant) {
		Set<PairStep> PairStepDependsOnP = p.CollecttParents();
		Map<PairStep, BoolExpr> newInterpolantResult = new HashMap<PairStep, BoolExpr>();
		Queue<PairStep> refineStep = new LinkedList<PairStep>();
		refineStep.add(this.root);
		Set<PairStep> haveRefined = new HashSet<PairStep>();
		while (!refineStep.isEmpty()) {
			PairStep currentPairStep = refineStep.poll();
			// System.out.println("update refine:"+currentPairStep.getId());
			if (this.infeasibleSteps.contains(currentPairStep)) {
				newInterpolantResult.put(currentPairStep, this.ictx.mkFalse());
				continue;
			}
			Set<PairStep> successors = currentPairStep.getSuccessors();
			for (PairStep successor : successors) {
				if ((!haveRefined.contains(successor)) && (this.stepsInDAG.contains(successor))) {
					haveRefined.add(successor);
					refineStep.add(successor);
				}
			}
			if (this.convincedInterpolants.containsKey(currentPairStep)) {
				BoolExpr convincedInterpolant = this.convincedInterpolants.get(currentPairStep);
				newInterpolantResult.put(currentPairStep, convincedInterpolant);
				continue;
			}
			if (currentPairStep == p) {
				newInterpolantResult.put(currentPairStep, pInterpolant);
				continue;
			}
			if (currentPairStep == this.root) {
				BoolExpr sat_formula = this.prePolicy;
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
				BoolExpr allDescendConstrains = null;
				if (PairStepDependsOnP.contains(currentPairStep)) {
					// System.out.println("the ancestor");
					BoolExpr constrains = this.ictx.mkTrue();
					Node currentLeftNode = currentPairStep.getLeftNode();
					Node currentRightNode = currentPairStep.getRightNode();
					Node leftNode = p.getLeftNode();
					Node rightNode = p.getRightNode();
					while (leftNode != currentLeftNode) {
						leftNode = leftNode.getParent();
						BoolExpr thisConstrain = this.leftPathZ3.get(leftNode);
						constrains = this.ictx.mkAnd(constrains, thisConstrain);
					}
					while (rightNode != currentRightNode) {
						rightNode = rightNode.getParent();
						BoolExpr thisConstrain = this.rightPathZ3.get(rightNode);
						constrains = this.ictx.mkAnd(constrains, thisConstrain);
					}
					BoolExpr notP = this.ictx.mkNot(pInterpolant);
					allDescendConstrains = this.ictx.mkAnd(constrains, notP);
				} else {
					allDescendConstrains = this.pDAG.getAllDescendConstrains(currentPairStep, infeasibleSteps);
				}
				BoolExpr unSatFormula = this.ictx.mkAnd(addInterpolant, allDescendConstrains);
				Params params = this.ictx.mkParams();
				ComputeInterpolantResult result = this.ictx.ComputeInterpolant(unSatFormula, params);
				Z3_lbool status = result.status;
				if (status == Z3_lbool.Z3_L_FALSE) {
					BoolExpr thisInterpolant = result.interp[0];
					thisInterpolant = Z3Utility.getSimplify(thisInterpolant, ictx);
					newInterpolantResult.put(currentPairStep, thisInterpolant);
				} else {
					System.out.println("there is an serious error in update refine1");
				}
				continue;
			}
			ArrayList<PairStep> parents = currentPairStep.getParents();
			BoolExpr[] successorInterPolants = new BoolExpr[parents.size()];
			int index = 0;
			BoolExpr allDescendConstrains = null;
			if (PairStepDependsOnP.contains(currentPairStep)) {
				BoolExpr constrains = this.ictx.mkTrue();
				Node currentLeftNode = currentPairStep.getLeftNode();
				Node currentRightNode = currentPairStep.getRightNode();
				Node leftNode = p.getLeftNode();
				Node rightNode = p.getRightNode();
				while (leftNode != currentLeftNode) {
					leftNode = leftNode.getParent();
					BoolExpr thisConstrain = this.leftPathZ3.get(leftNode);
					constrains = this.ictx.mkAnd(constrains, thisConstrain);
				}
				while (rightNode != currentRightNode) {
					rightNode = rightNode.getParent();
					BoolExpr thisConstrain = this.rightPathZ3.get(rightNode);
					constrains = this.ictx.mkAnd(constrains, thisConstrain);
				}
				BoolExpr notP = this.ictx.mkNot(pInterpolant);
				allDescendConstrains = this.ictx.mkAnd(constrains, notP);
			} else {
				allDescendConstrains = this.pDAG.getAllDescendConstrains(currentPairStep, infeasibleSteps);
			}
			for (PairStep parent : parents) {
				BoolExpr constrains = newInterpolantResult.get(parent);
				Node currentLeftNode = currentPairStep.getLeftNode();
				Node currentRightNode = currentPairStep.getRightNode();
				Node leftNode = parent.getLeftNode();
				Node rightNode = parent.getRightNode();
				while (currentLeftNode != leftNode) {
					currentLeftNode = currentLeftNode.getParent();
					BoolExpr nextConstrains = this.leftPathZ3.get(currentLeftNode);
					constrains = ictx.mkAnd(constrains, nextConstrains);
				}
				while (currentRightNode != rightNode) {
					currentRightNode = currentRightNode.getParent();
					BoolExpr nextConstrains = this.rightPathZ3.get(currentRightNode);
					constrains = ictx.mkAnd(constrains, nextConstrains);

				}
				successorInterPolants[index] = constrains;
				index++;
			}
			// for interpolants is represent as A /\ B ,A is the formula that
			// interpolants need to consistent,and B is inconsistent
			BoolExpr A = null;
			BoolExpr wrongA=null;
			if (successorInterPolants.length > 1) {
				A = this.ictx.mkOr(successorInterPolants);
				wrongA=successorInterPolants[1];
			} else {
				A = successorInterPolants[0];
			}
			BoolExpr addInterpolant = this.ictx.MkInterpolant(A);
			//System.out.println(allDescendConstrains);
			BoolExpr unSatFormula = this.ictx.mkAnd(addInterpolant, allDescendConstrains);
			Params params = this.ictx.mkParams();
			ComputeInterpolantResult result = this.ictx.ComputeInterpolant(unSatFormula, params);
			Z3_lbool status = result.status;
			if (status == Z3_lbool.Z3_L_FALSE) {
				BoolExpr thisInterpolant = result.interp[0];
				if(p.getId().equals("5#8")&&(currentPairStep.getId().equals("5#12"))){
					System.out.println(pInterpolant);
				}
				thisInterpolant = Z3Utility.getSimplify(thisInterpolant, ictx);
				newInterpolantResult.put(currentPairStep, thisInterpolant);
			} else {
				System.out.println(status);
				System.out.println("there is a serious error in update refine");
				System.out.println("P is "+p.getId());
				System.out.println("current id is"+currentPairStep.getId());
			}
		}
		this.potentialConvincedPairSteps = PairStepDependsOnP;
		this.potentialConvincedPairSteps.add(p);
		return newInterpolantResult;
	}
}
