package equivalence;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;

import org.jgraph.graph.DefaultEdge;
import org.jgrapht.graph.SimpleDirectedGraph;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.InterpolationContext;

import soot.Unit;
import soot.jimple.GotoStmt;
import z3_helper.Z3Utility;

public class PairStep {
	static int numberOfPairStep = 0;
	static Map<String,PairStep> createdStep=new HashMap<String,PairStep>();
	private int count;
	private String id;
	private long leftStepId;
	private long rightStepId;
	private ArrayList<PairStep> parents;
	private Set<String> parentsId;
	private Node leftNode;
	private Node rightNode;
	private PairDAG unwindPairDAG;
	private Set<PairStep> successors;
	private Map<PairStep,Node> successorsMapNode;
	private boolean isUnwind;
	private BoolExpr interpolant;
	private String UnitId;
	private boolean isSafe;
	private Set<HyperEdge> successorHyperEdge;
	private Set<PairStep> leftProgram;
	private Set<PairStep> rightprogram;
	private boolean isEntry;
	private ArrayList<Node> leftProgramNode;
	private ArrayList<Node> rightProgramNode;
	private boolean isRefine;
	private BoolExpr lastInterpolant;
	private boolean ifFalse;
	// 1 means left and right statement are both not return statement, 2 means left is return statement,3 means right is
	// return statement, 4 means that both are return statement
	private int type;
	
	static public PairStep getNewPairStep(PairStep parent, Node leftNode, Node rightNode, PairDAG unwindPairDAG) {
		Node currentLeftNode=leftNode;
		while((!currentLeftNode.ifMultiPredecssor())&&(!currentLeftNode.isEntry())){
			currentLeftNode=currentLeftNode.getSuccessors().get(0);
		}
		Node currentRightNode=rightNode;
		while((!currentRightNode.ifMultiPredecssor())&&(!currentRightNode.isEntry())){
			currentRightNode=currentRightNode.getSuccessors().get(0);
		}
		long leftId=currentLeftNode.getId();
		long rightId=currentRightNode.getId();
		String id=leftId+"#"+rightId;
		if(createdStep.containsKey(id)){
			PairStep oldStep=createdStep.get(id);
			oldStep.addParents(parent);
			return oldStep;
		}
		else{
		PairStep newPairStep = new PairStep(id, parent, leftNode, rightNode, unwindPairDAG,numberOfPairStep);
		numberOfPairStep++;
		createdStep.put(id, newPairStep);
		unwindPairDAG.addPairStep(newPairStep);
		return newPairStep;
		}

	}

	private PairStep(String Id, PairStep parent, Node leftNode, Node rightNode, PairDAG unwindPairDAG,int count) {
		this.interpolant=unwindPairDAG.getIctx().mkTrue();
		this.id = Id;
		this.count=count;
		this.leftStepId = leftNode.getId();
		this.rightStepId = rightNode.getId();
		this.parents = new ArrayList<PairStep>();
		if(parent!=null){
		this.parents.add(parent);
		}
		this.unwindPairDAG = unwindPairDAG;
		this.successors=new HashSet<PairStep>();
		// will figure out later
		this.type=1;
		this.isUnwind=false;
		this.parentsId=new HashSet<String>();
		if(parent!=null){
		this.parentsId.add(parent.getId());
		}
		this.successorsMapNode=new HashMap<PairStep,Node>();
		this.isSafe=false;
		this.successorHyperEdge=new HashSet<HyperEdge>();
		this.leftProgram=new HashSet<PairStep>();
		this.rightprogram=new HashSet<PairStep>();
		this.leftProgramNode=new ArrayList<Node>();
		this.rightProgramNode=new ArrayList<Node>();
		Node currentLeftNode=leftNode;
		while((!currentLeftNode.ifMultiPredecssor())&&(!currentLeftNode.isEntry())){
			this.leftProgramNode.add(currentLeftNode);
			currentLeftNode=currentLeftNode.getSuccessors().get(0);
		}
		this.leftProgramNode.add(currentLeftNode);
		this.leftNode=currentLeftNode;
		Node currentRightNode=rightNode;
		while((!currentRightNode.ifMultiPredecssor())&&(!currentRightNode.isEntry())){
			this.rightProgramNode.add(currentRightNode);
			currentRightNode=currentRightNode.getSuccessors().get(0);
		}
		this.rightProgramNode.add(currentRightNode);
		this.rightNode=currentRightNode;
		if((this.leftNode.isEntry())&&(this.rightNode.isEntry())){
			this.isEntry=true;
		}
		else{
		this.isEntry=false;
		}
		this.UnitId=this.leftNode.getUnitId()+"#"+this.rightNode.getUnitId();
		this.unwindPairDAG.addUnitMap(this);
		this.isRefine=false;
		this.ifFalse=false;
	}
	public boolean isEntry(){
		return this.isEntry;
	}
	public String getUnitId(){
		return this.UnitId;
	}
	public String getId(){
		return this.id;
	}
    public Set<PairStep> getSuccessors(){
    	return this.successors;
    }
    public Set<PairStep> getAllSuccessors(){
    	Set<PairStep> result=new HashSet<PairStep>();
    	for(PairStep successor:this.successors){
    		if(!result.contains(successor)){
    			result.add(successor);
    			Set<PairStep> subSuccessors=successor.getAllSuccessors();
    			for(PairStep subSuccessor:subSuccessors){
    				if(!result.contains(subSuccessor)){
    					result.add(subSuccessor);
    				}
    			}
    		}
    	}
    	return result;
    }
    public ArrayList<PairStep> getParents(){
    	return this.parents;
    }
    public Set<PairStep> CollecttParents(){
    	Set<PairStep> result=new HashSet<PairStep>();
    	ArrayList<PairStep> parents=this.parents;
    	for(int i=0;i<parents.size();i++){
    		PairStep parent=parents.get(i);
    		Set<PairStep> upParents=parent.CollecttParents();
    		for(PairStep upParent:upParents){
    			if(!result.contains(upParent)){
    				result.add(upParent);
    			}
    		}
    	}
    	for(int i=0;i<parents.size();i++){
    		PairStep parent=parents.get(i);
    		if(!result.contains(parent)){
    			result.add(parent);
    		}
    	}
    	return result;
    }
    public void addParents(PairStep parent){
    	if(!this.parentsId.contains(parent.getId())){
    	this.parents.add(parent);
    	this.parentsId.add(parent.getId());
    	}
    }
	public void unwind() {
		if(this.isUnwind){
			this.unwindPairDAG.insertNewGroupOfSteps(this.successorHyperEdge,this);
			return;
		}
		// when left and right are both not entry
		if ((!this.leftNode.isEntry()) && (!this.rightNode.isEntry())) {
			ArrayList<Node> leftSuccessors = this.leftNode.getSuccessors();
			ArrayList<Node> rightSuccessors = this.rightNode.getSuccessors();
			ArrayList<PairStep> unwindToLeft = new ArrayList<PairStep>();
			ArrayList<PairStep> unwindToRight = new ArrayList<PairStep>();
			for (int i = 0; i < leftSuccessors.size(); i++) {
				Node leftNode = leftSuccessors.get(i);
				PairStep unwindLeft=null;
				unwindLeft = PairStep.getNewPairStep(this, leftNode, this.rightNode, this.unwindPairDAG);
				this.successors.add(unwindLeft);
				this.successorsMapNode.put(unwindLeft, leftNode);
				unwindToLeft.add(unwindLeft);
				this.leftProgram.add(unwindLeft);
			}
			for (int i = 0; i < rightSuccessors.size(); i++) {
				Node rightNode = rightSuccessors.get(i);
				PairStep unwindRight = PairStep.getNewPairStep(this, this.leftNode, rightNode, this.unwindPairDAG);
				this.successors.add(unwindRight);
				this.successorsMapNode.put(unwindRight, rightNode);
				unwindToRight.add(unwindRight);
				this.rightprogram.add(unwindRight);
			}
			Set<HyperEdge> allHyperEdges = new HashSet<HyperEdge>();
			for (int i = 0; i < unwindToLeft.size(); i++) {
				for (int j = 0; j < unwindToRight.size(); j++) {
					HyperEdge hyerEdge = new HyperEdge(this);
					hyerEdge.addLeftMain(unwindToLeft.get(i));
					hyerEdge.addRightMain(unwindToRight.get(j));
					allHyperEdges.add(hyerEdge);
				}
			}
			for(HyperEdge hEdge:allHyperEdges){
				if(!this.successorHyperEdge.contains(hEdge)){
					this.successorHyperEdge.add(hEdge);
				}
			}
			/** if(this.successors.size()==2){
				if(this.successorHyperEdge.size()>1){
					System.out.println("start error");
					System.out.println(this.successorHyperEdge.size());
				}
			}
			if((unwindToLeft.size()==1)&&(unwindToRight.size())==1){
				System.out.println("end error");
			} **/
			/**Unit leftUnit=this.leftNode.getStmt();
			Unit rightUnit=this.rightNode.getStmt();
			if(leftUnit  instanceof GotoStmt){
				if(rightUnit instanceof GotoStmt){
					if(allHyperEdges.size()>2){
						int i=1;
					}
				}
			} */
			this.unwindPairDAG.insertNewGroupOfSteps(allHyperEdges,this);
		}
		// when left is not entry and right is
		if ((!this.leftNode.isEntry()) && (this.rightNode.isEntry())) {
			ArrayList<Node> leftSuccessors = this.leftNode.getSuccessors();
			Set<HyperEdge> allHyperEdges = new HashSet<HyperEdge>();
			for (int i = 0; i < leftSuccessors.size(); i++) {
				Node leftNode = leftSuccessors.get(i);
				PairStep unwindLeft = PairStep.getNewPairStep(this, leftNode, this.rightNode, this.unwindPairDAG);
				this.successors.add(unwindLeft);
				this.successorsMapNode.put(unwindLeft, leftNode);
				HyperEdge hyperEdge = new HyperEdge(this);
				hyperEdge.addLeftMain(unwindLeft);
				allHyperEdges.add(hyperEdge);
				this.leftProgram.add(unwindLeft);
			}
			this.successorHyperEdge.addAll(allHyperEdges);
			this.unwindPairDAG.insertNewGroupOfSteps(allHyperEdges,this);
		}
		// when left is entry and right is not
		if ((this.leftNode.isEntry()) && (!this.rightNode.isEntry())) {
			ArrayList<Node> rightSuccessors = this.rightNode.getSuccessors();
			Set<HyperEdge> allHyperEdges = new HashSet<HyperEdge>();
			for (int i = 0; i < rightSuccessors.size(); i++) {
				Node rightNode = rightSuccessors.get(i);
				PairStep unwindRight = PairStep.getNewPairStep(this, this.leftNode, rightNode, this.unwindPairDAG);
				this.successors.add(unwindRight);
				this.successorsMapNode.put(unwindRight, rightNode);
				HyperEdge hyperEdge = new HyperEdge(this);
				hyperEdge.addRightMain(unwindRight);
				allHyperEdges.add(hyperEdge);
				this.rightprogram.add(unwindRight);
			}
			this.successorHyperEdge.addAll(allHyperEdges);
			this.unwindPairDAG.insertNewGroupOfSteps(allHyperEdges,this);
		}
		// when both are entry steps
		if((this.leftNode.isEntry())&&(this.rightNode.isEntry())){
			this.unwindPairDAG.setEntryStep(this);
			this.isEntry=true;
		}
		this.isUnwind=true;

	}
	public Node getSuccessorCorrespondNode(PairStep pStep){
		return this.successorsMapNode.get(pStep);
	}
	public Node getLeftNode(){
		return this.leftNode;
	}
	public Node getRightNode(){
		return this.rightNode;
	}
	public int getType(){
		return this.type;
	}
	public long getLeftId(){
		return this.leftStepId;
	}
	public long getRightId(){
		return this.rightStepId;
	}
	public boolean ifUnwind(){
		return this.isUnwind;
	}
	public boolean isInPath(Set<Node> leftPath,Set<Node> rightPath){
		if(!leftPath.contains(this.leftNode)){
			return false;
		}
		if(!rightPath.contains(this.rightNode)){
			return false;
		}
		return true;
	}
	public void addInterpolants(BoolExpr I){
		if(!this.ifFalse){
		this.interpolant=this.unwindPairDAG.getIctx().mkAnd(this.interpolant,I);
		this.lastInterpolant=I;
		this.interpolant=Z3Utility.getSimplify(this.interpolant, this.getIctx());
		if(Z3Utility.ifFalse(interpolant, this.getIctx())){
			this.ifFalse=true;
			Set<PairStep> successors=this.getAllSuccessors();
			for(PairStep successor:successors){
				successor.setInterpolantFasle();
			}
		}}
		else{
			this.interpolant=this.getIctx().mkFalse();
		}
       /* System.out.println("after simplify");
		System.out.println(this.interpolant.toString()); */
	}
	public boolean isSafe(){
		if((this.isSafe)||(this.ifFalse)){
			return true;
		}
		else{
			return false;
		}
	}
	public boolean isFalse(){
		return this.ifFalse;
	}
	public void setSafe(){
		this.isSafe=true;
	}
	// return the sum of left and right steps to entry
	public int getSumOfSteps(){
		int sum=0;
		sum=sum+this.leftNode.getStepsToEntry();
		sum=sum+this.rightNode.getStepsToEntry();
		return sum;
		
	}
	public void printUnit(){
		System.out.println("left unit: "+this.leftNode.getStmt().toString()+",right unit:"+this.rightNode.getStmt().toString());
	}
	public BoolExpr getInterpolants(){
		return this.interpolant;
	}
    static public void addVertexAndEdge(SimpleDirectedGraph<PairStep, DefaultEdge> graph){
		for(Entry<String,PairStep> p:createdStep.entrySet()){
			graph.addVertex(p.getValue());
		}
		 for(Entry<String,PairStep> p:createdStep.entrySet()){
			PairStep theStep=p.getValue();
			Set<PairStep> successors=theStep.getSuccessors();
			for(PairStep successor:successors){
				graph.addEdge(theStep, successor);
			}
		}
	}
    static public void RemoveVertexAndEdge(SimpleDirectedGraph<PairStep, DefaultEdge> graph){
    	for(Entry<String,PairStep> p:createdStep.entrySet()){
			PairStep theStep=p.getValue();
			Set<PairStep> successors=theStep.getSuccessors();
			for(PairStep successor:successors){
				graph.removeAllEdges(theStep, successor);
			}
		}
    	for(Entry<String,PairStep> p:createdStep.entrySet()){
			graph.removeVertex(p.getValue());
		}
    }
	static public void addSpecialVertexAndEdge(SimpleDirectedGraph<PairStep, DefaultEdge> graph,Set<PairStep> entrySet){
		Set<PairStep> includedStep=new HashSet<PairStep>();
		for(PairStep entryStep:entrySet){
			Set<PairStep> allPairSteps=entryStep.CollecttParents();
			for(PairStep pStep:allPairSteps){
				includedStep.add(pStep);
			}
			includedStep.add(entryStep);
		}
		for(PairStep pStep:includedStep){
			graph.addVertex(pStep);
		}
		for(PairStep pStep:includedStep){
			Set<PairStep> successors=pStep.getSuccessors();
			for(PairStep successor:successors){
				if(includedStep.contains(successor)){
					graph.addEdge(pStep, successor);
				}
			}
		}
		
		
	}
	public Set<HyperEdge> getSuccessorHyperEdge(){
		return this.successorHyperEdge;
	}
	public void checkAllUsed(){
		for(HyperEdge hEdge:this.successorHyperEdge){
			if((!hEdge.isCovered())&&(!hEdge.isUnwind())){
				System.out.println("there are some error");
			}
		}
		for(PairStep pStep:this.successors){
			pStep.checkAllUsed();
		}
	}
	public InterpolationContext getIctx(){
		return this.unwindPairDAG.getIctx();
	}
	public int getCount(){
		return this.count;
	}
	public void resetSafe(){
		this.isSafe=false;
	}
	static public void clearSafe1(){
		for(Entry<String,PairStep> pairStep:createdStep.entrySet()){
			PairStep pStep=pairStep.getValue();
			pStep.resetSafe();
		}
	}
	public Set<PairStep> getLeftProgram(){
		return this.leftProgram;
	}
	public Set<PairStep> getRightProgram(){
		return this.rightprogram;
	}
	public ArrayList<Node> getLeftProgramExtension(){
		return this.leftProgramNode;
	}
	public ArrayList<Node> getRightProgramExtension(){
		return this.rightProgramNode;
	}
	public void SetIsRefine(){
		this.isRefine=true;
	}
	public boolean IfRefine(){
		return this.isRefine;
	}
	public BoolExpr getLastInterpolant(){
		return this.lastInterpolant;
	}
	public void setInterpolantFasle(){
		this.interpolant=this.getIctx().mkFalse();
		this.ifFalse=true;
		Set<PairStep> allSuccessors=this.getAllSuccessors();
		for(PairStep p:allSuccessors){
			p.setSingleInterpolantFalse();
		}
	}
	public void setSingleInterpolantFalse(){
		this.ifFalse=true;
		this.interpolant=this.getIctx().mkFalse();
	}
	
}
