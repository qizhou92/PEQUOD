package equivalence;

import java.util.ArrayList;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.InterpolationContext;

import soot.Unit;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.toolkits.graph.ExceptionalUnitGraph;
import z3_helper.ErrorHelper;
import z3_helper.SpecialInvoker;
import z3_helper.Z3Utility;

public class Node {
	static long NumberOfId = 0;
	// if this is entry node
	private boolean isEntry;
	// Each Node has a associate unit(statement) in SSA
	private Unit statment;
	// All successors of this node
	private ArrayList<Node> successors;
	// the predecessor of this node
	private Node parent;
	// if unwind
	private boolean isUnwind;
	// unique id for every node
	private long id;
	// Each node has connect to tree get some overall info
	private HelpTree helpTree;
	// shortest steps to entry
	private int shortestReturn;
	// theCfg
    private ExceptionalUnitGraph cfg;
    // path from root to current node, store in set
    private Set<Node> pathSet;
    // to distinguish left and right program
    private boolean ifLeftProgram;
    // to say if this has multiple predeccsor
    private boolean ifMultiPredecssor;
    // check if this involve a function;
    private boolean noSenseFunction;
    // check if this function is input;
    private boolean inputFunction;
    // check if this output function
    private boolean ifOutput;
	// static constructor to make sure each node has an unique id
   
	static public Node getNewNode(Unit statement, Node parent,
			HelpTree theTree, ExceptionalUnitGraph cfg,boolean ifLeftProgram) {
		Node n1 = new Node(statement, parent, NumberOfId, theTree, cfg,ifLeftProgram);
		NumberOfId++;
		return n1;
	}

	private Node(Unit statement, Node parent, long NumberOfId,HelpTree theTree,ExceptionalUnitGraph cfg,boolean ifLeftProgram) {
		this.ifLeftProgram=ifLeftProgram;
		this.isUnwind=false;
		this.helpTree = theTree;
		this.statment = statement;
		this.successors = new ArrayList<Node>();
		this.parent = parent;
		this.id = NumberOfId;
		this.cfg = cfg;
		this.pathSet=new HashSet<Node>();
		if(this.parent!=null){
		this.pathSet.addAll(parent.getPathSet());
		}
		this.pathSet.add(this);
		this.shortestReturn = this.helpTree.getNodeShortest(
				statement);
		List<Unit> next = this.cfg.getUnexceptionalSuccsOf(statement);
		if(next.isEmpty()){
			this.isEntry=true;
			this.isUnwind=true;
			this.ifMultiPredecssor=false;
		}
		else{
			this.isEntry=false;
		}
		if(next.size()>1){
			this.ifMultiPredecssor=true;
		}
		else{
			this.ifMultiPredecssor=false;
		}
		 List<Unit> successor=this.cfg.getUnexceptionalPredsOf(statement);
		if(successor.size()>1){
			this.ifMultiPredecssor=true;
		}
		this.noSenseFunction=false;
		this.inputFunction=false;
		this.ifOutput=false;
		if(SpecialInvoker.ifInvokeExpr(this.statment)){
			this.noSenseFunction=true;
			String s=SpecialInvoker.getMethodSignature(this.statment);
			if(SpecialInvoker.isInput(s)){
				this.inputFunction=true;
				this.noSenseFunction=false;
			}
			if(SpecialInvoker.isOutPut(s)){
				this.ifOutput=true;
				this.noSenseFunction=false;
			}
		}
		if(SpecialInvoker.isNonsenseDef(this.statment)){
			this.noSenseFunction=true;
		}
		
	}
	public void setPoint(){
		this.ifMultiPredecssor=true;
	}
	public ArrayList<Node> getSuccessors(){
		if(this.isUnwind){
			return this.successors;
		}
		else{
			this.unwind();
			return this.successors;
		}
		
	}
    public long getId(){
    	return this.id;
    }
	public boolean isEntry(){
		return this.isEntry;
	}
	public boolean getIfLeftProgram(){
		return this.ifLeftProgram;
	}
	public void unwind(){
		if(!this.isUnwind){
		List<Unit> next = this.cfg.getUnexceptionalSuccsOf(this.statment);
		for(Unit stmt:next){
			Node successsor=Node.getNewNode(stmt, this,this.helpTree, this.cfg,this.getIfLeftProgram());
			this.successors.add(successsor);
		}
		this.isUnwind=true;
		}
	}
	public boolean isUnwind(){
		return this.isUnwind;
	}
	public int getStepsToEntry(){
		return this.shortestReturn;
	}
	public Node getShortestSuccessor(){
		int minStepsToEntry=Integer.MAX_VALUE;
		Node shortestSuccessor=null;
		for(Node successor:this.successors){
			int stepsToEntry =successor.getStepsToEntry();
			if(stepsToEntry<minStepsToEntry){
				minStepsToEntry=stepsToEntry;
				shortestSuccessor=successor;
			}
		}
		return shortestSuccessor;
	}
	public Set<Node> getPathSet(){
		return this.pathSet;
	}
	public Node getParent(){
		return this.parent;
	}
	public ArrayList<Node> getPath(){
		ArrayList<Node> path=new ArrayList<Node>();
		Node currentNode=this;
		while(currentNode!=null){
			path.add(currentNode);
			currentNode=currentNode.getParent();
		}
		Collections.reverse(path);
		return path;
	}
	public Unit getStmt(){
		return this.statment;
	}
	public int getUnitId(){
		return this.helpTree.getUnitId(this.statment);
	}
	public void printPath(){
		ArrayList<Node> path=this.getPath();
		for(int i=0;i<path.size();i++){
			System.out.println(path.get(i).getStmt().toString()+","+path.get(i).getId());
		}
	}
	public boolean ifMultiPredecssor(){
		return this.ifMultiPredecssor;
	}
	public boolean ifNosense(){
		return this.noSenseFunction;
	}
	public boolean ifOutput(){
		return this.ifOutput;
	}
	public boolean ifInput(){
		return this.ifInput();
	}
}
