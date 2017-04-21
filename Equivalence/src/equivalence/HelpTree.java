package equivalence;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;

import soot.Unit;
import soot.Value;
import soot.JastAddJ.ThisAccess;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.toolkits.graph.ExceptionalUnitGraph;

public class HelpTree {
	private ExceptionalUnitGraph cfg;
	private Map<Unit, Integer> shortestPath;
	private boolean findReturn;
	private Unit returnUnit;
	private Unit root;
	private Map<String, HelpTree> stores;
	private boolean ifModified;
    private Map<Unit,Integer> UnitId;
	public HelpTree(ExceptionalUnitGraph cfg) {
		this.cfg = cfg;
		int id=1;
		this.UnitId=new HashMap<Unit,Integer>();
		for(Unit u:cfg){
			this.UnitId.put(u, id);
			id++;
		}
		this.shortestPath = new HashMap<Unit, Integer>();
		this.root = this.cfg.getHeads().get(0);
		Set<Unit> expandSet=new HashSet<Unit>();
		Unit returnUnit=null;
		for(Unit u:this.cfg){
			if(u instanceof ReturnStmt){
				returnUnit=u;
			}
			if(u instanceof ReturnVoidStmt){
				returnUnit=u;
			}
		}
		expandSet.add(returnUnit);
		this.getUnitSteps(expandSet, 0);
		Map<Unit,Integer> newShortestPath=new HashMap<Unit,Integer>();
		for(Entry<Unit,Integer> theUnit:this.shortestPath.entrySet()){
			int currentValue=theUnit.getValue();
			newShortestPath.put(theUnit.getKey(), currentValue);
		}
		this.shortestPath=newShortestPath;
		System.out.println("ready to print");
	}
	private void getUnitSteps(Set<Unit> expandSet,int depth){
		if(!expandSet.isEmpty()){
			Set<Unit> nextSet=new HashSet<Unit>();
			for(Unit u:expandSet){
				this.shortestPath.put(u, depth);
				List<Unit> successors=this.cfg.getUnexceptionalPredsOf(u);
				for(int i=0;i<successors.size();i++){
					Unit successor=successors.get(i);
				if(!nextSet.contains(successor)){
					nextSet.add(successor);
				}
				}
				if (u instanceof ReturnStmt){
					this.returnUnit=u;
				}
				
			}
			Set<Unit> realExpandSet=new HashSet<Unit>();
			for (Unit u:nextSet){
				if(!this.shortestPath.containsKey(u)){
					realExpandSet.add(u);
				}
			}
		getUnitSteps(realExpandSet, depth+1);
		}
	}
	public int getNodeShortest(Unit statment){
		return this.shortestPath.get(statment);
	}
	public int getUnitId(Unit statement){
		return this.UnitId.get(statement);
	}
	public Unit getRoot() {
		return this.root;
	}
	public Unit getReturn(){
		return this.returnUnit;
	}
	public void print(){
		for(Entry<Unit,Integer> e:this.shortestPath.entrySet()){
			System.out.println(e.getKey().toString()+":"+e.getValue());
		}
	}
	static boolean tooLarge(ExceptionalUnitGraph cfg){
		int i=0;
		for(Unit u:cfg){
			i++;
		}
		if(i>30){
			return true;
		}
		return false;
	}
}
