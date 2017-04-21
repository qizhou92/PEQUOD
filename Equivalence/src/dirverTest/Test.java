package dirverTest;

import java.io.IOException;


import java.io.PrintWriter;

import com.microsoft.z3.InterpolationContext;
import com.microsoft.z3.Model;

import equivalence.Node;
import equivalence.PairDAG;
import equivalence.PairStep;
import soot.Body;
import soot.toolkits.graph.ExceptionalUnitGraph;

public class Test extends Thread{

	private Body left;
	private Body right;
	private String Name;
	private PrintWriter equivalent;
	private PrintWriter notEquivalent;
	public Test(Body leftBody,Body rightBody,String rightName,PrintWriter equivalent,PrintWriter NotEquivalent){
		this.left=leftBody;
		this.right=rightBody;
		this.Name=rightName;
		this.equivalent=equivalent;
		this.notEquivalent=NotEquivalent;
	}
	
 @Override
    public void run() {
		  long startTime = System.currentTimeMillis();
	      ExceptionalUnitGraph cfgLeft = new ExceptionalUnitGraph(this.left);
		  ExceptionalUnitGraph cfgRight = new ExceptionalUnitGraph(this.right);
		  PairDAG theSolver = new PairDAG(cfgLeft, cfgRight, "test");
			try {
				if (theSolver.isEquivalent()) {
					long endTime   = System.currentTimeMillis();
					long totalTime = endTime - startTime;
					this.equivalent.println(this.Name+":"+"is equivalent"+" time:"+totalTime);
					this.equivalent.flush();
					InterpolationContext ictx=theSolver.getIctx();
				} else {
					this.notEquivalent.println(this.Name+":"+"are different");
					this.notEquivalent.flush();
					InterpolationContext ictx=theSolver.getIctx();
				}
			} catch (IOException e) {
			}
    }
}
