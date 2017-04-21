package equivalence;

import java.util.HashSet;
import java.util.Set;

public class HyperEdge {
	private Set<PairStep> members;
	// the pair step that this groupSteps attach to
	private PairStep parent;
	// 1 means left and right statement are both not return statement, 2 means left is return statement,3 means right is
	// return statement, 4 means that both are return statement
	private int type;
	// at most four PairStep in groupSteps
	private PairStep leftMain;
	private PairStep leftCall;
	private PairStep rightMain;
	private PairStep rightCall;
	public HyperEdge(PairStep parent){
		this.members=new HashSet<PairStep>();
		this.parent=parent;
		if(parent==null){
			this.type=0;
		}
		else{
		this.type=parent.getType();
		}
	}
	public PairStep getParent(){
		return this.parent;
	}
	public void  addLeftMain(PairStep pStep){
		this.leftMain=pStep;
		this.addStep(pStep);
	}
	public PairStep getLeftMain(){
		return this.leftMain;
	}
	public void addLeftCall(PairStep pStep){
		this.leftCall=pStep;
		this.addStep(pStep);
	}
	public PairStep getLeftCall(){
		return this.leftCall;
	}
	public void addRightMain(PairStep pStep){
		this.rightMain=pStep;
		this.addStep(pStep);
	}
	public PairStep getRightMain(){
		return this.rightMain;
	}
	public void addRightCall(PairStep pStep){
		this.rightCall=pStep;
		this.addStep(pStep);
	}
	public PairStep getRightCall(){
		return this.rightCall;
	}
	private void addStep(PairStep pStep){
		if(!this.members.contains(pStep)){
			this.members.add(pStep);
		}
	}
	public void Unwind(){
		for(PairStep pStep:this.members){
			pStep.unwind();
		}
	}
	public boolean isUnwind(){
		boolean isUnwind=true;
		for(PairStep pStep:this.members){
			if(!pStep.ifUnwind()){
				isUnwind=false;
				break;
			}
		}
		return isUnwind;
	}
	public boolean isInPath(Set<Node> leftPath,Set<Node> rightPath){
		boolean result=true;
		for (PairStep pStep:this.members){
			if(!pStep.isInPath(leftPath, rightPath)){
				result=false;
				break;
			}
		}
		return result;
	}
	public Set<PairStep> getMembers(){
		return this.members;
	}
	public boolean isCovered(){
		boolean result=false;
		for(PairStep p:this.members){
			if(p.isSafe()){
				result=true;
				break;
			}
		}
		return result;
	}
}
