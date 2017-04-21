package dot_output;

import java.util.ArrayList;


import org.jgrapht.ext.VertexNameProvider;

import com.microsoft.z3.ApplyResult;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Goal;
import com.microsoft.z3.InterpolationContext;
import com.microsoft.z3.Tactic;

import equivalence.Node;
import equivalence.PairStep;
import soot.Unit;
import z3_helper.Z3Utility;

public class vertextName implements VertexNameProvider<PairStep>{
	@Override
	public String getVertexName(PairStep p) {
		Unit left=p.getLeftNode().getStmt();
		Unit right=p.getRightNode().getStmt();
		String result="";
		result=result+p.getUnitId()+"\n";
		result=result+p.getId()+"\n";
		result=result+left+"\n";
		result=result+right+"\n";
		/* ArrayList<Node> leftProgram=p.getLeftProgramExtension();
		result=result+"leftProgram(";
		for(int i=0;i<leftProgram.size();i++){
			result=result+leftProgram.get(i).getId()+",";
		}
		result=result+")\n";
		ArrayList<Node> rightProgram=p.getRightProgramExtension();
		result=result+"rightProgram(";
		for(int i=0;i<rightProgram.size();i++){
			result=result+rightProgram.get(i).getId()+",";
		}
		result=result+")\n";*/
		//result=result+p.getUnitId()+"\n";
		//result=result+p.getCount()+"\n";
	    //result=result+left.toString()+"\n"+right.toString()+"\n";
	    result=result+"interpolant of all refinement\n";
	    BoolExpr interpolants=p.getInterpolants();
		interpolants=Z3Utility.getSimplify(interpolants, p.getIctx());
		result=result+interpolants.toString();
		if(p.isSafe()){
			result=result+"\n Safe";
		}
		result=result.replaceAll("\n", "\\\\n");
		return result;
	}
}
