package dot_output;

import org.jgrapht.ext.VertexNameProvider;

import com.microsoft.z3.BoolExpr;

import equivalence.PairStep;
import soot.Unit;
import z3_helper.Z3Utility;

public class vertexName2  implements VertexNameProvider<PairStep>{
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
		if(p.getLastInterpolant()!=null){
	    result=result+"interpolant of this refinement\n";
		BoolExpr currentInterpolants=Z3Utility.getSimplify(p.getLastInterpolant(), p.getIctx());
		result=result+currentInterpolants.toString()+"\n"; 
	    }
		result=result.replaceAll("\n", "\\\\n");
		return result;
	}

}
