package dot_output;

import java.util.HashMap;
import java.util.Map;

import org.jgraph.graph.DefaultEdge;
import org.jgrapht.ext.ComponentAttributeProvider;

import equivalence.PairStep;

public class vertexAttribute implements ComponentAttributeProvider<PairStep>{

	@Override
	public Map<String, String> getComponentAttributes(PairStep pStep) {
		HashMap<String, String> attrs = new HashMap<String, String>();
		if(pStep.getSuccessorHyperEdge().size()>1){
			attrs.put("color", "red");
		}
		if((pStep.getSuccessors().size()==0)){
			attrs.put("color", "green");
		}
		return attrs;
	}

}
