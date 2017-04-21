package dot_output;

import org.jgrapht.ext.VertexNameProvider;

import equivalence.PairStep;
import soot.Unit;

public class vertexID implements VertexNameProvider<PairStep>{
	@Override
	public String getVertexName(PairStep p) {
		return p.getId();
	}

}
