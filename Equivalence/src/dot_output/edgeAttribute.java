package dot_output;

import java.util.HashMap;
import java.util.Map;

import org.jgraph.graph.DefaultEdge;
import org.jgrapht.ext.ComponentAttributeProvider;
import org.jgrapht.graph.SimpleDirectedGraph;

import equivalence.PairStep;

public class edgeAttribute implements ComponentAttributeProvider<DefaultEdge>{
       SimpleDirectedGraph<PairStep, DefaultEdge> graph = null;
	
	public edgeAttribute(SimpleDirectedGraph<PairStep, DefaultEdge> graph) {
		this.graph = graph;
	}

	@Override
	public Map<String, String> getComponentAttributes(DefaultEdge edge) {
		Map<String, String> attrs = new HashMap<String, String>();
		PairStep srcV = this.graph.getEdgeSource(edge);
		PairStep dstV = this.graph.getEdgeTarget(edge);
		return attrs;
	}

}
