package equivalence;

import java.util.Comparator;
import java.util.Set;

public class HyperEdgeComparator implements Comparator<HyperEdge>{
	@Override
	public int compare(HyperEdge n1, HyperEdge n2) {
		int leftLargest=Integer.MIN_VALUE;
		int rightLargest=Integer.MIN_VALUE;
		int leftId=Integer.MIN_VALUE;
		int rightId=Integer.MIN_VALUE;
		Set<PairStep> leftMembers=n1.getMembers();
		Set<PairStep> rightMembers=n2.getMembers();
		for(PairStep leftM:leftMembers){
			if(leftM.getSumOfSteps()>leftLargest){
				leftLargest=leftM.getSumOfSteps();
			}
			if(leftM.getCount()>leftId){
				leftId=leftM.getCount();
			}
		}
		for (PairStep rightM:rightMembers){
			if(rightM.getSumOfSteps()>rightLargest){
				rightLargest=rightM.getSumOfSteps();
			}
			if(rightM.getCount()>rightId){
				rightId=rightM.getCount();
			}
		}
		if (leftLargest<rightLargest){
		return -1;
		}
		if (leftLargest>rightLargest){
		return 1;
		}
		if (leftLargest == rightLargest){
			if (leftId < rightId){
				return -1;
			}
			if (leftId > rightId){
				return 1;
			}
		}
		return 0;
	}
}
