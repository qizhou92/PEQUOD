package z3_helper;

import java.util.Comparator;
import java.util.Set;


public class SetSizeComparator implements Comparator<Set<Integer>>{

	@Override
	public int compare(Set<Integer> o1, Set<Integer> o2) {
		int size1=o1.size();
		int size2=o2.size();
		if(size1>size2){
			return -1;
		}
		if(size1<size2){
			return 1;
		}
		return 0;
	}

}
