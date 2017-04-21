package z3_helper;

import soot.PrimType;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;

public class SpecialInvoker {
	static public boolean ifInvokeExpr(Unit u){
		if (u instanceof InvokeStmt) {
			return true;
		}
		else{
			if (u instanceof AssignStmt) {
				Value right = ((AssignStmt) u).getRightOp();
				if(right instanceof InvokeExpr){
					return true;
				}
			}
		}
		return false;
	}
	static public String getMethodSignature(Unit u) {
		if (u instanceof InvokeStmt) {
			InvokeStmt iStmt = (InvokeStmt) u;
			return iStmt.getInvokeExpr().getMethod().getSignature();
		} else {
			if (u instanceof AssignStmt) {
				Value right = ((AssignStmt) u).getRightOp();
				InvokeExpr iExpr = (InvokeExpr) right;
				return iExpr.getMethod().getSignature();
			}
		}
		return null;
	}
	static public boolean isInput(String s){
		if(s.contains("nextInt()")){
			return true;
		}
		if(s.contains("parseInt")){
			return true;
		}
		return false;
	}
	static public boolean isOutPut(String s){
		if(s.contains("println")){
			return true;
		}
		return false;
	}
	static public boolean isNonsenseDef(Unit u){
		if(u instanceof AssignStmt){
			Value left=((AssignStmt) u).getLeftOp();
			Type t=left.getType();
			if (t instanceof PrimType) {
				return false;
			}
			else{
				return true;
			}
		}
		if(u instanceof IdentityStmt){
			Value left=((IdentityStmt) u).getLeftOp();
			Type t=left.getType();
			if (t instanceof PrimType) {
				return false;
			}
			else{
				return true;
			}
		}
		return false;
	}
}
