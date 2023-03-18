package block;

import java.util.ArrayList;

import com.microsoft.z3.BoolExpr;

public class Constraint {
	
	BoolExpr predicate;
	Constraint parent;
	
	public Constraint(Constraint parent, BoolExpr last_predicate) {
		this.parent = parent;
        this.predicate = last_predicate;
	}

	public boolean equals(Constraint other) {
        if(!(predicate.equals(other.predicate)))
            return false;
        return parent.equals(other.parent);
	}

    void update_predicate(BoolExpr last_predicate) {
        predicate = last_predicate;
    }

    public ArrayList<BoolExpr> get_asserts() {
    	ArrayList<BoolExpr> asserts = new ArrayList<BoolExpr>();
        Constraint tmp = parent;
        asserts.add(predicate);
        while(tmp != null && tmp.parent != null) {
            asserts.add(tmp.predicate);
            tmp = tmp.parent;
        }
        return asserts;
    }

    public String toString() {
    	StringBuilder sb = new StringBuilder();
    	sb.append(predicate.toString());
    	if(parent != null) {
    		sb.append(String.format("\\l%s", parent.toString()));
    	}
    	return sb.toString();
    }
        		
}
