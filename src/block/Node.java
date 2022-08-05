package block;

import com.microsoft.z3.BitVecExpr;

public class Node {
	public BitVecExpr expr;
	public Integer block_id;
	
	public Node(BitVecExpr expr, int block_id) {
		update(expr, block_id);
	}
	
	public void update(BitVecExpr expr, int block_id) {
		this.expr = expr;
		this.block_id = block_id;
	}
	
	public void update_expr(BitVecExpr expr) {
		this.expr = expr;
	}
	
}
