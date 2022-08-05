package block;

import java.util.ArrayList;

public class Block {
	static int cnt = -1;
	
	public int parent_id = -1;
	public int block_id = -1;
	public long address = -1;
	public String inst = null;
	public Store store = null;
	public Constraint constraint = null;
	ArrayList<Integer> children_blk_list;
	
	public Block(Integer parent_no, Long address, String inst, Store store, Constraint constraint) {
		this.parent_id = parent_no;
		this.address = address;
		this.inst = inst;
		this.store = store;
		this.constraint = constraint;
        children_blk_list = new ArrayList<Integer>();
        block_id = cnt;
        cnt += 1;
	}
	
	public void add_to_children_list(int block_id) {
		children_blk_list.add(block_id);
	}
		        		
}
