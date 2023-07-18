package block;

public class Block {
	static int cnt = -1;
	
	public int parentID = -1;
	public int blockID = -1;
	public long address = -1;
	public String inst = null;
	public Store store = null;
	public Constraint constraint = null;
	
	public Block(int parentID, long address, String inst, Store store, Constraint constraint) {
		this.parentID = parentID;
		this.address = address;
		this.inst = inst;
		this.store = store;
		this.constraint = constraint;
        blockID = cnt;
        cnt += 1;
	}        		
}
