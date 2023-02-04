package controlflow;

import java.util.ArrayList;

import block.Block;

public class BlockNode {
	
	BlockNode parent;
	
	Block block;
	ArrayList<String> symNames;
	Block prevBlock;
	
	ArrayList<BlockNode> childrenList;
	
	public BlockNode(BlockNode parent) {
		this.parent = parent;
		this.block = null;
		this.symNames = null;
		this.prevBlock = null;
		this.childrenList = new ArrayList<>();
	}
	
	void setBlock(Block blk) {
		this.block = blk;
	}
	
	void setSymNames(ArrayList<String> symNames) {
		this.symNames = symNames;
	}
	
	void setPrevBlock(Block blk) {
		this.prevBlock = blk;
	}
	
}
