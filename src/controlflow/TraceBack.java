package controlflow;

import java.util.ArrayList;
import java.util.HashMap;

import block.Block;
import block.Store;
import common.Tuple;
import common.Lib.TRACE_BACK_RET_TYPE;
import common.Utils;
import semantics.SemanticsTB;
import semantics.TBRetInfo;

public class TraceBack {

	static String pp_tb_debug_info(TRACE_BACK_RET_TYPE retType, long address, String inst) {
	    String res = "The path is unsound due to ";
	    res += retType.toString().toLowerCase();
	    res += " at " + Utils.num_to_hex_string(address) + ": " + inst + "\n";
	    return res;
	}


	static boolean reach_traceback_halt_point(HashMap<Integer, ArrayList<String>> bIDSymMap) {
		boolean res = false;
		if(bIDSymMap.size() == 1) {
			for(Integer bID: bIDSymMap.keySet()) {
				ArrayList<String> symInfo = bIDSymMap.get(bID);
				if(symInfo.size() == 1) {
					String symName = symInfo.get(0);
					if((symName.equals("rdi") || symName.equals("edi") || symName.equals("rsi") || symName.equals("esi")) && bID < 12)
			            res = true;
				}
			}
		}
		return res;
	}
	
	
	static Tuple<Integer, Boolean> tracebackSymAddr(HashMap<Integer, Block> blockMap, HashMap<Long, String> addressExtFuncMap, HashMap<Long, String> addressInstMap, Block blk, ArrayList<HashMap<Integer, ArrayList<String>>> traceBIDSymList, HashMap<String, Integer> memLenMap, ArrayList<String> symNames) {
        Utils.logger.info("Trace back for symbolized memory address");
        Utils.logger.info(Utils.num_to_hex_string(blk.address) + ": " + blk.inst);
        Store store = blk.store;
        long rip = store.rip;
        boolean funcCallPoint = false;
        int count = 0;
        ArrayList<String> srcNames = null;
        HashMap<Integer, ArrayList<String>> bIDSymMap = new HashMap<Integer, ArrayList<String>>();
        bIDSymMap = CFHelper.updateBIDSymInfo(bIDSymMap, store, rip, symNames);
        ArrayList<Integer> bIDList = null;
        ArrayList<String> symList = null;
        while(bIDSymMap != null && bIDSymMap.size() > 0 && count < Utils.MAX_TRACEBACK_COUNT) {
        	bIDList = new ArrayList<Integer>();
        	bIDList.addAll(bIDSymMap.keySet());
        	Integer currBlockID = bIDList.get(bIDList.size() - 1);
        	symList = bIDSymMap.get(currBlockID);
        	String currSymName = symList.remove(0);
        	if(symList == null || symList.size() == 0) 
        		bIDSymMap.remove(currBlockID);
            if(currBlockID != -1) {
                Block currBlk = blockMap.get(currBlockID);
                Store currStore = currBlk.store;
                long currRIP = currStore.rip;
                String currInst = currBlk.inst;
                Block pBlock = CFHelper.getParentBlockInfo(blockMap, currBlk);
                if(pBlock == null)
                    return new Tuple<>(-1, true);
                ArrayList<String> tmpSymList = new ArrayList<>();
                tmpSymList.add(currSymName);
                TBRetInfo tbInfo = SemanticsTB.parse_sym_src(addressExtFuncMap, addressInstMap, pBlock.store, currRIP, currInst, tmpSymList);
                srcNames = tbInfo.srcNames;
                funcCallPoint = tbInfo.funcCallPoint;
                HashMap<String, Integer> mLenMap = tbInfo.memLenMap;
                memLenMap.putAll(mLenMap);
                Utils.logger.info("Block id " + Integer.toString(currBlockID) + ": " + Utils.num_to_hex_string(currBlk.address) + "  " + currInst);
                Utils.logger.info(srcNames.toString());
                if(funcCallPoint) {
                	traceBIDSymList.add(bIDSymMap);
                }
                else if(reach_traceback_halt_point(bIDSymMap)) {
                	traceBIDSymList.add(bIDSymMap);
                }
                else {
                	bIDSymMap = CFHelper.updateBIDSymInfo(bIDSymMap, pBlock.store, currRIP, srcNames);
                }
            }
            count += 1;
        }
        Utils.logger.info("Traceback ends\n");
        return new Tuple<>(count, funcCallPoint);
    }
        

    static BlockNode updateBlockNode(HashMap<Integer, Block> blockMap, int blockID, String symName, Block prevBlock) {
    	BlockNode node = null;
        if(blockMap.containsKey(blockID)) {
            node = new BlockNode(null);
            Block block = blockMap.get(blockID);
            node.setBlock(block);
            ArrayList<String> symNames = new ArrayList<>();
            symNames.add(symName);
            node.setSymNames(symNames);
            node.setPrevBlock(prevBlock);
        }
        return node;
    }
    
    
    static void locatePointerRelatedError(HashMap<Integer, Block> blockMap, HashMap<Long, String> addressExtFuncMap, HashMap<Long, String> addressInstMap, HashMap<Long, String> addressSymTable, Block block, Store initStore, long address, String inst, ArrayList<String> symNames) {
        Utils.logger.info("Trace back for pointer-related error");
        Utils.logger.info(Utils.num_to_hex_string(address) + ": " + block.inst);
        Utils.output_logger.info("Trace back to " + symNames.toString() + " after " + Utils.num_to_hex_string(block.address) + ": " + block.inst);
        ArrayList<BlockNode> nodeStack = new ArrayList<>();
        ArrayList<String> srcNames = null;
        HashMap<Integer, ArrayList<String>> bIDSymMap = CFHelper.retrieveBIDSymInfo(initStore, initStore.rip, symNames);
        ArrayList<String> symList = null;
        for(Integer currBlockID : bIDSymMap.keySet()) {
        	symList = bIDSymMap.get(currBlockID);
        	for(String currSymName : symList) {
        		BlockNode node = updateBlockNode(blockMap, currBlockID, currSymName, block);
                if(node != null)
                    nodeStack.add(node);
        	}
        }
        Utils.logger.info(symNames.toString());
        while(nodeStack.size() > 0) {
        	BlockNode node = nodeStack.remove(nodeStack.size() - 1);
        	Block currBlk = node.block;
        	Store currStore = currBlk.store;
            Block pBlock = CFHelper.getParentBlockInfo(blockMap, currBlk);
            if(pBlock == null) return;
            for(String symName : symNames) {
            	ArrayList<String> tmpNames = new ArrayList<>();
            	tmpNames.add(symName);
            	TBRetInfo tbInfo = SemanticsTB.parse_sym_src(addressExtFuncMap, addressInstMap, pBlock.store, currStore.rip, inst, tmpNames);
            	srcNames = tbInfo.srcNames;
            	boolean haltPoint = tbInfo.haltPoint;
                Utils.logger.info(Utils.num_to_hex_string(currBlk.address) + ": " + currBlk.inst);
                Utils.logger.info(srcNames.toString());
                Utils.output_logger.info("Trace back to " + srcNames.toString() + " after " + Utils.num_to_hex_string(currBlk.address) + ": " + currBlk.inst);
                bIDSymMap = CFHelper.retrieveBIDSymInfo(pBlock.store, pBlock.store.rip, srcNames);
                if(haltPoint) continue;
                else {
                	for(Integer bID : bIDSymMap.keySet()) {
                		if(bID != null) {
                			if(bID != -1) {
                				symList = bIDSymMap.get(bID);
                				for(String srcName : symList) {
	                            	Block newBlk = blockMap.get(bID);
	                                BlockNode newNode = new BlockNode(node);
	                                newNode.setBlock(newBlk);
	                                newNode.setPrevBlock(currBlk);
	                                ArrayList<String> newSymNames = new ArrayList<>();
	                                newSymNames.add(srcName);
	                                newNode.setSymNames(newSymNames);
	                                node.childrenList.add(newNode);
	                                nodeStack.add(newNode);
                				}
                            }
                		}
                	}
                }
        	}
        }
        Utils.output_logger.info("\n\n");
        Utils.logger.info("\n\n");
    }

}
