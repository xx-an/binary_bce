package controlflow;

import java.util.ArrayList;
import java.util.HashMap;

import com.microsoft.z3.BitVecExpr;

import block.Block;
import block.Store;
import common.Lib;
import common.Triplet;
import common.Tuple;
import common.Lib.TRACE_BACK_RET_TYPE;
import common.Utils;
import semantics.SemanticsTBMemAddr;
import semantics.SemanticsTB;
import semantics.SemanticsTBSym;
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
	
	
	static Tuple<Integer, Boolean> tracebackSymAddr(HashMap<Integer, Block> blockMap, HashMap<Long, String> addressExtFuncMap, HashMap<Long, String> dllFuncInfo, HashMap<Long, String> addressInstMap, Block blk, ArrayList<HashMap<Integer, ArrayList<String>>> traceBIDSymList, HashMap<String, Integer> memLenMap, ArrayList<String> symNames) {
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
                TBRetInfo tbInfo = SemanticsTBSym.parse_sym_src(addressExtFuncMap, dllFuncInfo, addressInstMap, pBlock.store, currRIP, currInst, tmpSymList);
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
    
    
	static Triplet<Lib.TRACE_BACK_RET_TYPE, ArrayList<String>, Integer> tracebackIndirectJumps(HashMap<Integer, Block> blockMap, Block blk, ArrayList<String> symNames, HashMap<String, Integer> memLenMap, ArrayList<Block> traceBlockList) {
        Utils.logger.info("\nResolve indirect jump address");
        for(int i = 0; i < Utils.MAX_TRACEBACK_COUNT; i++) {
            Store pStore = CFHelper.getParentStore(blockMap, blk);
            if(pStore == null) {
                return new Triplet<>(Lib.TRACE_BACK_RET_TYPE.TB_PARENT_BLOCK_DOES_NOT_EXIST, symNames, 0);
            }
            TBRetInfo retInfo = SemanticsTB.parse_sym_src(pStore, blk.store.rip, blk.inst, symNames);
            ArrayList<String> srcNames = retInfo.srcNames;
            boolean haltPoint = retInfo.haltPoint;
            Integer boundary = retInfo.boundary;
            boolean stillTB = retInfo.stillTB;
            HashMap<String, Integer> mLenMap = retInfo.memLenMap;
            memLenMap.putAll(mLenMap);
            Utils.logger.info(Utils.num_to_hex_string(blk.address) + ": " + blk.inst);
            Utils.logger.info(srcNames.toString());
            if(haltPoint && srcNames.size() == 1) {
                return new Triplet<>(Lib.TRACE_BACK_RET_TYPE.JT_SUCCEED, srcNames, boundary);
            }
            else if(stillTB) {
            	traceBlockList.add(blk);
                blk = blockMap.get(blk.parent_id);
                symNames = srcNames;
            }
            else { 
                Utils.logger.info("Traceback ends due to unresolved indirect jumps\n");
                break;
            }
        }
        return new Triplet<>(Lib.TRACE_BACK_RET_TYPE.JT_UNRESOLVED, symNames, 0);
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
    
    
    static void locatePointerRelatedError(HashMap<Integer, Block> blockMap, HashMap<Long, String> addressExtFuncMap, HashMap<Long, String> addressInstMap, HashMap<BitVecExpr, ArrayList<String>> addressSymTable, Block block, Store initStore, long address, String inst, ArrayList<String> symNames) {
        // store, rip = store, store.rip
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
            	TBRetInfo tbInfo = SemanticsTBMemAddr.parse_sym_src(addressExtFuncMap, addressInstMap, addressSymTable, pBlock.store, currStore.rip, inst, tmpNames);
            	srcNames = tbInfo.srcNames;
            	boolean funcCallPoint = tbInfo.funcCallPoint;
            	boolean haltPoint = tbInfo.haltPoint;
            	boolean concrete_val = tbInfo.concrete_val;
                Utils.logger.info(Utils.num_to_hex_string(currBlk.address) + ": " + currBlk.inst);
                Utils.logger.info(srcNames.toString());
                Utils.output_logger.info("Trace back to " + srcNames.toString() + " after " + Utils.num_to_hex_string(currBlk.address) + ": " + currBlk.inst);
                bIDSymMap = CFHelper.retrieveBIDSymInfo(pBlock.store, pBlock.store.rip, srcNames);
                if(funcCallPoint || haltPoint || concrete_val) continue;
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
