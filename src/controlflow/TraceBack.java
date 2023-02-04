package controlflow;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Random;

import com.microsoft.z3.BitVecExpr;

import block.Block;
import block.Constraint;
import block.Store;
import common.Config;
import common.Helper;
import common.Lib;
import common.Triplet;
import common.Tuple;
import common.Lib.TRACE_BACK_RET_TYPE;
import common.Utils;
import semantics.SemanticsTBMemAddr;
import semantics.Semantics;
import semantics.SemanticsTB;
import semantics.SemanticsTBSym;
import semantics.TBRetInfo;
import symbolic.SymEngine;

public class TraceBack {
	
	TraceBack() {}

	static String pp_tb_debug_info(TRACE_BACK_RET_TYPE retType, long address, String inst) {
	    String res = "The path is unsound due to ";
	    res += retType.toString().toLowerCase();
	    res += " at " + Long.toHexString(address) + ": " + inst;
	    return res;
	}


	static boolean reach_traceback_halt_point(HashMap<Integer, ArrayList<String>> bIDSymMap) {
		boolean res = false;
		if(bIDSymMap.size() == 1) {
			for(Integer bID: bIDSymMap.keySet()) {
				ArrayList<String> symInfo = bIDSymMap.get(bID);
				if(symInfo.size() == 1) {
					String symName = symInfo.get(0);
					if((symName == "rdi" || symName == "rsi") && bID < 12)
			            res = true;
				}
			}
		}
		return res;
	}
	
	
	static Triplet<Integer, Boolean, Boolean> tracebackSymAddr(HashMap<Integer, Block> blockMap, HashMap<Long, String> addressExtFuncMap, HashMap<Long, String> dllFuncInfo, HashMap<Long, String> addressInstMap, Block blk, ArrayList<HashMap<Integer, ArrayList<String>>> traceBIDSymList, HashMap<String, Integer> memLenMap, ArrayList<String> symNames) {
        Utils.logger.info("Trace back for symbolized memory address");
        Utils.logger.info(Long.toHexString(blk.address) + ": " + blk.inst);
        Store store = blk.store;
        long rip = store.rip;
        boolean tbHaltPoint = false;
        boolean funcCallPoint = false;
        int count = 0;
        ArrayList<String> srcNames = null;
        HashMap<Integer, ArrayList<String>> bIDSymMap = new HashMap<Integer, ArrayList<String>>();
        bIDSymMap = CFHelper.updateBIDSymInfo(bIDSymMap, store, rip, symNames);
        ArrayList<Integer> bIDList = null;
        ArrayList<String> symList = null;
        while(bIDSymMap != null && count < Utils.MAX_TRACEBACK_COUNT) {
        	bIDList = (ArrayList<Integer>) bIDSymMap.keySet();
        	Collections.sort(bIDList);
        	Integer currBlockID = bIDList.get(bIDList.size() - 1);
        	symList = bIDSymMap.get(currBlockID);
        	String currSymName = symList.remove(0);
        	if(symList == null) 
        		bIDSymMap.remove(currBlockID);
            if(currBlockID != -1) {
                Block currBlk = blockMap.get(currBlockID);
                Store currStore = currBlk.store;
                long currRIP = currStore.rip;
                String currInst = currBlk.inst;
                Block pBlock = CFHelper.getParentBlockInfo(blockMap, currBlk);
                if(pBlock == null)
                    return new Triplet<>(-1, true, true);
                ArrayList<String> tmpSymList = new ArrayList<>();
                tmpSymList.add(currSymName);
                TBRetInfo tbInfo = SemanticsTBSym.parse_sym_src(addressExtFuncMap, dllFuncInfo, addressInstMap, pBlock.store, currRIP, currInst, tmpSymList);
                srcNames = tbInfo.src_names;
                funcCallPoint = tbInfo.func_call_point;
                tbHaltPoint = tbInfo.halt_point;
                HashMap<String, Integer> mLenMap = tbInfo.mem_len_map;
                memLenMap.putAll(mLenMap);
                Utils.logger.info("Block id " + Integer.toString(currBlockID) + ": " + Long.toHexString(currBlk.address) + "  " + currInst);
                Utils.logger.info(srcNames.toString());
                if(funcCallPoint)
                    // _update_external_assumptions(curr_store, curr_rip, curr_inst, src_names)
                	traceBIDSymList.add(bIDSymMap);
                    // break
                else if(tbHaltPoint)
                	traceBIDSymList.add(bIDSymMap);
                    // break
                else if(reach_traceback_halt_point(bIDSymMap)) {
                	tbHaltPoint = true;
                    // _update_external_assumptions(curr_store, curr_rip, curr_inst, src_names)
                    // break
                }
                else {
                	bIDSymMap = CFHelper.updateBIDSymInfo(bIDSymMap, pBlock.store, currRIP, srcNames);
            // else {
            //     tb_halt_point = true
            //     break
                }
            }
            count += 1;
        }
        return new Triplet<>(count, tbHaltPoint, funcCallPoint);
    }
    
    
	static Triplet<Lib.TRACE_BACK_RET_TYPE, ArrayList<String>, Integer> tracebackIndirectJumps(HashMap<Integer, Block> blockMap, Block blk, ArrayList<String> symNames, HashMap<String, Integer> memLenMap, ArrayList<Block> traceBlockList) {
        Utils.logger.info("Resolve indirect jump address");
        for(int i = 0; i < Utils.MAX_TRACEBACK_COUNT; i++) {
            Store pStore = CFHelper.getParentStore(blockMap, blk);
            if(pStore == null) {
                return new Triplet<>(Lib.TRACE_BACK_RET_TYPE.TB_PARENT_BLOCK_DOES_NOT_EXIST, symNames, 0);
            }
            TBRetInfo retInfo = SemanticsTB.parse_sym_src(pStore, blk.store.rip, blk.inst, symNames);
            ArrayList<String> srcNames = retInfo.src_names;
            boolean needStop = retInfo.need_stop;
            int boundary = retInfo.boundary;
            boolean stillTB = retInfo.still_tb;
            HashMap<String, Integer> mLenMap = retInfo.mem_len_map;
            memLenMap.putAll(mLenMap);
            Utils.logger.info(Long.toHexString(blk.address) + ": " + blk.inst);
            Utils.logger.info(srcNames.toString());
            if(needStop && srcNames.size() == 1) {
                return new Triplet<>(Lib.TRACE_BACK_RET_TYPE.JT_SUCCEED, srcNames, boundary);
            }
            else if(stillTB) {
            	traceBlockList.add(blk);
                blk = blockMap.get(blk.parent_id);
                symNames = srcNames;
            }
            else { 
                Utils.logger.info("\n");
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
        Utils.logger.info(Long.toHexString(address) + ": " + block.inst);
        Utils.output_logger.info("Trace back to " + symNames.toString() + " after " + Long.toHexString(block.address) + ": " + block.inst);
        boolean tbHaltPoint = false;
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
        	ArrayList<String> currSymNames = node.symNames;
        	Store currStore = currBlk.store;
        	String currInst = currBlk.inst;
            Block pBlock = CFHelper.getParentBlockInfo(blockMap, currBlk);
            if(pBlock == null) return;
            for(String symName : symNames) {
            	ArrayList<String> tmpNames = new ArrayList<>();
            	tmpNames.add(symName);
            	TBRetInfo tbInfo = SemanticsTBMemAddr.parse_sym_src(addressExtFuncMap, addressInstMap, addressSymTable, pBlock.store, currStore.rip, inst, tmpNames);
            	srcNames = tbInfo.src_names;
            	boolean funcCallPoint = tbInfo.func_call_point;
            	boolean haltPoint = tbInfo.halt_point;
            	boolean concrete_val = tbInfo.concrete_val;
                Utils.logger.info(Long.toHexString(currBlk.address) + ": " + currBlk.inst);
                Utils.logger.info(srcNames.toString());
                Utils.output_logger.info("Trace back to " + srcNames.toString() + " after " + Long.toHexString(currBlk.address) + ": " + currBlk.inst);
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
