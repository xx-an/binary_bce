package controlflow;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;

import block.Block;
import block.Constraint;
import block.Store;
import common.Config;
import common.Helper;
import common.InstElement;
import common.Lib;
import common.Lib.TRACE_BACK_RET_TYPE;
import common.Triplet;
import common.Tuple;
import common.Utils;
import semantics.SMTHelper;
import semantics.Semantics;
import symbolic.SymEngine;
import symbolic.SymHelper;
import normalizer.Normalizer;

public class ControlFlow {
	
	HashMap<Integer, Block> blockMap;
	ArrayList<Block> blockStack;
    HashMap<Long, Block> addrBlockMap;
    HashMap<Long, Integer> addressBlockCntMap;
    HashMap<Long, String> addressExtFuncMap;
    HashMap<String, Integer> memLenMap;
    HashMap<String, Long> symTable;
    HashMap<Long, String> addrSymMap;
    HashMap<Long, String> addrInstMap;
    HashMap<Long, Long> addrNextMap;
    HashMap<Long, HashMap<Long, Integer>> loopTraceCounter;
    HashMap<String, ArrayList<String>> gPreConstraint;
    HashSet<Long> funcEndAddressSet;
    ArrayList<Long> extFuncCallAddr;
    ArrayList<BitVecExpr> extMemPreserv;
    String disasmType;
    Block dummyBlock;
    public int[] cmcExecInfo;
    final Long startAddress;
    final Long mainAddress;
    HashMap<Long, Long> retCallAddressMap;
    HashMap<Long, Triplet<String, String, ArrayList<Long>>> addressJPTEntriesMap;
    HashMap<Long, ArrayList<Long>> globalJPTEntriesMap;
    HashMap<String, ArrayList<String>> extLibAssumptions;
    HashMap<BitVecExpr, ArrayList<BitVecExpr>> symAddrValuesetMap;

    
    public ControlFlow(HashMap<String, ArrayList<String>> gPreConstraint, Normalizer norm) {
    	blockMap = new HashMap<>();
    	blockStack = new ArrayList<>();
        addrBlockMap = new HashMap<>();
        addressBlockCntMap = new HashMap<>();
        loopTraceCounter = new HashMap<>();
        memLenMap = new HashMap<>();
        this.symTable = norm.getSymTbl();
        this.addrSymMap = norm.getAddressSymTbl();
        this.startAddress = norm.getEntryAddress();
        this.addrInstMap = norm.getAddressInstMap();
        this.addrNextMap = norm.getAddressNextMap();
        this.funcEndAddressSet = norm.getFuncEndAddrSet();
        dummyBlock = new Block(-1, 0, "", null, null);
        this.mainAddress = norm.getMainAddress();
        this.gPreConstraint = gPreConstraint;
        retCallAddressMap = new HashMap<>();
        extFuncCallAddr = new ArrayList<>();
        addressJPTEntriesMap = new HashMap<>();
        symAddrValuesetMap = new HashMap<>();
        extLibAssumptions = new HashMap<>();
        extMemPreserv = new ArrayList<>();
        this.addressExtFuncMap = norm.getAddressExtFuncMap();
        this.globalJPTEntriesMap = norm.readGlobalJPTEntriesMap();
        Store store = new Store(null);
        cmcExecInfo = new int[Utils.CMC_EXEC_RES_COUNT];
        Constraint constraint = null;
        SymHelper.cnt_init();
        CFHelper.cfg_init_parameter(store, symTable);
        if(startAddress == null)
        	CFHelper.start_init(store, mainAddress, Utils.INIT_BLOCK_NO);
        else
        	CFHelper.start_init(store, startAddress, Utils.INIT_BLOCK_NO);
        constraint = CFHelper.handlePreConstraint(store, store.rip, constraint, Utils.INIT_BLOCK_NO, gPreConstraint, extLibAssumptions);
        if(startAddress == null)
        	build_cfg(mainAddress, store, constraint);
        else
        	build_cfg(startAddress, store, constraint);
        pp_unreachable_instrs();
    }

        
    void build_cfg(long startAddress, Store startStore, Constraint startConstraint) {
    	String startInst = addrInstMap.get(startAddress);
    	add_new_block(null, startAddress, startInst, startStore, startConstraint);
        while(blockStack != null && blockStack.size() > 0) {
            Block curr = blockStack.remove(blockStack.size() - 1);
            Utils.logger.info(Utils.num_to_hex_string(curr.address) + ": " + curr.inst);
            Utils.logger.info("Block " + Integer.toString(curr.block_id));
            Utils.logger.info(curr.store.pp_reg_store());
            Utils.logger.info(curr.store.pp_mem_store());
            long address = curr.address;
            if(address == 0x403da7) {
            	System.exit(1);
            }
            String inst = curr.inst;
            Store store = curr.store;
            Constraint constraint = curr.constraint;
            if(inst != null && inst.startsWith("bnd "))
                inst = inst.strip().split(" ", 2)[1];
            if(Utils.check_branch_inst(inst))
                construct_branch(curr, address, inst, store, constraint);
            else {
            	if(!funcEndAddressSet.contains(curr.address))
            		_jump_to_next_block(curr, address, store, constraint);
            	else
            		Utils.logger.info("\n");
            }
        }
    }


    void construct_conditional_branches(Block block, long address, String inst, long newAddress, Store store, Constraint constraint) {
        BoolExpr res = SMTHelper.parse_predicate(store, inst, true, "j");
        if(res == null) {
        	long nextAddress = CFHelper.get_next_address(address, addrNextMap, addrSymMap);
            construct_conditional_jump_block(block, address, inst, nextAddress, store, constraint, false, true);
            construct_conditional_jump_block(block, address, inst, newAddress, store, constraint, true, true);
        }
        else {
	        if(res.equals(Helper.SymFalse)) {
	            long nextAddress = CFHelper.get_next_address(address, addrNextMap, addrSymMap);
	            construct_conditional_jump_block(block, address, inst, nextAddress, store, constraint, false, true);
	        }
	        else if(res.equals(Helper.SymTrue)) {
	            construct_conditional_jump_block(block, address, inst, newAddress, store, constraint, true, true);
	        }
	        else {
	            long nextAddress = CFHelper.get_next_address(address, addrNextMap, addrSymMap);
	            construct_conditional_jump_block(block, address, inst, nextAddress, store, constraint, false, true);
	            construct_conditional_jump_block(block, address, inst, newAddress, store, constraint, true, true);
	        }
        }
    }

    void construct_conditional_jump_block(Block block, long address, String inst, long newAddress, Store store, Constraint constraint, boolean val, boolean need_new_constraint) {
        if(addrBlockMap.containsKey(address)) {
        	if(loopTraceCounter.containsKey(address)) {
        		HashMap<Long, Integer> loopInfo = loopTraceCounter.get(address);
        		if(loopInfo.containsKey(newAddress)) {
        			int counter = loopInfo.get(newAddress);
        			if(counter < Utils.MAX_LOOP_COUNT) {
        				loopInfo.put(newAddress, counter + 1);
                        jump_to_block_w_new_constraint(block, inst, newAddress, store, constraint, val, need_new_constraint);
                    }
                    else {
                        Utils.logger.info("The path is terminated since the loop upperbound is hit\n");
                        handle_cmc_path_termination(store);
                    }
        		}
        		else {
        			boolean exists_loop = CFHelper.detect_loop(block, address, newAddress, blockMap);
                    if(exists_loop) {
                    	loopInfo.put(newAddress, 1);
                    }
                    jump_to_block_w_new_constraint(block, inst, newAddress, store, constraint, val, need_new_constraint);
                }
        	}
            else {
                boolean exists_loop = CFHelper.detect_loop(block, address, newAddress, blockMap);
                if(exists_loop) {
                	HashMap<Long, Integer> loopInfo = new HashMap<>();
                	loopInfo.put(newAddress, 1);
                	loopTraceCounter.put(address, loopInfo);
                }
                jump_to_block_w_new_constraint(block, inst, newAddress, store, constraint, val, need_new_constraint);
            }
        }
        else {
            jump_to_block_w_new_constraint(block, inst, newAddress, store, constraint, val, need_new_constraint);
        }
    }

    int jump_to_block_w_new_constraint(Block block, String inst, long newAddress, Store store, Constraint constraint, boolean val, boolean need_new_constraint) {
        Constraint new_constraint = constraint;
        if(need_new_constraint) {
            new_constraint = add_new_constraint(store, constraint, inst, val, "j");
        }
        String new_inst = addrInstMap.get(newAddress);
        int blockID = add_new_block(block, newAddress, new_inst, store, new_constraint);
        return blockID;
    }
        
    void construct_branch(Block block, long address, String inst, Store store, Constraint constraint) {
        if(inst.startsWith("ret") || inst.endsWith(" ret")) {
        	build_ret_branch(block, address, inst, store, constraint);
        }
        else {
            String jumpAddrStr = inst.split(" ", 2)[1].strip();
            BitVecExpr nAddress = SMTHelper.get_jump_address(store, store.rip, jumpAddrStr, addressExtFuncMap);
//            Utils.logger.info(Long.toHexString(address) + ": " + inst + " :: " + nAddress.toString());
            Long newAddress = null;
	        if(Helper.is_bit_vec_num(nAddress)) {
	        	newAddress = Helper.long_of_sym(nAddress);
	        }
            if(addrInstMap.containsKey(newAddress)) {
                if(addressExtFuncMap.containsKey(newAddress)) {
                    if(!extFuncCallAddr.contains(address)) {
                        extFuncCallAddr.add(address);
                    }
                    String extFuncName = CFHelper.readFuncName(addrSymMap, newAddress);
                    handle_external_function(extFuncName, block, address, inst, store, constraint);
                }
                else {
                    handle_internal_jumps(block, address, inst, store, constraint, newAddress);
                }
            }
            else if(addrSymMap.containsKey(newAddress)) {
            	String extFuncName = CFHelper.readFuncName(addrSymMap, newAddress);
            	if(!extFuncCallAddr.contains(address)) {
                    extFuncCallAddr.add(address);
                }
                handle_external_function(extFuncName, block, address, inst, store, constraint);
            }
            else if(addressExtFuncMap.containsKey(newAddress)) {
                String extFuncName = addressExtFuncMap.get(newAddress);
                if(!extFuncCallAddr.contains(address))
                    extFuncCallAddr.add(address);
                handle_external_function(extFuncName, block, address, inst, store, constraint);
            }
            else if(Helper.is_bit_vec_num(nAddress) || nAddress.toString().startsWith(Utils.MEM_DATA_SEC_SUFFIX)) {
            	String extFuncName = nAddress.toString();
                if(!extFuncCallAddr.contains(address))
                    extFuncCallAddr.add(address);
                handle_external_function(extFuncName, block, address, inst, store, constraint);
                // Utils.logger.debug("Jump to an undefined external address " + str(newAddress) + " at address " + hex(address))
            }
            else
                handleUnresolvedIndirectJumps(block, address, nAddress, inst, constraint);
        }
    }

    void handle_internal_jumps(Block block, long address, String inst, Store store, Constraint constraint, long newAddress) {
        Utils.logger.info(Utils.num_to_hex_string(address) + ": jump address is " + Utils.num_to_hex_string(newAddress));
        if(Utils.check_not_single_branch_inst(inst)) {    // je xxx
            construct_conditional_branches(block, address, inst, newAddress, store, constraint);
        }
        else {
            if(addrBlockMap.containsKey(newAddress) && retCallAddressMap.containsValue(newAddress)) {
                if(isFuncBlockExplored(store, newAddress)) {
                    if(!extFuncCallAddr.contains(newAddress))
                        build_ret_branch(block, newAddress, "retn", store, constraint);
                    else
                        jump_to_block(block, newAddress, store, constraint);
                }
                else
                    jump_to_block(block, newAddress, store, constraint);
            }
            else {
                if(inst.startsWith("jmp "))
                    construct_conditional_jump_block(block, address, inst, newAddress, store, constraint, true, false);
                else
                	jump_to_block(block, newAddress, store, constraint);
            }
        }
    }

    void handle_external_function(String extFuncName, Block block, long address, String inst, Store store, Constraint constraint) {
        long rip = store.rip;
        Constraint newConstraint = constraint;
        String extName = extFuncName.split("@", 2)[0].strip();
        Utils.logger.info("Call the external function " + extName + " at address " + Long.toHexString(address));
        ArrayList<String> preConstraint = gPreConstraint.getOrDefault(extName, null);
        if(extFuncName.startsWith("__libc_start_main") && mainAddress != null) {
            Semantics.call_op(store, rip, block.block_id);
            long nextAddress = mainAddress;
            ExtHandler.ext__libc_start_main(store, rip, mainAddress, block.block_id);
            newConstraint = CFHelper.insert_new_constraints(store, rip, block.block_id, extFuncName, preConstraint, constraint);
            jump_to_block(block, nextAddress, store, newConstraint);
        }
        else {
            if(extFuncName.startsWith("malloc") || extFuncName.startsWith("calloc") || extFuncName.startsWith("realloc")) {
            	ExtHandler.ext_alloc_mem_call(store, rip, extFuncName, block.block_id);
                newConstraint = CFHelper.insert_new_constraints(store, rip, block.block_id, extFuncName, preConstraint, constraint);
            }
            else if(extFuncName.startsWith("free")) {
                ExtHandler.ext_free_mem_call(store, rip, block.block_id);
//                if(!succeed) return;
            }
            else {
                ExtHandler.ext_func_call(store, rip, block.block_id);
                if(Lib.TERMINATION_FUNCTIONS.contains(extName)) {
                    handle_cmc_path_termination(store);
                    Utils.logger.info("The symbolic execution has been terminated at the path due to the call of the function " + extName + "\n");
                    return;
                }
                newConstraint = CFHelper.insert_new_constraints(store, rip, block.block_id, extFuncName, preConstraint, constraint);
            }
            build_ret_branch(block, address, "retn", store, newConstraint);
        }
    }
    
    
    void reconstructNewBranches(Block blk, String symName, String jptIdxRegName, ArrayList<Long> targetAddrs) {
        int blkID = blk.block_id;
    	Long address = blk.address;
        String inst = blk.inst;
        Store store = blk.store;
        long rip = store.rip;
        Constraint constraint = blk.constraint;
        Tuple<ArrayList<Constraint>, ArrayList<Long>> unifiedJPTInfo = CFHelper.setNewJPTConstraint(store, rip, constraint, blkID, jptIdxRegName, targetAddrs);
        ArrayList<Constraint> constraintList = unifiedJPTInfo.x;
    	ArrayList<Long> unifiedTargetAddrs = unifiedJPTInfo.y;
    	int length = unifiedTargetAddrs.size();
    	for(int idx = 0; idx < length; idx++) {
    		Long tAddr = unifiedTargetAddrs.get(idx);
    		constraint = constraintList.get(idx);
            Store newStore = new Store(store, rip);
            int block_id = addNewBlock(blk, address, inst, newStore, constraint, false);
            SymEngine.set_sym(newStore, rip, symName, Helper.gen_bv_num(tAddr, Config.MEM_ADDR_SIZE), block_id);
            newStore.g_NeedTraceBack = false;
            newStore.g_PointerRelatedError = null;
        }
    }
                

    void handleUnresolvedIndirectJumps(Block block, long address, BitVecExpr newAddress, String inst, Constraint constraint) {
        if(inst.startsWith("jmp ")) {
        	Lib.TRACE_BACK_RET_TYPE res = null;
            if(addressJPTEntriesMap.containsKey(block.address)) {
            	Triplet<String, String, ArrayList<Long>> addrJTEntry = addressJPTEntriesMap.get(block.address);
            	String instDest = addrJTEntry.x;
            	String jptIdxRegName = addrJTEntry.y;
            	ArrayList<Long> targetAddrs = addrJTEntry.z;
                reconstructNewBranches(block, instDest, jptIdxRegName, targetAddrs);
                res = Lib.TRACE_BACK_RET_TYPE.JT_SUCCEED;
            }
            if(res != Lib.TRACE_BACK_RET_TYPE.JT_SUCCEED) {
                if(constraint != null) {
                    boolean isPathReachable = CFHelper.check_path_reachability(constraint);
                    if(isPathReachable == false) return;
                }
                // num_of_unresolved_indirects
                cmcExecInfo[2] += 1;
                handle_cmc_path_termination(block.store);
                Utils.logger.info("Cannot resolve the jump address " + newAddress.toString() + " of " + inst + " at address " + Utils.num_to_hex_string(address));
                Utils.logger.info(TraceBack.pp_tb_debug_info(res, address, inst));
            }
        }
        else {
            if(constraint != null) {
            	boolean isPathReachable = CFHelper.check_path_reachability(constraint);
                if(isPathReachable == false) { 
                    Utils.logger.info("The path is infeasible at the jump address " + newAddress.toString() + " of " + inst + " at address " + Utils.num_to_hex_string(address) + "\n");
                    return;
                }
            }
            ArrayList<String> newSrcs = CFHelper.retrieveSymSrcs(block);
            ArrayList<HashMap<Integer, ArrayList<String>>> traceBIDSymList = new ArrayList<>();
            TraceBack.tracebackSymAddr(blockMap, addressExtFuncMap, addrInstMap, block, traceBIDSymList, memLenMap, newSrcs);
            // num_of_unresolved_indirects
            cmcExecInfo[2] += 1;
            Utils.logger.info("Cannot resolve the jump address " + newAddress.toString() + " of " + inst + " at address " + Utils.num_to_hex_string(address) + "\n");
            handle_cmc_path_termination(block.store);
            // sys.exit("Can!resolve the jump address " + SymHelper.string_of_address(newAddress) + " of " + inst + " at address " + hex(address))
        }
    }


    Integer exec_ret_operation(Block block, long address, Store store, Constraint constraint, long newAddress) {
        Integer block_id = null;
        Utils.logger.info(Utils.num_to_hex_string(address) + ": the return address is " + Utils.num_to_hex_string(newAddress));
        if(addrInstMap.containsKey(newAddress)) {
            if(!retCallAddressMap.containsKey(newAddress)) {
                Long callTarget = _get_prev_inst_target(newAddress);
                if(callTarget != null) {
                    retCallAddressMap.put(newAddress, callTarget);
                }
            }
            block_id = jump_to_block(block, newAddress, store, constraint);
        }
        else
            jump_to_dummy(block);
        return block_id;
    }


    Integer build_ret_branch(Block block, long address, String inst, Store store, Constraint constraint) {
        Integer blockID = null;
        BitVecExpr newAddress = null;
		Long alter_address = null;
        if(inst.equals("ret") || inst.equals("retf")) {
        	Tuple<BitVecExpr, Long> addrInfo = Semantics.ret(store, block.block_id);
        	newAddress = addrInfo.x;
        	alter_address = addrInfo.y;
        }
        else if(inst.startsWith("retn")) {
        	Tuple<BitVecExpr, Long> addrInfo = Semantics.retn(store, block.inst, block.block_id);
            newAddress = addrInfo.x;
        	alter_address = addrInfo.y;
        }
        if(newAddress != null) {
            if(Helper.is_bit_vec_num(newAddress)) {
            	blockID = exec_ret_operation(block, address, store, constraint, Helper.long_of_sym(newAddress));
            }
            else if(Helper.is_term_address(newAddress)) {
                jump_to_dummy(block);
                handle_cmc_path_termination(store);
            }
            // Return address is symbolic
            else {
                if(alter_address != null) {
                    blockID = exec_ret_operation(block, address, store, constraint, alter_address);
                }
                else if(constraint != null) {
                    boolean isPathReachable = CFHelper.check_path_reachability(constraint);
                    if(isPathReachable == false) return null;
                }
                else {
                    // num_of_unresolved_indirects
                    cmcExecInfo[2] += 1;
                    handle_cmc_path_termination(store);
                    Utils.logger.info("Cannot resolve the return address " + newAddress.toString() + " of " + block.inst + " at address " + Utils.num_to_hex_string(address) + "\n");
                    System.exit(1);
//                    System.exit("Cannot resolve the return address of " + block.inst + " at address " + Utils.num_to_hex_string(address));
                }
            }
        }
        return blockID;
   }


    TRACE_BACK_RET_TYPE concrSymMemAddr(Block blk, int tbCount, int haltPoint, ArrayList<HashMap<Integer,ArrayList<String>>> traceBIDSymList, ArrayList<String> symNames) {
    	Lib.TRACE_BACK_RET_TYPE res;
    	if(haltPoint >= 0)
            res = handleSymAddrWConcretize(blk, traceBIDSymList, symNames, haltPoint);
        else if(tbCount >= Utils.MAX_TRACEBACK_COUNT)
            res = TRACE_BACK_RET_TYPE.TB_COUNT_EXCEEDS_LIMITATION;
        else
            res = TRACE_BACK_RET_TYPE.TB_BLOCK_DOES_NOT_EXIST;
        return res;
    }


    // example: mov eax,DWORD PTR [rip+0x205a28]        // <optind@@GLIBC_2.2.5>
    Constraint constrFromMovWExtSrc(Block blk, Constraint constraint) {
    	Store store = blk.store;
    	long rip = store.rip;
    	String inst = blk.inst;
        Constraint newConstraint = constraint;
        if(inst.startsWith("mov")) {
        	InstElement instElem = new InstElement(inst);
            ArrayList<String> inst_args = instElem.inst_args;
            if(inst_args.get(1).endsWith("]")) {
                BitVecExpr eAddr = SymEngine.get_effective_address(store, rip, inst_args.get(1));
                if(Helper.is_bit_vec_num(eAddr)) {
                    long address = Helper.long_of_sym(eAddr);
                    String symName = CFHelper.getNormalizedSymName(addrSymMap, address);
                    if(symName != null) {
                        if(gPreConstraint.containsKey(symName)) {
                            ArrayList<String> preConstraint = gPreConstraint.getOrDefault(symName, null);
                            newConstraint = CFHelper.insert_new_constraints(store, rip, blk.block_id, symName, preConstraint, constraint);
                        }
                    }
                }
            }
        }
        return newConstraint;
    }


    TRACE_BACK_RET_TYPE handleSymAddrWConcretize(Block restartBlk, ArrayList<HashMap<Integer, ArrayList<String>>> traceBIDSymList, ArrayList<String> symNames, int haltPoint) {
        Utils.logger.info("Handle symbolized memory address with concretization");
        ArrayList<BitVecExpr> symValues = new ArrayList<>();
        ArrayList<Integer> symLengths = new ArrayList<>();
        Constraint newConstraint = restartBlk.constraint;
        for(HashMap<Integer, ArrayList<String>> bIDSymMap : traceBIDSymList) {
        	for(Integer blockID : bIDSymMap.keySet()) {
        		ArrayList<String> srcNames = bIDSymMap.get(blockID);
        		Block currBlock = blockMap.get(blockID);
                newConstraint = constrFromMovWExtSrc(currBlock, newConstraint);
                Store store = currBlock.store;
        		for(String srcName: srcNames) {
	                int length = CFHelper.getOperandSize(currBlock.inst, srcName, memLenMap);
	                BitVecExpr symVal = CFHelper.get_inv_arg_val(store, store.rip, srcName, blockID, length);
	                if(!symAddrValuesetMap.containsKey(symVal)) {
	                	symValues.add(symVal);
	                	symLengths.add(length);
	                }
        		}
            }
        }
        HashMap<BitVecExpr, ArrayList<BitVecExpr>> concrRes = CFHelper.concretizeSymArg(restartBlk.store, symValues, symLengths, newConstraint, haltPoint);
        Utils.logger.info("The following symbolic values are concretized: " + symValues.toString());
        Utils.logger.info(concrRes.toString());
        CFHelper.update_sym_addr_valueset_map(symAddrValuesetMap, concrRes);
        TRACE_BACK_RET_TYPE res = reconstructNewBranchesWValueSet(restartBlk, symValues, symNames);
        return res;
    }
    
    
    TRACE_BACK_RET_TYPE handle_unbounded_jump_table_w_tb(ArrayList<Block> traceList, ArrayList<String> srcNames, int boundary) {
    	Tuple<Integer, Integer> jtUpperboundInfo = CFHelper.gen_jt_upperbound(traceList, boundary);
        Integer cjmpBlkIdx = jtUpperboundInfo.x, jtUpperbound = jtUpperboundInfo.y;
        if(jtUpperbound == null) 
        	return TRACE_BACK_RET_TYPE.JT_NO_UPPERBOUND;
        Tuple<String, ArrayList<Long>> jptTargetInfo = CFHelper.readJPTTargetAddrs(traceList, cjmpBlkIdx, globalJPTEntriesMap);
        String jptIdxRegName = jptTargetInfo.x;
        ArrayList<Long> targetAddrs = jptTargetInfo.y;
        if(targetAddrs == null) 
        	return TRACE_BACK_RET_TYPE.JT_NOT_CORRECT_ASSIGN_INST;
        if(targetAddrs.size() != jtUpperbound)
        	return TRACE_BACK_RET_TYPE.JT_UPPERBOUND_DISMATCH;
        Block blk = traceList.get(0);
        String inst = blk.inst;
        if(Utils.check_jmp_with_address(inst)) {
	        String[] instSplit = inst.split(" ", 2);
	        String dest = instSplit[1].strip();
	        ArrayList<String> addrsInfo = new ArrayList<>();
	        String targetAddr = "";
	        for(Long tAddr : targetAddrs) {
	        	targetAddr = Long.toHexString(tAddr);
	        	if(!addrsInfo.contains(targetAddr))
	        		addrsInfo.add(targetAddr);
	        }
	        String jptInfo = String.join(", ", addrsInfo);
	        Utils.logger.info(Utils.num_to_hex_string(traceList.get(0).address) + ": jump addresses resolved using jump table with entries: [" + jptInfo + "]\n");
	        addressJPTEntriesMap.put(blk.address, new Triplet<>(dest, jptIdxRegName, targetAddrs));
	        reconstructNewBranches(blk, dest, jptIdxRegName, targetAddrs);
        }
        else
        	return TRACE_BACK_RET_TYPE.JT_NO_CORRECT_JMP_INST;
        return TRACE_BACK_RET_TYPE.JT_SUCCEED;
    }


    TRACE_BACK_RET_TYPE reconstructNewBranchesWValueSet(Block block, ArrayList<BitVecExpr> symValues, ArrayList<String> sym_names) {
        Store store = block.store;
        Utils.logger.info("Reconstruct new branches with concretized value\n");
        for(int i = 0; i < Utils.REBUILD_BRANCHES_NUM; i++) {
            Store newStore = new Store(store, store.rip);
            newStore.g_NeedTraceBack = false;
            newStore.g_PointerRelatedError = null;
            int block_id = addNewBlock(block, block.address, block.inst, newStore, block.constraint, false);
            for(BitVecExpr symVal : symValues) {
                if(symAddrValuesetMap.containsKey(symVal)) {
                    _substitute_sym_arg(newStore, newStore.rip, symVal, symAddrValuesetMap.get(symVal).get(i), block_id, sym_names);
                }
                else
                    return TRACE_BACK_RET_TYPE.SYMADDR_SYM_NOT_IN_GLOBAL_VALUTSET;
            }
        }
        return TRACE_BACK_RET_TYPE.SYMADDR_SUCCEED;
    }


    void _substitute_sym_arg(Store store, long rip, BitVecExpr symArg, BitVecExpr symNew, int block_id, ArrayList<String> symNames) {
        for(String symName : symNames) {
            String tmpName = symName;
            if(Utils.imm_start_pat.matcher(symName).matches()) {
            	tmpName = "[" + symName + "]";
            }
            BitVecExpr prevVal = SymEngine.get_sym(store, rip, tmpName, block_id);
            SymEngine.set_sym(store, rip, tmpName, Helper.substitute_sym_val(prevVal, symArg, symNew), block_id);
        }
    }


    void _update_external_assumptions(Store store, long rip, String inst, ArrayList<String> srcNames) {
        String jumpAddrStr = inst.split(" ", 2)[1].strip();
        BitVecExpr newAddress = SMTHelper.get_jump_address(store, rip, jumpAddrStr, addressExtFuncMap);
        extLibAssumptions.put(newAddress.toString(), srcNames);
        if(!extMemPreserv.contains(newAddress)) {
            for(String srcName : srcNames) {
                if(Utils.imm_start_pat.matcher(srcName).matches()) {
                    extMemPreserv.add(newAddress);
                }
            }
        }
    }


    Integer jump_to_block(Block block, long newAddress, Store store, Constraint constraint) {
        String new_inst = addrInstMap.get(newAddress);
        Integer block_id = add_new_block(block, newAddress, new_inst, store, constraint);
        return block_id;
    }


    void jump_to_dummy(Block block) {
        block.add_to_children_list(dummyBlock.block_id);
    }
        

    int add_new_block(Block parent_blk, long address, String inst, Store store, Constraint constraint) {
    	long rip = CFHelper.get_next_address(address, addrNextMap, addrSymMap);
        Integer block_id = null;
        if(inst.startsWith("bnd ")) {
            inst = inst.strip().split(" ", 2)[1];
        }
        if(inst.startsWith("cmov")) {
            block_id = _add_new_block_w_cmov_inst(parent_blk, address, inst, store, constraint, rip);
        }
        // Check whether a block is visited too many times at the jump instructions
        else if(Utils.check_jmp_with_jump_instr(inst)) {
        	Triplet<Boolean, Integer, Store> blockVisitedInfo = checkBlockVisitedTimes(store, constraint, address, inst);
            boolean visitedTooManyTimes = blockVisitedInfo.x;
        	int bID = blockVisitedInfo.y;
            Store bStore = blockVisitedInfo.z;
            if(!visitedTooManyTimes) {
            	Store newStore = null;
                if(bStore != null)
                	newStore = new Store(bStore, rip);
                else
                	newStore = new Store(store, rip);
                block_id = addNewBlock(parent_blk, address, inst, newStore, constraint, true);
            }
            else {
            	parent_blk.add_to_children_list(bID);
                block_id = bID;
            }
        }
        else {
            Store newStore = new Store(store, rip);
            block_id = addNewBlock(parent_blk, address, inst, newStore, constraint, true);
        }
        return block_id;
    }


    Integer addNewBlock(Block parent_blk, long address, String inst, Store store, Constraint constraint, boolean needsUpdateStore) {
    	Integer block_id = null;
        if(inst.startsWith("bnd ")) {
            inst = inst.strip().split(" ", 2)[1];
        }
        Integer parent_id = (parent_blk != null) ? parent_blk.block_id : null;
        Block block = new Block(parent_id, address, inst.strip(), store, constraint);
        block_id = block.block_id;
        blockMap.put(block_id, block);
        if(needsUpdateStore && inst != null && !Utils.check_branch_inst_wo_call(inst) && !inst.startsWith("cmov")) {
            Semantics.parse_semantics(store, store.rip, inst, block_id);
        }
        if(store.g_NeedTraceBack) {
        	handleSymMemAddr(block, address, inst, store, constraint);
        }
        else if(store.g_PointerRelatedError != null && store.g_PointerRelatedError != Lib.MEMORY_RELATED_ERROR_TYPE.NONE && store.g_PointerRelatedError != Lib.MEMORY_RELATED_ERROR_TYPE.UNINITIALIZED_CONTENT) {
        	terminatePointerRelatedErrorPath(block, store, address, inst, constraint, true);
        }
        else {
            if(store.g_PointerRelatedError != null && store.g_PointerRelatedError == Lib.MEMORY_RELATED_ERROR_TYPE.UNINITIALIZED_CONTENT) {
                String error_msg = Utils.num_to_hex_string(address) + "\t" + inst + "\n\t" + CFHelper.str_of_error_type(store.g_PointerRelatedError) + " at address " + Utils.num_to_hex_string(store.g_PRErrorAddress) + "\n";
//                Utils.output_logger.error(error_msg);
                Utils.logger.info(error_msg);
                store.g_PointerRelatedError = null;
                // number of negative paths with uninitialized content
                cmcExecInfo[3] += 1;
            }
            if(parent_blk != null)
                parent_blk.add_to_children_list(block_id);
            if(addrBlockMap.containsKey(address)) {
            	int cnt = addressBlockCntMap.get(address);
            	addressBlockCntMap.put(address, cnt + 1);
            }
            else {
            	addressBlockCntMap.put(address, 1);
            }
            addrBlockMap.put(address, block);
            blockStack.add(block);
        }
        return block_id;
    }
    

        
    Constraint add_new_constraint(Store store, Constraint constraint, String inst, boolean val, String prefix) {
        Constraint newConstraint = constraint;
        BoolExpr predExpr = SMTHelper.parse_predicate(store, inst, val, prefix);
        if(predExpr != null)
        	newConstraint = new Constraint(constraint, predExpr);
        return newConstraint;
    }


    void handleSymMemAddr(Block block, long address, String inst, Store store, Constraint constraint) {
    	if(constraint != null) {
            boolean isPathReachable = CFHelper.check_path_reachability(constraint);
            if(!isPathReachable) return;
        }
        ArrayList<String> symNames = CFHelper.retrieveSymSrcs(block);
        ArrayList<HashMap<Integer, ArrayList<String>>> traceBIDSymList = new ArrayList<>();
        HashMap<String, Integer> memLenMap = new HashMap<>();
        Tuple<Integer, Integer> tbInfo = TraceBack.tracebackSymAddr(blockMap, addressExtFuncMap, addrInstMap, block, traceBIDSymList, memLenMap, symNames);
        int tbCount = tbInfo.x;
        if(tbCount == -1) {
        	Utils.logger.info("Parent block does not exist.");
        }
        else {
	        int haltPoint = tbInfo.y;
	        TRACE_BACK_RET_TYPE res = concrSymMemAddr(block, tbCount, haltPoint, traceBIDSymList, symNames);
	        if(res != TRACE_BACK_RET_TYPE.SYMADDR_SUCCEED) {
	            String printInfo = TraceBack.pp_tb_debug_info(res, address, inst);
	            Utils.logger.info(printInfo);
	        }
        }
    }


    void terminatePointerRelatedErrorPath(Block block, Store store, long address, String inst, Constraint constraint, boolean common) {
        // Utils.output_logger.info("Terminate path with pointer-related error at " + hex(address) + ") { " + inst)
        if(constraint != null) {
            boolean isPathReachable = CFHelper.check_path_reachability(constraint);
            if(!isPathReachable) { 
                // number of paths
                cmcExecInfo[0] += 1;
                return;
            }
        }
        String error_msg = "Error: " + Utils.num_to_hex_string(address) + "\t" + inst + "\n\t" + CFHelper.str_of_error_type(store.g_PointerRelatedError) + " at address " + Utils.num_to_hex_string(store.g_PRErrorAddress) + "\n";
//        Utils.output_logger.error(error_msg);
        Utils.logger.info(error_msg);
        ArrayList<String> symNames = CFHelper.retrieve_source_for_memaddr(inst, common);
        if(symNames != null)
            TraceBack.locatePointerRelatedError(blockMap, addressExtFuncMap, addrInstMap, addrSymMap, block, store, address, inst, symNames);
        // number of paths
        cmcExecInfo[0] += 1;
        // number of negative paths
        cmcExecInfo[1] += 1;
    }
        

    Integer _add_new_block_w_cmov_inst(Block parent_blk, long address, String inst, Store store, Constraint constraint, long rip) {
        Integer block_id = null;
        String prefix = "cmov";
        BoolExpr res = SMTHelper.parse_predicate(store, inst, true, prefix);
        if(res.isTrue())
            block_id = addBlockwPredicate(parent_blk, address, inst, store, constraint, rip, true);
        else if(res.isFalse())
            block_id = addBlockwPredicate(parent_blk, address, inst, store, constraint, rip, false);
        else {
            block_id = addBlockwPredicate(parent_blk, address, inst, store, constraint, rip, true);
            block_id = addBlockwPredicate(parent_blk, address, inst, store, constraint, rip, false);
        }
        return block_id;
    }


    Integer addBlockwPredicate(Block parent_blk, long address, String inst, Store store, Constraint constraint, long rip, boolean pred) {
        Store newStore = new Store(store, rip);
        int block_id = addNewBlock(parent_blk, address, inst, newStore, constraint, true);
        Semantics.cmov(store, rip, inst, pred, block_id);
        return block_id;
    }


    Long _get_prev_inst_target(long address) {
    	Long target = null;
        Long preAddress = CFHelper.get_prev_address(address, addrInstMap);
        if(preAddress != null) {
            String preInst = addrInstMap.get(preAddress);
            if(preInst.startsWith("call")) {
                Block blk = addrBlockMap.get(preAddress);
                BitVecExpr jmpTarget = SMTHelper.get_jump_address(blk.store, address, preInst.split(" ", 2)[1].strip(), addressExtFuncMap);
                if(Helper.is_bit_vec_num(jmpTarget)) {
                    target = Helper.long_of_sym(jmpTarget);
                }
            }
        }
        return target;
    }


    boolean isFuncBlockExplored(Store store, long newAddress) {
    	Block blk = addrBlockMap.get(newAddress);
    	int cnt = addressBlockCntMap.get(newAddress);
        if(cnt > Utils.MAX_VISIT_COUNT) return true;
        else if(cnt == 0) return false;
        Store preStore = blk.store;
        String newInst = addrInstMap.get(newAddress);
        Store newStore = new Store(store, preStore.rip);
        if(!Utils.check_branch_inst_wo_call(newInst) && !newInst.startsWith("cmov"))
        	Semantics.parse_semantics(newStore, newStore.rip, newInst, -1);
        boolean res = newStore.state_ith_eq(preStore, addrInstMap, Lib.REG);
        return res;
    }


    void _jump_to_next_block(Block block, long address, Store store, Constraint constraint) {
        long newAddress = CFHelper.get_next_address(address, addrNextMap, addrSymMap);
        if(newAddress != -1) {
            jump_to_block(block, newAddress, store, constraint);
        }
    }



    Triplet<Boolean, Integer, Store> checkBlockVisitedTimes(Store store, Constraint constraint, long newAddress, String new_inst) {
        if(addrBlockMap.containsKey(newAddress)) {
        	Block blk = addrBlockMap.get(newAddress);
        	int cnt = addressBlockCntMap.get(newAddress);
            if(cnt == 0) {
                return new Triplet<>(false, blk.block_id, null);
            }
            else if(cnt > Utils.MAX_VISIT_COUNT) {
                Utils.logger.info("Instruction " + new_inst + " at address " + Utils.num_to_hex_string(newAddress) + " is visited for " + Integer.toString(cnt) + " times\n");
                return new Triplet<>(true, blk.block_id, blk.store);
            }
            else if(cnt > 3) {
                Store prevStore = blk.store;
                long rip = prevStore.rip;
                Store newStore = new Store(store, rip);
                newStore.merge_store(prevStore, addrInstMap);
                if(newStore.state_equal(prevStore, addrInstMap) && cnt > 10) {
                    Utils.logger.info("Block exists: " + new_inst + " at address " + Utils.num_to_hex_string(newAddress) + " is visited for " + Integer.toString(cnt) + " times\n");
                    // Utils.logger.debug(prev_sym_store.pp_store())
                    // Utils.logger.debug(sym_store.pp_store())
                    // sys.exit(1)
                    return new Triplet<>(true, blk.block_id, blk.store);
                }
                else {
                    // address_block_map[newAddress][0] = cnt + 1
                    return new Triplet<>(false, blk.block_id, newStore);
                }
            }
        }
        return new Triplet<>(false, 0, null);
    }


    void handle_cmc_path_termination(Store store) {
        // NUM_OF_PATHS
        cmcExecInfo[0] += 1;
        // if(store[Lib.POINTER_RELATED_ERROR] && store[Lib.POINTER_RELATED_ERROR][0] != MEMORY_RELATED_ERROR_TYPE.UNINITIALIZED_CONTENT) {
        //     // NUM_OF_NEGATIVES
        //     cmcExecInfo[1] += 1
        //     Utils.logger.info("The symbolic execution has been terminated at the path with pointer-related error\n")
    }

    public int reachable_addresses_num() {
        int res = addrBlockMap.keySet().size();
        return res;
    }
            
    
    void pp_unreachable_instrs() {
        Set<Long> reachableAddrs = addrBlockMap.keySet();
        Set<Long> instAddrs = addrInstMap.keySet();
        ArrayList<Long> sortedAddrs = new ArrayList<Long>(instAddrs);
        Collections.sort(sortedAddrs);
        Utils.logger.info("\n");
        Utils.logger.info(Utils.LOG_UNREACHABLE_INDICATOR);
        for(Long address : sortedAddrs) {
            if(!reachableAddrs.contains(address)) {
                Utils.logger.info(Utils.num_to_hex_string(address) + ": " + addrInstMap.get(address));
            }
        }
    }
}
