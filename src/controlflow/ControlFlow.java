package controlflow;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

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
import graph.GraphBuilder;
import semantics.SMTHelper;
import semantics.Semantics;
import symbolic.SymEngine;
import symbolic.SymHelper;
import normalizer.Normalizer;

public class ControlFlow {
	
	HashMap<Integer, Block> blockMap;
	ArrayList<Block> blockStack;
    HashMap<Long, Block> addrBlockMap;
    HashMap<Long, String> addrExtFuncMap;
    HashMap<String, Integer> memLenMap;
    HashMap<String, Long> symTable;
    HashMap<Long, String> addrSymMap;
    HashMap<Long, String> addrInstMap;
    HashMap<Long, Long> addrNextMap;
    HashSet<Long> addrFuncEndSet;
    
    Block dummyBlock;
    public int[] wincheckExecInfo;
    Long startAddress;
    Long mainAddress;
    HashMap<Long, Triplet<String, String, ArrayList<Long>>> addrJPTEntriesMap;
    HashMap<Long, ArrayList<Long>> globalJPTEntriesMap;
    HashMap<String, ArrayList<String>> gPreConstraint;
    HashMap<String, ArrayList<String>> extLibAssumptions;
    HashMap<BitVecExpr, ArrayList<BitVecExpr>> symAddrValuesetMap;
    HashMap<Long, Integer> gHeapAllocMemInfo;
    GraphBuilder graphBuilder;

    
    public ControlFlow(HashMap<String, ArrayList<String>> gPreConstraint, Normalizer norm, GraphBuilder graphBuilder) {
    	blockMap = new HashMap<>();
    	blockStack = new ArrayList<>();
        addrBlockMap = new HashMap<>();
        memLenMap = new HashMap<>();
        symTable = norm.getSymTbl();
        addrSymMap = norm.getAddressSymTbl();
        startAddress = norm.getEntryAddress();
        addrInstMap = norm.getAddressInstMap();
        addrNextMap = norm.getAddressNextMap();
        addrFuncEndSet = norm.getFuncEndAddrSet();
        this.graphBuilder = graphBuilder;
        dummyBlock = new Block(-1, 0, "", null, null);
        mainAddress = norm.getMainAddress();
        this.gPreConstraint = gPreConstraint;
        addrJPTEntriesMap = new HashMap<>();
        symAddrValuesetMap = new HashMap<>();
        extLibAssumptions = new HashMap<>();
        addrExtFuncMap = norm.getAddressExtFuncMap();
        globalJPTEntriesMap = norm.readGlobalJPTEntriesMap();
        gHeapAllocMemInfo = new HashMap<>();
        Store store = new Store(null);
        store.rip = (startAddress == null) ? mainAddress : startAddress;
        wincheckExecInfo = new int[Utils.WINCHECK_EXEC_RES_COUNT];
        Constraint constraint = null;
        SymHelper.cnt_init();
        CFHelper.cfg_init_parameter(store, symTable);
        CFHelper.start_init(store, Utils.INIT_BLOCK_NO);
        constraint = CFHelper.handlePreConstraint(gHeapAllocMemInfo, store, constraint, Utils.INIT_BLOCK_NO, gPreConstraint, extLibAssumptions);
        buildCFG(store.rip, store, constraint);
        pp_unreachable_instrs();
    }

        
    void buildCFG(long startAddress, Store startStore, Constraint startConstraint) {
    	add_new_block(null, startAddress, startStore, startConstraint);
        while(blockStack != null && blockStack.size() > 0) {
            Block curr = blockStack.remove(blockStack.size() - 1);
            Utils.logger.info(Utils.toHexString(curr.address) + ": " + curr.inst);
            if(Config.VERBOSE) {
                Utils.logger.info("Block " + Integer.toString(curr.blockID));
	            Utils.logger.info(curr.store.pp_reg_store());
	            Utils.logger.info(curr.store.pp_mem_store());
            }
            long address = curr.address;
            String inst = curr.inst;
            Store store = curr.store;
            Constraint constraint = curr.constraint;
            if(inst != null && inst.startsWith("bnd "))
                inst = inst.strip().split(" ", 2)[1];
            if(Utils.check_branch_inst(inst))
                constructBranch(curr, address, inst, store, constraint);
            else {
            	if(!addrFuncEndSet.contains(curr.address))
            		buildNextBlock(curr, address, store, constraint);
            	else
            		Utils.logger.info("\n");
            }
        }
    }
    
    
    void constructBranch(Block block, long address, String inst, Store store, Constraint constraint) {
        if(inst.startsWith("ret") || inst.endsWith(" ret")) {
        	buildRetBranch(block, address, inst, store, constraint);
        	return;
        }
        String jumpAddrStr = inst.split(" ", 2)[1].strip();
        BitVecExpr nAddress = SMTHelper.get_jump_address(store, jumpAddrStr, addrExtFuncMap);
        Long newAddress = null;
        if(Helper.is_bit_vec_num(nAddress)) {
        	newAddress = Helper.long_of_sym(nAddress);
        }
        if(addrExtFuncMap.containsKey(newAddress)) {
            String extFuncName = addrExtFuncMap.get(newAddress);
            handleExtJumps(extFuncName, block, address, inst, store, constraint);
        }
        else if(addrInstMap.containsKey(newAddress)) {
        	if(!graphBuilder.containsEdge(address, newAddress) && !inst.startsWith("call")) {
            	graphBuilder.updateCycleInfo(address, newAddress);
            }
            handleInternalJumps(block, address, inst, store, constraint, newAddress);
        }
        else if(addrSymMap.containsKey(newAddress)) {
        	String extFuncName = CFHelper.readFuncName(addrSymMap, newAddress);
            handleExtJumps(extFuncName, block, address, inst, store, constraint);
        }
        else if(Helper.is_bit_vec_num(nAddress) || nAddress.toString().startsWith(Utils.MEM_DATA_SEC_SUFFIX)) {
        	String extFuncName = "mem@" + nAddress.toString();
            handleExtJumps(extFuncName, block, address, inst, store, constraint);
        }
        else
            handleUnresolvedIndirectJumps(block, address, nAddress, inst, constraint);
    }


    void constructCondBranches(Block block, long address, String inst, long newAddress, Store store, Constraint constraint) {
        BoolExpr res = SMTHelper.parse_predicate(store, inst, true, "j");
        if(res == null) {
        	long nextAddress = CFHelper.get_next_address(address, addrNextMap, addrSymMap);
        	addBlockWNewConstr(block, inst, nextAddress, store, constraint, false, true);
        	addBlockWNewConstr(block, inst, newAddress, store, constraint, true, true);
        }
        else {
	        if(res.equals(Helper.SymFalse)) {
	            long nextAddress = CFHelper.get_next_address(address, addrNextMap, addrSymMap);
	            addBlockWNewConstr(block, inst, nextAddress, store, constraint, false, true);
	        }
	        else if(res.equals(Helper.SymTrue)) {
	        	addBlockWNewConstr(block, inst, newAddress, store, constraint, true, true);
	        }
	        else {
	            long nextAddress = CFHelper.get_next_address(address, addrNextMap, addrSymMap);
	            addBlockWNewConstr(block, inst, nextAddress, store, constraint, false, true);
	            addBlockWNewConstr(block, inst, newAddress, store, constraint, true, true);
	        }
        }
    }

    void addBlockWNewConstr(Block block, String inst, long newAddress, Store store, Constraint constraint, boolean val, boolean needNewConstr) {
        Constraint newConstraint = constraint;
        if(needNewConstr) {
        	newConstraint = addNewConstraint(store, constraint, inst, val, "j");
        }
        add_new_block(block, newAddress, store, newConstraint);
    }
        
    
    void handleInternalJumps(Block block, long address, String inst, Store store, Constraint constraint, long newAddress) {
        Utils.logger.info(Utils.toHexString(address) + ": jump address is " + Utils.toHexString(newAddress));
        if(Utils.check_not_single_branch_inst(inst))   // je xxx
            constructCondBranches(block, address, inst, newAddress, store, constraint);
        else if(inst.startsWith("jmp "))
        	addBlockWNewConstr(block, inst, newAddress, store, constraint, true, false);
        else
        	add_new_block(block, newAddress, store, constraint);
    }
    

    void handleExtJumps(String extFuncName, Block block, long address, String inst, Store store, Constraint constraint) {
        Constraint newConstraint = constraint;
        String extName = extFuncName.split("@", 2)[0].strip();
        Utils.logger.info("Call the external function " + extName + " at address " + Long.toHexString(address));
        ArrayList<String> preConstraint = gPreConstraint.getOrDefault(extName, null);
        if(extFuncName.startsWith("__libc_start_main") && mainAddress != null) {
            Semantics.call_op(store, block.blockID);
            long nextAddress = mainAddress;
            ExtHandler.ext__libc_start_main(store, mainAddress, block.blockID);
            newConstraint = CFHelper.insert_new_constraints(gHeapAllocMemInfo, store, block.blockID, extFuncName, preConstraint, constraint);
            add_new_block(block, nextAddress, store, newConstraint);
        }
        else {
            if(extFuncName.startsWith("malloc") || extFuncName.startsWith("calloc") || extFuncName.startsWith("realloc")) {
            	ExtHandler.ext_alloc_mem_call(gHeapAllocMemInfo, store, extFuncName, block.blockID);
                newConstraint = CFHelper.insert_new_constraints(gHeapAllocMemInfo, store, block.blockID, extFuncName, preConstraint, constraint);
            }
            else if(extFuncName.startsWith("free")) {
                boolean succeed = ExtHandler.ext_free_mem_call(gHeapAllocMemInfo, store, block.blockID);
                if(!succeed) {
                	terminatePointerRelatedErrorPath(block, store, address, inst, constraint, true);
                	return;
                }
            }
            else {
                ExtHandler.ext_func_call(store, block.blockID);
                if(Lib.TERMINATION_FUNCTIONS.contains(extName)) {
                    handle_cmc_path_termination(store);
                    Utils.logger.info("The symbolic execution has been terminated at the path due to the call of the function " + extName + "\n");
                    return;
                }
                newConstraint = CFHelper.insert_new_constraints(gHeapAllocMemInfo, store, block.blockID, extFuncName, preConstraint, constraint);
            }
            buildRetBranch(block, address, "retn", store, newConstraint);
        }
    }
    
    
    void constructNewBranches(Block blk, String symName, String jptIdxRegName, ArrayList<Long> targetAddrs) {
        int blkID = blk.blockID;
    	Long address = blk.address;
        String inst = blk.inst;
        Store store = blk.store;
        Constraint constraint = blk.constraint;
        Tuple<ArrayList<Constraint>, ArrayList<Long>> unifiedJPTInfo = CFHelper.setNewJPTConstraint(store, constraint, blkID, jptIdxRegName, targetAddrs);
        ArrayList<Constraint> constraintList = unifiedJPTInfo.x;
    	ArrayList<Long> unifiedTargetAddrs = unifiedJPTInfo.y;
    	int length = unifiedTargetAddrs.size();
    	for(int idx = 0; idx < length; idx++) {
    		Long tAddr = unifiedTargetAddrs.get(idx);
    		constraint = constraintList.get(idx);
            Store newStore = new Store(store, store.rip);
            int blockID = addNewBlock(blk, address, inst, newStore, constraint, false);
            SymEngine.set_sym(newStore, symName, Helper.gen_bv_num(tAddr), blockID);
            newStore.g_NeedTraceBack = false;
            newStore.g_PointerRelatedError = null;
        }
    }
                

    void handleUnresolvedIndirectJumps(Block block, long address, BitVecExpr newAddress, String inst, Constraint constraint) {
        if(inst.startsWith("jmp ")) {
        	Lib.TRACE_BACK_RET_TYPE res = null;
            if(addrJPTEntriesMap.containsKey(block.address)) {
            	Triplet<String, String, ArrayList<Long>> addrJTEntry = addrJPTEntriesMap.get(block.address);
            	String instDest = addrJTEntry.x;
            	String jptIdxRegName = addrJTEntry.y;
            	ArrayList<Long> targetAddrs = addrJTEntry.z;
                constructNewBranches(block, instDest, jptIdxRegName, targetAddrs);
                res = Lib.TRACE_BACK_RET_TYPE.JT_SUCCEED;
            }
            else {
            	res = resolveGlobalJPTEntries(block);
            }
            if(res != Lib.TRACE_BACK_RET_TYPE.JT_SUCCEED) {
                if(constraint != null) {
                    boolean isPathReachable = CFHelper.check_path_reachability(constraint);
                    if(isPathReachable == false) return;
                }
                // num_of_unresolved_indirects
                wincheckExecInfo[2] += 1;
                handle_cmc_path_termination(block.store);
                Utils.logger.info("Cannot resolve the jump address " + newAddress.toString() + " of " + inst + " at address " + Utils.toHexString(address));
                Utils.logger.info(TraceBack.pp_tb_debug_info(res, address, inst));
            }
        }
        else {
            if(constraint != null) {
            	boolean isPathReachable = CFHelper.check_path_reachability(constraint);
                if(isPathReachable == false) { 
                    Utils.logger.info("The path is infeasible at the jump address " + newAddress.toString() + " of " + inst + " at address " + Utils.toHexString(address) + "\n");
                    return;
                }
            }
            ArrayList<String> newSrcs = CFHelper.retrieveSymSrcs(block);
            ArrayList<HashMap<Integer, ArrayList<String>>> traceBIDSymList = new ArrayList<>();
            TraceBack.tracebackSymAddr(blockMap, addrExtFuncMap, addrInstMap, block, traceBIDSymList, memLenMap, newSrcs);
            // num_of_unresolved_indirects
            wincheckExecInfo[2] += 1;
            Utils.logger.info("Cannot resolve the jump address " + newAddress.toString() + " of " + inst + " at address " + Utils.toHexString(address) + "\n");
            handle_cmc_path_termination(block.store);
            // sys.exit("Cannot resolve the jump address " + SymHelper.string_of_address(newAddress) + " of " + inst + " at address " + hex(address))
        }
    }


    void exec_ret_operation(Block block, long address, Store store, Constraint constraint, long newAddress) {
        Utils.logger.info(Utils.toHexString(address) + ": the return address is " + Utils.toHexString(newAddress));
        if(addrInstMap.containsKey(newAddress)) {
            add_new_block(block, newAddress, store, constraint);
        }
    }


    void buildRetBranch(Block block, long address, String inst, Store store, Constraint constraint) {
        BitVecExpr newAddress = null;
		Long alter_address = null;
        if(inst.equals("ret") || inst.equals("retf")) {
        	Tuple<BitVecExpr, Long> addrInfo = Semantics.ret(store, block.blockID);
        	newAddress = addrInfo.x;
        	alter_address = addrInfo.y;
        }
        else if(inst.startsWith("retn")) {
        	Tuple<BitVecExpr, Long> addrInfo = Semantics.retn(store, block.inst, block.blockID);
            newAddress = addrInfo.x;
        	alter_address = addrInfo.y;
        }
        if(newAddress != null) {
            if(ExtHandler.is_term_address(newAddress))
                handle_cmc_path_termination(store);
            else if(Helper.is_bit_vec_num(newAddress))
            	exec_ret_operation(block, address, store, constraint, Helper.long_of_sym(newAddress));
            // Return address is symbolic
            else {
                if(alter_address != null)
                    exec_ret_operation(block, address, store, constraint, alter_address);
                else if(constraint != null) {
                    boolean isPathReachable = CFHelper.check_path_reachability(constraint);
                    if(isPathReachable) {
                        handleUnresolvedReturnAddr(block, store, address, newAddress);
                    }
                }
                else {
                    handleUnresolvedReturnAddr(block, store, address, newAddress);
                }
            }
        }
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
    	String inst = blk.inst;
        Constraint newConstraint = constraint;
        if(inst.startsWith("mov")) {
        	InstElement instElem = new InstElement(inst);
            ArrayList<String> inst_args = instElem.inst_args;
            if(inst_args.get(1).endsWith("]")) {
                BitVecExpr eAddr = SymEngine.get_effective_address(store, inst_args.get(1));
                if(Helper.is_bit_vec_num(eAddr)) {
                    long address = Helper.long_of_sym(eAddr);
                    String symName = CFHelper.getNormalizedSymName(addrSymMap, address);
                    if(symName != null) {
                        if(gPreConstraint.containsKey(symName)) {
                            ArrayList<String> preConstraint = gPreConstraint.getOrDefault(symName, null);
                            newConstraint = CFHelper.insert_new_constraints(gHeapAllocMemInfo, store, blk.blockID, symName, preConstraint, constraint);
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
	                BitVecExpr symVal = CFHelper.get_inv_arg_val(store, srcName, blockID, length);
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
    
    
    TRACE_BACK_RET_TYPE resolveGlobalJPTEntries(Block block) {
        Tuple<String, ArrayList<Long>> jptTargetInfo = CFHelper.readJPTTargetAddrs(blockMap, block, globalJPTEntriesMap);
        String jptIdxRegName = jptTargetInfo.x;
        ArrayList<Long> targetAddrs = jptTargetInfo.y;
        if(targetAddrs == null) 
        	return TRACE_BACK_RET_TYPE.JT_NOT_CORRECT_ASSIGN_INST;
        String inst = block.inst;
        if(Utils.check_jmp_with_address(inst)) {
	        String[] instSplit = inst.split(" ", 2);
	        String dest = instSplit[1].strip();
	        addrJPTEntriesMap.put(block.address, new Triplet<>(dest, jptIdxRegName, targetAddrs));
	        constructNewBranches(block, dest, jptIdxRegName, targetAddrs);
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
            int blockID = addNewBlock(block, block.address, block.inst, newStore, block.constraint, false);
            for(BitVecExpr symVal : symValues) {
                if(symAddrValuesetMap.containsKey(symVal)) {
                    CFHelper.substituteSymVal(newStore, symVal, symAddrValuesetMap.get(symVal).get(i), blockID, sym_names);
                }
                else
                    return TRACE_BACK_RET_TYPE.SYMADDR_SYM_NOT_IN_GLOBAL_VALUTSET;
            }
        }
        return TRACE_BACK_RET_TYPE.SYMADDR_SUCCEED;
    }
        

    void add_new_block(Block parentBlk, long address, Store store, Constraint constraint) {
    	long rip = CFHelper.get_next_address(address, addrNextMap, addrSymMap);
    	String inst = addrInstMap.get(address);
        if(inst.startsWith("bnd ")) {
            inst = inst.strip().split(" ", 2)[1];
        }
    	Tuple<Integer, Stack<Long>> res = checkBlockCycleCount(parentBlk, address, inst);
    	int cycleCount = res.x;
    	Stack<Long> cycle = res.y;
    	if(cycleCount <= Config.MAX_CYCLE_COUNT) {
    		if(inst.startsWith("cmov")) {
                addNewBlockWCMovInst(parentBlk, address, inst, store, rip, constraint);
            }
            else {
                Store newStore = new Store(store, rip);
                addNewBlock(parentBlk, address, inst, newStore, constraint, true);
            }
        }
    	else {
            Utils.logger.info("The cycle " + Utils.ppCycle(cycle) + " is visited more than the maximum limitation");
            Block blk = addrBlockMap.get(address);
            Store prevStore = blk.store;
            rip = prevStore.rip;
            Store newStore = new Store(store, rip);
            newStore.merge_store(prevStore, addrInstMap);
            addNewBlock(parentBlk, address, inst, newStore, constraint, true);
    	}
    }


    Integer addNewBlock(Block parentBlk, long address, String inst, Store store, Constraint constraint, boolean updateStore) {
    	Integer blockID = null;
        if(inst.startsWith("bnd ")) {
            inst = inst.strip().split(" ", 2)[1];
        }
        int parentID = (parentBlk != null) ? parentBlk.blockID : -1;
        Block block = new Block(parentID, address, inst.strip(), store, constraint);
        blockID = block.blockID;
        blockMap.put(blockID, block);
        if(updateStore && inst != null && !Utils.check_branch_inst_wo_call(inst) && !inst.startsWith("cmov")) {
            Semantics.parse_semantics(store, inst, blockID);
        }
        if(store.g_NeedTraceBack) {
        	handleSymMemAddr(block, address, inst, store, constraint);
        }
        else if(store.g_PointerRelatedError != null && store.g_PointerRelatedError != Lib.MEMORY_RELATED_ERROR_TYPE.NONE && store.g_PointerRelatedError != Lib.MEMORY_RELATED_ERROR_TYPE.UNINITIALIZED_CONTENT) {
        	terminatePointerRelatedErrorPath(block, store, address, inst, constraint, true);
        }
        else {
            if(store.g_PointerRelatedError != null && store.g_PointerRelatedError == Lib.MEMORY_RELATED_ERROR_TYPE.UNINITIALIZED_CONTENT) {
                String error_msg = Utils.toHexString(address) + "\t" + inst + "\n\t" + CFHelper.str_of_error_type(store.g_PointerRelatedError) + " at address " + Utils.toHexString(store.g_PRErrorAddress) + "\n";
                Utils.logger.info(error_msg);
                store.g_PointerRelatedError = null;
                // number of negative paths with uninitialized content
                wincheckExecInfo[3] += 1;
            }
            addrBlockMap.put(address, block);
            blockStack.add(block);
        }
        return blockID;
    }
    

        
    Constraint addNewConstraint(Store store, Constraint constraint, String inst, boolean val, String prefix) {
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
        Tuple<Integer, Integer> tbInfo = TraceBack.tracebackSymAddr(blockMap, addrExtFuncMap, addrInstMap, block, traceBIDSymList, memLenMap, symNames);
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
        if(constraint != null) {
            boolean isPathReachable = CFHelper.check_path_reachability(constraint);
            if(!isPathReachable) { 
                // number of paths
                wincheckExecInfo[0] += 1;
                return;
            }
        }
        String error_msg = "Error: " + Utils.toHexString(address) + "\t" + inst + "\n\t" + CFHelper.str_of_error_type(store.g_PointerRelatedError) + " : " + Utils.toHexString(store.g_PRErrorAddress) + "\n";
        Utils.output_logger.info(error_msg);
        Utils.logger.info(error_msg);
        ArrayList<String> symNames = CFHelper.retrieveSymSources(inst, common);
        if(symNames != null)
            TraceBack.locatePointerRelatedError(blockMap, addrExtFuncMap, addrInstMap, addrSymMap, block, store, address, inst, symNames);
        // number of paths
        wincheckExecInfo[0] += 1;
        // number of negative paths
        wincheckExecInfo[1] += 1;
    }
        

    Integer addNewBlockWCMovInst(Block parent_blk, long address, String inst, Store store, long rip, Constraint constraint) {
        Integer blockID = null;
        String prefix = "cmov";
        BoolExpr res = SMTHelper.parse_predicate(store, inst, true, prefix);
        if(res.isTrue())
            blockID = addBlockWPredicate(parent_blk, address, inst, store, rip, constraint, true);
        else if(res.isFalse())
            blockID = addBlockWPredicate(parent_blk, address, inst, store, rip, constraint, false);
        else {
            blockID = addBlockWPredicate(parent_blk, address, inst, store, rip, constraint, true);
            blockID = addBlockWPredicate(parent_blk, address, inst, store, rip, constraint, false);
        }
        return blockID;
    }


    Integer addBlockWPredicate(Block parent_blk, long address, String inst, Store store, long rip, Constraint constraint, boolean pred) {
        Store newStore = new Store(store, rip);
        int blockID = addNewBlock(parent_blk, address, inst, newStore, constraint, true);
        Semantics.cmov(newStore, inst, pred, blockID);
        return blockID;
    }


    void buildNextBlock(Block block, long address, Store store, Constraint constraint) {
        long newAddress = CFHelper.get_next_address(address, addrNextMap, addrSymMap);
        if(newAddress != -1) {
            add_new_block(block, newAddress, store, constraint);
        }
    }


    Tuple<Integer, Stack<Long>> checkBlockCycleCount(Block block, long newAddress, String newInst) {
    	int res = 0;
    	Stack<Long> cycle = null;
        if(addrBlockMap.containsKey(newAddress)) {
        	if(graphBuilder.mayExistCycle(newAddress)) {
        		cycle = CFHelper.detectCycle(block, newAddress, newInst, blockMap, graphBuilder);
        		if(cycle != null) {
        			res = graphBuilder.updateCycleCount(newAddress, cycle);
        		}
        	}
        }
        return new Tuple<>(res, cycle);
    }


    void handle_cmc_path_termination(Store store) {
        // NUM_OF_PATHS
        wincheckExecInfo[0] += 1;
    }


    void handleUnresolvedReturnAddr(Block block, Store store, long address, BitVecExpr newAddress) {
        // num_of_unresolved_indirects
        wincheckExecInfo[2] += 1;
        handle_cmc_path_termination(store);
        Utils.logger.info("Cannot resolve the return address " + newAddress.toString() + " of " + block.inst + " at address " + Utils.toHexString(address) + "\n");
        System.exit(1);
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
                Utils.logger.info(Utils.toHexString(address) + ": " + addrInstMap.get(address));
            }
        }
    }
}
