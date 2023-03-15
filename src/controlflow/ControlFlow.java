package controlflow;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BitVecNum;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Model;

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

public class ControlFlow {
	
	HashMap<Integer, Block> blockMap;
	ArrayDeque<Block> blockStack;
    HashMap<Long, Block> addressBlockMap;
    HashMap<Long, Integer> addressBlockCntMap;
    HashMap<Long, String> addressExtFuncMap;
    HashMap<String, Integer> memLenMap;
    HashMap<String, BitVecExpr> symTable;
    HashMap<BitVecExpr, ArrayList<String>> addressSymTable;
    HashMap<Long, String> addressInstMap;
    HashMap<Long, Long> addressNextMap;
    HashMap<Long, String> dllFuncInfo;
    HashMap<Tuple<Long, Long>, Integer> loopTraceCounter;
    HashMap<String, ArrayList<String>> gPreConstraint;
    ArrayList<Long> extFuncCallAddr;
    ArrayList<BitVecExpr> extMemPreserv;
    String disasmType;
    Block dummyBlock;
    public int[] cmcExecInfo;
    final long startAddress;
    final long mainAddress;
    HashMap<Long, Long> retCallAddressMap;
    HashMap<Long, Tuple<String, ArrayList<BitVecExpr>>> addressJTEntriesMap;
    HashMap<String, ArrayList<String>> extLibAssumptions;
    HashMap<BitVecExpr, ArrayList<BitVecExpr>> symAddrValuesetMap;

    public ControlFlow(HashMap<String, BitVecExpr> symTable, HashMap<BitVecExpr, ArrayList<String>> addressSymTable, HashMap<Long, String> addressInstMap, HashMap<Long, Long> addressNextMap, long startAddress, long mainAddress, String func_name, HashMap<Long, String> addressExtFuncMap, HashMap<String, ArrayList<String>> gPreConstraint, HashMap<Long, String> dllFuncInfo) {
    	blockMap = new HashMap<>();
    	blockStack = new ArrayDeque<>();
        addressBlockMap = new HashMap<>();
        loopTraceCounter = new HashMap<>();
        memLenMap = new HashMap<>();
        this.symTable = symTable;
        this.addressSymTable = addressSymTable;
        this.startAddress = startAddress;
        this.addressInstMap = addressInstMap;
        this.addressNextMap = addressNextMap;
        dummyBlock = new Block(-1, 0, "", null, null);
        this.mainAddress = mainAddress;
        this.gPreConstraint = gPreConstraint;
        retCallAddressMap = new HashMap<>();
        extFuncCallAddr = new ArrayList<>();
        addressJTEntriesMap = new HashMap<>();
        symAddrValuesetMap = new HashMap<>();
        extLibAssumptions = new HashMap<>();
        extMemPreserv = new ArrayList<>();
        this.addressExtFuncMap = addressExtFuncMap;
        this.dllFuncInfo = dllFuncInfo;
        Store store = new Store(null);
        cmcExecInfo = new int[Utils.CMC_EXEC_RES_COUNT];
        Constraint constraint = null;
        SymHelper.cnt_init();
        CFHelper.cfg_init_parameter(store, symTable);
        CFHelper.start_init(store, startAddress, Utils.INIT_BLOCK_NO);
        constraint = CFHelper.handlePreConstraint(store, store.rip, constraint, Utils.INIT_BLOCK_NO, gPreConstraint, extLibAssumptions);
        build_cfg(startAddress, store, constraint);
        pp_unreachable_instrs();
    }

        
    void build_cfg(long startAddress, Store startStore, Constraint startConstraint) {
    	String startInst = addressInstMap.get(startAddress);
        add_new_block(null, startAddress, startInst, startStore, startConstraint);
        while(blockStack != null) {
            Block curr = blockStack.pop();
            Utils.logger.info(Long.toHexString(curr.address) + ": " + curr.inst); 
            long address = curr.address;
            String inst = curr.inst;
            Store store = curr.store;
            Constraint constraint = curr.constraint;
            if(inst != null && inst.startsWith("bnd "))
                inst = inst.strip().split(" ", 2)[1];
            if(Utils.check_branch_inst(inst))
                construct_branch(curr, address, inst, store, constraint);
            else
                _jump_to_next_block(curr, address, store, constraint);
        }
    }


    void construct_conditional_branches(Block block, long address, String inst, long newAddress, Store store, Constraint constraint) {
        BoolExpr res = SMTHelper.parse_predicate(store, inst, true, "j");
        if(res == Helper.sym_false()) {
            long nextAddress = CFHelper.get_next_address(address, addressNextMap, addressSymTable);
            construct_conditional_jump_block(block, address, inst, nextAddress, store, constraint, false, true);
        }
        else if(res == Helper.sym_true()) {
            construct_conditional_jump_block(block, address, inst, newAddress, store, constraint, true, true);
        }
        else {
            long nextAddress = CFHelper.get_next_address(address, addressNextMap, addressSymTable);
            construct_conditional_jump_block(block, address, inst, nextAddress, store, constraint, false, true);
            construct_conditional_jump_block(block, address, inst, newAddress, store, constraint, true, true);
        }
    }

    void construct_conditional_jump_block(Block block, long address, String inst, long newAddress, Store store, Constraint constraint, boolean val, boolean need_new_constraint) {
        if(addressBlockMap.containsKey(address)) {
        	Tuple<Long, Long> traceKey = new Tuple<>(address, newAddress);
            if(loopTraceCounter.containsKey(traceKey)) {
                int counter = loopTraceCounter.get(traceKey);
                if(counter < Utils.MAX_LOOP_COUNT) {
                    loopTraceCounter.put(traceKey, counter + 1);
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
                    loopTraceCounter.put(traceKey, 1);
                }
                jump_to_block_w_new_constraint(block, inst, newAddress, store, constraint, val, need_new_constraint);
            }
        }
        else {
            // Utils.logger.info("jump_to_block_w_new_constraint")
            jump_to_block_w_new_constraint(block, inst, newAddress, store, constraint, val, need_new_constraint);
        }
    }

    int jump_to_block_w_new_constraint(Block block, String inst, long newAddress, Store store, Constraint constraint, boolean val, boolean need_new_constraint) {
        Constraint new_constraint = constraint;
        if(need_new_constraint) {
            new_constraint = add_new_constraint(store, constraint, inst, val, "j");
        }
        String new_inst = addressInstMap.get(newAddress);
        int blockID = add_new_block(block, newAddress, new_inst, store, new_constraint);
        return blockID;
    }
        
    void construct_branch(Block block, long address, String inst, Store store, Constraint constraint) {
        if(inst.startsWith("ret") || inst.endsWith(" ret")) {
            build_ret_branch(block, address, inst, store, constraint);
        }
        else {
            String jumpAddrStr = inst.split(" ", 2)[1].strip();
            BitVecExpr nAddress = SMTHelper.get_jump_address(store, store.rip, jumpAddrStr);
            Long newAddress = null;
	        if(Helper.is_bit_vec_num(nAddress)) {
	        	newAddress = Helper.long_of_sym(nAddress);
	        }
            if(addressInstMap.containsKey(newAddress)) {
                if(addressExtFuncMap.containsKey(newAddress)) {
                    if(!extFuncCallAddr.contains(address)) {
                        extFuncCallAddr.add(address);
                    }
                    String extFuncName = CFHelper.get_function_name_from_addr_sym_table(addressSymTable, newAddress);
                    handle_external_function(newAddress, extFuncName, block, address, inst, store, constraint);
                }
                else {
                    handle_internal_jumps(block, address, inst, store, constraint, newAddress);
                }
            }
            else if(addressSymTable.containsKey(newAddress)) {
                String extFuncName = CFHelper.get_function_name_from_addr_sym_table(addressSymTable, newAddress);
                if(!extFuncCallAddr.contains(address)) {
                    extFuncCallAddr.add(address);
                }
                handle_external_function(newAddress, extFuncName, block, address, inst, store, constraint);
            }
            else if(dllFuncInfo.containsKey(newAddress)) {
                String extFuncName = dllFuncInfo.get(newAddress);
                if(!extFuncCallAddr.contains(address))
                    extFuncCallAddr.add(address);
                handle_external_function(newAddress, extFuncName, block, address, inst, store, constraint);
            }
            else if(Helper.is_bit_vec_num(nAddress) || nAddress.toString().startsWith(Utils.MEM_DATA_SEC_SUFFIX)) {
            	String extFuncName = nAddress.toString();
                if(!extFuncCallAddr.contains(address))
                    extFuncCallAddr.add(address);
                handle_external_function(newAddress, extFuncName, block, address, inst, store, constraint);
                // Utils.logger.debug("Jump to an undefined external address " + str(newAddress) + " at address " + hex(address))
            }
            else
                handleUnresolvedIndirectJumps(block, address, inst, constraint, newAddress);
        }
    }

    void handle_internal_jumps(Block block, long address, String inst, Store store, Constraint constraint, long newAddress) {
        Utils.logger.info(Long.toHexString(address) + ": jump address is " + Long.toHexString(address));
        if(Utils.check_not_single_branch_inst(inst)) {    // je xxx
            construct_conditional_branches(block, address, inst, newAddress, store, constraint);
        }
        else {
            if(addressBlockMap.containsKey(newAddress) && retCallAddressMap.containsValue(newAddress)) {
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

    void handle_external_function(long ext_func_address, String extFuncName, Block block, long address, String inst, Store store, Constraint constraint) {
        long rip = store.rip;
        Constraint newConstraint = constraint;
        ArrayList<String> inv_names = extLibAssumptions.get(ext_func_address);
        String extName = extFuncName.split("@", 2)[0].strip();
        ArrayList<String> preConstraint = gPreConstraint.getOrDefault(extName, null);
        if(extFuncName.startsWith("__libc_start_main")) {
            Semantics.call_op(store, rip, block.block_id);
            long nextAddress = mainAddress;
            ExtHandler.ext__libc_start_main(store, rip, mainAddress, block.block_id);
            newConstraint = CFHelper.insert_new_constraints(store, rip, block.block_id, extName, preConstraint, constraint);
            jump_to_block(block, nextAddress, store, newConstraint);
        }
        else {
            if(extFuncName.startsWith("malloc") || extFuncName.startsWith("calloc") || extFuncName.startsWith("realloc")) {
                ExtHandler.ext_alloc_mem_call(store, rip, extName, block.block_id);
                newConstraint = CFHelper.insert_new_constraints(store, rip, block.block_id, extName, preConstraint, constraint);
            }
            else if(extFuncName.startsWith("free")) {
                boolean succeed = ExtHandler.ext_free_mem_call(store, rip, block.block_id);
                if(!succeed) return;
            }
            else {
                boolean isMemPreserved = extMemPreserv.contains(ext_func_address);
                ExtHandler.ext_func_call(store, rip, block.block_id);
                if(Lib.TERMINATION_FUNCTIONS.contains(extName)) {
                    handle_cmc_path_termination(store);
                    Utils.logger.info("The symbolic execution has been terminated at the path due to the call of the function " + extName + "\n");
                    return;
                }
                newConstraint = CFHelper.insert_new_constraints(store, rip, block.block_id, extName, preConstraint, constraint);
            }
            build_ret_branch(block, address, "retn", store, newConstraint);
        }
    }
    
    
    void reconstructNewBranches(Block blk, String alternative_sym, ArrayList<BitVecExpr> alternative_values) {
        Long address = blk.address;
        String inst = blk.inst;
        Store store = blk.store;
        long rip = store.rip;
        Constraint constraint = blk.constraint;
        for(BitVecExpr val : alternative_values) {
            Store newStore = new Store(store, rip);
            int block_id = addNewBlock(blk, address, inst, newStore, constraint, false);
            SymEngine.set_sym(newStore, rip, alternative_sym, val, block_id);
        }
    }
                

    void handleUnresolvedIndirectJumps(Block block, long address, String inst, Constraint constraint, long newAddress) {
        if(inst.startsWith("jmp ")) {
        	Lib.TRACE_BACK_RET_TYPE res = null;
            ArrayList<Block> trace_list = new ArrayList<>();
            if(addressJTEntriesMap.containsKey(block.address)) {
            	Tuple<String, ArrayList<BitVecExpr>> addrJTEntry = addressJTEntriesMap.get(block.address);
            	String instDest = addrJTEntry.x;
            	ArrayList<BitVecExpr> targetAddrs = addrJTEntry.y;
                reconstructNewBranches(block, instDest, targetAddrs);
                res = Lib.TRACE_BACK_RET_TYPE.JT_SUCCEED;
            }
            else {
            	ArrayList<String> srcNames = new ArrayList<>();
            	srcNames.add(inst.split(" ", 2)[1].strip());
            	Triplet<Lib.TRACE_BACK_RET_TYPE, ArrayList<String>, Integer> tbInfo = TraceBack.tracebackIndirectJumps(blockMap, block, srcNames, memLenMap, trace_list);
            	res = tbInfo.x;
            	if(res == Lib.TRACE_BACK_RET_TYPE.JT_SUCCEED) {
	            	srcNames = tbInfo.y;
	            	int boundary = tbInfo.z;
	            	res = handle_unbounded_jump_table_w_tb(trace_list, srcNames, boundary, block);
            	}
            }
            if(res != Lib.TRACE_BACK_RET_TYPE.JT_SUCCEED) {
                if(constraint != null) {
                    boolean isPathReachable = CFHelper.check_path_reachability(constraint);
                    if(isPathReachable == false) return;
                }
                // num_of_unresolved_indirects
                cmcExecInfo[2] += 1;
                handle_cmc_path_termination(block.store);
                Utils.logger.info("Cannot resolve the jump address " + Long.toHexString(newAddress) + " of " + inst + " at address " + Long.toHexString(address));
//                Utils.logger.info(TraceBack.pp_tb_debug_info(res, address, inst));
                // sys.exit("Can!resolve the jump address " + SymHelper.string_of_address(newAddress) + " of " + inst + " at address " + hex(address))
            }
        }
        else {
            if(constraint != null) {
            	boolean isPathReachable = CFHelper.check_path_reachability(constraint);
                if(isPathReachable == false) { 
                    Utils.logger.info("The path is infeasible at the jump address " + Long.toHexString(newAddress) + " of " + inst + " at address " + Long.toHexString(address) + "\n");
                    return;
                }
            }
            ArrayList<String> newSrcs = CFHelper.retrieveSymSrcs(block);
            ArrayList<HashMap<Integer, ArrayList<String>>> traceBIDSymList = new ArrayList<>();
            TraceBack.tracebackSymAddr(blockMap, addressExtFuncMap, dllFuncInfo, addressInstMap, block, traceBIDSymList, memLenMap, newSrcs);
            // num_of_unresolved_indirects
            cmcExecInfo[2] += 1;
            Utils.logger.info("Can!resolve the jump address " + Long.toHexString(newAddress) + " of " + inst + " at address " + Long.toHexString(address));
            handle_cmc_path_termination(block.store);
            // sys.exit("Can!resolve the jump address " + SymHelper.string_of_address(newAddress) + " of " + inst + " at address " + hex(address))
        }
    }


    Integer exec_ret_operation(Block block, long address, Store store, Constraint constraint, long newAddress) {
        Integer block_id = null;
        Utils.logger.info(Long.toHexString(address) + ": the return address is " + Long.toHexString(newAddress));
        if(addressInstMap.containsKey(newAddress)) {
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
                    Utils.logger.info("Cannot resolve the return address of " + block.inst + " at address " + Long.toHexString(address));
                    System.exit(1);
//                    System.exit("Cannot resolve the return address of " + block.inst + " at address " + Long.toHexString(address));
                }
            }
        }
        return blockID;
   }


    TRACE_BACK_RET_TYPE handle_sym_memwrite_addr(Block blk, int count, boolean tb_halt_point, boolean func_call_point, ArrayList<HashMap<Integer,ArrayList<String>>> traceList, ArrayList<String> symNames) {
    	Lib.TRACE_BACK_RET_TYPE res;
    	if(tb_halt_point || func_call_point)
            res = _handle_sym_addr_w_concretize(blk, traceList, symNames);
        else if(count >= Utils.MAX_TRACEBACK_COUNT)
            res = TRACE_BACK_RET_TYPE.TB_COUNT_EXCEEDS_LIMITATION;
        else
            res = TRACE_BACK_RET_TYPE.TB_BLOCK_DOES_NOT_EXIST;
        return res;
    }


    int get_operand_size(String inst, String arg) {
        int res = Config.MEM_ADDR_SIZE;
        InstElement instElem = new InstElement(inst);
        if(instElem.inst_args.size() == 2) {
            String operand = instElem.inst_args.get(1);
            res = Utils.get_sym_length(operand);
        }
        else
            res = CFHelper.get_real_length(memLenMap, arg);
        return res;
    }


    // example) { mov eax,DWORD PTR [rip+0x205a28]        // <optind@@GLIBC_2.2.5>
    Constraint _sym_src_from_mov_with_ext_env(Block blk, Constraint constraint) {
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
                    String symName = CFHelper.get_unified_sym_name(addressSymTable, address);
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


    TRACE_BACK_RET_TYPE _handle_sym_addr_w_concretize(Block restartBlk, ArrayList<HashMap<Integer, ArrayList<String>>> traceList, ArrayList<String> sym_names) {
        Utils.logger.info("Handle symbolized memory address with concretization");
        ArrayList<BitVecExpr> symValues = new ArrayList<>();
        ArrayList<Integer> symLengths = new ArrayList<>();
        Constraint newConstraint = restartBlk.constraint;
        for(HashMap<Integer, ArrayList<String>> bIDSymMap : traceList) {
        	for(Integer blockID : bIDSymMap.keySet()) {
        		ArrayList<String> symInfo = bIDSymMap.get(blockID);
        		Block currBlock = blockMap.get(blockID);
                newConstraint = _sym_src_from_mov_with_ext_env(currBlock, newConstraint);
                Store store = currBlock.store;
        		for(String symArg: symInfo) {
	                int length = get_operand_size(currBlock.inst, symArg);
	                BitVecExpr symVal = CFHelper.get_inv_arg_val(store, store.rip, symArg, blockID, length);
	                if(!symAddrValuesetMap.containsKey(symVal)) {
	                	symValues.add(symVal);
	                	symLengths.add(length);
	                }
        		}
            }
        }
        HashMap<BitVecExpr, ArrayList<BitVecExpr>> concrete_res = CFHelper.concretize_sym_arg(symValues, symLengths, newConstraint);
        Utils.logger.info("The following symbolic values are concretized: " + symValues.toString());
        Utils.logger.info(concrete_res.toString());
        CFHelper.update_sym_addr_valueset_map(symAddrValuesetMap, concrete_res);
        TRACE_BACK_RET_TYPE res = _reconstruct_new_branches_w_valueset(restartBlk, symValues, sym_names);
        return res;
    }
    
    
    TRACE_BACK_RET_TYPE handle_unbounded_jump_table_w_tb(ArrayList<Block> traceList, ArrayList<String> srcNames, int boundary, Block blk) {
    	traceList.remove(traceList.size() - 1);
        String srcName = srcNames.get(0);
        int src_len = Utils.get_sym_length(srcName);
        long rip = blk.store.rip;
        BitVecExpr src_sym = SymEngine.get_sym(blk.store, rip, srcName, blk.block_id, src_len);
        Tuple<Integer, Integer> jt_idx_upperbound_info = CFHelper.gen_jt_idx_upperbound(traceList, boundary);
        Integer cjmp_blk_idx = jt_idx_upperbound_info.x, jt_idx_upperbound = jt_idx_upperbound_info.y;
        if(jt_idx_upperbound == null) 
        	return TRACE_BACK_RET_TYPE.JT_NO_UPPERBOUND;
        Tuple<Integer, Boolean> jt_assign_inst_info = CFHelper.check_jump_table_assign_inst(traceList, cjmp_blk_idx);
        Integer jt_assign_blk_idx = jt_assign_inst_info.x;
        boolean is_jt_assign_inst = jt_assign_inst_info.y;
        if(!is_jt_assign_inst) 
        	return TRACE_BACK_RET_TYPE.JT_NOT_ASSIGN_INST;
        Block jt_assign_blk = traceList.get(jt_assign_blk_idx);
        Triplet<ArrayList<BitVecExpr>, String, Integer> distinctJTEntriesInfo = CFHelper.get_distinct_jt_entries(jt_assign_blk, src_sym, jt_idx_upperbound, blockMap);
        ArrayList<BitVecExpr> distinctEntries = distinctJTEntriesInfo.x;
        String instDest = distinctJTEntriesInfo.y;
        int srcLen = distinctJTEntriesInfo.z;
        if(distinctEntries == null) 
        	return TRACE_BACK_RET_TYPE.JT_NO_DISTINCT_ENTRIES;
        ArrayList<Store> storeList = CFHelper.reconstruct_jt_sym_stores(jt_assign_blk, distinctEntries, instDest, srcLen);
        Tuple<String, ArrayList<BitVecExpr>> JTTargetAddrsInfo = CFHelper.reconstruct_jt_target_addresses(traceList, jt_assign_blk_idx, storeList, addressJTEntriesMap);
        String dest = JTTargetAddrsInfo.x;
        ArrayList<BitVecExpr> targetAddrs = JTTargetAddrsInfo.y;
        if(targetAddrs == null) 
        	return TRACE_BACK_RET_TYPE.JT_NO_TARGET_ADDRESSES;
        ArrayList<String> addrsInfo = new ArrayList<>();
        for(BitVecExpr tAddr : targetAddrs) {
        	addrsInfo.add(Long.toHexString(Helper.long_of_sym(tAddr)));
        }
        String jtInfo = String.join(", ", addrsInfo);
        Utils.logger.info(Long.toHexString(traceList.get(traceList.size() - 1).address) + ": jump addresses resolved using jump table [" + jtInfo + "]");
        reconstructNewBranches(traceList.get(traceList.size() - 1), dest, targetAddrs);
        return TRACE_BACK_RET_TYPE.JT_SUCCEED;
    }


    TRACE_BACK_RET_TYPE _reconstruct_new_branches_w_valueset(Block block, ArrayList<BitVecExpr> symValues, ArrayList<String> sym_names) {
        Store store = block.store;
        Utils.logger.info("Reconstruct new branches with concretized value\n");
        for(int i = 0; i < Utils.REBUILD_BRANCHES_NUM; i++) {
            Store newStore = new Store(store, store.rip);
            newStore.g_NeedTraceBack = false;
            newStore.g_PointerRelatedError = null;
            int block_id = addNewBlock(block, block.address, block.inst, newStore, block.constraint, false);
            for(BitVecExpr symVal : symValues) {
                if(symAddrValuesetMap.containsKey(symVal))
                    _substitute_sym_arg(newStore, newStore.rip, symVal, symAddrValuesetMap.get(symVal).get(i), block_id, sym_names);
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
        BitVecExpr newAddress = SMTHelper.get_jump_address(store, rip, jumpAddrStr);
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
        String new_inst = addressInstMap.get(newAddress);
        Integer block_id = add_new_block(block, newAddress, new_inst, store, constraint);
        return block_id;
    }


    void jump_to_dummy(Block block) {
        block.add_to_children_list(dummyBlock.block_id);
    }
        

    int add_new_block(Block parent_blk, long address, String inst, Store store, Constraint constraint) {
    	long rip = CFHelper.get_next_address(address, addressNextMap, addressSymTable);
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
        if(store.g_NeedTraceBack)
        	handleSymMemAddr(block, address, inst, store, constraint);
        else if(store.g_PointerRelatedError != null && store.g_PointerRelatedError != Lib.MEMORY_RELATED_ERROR_TYPE.UNINITIALIZED_CONTENT)
        	terminatePointerRelatedErrorPath(block, store, address, inst, constraint, true);
        else {
            if(store.g_PointerRelatedError != null && store.g_PointerRelatedError == Lib.MEMORY_RELATED_ERROR_TYPE.UNINITIALIZED_CONTENT) {
                String error_msg = Long.toHexString(address) + "\t" + inst + "\n\t" + CFHelper.str_of_error_type(store.g_PointerRelatedError) + " at address " + Long.toHexString(store.g_PRErrorAddress) + "\n";
//                Utils.output_logger.error(error_msg);
                Utils.logger.info(error_msg);
                store.g_PointerRelatedError = null;
                // number of negative paths with uninitialized content
                cmcExecInfo[3] += 1;
            }
            if(parent_blk != null)
                parent_blk.add_to_children_list(block_id);
            if(addressBlockMap.containsKey(address)) {
            	int cnt = addressBlockCntMap.get(address);
            	addressBlockCntMap.put(address, cnt + 1);
            }
            else {
            	addressBlockCntMap.put(address, 1);
            }
            addressBlockMap.put(address, block);
            blockStack.add(block);
        }
        return block_id;
    }
    

        
    Constraint add_new_constraint(Store store, Constraint constraint, String inst, boolean val, String prefix) {
        Constraint newConstraint = constraint;
        BoolExpr pred_expr = SMTHelper.parse_predicate(store, inst, val, prefix);
        if(pred_expr != null)
        	newConstraint = new Constraint(constraint, pred_expr);
        return newConstraint;
    }


    void handleSymMemAddr(Block block, long address, String inst, Store store, Constraint constraint) {
        ArrayList<String> symNames = CFHelper.retrieveSymSrcs(block);
        ArrayList<HashMap<Integer, ArrayList<String>>> traceBIDSymList = new ArrayList<>();
        HashMap<String, Integer> memLenMap = new HashMap<>();
        Triplet<Integer, Boolean, Boolean> tbInfo = TraceBack.tracebackSymAddr(blockMap, addressExtFuncMap, dllFuncInfo, addressInstMap, block, traceBIDSymList, memLenMap, symNames);
        int count = tbInfo.x;
        if(count == -1) {
        	Utils.logger.info("Parent block does not exist.");
        }
        else {
	        boolean haltPoint = tbInfo.y;
	        boolean funcCallPoint = tbInfo.z;
	        TRACE_BACK_RET_TYPE res = handle_sym_memwrite_addr(block, count, haltPoint, funcCallPoint, traceBIDSymList, symNames);
	        if(res != TRACE_BACK_RET_TYPE.SYMADDR_SUCCEED) {
	            if(constraint != null) {
	                boolean isPathReachable = CFHelper.check_path_reachability(constraint);
	                if(!isPathReachable) return;
	            }
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
        String error_msg = "Error: " + Long.toHexString(address) + "\t" + inst + "\n\t" + CFHelper.str_of_error_type(store.g_PointerRelatedError) + " at address " + Long.toHexString(store.g_PRErrorAddress) + "\n";
//        Utils.output_logger.error(error_msg);
        Utils.logger.info(error_msg);
        ArrayList<String> symNames = CFHelper.retrieve_source_for_memaddr(inst, common);
        if(symNames != null)
            TraceBack.locatePointerRelatedError(blockMap, addressExtFuncMap, addressInstMap, addressSymTable, block, store, address, inst, symNames);
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
        Long preAddress = CFHelper.get_prev_address(address, addressInstMap);
        if(preAddress != null) {
            String preInst = addressInstMap.get(preAddress);
            if(preInst.startsWith("call")) {
                Block blk = addressBlockMap.get(preAddress);
                BitVecExpr jmpTarget = SMTHelper.get_jump_address(blk.store, address, preInst.split(" ", 2)[1].strip());
                if(Helper.is_bit_vec_num(jmpTarget)) {
                    target = Helper.long_of_sym(jmpTarget);
                }
            }
        }
        return target;
    }


    boolean isFuncBlockExplored(Store store, long newAddress) {
    	Block blk = addressBlockMap.get(newAddress);
    	int cnt = addressBlockCntMap.get(newAddress);
        if(cnt > Utils.MAX_VISIT_COUNT) return true;
        else if(cnt == 0) return false;
        Store preStore = blk.store;
        String newInst = addressInstMap.get(newAddress);
        Store newStore = new Store(store, preStore.rip);
        Semantics.parse_semantics(newStore, newStore.rip, newInst, -1);
        boolean res = newStore.state_ith_eq(preStore, addressInstMap, Lib.REG);
        return res;
    }


    void _jump_to_next_block(Block block, long address, Store store, Constraint constraint) {
        long newAddress = CFHelper.get_next_address(address, addressNextMap, addressSymTable);
        if(newAddress != -1) {
            jump_to_block(block, newAddress, store, constraint);
        }
    }



    Triplet<Boolean, Integer, Store> checkBlockVisitedTimes(Store store, Constraint constraint, long newAddress, String new_inst) {
        if(addressBlockMap.containsKey(newAddress)) {
        	Block blk = addressBlockMap.get(newAddress);
        	int cnt = addressBlockCntMap.get(newAddress);
            if(cnt == 0) {
                return new Triplet<>(false, blk.block_id, null);
            }
            else if(cnt > Utils.MAX_VISIT_COUNT) {
                Utils.logger.info("Instruction " + new_inst + " at address " + Long.toHexString(newAddress) + " is visited for " + Integer.toString(cnt) + " times\n");
                return new Triplet<>(true, blk.block_id, blk.store);
            }
            else if(cnt > 3) {
                Store prevStore = blk.store;
                long rip = prevStore.rip;
                Store newStore = new Store(store, rip);
                newStore.merge_store(prevStore, addressInstMap);
                if(newStore.state_equal(prevStore, addressInstMap) && cnt > 10) {
                    Utils.logger.info("Block exists: " + new_inst + " at address " + Long.toHexString(newAddress) + " is visited for " + Integer.toString(cnt) + " times\n");
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
        return new Triplet<>(false, null, null);
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
        int res = addressBlockMap.keySet().size();
        return res;
    }
            
    
    void pp_unreachable_instrs() {
        HashSet<Long> reachableAddrs = (HashSet<Long>) addressBlockMap.keySet();
        HashSet<Long> instAddrs = (HashSet<Long>) addressInstMap.keySet();
        Utils.logger.info("\n");
        Utils.logger.info(Utils.LOG_UNREACHABLE_INDICATOR);
        for(Long address : instAddrs) {
            if(!reachableAddrs.contains(address)) {
                Utils.logger.info(Long.toHexString(address) + ": " + addressInstMap.get(address));
            }
        }
    }
}
