package controlflow;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Random;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;

import block.Block;
import block.Constraint;
import block.Node;
import block.Store;
import common.Config;
import common.Lib;
import common.Lib.MEMORY_RELATED_ERROR_TYPE;
import common.Utils;
import semantics.SMTHelper;
import symbolic.SymEngine;
import symbolic.SymHelper;
import common.Helper;
import common.InstElement;
import common.Tuple;

public class CFHelper {

	static Integer gen_cjmp_upperbound(String inst_name, int boundary) {
	    Integer res = null;
	    String jmp_condition = inst_name.split("j", 2)[1].strip();
	    if(jmp_condition.startsWith("n")) {
	        String rest = jmp_condition.split("n")[1];
	        if(Utils.OPPOSITE_FLAG_MAP.containsKey(rest))
	            jmp_condition = Utils.OPPOSITE_FLAG_MAP.get(rest);
	    }
	    if(jmp_condition.startsWith("g") || jmp_condition.startsWith("a")) {
	        if(jmp_condition.contains("e"))
	            res = boundary;
	        else
	            res = boundary + 1;
	    }
	    return res;
	}


	/**
	    * Calculate the real upperbound according to the type of the condition jump instruction
	    * @param  trace_list	the list that contains all the visited blocks till the indirect jump block
	    * @param  boundary	the current boundary information
	    * @return			the real upperbound information
	    */
	static Tuple<Integer, Integer> gen_jt_upperbound(ArrayList<Block> trace_list, int boundary) {
	    Integer res = null;
	    Integer idx = 0;
	    for(idx = 0; idx < trace_list.size(); idx++) {
	    	Block blk = trace_list.get(idx);
	        String inst = blk.inst;
	        if(Utils.check_not_single_branch_inst(inst)) {
	            res = gen_cjmp_upperbound(inst.split(" ", 2)[0], boundary);
	            break;
	        }
	    }
	    return new Tuple<Integer, Integer>(idx, res);
	}


	static Long get_prev_address(long address, HashMap<Long, String> address_inst_map) {
	    Long p_address = null;
	    for(int idx = 1; idx < Config.MAX_INST_ADDR_GAP; idx++) {
	        long tmp = address - idx;
	        if(address_inst_map.containsKey(tmp)) {
	            p_address = tmp;
	            break;
	        }
	    }
	    return p_address;
	}


	static long get_next_address(long address, HashMap<Long, Long> address_next_map, HashMap<Long, String> address_sym_table) {
	    long next_address = address_next_map.get(address);
	    if(address_sym_table.containsKey(next_address)) return -1;
	    return next_address;
	}
	
	static Tuple<String, ArrayList<Long>> readJPTTargets(String instArg, HashMap<Long, ArrayList<Long>> globalJPTEntriesMap) {
		ArrayList<Long> targetAddrs = null;
		String jptIdxRegName = "";
		if(instArg.endsWith("]") && !(instArg.contains("rip")) && instArg.contains("*") && (instArg.contains("+"))) {
			String arg = Utils.extract_content(instArg, "[");
			String[] argSplit = arg.split("\\+");
			for(String as : argSplit) {
				as = as.strip();
				if(as.startsWith("0x")) {
					long addr = Long.decode(as);
		    		targetAddrs = globalJPTEntriesMap.get(addr);
				}
				else if(as.contains("*")) {
					String[] asSplit = as.split("\\*");
					jptIdxRegName = asSplit[0].strip();
				}
			}
	    }
	    return new Tuple<>(jptIdxRegName, targetAddrs);
	}
	
	static Tuple<String, ArrayList<Long>> readJPTTargetAddrs(ArrayList<Block> trace_list, int idx, HashMap<Long, ArrayList<Long>> globalJPTEntriesMap) {
		ArrayList<Long> targetAddrs = null;
		String jptIdxRegName = "";
		int aIdx = 0;
		for(aIdx = 0; aIdx < idx; aIdx++) {
	        Block blk = trace_list.get(aIdx);
	        String inst = blk.inst;
	        String instArg = inst.strip().split(" ", 2)[1].strip();
	        if(inst.startsWith("mov")) {
	        	String[] instArgs = instArg.split(",", 2);
			    if(instArgs.length == 2) {
			        String instArg0 = instArgs[0].strip();
			        String instArg1 = instArgs[1].strip();
			        if(Lib.REG_NAMES.contains(instArg0)) {
			        	Tuple<String, ArrayList<Long>> jptTargetInfo = readJPTTargets(instArg1, globalJPTEntriesMap);
			        	jptIdxRegName = jptTargetInfo.x;
			        	targetAddrs = jptTargetInfo.y;
			        }
			    }
	        }
	        else if(inst.startsWith("jmp")) {
	        	Tuple<String, ArrayList<Long>> jptTargetInfo = readJPTTargets(instArg, globalJPTEntriesMap);
	        	jptIdxRegName = jptTargetInfo.x;
	        	targetAddrs = jptTargetInfo.y;
	        }
	        if(targetAddrs != null) break;
	    }
		return new Tuple<>(jptIdxRegName, targetAddrs);
	}
	
	
	/**
	    * Unify the jump table entries and construct new constraints accordingly
	    * @param  store		the local store for the concolic execution process
	    * @param  rip		next address stored in the RIP register
	    * @param  constraint	the local current constraint for the concolic execution process
	    * @param  blkID		the block id for current block
	    * @param  jptIdxRegName		the name of the register that stores the symbolic index for the jump table entries, such as "ebx"
	    * @param  targetAddrs		a list that contains all the jump table entries
	    * @return			new constrains and unified jump table entries
	    */
	static Tuple<ArrayList<Constraint>, ArrayList<Long>> setNewJPTConstraint(Store store, long rip, Constraint constraint, int blkID, String jptIdxRegName, ArrayList<Long> targetAddrs) {
    	ArrayList<Constraint> constraintList = new ArrayList<>();
    	ArrayList<Long> unifiedTargetAddrs = new ArrayList<>();
    	HashMap<Long, Integer> tAddrFistIdxMap = new HashMap<>();
    	BitVecExpr symIdxReg = SymEngine.get_sym(store, rip, jptIdxRegName, blkID);
    	int jptUpperbound = targetAddrs.size();
    	int index = 0;
    	for(int idx = 0; idx < jptUpperbound; idx++) {
    		Long tAddr = targetAddrs.get(idx);
    		if(!unifiedTargetAddrs.contains(tAddr)) {
    			unifiedTargetAddrs.add(tAddr);
    			BoolExpr predicate = Helper.is_equal(symIdxReg, idx);
    			Constraint newConstraint = new Constraint(constraint, predicate);
    			constraintList.add(newConstraint);
    			tAddrFistIdxMap.put(tAddr, index);
    			index++;
    		}
    		else {
    			int tIdx = tAddrFistIdxMap.get(tAddr);
    			Constraint currConstraint = constraintList.get(tIdx);
    			BoolExpr predicate = constraint.getPredicate();
    			predicate = Helper.bv_or(predicate, Helper.is_equal(symIdxReg, idx));
    			currConstraint.updatePredicate(predicate);
    		}
    	}
    	return new Tuple<>(constraintList, unifiedTargetAddrs);
    }
    


	static ArrayList<Long> detect_loop(Block block, Long address, Long new_address, HashMap<Integer, Block> block_set) {
	    ArrayList<Long> loopList = new ArrayList<>();
		boolean existsLoop = false;
	    Integer parent_id = block.parent_id;
	    Long prev_address = null;
	    while(parent_id != null) {
	        if(block_set.containsKey(parent_id)) {
	            Block parent_blk = block_set.get(parent_id);
	            Long currAddr = parent_blk.address;
	            loopList.add(currAddr);
	            if(currAddr == address) {
	                if(prev_address != -1 && prev_address == new_address) {
	                	existsLoop = true;
	                    break;
	                }
	            }
	            parent_id = parent_blk.parent_id;
	            prev_address = currAddr;
	        }
	        else break;
	    }
	    if(!existsLoop) loopList = null;
	    return loopList;
	}


	ArrayList<Long> backtrack_to_start(Block block, Long address, HashMap<Integer, Block> block_set) {
		ArrayList<Long> trace_list = new ArrayList<Long>();
		trace_list.add(address);
	    int parent_id = block.parent_id;
	    while(parent_id != -1) {
	        Block parent_blk = block_set.get(parent_id);
	        long p_address = parent_blk.address;
	        trace_list.add(p_address);
	        parent_id = parent_blk.parent_id;
	    }
	    return trace_list;
	}


	static String getNormalizedSymName(HashMap<Long, String> addrSymMap, long address) {
	    String res = "";
	    if(addrSymMap.containsKey(address)) {
	        String sym_name = addrSymMap.get(address);
	        res = sym_name.split("@", 2)[0].strip();
	    }
	    return res;
	}


	static int getRealLength(HashMap<String, Integer> memLenMap, String arg) {
	    int length = Config.MEM_ADDR_SIZE;
	    if(!Lib.REG_NAMES.contains(arg))
	        length = memLenMap.get(arg);
	    return length;
	}


	static BitVecExpr get_inv_arg_val(Store store, long rip, String inv_arg, int block_id, int length) {
	    BitVecExpr res = null;
	    if(Lib.REG_NAMES.contains(inv_arg))
	        res = SymEngine.get_sym(store, rip, inv_arg, block_id, length);
	    else
	        res = SymEngine.get_sym(store, rip, "[" + inv_arg + "]", block_id, length);
	    return res;
	}

    static Store getParentStore(HashMap<Integer, Block> blockSet, Block blk) {
        Store store = null;
        if(blockSet.containsKey(blk.parent_id)) {
        	Block parentBlock = blockSet.get(blk.parent_id);
            store = parentBlock.store;
        }
        else {
            if(blk.inst.startsWith("cmp")) {
                store = blk.store;
            }
        }
        return store;
    }
    
    
    static ArrayList<String> retrieveSymSrcs(Block block) {
    	HashMap<String, Integer> memLenMap = new HashMap<>();
//    	System.out.println(Long.toHexString(block.address) + ": " + block.inst);
        String[] inst_split = block.inst.strip().split(" ", 2);
        ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
        Store store = block.store;
        Tuple<ArrayList<String>, Boolean> res = SMTHelper.get_bottom_source(inst_args.get(0), store, store.rip, memLenMap);
        return res.x;
    }
	
	
	static HashMap<Integer, ArrayList<String>> retrieveBIDSymInfo(Store p_store, long rip, ArrayList<String> srcNames) {
    	HashMap<Integer, ArrayList<String>> res = new HashMap<Integer, ArrayList<String>>();
        for(String symName : srcNames) {
            String tmpName = symName;
            if(Utils.imm_start_pat.matcher(symName).matches()) {
            	tmpName = "[" + symName + "]";
            }
            Integer bID = SymEngine.get_sym_block_id(p_store, rip, tmpName);
            if(bID != null) {
            	if(!res.containsKey(bID)) {
            		ArrayList<String> symInfo = new ArrayList<String>();
            		symInfo.add(symName);
            		res.put(bID, symInfo);
            	}
            	else {
            		ArrayList<String> symInfo = res.get(bID);
            		if(!symInfo.contains(symName))
            			symInfo.add(symName);
            	}
            }
        }
        return res;
    }


    // Add new (block_id, sym_name) pair to blockid_sym_list according to current src_names
    static HashMap<Integer, ArrayList<String>> updateBIDSymInfo(HashMap<Integer, ArrayList<String>> bIDSymMap, Store preStore, long rip, ArrayList<String> srcNames) {
    	HashMap<Integer, ArrayList<String>> newBIDSymMap = retrieveBIDSymInfo(preStore, rip, srcNames);
//    	System.out.println(newBIDSymMap.toString());
    	for(Integer bID : newBIDSymMap.keySet())
    	{
    		ArrayList<String> newSymInfo = newBIDSymMap.get(bID);
    		if(!bIDSymMap.containsKey(bID)) {
    			bIDSymMap.put(bID, newSymInfo);
    		}
    		else {
    			ArrayList<String> symInfo = bIDSymMap.get(bID);
    			for(String symName : newSymInfo) {
    				if(!symInfo.contains(symName)) {
    					symInfo.add(symName);
    				}
    			}
    		}
    	}
        return bIDSymMap;
    }
	    

	static void repeated_random_concretization(HashMap<BitVecExpr, ArrayList<BitVecExpr>> conc_res, BitVecExpr symValue, int sym_len, int count, Random random, int haltPoint) {
	    while(conc_res.get(symValue).size() < count) {
	        // rand_val = random.randint(0, 2**sym_len - 1)
	    	int concrValue = random.nextInt(Config.MAX_ARGC_NUM);
	        if(!conc_res.containsKey(symValue)) {
	        	conc_res.clear();
	        	ArrayList<BitVecExpr> tmp = new ArrayList<BitVecExpr>();
	        	tmp.add(Helper.gen_bv_num(concrValue, sym_len));
	        	conc_res.put(symValue, tmp);
	        }
	        else
	            conc_res.get(symValue).add(Helper.gen_bv_num(concrValue, sym_len));
	    }
	}



	static void ramdom_concretize_sym(Store store, HashMap<BitVecExpr, ArrayList<BitVecExpr>> concrRes, ArrayList<BitVecExpr> sym_vals, ArrayList<Integer> sym_lens, int count, Random random, int haltPoint) {
		Utils.REBUILD_BRANCHES_NUM = (haltPoint == 0) ? 1 : 2;
		for(int idx = 0; idx < sym_vals.size(); idx++) {
	    	BitVecExpr symValue = sym_vals.get(idx);
	        int sym_len = sym_lens.get(idx);
	        if(haltPoint == 2) {
		        if(concrRes.containsKey(symValue))
		            repeated_random_concretization(concrRes, symValue, sym_len, count, random, haltPoint);
		        else {
		            // rand_val = random.randint(0, 2**sym_len - 1)
		            int rand_val = random.nextInt(Config.MAX_ARGC_NUM);
		            concrRes.clear();
		            ArrayList<BitVecExpr> tmp = new ArrayList<BitVecExpr>();
		            tmp.add(Helper.gen_bv_num(rand_val, sym_len));
		            concrRes.put(symValue, tmp);
		            repeated_random_concretization(concrRes, symValue, sym_len, count, random, haltPoint);
		        }
	        }
	        else if(haltPoint == 0) {
	        	if(!concrRes.containsKey(symValue)) {
		    		long concrValue = ExtHandler.genFreshHeapPointer(store);
		        	ArrayList<BitVecExpr> tmp = new ArrayList<BitVecExpr>();
		        	tmp.add(Helper.gen_bv_num(concrValue, sym_len));
		        	concrRes.put(symValue, tmp);
	        	}
	        }
	    }
	}

	            

	static HashMap<BitVecExpr, ArrayList<BitVecExpr>> concretizeSymArg(Store store, ArrayList<BitVecExpr> symValues, ArrayList<Integer> symLengths, Constraint constraint, int haltPoint) {
		HashMap<BitVecExpr, ArrayList<BitVecExpr>> conc_res = new HashMap<BitVecExpr, ArrayList<BitVecExpr>>();
	    Random random = new Random();
	    ArrayList<String> symValueStrs = new ArrayList<String>();
	    for(BitVecExpr sym_val : symValues) {
	    	symValueStrs.add(sym_val.toString());
	    }
	    boolean sym_exist_in_constraint = false;
	    ArrayList<BoolExpr> predicates = constraint.get_asserts();
	    ArrayList<Model> m_list = Helper.checkPredsSatisfiable(predicates, Config.REBUILD_BRANCHES_NUM);
	    if(m_list != null) {
	    	for(Model m : m_list) {
	    		for(FuncDecl<?> d : m.getDecls()) {
	    			String dName = d.getName().toString();
	    			if(symValueStrs.contains(dName)) {
	    				int idx = symValueStrs.indexOf(dName);
	    				BitVecExpr symValue = symValues.get(idx);
	    				if(conc_res.containsKey(symValue)) {
	    					conc_res.get(symValue).add((BitVecExpr) m.getConstInterp(d));
	    				}
	    				else {
	    					ArrayList<BitVecExpr> tmp = new ArrayList<BitVecExpr>();
	    					conc_res.put(symValue, tmp);
	    					tmp.add((BitVecExpr) m.getConstInterp(d));
	    				}
	    			}
	    		}
	    		if(!sym_exist_in_constraint) break;
	    	}
	    }
	    ramdom_concretize_sym(store, conc_res, symValues, symLengths, Config.REBUILD_BRANCHES_NUM, random, haltPoint);
	    return conc_res;
	}


	static void update_sym_addr_valueset_map(HashMap<BitVecExpr, ArrayList<BitVecExpr>> sym_addr_valueset_map, HashMap<BitVecExpr, ArrayList<BitVecExpr>> concretize_sym_args) {
	    for(BitVecExpr sym_val : concretize_sym_args.keySet()) {
	        if(!sym_addr_valueset_map.containsKey(sym_val)) {
	        	sym_addr_valueset_map.put(sym_val, concretize_sym_args.get(sym_val));
	        }
	        // if(sym_val !in sym_addr_valueset_map:
	        //     sym_addr_valueset_map[sym_val] = conc_vals
	        // else:
	        //     sym_addr_valueset_map[sym_val].add(conc_val)
	    }
	}
	
	static ArrayList<String> detect_reg_in_memaddr_rep(String arg) {
		String reg = "(\\W+)";
		String[] argSplit = arg.split(reg);
		ArrayList<String> res = new ArrayList<String>();
	    for(String asi : argSplit) {
	        String as = asi.strip();
	        if(Lib.REG_NAMES.contains(as))
	            res.add(SymHelper.getRootReg(as));
	    }
	    return res;
	}
	
	
	static ArrayList<String> retrieve_source_for_memaddr(String inst, boolean common) {
		ArrayList<String> symNames = new ArrayList<String>();
	    if(common) {
	        String[] instSplit = inst.strip().split(" ", 2);
	        ArrayList<String> instArgs = Utils.parse_inst_args(instSplit);
	        for(String arg : instArgs) {
	            if(arg.endsWith("]")) {
	                String ar = Utils.extract_content(arg, "[");
	                symNames = detect_reg_in_memaddr_rep(ar);
	                break;
	            }
	        }
	    }
	    else {
	    	String symName = (Config.MEM_ADDR_SIZE == 64) ? "rdi": "edi";
	    	symNames.add(symName);
	    }
	    return symNames;
	}
	
	
	static String str_of_error_type(MEMORY_RELATED_ERROR_TYPE err) {
	    String res = "";
	    if(err == MEMORY_RELATED_ERROR_TYPE.NULL_POINTER_DEREFERENCE)
	        res = "Null pointer dereference";
	    else if(err == MEMORY_RELATED_ERROR_TYPE.USE_AFTER_FREE)
	        res = "Use after free";
	    else if(err == MEMORY_RELATED_ERROR_TYPE.FREE_AFTER_FREE)
	        res = "Use after free";
	    else if(err == MEMORY_RELATED_ERROR_TYPE.BUFFER_OVERFLOW)
	        res = "Buffer overflow";
	    else if(err == MEMORY_RELATED_ERROR_TYPE.UNINITIALIZED_CONTENT)
	        res = "Uninitialized content";
	    return res;
	}


	void resolve_value_for_stack_addr_inv_arg(int block_id, Store store, String stack_addr, ArrayList<BitVecExpr> substitute_pair, Constraint last_constraint, HashMap<String, Integer> mem_len_map) {
		ArrayList<BoolExpr> predicates = last_constraint.get_asserts();
	    Model m = Helper.check_pred_satisfiable(predicates);
	    if(m != null) {
	        int stack_val_len = mem_len_map.get(stack_addr);
	        BitVecExpr stack_val = SymEngine.get_sym(store, store.rip, "[" + stack_addr + "]", block_id, stack_val_len);
	        BitVecExpr res = stack_val;
	        for(FuncDecl<?> d : m.getDecls()) {
	            BitVecExpr s_val = (BitVecExpr) m.getConstInterp(d);
	            int s_len = s_val.getSortSize();
	            res = Helper.substitute_sym_val(res, Helper.gen_spec_sym(d.getName().toString(), s_len), s_val);
	            substitute_pair.add(Helper.gen_spec_sym(d.getName().toString(), s_len));
	            substitute_pair.add(s_val);
	        }
	        SymEngine.set_sym(store, store.rip, "[" + stack_addr + "]", res, block_id);
	    }
	}


	void substitute_sym_arg_for_all(Store store, BitVecExpr sym_arg, BitVecExpr sym_new) {
		HashMap<BitVecExpr, Node> mem_store = store.g_MemStore;
		for(BitVecExpr k : mem_store.keySet()) {
			Node v = mem_store.get(k);
			v.expr = Helper.substitute_sym_val(v.expr, sym_arg, sym_new);
		}
		HashMap<String, Node> reg_store = store.g_RegStore;
		for(String k : reg_store.keySet()) {
			Node v = reg_store.get(k);
			v.expr = Helper.substitute_sym_val(v.expr, sym_arg, sym_new);
		}
	}


	static void cfg_init_parameter(Store store, HashMap<String, Long> sym_table) {
		int length = Config.MEM_ADDR_SIZE;
	    if(sym_table.containsKey(Lib.STDIN)) {
	        Long stdin_address = sym_table.get(Lib.STDIN);
	        store.g_StdinAddress = Helper.gen_bv_num(stdin_address, Config.MEM_ADDR_SIZE);
	        store.g_StdinHandler = SymEngine.get_memory_val(store, store.g_StdinAddress, Utils.INIT_BLOCK_NO, Config.MEM_ADDR_SIZE);
	    }
	    else {
	        store.g_StdinAddress = Helper.gen_sym(length);
	        store.g_StdinHandler = Helper.gen_sym(length);
	    }
	    if(sym_table.containsKey(Lib.STDOUT)) {
	    	Long stdout_address = sym_table.get(Lib.STDOUT);
	    	store.g_StdoutAddress = Helper.gen_bv_num(stdout_address, Config.MEM_ADDR_SIZE);
	        store.g_StdoutHandler = SymEngine.get_memory_val(store, store.g_StdoutAddress, Utils.INIT_BLOCK_NO, Config.MEM_ADDR_SIZE);
	    }
	    else {
	    	store.g_StdoutAddress = Helper.gen_sym(length);
	        store.g_StdoutHandler = Helper.gen_sym(length);
	    }
	}
	
	
	static Block getParentBlockInfo(HashMap<Integer, Block> blockMap, Block blk) {
		Block pBlock = null;
		if(blockMap.containsKey(blk.parent_id)) {
			pBlock = blockMap.get(blk.parent_id);
		}
	    return pBlock;
	}


	static boolean check_path_reachability(Constraint constraint) {
		boolean res = true;
		ArrayList<BoolExpr> predicates = constraint.get_asserts();
	    Model m = Helper.check_pred_satisfiable(predicates);
	    if(m == null)
	    	res = false;
	    return res;
	}

	String find_out_func_name_with_addr_in_range(HashMap<Long, String> func_start_addr_name_map, long address) {
	    String res = "";
	    ArrayList<Long> start_addr_list = new ArrayList<Long>();
	    start_addr_list.addAll(func_start_addr_name_map.keySet());
	    Collections.sort(start_addr_list);
	    int addr_num = start_addr_list.size();
	    for(int idx = 0; idx < start_addr_list.size(); idx++) {
	    	long start_addr = start_addr_list.get(idx);
	    	if(idx + 1 < addr_num) {
	    		long next_addr = start_addr_list.get(idx + 1);
	    		if(address >= start_addr && address < next_addr) {
	    			res = func_start_addr_name_map.get(start_addr);
	    			break;
	    		}
	    	}
	    	else
	    		res = func_start_addr_name_map.get(start_addr);
	    }
	    return res;
	}


	int[] collect_statistic_data_from_map(HashMap<String, ArrayList<Integer>> cmc_func_exec_info) {
		int[] res = new int[Config.CMC_EXEC_RES_COUNT];
		for(String name : cmc_func_exec_info.keySet()) {
			ArrayList<Integer> func_exec_info = cmc_func_exec_info.get(name);
			for(int idx = 0; idx < res.length; idx++) {
				res[idx] += func_exec_info.get(idx);
			}
		}
	    return res;
	}


	static String readFuncName(HashMap<Long, String> addressSymTable, long address) {
		String res = "";
	    if(addressSymTable.containsKey(address)) {
	    	res = addressSymTable.get(address);
	    }
	    return res;
	}
	 

	static void start_init(Store store, long rip, int block_id) {
		List<String> dests = Config.ADDR_SIZE_REGS_MAP.get(Config.MEM_ADDR_SIZE);
		ExtHandler.set_regs_sym(store, rip, dests, block_id);
	    String spName = Config.ADDR_SIZE_SP_MAP.get(Config.MEM_ADDR_SIZE);
	    long stack_frame_pointer = Config.INIT_STACK_FRAME_POINTER.get(Config.MEM_ADDR_SIZE);
	    SymEngine.set_sym(store, rip, spName, Helper.gen_bv_num(stack_frame_pointer, Config.MEM_ADDR_SIZE), block_id);
	    ExtHandler.clear_flags(store);
	    BitVecExpr sym_src = Helper.gen_sym(Config.MEM_ADDR_SIZE);
	    BitVecExpr symSP = SymEngine.get_sym(store, rip, Config.ADDR_SIZE_SP_MAP.get(Config.MEM_ADDR_SIZE), block_id);
	    SymEngine.set_mem_sym(store, symSP, sym_src, block_id);
	    ExtHandler.insert_termination_symbol(store, rip, block_id);
	    ExtHandler.insert_termination_symbol(store, rip, block_id);
	}
	
	static Constraint handlePreConstraint(Store store, long rip, Constraint constraint, int block_id, HashMap<String, ArrayList<String>> gPreConstraint, HashMap<String, ArrayList<String>> extLibAssumptions) {
		Constraint newConstraint = constraint;
	    if(gPreConstraint != null) {
	        BoolExpr predicates = null;
	        for(String extName : gPreConstraint.keySet()) {
	        	ArrayList<String> preConstraint = gPreConstraint.get(extName);
	            for(String pConstraint : preConstraint) {
	                String constr = Utils.remove_multiple_spaces(pConstraint);
	                constr = constr.toLowerCase();
	                if(constr.contains("unchanged")) {
	                    String statepart = constr.split("=", 2)[0].strip();
	                    if(extLibAssumptions.containsKey(extName)) {
	                    	ArrayList<String> assumptions = extLibAssumptions.get(extName);
	                    	assumptions.add(statepart);
	                    }
	                    else {
	                    	ArrayList<String> assumptions = new ArrayList<String>();
	                    	assumptions.add(statepart);
	                    	extLibAssumptions.put(extName, assumptions);
	                    }
	                }
	                else if(extName.equals("starting_point")) {
	                	BoolExpr pred = parse_predicates(store, rip, block_id, extName, constr);
	                    if(pred != null) {
	                        if(predicates != null)
	                            predicates = Helper.bv_and(predicates, pred);
	                        else
	                            predicates = pred;
	                    }
	                }
	            }
	        }
	        if(predicates != null)
	        	newConstraint = new Constraint(constraint, predicates);
	    }
	    return newConstraint;
	}
	    

	static BitVecExpr get_sym_val(Store store, long rip, String src, int block_id) {
	    BitVecExpr res = null;
	    res = SymEngine.get_sym(store, rip, src.strip(), block_id);
	    return res;
	}


	static String preprocess_constraint(Store store, long rip, int block_id, String ext_name, String constraint) {
	    String res = null;
	    if(constraint.contains("fresh heap pointer")) {
	        // op = re.search(r"[<!=>]+", constraint).group(0)
	        // arg = constraint.split(op, 1)[0].strip()
	        // res = Utils.MIN_HEAP_ADDR + "<=" + arg + "<=" + Utils.MAX_HEAP_ADDR
	        // mem_size = SymEngine.get_sym(store, rip, "rdi", block_id) if(ext_name in ("malloc", "calloc") else SymEngine.get_sym(store, rip, "rsi", block_id)
	        BitVecExpr mem_size = Helper.gen_bv_num(Config.MAX_MALLOC_SIZE, Config.MEM_ADDR_SIZE);
	        ExtHandler.ext_gen_fresh_heap_pointer(store, rip, ext_name, block_id, mem_size);
	    }
	    else
	        res = constraint;
	    return res;
	}


	static BoolExpr parse_basic_pred(Store store, long rip, int block_id, String logic_op, String left, String right) {
	    BitVecExpr lhs = get_sym_val(store, rip, left, block_id);
	    BitVecExpr rhs = get_sym_val(store, rip, right, block_id);
	    if(lhs == null || rhs == null) return null;
	    Function<Tuple<BitVecExpr, BitVecExpr>, BoolExpr> func = Helper.LOGIC_OP_FUNC_MAP.get(logic_op);
	    BoolExpr pred = func.apply(new Tuple<BitVecExpr, BitVecExpr>(lhs, rhs));
	    return pred;
	}


	static BoolExpr parse_single_predicate(Store store, long rip, int block_id, String ext_name, String constr) {
		BoolExpr predicates = null;
	    String constraint = preprocess_constraint(store, rip, block_id, ext_name, constr);
	    if(constraint != null) {
	    	ArrayList<String> logic_ops = new ArrayList<String>();
	    	Matcher m = Pattern.compile("[<!=>]+").matcher(constraint);
	    	while (m.find()) {
	    		logic_ops.add(m.group());
	    	}
	        if(logic_ops.size() > 1) {
	        	ArrayList<String> operands = new ArrayList<String>();
	            String rest = constraint;
	            for(String logic_op : logic_ops) {
	            	String[] tmp = rest.split(logic_op, 2);
	            	String lhs = tmp[0];
	            	rest = tmp[1];
	                operands.add(lhs.strip());
	            }
	            operands.add(rest.strip());
	            int index = 0;
	            for(String logic_op : logic_ops) {
	                BoolExpr pred = parse_basic_pred(store, rip, block_id, logic_op, operands.get(index), operands.get(index+1));
	                if(pred != null) {
	                    if(predicates != null)
	                        predicates = Helper.bv_and(predicates, pred);
	                    else
	                        predicates = pred;
	                }
	                index += 1;
	            }
	        }
	        else if(logic_ops.size() == 1) {
	            String logic_op = logic_ops.get(0);
	            String[] constr_split = constraint.split(logic_op);
	            predicates = parse_basic_pred(store, rip, block_id, logic_op, constr_split[0], constr_split[1]);
	        }
	    }
	    return predicates;
	}


	static BoolExpr parse_predicates(Store store, long rip, int block_id, String ext_name, String constraint) {
	    String[] constraint_list = constraint.split("or");
	    BoolExpr predicates = null;
	    for(String c : constraint_list) {
	        BoolExpr pred = parse_single_predicate(store, rip, block_id, ext_name, c);
	        if(pred != null) {
	            if(predicates != null)
	                predicates = Helper.bv_or(predicates, pred);
	            else
	                predicates = pred;
	        }
	    }
	    return predicates;
	}


	static Constraint insert_new_constraints(Store store, long rip, int block_id, String ext_name, ArrayList<String> preConstraint, Constraint constraint) {
	    Constraint new_constraint = constraint;
	    if(preConstraint != null && preConstraint.size() > 0) {
	        BoolExpr predicates = null;
	        for(String p_constraint : preConstraint) {
	            String p_constr = Utils.remove_multiple_spaces(p_constraint);
	            p_constr = p_constraint.toLowerCase();
	            BoolExpr pred = parse_predicates(store, rip, block_id, ext_name, p_constr);
	            if(pred != null)
	                if(predicates != null)
	                    predicates = Helper.bv_and(predicates, pred);
	                else
	                    predicates = pred;
	        }
	        if(predicates != null)
	            new_constraint = new Constraint(constraint, predicates);
	    }
	    return new_constraint;
	}
	
	
    static int getOperandSize(String inst, String arg, HashMap<String, Integer> memLenMap) {
        int res = Config.MEM_ADDR_SIZE;
        InstElement instElem = new InstElement(inst);
        if(instElem.inst_args.size() == 2) {
            String operand = instElem.inst_args.get(1);
            res = Utils.getSymLength(operand);
        }
        else
            res = getRealLength(memLenMap, arg);
        return res;
    }


}
