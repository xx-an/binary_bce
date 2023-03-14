package controlflow;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_sort_kind;

import block.Block;
import block.Constraint;
import block.Node;
import block.Store;
import common.Config;
import common.Lib;
import common.Lib.MEMORY_RELATED_ERROR_TYPE;
import common.Triplet;
import common.Utils;
import semantics.SMTHelper;
import semantics.Semantics;
import symbolic.SymEngine;
import symbolic.SymHelper;
import common.Helper;
import common.Tuple;

public class CFHelper {

	static Integer gen_cjmp_idx_upperbound(String inst_name, int boundary) {
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


	static Tuple<Integer, Integer> gen_jt_idx_upperbound(ArrayList<Block> trace_list, int boundary) {
	    Integer res = null;
	    Integer idx = 0;
	    for(idx = 0; idx < trace_list.size(); idx++) {
	    	Block blk = trace_list.get(idx);
	        String inst = blk.inst;
	        if(Utils.check_not_single_branch_inst(inst)) {
	            res = gen_cjmp_idx_upperbound(inst.split(" ", 2)[0], boundary);
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


	static long get_next_address(long address, HashMap<Long, Long> address_next_map, HashMap<BitVecExpr, ArrayList<String>> address_sym_table) {
	    long next_address = address_next_map.get(address);
	    if(address_sym_table.containsKey(Helper.gen_bv_num(next_address, Config.MEM_ADDR_SIZE))) return -1;
	    return next_address;
	}


	static boolean check_jt_assign_inst(String inst_args) {
	    boolean res = false;
	    String[] inst_arg_s = inst_args.split(",");
	    if(inst_arg_s.length == 2) {
	        String inst_arg_0 = inst_arg_s[0].strip();
	        String inst_arg_1 = inst_arg_s[1].strip();
	        if(Lib.REG_NAMES.contains(inst_arg_0) && inst_arg_1.endsWith("]") && !(inst_arg_1.contains("rip")))
	            res = (inst_arg_1.contains("*")) && (inst_arg_1.contains("+"));
	    }
	    return res;
	}


	static Tuple<Integer, Boolean> check_jump_table_assign_inst(ArrayList<Block> trace_list, int idx) {
	    boolean res = false;
	    int n_idx = 0;
	    int trace_count = trace_list.size();
	    for(n_idx = idx + 1; n_idx < trace_count; n_idx++) {
	        Block blk = trace_list.get(n_idx);
	        String inst = blk.inst;
	        if(inst.startsWith("mov")) {
	            res = check_jt_assign_inst(inst.split(" ", 2)[1].strip());
	            if(res) break;
	        }
	    }
	    return new Tuple<Integer, Boolean>(n_idx, res);
	}


	// Read all the jump table entries
	static Triplet<ArrayList<BitVecExpr>, String, Integer> get_distinct_jt_entries(Block blk, BitVecExpr src_sym, int jt_idx_upperbound, HashMap<Integer, Block> block_set) {
		ArrayList<BitVecExpr> res = new ArrayList<BitVecExpr>();
	    String inst = blk.inst;
	    String[] inst_arg_split = inst.split(" ", 2)[1].strip().split(",");
	    String inst_dest = inst_arg_split[0];
	    String inst_src = inst_arg_split[1].strip();
	    int src_len = Utils.get_sym_length(inst_src);
	    Block parent_blk = block_set.get(blk.parent_id);
	    Store p_store = parent_blk.store;
	    for(int idx = 0; idx < jt_idx_upperbound; idx++) {
	    	BitVecExpr src_val = Helper.gen_bv_num(idx, src_sym.getSortSize());
	        BitVecExpr mem_address = SymEngine.get_jump_table_address(p_store, inst_src, src_sym, src_val, Config.MEM_ADDR_SIZE);
	        BitVecExpr mem_val = SymEngine.read_memory_val(p_store, mem_address, Utils.INIT_BLOCK_NO, src_len);
	        if(!Helper.is_bit_vec_num(mem_val)) {
	            return new Triplet<ArrayList<BitVecExpr>, String, Integer>(null, inst_dest, src_len);
	        }
	        if(!res.contains(mem_val))
	        	res.add(mem_val);
	    }
	    return new Triplet<ArrayList<BitVecExpr>, String, Integer>(res, inst_dest, src_len);
	}


	static boolean detect_loop(Block block, Long address, Long new_address, HashMap<Integer, Block> block_set) {
	    boolean exists_loop = false;
	    Integer parent_id = block.parent_id;
	    Long prev_address = null;
	    while(parent_id != null) {
	        if(block_set.containsKey(parent_id)) {
	            Block parent_blk = block_set.get(parent_id);
	            Long p_address = parent_blk.address;
	            if(p_address == address) {
	                if(prev_address != -1 && prev_address == new_address) {
	                    exists_loop = true;
	                    break;
	                }
	            }
	            parent_id = parent_blk.parent_id;
	            prev_address = p_address;
	        }
	        else break;
	    }
	    return exists_loop;
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


	static ArrayList<Store> reconstruct_jt_sym_stores(Block blk, ArrayList<BitVecExpr> distinct_entries, String inst_dest, int src_len) {
	    String inst = blk.inst;
	    Store store = blk.store;
	    long rip = store.get_rip();
	    int dest_len = Utils.get_sym_length(inst_dest);
	    ArrayList<Store> store_list = new ArrayList<Store>();
	    String inst_name = inst.split(" ", 2)[0];
	    for(BitVecExpr mem_val : distinct_entries) {
	        Store new_store = new Store(store, rip);
	        if(inst_name.equals("mov"))
	            SymEngine.set_sym(new_store, rip, inst_dest, mem_val, blk.block_id);
	        else if(inst_name.contains("s"))
	            Semantics.mov_op(new_store, inst_dest, dest_len, mem_val, src_len, true);
	        else if(inst_name.contains("z"))
	            Semantics.mov_op(new_store, inst_dest, dest_len, mem_val, src_len, false);
	        store_list.add(new_store);
	    }
	    return store_list;
	}


	static Tuple<String, ArrayList<BitVecExpr>> reconstruct_jt_target_addresses(ArrayList<Block> trace_list, int blk_idx, ArrayList<Store> store_list, HashMap<Long, Tuple<String, ArrayList<BitVecExpr>>> address_jt_entries_map) {
	    for(int idx = blk_idx + 1; idx < trace_list.size(); idx++) {
	    	Block blk = trace_list.get(idx);
	    	long address = blk.address;
	    	String inst = blk.inst;
	    	long rip = blk.store.get_rip();
	        String[] inst_split = inst.split(" ", 2);
	        String inst_name = inst_split[0];
	        if(Utils.check_jmp_with_address(inst_name)) {
	            String inst_dest = inst_split[1].strip();
	            ArrayList<BitVecExpr> target_addresses = new ArrayList<BitVecExpr>();
	            for(Store store : store_list) {
	            	BitVecExpr target_addr = SymEngine.get_sym(store, rip, inst_dest, Utils.INIT_BLOCK_NO);
	                target_addresses.add(target_addr);
	            }
	            address_jt_entries_map.put(address, new Tuple<>(inst_dest, target_addresses));
	            return new Tuple<>(inst_dest, target_addresses);
	        }
	        else {
	        	for(Store store : store_list) {
	                store.rip = rip;
	                Semantics.parse_semantics(store, rip, inst, blk.block_id);
	        	}
	        }
	    }
	    return new Tuple<>(null, null);
	}


	static String get_unified_sym_name(HashMap<BitVecExpr, ArrayList<String>> address_sym_table, long address) {
	    String res = "";
	    BitVecExpr bv_address = Helper.gen_bv_num(address, Config.MEM_ADDR_SIZE);
	    if(address_sym_table.containsKey(bv_address)) {
	        String sym_name = address_sym_table.get(bv_address).get(0);
	        res = sym_name.split("@", 2)[0].strip();
	    }
	    return res;
	}


	static int get_real_length(HashMap<String, Integer> mem_len_map, String arg) {
	    int length = Config.MEM_ADDR_SIZE;
	    if(!Lib.REG_NAMES.contains(arg));
	        length = mem_len_map.get(arg);
	    return length;
	}

	Tuple<String, ArrayList<String>> construct_print_info(int parent_id, Store parent_store, long parent_rip, Store new_store, long rip, ArrayList<String> invariant_arguments) {
	    ArrayList<String> p_info = new ArrayList<String>();
	    ArrayList<String> stack_addr = new ArrayList<String>();
	    long stack_top = SymHelper.top_stack_addr(new_store);
	    for(String inv_arg : invariant_arguments) {
	        if(Lib.REG_NAMES.contains(inv_arg))
	            p_info.add("register " + inv_arg);
	        else {
	            p_info.add("memory address " + inv_arg);
	            if(Utils.imm_start_pat.matcher(inv_arg).matches()) {
	                long mem_addr = Utils.imm_str_to_int(inv_arg);
	                if(mem_addr >= stack_top)
	                    stack_addr.add(inv_arg);
	            }
	        }
	        BitVecExpr prev_val = SymEngine.get_sym(parent_store, parent_rip, inv_arg, parent_id);
	        SymEngine.set_sym(new_store, rip, inv_arg, prev_val, parent_id);
	    }
	    String print_info = String.join(", ", p_info);
	    return new Tuple<String, ArrayList<String>>(print_info, stack_addr);
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
        String[] inst_split = block.inst.strip().split(" ", 2);
        ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
        Store store = block.store;
        Tuple<ArrayList<String>, Boolean> res = SMTHelper.get_bottom_source(inst_args.get(0), store, store.rip, memLenMap);
        return res.x;
    }
	
	
	static HashMap<Integer, ArrayList<String>> retrieveBIDSymInfo(Store p_store, long rip, ArrayList<String> src_names) {
    	HashMap<Integer, ArrayList<String>> res = new HashMap<Integer, ArrayList<String>>();
        for(String symName : src_names) {
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
	    

	static void repeated_random_concretization(HashMap<BitVecExpr, ArrayList<BitVecExpr>> conc_res, BitVecExpr sym_val, int sym_len, int count, Random random) {
	    while(conc_res.get(sym_val).size() < count) {
	        // rand_val = random.randint(0, 2**sym_len - 1)
	        int rand_val = random.nextInt(Config.MAX_ARGC_NUM);
	        if(!conc_res.containsKey(sym_val)) {
	        	conc_res.clear();
	        	ArrayList<BitVecExpr> tmp = new ArrayList<BitVecExpr>();
	        	tmp.add(Helper.gen_bv_num(rand_val, sym_len));
	        	conc_res.put(sym_val, tmp);
	        }
	        else
	            conc_res.get(sym_val).add(Helper.gen_bv_num(rand_val, sym_len));
	    }
	}



	static void ramdom_concretize_sym(HashMap<BitVecExpr, ArrayList<BitVecExpr>> conc_res, ArrayList<BitVecExpr> sym_vals, ArrayList<Integer> sym_lens, int count, Random random) {
	    for(int idx = 0; idx < sym_vals.size(); idx++) {
	    	BitVecExpr sym_val = sym_vals.get(idx);
	        int sym_len = sym_lens.get(idx);
	        if(conc_res.containsKey(sym_val))
	            repeated_random_concretization(conc_res, sym_val, sym_len, count, random);
	        else {
	            // rand_val = random.randint(0, 2**sym_len - 1)
	            int rand_val = random.nextInt(Config.MAX_ARGC_NUM);
	            conc_res.clear();
	            ArrayList<BitVecExpr> tmp = new ArrayList<BitVecExpr>();
	            tmp.add(Helper.gen_bv_num(rand_val, sym_len));
	        	conc_res.put(sym_val, tmp);
	            repeated_random_concretization(conc_res, sym_val, sym_len, count, random);
	        }
	    }
	}

	            

	static HashMap<BitVecExpr, ArrayList<BitVecExpr>> concretize_sym_arg(ArrayList<BitVecExpr> sym_vals, ArrayList<Integer> sym_lens, Constraint constraint) {
		HashMap<BitVecExpr, ArrayList<BitVecExpr>> conc_res = new HashMap<BitVecExpr, ArrayList<BitVecExpr>>();
	    Random random = new Random();
	    ArrayList<String> sym_val_strs = new ArrayList<String>();
	    for(BitVecExpr sym_val : sym_vals) {
	    	sym_val_strs.add(sym_val.toString());
	    }
	    boolean sym_exist_in_constraint = false;
	    ArrayList<BoolExpr> predicates = constraint.get_asserts();
	    ArrayList<Model> m_list = Helper.repeated_check_pred_satisfiable(predicates, Config.REBUILD_BRANCHES_NUM);
	    if(m_list != null) {
	    	for(Model m : m_list) {
	    		for(FuncDecl<?> d : m.getDecls()) {
	    			String d_name = d.getName().toString();
	    			if(sym_val_strs.contains(d_name)) {
	    				int idx = sym_val_strs.indexOf(d_name);
	    				BitVecExpr sym_val = sym_vals.get(idx);
	    				if(conc_res.containsKey(sym_val)) {
	    					conc_res.get(sym_val).add((BitVecExpr) m.getConstInterp(d));
	    				}
	    				else {
	    					ArrayList<BitVecExpr> tmp = new ArrayList<BitVecExpr>();
	    					conc_res.put(sym_val, tmp);
	    					tmp.add((BitVecExpr) m.getConstInterp(d));
	    				}
	    			}
	    		}
	    		if(!sym_exist_in_constraint) break;
	    	}
	    }
	    ramdom_concretize_sym(conc_res, sym_vals, sym_lens, Config.REBUILD_BRANCHES_NUM, random);
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
	            res.add(SymHelper.get_root_reg(as));
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
	    else
	    	symNames.add("rdi");
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

	Tuple<String, Long> retrieve_call_inst_func_name(Block func_call_blk, HashMap<Long, String> address_inst_map, HashMap<BitVecExpr, ArrayList<String>> address_sym_table) {
	    String func_name = null;
	    Store store = func_call_blk.store;
	    long rip = store.rip;
	    String jump_address_str = func_call_blk.inst.split(" ", 2)[1].strip();
	    BitVecExpr n_address = SMTHelper.get_jump_address(store, rip, jump_address_str);
	    long new_address = Helper.long_of_sym(n_address);
	    if(address_inst_map.containsKey(new_address))
	        func_name = get_function_name_from_addr_sym_table(address_sym_table, new_address);
	    else {
	    	BitVecExpr bv_addr = SymEngine.get_effective_address(store, rip, String.valueOf(new_address));
	    	if(address_sym_table.containsKey(bv_addr))
		        func_name = get_function_name_from_addr_sym_table(address_sym_table, new_address);
            
	    }
	    return new Tuple<String, Long>(func_name, new_address);
	}


	static void cfg_init_parameter(Store store, HashMap<String, BitVecExpr> sym_table) {
		int length = Config.MEM_ADDR_SIZE;
	    if(sym_table.containsKey(Lib.STDIN)) {
	        BitVecExpr stdin_address = sym_table.get(Lib.STDIN);
	        store.g_StdinAddress = stdin_address;
	        store.g_StdinHandler = SymEngine.get_memory_val(store, stdin_address, Utils.INIT_BLOCK_NO, Config.MEM_ADDR_SIZE);
	    }
	    else {
	        store.g_StdinAddress = Helper.gen_sym(length);
	        store.g_StdinHandler = Helper.gen_sym(length);
	    }
	    if(sym_table.containsKey(Lib.STDOUT)) {
	    	BitVecExpr stdout_address = sym_table.get(Lib.STDOUT);
	    	store.g_StdoutAddress = stdout_address;
	        store.g_StdoutHandler = SymEngine.get_memory_val(store, stdout_address, Utils.INIT_BLOCK_NO, Config.MEM_ADDR_SIZE);
	    }
	    else {
	    	store.g_StdoutAddress = Helper.gen_sym(length);
	        store.g_StdoutHandler = Helper.gen_sym(length);
	    }
	}


	Tuple<String, Long> retrieve_internal_call_inst_func_name(Block func_call_blk, HashMap<Long, String> address_inst_map, HashMap<BitVecExpr, ArrayList<String>> address_sym_table) {
	    String func_name = null;
	    Store store = func_call_blk.store;
	    long rip = store.rip;
	    String jump_address_str = func_call_blk.inst.split(" ", 2)[1].strip();
	    BitVecExpr n_address = SMTHelper.get_jump_address(store, rip, jump_address_str);
	    long new_address = Helper.long_of_sym(n_address);
	    if(address_inst_map.containsKey(new_address))
	    	func_name = get_function_name_from_addr_sym_table(address_sym_table, new_address);
	    else {
	    	BitVecExpr bv_addr = SymEngine.get_effective_address(store, rip, String.valueOf(new_address));
	    	if(address_sym_table.containsKey(bv_addr))
	    		func_name = get_function_name_from_addr_sym_table(address_sym_table, new_address);
	    }
	    return new Tuple<String, Long>(func_name, new_address);
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


	static String get_function_name_from_addr_sym_table(HashMap<BitVecExpr, ArrayList<String>> addressSymTable, long address) {
		String res = "";
		BitVecExpr bv_addr = Helper.gen_bv_num(address, Config.MEM_ADDR_SIZE);
	    if(addressSymTable.containsKey(bv_addr)) {
	    	ArrayList<String> val = addressSymTable.get(bv_addr);
	        if(val.size() > 1)
	            res = val.get(1);
	        else
	            res = val.get(0);
	    }
	    return res;
	}
	 

	static void start_init(Store store, long rip, int block_id) {
		List<String> dests = Config.ADDR_SIZE_REGS_MAP.get(Config.MEM_ADDR_SIZE);
		ExtHandler.set_regs_sym(store, rip, dests, block_id);
	    String sp_name = Config.ADDR_SIZE_SP_MAP.get(Config.MEM_ADDR_SIZE);
	    long stack_frame_pointer = Config.INIT_STACK_FRAME_POINTER.get(Config.MEM_ADDR_SIZE);
	    SymEngine.set_sym(store, rip, sp_name, Helper.gen_bv_num(stack_frame_pointer, Config.MEM_ADDR_SIZE), block_id);
	    ExtHandler.set_segment_regs_sym(store, rip);
	    ExtHandler.clear_flags(store);
	    BitVecExpr sym_src = Helper.gen_sym(Config.MEM_ADDR_SIZE);
	    BitVecExpr sym_sp = SymEngine.get_sym(store, rip, Config.ADDR_SIZE_SP_MAP.get(Config.MEM_ADDR_SIZE), block_id);
	    SymEngine.set_mem_sym(store, sym_sp, sym_src, block_id);
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
	    BoolExpr pred = Helper.LOGIC_OP_FUNC_MAP.get(logic_op).apply(new Tuple<>(lhs, rhs));
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
	    if(preConstraint.size() > 0) {
	        BoolExpr predicates = null;
	        for(String p_constraint : preConstraint) {
	            String p_constr = Utils.remove_multiple_spaces(p_constraint);
	            p_constr = p_constraint.toLowerCase();
	            BoolExpr pred = parse_predicates(store, rip, block_id, ext_name, p_constraint);
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


}
