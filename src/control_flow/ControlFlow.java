package control_flow;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Model;

import block.Block;
import block.Constraint;
import block.Store;
import common.Config;
import common.Helper;
import common.Lib;
import common.Triplet;
import common.Tuple;
import common.Utils;
import semantics.SMTHelper;
import semantics.Semantics;
import symbolic.SymEngine;
import symbolic.SymHelper;

public class ControlFlow {
	
	HashMap<Integer, Block> block_set;
	ArrayDeque<Block> block_stack;
    HashMap<Long, Block> address_block_map;
    HashMap<Long, Integer> address_block_cnt_map;
    HashMap<Long, String> address_ext_func_map;
    HashMap<String, Integer> mem_len_map;
    HashMap<String, BitVecExpr> sym_table;
    HashMap<BitVecExpr, ArrayList<String>> address_sym_table;
    HashMap<Long, String> address_inst_map;
    HashMap<Long, Long> address_next_map;
    HashMap<BitVecExpr, String> dll_func_info;
    HashMap<Tuple<Long, Long>, Integer> loop_trace_counter;
    String disasm_type;
    Block dummy_block;
    long start_address;
    long main_address;
    int valid_address_no;
    HashSet<Long> address_except_set;
    HashMap<Long, Long> ret_call_address_map;
    HashMap<Long, Tuple<String, ArrayList<BitVecExpr>>> address_jt_entries_map;
    HashSet<Long> indirect_inst_set;
    Store store;
    Constraint constraint;
	
	ControlFlow(HashMap<String, BitVecExpr> sym_table, HashMap<BitVecExpr, ArrayList<String>> address_sym_table, HashMap<Long, String> address_inst_map, HashMap<Long, Long> address_next_map, long start_address, long main_address, String func_name, HashMap<Long, String> address_ext_func_map, int valid_address_no, HashMap<BitVecExpr, String> dll_func_info) {
        block_set = new HashMap<Integer, Block>();
        block_stack = new ArrayDeque<Block>();
        address_block_map = new HashMap<Long, Block>();
        mem_len_map = new HashMap<String, Integer>();
        loop_trace_counter = new HashMap<>();
        this.sym_table = sym_table;
        this.address_sym_table = address_sym_table;
        this.start_address = start_address;
        this.address_inst_map = address_inst_map;
        this.address_next_map = address_next_map;
        this.address_ext_func_map = address_ext_func_map;
        this.dll_func_info = dll_func_info;
        this.disasm_type = disasm_type;
        this.main_address = main_address;
        this.valid_address_no = valid_address_no;
        address_except_set = new HashSet<Long>();
        ret_call_address_map = new HashMap<Long, Long>();
        address_jt_entries_map = new HashMap<Long, Tuple<String, ArrayList<BitVecExpr>>>();
        indirect_inst_set = new HashSet<Long>();
        dummy_block = new Block(null, null, "", null, null);
        store = new Store(null);
        constraint = null;
        retrieve_all_branch_inst();
        Helper.cnt_init();
        CFHelper.start_init(store, start_address, Utils.INIT_BLOCK_NO);
        CFHelper.cfg_init_parameter(store, sym_table);
        build_cfg(start_address, store, constraint);
//        pp_unreachable_instrs();
	}

    
    void build_cfg(long start_address, Store store, Constraint constraint) {
        String start_inst = address_inst_map.get(start_address);
        add_new_block(null, start_address, start_inst, store, constraint);
        while(block_stack.size() != 0) {
            Block curr = block_stack.pop();
            Utils.logger.info(Long.toHexString(curr.address) + ": " + curr.inst);
//            Utils.logger.info(curr.store.pp_store());
            String inst = curr.inst;
            if(inst != null && inst.startsWith("bnd "))
                inst = inst.strip().split(" ", 1)[1];
            if(Utils.check_branch_inst(inst)) {
                construct_branch(curr, curr.address, inst, curr.store, curr.constraint);
            }
            else
            	jump_to_next_block(curr, curr.address, curr.store, curr.constraint);
        }
    }
    
    
    void construct_conditional_branches(Block block, long address, String inst, long new_address, Store store, Constraint constraint) {
        BoolExpr res = SMTHelper.parse_predicate(store, inst, true, "j");
        if(res == Helper.sym_false()) {
        	long next_address = CFHelper.get_next_address(address, address_next_map, address_sym_table);
        	construct_conditional_jump_block(block, address, inst, next_address, store, constraint, res);
        }
        else if(res == Helper.sym_true())
        	construct_conditional_jump_block(block, address, inst, new_address, store, constraint, res);
        else {
        	long next_address = CFHelper.get_next_address(address, address_next_map, address_sym_table);
            construct_conditional_jump_block(block, address, inst, next_address, store, constraint, Helper.sym_false());
            construct_conditional_jump_block(block, address, inst, new_address, store, constraint, Helper.sym_true());
        }
    }
    
    
    void construct_conditional_jump_block(Block block, long address, String inst, long new_address, Store store, Constraint constraint, BoolExpr val) {
        if(address_block_map.containsKey(address)) {
        	Tuple<Long, Long> addr_pair = new Tuple<Long, Long>(address, new_address);
            if(loop_trace_counter.containsKey(addr_pair)) {
                int counter = loop_trace_counter.get(addr_pair);
                if(counter < Config.MAX_LOOP_COUNT) {
                	loop_trace_counter.put(addr_pair, counter + 1);
                    jump_to_block_w_new_constraint(block, inst, new_address, store, constraint, val);
                }
            }
            else {
                boolean exists_loop = CFHelper.detect_loop(block, address, new_address, block_set);
                if(exists_loop)
                	loop_trace_counter.put(addr_pair, 1);
                jump_to_block_w_new_constraint(block, inst, new_address, store, constraint, val);
            }
        }
        else
        	jump_to_block_w_new_constraint(block, inst, new_address, store, constraint, val);
    }
    
    
    void jump_to_block_w_new_constraint(Block block, String inst, long new_address, Store store, Constraint constraint, BoolExpr val) {
    	Constraint new_constraint = add_new_constraint(store, constraint, inst, val, "j");
        String new_inst = address_inst_map.get(new_address);
        add_new_block(block, new_address, new_inst, store, new_constraint);
    }
                

    void construct_branch(Block block, long address, String inst, Store store, Constraint constraint) {
        if(inst == "ret" || inst.endsWith(" ret") || inst.startsWith("ret ")) {
//            indirect_inst_set.add(address);
            build_ret_branch(block, address, inst, store, constraint);
        }
        else {
            String jump_address_str = inst.split(" ", 1)[1].strip();
            BitVecExpr n_address = SMTHelper.get_jump_address(store, store.rip, jump_address_str);
            Long new_address = null;
            if(Helper.is_bit_vec_num(n_address)) {
            	new_address = Helper.long_of_sym(n_address);
	            if(address_inst_map.containsKey(new_address)) {
	                if(address_ext_func_map.containsKey(new_address)) {
	                    String ext_func_name = CFHelper.get_function_name_from_addr_sym_table(address_sym_table, new_address);
	                    handle_external_function(new_address, ext_func_name, block, address, inst, store, constraint);
	                }
	                else {
	                    handle_internal_jumps(block, address, inst, store, constraint, new_address);
	                }
	            }
	            else if(address_sym_table.containsKey(new_address)) {
	                String ext_func_name = CFHelper.get_function_name_from_addr_sym_table(address_sym_table, new_address);
	                handle_external_function(new_address, ext_func_name, block, address, inst, store, constraint);
	            }
	            else if(dll_func_info.containsKey(new_address)) {
	                String ext_func_name = dll_func_info.get(new_address);
	                handle_external_function(new_address, ext_func_name, block, address, inst, store, constraint);
	            }
	            else {
	            	String ext_func_name = "unresolved";
	                Utils.logger.info("Jump to an unresolved address " + Long.toHexString(new_address) + " at " + Long.toHexString(address) + ": " + inst);
	                external_branch(ext_func_name, block, address, inst, store, constraint);
	                // sys.exit("There exists an unresolved jump address " + Long.toHexString(new_address) + " at " + Long.toHexString(address) + ": " + inst)
	            }
            }
            else {
            	if(n_address.toString().startsWith(Utils.MEM_DATA_SEC_SUFFIX)) {
                	String ext_func_name = new_address.toString();
                    Utils.logger.info("Jump to an external address " + new_address.toString() + " at " + Long.toHexString(address) + ": " + inst);
                    external_branch(ext_func_name, block, address, inst, store, constraint);
                }
                else
                    handle_unresolved_indirect_jumps(block, address, inst, constraint, new_address);
            }
        }
    }    
                        

    void handle_unresolved_indirect_jumps(Block block, long address, String inst, Constraint constraint, long new_address) {
        if(inst.startsWith("jmp ") && !inst.endsWith("]")) {
            ArrayList<Block> trace_list = new ArrayList<Block>();
            ArrayList<String> sym_names = new ArrayList<String>();
            sym_names.add(inst.split(" ", 1).get(1].strip());
            int res = trace_back(block, sym_names, trace_list);
            if(res == -1) {
                if(constraint != null) {
                    Model path_reachable = _check_path_reachability(constraint);
                    if(path_reachable == null)
                        return;
                }
                Utils.logger.info("Cannot resolve the jump address " + Long.toHexString(new_address) + " of " + inst + " at address " + Long.toHexString(address));
                // sys.exit("Can!resolve the jump address " + Long.toHexString(new_address) + " of " + inst + " at address " + Long.toHexString(address))
            }
        }
        else {
            if(constraint != null) {
            	Model path_reachable = _check_path_reachability(constraint);
                if(path_reachable == null) {
                    Utils.logger.info("The path is infeasible at the jump address " + Long.toHexString(new_address) + " of " + inst + " at address " + Long.toHexString(address) + "\n");
                    return;
                }
            }
            Utils.logger.info("Cannot resolve the jump address " + Long.toHexString(new_address) + " of " + inst + " at address " + Long.toHexString(address))
            // sys.exit("Can!resolve the jump address " + Long.toHexString(new_address) + " of " + inst + " at address " + Long.toHexString(address))
        }
    }

    void handle_external_function(long ext_func_address, String ext_func_name, Block block, long address, String inst, Store store, Constraint constraint) {
        Utils.logger.info("Execute the function: " + ext_func_name + "\n");
        long rip = store.rip;
        String ext_name = ext_func_name.split("@", 1)[0].strip();
        String pre_constraint = global_pre_constraint[ext_name] if ext_name in self.global_pre_constraint else None
        if(ext_func_name.startsWith("__libc_start_main")) {
            Semantics.call(store, rip);
            long next_address = main_address;
            Utils.logger.info(Long.toHexString(address) + ": jump address == " + Long.toHexString(next_address));
            ExtHandler.ext__libc_start_main(store, rip, main_address);
            jump_to_block(block, inst, next_address, store, constraint);
        }
        else if(ext_func_name == "pthread_create") {
            Store jmp_store = new Store(store, rip);
            BitVecExpr sym_rdi = SymEngine.get_sym(store, rip, "rdi");
            if(Helper.is_bit_vec_num(sym_rdi)) {
                Semantics.ret(jmp_store);
                long rdi_val = Helper.long_of_sym(sym_rdi);
                if(address_inst_map.containsKey(rdi_val)) {
                    Utils.logger.info(Long.toHexString(address) + ": jump address == " + Long.toHexString(rdi_val));
                    jump_to_block(block, inst, rdi_val, jmp_store, constraint);
                }
            }
            Store fall_through_store = new Store(store, rip);
            ExtHandler.ext_func_call(fall_through_store, ext_func_name);
            build_ret_branch(block, address, inst, fall_through_sym_store, constraint);
        }
        else if(ext_func_name == "malloc" || ext_func_name == "calloc" || ext_func_name == "realloc") {
            ExtHandler.ext_alloc_mem_call(store, rip, ext_func_name, block.block_id);
//            build_ret_branch(block, address, inst, store, constraint);
            new_constraint = CFHelper.insert_new_constraints(store, rip, block.block_id, ext_name, pre_constraint, constraint);
        }
        else if(ext_func_name == "free") {
            ExtHandler.ext_free_mem_call(store, rip);
            build_ret_branch(block, address, inst, store, constraint);
        }
        else {
            ExtHandler.ext_func_call(store, rip, ext_func_name);
            String ext_name = ext_func_name.split("@", 1).get(0].strip();
            if(!Lib.TERMINATION_FUNCTIONS.contains(ext_name))
                build_ret_branch(block, address, inst, store, constraint);
        }
    }


    void build_ret_branch(Block block, long address, String inst, Store store, Constraint constraint) {
        Long new_address = Semantics.ret(store, inst);
        if(new_address != null) {
            if(Helper.is_bit_vec_num(new_address)) {
                Utils.logger.info(Long.toHexString(address) + ": the return address == {}".format(Long.toHexString(new_address)))
                if(address_inst_map.containsKey(new_address)) {
                    if(!ret_call_address_map.containsKey(new_address)) {
                        // call 0x1453: 
                        // call_target: 0x1453
                        Long call_target = get_prev_inst_target(new_address);
                        if(call_target != null)
                            ret_call_address_map.put(new_address, call_target);
                    }
                    jump_to_block(block, inst, new_address, store, constraint);
                }
                else
                    jump_to_dummy(block);
            }
            else if(Helper.is_term_address(new_address)) {
                jump_to_dummy(block);
                Utils.logger.info("The symbolic execution has been successfully terminated\n");
            }
            else {
                Utils.logger.info(Long.toHexString(address) + ": the return address == {}".format(new_address));
                if(constraint != null)
                    path_reachable = _check_path_reachability(constraint);
                    if(path_reachable == null) return;
            }
        }
        else
            Utils.logger.info(Long.toHexString(address) + ": the return address == {}".format(new_address));
    }


    int trace_back(Block blk, ArrayList<String> sym_names, ArrayList<Block> trace_list) {
    	ArrayList<String> src_names = sym_names;
        Utils.logger.info("trace back");
        for(int i = 0; i < Config.MAX_TRACEBACK_COUNT; i++) {
            if(address_jt_entries_map.containsKey(blk.address)) {
            	Tuple<String, ArrayList<BitVecExpr>> jt_entries = address_jt_entries_map.get(blk.address);
            	String inst_dest = jt_entries.x;
            	ArrayList<BitVecExpr> target_addresses = jt_entries.y;
                _reconstruct_jump_targets(blk, inst_dest, target_addresses);
                return 0;
            }
            Store p_store = null;
            if(block_set.containsKey(blk.parent_id))
                p_store = block_set.get(blk.parent_id).store;
            else {
                if(blk.inst.startsWith("cmp")) {
                    p_store = blk.store;
                }
                else
                    return -1;
            }
            src_names, need_stop, boundary, still_tb = SemanticsTB.parse_sym_src(p_store, blk.store.rip, blk.inst, src_names);
            Utils.logger.info(Long.toHexString(blk.address) + ": " + blk.inst);
            // Utils.logger.info(src_names)
            // Utils.logger.info(blk.store.pp_store())
            if(need_stop && src_names.size() == 1) {
                return handle_unbounded_jump_table_w_tb(trace_list, src_names, boundary, blk);
            }
            else if(still_tb) {
                trace_list.add(blk);
                blk = block_set.get(blk.parent_id);
            }
            else {
                Utils.logger.info("\n");
                break;
            }
        }
        return -1;
    }


    int handle_unbounded_jump_table_w_tb(ArrayList<Block> trace_list, ArrayList<String> src_names, int boundary, Block blk) {
        trace_list = trace_list.remove(trace_list.size() - 1);
        String src_name = src_names.get(0);
        int src_len = Utils.get_sym_length(src_name);
        long rip = blk.store.rip;
        BitVecExpr src_sym = SymEngine.get_sym(blk.store, rip, src_name, src_len);
        Tuple<Integer, Integer> jt_idx_upperbound = CFHelper.gen_jt_idx_upperbound(trace_list, boundary);
        Integer cjmp_blk_idx = jt_idx_upperbound.x;
        Integer jt_upperbound = jt_idx_upperbound.y;
        if(jt_upperbound == null) return -1;
        Tuple<Integer, Boolean> jt_assign_check = CFHelper.check_jump_table_assign_inst(trace_list, cjmp_blk_idx);
        Integer jt_assign_blk_idx = jt_assign_check.x;
        boolean is_jt_assign_inst = jt_assign_check.y;
        if(!is_jt_assign_inst) return -1;
        Block jt_assign_blk = trace_list.get(jt_assign_blk_idx);
        Triplet<ArrayList<BitVecExpr>, String, Integer> distinct_jt_entries_info = CFHelper.get_distinct_jt_entries(jt_assign_blk, src_sym, jt_upperbound, block_set);
        ArrayList<BitVecExpr> distinct_entries = distinct_jt_entries_info.x;
        String inst_dest = distinct_jt_entries_info.y;
        int src_len = distinct_jt_entries_info.z;
        if(distinct_entries == null) return -1;
        ArrayList<Store> sym_store_list = CFHelper.reconstruct_jt_sym_stores(jt_assign_blk, distinct_entries, inst_dest, src_len);
        Tuple<String, ArrayList<BitVecExpr>> target_info = CFHelper.reconstruct_jt_target_addresses(trace_list, jt_assign_blk_idx, store_list, address_jt_entries_map);
        String dest = target_info.x;
        ArrayList<BitVecExpr> target_addresses = target_info.y;
        if(target_addresses == null) return -1;
//        Utils.logger.info(Long.toHexString(trace_list.get(-1].address) + ": jump addresses resolved using jump table .get(" + ", ".join(map(lambda x: Long.toHexString(sym_helper.int_from_sym(x)), target_addresses)) + "]")
        _reconstruct_jump_targets(trace_list.get(-1], dest, target_addresses);
        return 0;
    }


    void jump_to_next_block(Block block, long address, Store store, Constraint constraint) {
        Long new_address = CFHelper.get_next_address(address, address_next_map, address_sym_table);
        if(new_address != -1) {
            String new_inst = address_inst_map.get(new_address);
            add_new_block(block, new_address, new_inst, store, constraint);
        }
    }


    void add_fall_through_block(Block block, long address, String inst, Store store, Constraint constraint) {
        Long new_address = CFHelper.get_next_address(address, address_next_map, address_sym_table);
        if(new_address != -1)
            jump_to_block(block, inst, new_address, store, constraint);
    }


    void jump_to_block(Block block, String inst, long new_address, Store store, Constraint constraint) {
        String new_inst = address_inst_map.get(new_address);
        Tuple<Boolean, Store> block_exist = check_block_exist(block, inst, store, constraint, new_address, new_inst);
        Boolean exist = block_exist.x;
        Store new_store = block_exist.y;
        if(!exist) {
            if(new_store != null)
                _add_new_block(block, new_address, new_inst, new_store, constraint);
            else
                add_new_block(block, new_address, new_inst, store, constraint);
        }
    }
            

    void jump_to_dummy(Block block) {
        block.add_to_children_list(dummy_block.block_id);
    }
        

    void _add_block_based_on_predicate(Block parent_blk, long address, String inst, Store store, Constraint constraint, long rip, boolean pred) {
        Store new_store = new Store(store, rip);
        Semantics.cmov(new_store, rip, inst, pred);
        _add_new_block(parent_blk, address, inst, new_store, constraint);
    }

    void add_new_block(Block parent_blk, long address, String inst, Store store, Constraint constraint) {
        long rip = CFHelper.get_next_address(address, address_next_map, address_sym_table);
        if(inst.startsWith("cmov")) {
            String prefix = "cmov";
            BoolExpr res = SMTHelper.parse_predicate(store, inst, true, prefix);
            if(res == Helper.sym_true())
                _add_block_based_on_predicate(parent_blk, address, inst, store, constraint, rip, true);
            else if(res == Helper.sym_false())
                _add_block_based_on_predicate(parent_blk, address, inst, store, constraint, rip, false);
            else
                _add_block_based_on_predicate(parent_blk, address, inst, store, constraint, rip, true);
                _add_block_based_on_predicate(parent_blk, address, inst, store, constraint, rip, false);
        }
        else {
            Store new_store = new Store(store, rip, inst);
            _add_new_block(parent_blk, address, inst, new_store, constraint);
        }
    }


    void _add_new_block(Block parent_blk, long address, String inst, Store store, Constraint constraint) {
        int parent_id = (parent_blk != null) ? parent_blk.block_id : null;
        Block block = new Block(parent_id, address, inst.strip(), store, constraint);
        block_set.put(block.block_id, block);
        if(address_block_map.containsKey(address)) {
            Block blk = address_block_map.get(address);
            address_block_map.put(address, block);
            if(block_set.containsKey(blk.block_id))
            	block_set.remove(blk.block_id);
        }
        else {
            address_block_map.put(address, block);
            address_block_cnt_map.put(address, 1);
        }
        if(parent_blk != null)
            parent_blk.add_to_children_list(block.block_id);
        if(SMTHelper.is_inst_aff_flag(store, store.rip, address, inst)) {
            aff_flag_inst = (inst, store);
        }
        block_stack.add(block);
   }


    Constraint add_new_constraint(Store store, Constraint constraint, String inst, BoolExpr val, String suffix) {
        BoolExpr pred_expr = SMTHelper.parse_predicate(store, inst, val, suffix);
        Constraint new_constraint = _update_new_constraint(pred_expr, constraint);
        return new_constraint;
    }


    Constraint _update_new_constraint(BoolExpr pred_expr, Constraint constraint) {
    	Constraint new_constraint = constraint;
        if(pred_expr != null)
            new_constraint = new Constraint(constraint, pred_expr);
        return new_constraint;
    }


    void _reconstruct_jump_targets(Block blk, String inst_dest, ArrayList<BitVecExpr> target_addresses) {
    	long address = blk.address;
    	String inst = blk.inst;
    	Store store = blk.store;
    	for(BitVecExpr target_addr : target_addresses) {
            if(disasm_type == "bap" && !address_inst_map.containsKey(target_addr)) {}
            Store new_store = new Store(store, store.rip);
            SymEngine.set_sym(new_store, new_store.rip, inst_dest, target_addr);
            _add_new_block(blk, address, inst, new_store, constraint);
    	}
    }


    Model _check_path_reachability(Constraint constraint) {
        Model res = null;
        ArrayList<BoolExpr> asserts = constraint.get_asserts();
        res = Helper.check_pred_satisfiable(asserts);
        return res;
    }


    Long get_prev_inst_target(long address) {
        Long target = null;
        Long prev_address = CFHelper.get_prev_address(address, address_inst_map);
        if(prev_address != null) {
            String prev_inst = address_inst_map.get(prev_address);
            if(prev_inst.startsWith("call")) {
                Block blk = address_block_map.get(prev_address);
                BitVecExpr jmp_target = SMTHelper.get_jump_address(blk.store, address, prev_inst.split(" ", 1)[1].strip());
                if(Helper.is_bit_vec_num(jmp_target)) {
                    target = Helper.long_of_sym(jmp_target);
                }
            }
        }
        return target;
    }


    boolean explored_func_block(Store store, long new_address) {
    	Block blk = address_block_map.get(new_address);
    	int cnt = address_block_cnt_map.get(new_address);
        if(cnt > Config.MAX_VISIT_COUNT) return true;
        else if(cnt == 0) return false;
        Store prev_store = blk.store;
        String new_inst = address_inst_map.get(new_address);
        Store new_store = new Store(store, prev_store.rip);
        Semantics.parse_semantics(new_store, new_store.rip, new_inst, -1) ;
        boolean res = new_store.state_ith_eq(prev_store, address_inst_map, Lib.REG);
        return res;
    }
        

    Tuple<Boolean, Store> exist_block(Store store, Constraint constraint, long new_address, String new_inst) {
        if(address_block_map.containsKey(new_address)) {
        	Block blk = address_block_map.get(new_address);
        	int cnt = address_block_cnt_map.get(new_address);
            if(cnt == 0)
                return new Tuple<>(false, null);
            else if(cnt > Config.MAX_VISIT_COUNT) {
                Utils.logger.info("Instruction " + new_inst + " at address " + Long.toHexString(new_address) + " == visited for " + str(cnt) + " times\n")
                return new Tuple<>(true, blk.store);
            }
            Store prev_store = blk.store;
            Constraint prev_constraint = blk.constraint;
            long rip = prev_store.rip;
            Store new_store = new Store(store, rip);
            Constraint new_constraint = constraint;
//            SymHelper.merge_state(new_store, new_constraint, prev_store, prev_constraint, address_inst_map);
            new_store.merge_store(prev_store, address_inst_map);
            if(new_store.state_equal(prev_store, address_inst_map)) { 
                Utils.logger.info("Block exists: " + new_inst + " at address " + Long.toHexString(new_address) + " == visited for " + Integer.toString(cnt) + " times\n");
                return new Tuple<>(true, blk.store);
            }
            else {
            	address_block_cnt_map.put(new_address, cnt + 1);
                return new Tuple<>(false, new_store);
            }
        }
        return new Tuple<>(false, null);
    }


    HashSet<Long> reachable_addresses() {
        HashSet<Long> reachable_addresses = (HashSet<Long>) address_block_map.keySet();
        return reachable_addresses;
    }


    void pp_unreachable_instrs() {
    	HashSet<Long> reachable_addresses = (HashSet<Long>) address_block_map.keySet();
        HashSet<Long> inst_addresses = (HashSet<Long>) address_inst_map.keySet();
        Utils.logger.info("\n");
        Utils.logger.info(Config.LOG_UNREACHABLE_INDICATOR);
        for(long address : inst_addresses) {
            if(!reachable_addresses.contains(address))
                Utils.logger.info(Long.toHexString(address) + ": " + address_inst_map.get(address));
        }
        Utils.logger.info(Integer.toString(valid_address_no));
        Utils.logger.info(Integer.toString(reachable_addresses.size()));
        Utils.logger.info(Integer.toString(indirect_inst_set.size()));
    }
            

}
