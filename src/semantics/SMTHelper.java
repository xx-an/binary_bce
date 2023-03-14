package semantics;

import java.util.ArrayList;
import java.util.HashMap;

import com.microsoft.z3.*;

import common.Config;
import common.Helper;
import common.Lib;
import common.Tuple;
import common.Utils;
import block.Store;
import symbolic.SymEngine;
import symbolic.SymHelper;


public class SMTHelper {

	static void set_flag_val(Store store, String flag_name, BoolExpr res) {
	    store.g_FlagStore.put(flag_name, res);
	}

	static void set_mul_OF_CF_flags(Store store, BoolExpr val) {
	    reset_all_flags(store);
	    if(val == Helper.sym_false())
	        set_OF_CF_flags(store, Helper.sym_true());
	    else if(val == Helper.sym_true())
	        set_OF_CF_flags(store, Helper.sym_false());
	}


	static void set_OF_flag(Store store, long rip, String dest, String src, BitVecExpr res, int block_id, String op) {
		Tuple<BitVecExpr, BitVecExpr> dest_src_sym = SymEngine.get_dest_src_sym(store, rip, dest, src, block_id);
		BitVecExpr dest_sym = dest_src_sym.x;
		BitVecExpr src_sym = dest_src_sym.y;
	    if(op.equals("+")) {
	    	BoolExpr case1 = Helper.bv_and(Helper.is_neg(dest_sym), Helper.is_neg(src_sym), Helper.is_pos(res));
	    	BoolExpr case2 = Helper.bv_and(Helper.is_pos(dest_sym), Helper.is_pos(src_sym), Helper.is_neg(res));
	    	set_flag_val(store, "OF", Helper.bv_or(case1, case2));
	    }
	    else if(op.equals("-")) {
	    	BoolExpr case1 = Helper.bv_and(Helper.is_neg(dest_sym), Helper.is_pos(src_sym), Helper.is_pos(res));
	    	BoolExpr case2 = Helper.bv_and(Helper.is_pos(dest_sym), Helper.is_neg(src_sym), Helper.is_neg(res));
	        set_flag_val(store, "OF", Helper.bv_or(case1, case2));
	    }
	    else
	    	store.set_flag_val("OF", Helper.sym_false());
	}


	static void set_CF_flag(Store store, long rip, String dest, String src, int block_id, String op) {
	    if(op.equals("+"))
	        _set_add_CF_flag(store, rip, dest, src, block_id);
	    else if(op.equals("-"))
	        _set_sub_CF_flag(store, rip, dest, src, block_id);
	    else
	    	store.set_flag_val("CF", Helper.sym_false());
	}


	static void set_flag_direct(Store store, String flag_name, BoolExpr value) {
    	store.set_flag_val(flag_name, value);
    }


	static BoolExpr get_flag_direct(Store store, String flag_name) {
		return store.get_flag_val(flag_name);
	}
	    

	void pp_flags(Store store) {
		for(String flag : Lib.RFlags)
			Utils.logger.info(flag + ": " + store.get_flag_val(flag).toString());
	}
	        

	static void _set_sub_CF_flag(Store store, long rip, String dest, String src, int block_id) {
		Tuple<BitVecExpr, BitVecExpr> dest_src_sym = SymEngine.get_dest_src_sym(store, rip, dest, src, block_id);
		BitVecExpr dest_sym = dest_src_sym.x;
		BitVecExpr src_sym = dest_src_sym.y;
	    BoolExpr res = Helper.is_less(dest_sym, src_sym);
	    store.set_flag_val("CF", res);
	}


	static void _set_add_CF_flag(Store store, long rip, String dest, String src, int block_id) {
		Tuple<BitVecExpr, BitVecExpr> dest_src_sym = SymEngine.get_dest_src_sym(store, rip, dest, src, block_id);
		BitVecExpr dest_sym = dest_src_sym.x;
		BitVecExpr src_sym = dest_src_sym.y;
		int dest_len = Utils.get_sym_length(dest, Config.MEM_ADDR_SIZE);
	    BitVecExpr res = Helper.bv_add(Helper.zero_ext(1, src_sym), Helper.zero_ext(1, dest_sym));
	    BoolExpr msb = Helper.most_significant_bit(res, dest_len + 1);
	    store.set_flag_val("CF", msb);
	}


	static void modify_status_flags(Store store, BitVecExpr sym, int dest_len) {
		store.set_flag_val("ZF", Helper.is_equal(sym, 0));
		store.set_flag_val("SF", Helper.most_significant_bit(sym, dest_len));
	}


	static void set_OF_CF_flags(Store store, BoolExpr val) {
		store.set_flag_val("CF", val);
		store.set_flag_val("OF", val);
	}


	static void set_test_OF_CF_flags(Store store) {
	    set_OF_CF_flags(store, Helper.sym_false());
	}


	static void reset_all_flags(Store store) {
	    for(String flag : Lib.RFlags)
	    	store.set_flag_val(flag, null);
	}


	static void reset_all_flags_except_one(Store store, String flag_name) {
		for(String flag : Lib.RFlags) {
			if(flag != flag_name)
				store.set_flag_val(flag, null);
		}
	}

	static BoolExpr parse_condition(Store store, String cond) {
	    String logic_op = Utils.search("[<!=>]+", cond);
	    String[] cond_split = cond.split(logic_op);
	    BoolExpr lhs = store.get_flag_val(cond_split[0].strip());
	    String rhs_str = cond_split[1].strip();
	    BoolExpr rhs = (Utils.imm_pat.matcher(rhs_str).matches()) ? Helper.gen_bool_sym(Utils.imm_str_to_int(rhs_str)) : store.get_flag_val(rhs_str);    
	    if(lhs == null || rhs == null)
	        return null;
	    return Helper.LOGIC_OP_FUNC_MAP_BOOLEXPR.get(logic_op).apply(new Tuple<BoolExpr, BoolExpr>(lhs, rhs));
	}


	// expr: ZF==1 || SF<>OF
	static BoolExpr parse_pred_expr(Store store, String expr) {
		BoolExpr result = Helper.sym_false();
	    String[] or_conds = expr.split(" || ");
	    for(String s : or_conds) {
	    	String[] and_conds = s.split(" && ");
	    	BoolExpr res = Helper.sym_true();
	    	for(String si : and_conds) {
	    		BoolExpr curr = parse_condition(store, si);
	    		res = Helper.bv_and(res, curr);
	    	}
	    	result = Helper.bv_or(result, res);
	    }
	    return result;
	}


	public static BoolExpr parse_predicate(Store store, String inst, boolean val, String prefix) {
	    String cond = inst.split(" ", 2)[0].split(prefix, 2)[1];
	    String expr = Lib.FLAG_CONDITIONS.get(cond);
	    BoolExpr res = parse_pred_expr(store, expr);
	    if(res == null)
	        return null;
	    else if(!val)
	    	res = Helper.bv_not(res);
	    return res;
	}
	
	
	public static BoolExpr parse_predicate(Store store, String inst, BoolExpr val, String prefix) {
	    String cond = inst.split(" ", 2)[0].split(prefix, 2)[1];
	    String expr = Lib.FLAG_CONDITIONS.get(cond);
	    BoolExpr res = parse_pred_expr(store, expr);
	    if(res == null)
	        return null;
	    else if(val == Helper.sym_false())
	    	res = Helper.bv_not(res);
	    return res;
	}


	Long top_stack(Store store, long rip) {
		Long result = null;
		String spName = Config.ADDR_SIZE_SP_MAP.get(Config.MEM_ADDR_SIZE);
	    BitVecExpr symSP = SymEngine.get_sym(store, rip, spName, Utils.INIT_BLOCK_NO);
	    BitVecExpr res = SymEngine.get_mem_sym(store, symSP);
	    if(res != null && Helper.is_bit_vec_num(res))
	    	result = Helper.long_of_sym(res);
	    return result;
	}


	boolean is_inst_aff_flag(Store store, long rip, String inst) {
	    String[] inst_split = inst.strip().split(" ", 2);
	    String inst_name = inst_split[0];
	    if(Lib.INSTS_AFF_FLAGS_WO_CMP_TEST.contains(inst_name))
	        return true;
	    else if(inst_name.equals("cmp") ||  inst_name.equals("test")) {
	        ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        _add_aux_memory(store, rip, inst_args);
	    }
	    return false;
	}


	void add_aux_memory(Store store, long rip, String inst) {
	    String[] inst_split = inst.strip().split(" ", 2);
	    String inst_name = inst_split[0];
	    if(Lib.INSTS_AFF_FLAGS_WO_CMP_TEST.contains(inst_name)) {
	    	ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        _add_aux_memory(store, rip, inst_args);
	    }
	}


	void _add_aux_memory(Store store, long rip, ArrayList<String> inst_args) {
	    for(String arg : inst_args) {
	        if(arg.endsWith("]")) {
	            BitVecExpr address = SymEngine.get_effective_address(store, rip, arg);
	            if(store.containsKey(address) && !store.contains_aux_mem(address)) {
	            	int block_id = store.get_block_id(address);
	                BitVecExpr sym_arg = SymEngine.get_sym(store, rip, address.toString(), block_id);
	                if(Helper.is_bit_vec_num(sym_arg)) {
	                	store.add_aux_mem(address);
	                }
	            }
	            break;
	        }
	    }
	}


	public static BitVecExpr get_jump_address(Store store, long rip, String operand) {
//	    Long res = null;
	    int length = Utils.get_sym_length(operand, Config.MEM_ADDR_SIZE);
	    BitVecExpr result = SymEngine.get_sym(store, rip, operand, Utils.INIT_BLOCK_NO, length);
//	    if(Helper.is_bit_vec_num(result)) {
//	    	res = Helper.long_of_sym(result);
//	    }
	    return result;
	}
	
	
	public static Long get_long_jump_address(Store store, long rip, String operand) {
	    Long res = null;
	    int length = Utils.get_sym_length(operand, Config.MEM_ADDR_SIZE);
	    BitVecExpr result = SymEngine.get_sym(store, rip, operand, Utils.INIT_BLOCK_NO, length);
	    if(Helper.is_bit_vec_num(result)) {
	    	res = Helper.long_of_sym(result);
	    }
	    return res;
	}


	// line: "rax + rbx * 1 + 0"
	// line: "rbp - 0x14"
	// line: "rax"
	public static Tuple<ArrayList<String>, Boolean> get_bottom_source(String line, Store store, long rip, HashMap<String, Integer> mem_len_map) {
	    String[] line_split = line.split("(\\W+)");
	    ArrayList<String> res = new ArrayList<String>();
	    boolean is_reg_bottom = false;
	    for(String lsi : line_split) {
	        String ls = lsi.strip();
	        if(Lib.REG_NAMES.contains(ls)) {
	            BitVecExpr val = SymEngine.get_sym(store, rip, ls, Utils.INIT_BLOCK_NO, Config.MEM_ADDR_SIZE);
	            if(!Helper.is_bit_vec_num(val)) {
	            	String root_reg = SymHelper.get_root_reg(ls);
	                res.add(root_reg);
	                is_reg_bottom = true;
	            }
	        }
	    }
	    if(!is_reg_bottom) {
	        BitVecExpr addr = SymEngine.get_effective_address(store, rip, line);
	        res.add(addr.toString());
	        int length = Utils.get_sym_length(line, Config.MEM_ADDR_SIZE);
	        mem_len_map.put(addr.toString(), length);
	    }
	    return new Tuple<ArrayList<String>, Boolean>(res, is_reg_bottom);
	}

	// line: "rax + rbx * 1 + 0"
	// line: "rbp - 0x14"
	// line: "rax"
	public static ArrayList<String> get_mem_reg_source(String line) {
	    String[] line_split = line.split("(\\W+)");
	    ArrayList<String> res = new ArrayList<String>();
	    for(String lsi : line_split) {
	        String ls = lsi.strip();
	        if(Lib.REG_NAMES.contains(ls))
	            res.add(ls);
	    }
	    return res;
	}


	static boolean check_source_is_sym(Store store, long rip, String src, ArrayList<String> syms) {
	    boolean res = false;
	    if(Lib.REG_INFO_DICT.containsKey(src)) {
	    	String root_src = SymHelper.get_root_reg(src);
	    	res = syms.contains(root_src);
	    }
	    else if(Lib.REG_NAMES.contains(src))
	        res = syms.contains(src);
	    else if(src.contains(":")) {
	        String[] src_split = src.split(":");
	        res = check_source_is_sym(store, rip, src_split[0], syms) || check_source_is_sym(store, rip, src_split[1], syms);
	    }
	    else if(src.endsWith("]")) {
	        BitVecExpr addr = SymEngine.get_effective_address(store, rip, src);
	        res = syms.contains(addr.toString());
	    }
	    return res;
	}


	static boolean check_sym_is_stack_addr(String sym) {
	    boolean res = false;
	    if(sym.matches("[1-9][0-9]*")) {
	        long addr = Long.decode(sym);
	        if(addr > Config.MAX_HEAP_ADDR)
	            res = true;
	    }
	    return res;
	}


	static boolean check_cmp_dest_is_sym(Store store, long rip, String dest, ArrayList<String> sym_names, HashMap<String, Integer> mem_len_map) {
		boolean res = false;
	    if(sym_names.size() == 1) {
	    	if(Lib.REG_NAMES.contains(dest))
	    		res = check_source_is_sym(store, rip, dest, sym_names);
	        else if(dest.endsWith("]")) {
	        	Tuple<ArrayList<String>, Boolean> tmp = get_bottom_source(dest, store, rip, mem_len_map);
	        	ArrayList<String> new_srcs = tmp.x;
	            boolean is_reg_bottom = tmp.y;
	            if(is_reg_bottom) {
	                if(new_srcs.size() == 1)
	                    res = new_srcs.get(0) == sym_names.get(0);
	            }
	            else {
	                BitVecExpr addr = SymEngine.get_effective_address(store, rip, dest);
	                res = addr.toString() == sym_names.get(0);
	            }
	        }
	    }
	    return res;
	}


	static void remove_reg_from_sym_srcs(String reg, ArrayList<String> src_names) {
	    String src_reg = SymHelper.get_root_reg(reg);
	    if(src_names.contains(src_reg))
	    	src_names.remove(src_reg);
	}


	static void add_new_reg_src(ArrayList<String> sym_names, String dest, String src) {
	    remove_reg_from_sym_srcs(dest, sym_names);
	    String root_reg = SymHelper.get_root_reg(src);
	    if(!sym_names.contains(root_reg))
	    	sym_names.add(root_reg);
	}


	static void add_src_to_syms(Store store, ArrayList<String> sym_names, String src) {
	    BitVecExpr sym_src = SymEngine.get_register_sym(store, src);
	    if(!Helper.is_bit_vec_num(sym_src)) {
	    	String root_reg = SymHelper.get_root_reg(src);
	    	if(!sym_names.contains(root_reg))
	    		sym_names.add(root_reg);
	    }
	}


	public static BitVecExpr sym_bin_op_na_flags(Store store, long rip, String op, String dest, String src, int block_id) {
	    BitVecExpr res = SymEngine.sym_bin_op(store, rip, op, dest, src, block_id);
	    SymEngine.set_sym(store, rip, dest, res, block_id);
	    return res;
	}


	public static void push_val(Store store, long rip, BitVecExpr sym_val, int block_id) {
		int operand_size = sym_val.getSortSize();
		BitVecExpr sym_rsp = sym_bin_op_na_flags(store, rip, "-", Config.ADDR_SIZE_SP_MAP.get(Config.MEM_ADDR_SIZE), String.valueOf(operand_size/8), block_id);
		SymEngine.set_mem_sym(store, sym_rsp, sym_val, block_id);
	}
	
	public static BitVecExpr get_sym_rsp(Store store, long rip) {
		BitVecExpr sym_rsp = SymEngine.get_sym(store, rip, Config.ADDR_SIZE_SP_MAP.get(Config.MEM_ADDR_SIZE), Config.MEM_ADDR_SIZE);
		return sym_rsp;
	}

}
