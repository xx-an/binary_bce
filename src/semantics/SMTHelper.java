package semantics;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.microsoft.z3.*;

import common.Config;
import common.Helper;
import common.Lib;
import common.Tuple;
import common.Utils;
import block.Store;
import symbolic.SymEngine;
import symbolic.SymHelper;
import symbolic.SymMemory;


public class SMTHelper {
	
	final static String[] pushaOrder = new String[] {"ax", "cx", "dx", "bx", "", "bp", "si", "di"};
    final static String[] pushadOrder = new String[] {"eax", "ecx", "edx", "ebx", "", "ebp", "esi", "edi"};

	static void set_flag_val(Store store, String flag_name, BoolExpr res) {
	    store.g_FlagStore.put(flag_name, res);
	}

	static void set_mul_OF_CF_flags(Store store, BoolExpr val) {
	    reset_all_flags(store);
	    if(val.equals(Helper.SymFalse))
	        set_OF_CF_flags(store, Helper.SymTrue);
	    else if(val.equals(Helper.SymTrue))
	        set_OF_CF_flags(store, Helper.SymFalse);
	}


	static void set_OF_flag(Store store, String dest, String src, BitVecExpr res, int block_id, String op) {
		Tuple<BitVecExpr, BitVecExpr> dest_src_sym = SymEngine.get_dest_src_sym(store, dest, src, block_id);
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
	    	store.set_flag_val("OF", Helper.SymFalse);
	}


	static void set_CF_flag(Store store, String dest, String src, int block_id, String op) {
	    if(op.equals("+"))
	        _set_add_CF_flag(store, dest, src, block_id);
	    else if(op.equals("-"))
	        _set_sub_CF_flag(store, dest, src, block_id);
	    else
	    	store.set_flag_val("CF", Helper.SymFalse);
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
	        

	static void _set_sub_CF_flag(Store store, String dest, String src, int block_id) {
		Tuple<BitVecExpr, BitVecExpr> dest_src_sym = SymEngine.get_dest_src_sym(store, dest, src, block_id);
		BitVecExpr dest_sym = dest_src_sym.x;
		BitVecExpr src_sym = dest_src_sym.y;
	    BoolExpr res = Helper.is_less(dest_sym, src_sym);
	    store.set_flag_val("CF", res);
	}


	static void _set_add_CF_flag(Store store, String dest, String src, int block_id) {
		Tuple<BitVecExpr, BitVecExpr> dest_src_sym = SymEngine.get_dest_src_sym(store, dest, src, block_id);
		BitVecExpr dest_sym = dest_src_sym.x;
		BitVecExpr src_sym = dest_src_sym.y;
		int dest_len = Utils.getSymLength(dest, Config.MEM_ADDR_SIZE);
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
	    set_OF_CF_flags(store, Helper.SymFalse);
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
		Pattern pat = Pattern.compile("[<!=>]+");
	    Matcher m = pat.matcher(cond);
	    if(!m.find()) return null;
		String logic_op = m.group();
	    String[] cond_split = cond.split(logic_op);
	    BoolExpr lhs = store.get_flag_val(cond_split[0].strip());
	    String rhs_str = cond_split[1].strip();
	    BoolExpr rhs = (Utils.imm_pat.matcher(rhs_str).matches()) ? Helper.gen_bool_sym(Utils.imm_str_to_int(rhs_str)) : store.get_flag_val(rhs_str);    
	    if(lhs == null || rhs == null)
	        return null;
	    return Helper.LOGIC_OP_FUNC_MAP_BOOLEXPR.get(logic_op).apply(new Tuple<BoolExpr, BoolExpr>(lhs, rhs));
	}
	
	
	// expr: SF<>OF && OF==0
	static BoolExpr parse_and_cond(Store store, String expr) {
		String[] andConds = expr.split(" && ");
		BoolExpr res = parse_condition(store, andConds[0]);
    	if(res == null) return null;
    	for(int idx = 1; idx < andConds.length; idx++) {
    		String ac = andConds[idx];
    		BoolExpr curr = parse_condition(store, ac);
    		if(curr == null) return null;
    		res = Helper.bv_and(res, curr);
    	}
    	return res;
	}


	// expr: ZF==1 || SF<>OF && OF==0
	static BoolExpr parse_pred_expr(Store store, String expr) {
//		System.out.println(expr);
	    String[] orConds = expr.split(" \\|\\| ");
	    BoolExpr res = parse_and_cond(store, orConds[0]);
    	if(res == null) return null;
    	for(int idx = 1; idx < orConds.length; idx++) {
    		String oc = orConds[idx];
    		BoolExpr curr = parse_and_cond(store, oc);
    		if(curr == null) return null;
    		res = Helper.bv_or(res, curr);
    	}
    	return res;
	}


	public static BoolExpr parse_predicate(Store store, String inst, boolean val, String prefix) {
	    String cond = inst.split(" ", 2)[0].split(prefix, 2)[1];
	    String expr = Lib.FLAG_CONDITIONS.get(cond);
	    BoolExpr res = parse_pred_expr(store, expr);
	    if(res == null)
	        return null;
	    else if(!val)
	    	res = Helper.bv_not(res);
//	    Utils.logger.info(expr);
//	    Utils.logger.info(res.toString());
	    return res;
	}


	boolean is_inst_aff_flag(Store store, String inst) {
	    String[] inst_split = inst.strip().split(" ", 2);
	    String inst_name = inst_split[0];
	    if(Lib.INSTS_AFF_FLAGS_WO_CMP_TEST.contains(inst_name))
	        return true;
	    else if(inst_name.equals("cmp") ||  inst_name.equals("test")) {
	        ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        _add_aux_memory(store, inst_args);
	    }
	    return false;
	}


	void add_aux_memory(Store store, String inst) {
	    String[] inst_split = inst.strip().split(" ", 2);
	    String inst_name = inst_split[0];
	    if(Lib.INSTS_AFF_FLAGS_WO_CMP_TEST.contains(inst_name)) {
	    	ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        _add_aux_memory(store, inst_args);
	    }
	}


	void _add_aux_memory(Store store, ArrayList<String> inst_args) {
	    for(String arg : inst_args) {
	        if(arg.endsWith("]")) {
	            BitVecExpr address = SymEngine.get_effective_address(store, arg);
	            if(store.containsKey(address) && !store.contains_aux_mem(address)) {
	            	int block_id = store.get_block_id(address);
	                BitVecExpr sym_arg = SymEngine.get_sym(store, address.toString(), block_id);
	                if(Helper.is_bit_vec_num(sym_arg)) {
	                	store.add_aux_mem(address);
	                }
	            }
	            break;
	        }
	    }
	}


	public static BitVecExpr get_jump_address(Store store, String operand, HashMap<Long, String> extFuncInfo) {
	    int length = Utils.getSymLength(operand, Config.MEM_ADDR_SIZE);
	    if(operand.endsWith("]")) {
	        BitVecExpr address = SymMemory.get_effective_address(store, operand, Config.MEM_ADDR_SIZE);
	        if(Helper.is_bit_vec_num(address)) {
	        	long intAddr = Helper.long_of_sym(address);
	        	if(extFuncInfo.containsKey(intAddr)) return address;
	        }
	    }
	    BitVecExpr result = SymEngine.get_sym(store, operand, Utils.INIT_BLOCK_NO, length);
	    return result;
	}
	
	
	public static Long get_long_jump_address(Store store, String operand) {
	    Long res = null;
	    int length = Utils.getSymLength(operand, Config.MEM_ADDR_SIZE);
	    BitVecExpr result = SymEngine.get_sym(store, operand, Utils.INIT_BLOCK_NO, length);
	    if(Helper.is_bit_vec_num(result)) {
	    	res = Helper.long_of_sym(result);
	    }
	    return res;
	}


	// line: "rax + rbx * 1 + 0"
	// line: "rbp - 0x14"
	// line: "rax"
	public static Tuple<ArrayList<String>, Boolean> get_bottom_source(String line, Store store, HashMap<String, Integer> mem_len_map) {
	    String[] line_split = line.split("(\\W+)");
	    ArrayList<String> res = new ArrayList<String>();
	    boolean is_reg_bottom = false;
	    for(String lsi : line_split) {
	        String ls = lsi.strip();
	        if(Lib.REG_NAMES.contains(ls)) {
	            BitVecExpr val = SymEngine.get_sym(store, ls, Utils.INIT_BLOCK_NO, Config.MEM_ADDR_SIZE);
	            if(!Helper.is_bit_vec_num(val)) {
	            	String root_reg = SymHelper.getRootReg(ls);
	                res.add(root_reg);
	                is_reg_bottom = true;
	            }
	        }
	    }
	    if(!is_reg_bottom) {
	        BitVecExpr addr = SymEngine.get_effective_address(store, line);
	        res.add(addr.toString());
	        int length = Utils.getSymLength(line, Config.MEM_ADDR_SIZE);
	        mem_len_map.put(addr.toString(), length);
	    }
	    return new Tuple<ArrayList<String>, Boolean>(res, is_reg_bottom);
	}

	// line: "rax + rbx * 1 + 0"
	// line: "rbp - 0x14"
	// line: "rax"
	public static ArrayList<String> getMemRegSrcs(String line) {
	    ArrayList<String> res = new ArrayList<String>();
	    String[] lineSplit = line.split("(\\W+)");
	    for(String lsi : lineSplit) {
	        String ls = lsi.strip();
	        if(Lib.REG_NAMES.contains(ls))
	            res.add(ls);
	    }
	    return res;
	}


	static boolean srcIsSymbolic(Store store, String src, ArrayList<String> syms) {
	    boolean res = false;
	    if(Lib.REG_INFO_DICT.containsKey(src)) {
	    	String rootReg = SymHelper.getRootReg(src);
	    	res = syms.contains(rootReg);
	    }
	    else if(Lib.REG_NAMES.contains(src))
	        res = syms.contains(src);
	    else if(src.contains(":")) {
	        String[] src_split = src.split(":");
	        res = srcIsSymbolic(store, src_split[0], syms) || srcIsSymbolic(store, src_split[1], syms);
	    }
	    else if(src.endsWith("]")) {
	        BitVecExpr addr = SymEngine.get_effective_address(store, src);
	        res = syms.contains(addr.toString());
	    }
	    return res;
	}


	static boolean isSymAddrAtStack(String sym) {
	    boolean res = false;
	    if(Utils.imm_start_pat.matcher(sym).find()) {
	        long addr = Long.decode(sym);
	        if(addr > Config.MAX_HEAP_ADDR)
	            res = true;
	    }
	    return res;
	}


	static boolean check_cmp_dest_is_sym(Store store, String dest, ArrayList<String> sym_names, HashMap<String, Integer> mem_len_map) {
		boolean res = false;
	    if(sym_names.size() == 1) {
	    	if(Lib.REG_NAMES.contains(dest))
	    		res = srcIsSymbolic(store, dest, sym_names);
	        else if(dest.endsWith("]")) {
	        	Tuple<ArrayList<String>, Boolean> tmp = get_bottom_source(dest, store, mem_len_map);
	        	ArrayList<String> newSrcs = tmp.x;
	            boolean is_reg_bottom = tmp.y;
	            if(is_reg_bottom) {
	                if(newSrcs.size() == 1)
	                    res = newSrcs.get(0).equals(sym_names.get(0));
	            }
	            else {
	                BitVecExpr addr = SymEngine.get_effective_address(store, dest);
	                res = addr.toString().equals(sym_names.get(0));
	            }
	        }
	    }
	    return res;
	}


	static void rmRegFromSymSrcs(String reg, ArrayList<String> src_names) {
	    String rootReg = SymHelper.getRootReg(reg);
	    if(src_names.contains(rootReg))
	    	src_names.remove(rootReg);
	}


	static void addNewRegSrc(ArrayList<String> sym_names, String dest, String src) {
	    rmRegFromSymSrcs(dest, sym_names);
	    String rootReg = SymHelper.getRootReg(src);
	    if(!sym_names.contains(rootReg))
	    	sym_names.add(rootReg);
	}


	static ArrayList<String> addRegSrcToSyms(Store store, ArrayList<String> symNames, String src) {
	    BitVecExpr sym_src = SymEngine.get_register_sym(store, src);
	    if(!Helper.is_bit_vec_num(sym_src)) {
	    	String root_reg = SymHelper.getRootReg(src);
	    	if(!symNames.contains(root_reg))
	    		symNames.add(root_reg);
	    }
	    return symNames;
	}


	public static BitVecExpr sym_bin_op_na_flags(Store store, String op, String dest, String src, int block_id) {
		BitVecExpr res = SymEngine.sym_bin_op(store, op, dest, src, block_id);
	    SymEngine.set_sym(store, dest, res, block_id);
	    return res;
	}


	public static void push_val(Store store, BitVecExpr sym_val, int block_id) {
		int operand_size = sym_val.getSortSize();
		BitVecExpr symSP = sym_bin_op_na_flags(store, "-", Config.SP_NAME, String.valueOf(operand_size/8), block_id);
		SymEngine.set_mem_sym(store, symSP, sym_val, block_id);
	}

}
