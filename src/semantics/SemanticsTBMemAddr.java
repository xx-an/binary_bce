package semantics;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.function.Function;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;

import block.Store;
import common.Config;
import common.Helper;
import common.Lib;
import common.Triplet;
import common.Tuple;
import common.Utils;
import symbolic.SymEngine;

public class SemanticsTBMemAddr {

	static long rip = 0;
	static boolean func_call_point = false;
	static boolean halt_point = false;
	static boolean concrete_val = false;
	static HashMap<BitVecExpr, ArrayList<String>> address_sym_table = null;
	static HashMap<Long, String> address_inst_map = null;
	static HashMap<String, Integer> mem_len_map = new HashMap<String, Integer>();
	static HashMap<String, Function<Triplet<Store, ArrayList<String>, ArrayList<String>>, ArrayList<String>>> INSTRUCTION_SEMANTICS_MAP;
	
	
	public SemanticsTBMemAddr() {
		INSTRUCTION_SEMANTICS_MAP = new HashMap<String, Function<Triplet<Store, ArrayList<String>, ArrayList<String>>, ArrayList<String>>>();
		INSTRUCTION_SEMANTICS_MAP.put("mov", arg -> mov_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("lea", arg -> lea_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("push", arg -> push_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("pop", arg -> pop_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("add", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("sub", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("xor", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("and", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("or", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("sar", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("shr", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("sal", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("shl", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("xchg", arg -> xchg_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("imul", arg -> imul_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("mul", arg -> mul_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("idiv", arg -> div_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("div", arg -> div_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("cmpxchg", arg -> cmpxchg_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("movzx", arg -> mov_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("movsx", arg -> mov_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("movsxd", arg -> mov_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("adc", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("sbb", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("cdqe", arg -> cdqe(arg.x, arg.y, arg.z));
	}
	
	public ArrayList<String> add_src_to_syms(ArrayList<String> sym_names, String src) {
		ArrayList<String> src_names = sym_names;
	    src_names.add(SMTHelper.get_root_reg(src));
	    return src_names;
	}

	static Boolean addr_points_to_external_lib(BitVecExpr addr) {
	    Boolean res = false;
	    if(address_sym_table.containsKey(addr)) {
	    	if(Helper.is_bit_vec_num(addr)) {
	    		Long int_addr = Helper.long_of_sym(addr);
	    		if(!address_inst_map.containsKey(int_addr))
	    			res = true;
	    	}
	    }
	    return res;
	}

	ArrayList<String> sym_bin_on_src(Store store, ArrayList<String> sym_names, String src) {
		ArrayList<String> src_names = sym_names;
	    if(!Utils.imm_start_pat.matcher(src).matches()) {
	        if(src.contains(":")) {
	        	String[] src_split = src.split(":");
	            src_names = add_src_to_syms(sym_names, src_split[0]);
	            src_names = add_src_to_syms(src_names, src_split[1]);
	        }
	        else if(src.endsWith("]")) {
	        	Tuple<ArrayList<String>, Boolean> bottom_source = SMTHelper.get_bottom_source(src, store, rip, mem_len_map);
	        	ArrayList<String> new_srcs = bottom_source.x;
	        	boolean is_reg_bottom = bottom_source.y;
	            if(is_reg_bottom) {
	            	src_names.addAll(new_srcs);
	            }
	            else {
	            	BitVecExpr addr = SymEngine.get_effective_address(store, rip, src);
	                if(addr_points_to_external_lib(addr)) {
	                    halt_point = true;
	                }
	                src_names.add(addr.toString());
	            }
	        }
	        else {
	            src_names.add(SMTHelper.get_root_reg(src));
	        }
	    }
	    return src_names;
	}

	ArrayList<String> sym_bin_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src1 = arg.get(1);
		String src2 = null;
		if(arg.size() > 2)
			src2 = arg.get(2);
		return sym_bin_oprt(store, sym_names, dest, src1, src2);
	}

	ArrayList<String> sym_bin_oprt(Store store, ArrayList<String> sym_names, String dest, String src1, String src2) {
		ArrayList<String> src_names = sym_names;
		if(src2 == null)
			src2 = dest;
	    src_names = sym_bin_on_src(store, sym_names, src1);
	    src_names = sym_bin_on_src(store, src_names, src2);
	    return src_names;
	}
	    		

	ArrayList<String> mov_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return mov(store, sym_names, dest, src);
	}

	static ArrayList<String> mov(Store store, ArrayList<String> sym_names, String dest, String src) {
		ArrayList<String> src_names = sym_names;
	    if(!Utils.imm_start_pat.matcher(src).matches()) {
	        if(Lib.REG_NAMES.contains(src)) {
	        	String dest_reg = null;
	            if(dest.endsWith("]")) {
	                BitVecExpr addr = SymEngine.get_effective_address(store, rip, dest);
	                dest_reg = addr.toString();
	            }
	            else {
	                dest_reg = SMTHelper.get_root_reg(dest);
	            }
	            if(src_names.contains(dest_reg)) {
	                src_names.remove(dest_reg);
	            }
	            src_names.add(SMTHelper.get_root_reg(src));
	        }
	        else if(src.endsWith("]")) {
	            SMTHelper.remove_reg_from_sym_srcs(dest, src_names);
	            Tuple<ArrayList<String>, Boolean> bottom_source = SMTHelper.get_bottom_source(src, store, rip, mem_len_map);
	        	ArrayList<String> new_srcs = bottom_source.x;
	        	boolean is_reg_bottom = bottom_source.y;
	            if(is_reg_bottom) {
	                src_names.addAll(new_srcs);
	            }
	            else {
	                BitVecExpr addr = SymEngine.get_effective_address(store, rip, src);
	                if(addr_points_to_external_lib(addr)) {
	                    halt_point = true;
	                }
	                src_names.add(addr.toString());
	            }
	        }
	    }
	    else {
	        concrete_val = true;
	    }
	    return src_names;
	}

	ArrayList<String> lea_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return lea(store, sym_names, dest, src);
	}

	ArrayList<String> lea(Store store, ArrayList<String> sym_names, String dest, String src) {
	    ArrayList<String> src_names = sym_names;
	    if(src_names.contains(dest)) {
	        src_names.remove(dest);
	        Tuple<ArrayList<String>, Boolean> bottom_source = SMTHelper.get_bottom_source(src, store, rip, mem_len_map);
        	ArrayList<String> new_srcs = bottom_source.x;
        	src_names.addAll(new_srcs);
	    }
	    return src_names;
	}

	ArrayList<String> push_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String src = arg.get(0);
		return push(store, sym_names, src);
	}

	ArrayList<String> push(Store store, ArrayList<String> sym_names, String src) {
		ArrayList<String> src_names = sym_names;
		BitVecExpr sym_rsp = SMTHelper.get_sym_rsp(store, rip);
	    String prev_rsp = Helper.bv_sub(sym_rsp, Config.MEM_ADDR_SIZE / 8).toString();
	    if(sym_names.contains(prev_rsp)) {
	        src_names.remove(prev_rsp);
	    }
	    src_names.add(src);
	    return src_names;
	}
	
	ArrayList<String> pop_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		return pop(store, sym_names, dest);
	}


	ArrayList<String> pop(Store store, ArrayList<String> sym_names, String dest) {
		BitVecExpr sym_rsp = SMTHelper.get_sym_rsp(store, rip);
//	    sym_rsp = str(SymEngine.get_sym(store, rip, "rsp", Utils.TB_DEFAULT_BLOCK_NO))
		ArrayList<String> src_names = sym_names;
	    SMTHelper.remove_reg_from_sym_srcs(dest, src_names);
	    src_names.add(sym_rsp.toString());
	    return src_names;
	}
	
	ArrayList<String> xchg_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return xchg(store, sym_names, dest, src);
	}


	ArrayList<String> xchg(Store store, ArrayList<String> sym_names, String dest, String src) {
		ArrayList<String> src_names = sym_names;
	    // if(check_source_is_sym(store, rip, dest, sym_names) {
	    SMTHelper.add_new_reg_src(src_names, dest, src);
	    return src_names;
	}
	
	ArrayList<String> mul_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		return mul(store, sym_names, dest);
	}

	ArrayList<String> mul(Store store, ArrayList<String> sym_names, String src) {
		ArrayList<String> src_names = sym_names;
	    int bits_len = Utils.get_sym_length(src);
	    Triplet<String,String,String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String a_reg = reg_info.x;
	    String dest = reg_info.z;
	    src_names = sym_bin_oprt(store, sym_names, dest, a_reg, src);
	    return src_names;
	}
	
	ArrayList<String> imul_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src1 = null;
		String src2 = null;
		if(arg.size() > 1)
			src1 = arg.get(1);
		if(arg.size() > 2)
			src2 = arg.get(2);
		return imul(store, sym_names, dest, src1, src2);
	}


	ArrayList<String> imul(Store store, ArrayList<String> sym_names, String dest, String src1, String src2) {
		ArrayList<String> src_names = sym_names;
	    if(src1 != null) {
	        if(src2 == null) {
	            src_names = sym_bin_oprt(store, sym_names, dest, src1, null);
	        }
	        else {
	            src_names = sym_bin_oprt(store, sym_names, src1, src2, null);
	        }
	    }
	    else {
	        src_names = mul(store, sym_names, dest);
	    }
	    return src_names;
	}
	
	ArrayList<String> div_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String src = arg.get(0);
		return div(store, sym_names, src);
	}


	ArrayList<String> div(Store store, ArrayList<String> sym_names, String src) {
	    int bits_len = Utils.get_sym_length(src);
	    Triplet<String,String,String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String qreg = reg_info.x;
	    String rreg = reg_info.y;
	    String dest = reg_info.z;
	    ArrayList<String> src_names = sym_bin_oprt(store, sym_names, qreg + ":" +rreg, dest, src);
	    return src_names;
	}


	ArrayList<String> cdqe(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
	    return sym_names;
	}

	
	ArrayList<String> cmpxchg_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return cmpxchg(store, sym_names, dest, src);
	}

	ArrayList<String> cmpxchg(Store store, ArrayList<String> sym_names, String dest, String src) {
		ArrayList<String> src_names = sym_names;
	    int bits_len = Utils.get_sym_length(dest);
	    Triplet<String,String,String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String a_reg = reg_info.x;
	    BitVecExpr sym_lhs = SymEngine.get_sym(store, rip, a_reg, Utils.TB_DEFAULT_BLOCK_NO, bits_len);
	    BitVecExpr sym_rhs = SymEngine.get_sym(store, rip, dest, Utils.TB_DEFAULT_BLOCK_NO, bits_len);
	    BoolExpr eq = Helper.is_equal(sym_lhs, sym_rhs);
	    if(eq == Helper.sym_true()) {
	        src_names = mov(store, sym_names, dest, src);
	    }
	    else {
	        src_names = mov(store, sym_names, a_reg, dest);
	    }
	    return src_names;
	}
	    

	static ArrayList<String> cmov(Store store, ArrayList<String> sym_names, String inst, String dest, String src) {
		ArrayList<String> src_names = sym_names;
	    BoolExpr res = SMTHelper.parse_predicate(store, inst, true, "cmov");
	    if(res == Helper.sym_false()) { }
	    else { 
	    	src_names = mov(store, sym_names, dest, src);
	    }
	    return src_names;
	}


	static Tuple<ArrayList<String>, ArrayList<String>> jmp_op(ArrayList<String> sym_names) {
		ArrayList<String> sym_in_stack = new ArrayList<String>();
		ArrayList<String> rest = new ArrayList<String>();
	    for(String sym : sym_names) {
	        boolean res = SMTHelper.check_sym_is_stack_addr(sym);
	        if(res) {
	            sym_in_stack.add(sym);
	        }
	        else {
	            rest.add(sym);
	        }
	    }
	    return new Tuple<>(sym_in_stack, rest);
	}


	Boolean call(Store store, ArrayList<String> sym_names) {
		Tuple<ArrayList<String>, ArrayList<String>> jmp_op_res = jmp_op(sym_names);
		ArrayList<String> sym_in_stack = jmp_op_res.x;
		ArrayList<String> sym_not_in_stack = jmp_op_res.y;
	    func_call_point = true;
	    for(String sym_name : sym_not_in_stack) {
	        int length = Config.MEM_ADDR_SIZE;
	        if(!Lib.REG_NAMES.contains(sym_name)) {
	            length = mem_len_map.get(sym_name);
	        }
	        if(Utils.imm_start_pat.matcher(sym_name).matches()) {
	            String s_name = "[" + sym_name + "]";
	            BitVecExpr val = SymEngine.get_sym(store, rip, s_name, Utils.TB_DEFAULT_BLOCK_NO, length);
	            if(!Helper.is_bit_vec_num(val)) {
	                func_call_point = false;
	            }
	        }
	    }
	    return func_call_point;
	}


	static boolean jmp_to_external_func(Store store, ArrayList<String> sym_names) {
		Tuple<ArrayList<String>, ArrayList<String>> jmp_op_res = jmp_op(sym_names);
		ArrayList<String> sym_not_in_stack = jmp_op_res.y;
	    func_call_point = true;
	    for(String sym_name : sym_not_in_stack) {
	        int length = Config.MEM_ADDR_SIZE;
	        // if(sym_name !in Lib.REG_NAMES {
	        //     length = mem_len_map[sym_name]
	        if(Utils.imm_start_pat.matcher(sym_name).matches()) {
	            String s_name = "[" + sym_name + "]";
	            BitVecExpr val = SymEngine.get_sym(store, rip, s_name, Utils.TB_DEFAULT_BLOCK_NO, length);
	            if(!Helper.is_bit_vec_num(val)) {
	                func_call_point = false;
	            }
	        }
	        else if(Lib.REG64_NAMES.contains(sym_name)) {
	            if(!Lib.CALLEE_NOT_SAVED_REGS.contains(sym_name)) {
	                func_call_point = false;
	            }
	        }
	    }
	    return func_call_point;
	}
	
	
	public static TBRetInfo parse_sym_src(HashMap<Long, String> address_ext_func_map, HashMap<Long, String> address_inst_tbl, HashMap<BitVecExpr, ArrayList<String>> address_sym_tbl, Store store, long curr_rip, String inst, ArrayList<String> sym_names) {
	    rip = curr_rip;
	    func_call_point = false;
	    halt_point = false;
	    concrete_val = false;
	    address_inst_map = address_inst_tbl;
	    address_sym_table = address_sym_tbl;
	    if(inst.startsWith("lock ")) {
	        inst = inst.split(" ", 2)[1];
	    }
	    String[] inst_split = inst.strip().split(" ", 2);
	    String inst_name = inst_split[0];
	    ArrayList<String> src_names = sym_names;
	    if(INSTRUCTION_SEMANTICS_MAP.containsKey(inst_name)) {
	    	Function<Triplet<Store, ArrayList<String>, ArrayList<String>>, ArrayList<String>> inst_op = INSTRUCTION_SEMANTICS_MAP.get(inst_name);
	        ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        src_names = inst_op.apply(new Triplet(store, sym_names, inst_args));
	    }
	    else if(inst_name.equals("nop") || inst_name.equals("hlt")) { }
	    else if(inst_name.startsWith("cmov")) {
	    	ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        src_names = cmov(store, sym_names, inst, inst_args.get(0), inst_args.get(1));
	    }
	    else if(inst_name.startsWith("rep")) {
	        inst = inst_split[1].strip();
	        TBRetInfo ret_info = parse_sym_src(address_ext_func_map, address_inst_map, address_sym_table, store, curr_rip, inst, sym_names);
	        src_names = ret_info.src_names;
	        func_call_point = ret_info.func_call_point;
	        halt_point = ret_info.halt_point;
	        concrete_val = ret_info.concrete_val;
	    }
	    else if(Utils.check_jmp_with_address(inst)) {
	        String jump_address_str = inst.split(" ", 2)[1].strip();
	        BitVecExpr n_address = SMTHelper.get_jump_address(store, rip, jump_address_str);
	        Long new_address = Helper.long_of_sym(n_address);
	        if(address_ext_func_map.containsKey(new_address)) {
	            func_call_point = jmp_to_external_func(store, sym_names);
	        }
	    }
	    ArrayList<String> res = new ArrayList<String>();
	    for(String src_name : src_names) {
	    	if(!res.contains(src_name))
	    		res.add(src_name);
	    }
	    return new TBRetInfo(res, func_call_point, halt_point, concrete_val);
	}

}

