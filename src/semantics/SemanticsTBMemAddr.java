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
import symbolic.SymHelper;

public class SemanticsTBMemAddr {

	static long rip = 0;
	static boolean funcCallPoint = false;
	static boolean haltPoint = false;
	static boolean concrete_val = false;
	static HashMap<String, Integer> memLenMap = new HashMap<String, Integer>();
	static HashMap<Long, String> addressSymTable = null;
	static HashMap<Long, String> addressInstMap = null;
	static HashMap<String, Function<Triplet<Store, ArrayList<String>, ArrayList<String>>, ArrayList<String>>> INSTRUCTION_SEMANTICS_MAP;
	
	static {
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
		INSTRUCTION_SEMANTICS_MAP.put("inc", arg -> inc_dec(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("dec", arg -> inc_dec(arg.x, arg.y, arg.z));
	}
	
	public static ArrayList<String> add_src_to_syms(ArrayList<String> sym_names, String src) {
		ArrayList<String> srcNames = sym_names;
	    srcNames.add(SymHelper.get_root_reg(src));
	    return srcNames;
	}

	static Boolean addr_points_to_external_lib(BitVecExpr addr) {
	    Boolean res = false;
	    if(Helper.is_bit_vec_num(addr)) {
    		Long int_addr = Helper.long_of_sym(addr);
    		if(addressSymTable.containsKey(int_addr)) {
	    		if(!addressInstMap.containsKey(int_addr))
	    			res = true;
	    	}
	    }
	    return res;
	}

	static ArrayList<String> sym_bin_on_src(Store store, ArrayList<String> sym_names, String src) {
		ArrayList<String> srcNames = sym_names;
	    if(!Utils.imm_start_pat.matcher(src).matches()) {
	        if(src.contains(":")) {
	        	String[] src_split = src.split(":");
	            srcNames = add_src_to_syms(sym_names, src_split[0]);
	            srcNames = add_src_to_syms(srcNames, src_split[1]);
	        }
	        else if(src.endsWith("]")) {
	        	Tuple<ArrayList<String>, Boolean> bottom_source = SMTHelper.get_bottom_source(src, store, rip, memLenMap);
	        	ArrayList<String> new_srcs = bottom_source.x;
	        	boolean is_reg_bottom = bottom_source.y;
	            if(is_reg_bottom) {
	            	srcNames.addAll(new_srcs);
	            }
	            else {
	            	BitVecExpr addr = SymEngine.get_effective_address(store, rip, src);
	                if(addr_points_to_external_lib(addr)) {
	                	haltPoint = true;
	                }
	                srcNames.add(addr.toString());
	                int length = Utils.get_sym_length(src);
	                memLenMap.put(addr.toString(), length);
	            }
	        }
	        else {
	            srcNames.add(SymHelper.get_root_reg(src));
	        }
	    }
	    return srcNames;
	}

	static ArrayList<String> sym_bin_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src1 = arg.get(1);
		String src2 = null;
		if(arg.size() > 2)
			src2 = arg.get(2);
		return sym_bin_oprt(store, sym_names, dest, src1, src2);
	}

	static ArrayList<String> sym_bin_oprt(Store store, ArrayList<String> sym_names, String dest, String src1, String src2) {
		ArrayList<String> srcNames = sym_names;
		if(src2 == null)
			src2 = dest;
	    srcNames = sym_bin_on_src(store, sym_names, src1);
	    srcNames = sym_bin_on_src(store, srcNames, src2);
	    return srcNames;
	}
	    		

	static ArrayList<String> mov_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return mov(store, sym_names, dest, src);
	}

	static ArrayList<String> mov(Store store, ArrayList<String> sym_names, String dest, String src) {
		ArrayList<String> srcNames = sym_names;
	    if(!Utils.imm_start_pat.matcher(src).matches()) {
	        if(Lib.REG_NAMES.contains(src)) {
	        	String dest_reg = null;
	            if(dest.endsWith("]")) {
	                BitVecExpr addr = SymEngine.get_effective_address(store, rip, dest);
	                dest_reg = addr.toString();
	            }
	            else {
	                dest_reg = SymHelper.get_root_reg(dest);
	            }
	            if(srcNames.contains(dest_reg)) {
	                srcNames.remove(dest_reg);
	            }
	            srcNames.add(SymHelper.get_root_reg(src));
	        }
	        else if(src.endsWith("]")) {
	            SMTHelper.remove_reg_from_sym_srcs(dest, srcNames);
	            Tuple<ArrayList<String>, Boolean> bottom_source = SMTHelper.get_bottom_source(src, store, rip, memLenMap);
	        	ArrayList<String> new_srcs = bottom_source.x;
	        	boolean is_reg_bottom = bottom_source.y;
	            if(is_reg_bottom) {
	                srcNames.addAll(new_srcs);
	            }
	            else {
	                BitVecExpr addr = SymEngine.get_effective_address(store, rip, src);
	                if(addr_points_to_external_lib(addr)) {
	                	haltPoint = true;
	                }
	                srcNames.add(addr.toString());
	            }
	        }
	    }
	    else {
	        concrete_val = true;
	    }
	    return srcNames;
	}

	static ArrayList<String> lea_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return lea(store, sym_names, dest, src);
	}

	static ArrayList<String> lea(Store store, ArrayList<String> sym_names, String dest, String src) {
	    ArrayList<String> srcNames = sym_names;
	    if(srcNames.contains(dest)) {
	        srcNames.remove(dest);
	        Tuple<ArrayList<String>, Boolean> bottom_source = SMTHelper.get_bottom_source(src, store, rip, memLenMap);
        	ArrayList<String> new_srcs = bottom_source.x;
        	srcNames.addAll(new_srcs);
	    }
	    return srcNames;
	}

	static ArrayList<String> push_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String src = arg.get(0);
		return push(store, sym_names, src);
	}

	static ArrayList<String> push(Store store, ArrayList<String> sym_names, String src) {
		ArrayList<String> srcNames = sym_names;
		BitVecExpr sym_rsp = SMTHelper.get_sym_rsp(store, rip);
	    String prev_rsp = Helper.bv_sub(sym_rsp, Config.MEM_ADDR_SIZE / 8).toString();
	    if(sym_names.contains(prev_rsp)) {
	        srcNames.remove(prev_rsp);
	    }
	    srcNames.add(src);
	    return srcNames;
	}
	
	static ArrayList<String> pop_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		return pop(store, sym_names, dest);
	}


	static ArrayList<String> pop(Store store, ArrayList<String> symNames, String dest) {
		BitVecExpr symSP = SMTHelper.get_sym_rsp(store, rip);
		ArrayList<String> srcNames = symNames;
		if(SMTHelper.check_source_is_sym(store, rip, dest, symNames)) {
		    SMTHelper.remove_reg_from_sym_srcs(dest, srcNames);
		    String symSPStr = symSP.toString();
		    if(!srcNames.contains(symSPStr)) {
			    srcNames.add(symSP.toString());
			    memLenMap.put(symSP.toString(), Config.MEM_ADDR_SIZE);
		    }
		}
	    return srcNames;
	}
	
	static ArrayList<String> xchg_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return xchg(store, sym_names, dest, src);
	}


	static ArrayList<String> xchg(Store store, ArrayList<String> sym_names, String dest, String src) {
		ArrayList<String> srcNames = sym_names;
	    // if(check_source_is_sym(store, rip, dest, sym_names) {
	    SMTHelper.add_new_reg_src(srcNames, dest, src);
	    return srcNames;
	}
	
	static ArrayList<String> mul_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		return mul(store, sym_names, dest);
	}

	static ArrayList<String> mul(Store store, ArrayList<String> sym_names, String src) {
		ArrayList<String> srcNames = sym_names;
	    int bits_len = Utils.get_sym_length(src);
	    Triplet<String,String,String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String a_reg = reg_info.x;
	    String dest = reg_info.z;
	    srcNames = sym_bin_oprt(store, sym_names, dest, a_reg, src);
	    return srcNames;
	}
	
	static ArrayList<String> imul_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src1 = null;
		String src2 = null;
		if(arg.size() > 1)
			src1 = arg.get(1);
		if(arg.size() > 2)
			src2 = arg.get(2);
		return imul(store, sym_names, dest, src1, src2);
	}


	static ArrayList<String> imul(Store store, ArrayList<String> sym_names, String dest, String src1, String src2) {
		ArrayList<String> srcNames = sym_names;
	    if(src1 != null) {
	        if(src2 == null) {
	            srcNames = sym_bin_oprt(store, sym_names, dest, src1, null);
	        }
	        else {
	            srcNames = sym_bin_oprt(store, sym_names, src1, src2, null);
	        }
	    }
	    else {
	        srcNames = mul(store, sym_names, dest);
	    }
	    return srcNames;
	}
	
	static ArrayList<String> div_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String src = arg.get(0);
		return div(store, sym_names, src);
	}


	static ArrayList<String> div(Store store, ArrayList<String> sym_names, String src) {
	    int bits_len = Utils.get_sym_length(src);
	    Triplet<String,String,String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String qreg = reg_info.x;
	    String rreg = reg_info.y;
	    String dest = reg_info.z;
	    ArrayList<String> srcNames = sym_bin_oprt(store, sym_names, qreg + ":" +rreg, dest, src);
	    return srcNames;
	}


	static ArrayList<String> cdqe(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
	    return sym_names;
	}

	
	static ArrayList<String> cmpxchg_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return cmpxchg(store, sym_names, dest, src);
	}

	static ArrayList<String> cmpxchg(Store store, ArrayList<String> sym_names, String dest, String src) {
		ArrayList<String> srcNames = sym_names;
	    int bits_len = Utils.get_sym_length(dest);
	    Triplet<String,String,String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String a_reg = reg_info.x;
	    BitVecExpr sym_lhs = SymEngine.get_sym(store, rip, a_reg, Utils.TB_DEFAULT_BLOCK_NO, bits_len);
	    BitVecExpr sym_rhs = SymEngine.get_sym(store, rip, dest, Utils.TB_DEFAULT_BLOCK_NO, bits_len);
	    BoolExpr eq = Helper.is_equal(sym_lhs, sym_rhs);
	    if(eq.equals(Helper.SymTrue)) {
	        srcNames = mov(store, sym_names, dest, src);
	    }
	    else {
	        srcNames = mov(store, sym_names, a_reg, dest);
	    }
	    return srcNames;
	}
	    

	static ArrayList<String> cmov(Store store, ArrayList<String> sym_names, String inst, String dest, String src) {
		ArrayList<String> srcNames = sym_names;
	    BoolExpr res = SMTHelper.parse_predicate(store, inst, true, "cmov");
	    if(res.equals(Helper.SymFalse)) { }
	    else { 
	    	srcNames = mov(store, sym_names, dest, src);
	    }
	    return srcNames;
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


	static Boolean call(Store store, ArrayList<String> sym_names) {
		Tuple<ArrayList<String>, ArrayList<String>> jmp_op_res = jmp_op(sym_names);
		ArrayList<String> sym_not_in_stack = jmp_op_res.y;
	    funcCallPoint = true;
	    for(String sym_name : sym_not_in_stack) {
	        int length = Config.MEM_ADDR_SIZE;
	        if(!Lib.REG_NAMES.contains(sym_name)) {
	            length = memLenMap.get(sym_name);
	        }
	        if(Utils.imm_start_pat.matcher(sym_name).matches()) {
	            String s_name = "[" + sym_name + "]";
	            BitVecExpr val = SymEngine.get_sym(store, rip, s_name, Utils.TB_DEFAULT_BLOCK_NO, length);
	            if(!Helper.is_bit_vec_num(val)) {
	                funcCallPoint = false;
	            }
	        }
	    }
	    return funcCallPoint;
	}


	static boolean jmp_to_external_func(Store store, ArrayList<String> sym_names) {
		Tuple<ArrayList<String>, ArrayList<String>> jmp_op_res = jmp_op(sym_names);
		ArrayList<String> sym_not_in_stack = jmp_op_res.y;
	    funcCallPoint = true;
	    for(String sym_name : sym_not_in_stack) {
	        int length = Config.MEM_ADDR_SIZE;
	        if(!Lib.REG_NAMES.contains(sym_name)) {
	            length = memLenMap.get(sym_name);
	        }
	        if(Utils.imm_start_pat.matcher(sym_name).matches()) {
	            String s_name = "[" + sym_name + "]";
	            BitVecExpr val = SymEngine.get_sym(store, rip, s_name, Utils.TB_DEFAULT_BLOCK_NO, length);
	            if(!Helper.is_bit_vec_num(val)) {
	                funcCallPoint = false;
	            }
	        }
	        else if(Lib.REG_NAMES.contains(sym_name)) {
	            if(!Lib.CALLEE_NOT_SAVED_REGS.get(Config.MEM_ADDR_SIZE).contains(sym_name)) {
	                funcCallPoint = false;
	            }
	        }
	    }
	    return funcCallPoint;
	}
	
	
	static ArrayList<String> inc_dec(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		return sym_bin_on_src(store, sym_names, dest);
	}
	
	
	public static TBRetInfo parse_sym_src(HashMap<Long, String> addressExtFuncMap, HashMap<Long, String> addressInstTbl, HashMap<Long, String> address_sym_tbl, Store store, long curr_rip, String inst, ArrayList<String> sym_names) {
	    rip = curr_rip;
	    funcCallPoint = false;
	    haltPoint = false;
	    concrete_val = false;
	    addressInstMap = addressInstTbl;
	    addressSymTable = address_sym_tbl;
	    if(inst.startsWith("lock ")) {
	        inst = inst.split(" ", 2)[1];
	    }
	    String[] inst_split = inst.strip().split(" ", 2);
	    String inst_name = inst_split[0];
	    ArrayList<String> srcNames = sym_names;
	    if(INSTRUCTION_SEMANTICS_MAP.containsKey(inst_name)) {
	    	Function<Triplet<Store, ArrayList<String>, ArrayList<String>>, ArrayList<String>> inst_op = INSTRUCTION_SEMANTICS_MAP.get(inst_name);
	        ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        srcNames = inst_op.apply(new Triplet<>(store, sym_names, inst_args));
	    }
	    else if(inst_name.equals("nop") || inst_name.equals("hlt")) { }
	    else if(inst_name.startsWith("cmov")) {
	    	ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        srcNames = cmov(store, sym_names, inst, inst_args.get(0), inst_args.get(1));
	    }
	    else if(inst_name.startsWith("rep")) {
	        inst = inst_split[1].strip();
	        TBRetInfo ret_info = parse_sym_src(addressExtFuncMap, addressInstMap, addressSymTable, store, curr_rip, inst, sym_names);
	        srcNames = ret_info.srcNames;
	        funcCallPoint = ret_info.funcCallPoint;
	        haltPoint = ret_info.haltPoint;
	        concrete_val = ret_info.concrete_val;
	        memLenMap = ret_info.memLenMap;
	    }
	    else if(Utils.check_jmp_with_address(inst)) {
	        String jump_address_str = inst.split(" ", 2)[1].strip();
	        BitVecExpr n_address = SMTHelper.get_jump_address(store, rip, jump_address_str);
	        Long new_address = Helper.long_of_sym(n_address);
	        if(addressExtFuncMap.containsKey(new_address)) {
	            funcCallPoint = jmp_to_external_func(store, sym_names);
	        }
	    }
	    ArrayList<String> res = new ArrayList<String>();
	    for(String src_name : srcNames) {
	    	if(!res.contains(src_name))
	    		res.add(src_name);
	    }
	    return new TBRetInfo(res, funcCallPoint, haltPoint, concrete_val);
	}

}

