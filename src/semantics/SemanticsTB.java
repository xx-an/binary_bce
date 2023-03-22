package semantics;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.function.Function;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;

import common.Config;
import common.Helper;
import common.Lib;
import common.Tuple;
import common.Utils;
import symbolic.SymEngine;
import symbolic.SymHelper;
import common.Triplet;
import block.Store;

public class SemanticsTB {
	
	static long rip = -1;
	static boolean haltPoint = false;
	static Integer boundary = null;
	static boolean stillTB = true;
	static HashMap<String, Integer> memLenMap = new HashMap<>();
	static HashMap<String, Function<Triplet<Store, ArrayList<String>, ArrayList<String>>, ArrayList<String>>> INSTRUCTION_SEMANTICS_MAP;

	static {
		INSTRUCTION_SEMANTICS_MAP = new HashMap<String, Function<Triplet<Store, ArrayList<String>, ArrayList<String>>, ArrayList<String>>>();
		INSTRUCTION_SEMANTICS_MAP.put("mov", arg -> mov(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("lea", arg -> lea(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("pop", arg -> pop(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("add", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("sub", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("xor", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("and", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("or", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("sar", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("shr", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("sal", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("shl", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("xchg", arg -> xchg(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("cmp", arg -> cmp_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("imul", arg -> imul(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("mul", arg -> mul(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("idiv", arg -> div_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("div", arg -> div_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("cmpxchg", arg -> cmpxchg(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("movzx", arg -> mov(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("movsx", arg -> mov(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("movsxd", arg -> mov(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("adc", arg -> sym_bin_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("sbb", arg -> sym_bin_op(arg.x, arg.y, arg.z));
	}
	
	
	static ArrayList<String> sym_bin_on_src(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String src = arg.get(0);
		return sym_bin_on_src(store, sym_names, src);
	}
	
	static ArrayList<String> sym_bin_on_src(Store store, ArrayList<String> sym_names, String src) {
		ArrayList<String> srcNames = sym_names;
		int src_len = Utils.get_sym_length(src);
	    BitVecExpr sym_src = SymEngine.get_sym(store, rip, src, src_len);
	    if(!Helper.is_bit_vec_num(sym_src)) {
	        if(src.contains(":")) {
	            String[] src_split = src.split(":");
	            SMTHelper.add_src_to_syms(store, srcNames, src_split[0]);
	            SMTHelper.add_src_to_syms(store, srcNames, src_split[1]);
	        }
	        else if(src.endsWith("]")) {
	        	Tuple<ArrayList<String>, Boolean> bottom_source = SMTHelper.get_bottom_source(src, store, rip, memLenMap);
	        	ArrayList<String> new_srcs = bottom_source.x;
	        	boolean is_reg_bottom = bottom_source.y;
	            if(is_reg_bottom)
	                srcNames.addAll(new_srcs);
	            else {
	                BitVecExpr addr = SymEngine.get_effective_address(store, rip, src);
	                srcNames.add(addr.toString());
	            }
	        }
	        else
	            srcNames.add(SymHelper.get_root_reg(src));
	    }
	    else {
	        if(src.contains(":")) {
	        	String[] src_split = src.split(":");
	            SMTHelper.remove_reg_from_sym_srcs(src_split[0], srcNames);
	            SMTHelper.remove_reg_from_sym_srcs(src_split[1], srcNames);
	        }
	        else if(src.endsWith("]")) {
	        	ArrayList<String> new_srcs = SMTHelper.get_mem_reg_source(src);
	        	srcNames.removeAll(new_srcs);
	        }
	        else
	            SMTHelper.remove_reg_from_sym_srcs(src, srcNames);
	    }
	    return srcNames;
	}


	static ArrayList<String> sym_bin_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src1 = arg.get(1);
		String src2 = (arg.size() > 2) ? arg.get(2) : null;
		return sym_bin_oprt(store, sym_names, dest, src1, src2);
	}
	
	static ArrayList<String> sym_bin_oprt(Store store, ArrayList<String> sym_names, String dest, String src1, String src2) {
		ArrayList<String> srcNames = sym_names;
	    if(SMTHelper.check_source_is_sym(store, rip, dest, sym_names)) {
	        String src_2 = (src2 == null) ? dest : src2;
	        srcNames = sym_bin_on_src(store, sym_names, src1);
	        srcNames = sym_bin_on_src(store, srcNames, src_2);
	    }
	    return srcNames;
	}


	static ArrayList<String> mov(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return mov_op(store, sym_names, dest, src);
	}
	
	
	static ArrayList<String> mov_op(Store store, ArrayList<String> sym_names, String dest, String src) {
		ArrayList<String> srcNames = sym_names;
	    if(SMTHelper.check_source_is_sym(store, rip, dest, sym_names)) {
	        if(Lib.REG_NAMES.contains(src)) {
	        	String destReg = "";
	        	if(dest.endsWith("]")) {
	        		BitVecExpr addr = SymEngine.get_effective_address(store, rip, dest);
	        		destReg = addr.toString();
	        	}
	        	else
	        		destReg = SymHelper.get_root_reg(dest);
	        	if(srcNames.contains(destReg))
	        		srcNames.remove(destReg);
 	            srcNames.add(SymHelper.get_root_reg(src));
	        }
	        else if(src.endsWith("]")) {
	            SMTHelper.remove_reg_from_sym_srcs(dest, srcNames);
	            Tuple<ArrayList<String>, Boolean> bottom_source = SMTHelper.get_bottom_source(src, store, rip, memLenMap);
	        	ArrayList<String> new_srcs = bottom_source.x;
	        	boolean is_reg_bottom = bottom_source.y;
	            if(is_reg_bottom)
	            	srcNames.addAll(new_srcs);
	            else {
	            	BitVecExpr addr = SymEngine.get_effective_address(store, rip, src);
	                srcNames.add(addr.toString());
	                int length = Utils.get_sym_length(src);
	                memLenMap.put(addr.toString(), length);
	            }
	        }
	    }
	    return srcNames;
	}


	static ArrayList<String> lea(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		ArrayList<String> srcNames = sym_names;
	    if(sym_names.contains(dest)) {
	    	sym_names.remove(dest);
	        Tuple<ArrayList<String>, Boolean> bottom_source = SMTHelper.get_bottom_source(src, store, rip, memLenMap);
        	ArrayList<String> new_srcs = bottom_source.x;
        	stillTB = bottom_source.y;
        	srcNames.addAll(new_srcs);
	    }
	    return srcNames;
	}


	static ArrayList<String> pop(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
	    ArrayList<String> srcNames = sym_names;
	    if(srcNames.contains(dest))
	        stillTB = false;
	    return srcNames;
	}


	static ArrayList<String> xchg(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		ArrayList<String> srcNames = sym_names;
	    if(SMTHelper.check_source_is_sym(store, rip, dest, sym_names))
	        SMTHelper.add_new_reg_src(sym_names, dest, src);
	    return srcNames;
	}

	
	static ArrayList<String> mul(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String src = arg.get(0);
		return mul_op(store, sym_names, src);
	}
	

	static ArrayList<String> mul_op(Store store, ArrayList<String> sym_names, String src) {
		ArrayList<String> srcNames = sym_names;
	    int bits_len = Utils.get_sym_length(src);
	    Triplet<String,String,String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String a_reg = reg_info.x;
	    String dest = reg_info.z;
	    srcNames = sym_bin_oprt(store, sym_names, dest, a_reg, src);
	    return srcNames;
	}


	static ArrayList<String> imul(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src1 = (arg.size() > 1) ? arg.get(1) : null;
		String src2 = (arg.size() > 2) ? arg.get(2) : null;
		ArrayList<String> srcNames = sym_names;
	    if(src1 != null) {
	        if(src2 == null)
	            srcNames = sym_bin_oprt(store, sym_names, dest, src1, null);
	        else
	            srcNames = sym_bin_oprt(store, sym_names, src1, src2, null);
	    }
	    else
	        srcNames = mul_op(store, sym_names, dest);
	    return srcNames;
	}


	static ArrayList<String> div_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String src = arg.get(0);
	    int bits_len = Utils.get_sym_length(src);
	    Triplet<String,String,String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String qreg = reg_info.x;
	    String rreg = reg_info.y;
	    String dest = reg_info.z;
	    ArrayList<String> srcNames = sym_bin_oprt(store, sym_names, qreg + ":" +rreg, dest, src);
	    return srcNames;
	}


	static ArrayList<String> cmpxchg(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		ArrayList<String> srcNames = sym_names;
	    int bits_len = Utils.get_sym_length(dest);
	    Triplet<String,String,String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String a_reg = reg_info.x;
	    BitVecExpr sym_lhs = SymEngine.get_sym(store, rip, a_reg, bits_len);
	    BitVecExpr sym_rhs = SymEngine.get_sym(store, rip, dest, bits_len);
	    BoolExpr eq = Helper.is_equal(sym_lhs, sym_rhs);
	    if(eq.equals(Helper.SymTrue))
	        srcNames = mov_op(store, sym_names, dest, src);
	    else
	        srcNames = mov_op(store, sym_names, a_reg, dest);
	    return srcNames;
	}
	    

	static ArrayList<String> cmov(Store store, ArrayList<String> sym_names, String inst, String dest, String src) {
		ArrayList<String> srcNames = sym_names;
	    BoolExpr res = SMTHelper.parse_predicate(store, inst, true, "cmov");
	    if(res.equals(Helper.SymTrue))
	    	srcNames = mov_op(store, sym_names, dest, src);
	    return srcNames;
	}


	static ArrayList<String> cmp_op(Store store, ArrayList<String> sym_names, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		ArrayList<String> srcNames = sym_names;
	    if(SMTHelper.check_source_is_sym(store, rip, src, sym_names)) {
	    	String tmp = src;
	    	src = dest;
	    	dest = tmp;
	    }
	    if(SMTHelper.check_cmp_dest_is_sym(store, rip, dest, sym_names, memLenMap)) {
	        BitVecExpr sym_src = SymEngine.get_sym(store, rip, src, Config.MEM_ADDR_SIZE);
	        if(Helper.is_bit_vec_num(sym_src)) {
	        	srcNames.clear();
	        	srcNames.add(dest);
	        	haltPoint = true;
	            boundary = Helper.int_of_sym(sym_src);
	        }
	        else
	            stillTB = false;
	    }
	    else
	        stillTB = false;
	    return srcNames;
	}


	public static TBRetInfo parse_sym_src(Store store, long curr_rip, String curr_inst, ArrayList<String> sym_names) {
	    rip = curr_rip;
	    haltPoint = false;
	    boundary = null;
	    stillTB = true;
	    String inst = curr_inst;
	    if(inst.startsWith("lock "))
	        inst = inst.split(" ", 2)[1];
	    String[] inst_split = inst.strip().split(" ", 2);
	    String inst_name = inst_split[0];
	    ArrayList<String> srcNames = sym_names;
	    if(INSTRUCTION_SEMANTICS_MAP.containsKey(inst_name)) {
	    	Function<Triplet<Store, ArrayList<String>, ArrayList<String>>, ArrayList<String>> inst_op = INSTRUCTION_SEMANTICS_MAP.get(inst_name);
	        ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        srcNames = inst_op.apply(new Triplet<>(store, sym_names, inst_args));
	    }
	    else if(inst_name.equals("nop") || inst_name.equals("hlt")) {}
	    else if(inst_name.startsWith("cmov")) {
	        ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        srcNames = cmov(store, sym_names, inst, inst_args.get(0), inst_args.get(1));
	    }
	    else if(inst_name.startsWith("rep")) {
	        String rep_inst = inst_split[1].strip();
	        TBRetInfo res = parse_sym_src(store, curr_rip, rep_inst, sym_names);
	        srcNames = res.srcNames;
	        haltPoint = res.haltPoint;
	        boundary = res.boundary;
	        stillTB = res.stillTB;
	        memLenMap = res.memLenMap;
	    }
	    ArrayList<String> res = new ArrayList<String>();
	    for(String src_name : srcNames) {
	    	if(!res.contains(src_name))
	    		res.add(src_name);
	    }
	    TBRetInfo ret_info = new TBRetInfo(res, haltPoint, boundary, stillTB, memLenMap);
	    return ret_info;
	}


}
