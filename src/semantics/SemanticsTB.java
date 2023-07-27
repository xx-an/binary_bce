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

public class SemanticsTB {

	static int haltPoint = -1;
	static HashMap<Long, String> addrExtFuncMap = null;
	static HashMap<String, Integer> memLenMap = new HashMap<String, Integer>();
	static HashMap<String, Function<Triplet<Store, ArrayList<String>, ArrayList<String>>, ArrayList<String>>> INSTRUCTION_SEMANTICS_MAP;
	
	static {
		INSTRUCTION_SEMANTICS_MAP = new HashMap<String, Function<Triplet<Store, ArrayList<String>, ArrayList<String>>, ArrayList<String>>>();
		INSTRUCTION_SEMANTICS_MAP.put("mov", arg -> mov_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("lea", arg -> lea_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("push", arg -> push_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("pop", arg -> pop_op(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("pusha", arg -> pusha(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("pushad", arg -> pushad(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("popa", arg -> popa(arg.x, arg.y, arg.z));
		INSTRUCTION_SEMANTICS_MAP.put("popad", arg -> popad(arg.x, arg.y, arg.z));
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
	
	static Boolean addrPointsToExtLib(BitVecExpr addr) {
	    Boolean res = false;
	    if(Helper.is_bit_vec_num(addr)) {
    		Long intAddr = Helper.long_of_sym(addr);
    		if(addrExtFuncMap.containsKey(intAddr)) {
	    		res = true;
	    	}
	    }
	    return res;
	}

	
	static ArrayList<String> sym_bin_on_src(Store store, ArrayList<String> symNames, String src) {
		ArrayList<String> srcNames = symNames;
	    int src_len = Utils.getSymLength(src);
	    BitVecExpr symSrc = SymEngine.get_sym(store, src, Utils.TB_DEFAULT_BLOCK_NO, src_len);
	    if(!Helper.is_bit_vec_num(symSrc)) {
	        if(src.contains(":")) {
	            String[] src_split = src.split(":"); 
	            SMTHelper.addRegSrcToSyms(store, symNames, src_split[0]);
	            SMTHelper.addRegSrcToSyms(store, srcNames, src_split[1]);
	        }
	        else if(src.endsWith("]")) {
	        	Tuple<ArrayList<String>, Boolean> bottom_source = SMTHelper.get_bottom_source(src, store, memLenMap);
	        	ArrayList<String> newSrcs = bottom_source.x;
	        	boolean bottomSrcIsReg = bottom_source.y;
	        	if(bottomSrcIsReg) {
	                srcNames.addAll(newSrcs);
	            }
	            else {
	                BitVecExpr addr = SymEngine.get_effective_address(store, src);
	                if(addrPointsToExtLib(addr)) {
	                	haltPoint = 0;
	                }
	                srcNames.add(addr.toString());
	                int length = Utils.getSymLength(src);
	                memLenMap.put(addr.toString(), length);
	            }
	        }
	        else {
	            srcNames.add(SymHelper.getRootReg(src));
	        }
	    }
	    else {
	        if(src.contains(":")) {
	        	String[] src_split = src.split(":"); 
	            SMTHelper.rmRegFromSymSrcs(src_split[0], srcNames);
	            SMTHelper.rmRegFromSymSrcs(src_split[1], srcNames);
	        }
	        else if(src.endsWith("]")) {
	        	ArrayList<String> newSrcs = SMTHelper.getMemRegSrcs(src);
	            srcNames.removeAll(newSrcs);
	        }
	        else {
	            SMTHelper.rmRegFromSymSrcs(src, srcNames);
	        }
	    }
	    return srcNames;
	}
	
	
	static ArrayList<String> sym_bin_op(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src1 = arg.get(1);
		String src2 = null;
		if(arg.size() > 2)
			src2 = arg.get(2);
		return sym_bin_oprt(store, symNames, dest, src1, src2);
	}
	
	
	static ArrayList<String> sym_bin_oprt(Store store, ArrayList<String> symNames, String dest, String src1, String src2) {
		ArrayList<String> srcNames = symNames;
	    if(SMTHelper.srcIsSymbolic(store, dest, symNames)) {
	        if(src2 == null) 
	        	src2 = dest;
	        srcNames = sym_bin_on_src(store, symNames, src1);
	        srcNames = sym_bin_on_src(store, srcNames, src2);
	    }
	    return srcNames;
	}

	
	static ArrayList<String> mov_op(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return mov(store, symNames, dest, src);
	}
	
	
	static ArrayList<String> mov(Store store, ArrayList<String> symNames, String dest, String src) {
		ArrayList<String> srcNames = symNames;
	    if(SMTHelper.srcIsSymbolic(store, dest, symNames)) {
	        if(Lib.REG_NAMES.contains(src)) {
	        	String destInfo = null;
	            if(dest.endsWith("]")) {
	                BitVecExpr addr = SymEngine.get_effective_address(store, dest);
	                destInfo = addr.toString();
	            }
	            else {
	            	destInfo = SymHelper.getRootReg(dest);
	            }
	            if(srcNames.contains(destInfo)) {
	                srcNames.remove(destInfo);
	            }
	            srcNames.add(SymHelper.getRootReg(src));
	        }
	        else if(src.endsWith("]")) {
	            SMTHelper.rmRegFromSymSrcs(dest, srcNames);
	            Tuple<ArrayList<String>, Boolean> bottom_source = SMTHelper.get_bottom_source(src, store, memLenMap);
	        	ArrayList<String> new_srcs = bottom_source.x;
	        	boolean is_reg_bottom = bottom_source.y;
	        	if(is_reg_bottom) {
	                srcNames.addAll(new_srcs);
	            }
	            else {
	                BitVecExpr addr = SymEngine.get_effective_address(store, src);
	                if(addrPointsToExtLib(addr)) {
	                	haltPoint = 0;
	                }
	                srcNames.add(addr.toString());
	                int length = Utils.getSymLength(src);
	                memLenMap.put(addr.toString(), length);
	            }
	        }
	    }
	    else {
	        haltPoint = 1;
	    }
	    return srcNames;
	}
	
	
	static ArrayList<String> lea_op(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return lea(store, symNames, dest, src);
	}
	
	
	static ArrayList<String> lea(Store store, ArrayList<String> symNames, String dest, String src) {
		ArrayList<String> srcNames = symNames;
	    if(srcNames.contains(dest)) {
	        srcNames.remove(dest);
	        Tuple<ArrayList<String>, Boolean> bottom_source = SMTHelper.get_bottom_source(src, store, memLenMap);
        	ArrayList<String> new_srcs = bottom_source.x;
	        srcNames.addAll(new_srcs);
	    }
	    return srcNames;
	}
	
	static ArrayList<String> push_op(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		String src = arg.get(0);
		BitVecExpr symSP = SymHelper.stackTopBVAddr(store);
		symSP = Helper.bv_sub(symSP, Config.MEM_ADDR_SIZE / 8);
		return push(store, symNames, symSP, src);
	}
	
	static ArrayList<String> pusha(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		ArrayList<String> srcNames = symNames;
		BitVecExpr symSP = SymHelper.stackTopBVAddr(store);
		for(String name: SMTHelper.pushaOrder) {
			if(name != "") {
				symSP = Helper.bv_sub(symSP, 2);
				srcNames = push(store, srcNames, symSP, name);
			}
			else
				symSP = Helper.bv_sub(symSP, 2);
		}
		return srcNames;
	}
	
	static ArrayList<String> pushad(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		ArrayList<String> srcNames = symNames;
		BitVecExpr symSP = SymHelper.stackTopBVAddr(store);
		for(String name: SMTHelper.pushadOrder) {
			if(name != "") {
				symSP = Helper.bv_sub(symSP, 4);
				srcNames = push(store, srcNames, symSP, name);
			}
			else
				symSP = Helper.bv_sub(symSP, 4);
		}
		return srcNames;
	}
	
	static ArrayList<String> push(Store store, ArrayList<String> symNames, BitVecExpr symSP, String src) {
		ArrayList<String> srcNames = symNames;
	    String symSPStr = symSP.toString();
	    if(symNames.contains(symSPStr)) {
	        srcNames.remove(symSPStr);
	        srcNames.add(src);
	    }
	    return srcNames;
	}
	
	static ArrayList<String> pop_op(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		String dest = arg.get(0);
		BitVecExpr symSP = SymHelper.stackTopBVAddr(store);
		return pop(store, symNames, symSP, dest);
	}
	
	static ArrayList<String> popa(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		ArrayList<String> srcNames = symNames;
		BitVecExpr symSP = SymHelper.stackTopBVAddr(store);
		for (int idx = SMTHelper.pushaOrder.length - 1; idx > 0; idx -= 2) {
			String name1 = SMTHelper.pushaOrder[idx];
			String name2 = SMTHelper.pushaOrder[idx - 1];
			srcNames = pop(store, srcNames, symSP, name1);
			if(name2 != "") {
				srcNames = pop(store, srcNames, symSP, name2);
			}
			symSP = Helper.bv_add(symSP, 4);
		}
		return srcNames;
	}
	
	static ArrayList<String> popad(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		ArrayList<String> srcNames = symNames;
		BitVecExpr symSP = SymHelper.stackTopBVAddr(store);
		for(int idx = SMTHelper.pushadOrder.length - 1; idx >= 0; idx--) {
			String name = SMTHelper.pushadOrder[idx];
			if(name != "") {
				srcNames = pop(store, srcNames, symSP, name);
			}
			symSP = Helper.bv_add(symSP, 4);
		}
		return srcNames;
	}
	
	
	static ArrayList<String> pop(Store store, ArrayList<String> symNames, BitVecExpr symSP, String dest) {
		ArrayList<String> srcNames = symNames;
		if(SMTHelper.srcIsSymbolic(store, dest, symNames)) {
		    SMTHelper.rmRegFromSymSrcs(dest, srcNames);
		    String symSPStr = symSP.toString();
		    if(!srcNames.contains(symSPStr)) {
			    srcNames.add(symSP.toString());
			    memLenMap.put(symSP.toString(), Config.MEM_ADDR_SIZE);
		    }
		}
	    return srcNames;
	}
	
	
	static ArrayList<String> xchg_op(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return xchg(store, symNames, dest, src);
	}
	
	
	static ArrayList<String> xchg(Store store, ArrayList<String> symNames, String dest, String src) {
		ArrayList<String> srcNames = symNames;
	    if(SMTHelper.srcIsSymbolic(store, dest, symNames)) {
	    	SMTHelper.addNewRegSrc(srcNames, dest, src);
	    }
	    return srcNames;
	}
	
	
	static ArrayList<String> mul_op(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		String dest = arg.get(0);
		return mul(store, symNames, dest);
	}
	
	
	static ArrayList<String> mul(Store store, ArrayList<String> symNames, String src) {
		ArrayList<String> srcNames = symNames;
	    int bits_len = Utils.getSymLength(src);
	    Triplet<String,String,String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String a_reg = reg_info.x;
	    String dest = reg_info.z;
	    srcNames = sym_bin_oprt(store, symNames, dest, a_reg, src);
	    return srcNames;
	}
	
	
	static ArrayList<String> imul_op(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src1 = null;
		String src2 = null;
		if(arg.size() > 1)
			src1 = arg.get(1);
		if(arg.size() > 2)
			src2 = arg.get(2);
		return imul(store, symNames, dest, src1, src2);
	}
	
	static ArrayList<String> imul(Store store, ArrayList<String> symNames, String dest, String src1, String src2) {
		ArrayList<String> srcNames = symNames;
	    if(src1 != null) {
	        if(src2 == null) {
	            srcNames = sym_bin_oprt(store, symNames, dest, src1, null);
	        }
	        else {
	            srcNames = sym_bin_oprt(store, symNames, src1, src2, null);
	        }
	    }
	    else {
	        srcNames = mul(store, symNames, dest);
	    }
	    return srcNames;
	}
	
	
	static ArrayList<String> div_op(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		String src = arg.get(0);
		return div(store, symNames, src);
	}
	
	
	static ArrayList<String> div(Store store, ArrayList<String> symNames, String src) {
	    int bits_len = Utils.getSymLength(src);
	    Triplet<String,String,String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String qreg = reg_info.x;
	    String rreg = reg_info.y;
	    String dest = reg_info.z;
	    ArrayList<String> srcNames = sym_bin_oprt(store, symNames, qreg + ":" +rreg, dest, src);
	    return srcNames;
	}
	
	
	static ArrayList<String> cdqe(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
	    return symNames;
	}
	
	
	static ArrayList<String> cmpxchg_op(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		return cmpxchg(store, symNames, dest, src);
	}

	
	static ArrayList<String> cmpxchg(Store store, ArrayList<String> symNames, String dest, String src) {
		ArrayList<String> srcNames = symNames;
	    int bits_len = Utils.getSymLength(dest);
	    Triplet<String,String,String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String a_reg = reg_info.x;
	    BitVecExpr sym_lhs = SymEngine.get_sym(store, a_reg, Utils.TB_DEFAULT_BLOCK_NO, bits_len);
	    BitVecExpr sym_rhs = SymEngine.get_sym(store, dest, Utils.TB_DEFAULT_BLOCK_NO, bits_len);
	    BoolExpr eq = Helper.is_equal(sym_lhs, sym_rhs);
	    if(eq.equals(Helper.SymTrue)) {
	        srcNames = mov(store, symNames, dest, src);
	    }
	    else {
	        srcNames = mov(store, symNames, a_reg, dest);
	    }
	    return srcNames;
	}
	    
	
	static ArrayList<String> cmov(Store store, ArrayList<String> symNames, String inst, String dest, String src) {
		ArrayList<String> srcNames = symNames;
	    BoolExpr res = SMTHelper.parse_predicate(store, inst, true, "cmov");
	    if(res.equals(Helper.SymFalse)) { }
	    else { 
	    	srcNames = mov(store, symNames, dest, src);
	    }
	    return srcNames;
	}
	
	static ArrayList<String> inc_dec(Store store, ArrayList<String> symNames, ArrayList<String> arg) {
		String dest = arg.get(0);
		return sym_bin_on_src(store, symNames, dest);
	}
	
	static ArrayList<String> jmp_op(ArrayList<String> symNames) {
		ArrayList<String> symsNotAtStack = new ArrayList<String>();
	    for(String sym : symNames) {
	        if(!SMTHelper.isSymAddrAtStack(sym)) {
	        	symsNotAtStack.add(sym);
	        }
	    }
	    return symsNotAtStack;
	}
	
	
	static int jumpToExtFunc(Store store, ArrayList<String> symNames) {
		ArrayList<String> symsNotAtStack = jmp_op(symNames);
	    haltPoint = 0;
	    for(String symName : symsNotAtStack) {
	        int length = Config.MEM_ADDR_SIZE;
	        if(!Lib.REG_NAMES.contains(symName)) {
	            length = memLenMap.get(symName);
	        }
	        if(Utils.imm_start_pat.matcher(symName).matches()) {
	            String sName = "[" + symName + "]";
	            BitVecExpr val = SymEngine.get_sym(store, sName, Utils.TB_DEFAULT_BLOCK_NO, length);
	            if(!Helper.is_bit_vec_num(val)) {
	                haltPoint = -1;
	            }
	        }
	        else if(Lib.REG_NAMES.contains(symName)) {
	            if(!Config.CALLEE_NOT_SAVED_REGS.contains(symName)) {
	                haltPoint = -1;
	            }
	        }
	    }
	    return haltPoint;
	}
	
	
	public static Triplet<Integer, ArrayList<String>, HashMap<String, Integer>> parse_sym_src(HashMap<Long, String> addressExtFuncMap, HashMap<Long, String> addressInstMap, Store store, String inst, ArrayList<String> symNames) {
	    haltPoint = -1;
	    addrExtFuncMap = addressExtFuncMap;
	    if(inst.startsWith("lock ")) {
	        inst = inst.split(" ", 2)[1];
	    }
	    String[] inst_split = inst.strip().split(" ", 2);
	    String inst_name = inst_split[0];
	    ArrayList<String> srcNames = symNames;
	    if(INSTRUCTION_SEMANTICS_MAP.containsKey(inst_name)) {
	    	Function<Triplet<Store, ArrayList<String>, ArrayList<String>>, ArrayList<String>> inst_op = INSTRUCTION_SEMANTICS_MAP.get(inst_name);
	        ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        srcNames = inst_op.apply(new Triplet<>(store, symNames, inst_args));
	    }
	    else if(inst_name.equals("nop") || inst_name.equals("hlt")) { }
	    else if(inst_name.startsWith("cmov")) {
	    	ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        srcNames = cmov(store, symNames, inst, inst_args.get(0), inst_args.get(1));
	    }
	    else if(inst_name.startsWith("rep")) {
	        inst = inst_split[1].strip();
	        Triplet<Integer, ArrayList<String>, HashMap<String, Integer>> retInfo = parse_sym_src(addrExtFuncMap, addressInstMap, store, inst, symNames);
	        haltPoint = retInfo.x;
	        srcNames = retInfo.y;
	        memLenMap = retInfo.z;
	    }
	    else if(Utils.check_jmp_with_address(inst)) {
	        String jmpAddrStr = inst.split(" ", 2)[1].strip();
	        BitVecExpr jumpAddr = SMTHelper.get_jump_address(store, jmpAddrStr, addrExtFuncMap);
	        Long newAddr = null;
	        if(Helper.is_bit_vec_num(jumpAddr)) {
	        	newAddr = Helper.long_of_sym(jumpAddr);
	        }
	        if(newAddr != null && addrExtFuncMap.containsKey(newAddr)) {
	            haltPoint = jumpToExtFunc(store, symNames);
	        }
	    }
	    ArrayList<String> newSrcs = new ArrayList<String>();
	    for(String srcName : srcNames) {
	    	if(!newSrcs.contains(srcName))
	    		newSrcs.add(srcName);
	    }
	    return new Triplet<>(haltPoint, newSrcs, memLenMap);
	}

}
