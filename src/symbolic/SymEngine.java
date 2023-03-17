package symbolic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.function.Function;

import com.microsoft.z3.BitVecExpr;

import block.Store;
import common.Config;
import common.Helper;
import common.Lib;
import common.Tuple;
import common.Utils;
import common.Triplet;

public class SymEngine {

	static HashSet<String> OPS_NEED_EXTENSION = new HashSet<String>();
	static HashMap<String, Function<Triplet<BitVecExpr, BitVecExpr, Integer>, BitVecExpr>> SYM_BIN_OP_MAP = new HashMap<String, Function<Triplet<BitVecExpr, BitVecExpr, Integer>, BitVecExpr>>();
	
	static {
		OPS_NEED_EXTENSION.add("<<");
		OPS_NEED_EXTENSION.add(">>");
		OPS_NEED_EXTENSION.add(">>>");
		
		SYM_BIN_OP_MAP.put("+", operand -> Helper.bv_add(operand.x, operand.y));
		SYM_BIN_OP_MAP.put("-", operand -> Helper.bv_sub(operand.x, operand.y));
		SYM_BIN_OP_MAP.put("&", operand -> Helper.bv_and(operand.x, operand.y));
		SYM_BIN_OP_MAP.put("|", operand -> Helper.bv_or(operand.x, operand.y));
		SYM_BIN_OP_MAP.put("^", operand -> Helper.bv_xor(operand.x, operand.y));
		SYM_BIN_OP_MAP.put(">>", operand -> Helper.bv_arith_rshift(operand.x, operand.y));
		SYM_BIN_OP_MAP.put("<<", operand -> Helper.bv_lshift(operand.x, operand.y));
		SYM_BIN_OP_MAP.put(">>>", operand -> Helper.bv_logic_rshift(operand.x, operand.y));
		SYM_BIN_OP_MAP.put("smul", operand -> Helper.bv_mult(Helper.sign_ext(operand.z, operand.x), Helper.sign_ext(operand.z, operand.y)));
		SYM_BIN_OP_MAP.put("umul", operand -> Helper.bv_mult(Helper.zero_ext(operand.z, operand.x), Helper.zero_ext(operand.z, operand.y)));
		SYM_BIN_OP_MAP.put("sdiv", operand -> Helper.extract(operand.z / 2 - 1, 0, Helper.bv_sdiv(operand.x, Helper.sign_ext(operand.z / 2, operand.y))));
		SYM_BIN_OP_MAP.put("udiv", operand -> Helper.extract(operand.z / 2 - 1, 0, Helper.bv_udiv(operand.x, Helper.zero_ext(operand.z / 2, operand.y))));
		SYM_BIN_OP_MAP.put("smod", operand -> Helper.extract(operand.z / 2 - 1, 0, Helper.bv_smod(operand.x, Helper.sign_ext(operand.z / 2, operand.y))));
		SYM_BIN_OP_MAP.put("umod", operand -> Helper.extract(operand.z / 2 - 1, 0, Helper.bv_umod(operand.x, Helper.zero_ext(operand.z / 2, operand.y))));
	}
	
	public static BitVecExpr get_sym(Store store, long rip, String src, int block_id) {
		return get_sym(store, rip, src, block_id, Config.MEM_ADDR_SIZE);
	}
	

	public static BitVecExpr get_sym(Store store, long rip, String src, int block_id, int length) {
	    BitVecExpr res = null;
	    if(Lib.REG_NAMES.contains(src)) // rax
	        res = SymRegister.get_register_sym(store, src);
	    else if(Utils.imm_pat.matcher(src).matches()) {    //0x123456
	        long val = Utils.imm_str_to_int(src);
	        res = Helper.gen_bv_num(val, length);
	    }
	    else if(src.contains("s:")) {       //fs:rax
	        String[] src_split = src.split(":");
	        String seg_reg = Utils.rsplit(src_split[0], " ")[1].strip();
	        String src_split_1 = src_split[1].strip();
	        BitVecExpr val = null;
	        if(src_split_1.endsWith("]")) {
	            val = SymMemory.get_effective_address(store, rip, src_split_1, Config.MEM_ADDR_SIZE);
	        }
	        else
	            val = get_sym(store, rip, src_split_1, block_id, Config.MEM_ADDR_SIZE);
	        BitVecExpr address = val;
	        res = SymMemory.get_seg_memory_val(store, address, seg_reg, length);
	    }
	    else if(src.endsWith("]")) { // byte ptr [rbx+rax*1]
	        BitVecExpr address = SymMemory.get_effective_address(store, rip, src, Config.MEM_ADDR_SIZE);
	        res = SymMemory.get_memory_val(store, address, block_id, length);
	    }
	    else if(src.contains(":")) {     // rdx:rax
	        String[] regs = src.split(":");
	        BitVecExpr left = SymRegister.get_register_sym(store, regs[0]);
	        BitVecExpr right = SymRegister.get_register_sym(store, regs[1]);
	        res = Helper.concat(left, right);
	    }
	    return res;
	}


	public static Integer get_sym_block_id(Store store, long rip, String src) {
	    Integer res = null;
	    if(Lib.REG_NAMES.contains(src)) // rax
	        res = SymRegister.get_reg_sym_block_id(store, src);
	    else if(Utils.imm_pat.matcher(src).matches()) {}  // 0x123
	    else if(src.contains("s:")) {}       //fs:rax
	    else if(src.endsWith("]")) { // byte ptr [rbx+rax*1]
	        BitVecExpr address = SymMemory.get_effective_address(store, rip, src, Config.MEM_ADDR_SIZE);
	        res = SymMemory.get_mem_sym_block_id(store, address);
	    }
	    else if(src.contains(":")) {    // rdx:rax
	        String[] regs = src.split(":");
	        Integer left = SymRegister.get_reg_sym_block_id(store, regs[0]);
//	        Integer right = SymRegister.get_reg_sym_block_id(store, regs[1]);
	        res = left;
	    }
	    return res;
	}


	public static BitVecExpr get_register_sym(Store store, String src) {
	    return SymRegister.get_register_sym(store, src);
	}

	public static BitVecExpr get_memory_val(Store store, BitVecExpr address, int block_id, int length) {
	    return SymMemory.get_memory_val(store, address, block_id, length);
	}

	public static void set_sym(Store store, long rip, String dest, BitVecExpr sym, int block_id) {
	    if(Lib.REG_NAMES.contains(dest)) {        // rax
	        int dest_len = Utils.get_sym_length(dest, Config.MEM_ADDR_SIZE);
	        if(sym.getSortSize() > dest_len)
	            sym = Helper.extract(dest_len - 1, 0, sym);
	        SymRegister.set_register_sym(store, dest, sym, block_id);
	    }
	    else if(dest.contains("s:")) {       // fs:rax
	        String[] destSplit = dest.split(":");
	        String seg_reg = Utils.rsplit(destSplit[0], " ")[1].strip();
	        // seg_reg_val = SymRegister.get_segment_reg_val(store, seg_reg)
	        String dest_rest = destSplit[1].strip();
	        BitVecExpr val = null;
	        if(dest_rest.endsWith("]"))
	            val = SymMemory.get_effective_address(store, rip, dest_rest, Config.MEM_ADDR_SIZE);
	        else {
	            int rest_len = Utils.get_sym_length(dest_rest, Config.MEM_ADDR_SIZE);
	            val = get_sym(store, rip, dest_rest, block_id, rest_len);
	        }
	        BitVecExpr address = val;
	        store.set_seg_val(seg_reg, address, sym);
	    }
	    else if(dest.endsWith("]")) {
	        int dest_len = Utils.get_sym_length(dest, Config.MEM_ADDR_SIZE);
	        BitVecExpr address = SymMemory.get_effective_address(store, rip, dest, Config.MEM_ADDR_SIZE);
	        SymMemory.set_mem_sym(store, address, sym, block_id, dest_len);
	    }
	    else if(dest.contains(":")) {     // rax:rdx
	        String[] destSplit = dest.split(":");
	        int reg_len = Utils.get_sym_length(destSplit[0], Config.MEM_ADDR_SIZE);
	        BitVecExpr left = Helper.extract(reg_len + reg_len - 1, reg_len, sym);
	        BitVecExpr right = Helper.extract(reg_len - 1, 0, sym);
	        SymRegister.set_register_sym(store, destSplit[0], left, block_id);
	        SymRegister.set_register_sym(store, destSplit[1], right, block_id);
	    }
	}
	    

	public static BitVecExpr get_effective_address(Store store, long rip, String operand) {
	    return SymMemory.get_effective_address(store, rip, operand, Config.MEM_ADDR_SIZE);
	}


	public static BitVecExpr get_jump_table_address(Store store, String arg, BitVecExpr src_sym, BitVecExpr src_val, int length) {
	    return SymMemory.get_jump_table_address(store, arg, src_sym, src_val, length);
	}


	public static BitVecExpr read_memory_val(Store store, BitVecExpr address, int block_id, int length) {
	    return SymMemory.read_memory_val(store, address, block_id, length);
	}


	void reset_mem_content_pollute(Store store, int block_id) {
	    SymHelper.reset_mem_content_pollute(store, block_id);
	}
	    

	public static void set_mem_sym(Store store, BitVecExpr address, BitVecExpr sym, int block_id) {
	    SymMemory.set_mem_sym(store, address, sym, block_id, Config.MEM_ADDR_SIZE);
	}
	
	public void set_mem_sym(Store store, BitVecExpr address, BitVecExpr sym, int block_id, int length) {
	    SymMemory.set_mem_sym(store, address, sym, block_id, length);
	}


	public BitVecExpr get_mem_sym(Store store, BitVecExpr address, int length) {
	    return SymMemory.get_mem_sym(store, address, length, Lib.MEM);
	}
	
	public static BitVecExpr get_mem_sym(Store store, BitVecExpr address) {
	    return SymMemory.get_mem_sym(store, address, Config.MEM_ADDR_SIZE, Lib.MEM);
	}


	public static BitVecExpr sym_bin_op(Store store, long rip, String op, String dest, String src, int block_id) {
		Function<Triplet<BitVecExpr, BitVecExpr, Integer>, BitVecExpr> func = SYM_BIN_OP_MAP.get(op);
		Tuple<Integer, Integer> dest_src_len = get_dest_src_length(store, rip, dest, src);
		int dest_len = dest_src_len.x;
		int src_len = dest_src_len.y;
		Tuple<BitVecExpr, BitVecExpr> dest_src_sym = get_dest_src_sym(store, rip, dest, src, block_id);
		BitVecExpr sym_dest = dest_src_sym.x;
		BitVecExpr sym_src = dest_src_sym.y;
	    if(OPS_NEED_EXTENSION.contains(op) && dest_len != src_len)
	        sym_src = extension_sym(sym_src, dest_len, src_len, false);
	    BitVecExpr res = (BitVecExpr) func.apply(new Triplet<BitVecExpr, BitVecExpr, Integer>(sym_dest, sym_src, dest_len)).simplify();
	    res = (BitVecExpr) res.simplify();
	    return res;
	}


	public static BitVecExpr extension(Store store, long rip, String src, int block_id, int dest_len, boolean sign) {
	    int src_len = Utils.get_sym_length(src, Config.MEM_ADDR_SIZE);
	    BitVecExpr sym_src = get_sym(store, rip, src, block_id, src_len);
	    BitVecExpr res = extension_sym(sym_src, dest_len, src_len, sign);
	    return res;
	}


	public static BitVecExpr extension_sym(BitVecExpr sym, int dest_len, int src_len, boolean sign) {
		BitVecExpr res = null;
	    if(Helper.is_bottom(sym, src_len))
	        return Helper.bottom(dest_len);
	    int len_diff = dest_len - src_len;
	    if(sign)
	        res = Helper.sign_ext(len_diff, sym);
	    else
	    	res = Helper.zero_ext(len_diff, sym);
	    return res;
	}


	public static void undefined(Store store, long rip, int block_id, ArrayList<String> args) {
	    if(args.size() > 0) {
	        String dest = args.get(0);
	        int dest_len = Utils.get_sym_length(dest, Config.MEM_ADDR_SIZE);
	        set_sym(store, rip, dest, Helper.bottom(dest_len), block_id);
	    }
	}

	
	public static Tuple<Integer, Integer> get_dest_src_length(Store store, long rip, String dest, String src) {
	    int dest_len = Utils.get_sym_length(dest, Config.MEM_ADDR_SIZE);
	    int src_len = Utils.get_sym_length(src, dest_len);
	    return new Tuple<Integer, Integer>(dest_len, src_len);
	}
	

	public static Tuple<BitVecExpr, BitVecExpr> get_dest_src_sym(Store store, long rip, String dest, String src, int block_id) {
		int dest_len = Utils.get_sym_length(dest, Config.MEM_ADDR_SIZE);
		int src_len = Utils.get_sym_length(src, dest_len);
	    BitVecExpr sym_src = get_sym(store, rip, src, block_id, src_len);
	    BitVecExpr sym_dest = get_sym(store, rip, dest, block_id, dest_len);
	    return new Tuple<BitVecExpr, BitVecExpr>(sym_dest, sym_src);
	}

}
