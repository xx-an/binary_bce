package semantics;

import common.Lib;
import common.Triplet;
import common.Tuple;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.function.Consumer;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;

import common.Config;
import common.Utils;
import symbolic.SymHelper;
import symbolic.SymEngine;
import common.Helper;

import block.Store;

public class Semantics {

	static long rip = 0;
	static int block_id = 0;
	static HashMap<String, Consumer<Tuple<Store, ArrayList<String>>>> INSTRUCTION_SEMANTICS_MAP = new HashMap<String, Consumer<Tuple<Store, ArrayList<String>>>>();
	
	Semantics() {
		INSTRUCTION_SEMANTICS_MAP.put("mov", arg -> mov(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("lea", arg -> lea(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("push", arg -> push(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("pusha", arg -> pusha(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("pushad", arg -> pushad(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("pop", arg -> pop(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("popa", arg -> popa(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("popad", arg -> popad(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("add", arg -> sym_bin_oprt(arg.x, "+", block_id, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("sub", arg -> sym_bin_oprt(arg.x, "-", block_id, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("xor", arg -> sym_bin_oprt(arg.x, "^", block_id, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("and", arg -> sym_bin_oprt(arg.x, "&", block_id, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("or", arg -> sym_bin_oprt(arg.x, "|", block_id, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("sar", arg -> sym_bin_oprt(arg.x, ">>", block_id, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("shr", arg -> sym_bin_oprt(arg.x, ">>>", block_id, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("sal", arg -> sym_bin_oprt(arg.x, "<<", block_id, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("shl", arg -> sym_bin_oprt(arg.x, "<<<", block_id, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("xchg", arg -> xchg(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("neg", arg -> neg(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("not", arg -> not_op(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("test", arg -> test(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("cmp", arg -> cmp_op(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("imul", arg -> imul(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("mul", arg -> mul(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("idiv", arg -> div(arg.x, true, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("div", arg -> div(arg.x, false, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("cmpxchg", arg -> cmpxchg(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("movabs", arg -> mov(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("movzx", arg -> mov_ext(arg.x, false, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("movsx", arg -> mov_ext(arg.x, true, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("movsxd", arg -> mov_ext(arg.x, true, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("cbw", arg -> cdqe(arg.x, 8));
		INSTRUCTION_SEMANTICS_MAP.put("cwde", arg -> cdqe(arg.x, 16));
		INSTRUCTION_SEMANTICS_MAP.put("cdqe", arg -> cdqe(arg.x, 32));
		INSTRUCTION_SEMANTICS_MAP.put("leave", arg -> leave(arg.x));
		INSTRUCTION_SEMANTICS_MAP.put("inc", arg -> inc_dec(arg.x, "+", arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("dec", arg -> inc_dec(arg.x, "-", arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("adc", arg -> sym_bin_op_with_cf(arg.x, "+", arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("sbb", arg -> sym_bin_op_with_cf(arg.x, "-", arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("cwd", arg -> cdq(arg.x, 16));
		INSTRUCTION_SEMANTICS_MAP.put("cdq", arg -> cdq(arg.x, 32));
		INSTRUCTION_SEMANTICS_MAP.put("cqo", arg -> cdq(arg.x, 64));
		INSTRUCTION_SEMANTICS_MAP.put("ror", arg -> rotate(arg.x, false, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("rol", arg -> rotate(arg.x, true, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("bt", arg -> bt(arg.x, arg.y));
		INSTRUCTION_SEMANTICS_MAP.put("call", arg -> call(arg.x, arg.y));
	}
	
	
	void sym_bin_oprt(Store store, String op, int block_id, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		sym_bin_oprt(store, op, dest, src, block_id);
	}
	
	void sym_bin_oprt(Store store, String op, String dest, String src, int block_id) {
		int dest_len = Utils.get_sym_length(dest, Config.MEM_ADDR_SIZE);
	    BitVecExpr res = SMTHelper.sym_bin_op_na_flags(store, rip, op, dest, src, block_id);
	    SMTHelper.modify_status_flags(store, res, dest_len);
	    SMTHelper.set_CF_flag(store, rip, dest, src, block_id, op);
	    SMTHelper.set_OF_flag(store, rip, dest, src, res, block_id, op);
	}


	void mov(Store store, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		mov_op(store, dest, src);
	}
	
	void mov_op(Store store, String dest, String src) {
	    int dest_len = Utils.get_sym_length(dest, Config.MEM_ADDR_SIZE);
	    BitVecExpr sym_src = SymEngine.get_sym(store, rip, src, block_id, dest_len);
	    SymEngine.set_sym(store, rip, dest, sym_src, block_id);
	}


	void lea(Store store, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
	    BitVecExpr address = SymEngine.get_effective_address(store, rip, src);
	    SymEngine.set_sym(store, rip, dest, address, block_id);
	}


	void pop(Store store, ArrayList<String> arg) {
		String dest = arg.get(0);
		pop(store, dest);
	}
	
	void pop(Store store, String dest) {
		int dest_len = Utils.get_sym_length(dest);
		BitVecExpr sym_rsp = SMTHelper.get_sym_rsp(store, rip);
//				SymEngine.get_sym(store, rip, "rsp", block_id);
		BitVecExpr res = SymEngine.get_mem_sym(store, sym_rsp);
	    if(res == null)
	        res = Helper.gen_sym(Config.MEM_ADDR_SIZE);
	    SymEngine.set_sym(store, rip, dest, res, block_id);
	    SMTHelper.sym_bin_op_na_flags(store, rip, "+", Config.ADDR_SIZE_SP_MAP.get(Config.MEM_ADDR_SIZE), 
	    		String.valueOf(dest_len / 8), block_id);
	}
	
	void popad(Store store, ArrayList<String> arg) {
	    pop(store, "edi");
	    pop(store, "esi");
	    pop(store, "ebp");
	    SMTHelper.sym_bin_op_na_flags(store, rip, "+", "esp", "4", block_id);
	    pop(store, "ebx");
	    pop(store, "edx");
	    pop(store, "ecx");
	    pop(store, "eax");
	}


	void popa(Store store, ArrayList<String> arg) {
	    pop(store, "di");
	    pop(store, "si");
	    pop(store, "bp");
	    SMTHelper.sym_bin_op_na_flags(store, rip, "+", "sp", "2", block_id);
	    pop(store, "bx");
	    pop(store, "dx");
	    pop(store, "cx");
	    pop(store, "ax");
	}


	void push(Store store, ArrayList<String> arg) {
		String src = arg.get(0);
		push(store, src);
	}
	
	void push(Store store, String src) {
	    BitVecExpr sym_src = SymEngine.get_sym(store, rip, src, block_id);
	    SMTHelper.push_val(store, rip, sym_src, block_id);
	}
	
	void pushad(Store store, ArrayList<String> arg) {
	    BitVecExpr sym_rsp = SymEngine.get_sym(store, rip, "esp", block_id, 32);
	    push(store, "eax");
	    push(store, "ecx");
	    push(store, "edx");
	    push(store, "ebx");
	    push(store, sym_rsp.toString());
	    push(store, "ebp");
	    push(store, "esi");
	    push(store, "edi");
	}


	void pusha(Store store, ArrayList<String> arg) {
		BitVecExpr sym_rsp = SymEngine.get_sym(store, rip, "sp", block_id, 16);
	    push(store, "ax");
	    push(store, "cx");
	    push(store, "dx");
	    push(store, "bx");
	    push(store, sym_rsp.toString());
	    push(store, "bp");
	    push(store, "si");
	    push(store, "di");
	}


	void call(Store store, ArrayList<String> arg) {
	    push(store, Long.toHexString(rip));
	}


	void call_op(Store store, long rip, int block_id) {
		BitVecExpr sym_src = SymEngine.get_sym(store, rip, Long.toHexString(rip), block_id);
	    SMTHelper.push_val(store, rip, sym_src, block_id);
	}


	Long[] ret(Store store, int block_id) {
		Long[] result;
		Long res = null;
		Long alter_res = null;
		BitVecExpr sym_rsp = SMTHelper.get_sym_rsp(store, rip);
		BitVecExpr mem_at_rsp = SymEngine.get_mem_sym(store, sym_rsp);
		if(mem_at_rsp != null) {
	        SymHelper.remove_memory_content(store, sym_rsp);
		}
	    SMTHelper.sym_bin_op_na_flags(store, rip, "+", Config.ADDR_SIZE_SP_MAP.get(Config.MEM_ADDR_SIZE), Integer.toString(Config.MEM_ADDR_SIZE / 8), block_id);  
	    if(mem_at_rsp != null) {
	    	if(Config.MEM_ADDR_SIZE == 16) {
	    		mem_at_rsp = Helper.bv_and(mem_at_rsp, 0x0000ffff);
	    	}
	    	if(Helper.is_bit_vec_num(mem_at_rsp))
	            res = Helper.long_of_sym(mem_at_rsp);
	    }
	    if(!store.g_FuncCallStack.isEmpty())
	        alter_res = store.g_FuncCallStack.remove(store.g_FuncCallStack.size() - 1);
	    result = new Long[]{res, alter_res};
	    return result;
	}


	void xchg(Store store, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
	    if(dest == src) return;
	    Tuple<BitVecExpr, BitVecExpr> dest_src_sym = SymEngine.get_dest_src_sym(store, rip, dest, src, block_id);
	    SymEngine.set_sym(store, rip, dest, dest_src_sym.y, block_id);
	    SymEngine.set_sym(store, rip, src, dest_src_sym.x, block_id);
	}


	void leave(Store store) {
	    if(Config.MEM_ADDR_SIZE == 64) {
	    	mov_op(store, "rsp", "rbp");
		    pop(store, "rbp");
	    }
	    else if(Config.MEM_ADDR_SIZE == 32) {
	    	mov_op(store, "esp", "ebp");
	        pop(store, "ebp");
	    }
	    else if(Config.MEM_ADDR_SIZE == 16) {
	    	mov_op(store, "sp", "bp");
	        pop(store, "bp");
	    }
	}
	

	void cdqe(Store store, int length) {
		String src = Lib.AUX_REG_INFO.get(length).x;
		String dest = Lib.AUX_REG_INFO.get(length * 2).x;
	    BitVecExpr res = SymEngine.extension(store, rip, src, block_id, length * 2, true);
	    SymEngine.set_sym(store, rip, dest, res, block_id);
	}


	void mov_ext(Store store, boolean signed, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
	    int src_len = Utils.get_sym_length(src);
	    BitVecExpr sym_src = SymEngine.get_sym(store, rip, src, block_id, src_len);
	    int dest_len = Utils.get_sym_length(dest);
	    mov_op(store, dest, dest_len, sym_src, src_len, signed);
	}


	public static void mov_op(Store store, String dest, int dest_len, BitVecExpr sym_src, int src_len, boolean signed) {
	    BitVecExpr sym = SymEngine.extension_sym(sym_src, dest_len, src_len, signed);
	    SymEngine.set_sym(store, rip, dest, sym, block_id);
	}


	void mul(Store store, ArrayList<String> arg) {
		String src = arg.get(0);
	    int bits_len = Utils.get_sym_length(src, Config.MEM_ADDR_SIZE);
	    Triplet<String, String, String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String a_reg = reg_info.x;
	    String dest = reg_info.z;
	    BitVecExpr res = SymEngine.sym_bin_op(store, rip, "umul", a_reg, src, block_id);
	    SymEngine.set_sym(store, rip, dest, res, block_id);
	    BoolExpr eq = Helper.is_equal(Helper.upper_half(res), 0);
	    SMTHelper.set_mul_OF_CF_flags(store, eq);
	}


	void imul(Store store, ArrayList<String> arg) {
		String src = arg.get(0);
		String src1 = arg.get(1);
		String src2 = arg.get(2);
		String dest = null;
	    int bits_len = Utils.get_sym_length(src, Config.MEM_ADDR_SIZE);
	    BitVecExpr res = null;
	    BitVecExpr tmp = null;
	    if(src1 != null) {
	        if(src2 == null)
	            tmp = SymEngine.sym_bin_op(store, rip, "smul", src, src1, block_id);
	        else
	            tmp = SymEngine.sym_bin_op(store, rip, "smul", src1, src2, block_id);
	        res = Helper.extract(bits_len - 1, 0, tmp);
	        SymEngine.set_sym(store, rip, src, res, block_id);
	        dest = src;
	    }
	    else {
	    	Triplet<String, String, String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
		    String a_reg = reg_info.x;
		    dest = reg_info.z;
	        tmp = SymEngine.sym_bin_op(store, rip, "smul", a_reg, src, block_id);
	        res = Helper.extract(bits_len - 1, 0, tmp);
	        SymEngine.set_sym(store, rip, dest, tmp, block_id);
	    }
	    BoolExpr eq = Helper.is_equal(Helper.sign_ext(bits_len, res), tmp);
	    SMTHelper.set_mul_OF_CF_flags(store, eq);
	}


	void div(Store store, boolean signed, ArrayList<String> arg) {
		String src = arg.get(0);
	    int bits_len = Utils.get_sym_length(src, Config.MEM_ADDR_SIZE);
	    Triplet<String, String, String> reg_info = Lib.AUX_REG_INFO.get(bits_len);
	    String qreg = reg_info.x;
	    String rreg = reg_info.y;
	    String dest = reg_info.z;
	    String div_op_name = (signed) ? "sdiv" : "udiv";
	    String rem_op_name = (signed) ? "smod" : "umod";
	    BitVecExpr quotient = SymEngine.sym_bin_op(store, rip, div_op_name, dest, src, block_id);
	    BitVecExpr remainder = SymEngine.sym_bin_op(store, rip, rem_op_name, dest, src, block_id);
	    SymEngine.set_sym(store, rip, qreg, quotient, block_id);
	    SymEngine.set_sym(store, rip, rreg, remainder, block_id);
	    SMTHelper.reset_all_flags(store);
	}


	void cmpxchg(Store store, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
	    int bits_len = Utils.get_sym_length(dest, Config.MEM_ADDR_SIZE);
	    String a_reg = Lib.AUX_REG_INFO.get(bits_len).x;
	    BitVecExpr sym_lhs = SymEngine.get_sym(store, rip, a_reg, block_id, bits_len);
	    BitVecExpr sym_rhs = SymEngine.get_sym(store, rip, dest, block_id, bits_len);
	    BoolExpr eq = Helper.is_equal(sym_lhs, sym_rhs);
	    if(eq == Helper.sym_true()) {
	        SMTHelper.set_flag_direct(store, "ZF", Helper.sym_true());
	        mov_op(store, dest, src);
	    }
	    else if(eq == Helper.sym_false()) {
	        SMTHelper.set_flag_direct(store, "ZF", Helper.sym_false());
	        mov_op(store, a_reg, dest);
	    }
	    else {
	        SMTHelper.set_flag_direct(store, "ZF", null);
	        SymEngine.set_sym(store, rip, dest, Helper.gen_sym(bits_len), block_id);
	        SymEngine.set_sym(store, rip, a_reg, Helper.gen_sym(bits_len), block_id);
	    }
	}


	void cmov(Store store, long curr_rip, String inst, boolean pred, int curr_block_id) {
	    block_id = curr_block_id;
	    String[] inst_split = inst.strip().split(" ", 1);
	    ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	    String dest = inst_args.get(0);
	    if(pred)
	        mov_op(store, dest, inst_args.get(1));
	}


	static void set_op(Store store, String inst, String dest) {
	    int dest_len = Utils.get_sym_length(dest);
	    BoolExpr res = SMTHelper.parse_predicate(store, inst, true, "set");
	    if(res == Helper.sym_false())
	        SymEngine.set_sym(store, rip, dest, Helper.gen_bv_num(0, dest_len), block_id);
	    else if(res == Helper.sym_true())
	        SymEngine.set_sym(store, rip, dest, Helper.gen_bv_num(1, dest_len), block_id);
	    else
	        SymEngine.set_sym(store, rip, dest, Helper.gen_sym(dest_len), block_id);
	}


	static void rep(Store store, String inst_name, String inst) {
		BitVecExpr sym_rcx = SymEngine.get_sym(store, rip, "rcx", block_id);
	    BoolExpr rcx_is_0 = Helper.is_equal(sym_rcx, 0);
	    while(rcx_is_0 == Helper.sym_false()) {
	        int res = parse_semantics(store, rip, inst, block_id);
	        if(res == -1) break;
	        sym_rcx = SMTHelper.sym_bin_op_na_flags(store, rip, "-", "rcx", "1", block_id);
	        rcx_is_0 = Helper.is_equal(sym_rcx, 0);
	        if(rcx_is_0 == Helper.sym_true())
	            break;
	        BoolExpr sym_zf = SMTHelper.get_flag_direct(store, "ZF");
	        if((inst_name == "repz" || inst_name == "repe") && sym_zf == Helper.sym_false())
	            break;
	        else if((inst_name == "repnz" || inst_name == "repne") && sym_zf == Helper.sym_true())
	            break;
	    }
	}


	void cmp_op(Store store, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		int dest_len = Utils.get_sym_length(dest, Config.MEM_ADDR_SIZE);
		Tuple<BitVecExpr, BitVecExpr> dest_src_sym = SymEngine.get_dest_src_sym(store, rip, dest, src, block_id);
		BitVecExpr sym_dest = dest_src_sym.x;
		BitVecExpr sym_src = dest_src_sym.y;
		BitVecExpr res = SymEngine.sym_bin_op(store, rip, "-", dest, src, block_id);
	    // if(isinstance(res, BitVecNumRef) {
	    //     if(not isinstance(sym_dest, BitVecNumRef) && not isinstance(sym_src, BitVecNumRef) {
	    //         tmp = res.as_long()
	    //         if(tmp != 0:
	    //             res = SymHelper.gen_sym()
	    //             SymEngine.set_sym(store, rip, src, SymHelper.gen_sym())
	    SMTHelper.modify_status_flags(store, res, dest_len);
	    SMTHelper.set_CF_flag(store, rip, dest, src, block_id, "-");
	    SMTHelper.set_OF_flag(store, rip, dest, src, res, block_id, "-");
	    // Utils.logger.debug("cmp_op")
	    // SMTHelper.pp_flags(store)
	}


	void sym_bin_op_with_cf(Store store, String op, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
	    int dest_len = Utils.get_sym_length(dest);
	    sym_bin_oprt(store, op, dest, src, block_id);
	    BoolExpr carry_val = SMTHelper.get_flag_direct(store, "CF");
	    if(carry_val == Helper.sym_true())
	        sym_bin_oprt(store, op, dest, "1", block_id);
	    else if(carry_val == Helper.sym_false()) {}
	    else
	        SymEngine.set_sym(store, rip, dest, Helper.gen_sym(dest_len), block_id);
	}


	void test(Store store, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
		BitVecExpr res = SymEngine.sym_bin_op(store, rip, "&", dest, src, block_id);
	    int dest_len = Utils.get_sym_length(dest);
	    SMTHelper.modify_status_flags(store, res, dest_len);
	    SMTHelper.set_test_OF_CF_flags(store);
	}


	void neg(Store store, ArrayList<String> arg) {
		String dest = arg.get(0);
	    int dest_len = Utils.get_sym_length(dest);
	    BitVecExpr sym_dest = SymEngine.get_sym(store, rip, dest, block_id, dest_len);
	    BoolExpr eq = Helper.not_equal(sym_dest, 0);
	    SMTHelper.set_flag_val(store, "CF", eq);
	    SymEngine.set_sym(store, rip, dest, Helper.neg(sym_dest), block_id);
	}


	void not_op(Store store, ArrayList<String> arg) {
		String dest = arg.get(0);
	    int dest_len = Utils.get_sym_length(dest);
	    BitVecExpr sym_dest = SymEngine.get_sym(store, rip, dest, block_id, dest_len);
	    SymEngine.set_sym(store, rip, dest, Helper.not_op(sym_dest), block_id);
	}

	
	void inc_dec(Store store, String op, ArrayList<String> arg) {
		String dest = arg.get(0);
	    int dest_len = Utils.get_sym_length(dest);
	    BitVecExpr res = SymEngine.sym_bin_op(store, rip, op, dest, "1", block_id);
	    SymEngine.set_sym(store, rip, dest, res, block_id);
	    SMTHelper.modify_status_flags(store, res, dest_len);
	    SMTHelper.set_OF_flag(store, rip, dest, "1", res, block_id, op);
	}


	void rotate(Store store, boolean to_left, ArrayList<String> arg) {
		String dest = arg.get(0);
		String src = arg.get(1);
	    int dest_len = Utils.get_sym_length(dest);
	    BitVecExpr bv_count = SymEngine.get_sym(store, rip, src, block_id, 8);
	    if(Helper.is_bit_vec_num(bv_count)) {
	        int count = Helper.int_of_sym(bv_count);
	        int mask = (dest_len == 64) ? 0x3f : 0x1f;
	        int temp = (count & mask) % dest_len;
	        BitVecExpr sym_dest = SymEngine.get_sym(store, rip, dest, block_id, dest_len);
	        while(temp != 0) {
	        	BoolExpr tmp = null;
	            if(to_left) {
	                tmp = Helper.most_significant_bit(sym_dest, dest_len);
	                sym_dest = Helper.bv_lshift(sym_dest, 1);
	                if(tmp == Helper.sym_true())
	                    sym_dest = Helper.bv_add(sym_dest, 1);
	            }
	            else {
	                tmp = Helper.least_significant_bit(sym_dest, dest_len);
	                sym_dest = Helper.bv_arith_rshift(sym_dest, 1);
	                if(tmp == Helper.sym_true())
	                	sym_dest = Helper.bv_add(sym_dest, (1 << dest_len));
	            }
	            temp -= 1;
	        }
	        SymEngine.set_sym(store, rip, dest, sym_dest, block_id);
	        BoolExpr cf_val = null;
	        if((count & mask) != 0) {
	            if(to_left)
	                cf_val = Helper.least_significant_bit(sym_dest, dest_len);
	            else
	                cf_val = Helper.most_significant_bit(sym_dest, dest_len);
	            SMTHelper.set_flag_val(store, "CF", cf_val);
	        }
	        if((count & mask) == 1) {
	        	BoolExpr of_val = null;
	        	if(to_left)
	                of_val = Helper.bv_xor(Helper.most_significant_bit(sym_dest, dest_len), cf_val);
	            else
	                of_val = Helper.bv_xor(Helper.most_significant_bit(sym_dest, dest_len), Helper.smost_significant_bit(sym_dest, dest_len));
	            SMTHelper.set_flag_val(store, "OF", of_val);
	        }
	        else
	            SMTHelper.set_flag_direct(store, "OF", null);
	    }
	    else
	        SymEngine.set_sym(store, rip, dest, Helper.gen_sym(dest_len), block_id);
	}


	void cdq(Store store, int length) {
		Triplet<String, String, String> reg_info = Lib.AUX_REG_INFO.get(length);
		String src = reg_info.x;
		String dest = reg_info.z;
	    BitVecExpr res = SymEngine.extension(store, rip, src, block_id, length * 2, true);
	    SymEngine.set_sym(store, rip, dest, res, block_id);
	}


	void bt(Store store, ArrayList<String> arg) {
		String bit_base = arg.get(0);
		String bit_offset = arg.get(1);
		BitVecExpr sym_base = SymEngine.get_sym(store, rip, bit_base, block_id);
		BitVecExpr sym_offset = SymEngine.get_sym(store, rip, bit_offset, block_id);
	    int offset_size = Utils.get_sym_length(bit_offset);
	    SMTHelper.reset_all_flags_except_one(store, "ZF");
	    if(Helper.is_bit_vec_num(sym_offset)) {
	        int offset = Helper.int_of_sym(sym_offset);
	        offset = offset % offset_size;
	        BitVecExpr bit_selected = Helper.bit_ith(sym_base, offset);
	        BoolExpr res = Helper.is_equal(bit_selected, 1);
	        SMTHelper.set_flag_val(store, "CF", res);
	    }
	    else
	        SMTHelper.set_flag_val(store, "CF", null);
	}


	public static int parse_semantics(Store store, long curr_rip, String curr_inst, int curr_block_id) {
	    rip = curr_rip;
	    block_id = curr_block_id;
	    String inst = curr_inst;
	    if(inst.startsWith("lock ")) {
	        inst = inst.split(" ", 1)[1];
	    }
	    String[] inst_split = inst.strip().split(" ", 1);
	    String inst_name = inst_split[0];
	    if(INSTRUCTION_SEMANTICS_MAP.containsKey(inst_name)) {
	    	Consumer<Tuple<Store, ArrayList<String>>> inst_op = INSTRUCTION_SEMANTICS_MAP.get(inst_name);
	        ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        inst_op.accept(new Tuple<Store, ArrayList<String>>(store, inst_args));
	    }
	    else if(inst_name == "nop" || inst_name == "hlt") {}
	    else if(inst_name.startsWith("set")) {
	    	ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	    	set_op(store, inst, inst_args.get(0));
	    }
	    else if(inst_name.startsWith("rep")) {
	        String rep_inst = inst_split[1].strip();
	        rep(store, inst_name, rep_inst);
	    }
	    else if(inst_name.startsWith("cmp")) {
	        SMTHelper.reset_all_flags(store);
	        return -1;
	    }
	    else {
	    	ArrayList<String> inst_args = Utils.parse_inst_args(inst_split);
	        SymEngine.undefined(store, rip, block_id, inst_args);
	        SMTHelper.reset_all_flags(store);
	        return -1;
	    }
	    return 0;
	}

}
