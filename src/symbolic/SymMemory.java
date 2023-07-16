package symbolic;

import java.util.ArrayList;
import java.util.Collections;
import java.util.regex.Pattern;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;

import binary.BinaryContent;
import block.Store;
import common.Config;
import common.Helper;
import common.Lib;
import common.Utils;
import normalizer.NormHelper;

public class SymMemory {

	static Pattern letter_num_neg_pat = Pattern.compile("\\w+");
	static Pattern sym_pat = Pattern.compile("\\W+");

	static BitVecExpr get_sym_val(String arg, Store store, int length) {
		BitVecExpr res = null;
	    if(Lib.REG_NAMES.contains(arg)) {
	        res = SymRegister.getRegSymAddr(store, arg);
	    }
	    else if(Utils.imm_pat.matcher(arg).matches())
	    	res = Helper.gen_bv_num(Utils.imm_str_to_int(arg), length);
	    else if(arg.contains(":")) {
	    	String[] s_split = arg.split(":", 2);
	    	BitVecExpr new_addr = get_effective_address(store, store.rip, s_split[1].strip(), length);
	    	res = store.get_seg_val(s_split[0], new_addr);
	    }
	    else
	        res = Helper.gen_spec_sym(arg, length);
	    return res;
	}

	
	static BitVecExpr get_idx_sym_val(Store store, String arg, BitVecExpr src_sym, BitVecExpr src_val, int length) {
		BitVecExpr res = null;
	    if(Lib.REG_NAMES.contains(arg)) {
	    	res = SymRegister.getRegSymAddr(store, arg);
	        if(!Helper.is_bit_vec_num(res)) {
	            ArrayList<BoolExpr> predicates = new ArrayList<BoolExpr>();
	            predicates.add(Helper.is_equal(src_sym, src_val));
	        	Model m = Helper.check_pred_satisfiable(predicates);
	            if(m != null) {
	            	for(FuncDecl<?> d : m.getDecls()) {
	            		BitVecExpr sVal = (BitVecExpr) m.getConstInterp(d);
	            		int sLen = sVal.getSortSize();
	            		res = (BitVecExpr) res.substitute(Helper.gen_spec_sym(d.getName().toString(), sLen), sVal);
	            	}
	            }
	        }
	    }
	    else if(Utils.imm_pat.matcher(arg).matches())
	        res = Helper.gen_bv_num(Utils.imm_str_to_int(arg), length);
	    return res;
	}
	

	static void calc_mult(ArrayList<BitVecExpr> stack, ArrayList<String> opStack) {
		BitVecExpr res = stack.get(0);
		ArrayList<Integer> to_remove_idx = new ArrayList<Integer>();
		for(int idx = 0; idx < opStack.size(); idx++) {
			String op = opStack.get(idx);
			if(op.equals("*")) {
	            res = Helper.bv_mult(stack.get(idx), stack.get(idx + 1));
	            stack.set(idx, res);
	            to_remove_idx.add(idx);
			}
		}
		Collections.reverse(to_remove_idx);
		for(int idx : to_remove_idx) {
			 stack.remove(idx + 1);
			 opStack.remove(idx);
		}
	}


	static BitVecExpr eval_simple_formula(ArrayList<BitVecExpr> stack, ArrayList<String> opStack) {
	    calc_mult(stack, opStack);
	    BitVecExpr res = stack.get(0);
	    for(int idx = 0; idx < opStack.size(); idx++) {
	    	String op = opStack.get(idx);
	    	if(op.equals("+"))
	            res = Helper.bv_add(res, stack.get(idx+1));
	        else if(op.equals("-"))
	        	res = Helper.bv_sub(res, stack.get(idx+1));
	    }
	    return res;
	}


	/**
	    * Calculate the effective address
	    * @param  arg		the operand for the jmp instruction. For example: "rax+rbx*1+0x402d34", "rbp-0x14", "rax"
	    * @param  store		the local store for the concolic execution process
	    * @param  length	the size of the memory address
	    * @return			the jump address
	    */
	static BitVecExpr calc_effective_address(String arg, Store store, int length) {
		ArrayList<BitVecExpr> stack = new ArrayList<BitVecExpr>();
		ArrayList<String> opStack = new ArrayList<String>();
	    String line = Utils.rmUnusedSpaces(arg.strip());
	    String[] lineSplit = NormHelper.simple_op_split_pat.split(line);
	    BitVecExpr val;
	    for(String lsi : lineSplit) {
	        lsi = lsi.strip();
	        if(NormHelper.simple_operator_pat.matcher(lsi).matches())
	            opStack.add(lsi);
	        else {
	            val = get_sym_val(lsi, store, length);
	            stack.add(val);
	        }
	    }
	    BitVecExpr res = eval_simple_formula(stack, opStack);
	    return res;
	}

	/**
	    * Calculate the address for a jump table entry
	    * @param  store		the local store for the concolic execution process
	    * @param  src		the operand for the jmp instruction. For example: "dword ptr [rcx+rdx*4]"
	    * @param  srcSym	the symbolic expression that needs to be substituted. For example: m#h
	    * @param  srcVal	the numeral value that is used to substitute the srcSym. For example: 4
	    * @return			the jump table address
	    */
	public static BitVecExpr get_jump_table_address(Store store, String src, BitVecExpr srcSym, BitVecExpr srcVal, int length) {
	    String arg = Utils.extract_content(src, "[");
	    ArrayList<BitVecExpr> stack = new ArrayList<BitVecExpr>();
	    ArrayList<String> opStack = new ArrayList<String>();
	    String line = Utils.rmUnusedSpaces(arg.strip());
	    String[] lineSplit = NormHelper.simple_op_split_pat.split(line);
	    BitVecExpr val;
	    for(String lsi : lineSplit) {
	        lsi = lsi.strip();
	        if(NormHelper.simple_operator_pat.matcher(lsi).matches())
	            opStack.add(lsi);
	        else {
	            val = get_idx_sym_val(store, lsi, srcSym, srcVal, length);
	            stack.add(val);
	        }
	    }
	    BitVecExpr res = eval_simple_formula(stack, opStack);
	    return res;
	}


	public static BitVecExpr get_effective_address(Store store, long rip, String src, int length) {
	    BitVecExpr res = null;
	    if(src.endsWith("]")) {
	        String content = Utils.extract_content(src, "[");
	        if(Utils.imm_pat.matcher(content).matches()) {
	        	long addr = Long.decode(content);
	            res = Helper.gen_bv_num(addr, length);
	        }
	        else if(content.contains("rip")) {  // "rip+0x2009a6"
	        	content = content.replace("rip", Utils.num_to_hex_string(rip));
	            long addr = (long) Utils.eval(content);
	            if(Config.MEM_ADDR_SIZE == 64)
	            	res = Helper.gen_bv_num(addr, length);
	            else if(Config.MEM_ADDR_SIZE == 32)
	            	res = Helper.gen_bv_num(addr & 0xffffffff, length);
	            else
	            	res = Helper.gen_bv_num(addr & 0xffff, length);
	        }
	        else {  // "rax + rbx * 1"
	            res = calc_effective_address(content, store, length);
	        }
	    }
	    else if(src.contains("s:")) {
	        String[] src_split = src.split(":", 2);
	        BitVecExpr seg_addr = get_sym_val(src_split[0].strip(), store, length);
	        BitVecExpr new_addr = get_effective_address(store, rip, src_split[1].strip(), length);
	        res = Helper.bv_add(seg_addr, new_addr);
	    }
	    else if(Utils.imm_pat.matcher(src).matches()) {
	        res = Helper.gen_bv_num(Utils.imm_str_to_int(src), length);
	    }
	    else {
	        Utils.logger.info("Cannot recognize the effective address of " + src);
	    }
	    return res;
	}
	
	
	static boolean check_mem_addr_overlapping(Store store, BitVecExpr address, int byte_len, String store_key) {
		boolean overlapping = false;
	    if(Helper.is_bit_vec_num(address)) {
	        for(int offset = -7; offset < byte_len; offset++) {
	            if(offset != 0) {
	            	BitVecExpr curr_address = Helper.bv_add(address, offset);
	                if(store.containsKey(store_key, curr_address)) {
//	                	BitVecExpr prev_sym = store.get_val(curr_address);
//	                    int prev_len = prev_sym.getSortSize() / 8;
	                    if(offset > 0) {
	                        overlapping = true;
	                        break;
	                    }
	                }
	            }
	        }
	    }
	    return overlapping;
	}


	static void set_mem_sym_val(Store store, BitVecExpr address,BitVecExpr sym, int block_id, int length, String store_key) { 
	    int byte_len = length / 8;
	    if(check_mem_addr_overlapping(store, address, byte_len, store_key)) return;
	    if(store.containsKey(address)) {
	    	BitVecExpr prev_sym = store.get_val(address);
	        int prev_len = prev_sym.getSortSize() / 8;
	        if(byte_len < prev_len) {
	        	BitVecExpr rest_sym = Helper.extract_bytes(prev_len, byte_len, prev_sym);
	        	BitVecExpr curr_sym = Helper.concat(rest_sym, sym);
	        	store.set_mem_val(address, curr_sym, block_id);
	        }
	        else
	        	store.set_mem_val(address, sym, block_id);
	    }
	    else {
	    	store.set_mem_val(address, sym, block_id);
	    }
	}

	static BitVecExpr is_mem_addr_in_stdout(Store store, BitVecExpr address) {
		BitVecExpr res = null;
        BitVecExpr tmp = Helper.bv_sub(address, store.g_StdoutHandler);
        if(Helper.is_bit_vec_num(tmp))
            res = tmp;
        else {
            tmp = Helper.bv_sub(address, SymHelper.STDOUT_ADDR);
            if(Helper.is_bit_vec_num(tmp))
                res = address;
        }
	    return res;
	}
	
	
	static BitVecExpr isMemAddrLocatedAtExtrnFunc(Store store, BitVecExpr address) {
		BitVecExpr res = null;
        BitVecExpr tmp = Helper.bv_sub(address, store.g_StdoutHandler);
        if(Helper.is_bit_vec_num(tmp))
            res = tmp;
        else {
            tmp = Helper.bv_sub(address, SymHelper.STDOUT_ADDR);
            if(Helper.is_bit_vec_num(tmp))
                res = address;
        }
	    return res;
	}


	public static void set_mem_sym(Store store, BitVecExpr address, BitVecExpr sym, int block_id, int length) {
	    // If the memory address is not a concrete value
	    if(!Helper.is_bit_vec_num(address)) {
	    	BitVecExpr tmp = is_mem_addr_in_stdout(store, address);
	        if(tmp !=  null)
	            set_mem_sym_val(store, tmp, sym, block_id, length, Lib.STDOUT);
	        else {
	        	store.set_mem_val(address, sym, block_id);
//	            Utils.logger.info("\nWarning: Potential buffer overflow with symbolic memory address " + address.toString());
	            String addrStr = address.toString();
	            if(!addrStr.contains(Utils.MEM_DATA_SEC_SUFFIX)) {
//	            	System.out.println(addrStr);
	            	store.g_NeedTraceBack = true;
	            }
	        }
	    }
	    else
	        set_mem_sym_val(store, address, sym, block_id, length, Lib.MEM);
	}
	    

	           
	public static BitVecExpr get_mem_sym(Store store, BitVecExpr address, int length, String store_key) {
		BitVecExpr res = null;
	    if(store.containsKey(address)) {
	    	BitVecExpr sym = null;
	    	if(store_key.equals(Lib.MEM))
	    		sym = store.get_val(address);
	    	else if(store_key.equals(Lib.STDOUT))
	    		sym = store.get_stdout_val(address);
	        int sym_len = sym.getSortSize();
	        if(sym_len > length)
	            res = Helper.extract(length - 1, 0, sym);
	        else if(sym_len == length)
	            res = sym;
	    }
	    return res;
	}


	static void read_mem_error_report(Store store, long int_address) {
	    Long stack_top = SymHelper.top_stack_addr(store);
	    if(SymHelper.addr_in_heap(int_address)) {
	    	store.g_PointerRelatedError = Lib.MEMORY_RELATED_ERROR_TYPE.USE_AFTER_FREE;
	    }
	    else if(Config.MAX_HEAP_ADDR <= int_address && int_address < stack_top) {
	    	store.g_PointerRelatedError = Lib.MEMORY_RELATED_ERROR_TYPE.NULL_POINTER_DEREFERENCE;
	    }
	}


	public static BitVecExpr readMemContent(Store store, BitVecExpr address, int block_id, int length) {
		BitVecExpr res = null;
	    if(Helper.is_bit_vec_num(address)) {
	    	Long val = null;
	        long intAddr = Helper.long_of_sym(address);
	        String secName = Helper.getAddrSecName(intAddr);
	        if(secName != null) {
	            long baseAddr = BinaryContent.secBaseAddrMap.get(secName);
	            val = BinaryContent.read_bytes(intAddr - baseAddr, length / 8);
	        }
	        else
	            read_mem_error_report(store, intAddr);
	        if(val != null)
	        	res = Helper.gen_bv_num(val, length);
	        else {
	            res = Helper.gen_spec_sym(Utils.MEM_DATA_SEC_SUFFIX + Utils.num_to_hex_string(intAddr), length);
	        }
	        store.set_mem_val(address, res, Utils.INIT_BLOCK_NO);
	    }
	    else {
	    	String addrStr = address.toString();
	    	if(addrStr.contains(Utils.MEM_DATA_SEC_SUFFIX)) {
	    		res = Helper.gen_spec_sym(Utils.MEM_DATA_SEC_SUFFIX + "(" + addrStr + ")", length);
	    	}
	    	else
	    		res = Helper.gen_mem_sym(length);
	        store.set_mem_val(address, res, block_id);
	    }
	    return res;
	}


	static BitVecExpr get_stdout_mem_val(Store store, BitVecExpr address, int length) {
		BitVecExpr res = null;
	    BitVecExpr tmp = is_mem_addr_in_stdout(store, address);
	    if(tmp != null) {
	        res = get_mem_sym(store, tmp, length, Lib.STDOUT);
	        if(res == null) {
	            res = Helper.gen_stdout_mem_sym(length);
	            store.set_stdout_val(tmp, res, Utils.INIT_BLOCK_NO);
	        }
	    }
	    return res;
	}


	public static BitVecExpr get_memory_val(Store store, BitVecExpr address, int block_id, int length) {
	    BitVecExpr res = get_stdout_mem_val(store, address, length);
	    if(res == null) {
	        res = get_mem_sym(store, address, length, Lib.MEM);
//	        System.out.println("Effective addr " + address.toString());
//	        System.out.println(res);
	        if(res == null)
	            res = readMemContent(store, address, block_id, length);
	    }
	    return res;
	}


	public static Integer get_mem_sym_block_id(Store store, BitVecExpr address) {
	    Integer res = null;
	    long intAddr = Helper.long_of_sym(address);
	    if(store.containsKey(address))
	    	res = store.get_block_id(address);
	    else {
	        if(Helper.addrAtRODataSection(intAddr))
	            res = Utils.INIT_BLOCK_NO;
	        else if(Helper.addrAtDataSection(intAddr))
	            res = store.g_MemPolluted;
	    }
	    return res;
	}


	public static BitVecExpr get_seg_memory_val(Store store, BitVecExpr address, String seg, int length) {
	    BitVecExpr res = null;
	    if(store.containsSegKey(seg, address)) {
	    	res = store.get_seg_val(seg, address);
	    }
	    else {
	        res = Helper.gen_mem_sym(length);
	        store.set_seg_val(seg, address, res);
	    }
	    return res;
	}


}
