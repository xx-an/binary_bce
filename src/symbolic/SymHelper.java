package symbolic;

import java.util.Set;

import com.microsoft.z3.*;

import common.Lib;
import common.Helper;
import common.Config;

import block.Store;

public class SymHelper {
	
	public static final BitVecExpr STDOUT_ADDR = Helper.gen_spec_sym("stdout", Config.MEM_ADDR_SIZE);
	public static int cnt;
	public static int memCnt;
			
	public static void cnt_init(){
	    cnt = 0;
	    memCnt = 0;
	}
	
	public static Long top_stack_addr(Store store) {
		Long res = null;
		String spName = Config.ADDR_SIZE_SP_MAP.get(Config.MEM_ADDR_SIZE);
		BitVecExpr spVal = store.get_val(spName);
	    if(spVal != null && (spVal instanceof BitVecNum)) {
	        res = ((BitVecNum) spVal).getLong();
	    }
	    return res;
	}
	
	
	static void reset_mem_content_pollute(Store store, int block_id) {
    	store.g_MemPolluted = block_id;
    }
	
	
	public static String get_root_reg(String src) {
	    String res = null;
	    if(Lib.REG64_NAMES.contains(src))
	        res = src;
	    else if(Config.MEM_ADDR_SIZE == 64) {
	    	if(Config.REGS_PARENT64_MAP.containsKey(src))
	    		res = Config.REGS_PARENT64_MAP.get(src);
	    }
	    else if(Config.MEM_ADDR_SIZE == 32) {
	    	if(Config.REGS_PARENT32_MAP.containsKey(src))
	    		res = Config.REGS_PARENT32_MAP.get(src);
	    }
	    return res;
	}


	void pollute_all_mem_content(Store store, int block_id) {
		store.g_MemPolluted = block_id;
		Set<BitVecExpr> addr_list = store.g_MemStore.keySet();
	    for(BitVecExpr addr : addr_list) {
	        if(!(addr instanceof BitVecNum)) {
	        	BitVecExpr val = store.get_val(addr);
	            if(Helper.is_bit_vec_num(val)) {
	            	store.set_mem_val(addr, Helper.gen_sym(val.getSortSize()), block_id);
	            }
	        }
	        else {
	            long int_addr = Helper.long_of_sym(addr);
	            if(int_addr >= Config.MIN_HEAP_ADDR && int_addr < Config.MAX_HEAP_ADDR) {
	            	BitVecExpr val = store.get_val(addr);
		            if(Helper.is_bit_vec_num(val)) {
		            	store.set_mem_val(addr, Helper.gen_sym(val.getSortSize()), block_id);
		            }
	            }
	        }
	    }
	}


	void pollute_mem_w_sym_address(Store store, int block_id) {
	    for(BitVecExpr addr : store.g_MemStore.keySet()) {
	        if(!Helper.is_bit_vec_num(addr)) {
	        	BitVecExpr val = store.get_val(addr);
	            if(Helper.is_bit_vec_num(val)) {
	            	store.set_mem_val(addr, Helper.gen_sym(val.getSortSize()), block_id);
	            }
	        }
	    }
	}
	
	public static void remove_memory_content(Store store, BitVecExpr mem_address) {
		store.remove_mem_val(mem_address);
	}

	public static boolean addr_in_heap(long int_addr) {
	    return Config.MIN_HEAP_ADDR <= int_addr && int_addr < Config.MAX_HEAP_ADDR;
	}


	boolean check_mem_addr_overlapping(Store store, BitVecExpr address, int byte_len) {
	    boolean overlapping = false;
	    if(Helper.is_bit_vec_num(address)) {
//	        long int_address = Helper.long_of_sym(address);
	        for(int offset = -7; offset < byte_len; offset++) {
	            if(offset != 0) {
	                BitVecExpr curr_address = Helper.bv_add(address, offset);
	                if(store.containsKey(curr_address)) {
//	                	BitVecExpr prev_sym = store.get_val(curr_address);
//	                	int prev_len = prev_sym.getSortSize() / 8;
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
	
}
