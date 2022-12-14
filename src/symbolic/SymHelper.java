package symbolic;

import java.util.HashMap;
import java.util.HashSet;

import com.microsoft.z3.*;

import common.Lib;
import common.Helper;
import common.Config;
import common.GlobalVar;

import block.Node;
import block.Store;

public class SymHelper {
	
	public static final BitVecExpr STDOUT_ADDR = Helper.gen_spec_sym("stdout", Config.MEM_ADDR_SIZE);
			
	
	public static Long top_stack_addr(Store store) {
		Long res = null;
		BitVecExpr rsp_val = store.get_val("rsp");
	    if(rsp_val != null && (rsp_val instanceof BitVecNum)) {
	        res = ((BitVecNum) rsp_val).getLong();
	    }
	    return res;
	}
	
	
	static void reset_mem_content_pollute(Store store, int block_id) {
    	store.g_MemPolluted = block_id;
    }


	void pollute_all_mem_content(Store store, int block_id) {
		store.g_MemPolluted = block_id;
		HashSet<BitVecExpr> addr_list = (HashSet) store.g_MemStore.keySet();
	    for(BitVecExpr addr : addr_list) {
	        if(!(addr instanceof BitVecNum)) {
	        	BitVecExpr val = store.get_val(addr);
	            if(Helper.is_bit_vec_num(val)) {
	            	store.set_val(addr, Helper.gen_sym(val.getSortSize()), block_id);
	            }
	        }
	        else {
	            long int_addr = Helper.long_of_sym(addr);
	            if(int_addr >= Config.MIN_HEAP_ADDR && int_addr < Config.MAX_HEAP_ADDR) {
	            	BitVecExpr val = store.get_val(addr);
		            if(Helper.is_bit_vec_num(val)) {
		            	store.set_val(addr, Helper.gen_sym(val.getSortSize()), block_id);
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
	            	store.set_val(addr, Helper.gen_sym(val.getSortSize()), block_id);
	            }
	        }
	    }
	}
	
	public static void remove_memory_content(Store store, BitVecExpr mem_address) {
		store.remove_val(mem_address);
	}


	public static boolean addr_in_rodata_section(long int_addr) {
	    return GlobalVar.binary_info.rodata_start_addr <= int_addr && int_addr < GlobalVar.binary_info.rodata_end_addr;
	}


	public static boolean addr_in_data_section(long int_addr) {
	    return GlobalVar.binary_info.data_start_addr <= int_addr && int_addr < GlobalVar.binary_info.data_end_addr;
	}


	public static boolean addr_in_heap(long int_addr) {
	    return Config.MIN_HEAP_ADDR <= int_addr && int_addr < Config.MAX_HEAP_ADDR;
	}


	boolean check_mem_addr_overlapping(Store store, BitVecExpr address, int byte_len) {
	    boolean overlapping = false;
	    if(Helper.is_bit_vec_num(address)) {
	        long int_address = Helper.long_of_sym(address);
	        for(int offset = -7; offset < byte_len; offset++) {
	            if(offset != 0) {
	                BitVecExpr curr_address = Helper.bv_add(address, offset);
	                if(store.containsKey(curr_address)) {
	                	BitVecExpr prev_sym = store.get_val(curr_address);
	                	int prev_len = prev_sym.getSortSize() / 8;
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

	    
	boolean check_buffer_overflow(Store store, BitVecExpr address, int length) {
	    boolean overflow = false;
	    int byte_len = length / 8;
	    long int_address = Helper.long_of_sym(address);
	    Long stack_top = top_stack_addr(store);
	    if(addr_in_data_section(int_address) || addr_in_heap(int_address)) {
	        overflow = check_mem_addr_overlapping(store, address, byte_len);
	    }
	    return overflow;
	}
}
