package symbolic;

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
	
	
	static void reset_mem_content_pollute(Store store, int block_id) {
    	store.g_MemPolluted = block_id;
    }
	
	
	public static String getRootReg(String src) {
	    String res = null;
	    if(Lib.REG64_NAMES.contains(src))
	        res = src;
	    else if(Config.REGS_PARENT_MAP.containsKey(src))
	    	res = Config.REGS_PARENT_MAP.get(src);
	    return res;
	}
	
	
	public static void remove_memory_content(Store store, BitVecExpr mem_address) {
		store.remove_mem_val(mem_address);
	}
	
	public static Long stackTopAddr(Store store) {
		Long res = null;
		String spName = Config.SP_NAME;
		BitVecExpr symSP = store.get_val(spName);
	    if(symSP != null && (symSP instanceof BitVecNum)) {
	        res = ((BitVecNum) symSP).getLong();
	    }
	    return res;
	}
	
	
	public static BitVecExpr stackTopBVAddr(Store store) {
		String spName = Config.SP_NAME;
		BitVecExpr symSP = store.get_val(spName);
	    return symSP;
	}
	
	public static BitVecExpr stackTopVal(Store store) {
		String spName = Config.SP_NAME;
		BitVecExpr symSP = store.get_val(spName);
		BitVecExpr res = SymEngine.get_mem_sym(store, symSP);
	    return res;
	}
	
	public static BitVecExpr stackSecondTopVal(Store store) {
		String spName = Config.SP_NAME;
		BitVecExpr symSP = store.get_val(spName);
		BitVecExpr res = SymEngine.get_mem_sym(store, Helper.bv_add(symSP, Config.MEM_ADDR_SIZE / 8));
	    return res;
	}

	public static boolean addrInHeap(long addr) {
	    return Config.INIT_HEAP_ADDR <= addr && addr < Config.MAX_HEAP_ADDR;
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
