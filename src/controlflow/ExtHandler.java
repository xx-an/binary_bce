package controlflow;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import com.microsoft.z3.BitVecExpr;

import block.Store;
import common.Lib;
import common.Config;
import common.Utils;
import semantics.SMTHelper;
import symbolic.SymHelper;
import symbolic.SymEngine;
import common.Helper;

public class ExtHandler {

	static BitVecExpr TERMINAL_ADDRESS = null;
	static BitVecExpr TERMINAL_SYMBOL = Helper.gen_spec_sym("x", Config.MEM_ADDR_SIZE);

	static ArrayList<String> regs_str_to_list(String regs) {
		ArrayList<String> res = new ArrayList<String>();
	    String[] regs_split = regs.split(",");
	    for(String reg : regs_split)
	    	res.add(reg.strip());
	    return res;
	}

	static void set_regs_sym(Store store, List<String> dests, int block_id) {
		for(String dest : dests) {
			int length = Utils.getSymLength(dest);
	        SymEngine.set_sym(store, dest, Helper.gen_sym(length), block_id);
		}
	}
	
	static void set_regs_sym(Store store, ArrayList<String> dests, int block_id) {
		for(String dest : dests) {
			int length = Utils.getSymLength(dest);
	        SymEngine.set_sym(store, dest, Helper.gen_sym(length), block_id);
		}
	}
	
	void set_regs_sym(Store store, String[] dests, int block_id) {
		for(String dest : dests) {
			int length = Utils.getSymLength(dest);
	        SymEngine.set_sym(store, dest, Helper.gen_sym(length), block_id);
		}
	}
	

	void set_reg_val(Store store, String dest, int val, int block_id) {
	    SymEngine.set_sym(store, dest, Helper.gen_bv_num(val), block_id);
	}
	
	
	static void set_reg_val(Store store, String dest, long val, int block_id) {
	    SymEngine.set_sym(store, dest, Helper.gen_bv_num(val), block_id);
	}


	static void clear_flags(Store store) {
	    for(String flag : Lib.RFlags)
	    	store.set_flag_val(flag, null);
	}

	public static boolean is_term_address(BitVecExpr address) {
		return address.equals(TERMINAL_ADDRESS) || address.equals(TERMINAL_SYMBOL);
	}

	static void insert_termination_symbol(Store store, int block_id) {
	    BitVecExpr sym_x = Helper.gen_spec_sym("x", Config.MEM_ADDR_SIZE);
	    SMTHelper.push_val(store, sym_x, block_id);
	};


	static void ext__libc_start_main(Store store, Long main_address, int block_id) {
		String regs = (Config.MEM_ADDR_SIZE==64)?"rcx, rdx, rsi, rdi, r8, r9, r10, r11":"ecx, edx, esi, edi";
	    ArrayList<String> dests = regs_str_to_list(regs);
	    set_reg_val(store, (Config.MEM_ADDR_SIZE==64)?"rax":"eax", main_address, block_id);
	    set_regs_sym(store, dests, block_id);
	    SymEngine.set_sym(store, (Config.MEM_ADDR_SIZE==64)?"rbp":"ebp", SymEngine.get_sym(store, (Config.MEM_ADDR_SIZE==64)?"rcx":"ecx", block_id), block_id);
	    clear_flags(store);
	    TERMINAL_ADDRESS = Helper.gen_bv_num(store.rip, Config.MEM_ADDR_SIZE);
	}
	    

	static void extAllocHeapMem(HashMap<Long, Integer> heapAllocMemInfo, Store store, String extFuncName, int block_id, BitVecExpr m_size) {
	    long heapAddr = store.get_heap_addr();
	    int memSize = 0;
	    BitVecExpr memAddr = Helper.gen_bv_num(heapAddr, Config.MEM_ADDR_SIZE);
	    SymEngine.set_sym(store, (Config.MEM_ADDR_SIZE==64)?"rax":"eax", memAddr, block_id);
	    if(Helper.is_bit_vec_num(m_size))
	    	memSize = Helper.int_of_sym(m_size);
	    else
	    	memSize = Config.MAX_MALLOC_SIZE;
	    if(memSize == 0) {
	    	Utils.logger.info("The allocation size for " + extFuncName + " function cannot be zero");
	    	System.exit(0);
	    }
	    heapAllocMemInfo.put(heapAddr, memSize);
	    BitVecExpr memVal = (!extFuncName.startsWith("calloc")) ? Helper.bottom(memSize) : Helper.gen_bv_num(0, memSize);
	    heapAddr += memSize;
	    Config.MAX_HEAP_ADDR = (Config.MAX_HEAP_ADDR < heapAddr) ? heapAddr : Config.MAX_HEAP_ADDR;
	    SymEngine.set_mem_sym(store, memAddr, memVal, memSize);
	    String regs = (Config.MEM_ADDR_SIZE==64)?"rcx, rdx, rsi, rdi, r8, r9, r10, r11":"ecx, edx, esi, edi";
	    ArrayList<String> dests = regs_str_to_list(regs);
	    set_regs_sym(store, dests, block_id);
	    clear_flags(store);
	    store.set_heap_addr(heapAddr);
	}
	
	
	static long genFreshHeapPointer(Store store) {
	    long headAddr = store.get_heap_addr();
	    long memAddr = headAddr;
	    int memSize = Config.MAX_MALLOC_SIZE;
	    headAddr += memSize;
	    Config.MAX_HEAP_ADDR = Math.max(Config.MAX_HEAP_ADDR, headAddr);
	    store.set_heap_addr(headAddr);
	    return memAddr;
	}
	
	
	HashMap<String, ArrayList<String>> parse_predefined_constraint(String constraint_config_file) throws FileNotFoundException {
		HashMap<String, ArrayList<String>> res = new HashMap<String, ArrayList<String>>();
		File f = new File(constraint_config_file);
		try (BufferedReader br = new BufferedReader(new FileReader(f))) {
    	    String line;
    	    while ((line = br.readLine()) != null) {
    	    	line = line.strip();
    	    	if(line != null) {
                    line = line.replace("\t", " ");
                    String[] lineSplit = line.strip().split(" ", 2);
                    String ext_func_name = lineSplit[0].strip();
                    String constraint = lineSplit[1].strip();
                    if(res.containsKey(constraint)) {
                    	ArrayList<String> constraint_list = res.get(ext_func_name);
                    	constraint_list.add(constraint);
                    }
                    else {
                    	ArrayList<String> constraint_list = new ArrayList<String>();
                    	constraint_list.add(constraint);
                    	res.put(ext_func_name, constraint_list);
                    }
    	        }
    	    }
    	} 
    	catch (IOException e) {
			e.printStackTrace();
		}
	    return res;
	}	
	    

	static void ext_alloc_mem_call(HashMap<Long, Integer> heapAllocMemInfo, Store store, String extFuncName, int block_id) {
	    BitVecExpr memSizeBV = SymHelper.stackTopVal(store);
	    extAllocHeapMem(heapAllocMemInfo, store, extFuncName, block_id, memSizeBV);
	}


	static boolean ext_free_mem_call(HashMap<Long, Integer> heapAllocMemInfo, Store store, int block_id) {
	    BitVecExpr memAddr = SymHelper.stackSecondTopVal(store);
	    Long heapAddr = null;
	    if(Helper.is_bit_vec_num(memAddr)) heapAddr = Helper.long_of_sym(memAddr);
//	    System.out.println(Utils.toHexString(heapAddr));
    	if(store.containsKey(memAddr) && heapAddr != null && heapAllocMemInfo.containsKey(heapAddr)) {
			int memSize = heapAllocMemInfo.get(heapAddr);
			long endAddr = heapAddr + memSize;
			HashSet<BitVecExpr> addrToBeRemoved = new HashSet<>();
			for(BitVecExpr bvAddr : store.g_MemStore.keySet()) {
				if(Helper.is_bit_vec_num(bvAddr)) {
					long intAddr = Helper.long_of_sym(bvAddr);
    				if(intAddr >= heapAddr && intAddr < endAddr)
    					addrToBeRemoved.add(bvAddr);
				}
			}
			for(BitVecExpr bvAddr : addrToBeRemoved) {
    			SymHelper.remove_memory_content(store, bvAddr);
			}
			heapAllocMemInfo.remove(heapAddr);
			return true;
		}
    	store.g_PointerRelatedError = Lib.MEMORY_RELATED_ERROR_TYPE.FREE_AT_INVALID_ADDR;
    	store.g_PRErrorAddress = heapAddr;
	    return false;
	}


	static void ext_func_call(Store store, int  block_id) {
	    List<String> dests = Config.CALLEE_NOT_SAVED_REGS;
	    set_regs_sym(store, dests, block_id);
	    clear_flags(store);
	}
	    
	    
}
