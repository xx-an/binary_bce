package controlflow;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
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

	static ArrayList<String> regs_str_to_list(String regs) {
		ArrayList<String> res = new ArrayList<String>();
	    String[] regs_split = regs.split(",");
	    for(String reg : regs_split)
	    	res.add(reg.strip());
	    return res;
	}

	static void set_regs_sym(Store store, long rip, List<String> dests, int block_id) {
		for(String dest : dests) {
			int length = Utils.get_sym_length(dest);
	        SymEngine.set_sym(store, rip, dest, Helper.gen_sym(length), block_id);
		}
	}
	
	static void set_regs_sym(Store store, long rip, ArrayList<String> dests, int block_id) {
		for(String dest : dests) {
			int length = Utils.get_sym_length(dest);
	        SymEngine.set_sym(store, rip, dest, Helper.gen_sym(length), block_id);
		}
	}
	
	void set_regs_sym(Store store, long rip, String[] dests, int block_id) {
		for(String dest : dests) {
			int length = Utils.get_sym_length(dest);
	        SymEngine.set_sym(store, rip, dest, Helper.gen_sym(length), block_id);
		}
	}
	

	void set_reg_val(Store store, long rip, String dest, int val, int block_id) {
	    SymEngine.set_sym(store, rip, dest, Helper.gen_bv_num(val, Config.MEM_ADDR_SIZE), block_id);
	}
	
	
	static void set_reg_val(Store store, long rip, String dest, long val, int block_id) {
	    SymEngine.set_sym(store, rip, dest, Helper.gen_bv_num(val, Config.MEM_ADDR_SIZE), block_id);
	}


	static void clear_flags(Store store) {
	    for(String flag : Lib.RFlags)
	    	store.set_flag_val(flag, null);
	}
	    

	static void insert_termination_symbol(Store store, long rip, int block_id) {
	    BitVecExpr sym_x = Helper.TERMINAL_SYMBOL.get(Config.MEM_ADDR_SIZE);
	    SMTHelper.push_val(store, rip, sym_x, block_id);
	};


	static void ext__libc_start_main(Store store, long rip, long main_address, int block_id) {
		String regs = (Config.MEM_ADDR_SIZE==64)?"rcx, rdx, rsi, rdi, r8, r9, r10, r11":"ecx, edx, esi, edi";
	    ArrayList<String> dests = regs_str_to_list(regs);
	    set_reg_val(store, rip, (Config.MEM_ADDR_SIZE==64)?"rax":"eax", main_address, block_id);
	    set_regs_sym(store, rip, dests, block_id);
	    SymEngine.set_sym(store, rip, (Config.MEM_ADDR_SIZE==64)?"rbp":"ebp", SymEngine.get_sym(store, main_address, (Config.MEM_ADDR_SIZE==64)?"rcx":"ecx", block_id), block_id);
	    clear_flags(store);
	    insert_termination_symbol(store, rip, block_id);
	}
	    

	static void ext_gen_fresh_heap_pointer(Store store, long rip, String ext_func_name, int block_id, BitVecExpr m_size) {
	    long heap_addr = store.g_HeapAddr;
	    BitVecExpr mem_addr = Helper.gen_bv_num(heap_addr, Config.MEM_ADDR_SIZE);
	    SymEngine.set_sym(store, rip, (Config.MEM_ADDR_SIZE==64)?"rax":"eax", mem_addr, block_id);
	    int mem_size = 0;
	    if(Helper.is_bit_vec_num(m_size))
	    	mem_size = Helper.int_of_sym(m_size);
	    else
	        mem_size = Config.MAX_MALLOC_SIZE;
	    if(mem_size == 0) {
	    	Utils.logger.info("The allocation size for " + ext_func_name + " function cannot be zero");
	        System.exit(0);
	    }
	    BitVecExpr mem_val = Helper.bottom(mem_size);
	    if(ext_func_name.startsWith("calloc"))
	    	mem_val = Helper.gen_bv_num(0, mem_size);
	    heap_addr += mem_size;
	    Config.MAX_HEAP_ADDR = Math.max(Config.MAX_HEAP_ADDR, heap_addr);
	    SymEngine.set_mem_sym(store, mem_addr, mem_val, mem_size);
	    String regs = (Config.MEM_ADDR_SIZE==64)?"rcx, rdx, rsi, rdi, r8, r9, r10, r11":"ecx, edx, esi, edi";
	    ArrayList<String> dests = regs_str_to_list(regs);
	    set_regs_sym(store, rip, dests, block_id);
	    clear_flags(store);
	    store.g_HeapAddr = heap_addr;
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
	    

	static void ext_alloc_mem_call(Store store, long rip, String ext_func_name, int block_id) {
	    long heap_addr = store.get_heap_addr();
//	    Utils.logger.info(heap_addr)
	    BitVecExpr bv_mem_size = (ext_func_name.startsWith("malloc") || ext_func_name.startsWith("calloc")) ? SymEngine.get_sym(store, rip, (Config.MEM_ADDR_SIZE==64)?"rdi":"edi", block_id) : SymEngine.get_sym(store, rip, (Config.MEM_ADDR_SIZE==64)?"rsi":"esi", block_id);
	    BitVecExpr mem_addr = Helper.gen_bv_num(heap_addr, Config.MEM_ADDR_SIZE);
	    SymEngine.set_sym(store, rip, (Config.MEM_ADDR_SIZE==64)?"rax":"eax", mem_addr, block_id);
	    int mem_size = 0;
	    if(Helper.is_bit_vec_num(bv_mem_size))
	        mem_size = Helper.int_of_sym(bv_mem_size);
	    else
	        mem_size = Config.MAX_MALLOC_SIZE;
	    if(mem_size == 0) {
	    	Utils.logger.info("The allocation size for " + ext_func_name + " function cannot be zero");
	    	System.exit(0);
	    }
	    BitVecExpr mem_val = (!ext_func_name.startsWith("calloc")) ? Helper.bottom(mem_size) : Helper.gen_bv_num(0, mem_size);
	    heap_addr += mem_size;
	    Config.MAX_HEAP_ADDR = (Config.MAX_HEAP_ADDR < heap_addr) ? heap_addr : Config.MAX_HEAP_ADDR;
	    SymEngine.set_mem_sym(store, mem_addr, mem_val, mem_size);
	    String regs = (Config.MEM_ADDR_SIZE==64)?"rcx, rdx, rsi, rdi, r8, r9, r10, r11":"ecx, edx, esi, edi";
	    ArrayList<String> dests = regs_str_to_list(regs);
	    set_regs_sym(store, rip, dests, block_id);
	    clear_flags(store);
	    store.set_heap_addr(heap_addr);
	}


	static boolean ext_free_mem_call(Store store, long rip, int block_id) {
	    boolean succeed = true;
	    BitVecExpr mem_addr = SymEngine.get_sym(store, rip, (Config.MEM_ADDR_SIZE==64)?"rdi":"edi", block_id);
	    if(store.containsKey(mem_addr))
	        SymHelper.remove_memory_content(store, mem_addr);
	    else if(Helper.is_bit_vec_num(mem_addr)) {
	        succeed = false;
	    }
	    return succeed;
	}


	static void ext_func_call(Store store, long rip, int  block_id) {
	    List<String> dests = Lib.CALLEE_NOT_SAVED_REGS.get(Config.MEM_ADDR_SIZE);
	    set_regs_sym(store, rip, dests, block_id);
	    clear_flags(store);
	}
	    
	    
}
