package symbolic;

import com.microsoft.z3.BitVecExpr;

import common.Lib;
import common.Config;
import common.Helper;
import common.Tuple;
import block.Store;

public class SymRegister {
	
	static BitVecExpr bitwise_sub(BitVecExpr sym, int start_idx, int length) {
		BitVecExpr res = null;
	    if(length == 8 && start_idx != 0)
	        res = Helper.extract(15, 8, sym);
	    else
	        res = Helper.extract(length - 1, 0, sym);
	    return res;
	}


	public static BitVecExpr get_register_sym(Store store, String name) {
	    BitVecExpr sym = null;
	    if(Lib.REG_INFO_DICT.containsKey(name)) {
	    	String p_name = SymHelper.getRootReg(name);
	    	if(p_name.equals(name)) {
	    		sym = store.get_val(name);
	    	}
	    	else {
		    	Tuple<Integer, Integer> t_info = Lib.REG_INFO_DICT.get(name);
		    	int start_idx = t_info.x;
		    	int length = t_info.y;
		        BitVecExpr p_sym = store.get_val(p_name);
		        if(p_sym.equals(Helper.bottom(p_sym.getSortSize())))
		            sym = Helper.bottom(length);
		        else
		            sym = bitwise_sub(p_sym, start_idx, length);
	    	}
	    }
	    else if(Lib.REG64_NAMES.contains(name)) {
	        sym = store.get_val(name);
	    }
	    else {
	        sym = Helper.bottom(Config.MEM_ADDR_SIZE);
	    }
	    return sym;
	}
	
	
	static BitVecExpr getRegSymAddr(Store store, String name) {
		BitVecExpr res = get_register_sym(store, name);
		int length = res.getSortSize();
		if(length < Config.MEM_ADDR_SIZE) {
			res = Helper.zero_ext(Config.MEM_ADDR_SIZE - length, res);
		}
		return res;
	}


	public static Integer get_reg_sym_block_id(Store store, String name) {
	    Integer res = null;
	    if(Lib.REG_INFO_DICT.containsKey(name)) {
	    	String p_name = SymHelper.getRootReg(name);
	    	res = store.get_block_id(p_name);
	    }
	    else if(Lib.REG64_NAMES.contains(name))
	    	res = store.get_block_id(name);
	    return res;
	}


	static BitVecExpr bitwise_extend_parent(BitVecExpr p_sym, BitVecExpr sym, int start_idx, int length) {
		BitVecExpr res = null;
		if(sym.equals(Helper.bottom(length)))
	    	res = Helper.bottom(p_sym.getSortSize());
	    else if(length == 32)
	    	res = Helper.zero_ext(Config.MEM_ADDR_SIZE - 32, sym);
	    else if(length == 8 && start_idx != 0)
	    	res = Helper.concat(Helper.extract(Config.MEM_ADDR_SIZE - 1, 16, p_sym), sym, Helper.extract(7, 0, p_sym));
	    else
	        res = Helper.concat(Helper.extract(Config.MEM_ADDR_SIZE - 1, length, p_sym), sym);
	    return res;
	}


	public static void set_register_sym(Store store, String name, BitVecExpr sym, int block_id) {
		if(Lib.REG_INFO_DICT.containsKey(name)) {
			String p_name = SymHelper.getRootReg(name);
			if(p_name.equals(name)) {
				store.set_val(name, sym, block_id);
	    	}
	    	else {
				Tuple<Integer, Integer> t_info = Lib.REG_INFO_DICT.get(name);
		    	int start_idx = t_info.x;
		    	int length = t_info.y;
		    	BitVecExpr p_sym = store.get_val(p_name);
		    	store.set_val(p_name, bitwise_extend_parent(p_sym, sym, start_idx, length), block_id);
	    	}
		}
	    else if(Lib.REG64_NAMES.contains(name)) {
	    	store.set_val(name, sym, block_id);
	    }
	}
}
