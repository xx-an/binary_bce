package block;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import com.microsoft.z3.*;

import common.Lib;
import common.Utils;
import common.Config;
import common.Helper;

public class Store {

	public long rip = -1;
	public HashMap<String, Node> g_RegStore;
	public HashMap<BitVecExpr, Node> g_MemStore;
	public HashSet<BitVecExpr> g_AuxMemStore;
	public HashMap<String, BoolExpr> g_FlagStore;
	public HashMap<String, HashMap<BitVecExpr, BitVecExpr>> g_SegStore;
	public HashMap<BitVecExpr, Node> g_StdoutStore;
	public ArrayList<Long> g_FuncCallStack;
	public Lib.MEMORY_RELATED_ERROR_TYPE g_PointerRelatedError;
	public long g_PRErrorAddress;
	public long g_HeapAddr;
	public BitVecExpr g_StdoutAddress;
	public BitVecExpr g_StdoutHandler;
	public BitVecExpr g_StdinAddress;
	public BitVecExpr g_StdinHandler;
	public Integer g_MemPolluted;
	public boolean g_NeedTraceBack;
	
	
	public Store(Store store) {
		init(store);
	}
	
	
	public Store(Store store, long rip) {
		this.rip = rip;
		init(store);
	}
	
		
	@SuppressWarnings("unchecked")
	void init(Store store) {
		if(store != null) {
			g_RegStore = (HashMap<String, Node>) store.g_RegStore.clone();
			g_MemStore = (HashMap<BitVecExpr, Node>) store.g_MemStore.clone();
			g_StdoutStore = (HashMap<BitVecExpr, Node>) store.g_StdoutStore.clone();
			g_SegStore = (HashMap<String, HashMap<BitVecExpr, BitVecExpr>>) store.g_SegStore.clone();
			for(String ss : Lib.SEG_STATE_NAMES) {
				g_SegStore.put(ss, (HashMap<BitVecExpr, BitVecExpr>) store.g_SegStore.get(ss).clone());
			}
			g_FlagStore = (HashMap<String, BoolExpr>) store.g_FlagStore.clone();
			g_AuxMemStore = (HashSet<BitVecExpr>) store.g_AuxMemStore.clone();
			g_FuncCallStack = (ArrayList<Long>) store.g_FuncCallStack.clone();
            g_HeapAddr = store.g_HeapAddr;
            g_StdoutHandler = store.g_StdoutHandler;
            g_MemPolluted = store.g_MemPolluted;
            g_NeedTraceBack = store.g_NeedTraceBack;
            g_PointerRelatedError = store.g_PointerRelatedError;
		}
		else {
			g_RegStore = new HashMap<String, Node>();
			g_MemStore = new HashMap<BitVecExpr, Node>();
			g_StdoutStore = new HashMap<BitVecExpr, Node>();
			g_SegStore = new HashMap<String, HashMap<BitVecExpr, BitVecExpr>>();
			for(String ss : Lib.SEG_STATE_NAMES) {
				g_SegStore.put(ss, new HashMap<BitVecExpr, BitVecExpr>());
			}
			g_FlagStore = new HashMap<String, BoolExpr>();
			g_AuxMemStore = new HashSet<BitVecExpr>();
			g_FuncCallStack = new ArrayList<Long>();
			g_HeapAddr = Config.MIN_HEAP_ADDR;
			g_StdoutHandler = null;
			g_MemPolluted = null;
			g_NeedTraceBack = false;
			g_PointerRelatedError = Lib.MEMORY_RELATED_ERROR_TYPE.NONE;
		}
	}
    
	String pp_val(BitVecExpr sym) {
        String res = "";
        if(Helper.is_bit_vec_num(sym)) {
        	res = "0x" + Long.toHexString(Helper.long_of_sym(sym));
        }
        else { 
        	res = sym.toString(); 
        }
        return res;
    }
	
	public long get_rip() {
		return rip;
	}
	
	public boolean containsKey(BitVecExpr key) {
		return g_MemStore.containsKey(key);
	}
	
	public boolean containsKey(String key) {
		return g_RegStore.containsKey(key);
	}
	
	public boolean containsKey(String store_key, BitVecExpr key) {
		boolean res = false;
		if(store_key.equals(Lib.MEM))
			res = g_MemStore.containsKey(key);
		else if(store_key.equals(Lib.AUX_MEM))
			res = g_AuxMemStore.contains(key);
		return res;
	}
	
	public BitVecExpr get_val(String reg_name) {
		return g_RegStore.get(reg_name).expr;
	}
	
	public BitVecExpr get_val(BitVecExpr addr) {
		return g_MemStore.get(addr).expr;
	}
	
	public void set_val(String reg_name, BitVecExpr val, int block_id) {
		Node node = new Node(val, block_id);
		g_RegStore.put(reg_name, node);
	}
	
	public void set_mem_val(BitVecExpr addr, BitVecExpr val, int block_id) {
		Node node = new Node(val, block_id);
		g_MemStore.put(addr, node);
	}
	
	public void remove_mem_val(BitVecExpr addr) {
		g_MemStore.remove(addr);
	}
	
	public int get_block_id(String reg_name) {
		return g_RegStore.get(reg_name).block_id;
	}
	
	public int get_block_id(BitVecExpr addr) {
		return g_MemStore.get(addr).block_id;
	}
	
	
	public BitVecExpr get_stdout_val(BitVecExpr addr) {
		return g_StdoutStore.get(addr).expr;
	}
	
	public void set_stdout_val(BitVecExpr addr, BitVecExpr val, int block_id) {
		Node node = new Node(val, block_id);
		g_StdoutStore.put(addr, node);
	}
	
	public boolean containsSegKey(String seg, BitVecExpr name) {
		return g_SegStore.get(seg).containsKey(name);
	}

	public BitVecExpr get_seg_val(String seg, BitVecExpr name) {
		return g_SegStore.get(seg).get(name);
	}
	
	public void set_seg_val(String seg, BitVecExpr name, BitVecExpr val) {
		g_SegStore.get(seg).put(name, val);
	}
	
	
	public BoolExpr get_flag_val(String flagName) {
		return g_FlagStore.get(flagName);
	}
	
	public void set_flag_val(String flagName, BoolExpr val) {
		g_FlagStore.put(flagName, val);
	}
	
	public boolean contains_aux_mem(BitVecExpr addr) {
		return g_AuxMemStore.contains(addr);
	}

	public boolean add_aux_mem(BitVecExpr addr) {
		return g_AuxMemStore.add(addr);
	}
	
	public long get_heap_addr() {
		return g_HeapAddr;
	}
	
	public void set_heap_addr(long heapAddr) {
		g_HeapAddr = heapAddr;
	}
	
	public String pp_reg_store() {
		StringBuilder sb = new StringBuilder();
        String res_str = "";
        for (String ki : g_RegStore.keySet()) {
        	BitVecExpr vi = g_RegStore.get(ki).expr;
        	res_str += ki + ": " + pp_val(vi) + ",\n";
        }
        sb.append("Reg: {\n" + res_str + "}\n");
		return sb.toString();
	}
	
	public String pp_mem_store() {
		StringBuilder sb = new StringBuilder();
        String res_str = "";
        for (BitVecExpr ki : g_MemStore.keySet()) {
        	BitVecExpr vi = g_MemStore.get(ki).expr;
        	res_str += pp_val(ki) + ": " + pp_val(vi) + ",\n";
        }
        sb.append("Mem: {\n" + res_str + "}\n");
		return sb.toString();
	}
	
    public String pp_store() {
        StringBuilder sb = new StringBuilder();
        if(rip != -1) {
        	sb.append("rip {" + Utils.toHexString(rip) + "\n");
        }
        sb.append(pp_reg_store());
        sb.append(pp_mem_store());
        return sb.toString();
    }
    
    public String pp_segreg_store() {
    	StringBuilder sb = new StringBuilder();
        sb.append(g_SegStore.toString());
		return sb.toString();
    }

    boolean reg_state_ith_eq(Store old, HashMap<Long, String> address_inst_map) {
    	HashMap<String, Node> reg_old = old.g_RegStore;
        for(String ki : g_RegStore.keySet()) {
        	Node v = g_RegStore.get(ki);
        	Node v_old = reg_old.getOrDefault(ki, null);
        	if(v_old != null) {
                if(!ki.endsWith("sp") && !ki.endsWith("bp")) {
                    if(!Helper.bitvec_eq(v_old.expr, v.expr)) {
                        return false;
                    }
                }
        	}
        }
        return true;
    }
    
    boolean mem_state_ith_eq(Store old, HashMap<Long, String> address_inst_map) {
    	HashMap<BitVecExpr, Node> mem_old = old.g_MemStore;
        for(BitVecExpr ki : g_MemStore.keySet()) {
        	Node v = g_MemStore.get(ki);
        	Node v_old = mem_old.getOrDefault(ki, null);
        	if(v_old != null) {
        		if(!Helper.bitvec_eq(v_old.expr, v.expr)) {
                    return false;
                }
        	}
        }
        return true;
    }

    public boolean state_ith_eq(Store old, HashMap<Long, String> address_inst_map, String k) {
    	if(k.equals(Lib.REG))
    		return reg_state_ith_eq(old, address_inst_map);
    	else if(k.equals(Lib.MEM))
    		return mem_state_ith_eq(old, address_inst_map);
        return true;
    }


    public boolean state_equal(Store old, HashMap<Long, String> address_inst_map) {
        for(String k : Lib.RECORD_STATE_NAMES) {
            boolean res = state_ith_eq(old, address_inst_map, k);
            if(!res)
                return false;
        }
        return true;
    }

        		
}
