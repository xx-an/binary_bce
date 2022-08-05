package semantics;

import java.util.ArrayList;
import java.util.HashMap;

import com.microsoft.z3.BitVecExpr;

public class TBRetInfo {
	public ArrayList<String> src_names;
	public Boolean need_stop;
	public Integer boundary;
	public Boolean still_tb;
	public Boolean func_call_point;
	public Boolean concrete_val;
	public Boolean halt_point;
	public HashMap<String, Integer> mem_len_map;
	
	public TBRetInfo() {
		src_names = null;
		need_stop = null;
		boundary = null;
		still_tb = null;
		func_call_point = null;
		concrete_val = null;
		halt_point = null;
		mem_len_map = null;
	}
	
	public TBRetInfo(ArrayList<String> src_names, Boolean need_stop, Integer boundary, Boolean still_tb, HashMap<String, Integer> mem_len_map) {
		this.src_names = src_names;
		this.need_stop = need_stop;
		this.boundary = boundary;
		this.still_tb = still_tb;
		this.mem_len_map = mem_len_map;
	}
	
	public TBRetInfo(ArrayList<String> src_names, Boolean func_call_point, Boolean halt_point, Boolean concrete_val) {
		this.src_names = src_names;
		this.func_call_point = func_call_point;
		this.halt_point = halt_point;
		this.concrete_val = concrete_val;
	}
	
	
	public TBRetInfo(ArrayList<String> src_names, Boolean func_call_point, Boolean halt_point, HashMap<String, Integer> mem_len_map) {
		this.src_names = src_names;
		this.func_call_point = func_call_point;
		this.halt_point = halt_point;
		this.mem_len_map = mem_len_map;
	}
}
