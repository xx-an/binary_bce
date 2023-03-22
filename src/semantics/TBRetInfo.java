package semantics;

import java.util.ArrayList;
import java.util.HashMap;

public class TBRetInfo {
	public ArrayList<String> srcNames;
	public Integer boundary;
	public Boolean stillTB;
	public Boolean funcCallPoint;
	public Boolean concrete_val;
	public Boolean haltPoint;
	public HashMap<String, Integer> memLenMap;
	
	public TBRetInfo() {
		srcNames = null;
		haltPoint = null;
		boundary = null;
		stillTB = null;
		funcCallPoint = null;
		concrete_val = null;
		memLenMap = null;
	}
	
	public TBRetInfo(ArrayList<String> srcNames, Boolean haltPoint, Integer boundary, Boolean still_tb, HashMap<String, Integer> memLenMap) {
		this.srcNames = srcNames;
		this.haltPoint = haltPoint;
		this.boundary = boundary;
		this.stillTB = still_tb;
		this.memLenMap = memLenMap;
	}
	
	public TBRetInfo(ArrayList<String> srcNames, Boolean func_call_point, Boolean haltPoint, Boolean concrete_val) {
		this.srcNames = srcNames;
		this.funcCallPoint = func_call_point;
		this.haltPoint = haltPoint;
		this.concrete_val = concrete_val;
	}
	
	
	public TBRetInfo(ArrayList<String> srcNames, Boolean func_call_point, HashMap<String, Integer> memLenMap) {
		this.srcNames = srcNames;
		this.funcCallPoint = func_call_point;
		this.memLenMap = memLenMap;
	}
	
	public TBRetInfo(ArrayList<String> srcNames, Boolean func_call_point, Boolean haltPoint, HashMap<String, Integer> memLenMap) {
		this.srcNames = srcNames;
		this.funcCallPoint = func_call_point;
		this.haltPoint = haltPoint;
		this.memLenMap = memLenMap;
	}
}
