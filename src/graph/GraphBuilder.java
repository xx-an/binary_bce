package graph;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Stack;

import common.Lib;
import common.Utils;
import normalizer.Normalizer;

public class GraphBuilder {

	Graph graph;
	HashMap<Long, ArrayList<Long>> jptEntriesMap;
	HashSet<Long> funcEndAddressSet;
	HashMap<Long, String> addrInstMap;
	HashMap<Long, String> addressExtFuncMap;
	ArrayList<Long> instAddrs;
	
	
	public GraphBuilder(long startVertex) {
		graph = new Graph(startVertex);
	}
	
	public GraphBuilder(Normalizer norm) {
		buildGraph(norm);
		graph.detectAllCycles();
	}
	
	
	public void detectAllCycles() {
		graph.detectAllCycles();
	}
	
	
	public boolean mayExistCycle(long addr) {
		return graph.mayExistCycle(addr);
	}
	
	
	public int updateCycleCount(long addr, Stack<Long> cycle) {
		return graph.updateCycleCount(addr, cycle);
	}
	
	public int longestCycleLength() {
		return graph.longestCycleLength();
	}
	
	
	void buildGraph(Normalizer norm) {
		long entryAddr = norm.getMainAddress();
		graph = new Graph(entryAddr);
		jptEntriesMap = norm.readGlobalJPTEntriesMap();
		funcEndAddressSet = norm.getFuncEndAddrSet();
		addrInstMap = norm.getAddressInstMap();
		addressExtFuncMap = norm.getAddressExtFuncMap();
		instAddrs = new ArrayList<>(addrInstMap.keySet());
		Collections.sort(instAddrs);
		constructGraph();
//		graph.ppEdges();
	}
	
	
	public void addEdge(long vertex1, long vertex2) {
		graph.addEdge(vertex1, vertex2);
	}

	
	public void updateCycleInfo(long vertex1, long vertex2) {
		graph.updateCycleInfo(vertex1, vertex2);
	}
	
	
	public boolean containsEdge(long vertex1, long vertex2) {
		return graph.containsEdge(vertex1, vertex2);
	}
	
	
	public void addVertex(long vertex) {
		graph.addVertex(vertex);
	}
	
	
	void resolveJPTEdges(int idx, long addr, String inst, String jmpAddrStr) {
		// inst: jmp dword ptr [edx*4+0x402d34]
		if(jmpAddrStr.endsWith("]")) {
			buildJPTEntries(addr, jmpAddrStr);
		}
		// inst: jmp eax
		else if(Lib.REG_NAMES.contains(jmpAddrStr)) {
			if(idx > 0) {
				long prevAddr = instAddrs.get(idx - 1);
				String prevInst = addrInstMap.get(prevAddr);
				// prevInst: mov     eax, [edi*4 + 0x40FC04]
				if(prevInst.startsWith("mov ")) {
					String movSrc = prevInst.split(",", 2)[1].strip();
					if(movSrc.endsWith("]")) {
						buildJPTEntries(addr, movSrc);
					}
				}
			}
		}
	}
	
	
    void constructGraph() {
    	for(int idx = 0; idx < instAddrs.size() - 1; idx++) {
    		long addr = instAddrs.get(idx);
    		long nextAddr = instAddrs.get(idx + 1);
    		String inst = addrInstMap.get(addr);
    		graph.addVertex(addr);
    		if(Utils.check_branch_inst(inst)) {
    			if(Utils.check_jmp_with_address(inst)) {
    				String[] instSplit = inst.split(" ", 2);
        			String jmpAddrStr = instSplit[1].strip();
        			Long jmpAddr = null;
        			if(Utils.imm_start_pat.matcher(jmpAddrStr).find()) {
        				jmpAddr = Utils.imm_str_to_int(jmpAddrStr);
        				if(jmpAddr != null && !addressExtFuncMap.containsKey(jmpAddr)) {
        					graph.addEdge(addr, jmpAddr);
            			}
        			}
        			else if(inst.startsWith("jmp ")) {
        				resolveJPTEdges(idx, addr, inst, jmpAddrStr);
        			}
    			}
    			if(Utils.check_not_single_branch_inst(inst) || inst.startsWith("call")) {
        			graph.addEdge(addr, nextAddr);
        		}
    		}
    		else if(!funcEndAddressSet.contains(addr)) {
    			graph.addEdge(addr, nextAddr);
    		}
    	}
    }

    
    void buildJPTEntries(long addr, String jmpAddrStr) {
    	String jmpAddrMemStr = Utils.extract_content(jmpAddrStr, "[");
		if(jmpAddrMemStr.contains("+")) {
			ArrayList<Long> jptTargets = null;
	    	String[] addrMemSplit = jmpAddrMemStr.split("\\+");
			String offsetStr = addrMemSplit[addrMemSplit.length - 1];
			if(Utils.imm_start_pat.matcher(offsetStr).find()) {
				long offsetValue = Utils.imm_str_to_int(offsetStr);
				if(jptEntriesMap.containsKey(offsetValue)) {
					jptTargets = jptEntriesMap.get(offsetValue);
					for(long jptEntry : jptTargets) {
						graph.addEdge(addr, jptEntry);
					}
				}
			}
		}
    }
}
