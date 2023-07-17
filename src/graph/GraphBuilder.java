package graph;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;

import common.Lib;
import common.Tuple;
import common.Utils;
import normalizer.Normalizer;

public class GraphBuilder {

//	HashMap<Long, GraphNode> nodeMap;
	Graph graph;
	HashMap<Long, ArrayList<Long>> addrEntriesMap;
	HashMap<Long, ArrayList<Long>> jptEntriesMap;
	HashSet<Long> callToAddrSet;
	HashMap<Long, String> addrInstMap;
	HashMap<Long, String> extFuncMap;
	HashMap<Long, String> addrSymMap;
	ArrayList<Long> instAddrs;
	ArrayList<Long> startAddrs;
	ArrayList<Long> endAddrs;
	
	
	void buildGraph(Normalizer norm) {
//		nodeMap = new HashMap<>();
		long entryAddr = (norm.getEntryAddress() != null) ? norm.getEntryAddress() : norm.getMainAddress();
		graph = new Graph(entryAddr);
		addrEntriesMap = new HashMap<>();
		jptEntriesMap = norm.readGlobalJPTEntriesMap();
		callToAddrSet = new HashSet<>();
		addrInstMap = norm.getAddressInstMap();
		extFuncMap = norm.getAddressExtFuncMap();
		addrSymMap = norm.getAddressSymTbl();
		instAddrs = new ArrayList<>(addrInstMap.keySet());
		Collections.sort(instAddrs);
		organizeAddrEntries(norm);
		String newContent = reconstructContent();
		divideBlocks(newContent);
		constructGraph();
	}
	
	
    void constructGraph() {
    	for(long addr : addrInstMap.keySet()) {
    		graph.addVertex(addr);
    		String inst = addrInstMap.get(addr);
    	}
    	for(int idx = 0; idx < startAddrs.size(); idx++) {
    		long startAddr = startAddrs.get(idx);
    		long endAddr = endAddrs.get(idx);
//    		addNode(startAddr, endAddr, instAddrs);
    		addEdge(startAddr);
    	}
    }
    
    void organizeAddrEntries(Normalizer norm) {
    	for(long addr : addrInstMap.keySet()) {
    		String inst = addrInstMap.get(addr);
    		if(Utils.check_branch_inst(inst)) {
    			if(Utils.check_jmp_with_address(inst)) {
    				String[] instSplit = inst.split(" ", 2);
        			String instName = instSplit[0];
        			String jmpAddrStr = instSplit[1];
        			Long jmpAddr = null;
        			if(Utils.imm_start_pat.matcher(jmpAddrStr).find()) {
        				jmpAddr = Utils.imm_str_to_int(jmpAddrStr);
        				if(jmpAddr != null) {
            				addToAddrEntriesMap(jmpAddr, addr);
            				if(instName.startsWith("call"))
            					callToAddrSet.add(addr);
            			}
        			}
        			// inst: jmp dword ptr [edx*4+0x402d34]
        			else if(jmpAddrStr.endsWith("]")) {
        				buildJPTEntries(jmpAddrStr, addr);
        			}
        			// inst: jmp eax
        			else if(Lib.REG_NAMES.contains(jmpAddrStr)) {
        				int idx = instAddrs.indexOf(addr);
        				if(idx > 0) {
        					long prevAddr = instAddrs.get(idx - 1);
        					String prevInst = addrInstMap.get(prevAddr);
        					// prevInst: mov     eax, [edi*4 + 0x40FC04]
        					if(prevInst.startsWith("mov ")) {
        						String movSrc = prevInst.split(", ", 2)[1].strip();
        						if(movSrc.endsWith("]")) {
        							buildJPTEntries(movSrc, addr);
        						}
        					}
        				}
        			}
    			}
    		}
    	}
    }
    
    
    String reconstructContent() {
    	StringBuilder sb = new StringBuilder();
    	Long prevAddr = null;
    	for(long addr : addrInstMap.keySet()) {
    		if(addrSymMap.containsKey(addr)) sb.append("\n");
    		else if(notContinuous(prevAddr)) {
    			String prevInst = addrInstMap.get(prevAddr);
    			if(Utils.check_not_single_branch_inst(prevInst))
    				addToAddrEntriesMap(addr, prevAddr);
    			sb.append("\n");
    		}
    		else if(addrEntriesMap.containsKey(addr)) {
    			ArrayList<Long> entries = addrEntriesMap.get(addr);
    			entries.add(prevAddr);
    			sb.append("\n");
    		}
    		sb.append(Long.toHexString(addr));
    		prevAddr = addr;
    	}
    	return sb.toString();
    }
    
    
    void divideBlocks(String content) {
    	startAddrs = new ArrayList<>();
    	endAddrs = new ArrayList<>();
    	boolean exists = false;
    	String[] lines = content.split("\n");
    	Long addr = null;
    	for(String line : lines) {
    		if(line != "") {
    			addr = Utils.imm_str_to_int(line);
    			if(!exists) {
    				startAddrs.add(addr);
    				exists = true;
    			}
    		}
    		else {
    			if(exists) endAddrs.add(addr);
    			exists = false;
    		}
    	}
    }

    
    void buildJPTEntries(String jmpAddrStr, long addr) {
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
						addToAddrEntriesMap(jptEntry, addr);
					}
				}
			}
		}
    }


    void addVertex(long startAddr, long endAddr, ArrayList<Long> instAddrs) {
//        GraphNode node = new GraphNode(startAddr, endAddr, instAddrs);
//        nodeMap.put(startAddr, node);
        graph.addVertex(startAddr);
    }


    void addEdge(long addr) {
    	if(addrEntriesMap.containsKey(addr)) {
    		ArrayList<Long> entries = addrEntriesMap.get(addr);
    		for(long entry : entries) {
    			Long nodeID = searchNodeID(entry);
    			if(nodeID != null) {
    				if(addr != nodeID) {
    					graph.addEdge(nodeID, addr);
    				}
    			}
    		}
    	}
    }
    
    
    Long searchNodeID(long addr) {
    	Long nodeID = null;
    	for(int idx = 0; idx < startAddrs.size(); idx++) {
    		long startAddr = startAddrs.get(idx);
    		long endAddr = endAddrs.get(idx);
    		if(addr >= startAddr && addr <= endAddr) {
    			GraphNode node = nodeMap.get(startAddr);
    			if(node.locatedInNode(addr))
    				nodeID = startAddr;
    			break;
    		}
    	}
    	return nodeID;
    }
    
    
    void printNodePath(ArrayList<Long> nodePath) {
    	for(long nodeID : nodePath) {
    		GraphNode node = nodeMap.get(nodeID);
    		String res = node.ppNode(addrInstMap);
    		System.out.println(res);
    		System.out.println("\n");
    	}
    }


    ArrayList<Long> findPath(long startAddr, long endAddr) {
    	ArrayList<Long> path = null;
    	Long startNodeID = searchNodeID(startAddr);
    	Long endNodeID = searchNodeID(endAddr);
    	if(startNodeID != null && endNodeID != null) {
    		if(startNodeID == endNodeID) {
    			GraphNode node = nodeMap.get(startNodeID);
    			path = node.getPath(startAddr, endAddr);
    		}
    		else {
    			Tuple<Boolean, ArrayList<Long>> res = graph.isReachable(startNodeID, endNodeID);
    			if(res.x) {
    				path = new ArrayList<>();
    				int idx = 0;
    				int nodeListSize = res.y.size();
    				ArrayList<Long> tmp = null;
    				for(long nodeID : res.y) {
    					GraphNode node = nodeMap.get(nodeID);
    					if(idx == 0) {
    						tmp = node.getTailPaths(startAddr);
    					}
    					else if(idx == nodeListSize - 1) {
    						tmp = node.getPath(nodeID, endAddr);
    					}
    					else {
	    					tmp = node.getPaths();
    					}
    					path.addAll(tmp);
    					idx++;
    				}
    			}
    		}
    	}
    	return path;
    }


    boolean notContinuous(Long prevAddr) {
    	if(prevAddr != null) {
    		String prevInst = addrInstMap.get(prevAddr);
    		/*** If previous instruction is a branch instruction (not call instruction)
    		, then current address and previous address are divided to different blocks ***/
    		if(Utils.check_branch_inst_wo_call(prevInst)) return true;
    		else if(prevInst.startsWith("call")) {
    			/*** If previous instruction is call instruction, and the jump address is an internal address, 
    			/ then current address and previous address are divided to different blocks ***/
    			if(callToAddrSet.contains(prevAddr)) return true;
    		}
    	}
    	return false;
    }
    
    
    void addToAddrEntriesMap(long addr, long entry) {
    	if(addrEntriesMap.containsKey(addr)) {
    		ArrayList<Long> entries = addrEntriesMap.get(addr);
    		if(!entries.contains(entry))
    			entries.add(entry);
    	}
    	else {
    		ArrayList<Long> entries = new ArrayList<>();
    		entries.add(entry);
    		addrEntriesMap.put(addr, entries);
    	}
    }


    void draw() {
    	ArrayList<Long> vertices = graph.getVertices();
    	StringBuilder sb = new StringBuilder();
        sb.append("digraph cfg {\n");
        sb.append("    node [shape=record];\n");
        for(long vertex : vertices) {
        	sb.append(drawNode(vertex));
        	HashSet<Long> edges = graph.getEdges(vertex);
        	for(long neighbour : edges) 
            	sb.append(drawEdge(vertex, neighbour));
        }
        sb.append("}");
        String dotPath = Utils.PROJECT_DIR.toString() + "graph";
        Utils.writeToFile(dotPath + ".dot", sb.toString());
        Utils.convertDotToPng(dotPath);
    }

    String drawNode(long nodeID) {
    	StringBuilder sb = new StringBuilder();
    	String hexNodeID = Long.toHexString(nodeID);
    	sb.append("    node_" + hexNodeID + " [label=\"");
        sb.append("<n" + hexNodeID + "> ");
        sb.append(hexNodeID);
        sb.append("\"];\n");
        return sb.toString();
    }

    String drawEdge(long startNodeID, long endNodeID) {
        StringBuilder sb = new StringBuilder();
        String hexStartNodeID = Long.toHexString(startNodeID);
        String hexEndNodeID = Long.toHexString(endNodeID);
        sb.append("    node_" + hexStartNodeID + ":n" + hexStartNodeID);
        sb.append(" -> ");
        sb.append("node_" + hexEndNodeID + ":n" + hexEndNodeID);
        sb.append(";\n");
        return sb.toString();
    }

}
