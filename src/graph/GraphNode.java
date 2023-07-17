package graph;

import java.util.ArrayList;
import java.util.HashMap;

public class GraphNode {
	
	ArrayList<Long> addrList = null;
	long startAddr, endAddr;
	
	public GraphNode(long startAddress, long endAddress, ArrayList<Long> instAddrs) {
		addrList = new ArrayList<>();
		startAddr = startAddress;
		endAddr = endAddress;
		if(instAddrs.contains(startAddr)) {
			int sIdx = instAddrs.indexOf(startAddr);
			if(instAddrs.contains(endAddr)) {
				int eIdx = instAddrs.indexOf(endAddr);
				for(int idx = sIdx; idx <= eIdx; idx++) {
					long addr = instAddrs.get(idx);
					addrList.add(addr);
				}
			}
		}
	}
	
	Boolean locatedInNode(long addr) {
		return addrList.contains(addr);
	}
	
	
	ArrayList<Long> getPath(long sAddr, long eAddr) {
		ArrayList<Long> path = null;
		if(locatedInNode(startAddr) && locatedInNode(endAddr)) {
			path = new ArrayList<>();
			int sIdx = addrList.indexOf(sAddr);
			int eIdx = addrList.indexOf(eAddr);
			for(int idx = sIdx; idx <= eIdx; idx++) {
				long addr = addrList.get(idx);
				path.add(addr);
			}
		}
		return path;
	}
	
	
	ArrayList<Long> getPaths() {
		return addrList;
	}
	
	
	ArrayList<Long> getTailPaths(long addr) {
		ArrayList<Long> path = null;
		if(locatedInNode(addr)) {
			path = new ArrayList<>();
			int idx = addrList.indexOf(addr);
			for(int i = idx; i < addrList.size(); i++) {
				long curr = addrList.get(i);
				path.add(curr);
			}
		}
		return path;

	}
	
	
	String ppNode(HashMap<Long, String> addrInstMap) {
		StringBuilder sb = new StringBuilder();
		for(Long addr : addrList) {
			sb.append(Long.toHexString(addr) + ": " + addrInstMap.get(addr));
		}
		return sb.toString();
	}
	
}
