package graph;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;

import common.Tuple;

public class Graph {
	
	HashMap<Long, ArrayList<Long>> graphMap;
	ArrayList<ArrayList<Long>> cycleList = new ArrayList<>();
	HashMap<Long, ArrayList<ArrayList<Long>>> cyclesMap = new HashMap<>();
	HashMap<ArrayList<Long>, Integer> cyclesInfo = new HashMap<>();
	
	int cycleNum;
	long startVertex;
	
	
	public Graph(long startVertex) {
		graphMap = new HashMap<>();
		this.startVertex = startVertex;
	}
	
	
	ArrayList<Long> getVertices() {
		return new ArrayList<Long>(graphMap.keySet());
	}
	
	void addVertex(long vertex) {
		if(!graphMap.containsKey(vertex)) {
			graphMap.put(vertex, new ArrayList<Long>());
		}
	}
	
	
	public HashSet<Long> getEdges(long vertex) {
		HashSet<Long> edges = null;
		if(graphMap.containsKey(vertex)) {
			ArrayList<Long> neighbours = graphMap.get(vertex);
			edges = new HashSet<>(neighbours);
		}
		return edges;
	}
	
	
	public HashMap<Long, ArrayList<Long>> getGraphMap() {
		return graphMap;
	}

    ArrayList<Tuple<Long, ArrayList<Long>>> getAllEdges() { 
        return genEdges();
    }

    public void addEdge(long vertex1, long vertex2) {
    	ArrayList<Long> neighbours = null;
    	if(graphMap.containsKey(vertex1)) {
    		neighbours = graphMap.get(vertex1);
    		if(!neighbours.contains(vertex2))
    			neighbours.add(vertex2);
    	}
    	else {
    		neighbours = new ArrayList<>();
    		neighbours.add(vertex2);
    		graphMap.put(vertex1, neighbours);
    	}
    }
    

    public ArrayList<Tuple<Long, ArrayList<Long>>> genEdges() {
    	ArrayList<Tuple<Long, ArrayList<Long>>> edges = new ArrayList<>();
    	for(Long vertex : graphMap.keySet()) {
    		ArrayList<Long> neighbours = graphMap.get(vertex);
    		Tuple<Long, ArrayList<Long>> edge = new Tuple<>(vertex, neighbours);
    		if(!edges.contains(edge)) {;
    			edges.add(edge);
    		}
    	}
    	return edges;
    }


    static ArrayList<Long> genPath(long startVertex, long endVertex, HashMap<Long, Long> prevMap) {
    	ArrayList<Long> path = new ArrayList<>();
    	path.add(endVertex);
    	Long curr = endVertex;
    	Long prev = null;
    	while(curr != startVertex) {
    		prev = prevMap.get(curr);
    		path.add(prev);
    		curr = prev;
    	}
    	Collections.reverse(path);
    	return path;
    }
    
    Tuple<Boolean, ArrayList<Long>> isReachable(long startVertex, long endVertex) {
    	HashMap<Long, Boolean> visited = new HashMap<>();
    	HashMap<Long, Long> prevMap = new HashMap<>();
    	for(Long vertex : graphMap.keySet()) {
    		visited.put(vertex, false);
    	}
    	ArrayList<Long> queue = new ArrayList<>();
    	queue.add(startVertex);
    	visited.put(startVertex, true);
    	while(queue.size() > 0) {
    		Long n = queue.remove(0);
    		if(n == endVertex) {
    			ArrayList<Long> path = genPath(startVertex, endVertex, prevMap);
    			return new Tuple<>(true, path);
    		}
    		for(Long v :graphMap.get(n)) {
    			if(!visited.get(v)) {
    				queue.add(v);
    				prevMap.put(v, n);
    				visited.put(v, true);
    			}
    		}
    	}
    	return new Tuple<>(false, null);
    }
    
    ArrayList<Long> findPath(long startVertex, long endVertex, ArrayList<Long> path) {
    	if(path == null) path = new ArrayList<>();
    	if(startVertex == endVertex) return path;
    	if(!graphMap.containsKey(startVertex)) return null;
    	for(long vertex : graphMap.get(startVertex)) {
    		if(!path.contains(vertex)) {
    			ArrayList<Long> extendedPath = findPath(vertex, endVertex, path);
    			if(extendedPath != null) return extendedPath;
    		}
    	}
    	return null;
    }

    // Find all paths from startVertex to endVertex in graph
    ArrayList<ArrayList<Long>> findAllPath(long startVertex, long endVertex, ArrayList<Long> path) { 
    	ArrayList<ArrayList<Long>> paths = new ArrayList<>();
        path.add(startVertex);
        if(startVertex == endVertex) {
        	paths.add(path);
        	return paths;
        }
        if(!graphMap.containsKey(startVertex)) return paths;
        for(long vertex : graphMap.get(startVertex)) {
        	if(!path.contains(vertex)) {
        		ArrayList<ArrayList<Long>> extendedPaths = findAllPath(vertex, endVertex, path);
        		for(ArrayList<Long> p : extendedPaths)
        			paths.add(p);
        	}
        }
        return paths;
    }

    int vertexDegree(long vertex) {
        ArrayList<Long> neighbours = graphMap.get(vertex);
        int degree = (int) (neighbours.size() + neighbours.stream().filter(e -> e == vertex).count());
        return degree;
    }
    
    
    // Construct a list of isolated vertices
    ArrayList<Long> findIsolatedVertices() {
    	ArrayList<Long> isolated = new ArrayList<>();
    	for(long vertex : graphMap.keySet()) {
    		ArrayList<Long> neighbours = graphMap.get(vertex);
    		if(neighbours == null || neighbours.size() == 0) {
    			isolated.add(vertex);
    		}
    	}
    	return isolated;
    }


    // Return the minimum degree of the vertices
    int minDegree() {
    	int res = 10000000;
    	for(long vertex : graphMap.keySet()) {
    		int vDegree = vertexDegree(vertex);
    		if(vDegree < res) res = vDegree;
    	}
    	return res;
    }
    
    // Return the maximum degree of the vertices
    int maxDegree() {
    	int res = 0;
    	for(long vertex : graphMap.keySet()) {
    		int vDegree = vertexDegree(vertex);
    		if(vDegree > res) res = vDegree;
    	}
    	return res;
    }
    
    void detectCycle(long vertex, long parent, HashMap<Long, Integer> colorMap, HashMap<Long, Long> parentMap) {
    	if(colorMap.get(vertex) == 2) return;
    	if(colorMap.get(vertex) == 1) {
    		ArrayList<Long> vList = new ArrayList<>();
    		long curr = parent;
    		vList.add(curr);
    		while(curr != vertex) {
    			curr = parentMap.get(curr);
    			vList.add(curr);
    		}
    		cycleList.add(vList);
    		cycleNum++;
    	}
    	parentMap.put(vertex, parent);
    	colorMap.put(vertex, 1);
    	for(long v : graphMap.get(vertex)) {
    		if(v == parentMap.get(vertex)) continue;
    		detectCycle(v, vertex, colorMap, parentMap);
    	}
    	colorMap.put(vertex, 2);
    }
    
    
    void detectAllCycles() {
    	HashMap<Long, Integer> colorMap = new HashMap<>();
    	HashMap<Long, Long> parentMap = new HashMap<>();
    	for(long vertex : graphMap.keySet()) {
    		colorMap.put(vertex, 0);
    		parentMap.put(vertex, (long) 0);
    	}
    	
    	cycleNum = 0;
    	ArrayList<Long> vList = graphMap.get(startVertex);
    	
    	detectCycle(vList.get(0), startVertex, colorMap, parentMap);
    	
    	for(ArrayList<Long> cycle : cycleList) {
    		long start = cycle.get(0);
    		ArrayList<ArrayList<Long>> curr = cyclesMap.getOrDefault(start, new ArrayList<>());
    		curr.add(cycle);
    		cyclesInfo.put(cycle, 0);
    	}
    }
    
    public boolean existsCycle(long start) {
    	return cyclesMap.containsKey(start);
    }
    
    
    public int updateCycleCount(long addr, ArrayList<Long> cycle) {
    	int count = 0;
    	if(cyclesMap.containsKey(addr)) {
	    	ArrayList<ArrayList<Long>> addrCycles = cyclesMap.get(addr);
	    	for(ArrayList<Long> curr : addrCycles) {
	    		if(cycle.size() == curr.size()) {
	    			boolean eq = true;
	    			for(int idx = 0; idx < cycle.size(); idx++) {
	    				if(cycle.get(idx) != curr.get(idx)) {
	    					eq = false;
	    					break;
	    				}
	    			}
	    			if(eq) {
	    				count = cyclesInfo.get(curr);
	    				count += 1;
	    				cyclesInfo.put(curr, count);
	    				break;
	    			}
	    		}
	    	}
    	}
    	return count;
    }
    
    
    @Override
    public String toString() {
    	StringBuilder sb = new StringBuilder();
    	sb.append("vertices: ");
    	for(long v : graphMap.keySet()) {
    		sb.append(Long.toHexString(v) + " ");
    	}
    	sb.append("\nedges: ");
    	ArrayList<Tuple<Long, ArrayList<Long>>> edges = genEdges();
    	for(Tuple<Long, ArrayList<Long>> edge : edges) {
    		sb.append(edge.toString() + " ");
    	}
    	return sb.toString();
    }

}
