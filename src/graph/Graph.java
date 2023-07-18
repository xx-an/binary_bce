package graph;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Stack;

import common.Tuple;
import common.Utils;

public class Graph {
	
	HashMap<Long, HashSet<Long>> graphMap;
	HashMap<Long, HashSet<Stack<Long>>> cyclesMap;
	HashMap<Stack<Long>, Integer> cyclesCount;
	
	long startVertex;
	int longestLength;
	
	
	public Graph(long sVertex) {
		graphMap = new HashMap<>();
		cyclesMap = new HashMap<>();
		cyclesCount = new HashMap<>();
		startVertex = sVertex;
		addVertex(startVertex);
		longestLength = 0;
	}
	
	
	ArrayList<Long> getVertices() {
		return new ArrayList<Long>(graphMap.keySet());
	}
	
	void addVertex(long vertex) {
		if(!graphMap.containsKey(vertex)) {
			graphMap.put(vertex, new HashSet<Long>());
		}
	}
	
	
	public HashSet<Long> getEdges(long vertex) {
		HashSet<Long> edges = null;
		if(graphMap.containsKey(vertex)) {
			edges = graphMap.get(vertex);
		}
		return edges;
	}
	
    public void addEdge(long vertex1, long vertex2) {
    	HashSet<Long> neighbours = graphMap.getOrDefault(vertex1, new HashSet<>());
		if(!neighbours.contains(vertex2))
			neighbours.add(vertex2);
		graphMap.put(vertex1, neighbours);
    	if(!graphMap.containsKey(vertex2)) addVertex(vertex2);
    }
    
    boolean containsEdge(long vertex1, long vertex2) {
    	if(!graphMap.containsKey(vertex1)) return false;
    	HashSet<Long> neighbours = graphMap.get(vertex1);
    	if(!neighbours.contains(vertex2)) return false;
    	return true;
    }
    

    public ArrayList<Tuple<Long, HashSet<Long>>> genEdges() {
    	ArrayList<Tuple<Long, HashSet<Long>>> edges = new ArrayList<>();
    	for(Long vertex : graphMap.keySet()) {
    		HashSet<Long> neighbours = graphMap.get(vertex);
    		Tuple<Long, HashSet<Long>> edge = new Tuple<>(vertex, neighbours);
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
    	HashSet<Long> neighbours = graphMap.get(vertex);
        int degree = (int) (neighbours.size() + neighbours.stream().filter(e -> e == vertex).count());
        return degree;
    }
    
    
    // Construct a list of isolated vertices
    ArrayList<Long> findIsolatedVertices() {
    	ArrayList<Long> isolated = new ArrayList<>();
    	for(long vertex : graphMap.keySet()) {
    		HashSet<Long> neighbours = graphMap.get(vertex);
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
    
    
    boolean containsCycle(Stack<Long> cycle, HashSet<Stack<Long>> cycleList) {
    	return cycleList.contains(cycle);

    }
    
    
    void buildCycle(Stack<Long> stack, long v, ArrayList<Stack<Long>> cycleList) {
    	Stack<Long> cycle = new Stack<>();
    	int idx = stack.size() - 1;
    	long curr = stack.get(idx);
    	cycle.push(curr);
    	while(idx > 0 && curr != v) {
    		idx -= 1;
    		curr = stack.get(idx);
    		cycle.push(curr);
    	}
		cycleList.add(cycle);
    }
    
    
    void processDFSTree(Stack<Long> stack, HashMap<Long, Boolean> visited, ArrayList<Stack<Long>> cycleList) {
    	HashSet<Long> neighbours = graphMap.get(stack.peek());
    	for(long v : neighbours) {
    		if(visited.get(v)) {
    			buildCycle(stack, v, cycleList);
    		}
    		else {
    			stack.push(v);
    			visited.put(v, true);
    			processDFSTree(stack, visited, cycleList);
    		}
    	}	    	
    	visited.put(stack.peek(), false);
	    stack.pop();
    }
    
    void processDFSTree(Stack<Long> stack, HashSet<Long> neighbours, HashMap<Long, Boolean> visited, ArrayList<Stack<Long>> cycleList) {
    	for(long v : neighbours) {
    		if(visited.get(v)) {
    			buildCycle(stack, v, cycleList);
    		}
    		else {
    			stack.push(v);
    			visited.put(v, true);
    			processDFSTree(stack, graphMap.get(stack.peek()), visited, cycleList);
    		}
    	}	    	
    	visited.put(stack.peek(), false);
	    stack.pop();
    }
    
    
    // Detect all the cycles in a directed graph
    void detectAllCycles() {
    	HashMap<Long, Boolean> visited = new HashMap<>();
    	ArrayList<Stack<Long>> cycleList = new ArrayList<>();
    	
    	for(long vertex : graphMap.keySet()) {
    		visited.put(vertex, false);
    	}

    	Stack<Long> stack = new Stack<>();
		stack.push(startVertex);
		visited.put(startVertex, true);
		processDFSTree(stack, visited, cycleList);
    	
    	for(Stack<Long> cycle : cycleList) {
    		Utils.ppCycle(cycle);
    		long start = cycle.peek();
    		HashSet<Stack<Long>> curr = cyclesMap.getOrDefault(start, new HashSet<>());
    		curr.add(cycle);
    		cyclesMap.put(start, curr);
    		cyclesCount.put(cycle, 0);
    		longestLength = Math.max(longestLength, cycle.size());
    	}
    }
    
    
    void updateCycleInfo(long vertex1, long vertex2) {
    	addEdge(vertex1, vertex2);
    	
    	HashMap<Long, Boolean> visited = new HashMap<>();
    	ArrayList<Stack<Long>> cycleList = new ArrayList<>();
    	
    	for(long vertex : graphMap.keySet()) {
    		visited.put(vertex, false);
    	}

    	Stack<Long> stack = new Stack<>();
		stack.push(vertex1);
		visited.put(vertex1, true);
		HashSet<Long> neighbours = new HashSet<>();
		neighbours.add(vertex2);
		processDFSTree(stack, visited, cycleList);
    	
    	for(Stack<Long> cycle : cycleList) {
    		boolean exists = false;
    		for(long vertex : cycle) {
    			if(cyclesMap.containsKey(vertex)) {
    				HashSet<Stack<Long>> curr = cyclesMap.getOrDefault(vertex, new HashSet<>());
    				int idx = cycle.indexOf(vertex);
    				Collections.rotate(cycle, cycle.size() - idx - 1);
    				if(!curr.contains(cycle)) {
    					Utils.ppCycle(cycle);
    					curr.add(cycle);
    					cyclesCount.put(cycle, 0);
    				}
    				cyclesMap.put(vertex, curr);
    				exists = true;
    				break;
    			}
    		}
    		if(!exists) {
    			long vertex = cycle.peek();
    			HashSet<Stack<Long>> curr = cyclesMap.getOrDefault(vertex, new HashSet<>());
    			Utils.ppCycle(cycle);
				curr.add(cycle);
				cyclesMap.put(vertex, curr);
				cyclesCount.put(cycle, 0);
    		}
    		longestLength = Math.max(longestLength, cycle.size());
    	}
    }

    
    public boolean mayExistCycle(long start) {
    	return cyclesMap.containsKey(start);
    }
    
    
    void analyzeCycleInfo(Stack<Long> stack) {
    	for(int i = stack.size() - 1; i >= 0; i--) {
    		
    	}
    }
    
    public int updateCycleCount(long addr, Stack<Long> cycle) {
    	int count = 0;
    	if(cyclesMap.containsKey(addr)) {
	    	HashSet<Stack<Long>> cycles = cyclesMap.get(addr);
	    	if(cycles.contains(cycle)) {
    			count = cyclesCount.get(cycle);
				count += 1;
				cyclesCount.put(cycle, count);
    		}
	    	else {
	    		cycles.add(cycle);
	    		count += 1;
	    		cyclesCount.put(cycle, count);
	    	}
    	}
    	return count;
    }
    
    
    int longestCycleLength() {
    	return longestLength;
    }
    
    
    @Override
    public String toString() {
    	StringBuilder sb = new StringBuilder();
    	sb.append("vertices: ");
    	for(long v : graphMap.keySet()) {
    		sb.append(Long.toHexString(v) + " ");
    	}
    	sb.append("\nedges: ");
    	ArrayList<Tuple<Long, HashSet<Long>>> edges = genEdges();
    	for(Tuple<Long, HashSet<Long>> edge : edges) {
    		sb.append(edge.toString() + " ");
    	}
    	return sb.toString();
    }

}
