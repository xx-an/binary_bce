package graph;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import common.Tuple;
import common.Utils;

public class Graph {
	
	static HashMap<Long, HashSet<Long>> graphMap;
	static HashMap<Long, HashSet<Stack<Long>>> cyclesMap;
	static HashMap<Stack<Long>, Integer> cyclesCount;
	
	long startVertex;
	static int longestLength;
	
	
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

	//Find all the cycles using depth-first search
	private List<Stack<Long>> findCyclesDFS(
            Long start,
            Set<Long> visited,
			Set<Long> inStack
    ) {
        List<Stack<Long>> cycles = new ArrayList<>();
		Stack<Long> stack = new Stack<>();
		Stack<Long> path = new Stack<>();
		Stack<Long> branchNodes = new Stack<>();
        stack.push(start);

        while (!stack.isEmpty()) {
            long curr = stack.pop();
			if (!visited.contains(curr)) {
				visited.add(curr);
				inStack.add(curr);
				path.push(curr);

				// System.out.println("bn: " + Utils.ppCycle(branchNodes));
				// System.out.println("stk: " + Utils.ppCycle(stack));
				// System.out.println("pt: " + Utils.ppCycle(path));

				if(!graphMap.get(curr).isEmpty()) {
					if(graphMap.get(curr).size() > 1) {
						branchNodes.push(curr);
					}
					for (long neighbor : graphMap.get(curr)) {
						if (!visited.contains(neighbor)) {
							stack.push(neighbor);
						} 
						else if (inStack.contains(neighbor)) {
							// Cycle detected
							Stack<Long> cycle = new Stack<>();
							Long tmp = null;
							while (!path.isEmpty() && !path.peek().equals(neighbor)) {
								if(!branchNodes.isEmpty() && branchNodes.peek().equals(path.peek()))
									tmp = path.peek();
								cycle.push(path.pop());
							}
							if(!path.isEmpty() && path.peek().equals(neighbor)) {
								cycle.add(path.pop());
								// System.out.println("cycle: " + Utils.ppCycle(cycle));
								cycles.add(cycle);
							}
							if(tmp != null) {
								branchNodes.pop();
								if(!branchNodes.isEmpty() && !stack.isEmpty()) {
									while (!path.isEmpty() && !path.peek().equals(branchNodes.peek())) {
										path.pop();
									}
								}
							}
						}
					}
				}
				// If a node has no children, which means the path reaches the termination point
				else {
					if(!stack.isEmpty() && !branchNodes.isEmpty()) {
						while (!path.isEmpty() && !path.peek().equals(branchNodes.peek())) {
							path.pop();
						}
						if(!graphMap.get(branchNodes.peek()).contains(stack.peek())) {
							branchNodes.pop();
						}
						// System.out.println("branchNodes: " + Utils.ppCycle(branchNodes));
						// System.out.println("stack: " + Utils.ppCycle(stack));
						// System.out.println("newPath: " + Utils.ppCycle(path));
					}
				}
			}
			else {
				inStack.remove(curr);
				path.remove(curr);
			}
        }
        return cycles;
    }


	// Detect all the cycles in a directed graph
	public void findAllCycles() {
		List<Stack<Long>> cycleList = new ArrayList<>();

        Set<Long> visited = new HashSet<>();
        Set<Long> inStack = new HashSet<>();

        for (Long node : graphMap.keySet()) {
            if (!visited.contains(node)) {
                cycleList.addAll(findCyclesDFS(node, visited, inStack));
            }
        }

		for(Stack<Long> cycle : cycleList) {
			// System.out.println(Utils.ppCycle(cycle));
    		long start = cycle.peek();
    		HashSet<Stack<Long>> curr = cyclesMap.getOrDefault(start, new HashSet<>());
    		curr.add(cycle);
    		cyclesMap.put(start, curr);
    		cyclesCount.put(cycle, 0);
    		longestLength = Math.max(longestLength, cycle.size());
    	}
    }

    
    void updateCycleInfo(Long vertex1, Long vertex2) {
    	addEdge(vertex1, vertex2);
    	
    	List<Stack<Long>> cycleList = new ArrayList<>();

		Set<Long> visited = new HashSet<>();
        Set<Long> inStack = new HashSet<>();
		cycleList = findCyclesDFS(vertex1, visited, inStack);
    	
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
    
    
    public void ppEdges() {
    	StringBuilder sb = new StringBuilder();
    	sb.append("\nedges: ");
    	ArrayList<Tuple<Long, HashSet<Long>>> edges = genEdges();
    	for(Tuple<Long, HashSet<Long>> edge : edges) {
    		long startVertex = edge.x;
    		HashSet<Long> toEdge = edge.y;
    		ArrayList<Long> toEdges = new ArrayList<>();
    		for(long e : toEdge) toEdges.add(e);
    		sb.append(Utils.toHexString(startVertex) + ": [" + String.join(", ", toEdges.stream().map(e -> Utils.toHexString(e)).toList()) + "], ");
    	}
    	System.out.println(sb.toString());
    }
    
    
    @Override
    public String toString() {
    	StringBuilder sb = new StringBuilder();
    	sb.append("vertices: ");
    	for(long v : graphMap.keySet()) {
    		sb.append(Utils.toHexString(v) + " ");
    	}
    	sb.append("\nedges: ");
    	ArrayList<Tuple<Long, HashSet<Long>>> edges = genEdges();
    	for(Tuple<Long, HashSet<Long>> edge : edges) {
    		sb.append(edge.toString() + " ");
    	}
    	return sb.toString();
    }

}
