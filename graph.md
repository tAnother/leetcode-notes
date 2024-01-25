#### Graph Representation
- adjacent matrix
    - space: v^2
    - time: O(1)
- adjacent list
    - space: O(v + e)
    - time: O(e)
    - implementation: Map<Node, List<Node>>


### Common problems
#### search
- traversal
- backtrack(DFS)
- divide & conquer(DFS)

#### shortest path
- consider BFS first
- 如果不是DAG，注意要keep track of visited nodes
- 如果是DAG，那indegree/outdegree应该在adjacency list中体现出来

#### topological sort

e.g. package dependency managers, course prereq satisfication, etc.

- BFS

    calc indegree of each node，then BFS，不断把indegree = 0的node加入结果，并更新其指向的node的indegree

- DFS
    
    a node is added to result only after all its inedges nodes have been visited 

    - think of it as visiting all chilren before parent -- postorder DFS


#### connectivity
- BFS/DFS
- Union find(for dynamic graph)

#### detect cycle

Tree: *acyclic connected* graph

e.g. 130 - recite!
1. construct graph(adjacency list)
2. maintain visited set (or an array of states)
3. bfs, cut off adjacency after adding to queue (*maintain curr - prev relationship*)

    or dfs: coloring
    each node can be in 3 states:
    - 0: not visited
    - 2: visited already
    - 1: visiting (in current dfs path - cycle detected)
    return true if there's no cycle

4. check if all nodes visited

#### bi-partition  

i.e. can u color the map with 2 colors s.t. adjacent nodes are of different colors?

When need to mark visited/unvisited/reachable/unreachable/bipartite, and there are multiple possibilities, consider **coloring**! 
- using nums to represent different states(*state machine*)



### BFS & DFS traversal/iteration
test如何表示：还是用recursion tree/search tree来keep track和backtrack，并且实时更改图 




