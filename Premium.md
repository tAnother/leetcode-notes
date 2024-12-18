#### [Inorder successor in BST](https://leetcode.com/problems/inorder-successor-in-bst/description/)

```java
class Solution {
    // find the "smallest" node larger than p
    public TreeNode inorderSuccessorRecur(TreeNode root, TreeNode p) {
        if (root == null) return null;
        
        if (root.val <= p.val) // the smallest node > p should live in the right subtree
            return inorderSuccessor(root.right, p);
        
        // the smallest node > p should live in the left subtree or be the root
        TreeNode left = inorderSuccessor(root.left, p);
        return left == null ? root : left;
    }
    
    // reduced version of an inorder traversal
    public TreeNode inorderSuccessor(TreeNode root, TreeNode p) {
        if (root == null) return null;
        Stack<TreeNode> st = new Stack<>();
        st.push(root);
        boolean foundp = false;
        
        while (!st.isEmpty()) {
            TreeNode n = st.pop();
            if (n.left == null && n.right == null) {
                if (foundp) {   // the node after p in inorder traversal
                    return n;
                }
                if (n.val == p.val) 
                    foundp = true;
            } else {
                if (n.right != null && p.val >= n.val) st.push(n.right);
                st.push(new TreeNode(n.val));
                if (n.left != null && p.val < n.val) st.push(n.left);
            }
        }
        return null;
    }
}

// root = [5,3,6,2,4,null,null,1], p = 4
// helper(5, 4) -> root(=5)
//      left: helper(3, 4) -> null
//          right: helper(4, 4) -> null
//               right: helper(null, 4) -> null
```

#### [Search in a sorted array of unknown size](https://leetcode.com/problems/search-in-a-sorted-array-of-unknown-size/description/)
>Given an integer array sorted in ascending order, write a function to search target in nums. If target exists, then return its index, otherwise return -1. However, the array size is unknown to you.

> You may only access the array using an ArrayReader interface, where ArrayReader.get(k) returns the element of the array at index k (0-indexed).
You may assume all integers in the array are less than 10000, and if you access the array out of bounds, ArrayReader.get will return 2147483647.

```java
final static int OUT_OF_BOUND = 2147483647;
    
public int search(ArrayReader reader, int target) {
    // array [first ... target]
    // since element in the array are unique, the right bound of the index = target - first
    int first = reader.get(0);
    if (first == OUT_OF_BOUND) return -1;
    
    int l = 0, r = target - first;
    while (l + 1 < r) {
        int m = l + (r - l) / 2;
        int num = reader.get(m);
        if (num == target) return m;
        if (num == OUT_OF_BOUND || num > target) {
            r = m;
        } else {
            l = m;
        }
    }
    
    // base case
    if (reader.get(l) == target) return l;
    if (reader.get(r) == target) return r;
    return -1;
}
```




#### [Meeting Rooms II]()
>Given an array of meeting time intervals intervals where intervals[i] = [starti, endi], return the minimum number of conference rooms required.

```java
class TimeNode {
    boolean isEnd;
    int time;
    TimeNode() {}
    TimeNode(boolean end, int t) {
        time = t;
        isEnd = end;
    }
}

public int minMeetingRooms(int[][] intervals) {
    // find max overlap num
    
    TimeNode[] tl = new TimeNode[intervals.length * 2];
    for (int i = 0; i < intervals.length; i++) {
        tl[i] = new TimeNode(false, intervals[i][0]);
        tl[i + intervals.length] = new TimeNode(true, intervals[i][1]);
    }
    
    // must make sure end is before start at the same time position
    Arrays.sort(tl, (a, b) -> {
        if (a.time != b.time) return Integer.compare(a.time, b.time);
        if (a.isEnd) return -1;
        return 1;
    });
    
    // scan timeline from left to right
    // room = num rooms currently occupied 
    // - encounter start: room++
    // - encounter end: room--
    
    int activeRoom = 0;
    int res = 0;
    for (TimeNode n : tl) {
        if (n.isEnd) activeRoom--;
        else activeRoom++;
        res = Math.max(res, activeRoom);
    }
    return res;
}
```

#### [Graph Valid Tree]()
>You have a graph of n nodes labeled from 0 to n - 1. You are given an integer n and a list of edges where edges[i] = [ai bi] indicates that there is an undirected edge between nodes ai and bi in the graph.\
Return true if the edges of the given graph make up a valid tree, and false otherwise.
>
>Input: n = 5, edges = [[0,1],[0,2],[0,3],[1,4]]\
Output: true
```java
public boolean validTree(int n, int[][] edges) {
    // construct adj list
    Map<Integer, Set<Integer>> g = new HashMap<>();
    for (int[] e : edges) {
        g.putIfAbsent(e[0], new HashSet<>());
        g.putIfAbsent(e[1], new HashSet<>());
        g.get(e[0]).add(e[1]);
        g.get(e[1]).add(e[0]);
    }
    
    Set<Integer> visited = new HashSet<>();
    Queue<Integer> q = new LinkedList<>();
    q.offer(0);
    visited.add(0);
    
    while (!q.isEmpty()) {
        int node = q.poll();
        for (int nbr : g.get(node)) {
            if (visited.contains(nbr)) return false;
            // add to queue and set as visited
            visited.add(nbr);
            q.add(nbr);
            g.get(nbr).remove(node); // prevent repetition
        }
    }
    
    return visited.size() == n;
}
```



#### [Walls and Gates]()

>You are given an m x n grid rooms initialized with these three possible values.\
-1 A wall or an obstacle.\
0 A gate.\
INF Infinity means an empty room. We use the value 231 - 1 = 2147483647 to represent INF as you may assume that the distance to a gate is less than 2147483647.\
Fill each empty room with the distance to its nearest gate. If it is impossible to reach a gate, it should be filled with INF.


```java
final int INF = 2147483647;
final int WALL = -1;
final int GATE = 0;
final int[][] dirs = {{0, 1}, {0, -1}, {-1, 0}, {1, 0}};
int m;
int n;
// do bfs starting from each gate to populate distance to each room
// update if better route found (if bfs, there won't be better route)

public void wallsAndGates(int[][] rooms) {
    m = rooms.length;
    n = rooms[0].length;
    Queue<int[]> q = new LinkedList<>(); // index of rooms whose neighbors to update
    
    for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
            if (rooms[i][j] == GATE) 
                q.offer(new int[]{i, j});
        }
    }
    
    while(!q.isEmpty()) {
        int[] idx = q.poll();
        for (int[] dir : dirs) {
            int i = idx[0], j = idx[1];
            int x = i + dir[0];
            int y = j + dir[1];
            // since we're doing bfs from multiple gates (dist = 0)
            // if a room is not in init state (dist = INF), it must already be set to optimal dist
            // so the last condition could just be checking rooms[x][y] == INF
            // plus, if doing level order bfs, can just set rooms[x][y] to level/depth
            if (valid(x, y) && rooms[x][y] != WALL && 
                rooms[x][y] > rooms[i][j] + 1) {
                rooms[x][y] = rooms[i][j] + 1;
                q.offer(new int[]{x, y});
            }
        }
    }
}

private boolean valid(int x, int y) {
    return x >= 0 && x < m && y >= 0 && y < n;
}
```

#### [Closest Binary Search Tree Value]()

```java
double smaller = Integer.MAX_VALUE;
double larger = Integer.MIN_VALUE;
public int closestValue(TreeNode root, double target) {
    // if ((double)root.val == target) return target;
    if (root == null) {
        return Math.abs(smaller - target) > Math.abs(larger - target) ? (int)larger : (int)smaller;
    }
    
    if ((double)root.val < target) { // search right
        smaller = (double)root.val;
        return closestValue(root.right, target);
    } else {    // search left
        larger = (double)root.val;
        return closestValue(root.left, target);
    }
}

// ================================
public int closestValue(TreeNode root, double target) {
    int res = -1;
    double minDelta = Double.MAX_VALUE;
    
    while (root != null) {
        if (target == (double)root.val) {
            return root.val;
        }
        
        double delta = Math.abs(target - (double)root.val);
        if (delta < minDelta) {
            res = root.val;
            minDelta = delta;
        }
        
        root = target < (double)root.val ? root.left : root.right;
    }
    return res;
}
    
public int closestValueRecur(TreeNode root, double target) {
    if ((double)root.val == target) return root.val;
    double delta = Math.abs((double)root.val - target);
    
    if (target < root.val) {
        if (root.left == null) return root.val;
        if (Math.abs((doube)root.left.val - target) >= delta) return root.val;
        return helper(root.left, target);
    } else {
        if (root.right == null) return root.val;
        if (Math.abs((doube)root.right.val - target) >= delta) return root.val;
        return helper(root.right, target);
    }
}
```

#### [Binary Tree Longest Consecutive Sequence]()
> Given the root of a binary tree, return the length of the longest consecutive sequence path (from parent to child).

```java
int longest = 0;
    
public int longestConsecutive(TreeNode root) {
    helper(root);
    return longest;
}

public int helper(TreeNode root) {
    if (root == null) return 0;
    
    int left = helper(root.left);
    int right = helper(root.right);
    int res = 1;    // longest consecutive sequence starting with root
    
    if (root.left != null && root.left.val == root.val + 1) {
        res = left + 1;
    }
    if (root.right != null && root.right.val == root.val + 1) {
        res = Math.max(res, right + 1);
    }
    
    // update global longest
    longest = Math.max(longest, res);
    
    return res;
}
```

> Given the root of a binary tree, return the length of the longest consecutive path in the tree. This path can be either increasing or decreasing.\
For example, [1,2,3,4] and [4,3,2,1] are both considered valid, but the path [1,2,4,3] is not valid.\
On the other hand, the path can be in the child-Parent-child order, where not necessarily be parent-child order.

```java
int longest = 1;
    
public int longestConsecutive(TreeNode root) {
    helper(root);   // rely on side effect
    return longest;
}

// return [length of (...root.val) i.e. consecutive seq ending with root, length of (root.val...)]
int[] helper(TreeNode root) {
    if (root == null) return new int[]{0, 0};

    int[] left = helper(root.left);
    int[] right = helper(root.right);
    int[] res = new int[]{1, 1};
    
    // construct local res
    if (root.left != null && root.left.val + 1 == root.val) {
        res[0] = left[0] + 1;
    } else if (root.left != null && root.left.val == root.val + 1) {
        res[1] = left[1] + 1;
    }
    if (root.right != null && root.right.val + 1 == root.val) {
        res[0] = Math.max(res[0], right[0] + 1);
    } else if (root.right != null && root.right.val == root.val + 1) {
        res[1] = Math.max(res[1], right[1] + 1);
    }
    
    // update global max
    // case one: the root forms a consecutive seq with two children
    if (root.left != null && root.right != null) {
        if (root.left.val + 1 == root.val && root.val + 1 == root.right.val) {
            longest = Math.max(longest, left[0] + right[1] + 1);
        } else if (root.right.val + 1 == root.val && root.val + 1 == root.left.val) {
            longest = Math.max(longest, right[0] + left[1] + 1);
        }
    }
    longest = Math.max(longest, res[0]);
    longest = Math.max(longest, res[1]);
    return res;
}
```

#### Number of Connected Components in an undirected graph

```java
public int countComponentsDFS(int n, int[][] edges) {
    // construct adj list
    Map<Integer, List<Integer>> g = new HashMap<>();
    for (int i = 0; i < n; i++) 
        g.put(i, new ArrayList<>());
    for (int[] e : edges) {
        g.get(e[0]).add(e[1]);
        g.get(e[1]).add(e[0]);
    }
     
    BitSet visited = new BitSet(n);
    int count = 0;
    for (int i = 0; i < n; i++) {
        if (visited.get(i)) continue;
        count++;
        dfs(g, i, visited);
    }
    
    return count;
}

private void dfs(Map<Integer, List<Integer>> g, int node, BitSet visited) {
    for (int nbr : g.get(node)) {
        if (visited.get(nbr)) continue;
        visited.set(nbr);
        dfs(g, nbr, visited);
    }
}
```

#### Maximum Size Subarray Sum Equals k

> Given an integer array nums and an integer k, return the maximum length of a subarray that sums to k. If there isn't one, return 0 instead.

```java
public int maxSubArrayLen(int[] nums, int k) {
    // calc prefix sum, then find the range sum
    // (note that sums[-1] = 0)
    //  - if sums is monotonically increasing, finding left bound -> a binary search
    //  - but it's not! e.g. sums = {1, 0, 5, 3, 6} is not monotonically increasing
    // work around: trade space for time! 
    // map each possible prefix sum to its (smallest) index
    // iterate prefix sum, find the prefix sum == **sums[r] - target**
    //  - if exists, calc length
    
    int[] sums = new int[nums.length + 1];
    sums[0] = 0;
    Map<Integer, Integer> m = new HashMap<>();
    
    int sum = 0;
    for (int i = 0; i < nums.length; i++) {
        sum += nums[i];
        sums[i+1] = sum;
        m.putIfAbsent(sum, i+1);
    }
    
    int res = 0;
    for (int r = 1; r <= nums.length; r++) {    // note that r is exclusive -- can go up to nums.length!
        if (sums[r] == k) {
            res = Math.max(res, r);
        } else if (m.containsKey(sums[r] - k)) {
            int l = m.get(sums[r] - k);
            res = Math.max(res, r - l);
        }
    }
    return res;
    
    // further optimize: combine 2 loops
}
```

#### Number of Distinct Islands
> You are given an m x n binary matrix grid. An island is a group of 1's (representing land) connected 4-directionally (horizontal or vertical.) You may assume all four edges of the grid are surrounded by water.

> An island is considered to be the same as another if and only if one island can be translated (and not rotated or reflected) to equal the other.

```java
class Solution {
    int m, n;
    boolean[][] visited;
    int[][] dirs = {{1,0}, {-1,0}, {0,1}, {0,-1}};
    
    public int numDistinctIslands(int[][] grid) {
        m = grid.length;
        n = grid[0].length;
        visited = new boolean[m][n];
        Set<String> patterns = new HashSet<>();
        
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
                if (!visited[i][j] && grid[i][j] == 1) {
                    String pattern = bfs(grid, i, j);
                    patterns.add(pattern);
                }
            }
        }
        
        return patterns.size();
    }
    
    // bfs to make sure the pattern is preserved
    String bfs(int[][] grid, int i, int j) {
        visited[i][j] = true;
        Queue<int[]> q = new LinkedList<>();
        q.offer(new int[]{i, j});
        
        StringBuilder sb = new StringBuilder();
        
        while (!q.isEmpty()) {
            int[] p = q.poll();
            for (int d = 0; d < 4; d++) {
                int x = p[0] + dirs[d][0];
                int y = p[1] + dirs[d][1];
                if (x >= 0 && x < m && y >= 0 && y < n && !visited[x][y] && grid[x][y] == 1) {
                    sb.append(d); // memorize direction
                    visited[x][y] = true;
                    q.offer(new int[]{x, y});
                }
            }
            sb.append(",");
        }
        return sb.toString();
    }
}
```

#### LCA of a binary tree II
> If either node does not exist, return null;
```java
class Result {
    int count;
    TreeNode a; // possible lca
    Result(int count, TreeNode a) {
        this.count = count;
        this.a = a;
    }
}

public TreeNode lowestCommonAncestor(TreeNode root, TreeNode p, TreeNode q) {
    Result res = helper(root, p, q);
    return res.count == 2 ? res.a : null;
}

private Result helper(TreeNode root, TreeNode p, TreeNode q) {
    if (root == null) return new Result(0, null);
    
    Result l = helper(root.left, p, q);
    if (l.count == 2) return l; // short circuit / cut off earlier
    
    Result r = helper(root.right, p, q);
    if (r.count == 2) return r;
    
    // combine results
    if (l.count == 1 && r.count == 1) return new Result(2, root);
    if (root == p || root == q) return new Result(l.count + r.count + 1, root);
    if (l.count == 0) return r;
    return l;
}
```
