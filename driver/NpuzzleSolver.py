from __future__ import print_function
from collections import deque
from math import sqrt
import getopt
import heapq
import itertools
import os
import sys
import timeit

def memory():
    """Returns program's memory usage, Windows or Unix."""
    if os.name == 'posix':
        import resource
        return float(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024)
    else:
        import psutil
        p = psutil.Process()
        return float(p.memory_info().rss / 1048576)

class Node(object):
    """Represents a node."""
    def __init__(self, state, path, parent, depth):
        self.state = state
        self.path = path
        self.parent = parent
        self.depth = depth
    def __eq__(self, other):
        return self.state == other[3].state

class Solver(object):
    """Handles all solving methods."""
    def __init__(self, initial_node):
        self.n = len(initial_node.state)
        self.row = int(sqrt(self.n))
        self.top = range(0, self.row)
        self.bottom = range(self.row * (self.row - 1), self.n)
        self.left = [i * self.row for i in range(0, self.row)]
        self.right = [i * self.row + self.row - 1 for i in range(0, self.row)]
        self.fringe_size = 0
        self.max_fringe_size = 0
        self.nodes_expanded = 0
        self.search_depth = 0
        self.max_search_depth = 0
        self.path_to_goal = []
        self.memory_usage = 0
    def solvable(self, state):
        """Teests if puzzle is solvable."""
        inversions = 0
        cfg = list(state)
        cfg.remove(0)
        ayy = reversed(range(len(cfg)))
        for i in reversed(range(len(cfg))):
            for j in range(len(cfg)):
                if j < i and cfg[j] > cfg[i]:
                    inversions += 1
        return inversions % 2 == 0
    def generate_state(self, current_node, direction, zero_index):
        """Generates a new state.
        
        Attributes:
            current_node -- state to generate new state from
            direction -- direction from current state to get to new state
        """
        if direction == 1:
            next_index = int(zero_index - sqrt(self.n))
        elif direction == 2:
            next_index = int(zero_index + sqrt(self.n))
        elif direction == 3:
            next_index = int(zero_index - 1)
        else:
            next_index = zero_index + 1
        next_state = list(current_node.state)
        next_state[zero_index] = current_node.state[next_index]
        next_state[next_index] = current_node.state[zero_index]
        next_direction = direction
        return Node(next_state, next_direction, current_node, current_node.depth + 1)
    def generate_neighbours(self, current_node):
        """Generates list of given state's neighbours."""
        zero_index = current_node.state.index(0)
        neighbours = []
        if zero_index not in self.top and not current_node.path == 2:
            neighbours.append(self.generate_state(current_node, 1, zero_index))
        if zero_index not in self.bottom and not current_node.path == 1:
            neighbours.append(self.generate_state(current_node, 2, zero_index))
        if zero_index not in self.left and not current_node.path == 4:
            neighbours.append(self.generate_state(current_node, 3, zero_index))
        if zero_index not in self.right and not current_node.path == 3:
            neighbours.append(self.generate_state(current_node, 4, zero_index))
        return neighbours
    def generate_neighbours_RLDU(self, current_node):
        """Generates given state's neighbours in reverse order."""
        zero_index = current_node.state.index(0)
        neighbours = []
        if zero_index not in self.right and not current_node.path == 3:
            neighbours.append(self.generate_state(current_node, 4, zero_index))
        if zero_index not in self.left and not current_node.path == 4:
            neighbours.append(self.generate_state(current_node, 3, zero_index))
        if zero_index not in self.bottom and not current_node.path == 1:
            neighbours.append(self.generate_state(current_node, 2, zero_index))
        if zero_index not in self.top and not current_node.path == 2:
            neighbours.append(self.generate_state(current_node, 1, zero_index))
        return neighbours
    def retrace_path(self, initial_node, current_node):
        """Genetrates path from initial to current state."""
        directions = ["None", "Up", "Down", "Left", "Right"]
        path_to_goal = []
        while not str(current_node.state) == str(initial_node.state):
            path_to_goal.append(directions[current_node.path])
            current_node = current_node.parent
        return path_to_goal[::-1]
    def manhattan_distance(self, current_node, goal_state):
        """Returns Manhattan distance from current state to goal."""
        m_distance = 0
        for n in range(1, self.n):
            current_index = current_node.state.index(n)
            goal_index = goal_state.index(n)
            m_distance += abs((current_index % self.row) - (goal_index % self.row)) + abs((current_index // self.row) - (goal_index // self.row))
        return m_distance


def bfs(solver, initial_node, goal_state):
    """Breadth First Search.
    
    Frontier is a Queue - FILO."""
    if not solver.solvable(initial_node.state):
        return False
    frontier = deque()
    frontier.append(initial_node)
    explored = set()
    explored.add(str(initial_node.state))
    while frontier:
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
        current_node = frontier.popleft()
        if current_node.state == goal_state:
            solver.memory_usage = memory()
            solver.fringe_size = len(frontier)
            solver.path_to_goal = solver.retrace_path(initial_node, current_node) 
            solver.search_depth = len(solver.path_to_goal)
            return current_node
        solver.nodes_expanded += 1
        for node in solver.generate_neighbours(current_node):
            if str(node.state) not in explored:
                frontier.append(node)
                explored.add(str(node.state))
                solver.max_search_depth = max(solver.max_search_depth, node.depth)
    return False

def dfs(solver, initial_node, goal_state):
    """Depth first search.
    
    Frontier is a Stack - LIFO.
    Checks if node is discovered before pushing."""
    if not solver.solvable(initial_node.state):
        return False
    frontier = []
    frontier.append(initial_node)
    explored = set()
    explored.add(str(initial_node.state))
    while frontier:
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
        current_node = frontier.pop()
        if current_node.state == goal_state:
            solver.memory_usage = memory()
            solver.fringe_size = len(frontier)
            solver.path_to_goal = solver.retrace_path(initial_node, current_node)
            solver.search_depth = len(solver.path_to_goal)            
            return current_node
        solver.nodes_expanded += 1
        for node in solver.generate_neighbours_RLDU(current_node):
            if str(node.state) not in explored:
                frontier.append(node)
                explored.add(str(node.state))
                solver.max_search_depth = max(solver.max_search_depth, node.depth)
    return False

def dfs_popped(solver, initial_node, goal_state):
    """Depth first search.
    
    Frontier is a Stack - LIFO.
    Checks if node is discovered when popped."""
    if not solver.solvable(initial_node.state):
        return False
    frontier = []
    frontier.append(initial_node)
    explored = set()
    while frontier:
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
        current_node = frontier.pop()
        if str(current_node.state) not in explored:
            explored.add(str(current_node.state))
            if current_node.state == goal_state:
                solver.memory_usage = memory()
                solver.fringe_size = len(frontier)
                solver.path_to_goal = solver.retrace_path(initial_node, current_node)
                solver.search_depth = len(solver.path_to_goal)            
                return current_node
            solver.nodes_expanded += 1
            for node in solver.generate_neighbours_RLDU(current_node):
                frontier.append(node)
                solver.max_search_depth = max(solver.max_search_depth, node.depth)
    return False

def iddfs(solver, initial_node, goal_state):
    """Iterative deepening depth first search.
    
    Repeats DFS for each depth and branch.
    Frontier is a Stack - LIFO."""
    if not solver.solvable(initial_node.state):
        return False
    for depth in itertools.count(1):
        frontier = [initial_node]  
        solver.max_search_depth = 0
        while frontier:
            solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
            current_node = frontier.pop()
            if current_node.depth > depth:
                continue
            if current_node.state == goal_state:
                solver.memory_usage = memory()
                solver.fringe_size = len(frontier)
                solver.path_to_goal = solver.retrace_path(initial_node, current_node)
                solver.search_depth = len(solver.path_to_goal)
                return current_node
            solver.nodes_expanded += 1
            for node in solver.generate_neighbours_RLDU(current_node):
                frontier.append(node)
                solver.max_search_depth = max(solver.max_search_depth, node.depth)
    return False

def iddfs_recursive(solver, initial_state, goal_state):
    """Recursive Iterative deepening depth first search.
    
    Repeats DFS for each depth and branch.
    Frontier is a Stack - LIFO."""
    def dfs(frontier, depth):
        if depth == 0:
            return
        current_node = frontier[-1]
        if current_node.state == goal_state:
            solver.memory_usage = memory()
            solver.fringe_size = len(frontier)
            solver.path_to_goal = solver.retrace_path(initial_node, current_node)
            solver.search_depth = len(solver.path_to_goal)
            return frontier
        solver.nodes_expanded += 1
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
        for node in solver.generate_neighbours_RLDU(current_node):
            solver.max_search_depth = max(solver.max_search_depth, node.depth)
            next_route = dfs(frontier + [node], depth - 1)            
            if next_route:
                return next_route

    for depth in itertools.count(1):
        solver.max_search_depth = 0
        route = dfs([initial_state], depth)
        if route:
            return route       

def ast_none(solver, initial_node, goal_state):
    """A* search.
       
    Frontier is a priority queue.
    Updates no explored nodes."""
    if not solver.solvable(initial_node.state):
        return False
    frontier = []
    counter = 0
    heapq.heappush(frontier, [solver.manhattan_distance(initial_node, goal_state), 0, counter, initial_node])
    explored = set()
    explored.add(str(initial_node.state))
    while frontier:
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
        current_node = heapq.heappop(frontier)[3]
        if current_node.state == goal_state:
            solver.memory_usage = memory()
            solver.fringe_size = len(frontier)
            solver.path_to_goal = solver.retrace_path(initial_node, current_node)
            solver.search_depth = len(solver.path_to_goal)
            return current_node
        solver.nodes_expanded += 1
        for node in solver.generate_neighbours(current_node):
            if str(node.state) not in explored:
                counter += 1
                heapq.heappush(frontier, [solver.manhattan_distance(node, goal_state) + node.depth, node.path, counter, node])
                explored.add(str(node.state))
                solver.max_search_depth = max(solver.max_search_depth, node.depth)
    return False

def ast_smaller(solver, initial_node, goal_state):
    """A* search.
       
    Frontier is a priority queue.
    Updates nodes if cost is smaller."""
    if not solver.solvable(initial_node.state):
        return False
    frontier = []
    counter = 0
    heapq.heappush(frontier, [solver.manhattan_distance(initial_node, goal_state), 0, counter, initial_node])
    while frontier:
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
        current_node = heapq.heappop(frontier)[3]
        if current_node.state == goal_state:
            solver.memory_usage = memory()
            solver.fringe_size = len(frontier)
            solver.path_to_goal = solver.retrace_path(initial_node, current_node)
            solver.search_depth = len(solver.path_to_goal)
            return current_node
        solver.nodes_expanded += 1
        for node in solver.generate_neighbours(current_node):
            if node not in frontier:
                counter += 1
                heapq.heappush(frontier, [solver.manhattan_distance(node, goal_state) + node.depth, node.path, counter, node])
                solver.max_search_depth = max(solver.max_search_depth, node.depth)
            else:
                index = frontier.index(node)
                new_cost = solver.manhattan_distance(node, goal_state) + node.depth
                if new_cost < frontier[index][0]:
                    counter += 1
                    frontier[index] = [new_cost, node.path, counter, node]
                    heapq.heapify(frontier)
                    solver.max_search_depth = max(solver.max_search_depth, node.depth)
    return False

def ast_smaller3(solver, initial_node, goal_state):
    """A* search.
       
    Frontier is a priority queue.
    Updates nodes if cost is smaller."""
    if not solver.solvable(initial_node.state):
        return False
    frontier = []
    frontier_copy = set()
    counter = 0
    explored = set()
    heapq.heappush(frontier, [solver.manhattan_distance(initial_node, goal_state), 0, counter, initial_node])
    frontier_copy.add(str(initial_node.state))
    while frontier_copy:
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier_copy))
        current_node = heapq.heappop(frontier)[3]
        frontier_copy.remove(str(current_node.state))
        explored.add(str(current_node.state))
        if current_node.state == goal_state:
            solver.memory_usage = memory()
            solver.fringe_size = len(frontier_copy)
            solver.path_to_goal = solver.retrace_path(initial_node, current_node)
            solver.search_depth = len(solver.path_to_goal)
            return current_node
        solver.nodes_expanded += 1
        for node in solver.generate_neighbours(current_node):
            if str(node.state) in explored:
                continue
            if str(node.state) not in frontier_copy:
                counter += 1
                heapq.heappush(frontier, [solver.manhattan_distance(node, goal_state) + node.depth, node.path, counter, node])
                frontier_copy.add(str(node.state))   
                solver.max_search_depth = max(solver.max_search_depth, node.depth)
            else:
                index = frontier.index(node)
                new_cost = solver.manhattan_distance(node, goal_state) + node.depth
                if new_cost < frontier[index][0]:
                    counter += 1
                    frontier[index] = [new_cost, node.path, counter, node]
                    heapq.heapify(frontier)
                    solver.max_search_depth = max(solver.max_search_depth, node.depth)
    return False

def ast_all(solver, initial_node, goal_state):
    """A* search.
       
    Frontier is a priority queue.
    Updates all child nodes."""
    if not solver.solvable(initial_node.state):
        return False
    frontier = []
    counter = 0 
    heapq.heappush(frontier, [solver.manhattan_distance(initial_node, goal_state), 0, counter, initial_node])
    while frontier:        
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
        current_node = heapq.heappop(frontier)[3]
        if current_node.state == goal_state:
            solver.memory_usage = memory()
            solver.fringe_size = len(frontier)
            solver.path_to_goal = solver.retrace_path(initial_node, current_node)
            solver.search_depth = len(solver.path_to_goal)
            return current_node
        solver.nodes_expanded += 1
        for node in solver.generate_neighbours(current_node):
            counter += 1
            heapq.heappush(frontier, [solver.manhattan_distance(node, goal_state) + node.depth, node.path, counter, node])
            solver.max_search_depth = max(solver.max_search_depth, node.depth)
    return False  

def idast(solver, initial_node, goal_state):
    """Iterative deepening A* search.
    
    Repeats A* for each depth and .
    Frontier is a Stack - LIFO."""
    if not solver.solvable(initial_node.state):
        return False
    depth = 0    
    next_min_cost = -1
    while depth < sys.maxsize:
        frontier = []
        counter = 0          
        initial_depth = solver.manhattan_distance(initial_node, goal_state)    
        if next_min_cost == -1:
            depth = initial_depth            
        else:
            depth = max(initial_depth, next_min_cost)
        next_min_cost = 0  
        heapq.heappush(frontier, [initial_depth, initial_node.path, counter, initial_node])
        while frontier:        
            solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
            current_node = heapq.heappop(frontier)[3]
            if current_node.state == goal_state:
                solver.memory_usage = memory()
                solver.fringe_size = len(frontier)
                solver.path_to_goal = solver.retrace_path(initial_node, current_node)
                solver.search_depth = len(solver.path_to_goal)
                return current_node
            solver.nodes_expanded += 1
            for node in solver.generate_neighbours(current_node):
                node_cost = solver.manhattan_distance(node, goal_state) + node.depth
                if node_cost > depth:
                    if next_min_cost == 0:
                        next_min_cost = node_cost
                    else:
                        next_min_cost = min(node_cost, next_min_cost)
                else:
                    counter += 1
                    heapq.heappush(frontier, [node_cost, node.path, counter, node])
                    solver.max_search_depth = max(solver.max_search_depth, node.depth)
    return False

def gbfs(solver, initial_node, goal_state):
    """Greedy best first search.

    Frontier is a priority queue."""
    if not solver.solvable(initial_node.state):
        return False
    frontier = []
    counter = 0
    heapq.heappush(frontier, [solver.manhattan_distance(initial_node, goal_state), counter, initial_node])
    explored = set()
    explored.add(str(initial_node.state))
    while frontier:
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
        current_node = heapq.heappop(frontier)[2]
        if current_node.state == goal_state:
            solver.memory_usage = memory()
            solver.fringe_size = len(frontier)
            solver.path_to_goal = solver.retrace_path(initial_node, current_node)
            solver.search_depth = len(solver.path_to_goal) 
            return current_node
        solver.nodes_expanded += 1
        for node in solver.generate_neighbours(current_node):
            if str(node.state) not in explored:
                counter += 1
                heapq.heappush(frontier, [solver.manhattan_distance(node, goal_state), counter, node])
                explored.add(str(node.state))
                solver.max_search_depth = max(solver.max_search_depth, node.depth)
    return False

def print_results(solver, algorithm, start = 0, stop = 0):
    """Prints details from solver."""
    print(algorithm)
    #print("path_to_goal: " + str(solver.path_to_goal))
    print("cost_of_path: " + str(len(solver.path_to_goal)))
    print("nodes_expanded: " + str(solver.nodes_expanded))
    print("fringe_size: " + str(solver.fringe_size))
    print("max_fringe_size: " + str(solver.max_fringe_size))
    print("search_depth: " + str(solver.search_depth))
    print("max_search_depth: " + str(solver.max_search_depth))
    print("max_ram_usage " + str(solver.memory_usage))
    print("running_time: " + str(stop - start) + "\n")

def execute_algorithms(solver, initial_node, goal_state, algorithms):
    """Executes each of alogirthms and prints results."""
    for algo in algorithms:
        start = timeit.default_timer()
        solver.nodes_expanded = 0
        solver.max_fringe_size = 0
        solver.max_search_depth = 0
        algo(solver, initial_node, goal_state)
        stop = timeit.default_timer()
        print_results(solver, str(algo), start, stop)

#goal_state = list(range(0, 9))
goal_state = list(range(1, 16)) + [0]
#initial_node = Node([2,0,1,6,7,8,5,3,4], 0, [], 0)
#initial_node = Node([4,1,3,7,6,0,5,2,8], 0, [], 0)
#initial_node = Node([7,2,4,5,0,6,8,3,1], 0, [], 0)
#initial_node = Node([6,0,4,8,2,3,5,1,7], 0, [], 0)
#initial_node = Node([4,6,5,1,3,2,8,0,7], 0, [], 0)
#initial_node = Node([7,1,2,0,3,6,5,8,4], 0, [], 0) # different results for AST
#initial_node = Node([3,1,2,0,4,5,6,7,8], 0, [], 0)
#initial_node = Node([1,2,5,3,4,0,6,7,8], 0, [], 0)
#initial_node = Node([8,5,2,7,1,4,6,0,3], 0, [], 0)
#initial_node = Node([3,1,2,4,7,0,6,8,5], 0, [], 0)
#initial_node = Node([6,1,8,4,0,2,7,3,5], 0, [], 0)
#initial_node = Node([0,6,2,1,3,5,7,4,8], 0, [], 0)
#initial_node = Node([1,2,8,3,6,0,7,4,5,9,13,15,10,11,12,14], 0, [], 0) # solved in 0.2s
#initial_node = Node([8,6,2,14,4,0,15,1,13,12,9,7,3,5,10,11], 0, [], 0) # solved in 2846s
#initial_node = Node([5,1,4,15,13,14,3,0,6,9,8,10,11,12,2,7], 0, [], 0) # solved in 1.2s 0.9s
initial_node = Node([1,8,12,14,5,4,15,0,9,11,10,7,13,2,6,3], 0, [], 0) # solved in 27s 5s
#initial_node = Node([1,2,4,8,9,0,7,10,12,15,13,3,11,6,5,14], 0, [], 0) # solved in 271s 15s
#initial_node = Node([5,11,2,7,1,12,4,3,13,15,14,9,10,6,8,0], 0, [], 0) # solved in 5677s 56s
#initial_node = Node([8,4,1,2,9,5,6,3,12,10,14,7,0,13,15,11], 0, [], 0)
#initial_node = Node([4,1,2,3,5,6,10,7,8,9,0,11,12,13,14,15], 0, [], 0)

solver = Solver(initial_node)
execute_algorithms(solver, initial_node, goal_state, [ast_smaller3])
