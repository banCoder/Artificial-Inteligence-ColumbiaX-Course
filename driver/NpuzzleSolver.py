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

class Solver(object):
    """Handles all solving methods."""
    def __init__(self, initial_node):
        self.n = len(initial_node.state) - 1
        self.pow = int(sqrt(self.n + 1))
        self.top = range(0, self.pow)
        self.bottom = range(self.pow * (self.pow - 1), self.pow ** 2)
        self.left = [i * self.pow for i in range(0, self.pow)]
        self.right = [i * self.pow + self.pow - 1 for i in range(0, self.pow)]
        self.fringe_size = 0
        self.max_fringe_size = 0
        self.nodes_expanded = 0
        self.search_depth = 0
        self.max_search_depth = 0
        self.path_to_goal = []
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
    def generate_state(self, current_node, direction):
        """Generates a new state.
        
        Attributes:
            current_node -- state to generate new state from
            direction -- direction from current state to get to new state
        """
        current = current_node.state.index(0)
        if direction == 1:
            next = int(current - sqrt(self.n + 1))
        elif direction == 2:
            next = int(current + sqrt(self.n + 1))
        elif direction == 3:
            next = int(current - 1)
        else:
            next = current + 1
        next_state = list(current_node.state)
        next_state[current] = current_node.state[next]
        next_state[next] = current_node.state[current]
        next_direction = direction
        return Node(next_state, next_direction, current_node, current_node.depth + 1)
    def generate_neighbours(self, current_node):
        """Generates list of given state's neighbours."""
        current_index = current_node.state.index(0)
        neighbours = []
        if current_index not in self.top and not current_node.path == 2:
            neighbours.append(self.generate_state(current_node, 1))
        if current_index not in self.bottom and not current_node.path == 1:
            neighbours.append(self.generate_state(current_node, 2))
        if current_index not in self.left and not current_node.path == 4:
            neighbours.append(self.generate_state(current_node, 3))
        if current_index not in self.right and not current_node.path == 3:
            neighbours.append(self.generate_state(current_node, 4))
        return neighbours
    def generate_neighbours_RLDU(self, current_node):
        """Generates given state's neighbours in reverse order."""
        current_index = current_node.state.index(0)
        neighbours = []
        if current_index not in self.right and not current_node.path == 3:
            neighbours.append(self.generate_state(current_node, 4))
        if current_index not in self.left and not current_node.path == 4:
            neighbours.append(self.generate_state(current_node, 3))
        if current_index not in self.bottom and not current_node.path == 1:
            neighbours.append(self.generate_state(current_node, 2))
        if current_index not in self.top and not current_node.path == 2:
            neighbours.append(self.generate_state(current_node, 1))
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
        for n in range(self.n + 1):
            where_it_is = current_node.state.index(n)
            should_be = goal_state.index(n)
            horizontal = (where_it_is % self.pow) - (should_be % self.pow)
            vertical = ((where_it_is - horizontal) / self.pow) - (should_be / self.pow)
            m_distance += abs(horizontal) + abs(vertical)
        return int(m_distance)

def bfs(solver, initial_node, goal_test):
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
        if current_node.state == goal_test:
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

def dfs(solver, initial_node, goal_test):
    """Depth first search.
    
    Frontier is a Stack - LIFO."""
    if not solver.solvable(initial_node.state):
        return False
    frontier = []
    frontier.append(initial_node)
    explored = set()
    explored.add(str(initial_node.state))
    while frontier:
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
        current_node = frontier.pop()
        if current_node.state == goal_test:
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

def ast(solver, initial_node, goal_test):
    """A* search.
    
    Frontier is a priority queue."""
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
        if current_node.state == goal_test:
            solver.fringe_size = len(frontier)
            solver.path_to_goal = solver.retrace_path(initial_node, current_node)
            solver.search_depth = len(solver.path_to_goal)
            return current_node
        solver.nodes_expanded += 1
        for node in solver.generate_neighbours(current_node):
            if str(node.state) not in explored:
                counter += 1
                node_priority = [node.depth + solver.manhattan_distance(node, goal_state), node.path, counter, node]
                heapq.heappush(frontier, node_priority)
                explored.add(str(node.state))
                solver.max_search_depth = max(solver.max_search_depth, node.depth)
            #elif node_priority in frontier:
            #    index = frontier.index(node_priority)
            #    cost = node.depth + solver.manhattan_distance(node, goal_state)
            #    if cost < frontier[index][0]:
            #        frontier[index][0] = cost
            #        frontier[index][1] = node.path
            #        heapq.heapify(frontier)
    return False

def print_end(sol_solver, method):
    """Prints details from solver."""
    print(method)
    print("path_to_goal: " + str(sol_solver.path_to_goal))
    print("cost_of_path: " + str(len(sol_solver.path_to_goal)))
    print("nodes_expanded: " + str(sol_solver.nodes_expanded))
    print("fringe_size: " + str(sol_solver.fringe_size))
    print("max_fringe_size: " + str(sol_solver.max_fringe_size))
    print("search_depth: " + str(sol_solver.search_depth))
    print("max_search_depth: " + str(sol_solver.max_search_depth))
    print("max_ram_usage " + str(memory()) + "\n")

goal_state = list(range(0, 9))
#goal_state = list(range(1, 16)) + [0]
#initial_node = Node([1,2,5,3,4,0,6,7,8], 0, [], 0)
#initial_node = Node([4,1,3,7,6,0,5,2,8], 0, [], 0)
initial_node = Node([7,2,4,5,0,6,8,3,1], 0, [], 0)
#initial_node = Node([6,0,4,8,2,3,5,1,7], 0, [], 0)
#initial_node = Node([1,2,8,3,6,0,7,4,5,9,13,15,10,11,12,14], 0, [], 0) # solved in 0.2s
#initial_node = Node([8,6,2,14,4,0,15,1,13,12,9,7,3,5,10,11], 0, [], 0) # unsolved
#initial_node = Node([5,1,4,15,13,14,3,0,6,9,8,10,11,12,2,7], 0, [], 0) # solved in 1.2s 0.9s
#initial_node = Node([1,8,12,14,5,4,15,0,9,11,10,7,13,2,6,3], 0, [], 0) # solved in 27s 5s
#initial_node = Node([1,2,4,8,9,0,7,10,12,15,13,3,11,6,5,14], 0, [], 0) # solved in 271s 15s
#initial_node = Node([5,11,2,7,1,12,4,3,13,15,14,9,10,6,8,0], 0, [], 0) # solved in 5677s 59s

sol_solver = Solver(initial_node)
start = timeit.default_timer()
bfs(sol_solver, initial_node, goal_state)
print_end(sol_solver, "BFS:")
dfs(sol_solver, initial_node, goal_state)
print_end(sol_solver, "DFS:")
ast(sol_solver, initial_node, goal_state)
print_end(sol_solver, "AST:")
stop = timeit.default_timer()
print("running_time: " + str(stop - start))