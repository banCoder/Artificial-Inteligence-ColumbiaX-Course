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

class PriorityQueue(object):
    """Queue with priority based on path and add order."""
    def __init__(self):
        self.elements = []
        self.counter = itertools.count()
        self.entries = 0
    def isEmpty(self):
        return len(self.elements) == 0
    def put(self, item, priority):
        heapq.heappush(self.elements, (float(str("%s%s" % (priority, next(self.counter)))), item))
    def deleteMin(self):
        return heapq.heappop(self.elements)[1]
    def get_item(self, item):
        for e in range(0, len(self.elements)):
            if self.elements[e][1].configuration == item.configuration:
                to_return = self.elements[e]
                self.elements.remove(self.elements[e])
                return to_return[1]
    def decreaseKey(self, item, solver):
        old = self.get_item(item)
        self.put(old, item.depth + solver.manhattan_distance(item, goal_state))

class State(object):
    """Represents a state/ node."""
    def __init__(self, configuration, path, parent, depth):
        self.configuration = configuration
        self.path = path
        self.parent = parent
        self.depth = depth
    def __eq__(self, other):
        if isinstance(other, tuple) or isinstance(other, list):
            return self.configuration == other[1].configuration
        else:
            return other and self.configuration == other.configuration
    def __lt__(self, other):
        return float(str("%s.%s" % (self.depth, self.path))) < float(str("%s.%s" % (other.depth, other.path)))

class Solver(object):
    """Handles all solving methods."""
    def __init__(self, initial_state):
        self.n = len(initial_state.configuration) - 1
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
    def solvable(self, configuration):
        """Teests if puzzle is solvable"""
        inversions = 0
        cfg = list(configuration)
        cfg.remove(0)
        ayy = reversed(range(len(cfg)))
        for i in reversed(range(len(cfg))):
            for j in range(len(cfg)):
                if j < i and cfg[j] > cfg[i]:
                    inversions += 1
        return inversions % 2 == 0
    def generate_state(self, current_state, direction):
        """Generates a new state.
        
        Attributes:
            current_state -- state to generate new state from
            direction -- direction from current state to get to new state
        """
        current = current_state.configuration.index(0)
        if direction == 1:
            next = int(current - sqrt(self.n + 1))
        elif direction == 2:
            next = int(current + sqrt(self.n + 1))
        elif direction == 3:
            next = int(current - 1)
        else:
            next = current + 1
        next_configuration = list(current_state.configuration)
        next_configuration[current] = current_state.configuration[next]
        next_configuration[next] = current_state.configuration[current]
        next_direction = direction
        return State(next_configuration, next_direction, current_state, current_state.depth + 1)
    def generate_neighbours(self, current_state):
        """Generates list of given state's neighbours."""
        current_index = current_state.configuration.index(0)
        neighbours = []
        if current_index not in self.top and (current_state.path == "" or not current_state.path == 2):
            neighbours.append(self.generate_state(current_state, 1))
        if current_index not in self.bottom and (current_state.path == "" or not current_state.path == 1):
            neighbours.append(self.generate_state(current_state, 2))
        if current_index not in self.left and (current_state.path == "" or not current_state.path == 4):
            neighbours.append(self.generate_state(current_state, 3))
        if current_index not in self.right and (current_state.path == "" or not current_state.path == 3):
            neighbours.append(self.generate_state(current_state, 4))
        return neighbours
    def generate_neighbours_RLDU(self, current_state):
        """Generates given state's neighbours in reverse order."""
        current_index = current_state.configuration.index(0)
        neighbours = []
        if current_index not in self.right and (current_state.path == "" or not current_state.path == 3):
            neighbours.append(self.generate_state(current_state, 4))
        if current_index not in self.left and (current_state.path == "" or not current_state.path == 4):
            neighbours.append(self.generate_state(current_state, 3))
        if current_index not in self.bottom and (current_state.path == "" or not current_state.path == 1):
            neighbours.append(self.generate_state(current_state, 2))
        if current_index not in self.top and (current_state.path == "" or not current_state.path == 2):
            neighbours.append(self.generate_state(current_state, 1))
        return neighbours
    def generate_path(self, initial_state, current_state):
        """Genetrates path from initial to current state."""
        directions = ["Up", "Down", "Left", "Right"]
        path_to_goal = []
        while not str(current_state.configuration) == str(initial_state.configuration):
            path_to_goal.insert(0, directions[current_state.path - 1])
            current_state = current_state.parent
        return path_to_goal
    def manhattan_distance(self, current_state, goal_state):
        """Returns Manhattan distance from current state to goal."""
        m_distance = 0
        for n in range(self.n + 1):
            where_it_is = current_state.configuration.index(n)
            should_be = goal_state.index(n)
            horizontal = (where_it_is % self.pow) - (should_be % self.pow)
            vertical = ((where_it_is - horizontal) / self.pow) - (should_be / self.pow)
            m_distance += abs(horizontal) + abs(vertical)
        return int(m_distance)

def bfs(solver, initial_state, goal_test):
    """Breadth First Search.
    
    Frontier is a Queue - FILO"""
    if not solver.solvable(initial_state.configuration):
        return False
    frontier = deque()
    frontier.append(initial_state)
    explored = set()
    explored.add(str(initial_state.configuration))
    while len(frontier) > 0:
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
        current_state = frontier.popleft()
        if current_state.configuration == goal_test:
            solver.fringe_size = len(frontier)
            solver.path_to_goal = solver.generate_path(initial_state, current_state)
            solver.search_depth = len(solver.path_to_goal)
            return current_state
        solver.nodes_expanded += 1
        for n in solver.generate_neighbours(current_state):
            if str(n.configuration) not in explored:
                frontier.append(n)
                explored.add(str(n.configuration))
                solver.max_search_depth = max(solver.max_search_depth, n.depth)
    return False

def dfs(solver, initial_state, goal_test):
    """Depth first search.
    
    Frontier is a Stack - LIFO"""
    if not solver.solvable(initial_state.configuration):
        return False
    frontier = []
    frontier.append(initial_state)
    explored = set()
    explored.add(str(initial_state.configuration))
    while not frontier == []:
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier))
        current_state = frontier.pop()
        if current_state.configuration == goal_test:
            solver.fringe_size = len(frontier)
            solver.path_to_goal = solver.generate_path(initial_state, current_state)
            solver.search_depth = len(solver.path_to_goal)
            return current_state
        solver.nodes_expanded += 1
        for n in solver.generate_neighbours_RLDU(current_state):
            if str(n.configuration) not in explored:
                frontier.append(n)
                explored.add(str(n.configuration))
                solver.max_search_depth = max(solver.max_search_depth, n.depth)
    return False

def ast(solver, initial_state, goal_test):
    """A* search.
    
    Frontier is a priority queue"""
    if not solver.solvable(initial_state.configuration):
        return False
    frontier = PriorityQueue()
    frontier.put(initial_state, solver.manhattan_distance(initial_state, goal_state))
    explored = set()
    explored.add(str(initial_state.configuration))
    while not frontier.isEmpty():
        solver.max_fringe_size = max(solver.max_fringe_size, len(frontier.elements))
        current_state = frontier.deleteMin()
        if current_state.configuration == goal_test:
            solver.fringe_size = len(frontier.elements)
            solver.path_to_goal = solver.generate_path(initial_state, current_state)
            solver.search_depth = len(solver.path_to_goal)
            return current_state
        solver.nodes_expanded += 1
        for n in solver.generate_neighbours(current_state):
            if str(n.configuration) not in explored:
                frontier.put(n, float(str("%s.%s" % (n.depth + solver.manhattan_distance(n, goal_state), n.path))))
                explored.add(str(n.configuration))
                solver.max_search_depth = max(solver.max_search_depth, n.depth)
            elif n in frontier.elements:
                frontier.decreaseKey(n, solver)
    return False

def print_end(sol_solver, method):
    """Prints details from solve."""
    print(method)
    #print("path_to_goal: " + str(sol_solver.path_to_goal))
    print("cost_of_path: " + str(len(sol_solver.path_to_goal)))
    print("nodes_expanded: " + str(sol_solver.nodes_expanded))
    print("fringe_size: " + str(sol_solver.fringe_size))
    print("max_fringe_size: " + str(sol_solver.max_fringe_size))
    print("search_depth: " + str(sol_solver.search_depth))
    print("max_search_depth: " + str(sol_solver.max_search_depth))
    print("max_ram_usage " + str(memory()) + "\n")

#goal_state = list(range(0, 9))
goal_state = list(range(1, 16)) + [0]
#file = open("output.txt", "w")
#initial_state = State([1,2,5,3,4,0,6,7,8], [], [], 0)
#initial_state = State([4, 1, 3, 7, 6, 0, 5, 2, 8], [], [], 0)
initial_state = State([1,2,8,3,6,0,7,4,5,9,13,15,10,11,12,14], [], [], 0)
#initial_state = State([8,6,2,14,4,0,15,1,13,12,9,7,3,5,10,11], [], [], 0)
sol_solver = Solver(initial_state)
start = timeit.default_timer()
#bfs(sol_solver, initial_state, goal_state)
#print_end(sol_solver, "BFS:")
#dfs(sol_solver, initial_state, goal_state)
#print_end(sol_solver, "DFS:")
ast(sol_solver, initial_state, goal_state)
print_end(sol_solver, "AST:")
stop = timeit.default_timer()
print("running_time: " + str(stop - start))
#if not search:
#    file.write("not solvable")
#else:
#    file.write("path_to_goal: " + str(sol_solver.path_to_goal) + "\n")
#    file.write("cost_of_path: " + str(len(sol_solver.path_to_goal)) + "\n")
#    file.write("nodes_expanded: " + str(sol_solver.nodes_expanded) + "\n")
#    file.write("fringe_size: " + str(sol_solver.fringe_size) + "\n")
#    file.write("max_fringe_size: " + str(sol_solver.max_fringe_size) + "\n")
#    file.write("search_depth: " + str(sol_solver.search_depth) + "\n")
#    file.write("max_search_depth: " + str(sol_solver.max_search_depth) + "\n")
#    file.write("running_time: " + str(stop - start) + "\n")
#    file.write("max_ram_usage " + str(memory()) + "\n")

