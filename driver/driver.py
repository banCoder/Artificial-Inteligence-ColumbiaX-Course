from __future__ import print_function
import getopt, sys
from math import sqrt
import heapq
import timeit
import os
import thread
import itertools

def memory():
    if os.name == 'posix':
        import resource
        return float(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024)
    else:
        import psutil
        p = psutil.Process()
        return float(p.memory_info().rss / 1048576)

class PriorityQueue(object):
    def __init__(self):
        self.elements = []
        self.counter = itertools.count()
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
    """ represents a state/ node """
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

class Queue:
    def __init__(self):
        self.items = []
    def isEmpty(self):
        return self.items == []
    def enqueue(self, item):
        self.items.insert(0,item)
    def dequeue(self):
        return self.items.pop()
    def size(self):
        return len(self.items)

class Stack:
     def __init__(self):
         self.items = []
     def isEmpty(self):
         return self.items == []
     def push(self, item):
         self.items.append(item)
     def pop(self):
         return self.items.pop()
     def peek(self):
         return self.items[len(self.items)-1]
     def size(self):
         return len(self.items)

class Solver(object):
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
        """ generates a new state """
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
        """ generates given state's neighbours """
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
        """ generates given state's neighbours """
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
        directions = ["Up", "Down", "Left", "Right"]
        path_to_goal = []
        while not str(current_state.configuration) == str(initial_state.configuration):
            path_to_goal.insert(0, directions[current_state.path - 1])
            current_state = current_state.parent
        return path_to_goal
    def manhattan_distance(self, current_state, goal_state):
        m_distance = 0
        for n in range(self.n + 1):
            where_it_is = current_state.configuration.index(n)
            should_be = goal_state.index(n)
            horizontal = (where_it_is % self.pow) - (should_be % self.pow)
            vertical = ((where_it_is - horizontal) / self.pow) - (should_be / self.pow)
            m_distance += abs(horizontal) + abs(vertical)
        return m_distance

def bfs(solver, initial_state, goal_test):
    if not solver.solvable(initial_state.configuration):
        return False
    frontier = Queue()
    frontier.enqueue(initial_state)
    explored = set()
    explored.add(str(initial_state.configuration))
    while not frontier.isEmpty():
        solver.max_fringe_size = max(solver.max_fringe_size, frontier.size())
        current_state = frontier.dequeue()
        if current_state.configuration == goal_test:
            solver.fringe_size = frontier.size()
            solver.path_to_goal = solver.generate_path(initial_state, current_state)
            solver.search_depth = len(solver.path_to_goal)
            return current_state
        solver.nodes_expanded += 1
        for n in solver.generate_neighbours(current_state):
            if str(n.configuration) not in explored:
                frontier.enqueue(n)
                explored.add(str(n.configuration))
                solver.max_search_depth = max(solver.max_search_depth, n.depth)
    return False

def dfs(solver, initial_state, goal_test):
    if not solver.solvable(initial_state.configuration):
        return False
    frontier = Stack()
    frontier.push(initial_state)
    explored = set()
    explored.add(str(initial_state.configuration))
    while not frontier.isEmpty():
        solver.max_fringe_size = max(solver.max_fringe_size, frontier.size())
        current_state = frontier.pop()
        if current_state.configuration == goal_test:
            solver.fringe_size = frontier.size()
            solver.path_to_goal = solver.generate_path(initial_state, current_state)
            solver.search_depth = len(solver.path_to_goal)
            return current_state
        solver.nodes_expanded += 1
        for n in solver.generate_neighbours_RLDU(current_state):
            if str(n.configuration) not in explored:
                frontier.push(n)
                explored.add(str(n.configuration))
                solver.max_search_depth = max(solver.max_search_depth, n.depth)
    return False

def ast(solver, initial_state, goal_test):
    if not solver.solvable(initial_state.configuration):
        return False
    frontier = PriorityQueue()
    frontier.put(initial_state, float("%s.0" % solver.manhattan_distance(initial_state, goal_state)))
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


goal_state = [0, 1, 2, 3, 4, 5, 6, 7, 8]
file = open("output.txt", "w")
initial_state = State(map(int, sys.argv[2].split(',')), "", None, 0)
sol_solver = Solver(initial_state)
start = timeit.default_timer()
search = ""
if sys.argv[1] == "bfs":
    search = bfs(sol_solver, initial_state, goal_state)
elif sys.argv[1] == "dfs":
    search = dfs(sol_solver, initial_state, goal_state)
elif sys.argv[1] == "ast":
    search = ast(sol_solver, initial_state, goal_state)
stop = timeit.default_timer()
if not search:
    file.write("not solvable")
else:
    file.write("path_to_goal: " + str(sol_solver.path_to_goal) + "\n")
    file.write("cost_of_path: " + str(len(sol_solver.path_to_goal)) + "\n")
    file.write("nodes_expanded: " + str(sol_solver.nodes_expanded) + "\n")
    file.write("fringe_size: " + str(sol_solver.fringe_size) + "\n")
    file.write("max_fringe_size: " + str(sol_solver.max_fringe_size) + "\n")
    file.write("search_depth: " + str(sol_solver.search_depth) + "\n")
    file.write("max_search_depth: " + str(sol_solver.max_search_depth) + "\n")
    file.write("running_time: " + str(stop - start) + "\n")
    file.write("max_ram_usage " + str(memory()) + "\n")

