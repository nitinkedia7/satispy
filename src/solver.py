from enum import Enum

class ClauseState(Enum):
    C_UNRESOLVED = 0
    C_SATISFIED = 1
    C_CONFLICTING = 2
    C_UNIT = 1

class LiteralState(Enum):
    L_UNASSIGNED = 0
    L_TRUE = 1
    L_FALSE = 2

class SolverState(Enum):
    S_UNRESOLVED = 0
    S_SATISFIED = 1
    S_UNSATISFIED = 2
    S_CONFLICT = 3

def get_literal(v: int) -> int:
    if (v == 0):
        raise Exception("Variable cannot be zero.")
    return 2 * v if v > 0 else 2 * (abs(v)) - 1

def get_variable(l : int) -> int:
    if (l <= 0):
        raise Exception("Literal must be a positive integer, is {}".format(l))
    return int((l + 1) / 2) if l % 2  else int(l / 2)

def get_opposite_literal(l : int) -> int:
    if (l <= 0):
        raise Exception("Literal must be a positive integer, is {}".format(l))
    return (l + 1) if l % 2 else (l - 1)

def is_negative(l : int) -> bool:
    if (l <= 0):
        raise Exception("Literal must be a positive integer, is {}".format(l))
    return True if l % 2 else False

class Clause:
    id : int
    literals: list
    first_watcher : int
    second_watcher : int
    is_unary: bool

    def __init__(self, literals: list, clause_id: int):
        self.id = clause_id
        self.literals = literals
        self.is_unary = (len(literals) == 1)
        self.first_watcher = 0
        self.second_watcher = len(literals) - 1

    def print(self):
        print("Clause {} with literals {}".format(self.id, self.literals))
    
    def get_first_watcher(self):
        return self.literals[self.first_watcher]
    def get_second_watcher(self):
        return self.literals[self.second_watcher]

class Solver:
    var_count: int
    clause_count: int
    clauses: list

    curr_level : int
    curr_assignment: list
    assignment_level: list
    assigned_till_now: list

    # BCP data structures
    bcp_stack: list
    watch_map : dict
    
    # MINISAT scores
    increment_value : float  
    activity : list

    def __init__(self, var_count, clause_count):
        self.var_count = var_count
        self.clause_count = clause_count
        
        self.clauses = []
        self.curr_level = 0
        self.curr_assignment = [LiteralState.L_UNASSIGNED] * (var_count + 1)
        self.assignment_level = [-1] * (var_count + 1)
        
        self.bcp_stack = []
        self.watch_map = {}
        
        self.increment_value = 1.0
        self.activity = [0.0] * (var_count + 1)

    def print(self):
        print("{} variables, {} clauses".format(self.var_count, self.clause_count))
        for clause in self.clauses:
            clause.print()

    def watch_this_clause(self, lit, clause_id):
        if lit in self.watch_map: 
            self.watch_map[lit].append(clause_id)
        else:
            self.watch_map[lit] = [clause_id]

    def insert_clause(self, clause : Clause):
        self.clauses.append(clause)
        clause_id = len(self.clauses) - 1
        # Bump their scores
        for literal in clause.literals:
            var = get_variable(literal)
            self.activity[var] += self.increment_value
        # Add this clause to two watch lists
        self.watch_this_clause(clause.get_first_watcher(), clause_id)
        self.watch_this_clause(clause.get_second_watcher(), clause_id)
    
    def assert_unary_literal(self, lit):
        var = get_variable(lit)
        if is_negative(lit):
            self.curr_assignment[var] = LiteralState.L_FALSE
        else:
            self.curr_assignment[var] = LiteralState.L_TRUE
        self.assignment_level[var] = 0
        print("Assiged unary literal {} as {}, variable {} as {}".format(
            lit, LiteralState.L_TRUE, var, self.curr_assignment[var]))

    def assert_nonunary_literal(self, lit):
        self.assigned_till_now.append(lit)
        var = get_variable(lit)
        if is_negative(lit):
            self.curr_assignment[var] = LiteralState.L_FALSE
        else:
            self.curr_assignment[var] = LiteralState.L_TRUE
        self.assignment_level[var] = self.curr_level
        print("Assiged literal {} as {}, variable {} as {}".format(
            lit, LiteralState.L_TRUE, var, self.curr_assignment[var]))

def read_cnf():
    input_file = open("unsat.cnf", 'r')
    current_line = input_file.readline()
    tokens = current_line.split()
    var_count = int(tokens[-2])
    clause_count = int(tokens[-1])

    solver = Solver(var_count, clause_count)
    for clause_id in range(clause_count):
        current_line = input_file.readline()
        tokens = current_line.split()
        assert(tokens.pop() == "0")
        
        literals = [get_literal(int(literal)) for literal in tokens]
        curr_clause = Clause(literals, clause_id)
        if (curr_clause.is_unary):
            lit = curr_clause.literals[0]
            solver.assert_unary_literal(lit)
            solver.bcp_stack.append(get_opposite_literal(lit))
        else:
            solver.insert_clause(curr_clause)
    solver.print()

read_cnf()