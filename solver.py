import time
from enum import Enum

class CONSTANTS:
    VAR_DECAY_RATE = 0.95
    THRESHOLD_MULTIPLIER = 1.1
    RESTART_LOWER_BOUND = 100
    RESTART_UPPER_BOUND_BASE = 1000

class ClauseState(Enum):
    C_UNRESOLVED = 0
    C_SATISFIED = 1
    C_CONFLICTING = 2
    C_UNIT = 3

class LiteralState(Enum):
    L_UNASSIGNED = -1
    L_FALSE = 0
    L_TRUE = 1

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
    literals: list
    first_watcher : int
    second_watcher : int
    is_unary: bool

    def __init__(self, literals: list):
        self.literals = literals
        self.is_unary = (len(literals) == 1)

    def insert_literal(self, lit):
        if lit not in self.literals:
            self.literals.append(lit)
            self.is_unary = (len(self.literals) == 1)

    def print(self, clause_id: int):
        print("Clause {} with literals {}, watchers {} and {}".format(
            clause_id, self.literals, self.first_watcher, self.second_watcher)
        )
    
    def get_first_watcher(self):
        return self.literals[self.first_watcher]
    def get_second_watcher(self):
        return self.literals[self.second_watcher]

    def change_watch_location(self, solver, is_first_watcher, other_watcher) -> (ClauseState, int):
        # find an unset watch position other than other_watcher
        for index, lit in enumerate(self.literals):
            if (lit == other_watcher):
                continue
            lit_state = solver.get_literal_status(lit)
            if (lit_state != LiteralState.L_FALSE):
                if is_first_watcher:
                    self.first_watcher = index
                else:
                    self.second_watcher = index
                return ClauseState.C_UNRESOLVED, index
        other_watch_status = solver.get_literal_status(other_watcher)
        if (other_watch_status == LiteralState.L_FALSE):
            return ClauseState.C_CONFLICTING, None
        elif other_watch_status == LiteralState.L_UNASSIGNED:
            return ClauseState.C_UNIT, None
        else:
            assert(other_watch_status == LiteralState.L_TRUE)
            return ClauseState.C_SATISFIED, None

class Solver:
    var_count: int
    clause_count: int
    clauses: list
    unary_clauses: list

    curr_level : int
    max_level : int
    curr_assignment: list
    prev_assignment: list
    assignment_level: list
    assigned_till_now: list
    antecedent : list
    assignments_upto_level : list
    conflicts_upto_level : list

    # BCP data structures
    bcp_stack: list
    watch_map : dict
    
    # MINISAT scores
    increment_value : float  
    activity : list

    # Dynamic restart parameters
    restart_threshold : int
    restart_upper_bound : int

    # Statistics
    restart_count: int
    learnt_clauses_count : int
    decision_count: int
    assignments_count: int

    def __init__(self, var_count, clause_count):
        self.var_count = var_count
        self.clause_count = clause_count
        self.clauses = []
        self.unary_clauses = []

        self.curr_level = 0
        self.max_level = 0
        self.curr_assignment = [LiteralState.L_UNASSIGNED] * (var_count + 1)
        self.prev_assignment = [-1] * (var_count + 1)
        self.assignment_level = [-1] * (var_count + 1)
        self.assigned_till_now = []
        self.antecedent = [-1] * (var_count + 1)
        self.assignments_upto_level = [0]
        self.conflicts_upto_level = [0]

        self.bcp_stack = []
        self.watch_map = {}
        
        self.increment_value = 1.0
        self.activity = [0.0] * (var_count + 1)

        self.restart_threshold = CONSTANTS.RESTART_LOWER_BOUND
        self.restart_upper_bound = CONSTANTS.RESTART_UPPER_BOUND_BASE
        
        self.restart_count = 0
        self.learnt_clauses_count = 0
        self.decision_count = 0
        self.assignments_count = 0

    def reset_state(self):
        # print("Restart")
        self.restart_count += 1
        self.restart_threshold = int(self.restart_threshold * CONSTANTS.THRESHOLD_MULTIPLIER)
        if (self.restart_threshold > self.restart_upper_bound):
            self.restart_threshold = CONSTANTS.RESTART_LOWER_BOUND
            self.restart_upper_bound = int(self.restart_upper_bound * CONSTANTS.THRESHOLD_MULTIPLIER)
        for var in range(1, self.var_count + 1):
            if (self.assignment_level[var] > 0):
                self.curr_assignment[var] = LiteralState.L_UNASSIGNED
        # self.curr_assignment = [0 if self.assignment_level[var] > 0 else self.curr_assignment[var] for var in range(1, self.var_count)]
        self.bcp_stack.clear()
        self.assigned_till_now.clear()
        self.assignments_upto_level = [0]
        self.conflicts_upto_level = [0]
        self.curr_level = 0
        self.max_level = 0

    def print_clauses(self):
        print("{} variables, {} clauses".format(self.var_count, self.clause_count))
        for clause_id, clause in enumerate(self.clauses):
            clause.print(clause_id)
    
    def print_curr_assignment(self):
        assignment = "State: "
        for var, state in enumerate(self.curr_assignment):
            if (var == 0):
                continue
            assignment += ", {}: {}".format(var, state.value)
        print(assignment)

    def watch_this_clause(self, lit, clause_id):
        if lit in self.watch_map: 
            self.watch_map[lit].append(clause_id)
        else:
            self.watch_map[lit] = [clause_id]

    def insert_clause(self, clause : Clause, first_watch, second_watch):
        self.clauses.append(clause)
        clause.first_watcher = first_watch
        clause.second_watcher = second_watch
        clause_id = len(self.clauses) - 1
        # Bump their scores
        for literal in clause.literals:
            var = get_variable(literal)
            self.activity[var] += self.increment_value
        # Add this clause to two watch lists
        self.watch_this_clause(clause.get_first_watcher(), clause_id)
        self.watch_this_clause(clause.get_second_watcher(), clause_id)
    
    def assert_unary_literal(self, lit):
        self.assignments_count += 1
        var = get_variable(lit)
        if is_negative(lit):
            self.curr_assignment[var] = LiteralState.L_FALSE
        else:
            self.curr_assignment[var] = LiteralState.L_TRUE
        self.assignment_level[var] = 0

    def assert_nonunary_literal(self, lit):
        self.assignments_count += 1
        self.assigned_till_now.append(lit)
        var = get_variable(lit)
        if is_negative(lit):
            self.prev_assignment[var] = self.curr_assignment[var] = LiteralState.L_FALSE
        else:
            self.prev_assignment[var] = self.curr_assignment[var] = LiteralState.L_TRUE
        self.assignment_level[var] = self.curr_level

    def get_literal_status(self, lit : int) -> LiteralState:
        var_status = self.curr_assignment[get_variable(lit)]
        if var_status == LiteralState.L_UNASSIGNED:
            return LiteralState.L_UNASSIGNED
        elif var_status == LiteralState.L_TRUE:
            return LiteralState.L_FALSE if is_negative(lit) else LiteralState.L_TRUE
        else:
            return LiteralState.L_TRUE if is_negative(lit) else LiteralState.L_FALSE

    def bcp(self) -> (SolverState, int):
        # print("Running BCP with stack", self.bcp_stack)
        conflicting_clause_id = -1
        while (self.bcp_stack):
            lit = self.bcp_stack.pop()
            assert self.get_literal_status(lit) == LiteralState.L_FALSE

            if lit not in self.watch_map:
                self.watch_map[lit] = []
            new_watch_list = [x for x in self.watch_map[lit]]
            for clause_id in reversed(self.watch_map[lit]):
                clause = self.clauses[clause_id]
                
                # Find how is it enforced that lit is one of the watchers
                first_watch = clause.get_first_watcher()
                second_watch = clause.get_second_watcher()
                lit_is_first = (lit == first_watch)
                other_watch = second_watch if lit_is_first else first_watch
                clause_state, new_watch_loc = clause.change_watch_location(self, lit_is_first, other_watch)
                
                if (clause_state == ClauseState.C_SATISFIED):
                    pass
                elif (clause_state == ClauseState.C_UNIT):
                    self.assert_nonunary_literal(other_watch)
                    var = get_variable(other_watch)
                    self.antecedent[var] = clause_id
                    self.bcp_stack.append(get_opposite_literal(other_watch))

                elif (clause_state == ClauseState.C_CONFLICTING):
                    if self.curr_level == 0:
                        return SolverState.S_UNSATISFIED, conflicting_clause_id
                    conflicting_clause_id = clause_id
                    self.bcp_stack.clear()
                    break

                elif (clause_state == ClauseState.C_UNRESOLVED):
                    new_watch_list.remove(clause_id)
                    new_watcher = clause.literals[new_watch_loc]
                    self.watch_this_clause(new_watcher, clause_id)
            self.watch_map[lit].clear()
            self.watch_map[lit] += new_watch_list
            if (conflicting_clause_id >= 0):
                return SolverState.S_CONFLICT, conflicting_clause_id
        return SolverState.S_UNRESOLVED, conflicting_clause_id

    def get_lit_memo(self, var: int) -> int:
        prev_state = self.prev_assignment[var]
        if (prev_state == 1):
            return get_literal(var)
        else:
            # Both 0 and 1
            return get_literal(-1 * var)

    def decide(self) -> SolverState: # MINISAT based decision heuristic
        # print("Running decider")
        # self.print_curr_assignment()
        # print("Activity: ", self.activity)
        # selected_var = 0
        selected_lit = 0
        max_activity_till_now = 0.0
        unassigned_var_found = False
        for var, state in enumerate(self.curr_assignment):
            if (var == 0):
                continue
            if (state == LiteralState.L_UNASSIGNED and self.activity[var] > 0.0):
                unassigned_var_found = True
                if (self.activity[var] > max_activity_till_now):
                    # selected_var = var
                    selected_lit = self.get_lit_memo(var)
                    max_activity_till_now = self.activity[var]
        if not unassigned_var_found:
            return SolverState.S_SATISFIED
        # print(selected_lit, selected_var, max_activity_till_now)
        assert selected_lit != 0
        self.decision_count += 1
        self.curr_level += 1
        if (self.curr_level > self.max_level):
            self.max_level = self.curr_level
            self.assignments_upto_level.append(len(self.assigned_till_now))
            self.conflicts_upto_level.append(self.learnt_clauses_count)
        else:
            self.assignments_upto_level[self.curr_level] = len(self.assigned_till_now) 
            self.conflicts_upto_level[self.curr_level] = self.learnt_clauses_count       
        self.assert_nonunary_literal(selected_lit)
        self.bcp_stack.append(get_opposite_literal(selected_lit))
        return SolverState.S_UNRESOLVED
    
    def analyze_conflict(self, conflicting_clause: Clause) -> (int, int):
        # print("Running analyse_conflict")
        curr_literals = [lit for lit in conflicting_clause.literals]
        learned_clause = Clause([])
        marked = [False] * (self.var_count + 1)
        backtrack_level = 0
        to_resolve_count = 0
        watch_lit = 0

        trail_index = len(self.assigned_till_now) - 1
        resolve_lit = 0
        resolve_var = 0
        iter = 0
        while (iter == 0 or to_resolve_count > 0):
            iter += 1
            for lit in curr_literals:
                var = get_variable(lit)
                if marked[var]:
                    continue
                marked[var] = True
                if (self.assignment_level[var] == self.curr_level):
                    to_resolve_count += 1
                else:
                    learned_clause.insert_literal(lit)
                    if (self.assignment_level[var] > backtrack_level):
                        backtrack_level = self.assignment_level[var]
                        watch_lit = len(learned_clause.literals) - 1
            # Find a variable to be resolved
            while (trail_index >= 0):
                resolve_lit = self.assigned_till_now[trail_index]
                resolve_var = get_variable(resolve_lit)
                trail_index -= 1
                if marked[resolve_var]:
                    break
            marked[resolve_var] = False
            to_resolve_count -= 1
            if not to_resolve_count:
                continue 
            antecedent_id = self.antecedent[resolve_var]
            curr_literals = [lit for lit in self.clauses[antecedent_id].literals if lit != resolve_lit]
        
        # resolve_lit is an UIP
        self.learnt_clauses_count += 1
        opposite_resolv_lit = get_opposite_literal(resolve_lit)
        learned_clause.insert_literal(opposite_resolv_lit)
        self.increment_value /= CONSTANTS.VAR_DECAY_RATE
        if learned_clause.is_unary:
            self.bcp_stack.append(resolve_lit)
            self.unary_clauses.append(learned_clause)
        else:
            self.bcp_stack.append(resolve_lit)
            self.insert_clause(learned_clause, watch_lit, len(learned_clause.literals) - 1)
        # for lit in learned_clause.literals:
        #     var = get_variable(lit)
        #     print("({}, {})".format(var, self.assignment_level[var]))
        return backtrack_level, opposite_resolv_lit
    
    def backtrack(self, k: int, uip_lit):
        # print("Running backtrack")
        
        # if (k < 0 or k >= len(self.conflicts_upto_level)):
        #     print("Current level {}, backtrack to {} and max level {}".format(self.curr_level, k, self.max_level))
        #     print(self.conflicts_upto_level)
        
        if k > 0 and (self.learnt_clauses_count - self.conflicts_upto_level[k] > self.restart_threshold):
            self.reset_state()
            return

        for index in range(self.assignments_upto_level[k+1], len(self.assigned_till_now)):
            var = get_variable(self.assigned_till_now[index])
            if (self.assignment_level[var] > k):
                self.curr_assignment[var] = LiteralState.L_UNASSIGNED

        self.assigned_till_now = self.assigned_till_now[:self.assignments_upto_level[k+1]]
        self.curr_level = k
        if k == 0:
            self.assert_unary_literal(uip_lit)
        else:
            self.assert_nonunary_literal(uip_lit)
        self.antecedent[get_variable(uip_lit)] = len(self.clauses) - 1

    def verify_assignment(self):
        non_true_clauses = []
        all_clauses = self.clauses + self.unary_clauses
        for clause in all_clauses:
            true_literal_found = False
            for lit in clause.literals:
                if (self.get_literal_status(lit) == LiteralState.L_TRUE):
                    true_literal_found = True
                    break
            if not true_literal_found:
                non_true_clauses.append(clause)
        if not non_true_clauses:
            print("AC, All clauses evaluate to true under given assignment")
        else:
            print("WA, {} unsatisfied clauses found".format(len(non_true_clauses)))

    def run_cdcl(self) -> SolverState:
        result: SolverState
        while (True):
            while (True):
                result, conflicting_clause_id = self.bcp()
                # print("BCP result was {}".format(result))
                if (result == SolverState.S_UNSATISFIED):
                    return result
                if (result == SolverState.S_CONFLICT):
                    assert conflicting_clause_id != -1
                    backtrack_level, uip_lit = self.analyze_conflict(self.clauses[conflicting_clause_id])
                    # print("Analyze result was k = {}, uip = {}".format(backtrack_level, uip_lit))
                    self.backtrack(backtrack_level, uip_lit)
                else:
                    break
            result = self.decide()
            # print("Decide result was {}".format(result))
            if (result == SolverState.S_UNSATISFIED or result == SolverState.S_SATISFIED):
                return result

    def solve(self):
        # print("Solving")
        result : SolverState = self.run_cdcl()
        if (result == SolverState.S_SATISFIED):
            # print("Assignment of {} variables:".format(self.var_count))
            # for var, state in enumerate(self.curr_assignment):
            #     if (var == 0):
            #         continue
            #     print("{}: {},".format(var, state.value), end = " ")
            # print()
            print("SATISFIABLE")
        else:
            print("UNSATISFIABLE")

    def print_statistics(self, solve_time):
        print("# Statistics: ")
        print("# Restarts: ", self.restart_count)
        print("# Learned cluases: ", self.learnt_clauses_count)
        print("# Decisions: ", self.decision_count)
        print("# Implications: ", self.assignments_count - self.decision_count)
        print("# Time (s): ", solve_time)

def read_and_solve_cnf():
    input_file = open("input/sat/bmc-13.cnf", 'r')
    current_line = input_file.readline()
    tokens = current_line.split()
    while (tokens[0] != "p"):
        current_line = input_file.readline()
        tokens = current_line.split()
    var_count = int(tokens[-2])
    clause_count = int(tokens[-1])

    solver = Solver(var_count, clause_count)
    for _ in range(clause_count):
        current_line = input_file.readline()
        tokens = current_line.split()
        assert(tokens.pop() == "0")
        
        literals = set([get_literal(int(literal)) for literal in tokens])
        curr_clause = Clause(list(literals))
        if (curr_clause.is_unary):
            lit = curr_clause.literals[0]
            solver.assert_unary_literal(lit)
            solver.bcp_stack.append(get_opposite_literal(lit))
            solver.unary_clauses.append(curr_clause)
        else:
            solver.insert_clause(curr_clause, 0, 1)
    # solver.print_clauses()
    start_time = time.process_time()
    solver.solve()
    finish_time = time.process_time()
    solver.verify_assignment()
    solver.print_statistics(finish_time - start_time)

if __name__ == "__main__":
    read_and_solve_cnf()