from enum import Enum

class ClauseState(Enum):
    C_UNRESOLVED = 0
    C_SATISFIED = 1
    C_CONFLICTING = 2
    C_UNIT = 3

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
    literals: list
    first_watcher : int
    second_watcher : int
    is_unary: bool

    # def __init__(self):
    #     self.literals = []
    #     self.is_unary = False

    def __init__(self, literals: list = []):
        self.literals = literals
        self.is_unary = (len(literals) == 1)
        # self.first_watcher = 0
        # self.second_watcher = len(literals) - 1

    def insert_literal(self, lit):
        self.literals.append(lit)
        self.is_unary = (len(self.literals) == 1)

    def print(self, clause_id: int):
        print("Clause {} with literals {}".format(clause_id, self.literals))
    
    def get_first_watcher(self):
        return self.literals[self.first_watcher]
    def get_second_watcher(self):
        return self.literals[self.second_watcher]

    def change_watch_location(self, solver, is_first_watcher, other_watcher) -> (ClauseState, int):
        # find an unset watch position other than other_watcher
        for index, lit in enumerate(self.literals):
            if (lit == other_watcher):
                pass
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

    curr_level : int
    max_level : int
    curr_assignment: list
    prev_assignment: list
    assignment_level: list
    assigned_till_now: list
    antecedent : list
    separators: list

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
        self.max_level = 0
        self.curr_assignment = [LiteralState.L_UNASSIGNED] * (var_count + 1)
        self.prev_assignment = [-1] * (var_count + 1)
        self.assignment_level = [-1] * (var_count + 1)
        self.antecedent = [-1] * (var_count + 1)
        self.separators.append(0)

        self.bcp_stack = []
        self.watch_map = {}
        
        self.increment_value = 1.0
        self.activity = [0.0] * (var_count + 1)

    def print(self):
        print("{} variables, {} clauses".format(self.var_count, self.clause_count))
        for clause_id, clause in enumerate(self.clauses):
            clause.print(clause_id)

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
            self.prev_assignment[var] = self.curr_assignment[var] = LiteralState.L_FALSE
        else:
            self.prev_assignment[var] = self.curr_assignment[var] = LiteralState.L_TRUE
        self.assignment_level[var] = self.curr_level
        print("Assiged literal {} as {}, variable {} as {}".format(
            lit, LiteralState.L_TRUE, var, self.curr_assignment[var]))

    def get_literal_status(self, lit : int) -> LiteralState:
        var_status = self.curr_assignment[get_variable(lit)]
        if var_status == LiteralState.L_UNASSIGNED:
            return LiteralState.L_UNASSIGNED
        elif var_status == LiteralState.L_TRUE:
            return LiteralState.L_FALSE if is_negative(lit) else LiteralState.L_TRUE
        else:
            return LiteralState.L_TRUE if is_negative(lit) else LiteralState.L_FALSE

    def bcp(self) -> (SolverState, int):
        while (self.bcp_stack):
            lit = self.bcp_stack.pop()
            assert self.get_literal_status(lit) == LiteralState.L_FALSE

            conflicting_clause_id = -1
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
                        return SolverState.S_UNSATISFIED
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

    def decide(self) -> SolverState:
        # MINISAT based decision heuristic
        # selected_var = 0
        selected_lit = 0
        max_activity_till_now = 0.0
        unassigned_var_found = False
        for var, state in enumerate(self.curr_assignment):
            if (var == 0):
                pass
            if (state == LiteralState.L_UNASSIGNED):
                unassigned_var_found = True
                if (self.activity[var] > max_activity_till_now):
                    selected_lit = self.get_lit_memo(var)
                    max_activity_till_now = self.activity[var]
        if not unassigned_var_found:
            return SolverState.S_UNSATISFIED
        assert selected_lit != 0
        self.curr_level += 1
        if (self.curr_level > self.max_level):
            self.max_level = self.curr_level
            self.separators.append(len(self.assigned_till_now))
        else:
            self.separators[self.curr_level] = len(self.assigned_till_now)        
        self.assert_nonunary_literal(selected_lit)
        self.bcp_stack.append(get_opposite_literal(selected_lit))
        return SolverState.S_UNRESOLVED
    
    def analyze_conflict(self, conflicting_clause: Clause) -> (int, int):
        curr_literals = [lit for lit in conflicting_clause.literals]
        learned_clause = Clause()
        marked = [False] * (self.var_count + 1)
        backtrack_level = 0
        to_resolve_count = 0
        watch_lit = 0

        trail_index = len(self.assigned_till_now) - 1
        resolve_lit = 0
        resolve_var = 0
        first_iter = True
        while (first_iter or to_resolve_count > 0):
            first_iter = False
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
            while (trail_index > 0):
                resolve_lit = self.assigned_till_now[trail_index]
                resolve_var = get_variable(resolve_lit)
                if marked[resolve_var]:
                    break
            marked[resolve_var] = False
            to_resolve_count -= 1
            if not to_resolve_count:
                break 
            antecedent_id = self.antecedent[resolve_var]
            curr_literals = [lit for lit in self.clauses[antecedent_id] if lit != resolve_lit]
        
        # resolve_lit is an UIP
        opposite_resolv_lit = get_opposite_literal(resolve_lit)
        learned_clause.insert_literal(opposite_resolv_lit)
        # TODO: MINISAT decay
        if learned_clause.is_unary:
            self.bcp_stack.append(opposite_resolv_lit)
        else:
            self.bcp_stack.append(resolve_lit)
            self.insert_clause(learned_clause, watch_lit, len(learned_clause) - 1)
        return backtrack_level, opposite_resolv_lit
        
    def backtrack(self, k: int, uip_lit):
        for index in range(self.separators[k+1], len(self.assigned_till_now)):
            var = get_variable(self.assigned_till_now[index])
            if (self.assignment_level[var] > 0):
                self.curr_assignment[var] = LiteralState.L_UNASSIGNED

        self.assigned_till_now = self.assigned_till_now[:self.separators[k+1]]
        self.curr_level = k
        if k == 0:
            self.assert_unary_literal(uip_lit)
        else:
            self.assert_nonunary_literal(uip_lit)
        self.antecedent[get_variable(uip_lit)] = len(self.clauses) - 1

    def run_cdcl(self) -> SolverState:
        result: SolverState
        while (True):
            while (True):
                result, conflicting_clause_id = self.bcp()
                if (result == SolverState.S_UNSATISFIED):
                    return result
                if (result == SolverState.S_CONFLICT):
                    assert conflicting_clause_id != -1
                    backtrack_level, uip_lit = self.analyze_conflict(self.clauses[conflicting_clause_id])
                    self.backtrack(backtrack_level, uip_lit)
                else:
                    break
            result = self.decide()
            if (result == SolverState.S_UNSATISFIED or SolverState.S_UNSATISFIED):
                return result

    def solve(self):
        result : SolverState = self.run_cdcl()
        if (result == SolverState.S_SATISFIED):
            print("SATISFIABLE")
            for var, state in enumerate(self.curr_assignment):
                if (var == 0):
                    continue
                print("{}: {}".format(var, state))
        else:
            print("UNSATISFIABLE")

def read_and_solve_cnf():
    input_file = open("unsat.cnf", 'r')
    current_line = input_file.readline()
    tokens = current_line.split()
    var_count = int(tokens[-2])
    clause_count = int(tokens[-1])

    solver = Solver(var_count, clause_count)
    for _ in range(clause_count):
        current_line = input_file.readline()
        tokens = current_line.split()
        assert(tokens.pop() == "0")
        
        literals = [get_literal(int(literal)) for literal in tokens]
        curr_clause = Clause(literals)
        if (curr_clause.is_unary):
            lit = curr_clause.literals[0]
            solver.assert_unary_literal(lit)
            solver.bcp_stack.append(get_opposite_literal(lit))
        else:
            solver.insert_clause(curr_clause, 0, 1)
    solver.print()
    solver.solve()

if __name__ == "__main__":
    read_and_solve_cnf()