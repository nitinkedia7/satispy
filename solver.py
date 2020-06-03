"""
Author: Nitin Kedia, 160101048
Description: A CDCL based SAT solver
"""

import time, random, copy, enum
from sortedcontainers import SortedSet

class CONSTANTS:
    # These constant will be explained in context
    # used in MINISAT (decision heuristic)
    VAR_DECAY_RATE = 0.95
    # used to decide when to restart
    THRESHOLD_MULTIPLIER = 1.1
    RESTART_LOWER_BOUND = 100
    RESTART_UPPER_BOUND_BASE = 1000

class ClauseState(enum.auto):
    C_UNRESOLVED = 0
    C_SATISFIED = 1
    C_CONFLICTING = 2
    C_UNIT = 3 # Only one literal is undecided, rest eval to false

# Note that LiteralState also functions as VariableState
# The state a literal of a variable fixes that of the variable and vice-versa
class LiteralState(enum.auto):
    L_UNASSIGNED = -1
    L_FALSE = 0
    L_TRUE = 1

class SolverState(enum.auto):
    S_UNRESOLVED = 0
    S_SATISFIED = 1
    S_UNSATISFIED = 2
    S_CONFLICT = 3

"""
Variables are denoted by positive integers 1, 2, ..., VAR_COUNT
The positive literal of a variable v is given by 2*v, while negation is 2*v - 1
Following four are help functions based on this terminology
"""
def get_literal(v: int) -> int:
    # if (v == 0):
    #     raise Exception("Variable cannot be zero.")
    return 2 * v if v > 0 else 2 * (abs(v)) - 1

def get_variable(l : int) -> int:
    # if (l <= 0):
    #     raise Exception("Literal must be a positive integer, is {}".format(l))
    return int((l + 1) / 2) if l % 2  else int(l / 2)

def get_opposite_literal(l : int) -> int:
    # if (l <= 0):
    #     raise Exception("Literal must be a positive integer, is {}".format(l))
    return (l + 1) if l % 2 else (l - 1)

def is_negative(l : int) -> bool:
    # if (l <= 0):
    #     raise Exception("Literal must be a positive integer, is {}".format(l))
    return True if l % 2 else False

class Clause:
    def __init__(self, literals: list):
        self.literals = literals
        self.is_unary = (len(literals) == 1)
        self.first_watcher = -1
        self.second_watcher = -1

    def insert_literal(self, lit):
        if lit not in self.literals: # To ensure all literals are unique
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

    """
    Two watch optimisation used in BCP (unit propagation):
    Base case: Initially we keep two watchers pointing to two different (unassigned) literals in the clause.
    Invariant: If both the watchers are unassigned, the clause cannot be unit (which requires exactly one assigned)
    """
    def change_watch_location(self, solver, is_first_watcher, other_watcher) -> (ClauseState, int):
        # This function is called in bcp(). One of the watchers depending on is_first_watcher is being assigned FALSE.
        # First, try to find another unassigned literal
        for index, lit in enumerate(self.literals):
            if (lit == other_watcher):
                continue
            lit_state = solver.curr_literal_assignment[lit]
            # lit_state = solver.get_literal_status(lit)
            if (lit_state != LiteralState.L_FALSE):
                if is_first_watcher:
                    self.first_watcher = index
                else:
                    self.second_watcher = index
                return ClauseState.C_UNRESOLVED, index
        # Could not find another unassigned, fate of the clause is in the hands of the other watcher
        other_watch_status = solver.curr_literal_assignment[other_watcher]
        # other_watch_status = solver.get_literal_status(other_watcher)
        if (other_watch_status == LiteralState.L_FALSE):
            # All literals are false
            return ClauseState.C_CONFLICTING, None
        elif other_watch_status == LiteralState.L_UNASSIGNED:
            # Exactly one unassigned (other watcher) remains
            return ClauseState.C_UNIT, None
        else:
            assert(other_watch_status == LiteralState.L_TRUE)
            return ClauseState.C_SATISFIED, None

class Solver:
    def __init__(self, var_count, clause_count):
        self.var_count = var_count
        self.clause_count = clause_count
        self.clauses = []
        self.unary_clauses = []
        self.curr_level = 0 # Current depth of the decision tree
        self.max_level = 0

        # Since variables are 1-indexed, size of these lists if (var_count + 1)
        # curr_assignment gives the latest assignment of a variable
        self.curr_assignment = [LiteralState.L_UNASSIGNED] * (var_count + 1)
        self.curr_literal_assignment = [LiteralState.L_UNASSIGNED] * (2 * var_count + 1)
        # prev_assignment is used in PHASE SAVING
        self.prev_assignment = [-1] * (var_count + 1)
        # The level the variable was assigned at (if at all)
        self.assignment_level = [-1] * (var_count + 1)
        # A stack of all assigned variables in current path, most recently assigned variables are at top
        self.assigned_till_now = []
        self.assignments_upto_level = [0] # How many assignments had happened upto a level?
        self.conflicts_upto_level = [0] # How many conflicts hence clauses learned upto a level?
        self.antecedent = [-1] * (var_count + 1)
        self.score2var = SortedSet()

        self.bcp_stack = []
        # watch_map: literal -> list of clauses for which this literal is the watcher
        self.watch_map = {} 

        # Used in MINISAT decision heuristic explained in decider()    
        self.increment_value = 1.0
        self.activity = [0.0] * (var_count + 1)

        # Used in restart optimisation explained in reset_state()
        self.restart_threshold = CONSTANTS.RESTART_LOWER_BOUND
        self.restart_upper_bound = CONSTANTS.RESTART_UPPER_BOUND_BASE
        
        # Statistics
        self.restart_count = 0
        self.learnt_clauses_count = 0
        self.decision_count = 0
        self.assignments_count = 0
        self.global_max_score = 0.0
    
    def assign_variable(self, var: int, assignment: LiteralState):
        self.curr_assignment[var] = assignment
        if assignment != LiteralState.L_UNASSIGNED:
            self.prev_assignment[var] = assignment
        self.curr_literal_assignment[get_literal(var)] = assignment
        neg_assignment = LiteralState.L_UNASSIGNED 
        if assignment == LiteralState.L_TRUE:
            neg_assignment = LiteralState.L_FALSE
        elif assignment == LiteralState.L_FALSE:
            neg_assignment = LiteralState.L_TRUE
        self.curr_literal_assignment[get_literal(-1 * var)] = neg_assignment
    
    def bump_var_score(self, var: int, increment_value = 0.0):
        if increment_value > 0:
            self.score2var.discard((self.activity[var], var))
            self.activity[var] += increment_value
        self.score2var.add((self.activity[var], var))

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
    
    # This fn is used to add the given clause to the watchlist of given literal
    def watch_this_clause(self, lit, clause_id):
        if lit in self.watch_map: 
            self.watch_map[lit].add(clause_id)
        else:
            self.watch_map[lit] = set([clause_id])
    
    # Insert a new (input / learned) clause to the cnf
    def insert_clause(self, clause : Clause, first_watch, second_watch):
        self.clauses.append(clause)
        # Setup the two-watch mechanism, both these literals are guaranteed to be unassigned currently
        clause.first_watcher = first_watch
        clause.second_watcher = second_watch
        clause_id = len(self.clauses) - 1
        self.watch_this_clause(clause.get_first_watcher(), clause_id)
        self.watch_this_clause(clause.get_second_watcher(), clause_id)
        
        # In MINISAT decision heusristic:
        # Score of a varible is the number of clauses in it
        # Since we are inserting a clause, increase the scores of variables in this literal
        for literal in clause.literals:
            var = get_variable(literal)
            self.bump_var_score(var, self.increment_value)
            # self.activity[var] += self.increment_value
    
    # Function used to assign a literal TRUE in a unary clause
    # These assignments are never reset hence not put in assigned_till_now[]
    def assert_unary_literal(self, lit):
        self.assignments_count += 1
        var = get_variable(lit)
        # Set state of the underlying variable
        if is_negative(lit):
            self.assign_variable(var, LiteralState.L_FALSE)
            # self.curr_assignment[var] = LiteralState.L_FALSE
        else:
            self.assign_variable(var, LiteralState.L_TRUE)
            # self.curr_assignment[var] = LiteralState.L_TRUE
        self.assignment_level[var] = 0 # Always done at ground level
    
    # Function used to assign a literal TRUE in a non-unary clause
    # Note that current level is important here
    def assert_nonunary_literal(self, lit):
        self.assignments_count += 1
        self.assigned_till_now.append(lit)
        var = get_variable(lit)
        if is_negative(lit):
            self.assign_variable(var, LiteralState.L_FALSE)
            # self.prev_assignment[var] = self.curr_assignment[var] = LiteralState.L_FALSE
        else:
            self.assign_variable(var, LiteralState.L_TRUE)
            # self.prev_assignment[var] = self.curr_assignment[var] = LiteralState.L_TRUE
        self.assignment_level[var] = self.curr_level

    """
    Function to implement Boolean Constant Propagation using Two-watcher optimisation:
    bcp_stack contains all the literals which have been assigned false in current search path.
    Since we know these literals can now change the state of other clauses.
    A naive approach of bcp would be iterate every clause to find a unit/unsatisifed clause.
    If found, repreat the process again else, stop and start guessing some variables in decider()
    """
    def bcp(self) -> (SolverState, int):
        # print("Running BCP with stack", self.bcp_stack)
        conflicting_clause_id = -1
        while (self.bcp_stack):
            # Got a literal with FALSE assignment
            lit = self.bcp_stack.pop()
            assert self.curr_literal_assignment[lit] == LiteralState.L_FALSE
            # assert self.get_literal_status(lit) == LiteralState.L_FALSE
            
            if lit not in self.watch_map:
                self.watch_map[lit] = set()
            new_watch_list = copy.copy(self.watch_map[lit]) # Backup watch list of lit
            

            # Traverse only the watchlist of that clause to save computation
            for clause_id in self.watch_map[lit]:
                clause = self.clauses[clause_id]
                
                # This block determines which watcher (1st / 2nd) was lit
                first_watch = clause.get_first_watcher()
                second_watch = clause.get_second_watcher()
                lit_is_first = (lit == first_watch)
                other_watch = second_watch if lit_is_first else first_watch
                # Now that we know lit has been assigned FALSE, we need to find another watcher
                new_clause_state, new_watch_loc = clause.change_watch_location(self, lit_is_first, other_watch)
                
                # clause has one more literal FALSE, this might change a state
                if (new_clause_state == ClauseState.C_SATISFIED):
                    pass
                elif (new_clause_state == ClauseState.C_UNIT):
                    # If the clause had become unit, we have got another implication here
                    self.assert_nonunary_literal(other_watch)
                    var = get_variable(other_watch)
                    self.antecedent[var] = clause_id
                    self.bcp_stack.append(get_opposite_literal(other_watch))
                elif (new_clause_state == ClauseState.C_CONFLICTING):
                    # All the literals of this clause became false, we have a conflict, need to backtrack
                    # If the conflict occured at ground level, we have a unsatisfiable cnf like (x) ^ (-x)
                    if self.curr_level == 0:
                        return SolverState.S_UNSATISFIED, conflicting_clause_id
                    conflicting_clause_id = clause_id
                    # Clear bcp_stack as a backtrack is coming, which will unassign several variables
                    # As such some information in bcp_state is likely to become stale
                    self.bcp_stack.clear()
                    break
                elif (new_clause_state == ClauseState.C_UNRESOLVED):
                    # The clause is still unresolved as we have found another watcher
                    # Remove this clause from watch list of current lit
                    new_watch_list.remove(clause_id)
                    new_watcher = clause.literals[new_watch_loc]
                    self.watch_this_clause(new_watcher, clause_id)
            
            # new_watch_list contains the clauses for which lit is still the watcher
            # Note that in case of backtrack, we dot need to revert the watchers in two-watcher method
            # since in backtracking, some variables will be unassigned, enforcing the two-watch invariant
            self.watch_map[lit].clear()
            self.watch_map[lit] = new_watch_list
            if (conflicting_clause_id >= 0):
                return SolverState.S_CONFLICT, conflicting_clause_id
        return SolverState.S_UNRESOLVED, conflicting_clause_id

    """
    This function is for the PHASE-SAVING heuristic
    In decider() after the variable to be guessed has been selected, we then
    need it set it to TRUE of FALSE. Phase-saving says we should set it to our
    previous assignment if any.  
    """
    def get_lit_memoised(self, var: int) -> int:
        prev_state = self.prev_assignment[var]
        if (prev_state == LiteralState.L_TRUE):
            return get_literal(var)
        else:
            return get_literal(-1 * var)

    """
    decide() function selects the next variable to be guessed and the guessed value.
    Based on MINISAT decision heuristic. Results in increment of current level.  
    Score of a varible is the number of clauses in it.
    """
    def decide(self) -> SolverState: # MINISAT based decision heuristic
        # print("Running decider")
        # self.print_curr_assignment()
        # print("Activity: ", self.activity)
        # Find an unassigned one with maximum score
        # Some inputs have unused variables, so we select only those with positive score.
        selected_lit = 0
        unassigned_var_found = False
        while self.score2var:
            max_score, var = self.score2var.pop()
            self.global_max_score = max(self.global_max_score, max_score)
            if self.curr_assignment[var] == LiteralState.L_UNASSIGNED:
                unassigned_var_found = True
                selected_lit = self.get_lit_memoised(var)
                break
        
        if not unassigned_var_found:
            return SolverState.S_SATISFIED
        # print(selected_lit, selected_var, max_activity_till_now)
        assert selected_lit != 0
        self.decision_count += 1
        self.curr_level += 1
        # We need to track this new assignment
        if (self.curr_level > self.max_level):
            # This branch is separate since we are at a new decision level,
            # so push_back is required instead of update
            self.max_level = self.curr_level
            self.assignments_upto_level.append(len(self.assigned_till_now))
            self.conflicts_upto_level.append(self.learnt_clauses_count)
        else:
            self.assignments_upto_level[self.curr_level] = len(self.assigned_till_now) 
            self.conflicts_upto_level[self.curr_level] = self.learnt_clauses_count       
        
        # Now we assign the literal as TRUE, and since put the (FALSE) opposite literal to bcp stack
        self.assert_nonunary_literal(selected_lit)
        self.bcp_stack.append(get_opposite_literal(selected_lit))
        return SolverState.S_UNRESOLVED
    
    """
    analyse_conflict() takes a conflicting clause and returns the level to backtrack to, and a learned clause
    We use the nearest UIP (Unique Implication Point) finding method as highlighted in Kroening's book.
    """
    def analyze_conflict(self, conflicting_clause: Clause) -> (int, int):
        # print("Running analyse_conflict")
        curr_literals = [lit for lit in conflicting_clause.literals]
        learned_clause = Clause([])
        backtrack_level = 0 # to be returned by this function
        to_resolve_count = 0
        watch_lit = 0 # a watcher for the new learned literal

        marked = [False] * (self.var_count + 1)
        trail_index = len(self.assigned_till_now) - 1
        resolve_lit = 0
        resolve_var = 0
        iter = 0
        """
        This loop outputs the learned clause, it works as follows:
        Invariant 1: curr_literals is the clause to be fused into learned_clause
        Invariant 2: learned caluse contains exactly one variable assigned at current level (UIP)
        All other literals are assigned before.
        """
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
                        # watch_lit: 2nd highest assigment level, first is UIP
                        backtrack_level = self.assignment_level[var]
                        watch_lit = len(learned_clause.literals) - 1
            # Find a variable to be resolved by traversing the recently assigned literals first
            while (trail_index >= 0):
                resolve_lit = self.assigned_till_now[trail_index]
                resolve_var = get_variable(resolve_lit)
                trail_index -= 1
                if marked[resolve_var]:
                    break
            marked[resolve_var] = False
            to_resolve_count -= 1
            if not to_resolve_count:
                # Just one literal remaining with current level assignment, we are done
                continue 
            antecedent_id = self.antecedent[resolve_var]
            curr_literals = [lit for lit in self.clauses[antecedent_id].literals if lit != resolve_lit]
        
        # The learned clause becomes an unit clause after backtracking
        # This is because every other literal in the learned clause was assigned before
        # the backtrack level
        # resolve_lit is an UIP
        self.learnt_clauses_count += 1
        opposite_resolv_lit = get_opposite_literal(resolve_lit)
        learned_clause.insert_literal(opposite_resolv_lit)
        self.increment_value /= CONSTANTS.VAR_DECAY_RATE
        if learned_clause.is_unary:
            # Not that we are inserting to bcp_stack without asserting UIP
            # Asserting will be done immediately after backtrack (see backtrack())
            self.bcp_stack.append(resolve_lit)
            self.unary_clauses.append(learned_clause)
        else:
            self.bcp_stack.append(resolve_lit)
            self.insert_clause(learned_clause, watch_lit, len(learned_clause.literals) - 1)
        # for lit in learned_clause.literals:
        #     var = get_variable(lit)
        #     print("({}, {})".format(var, self.assignment_level[var]))
        return backtrack_level, opposite_resolv_lit

    # RESTART heuristic, reset all assignments except ground level and start afresh
    # Note that learned claused are not deleted only we start assignments from the beginning 
    def reset_state(self):
        # print("Restart")
        """
        The threshold system works as follows eg. (chainsaw graph)
        1. We have a range [1, 10]. Threshold increases after every restart till it crosses the ub
        2. At that point the threshold is rest and the range is also increased to let it go even higher
        """
        self.restart_count += 1
        self.restart_threshold = int(self.restart_threshold * CONSTANTS.THRESHOLD_MULTIPLIER)
        if (self.restart_threshold > self.restart_upper_bound):
            self.restart_threshold = CONSTANTS.RESTART_LOWER_BOUND
            self.restart_upper_bound = int(self.restart_upper_bound * CONSTANTS.THRESHOLD_MULTIPLIER)

        # Resets are similar to backtrack() function below, except that it resets evrything to ground level  
        for var in range(1, self.var_count + 1):
            if (self.assignment_level[var] > 0):
                self.assign_variable(var, LiteralState.L_UNASSIGNED)
                # self.curr_assignment[var] = LiteralState.L_UNASSIGNED
                self.bump_var_score(var)
        
        self.bcp_stack.clear()
        self.assigned_till_now.clear()
        self.assignments_upto_level = [0]
        self.conflicts_upto_level = [0]
        self.curr_level = 0
        self.max_level = 0
    
    # Function to backtrack based on the output of analyse_conflict() 
    def backtrack(self, k: int, uip_lit):
        # print("Running backtrack")
        # Invoke restart heuristic if too many clauses have been learnt after backtrack target level
        if k > 0 and (self.learnt_clauses_count - self.conflicts_upto_level[k] > self.restart_threshold):
            self.reset_state()
            return
        # Iterate over the variables assigned at level >= k + 1 and unassign them
        for index in range(self.assignments_upto_level[k+1], len(self.assigned_till_now)):
            var = get_variable(self.assigned_till_now[index])
            if (self.assignment_level[var] > k):
                self.assign_variable(var, LiteralState.L_UNASSIGNED)
                # self.curr_assignment[var] = LiteralState.L_UNASSIGNED
                self.bump_var_score(var)

        # analyse_function() returns an asserting clause with the UIP just ready for assignment
        # This helps to immediately put the learnt clause into practice
        self.assigned_till_now = self.assigned_till_now[:self.assignments_upto_level[k+1]]
        self.curr_level = k
        if k == 0:
            # We had learnt a unary clause
            self.assert_unary_literal(uip_lit)
        else:
            self.assert_nonunary_literal(uip_lit)
        self.antecedent[get_variable(uip_lit)] = len(self.clauses) - 1

    # Function to verify output assignment if any
    def verify_assignment(self):
        non_true_clauses = []
        all_clauses = self.clauses + self.unary_clauses
        # Every clause including learnt and unary must have atleast one TRUE literal
        for clause in all_clauses:
            true_literal_found = False
            for lit in clause.literals:
                if self.curr_literal_assignment[lit] == LiteralState.L_TRUE:
                # if (self.get_literal_status(lit) == LiteralState.L_TRUE):
                    true_literal_found = True
                    break
            if not true_literal_found:
                non_true_clauses.append(clause)
        if not non_true_clauses:
            print("AC, All clauses evaluate to true under given assignment")
        else:
            print("WA, {} unsatisfied clauses found".format(len(non_true_clauses)))

    """
    Function implementing the standard CDCL framework:
        1. [Outer Loop] Run BCP and decide() alternately, bcp first because of unary clauses
        2. [INNER LOOP] Run till BCP gives UNRESOLVED result on which point guesswork must be done.
        If bcp encounters conflict a analyse, backtrack pair is done
    """     
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

    # Wrapper function to print the result of the CDCL framework
    def solve(self):
        # print("Solving")
        result : SolverState = self.run_cdcl()
        if (result == SolverState.S_SATISFIED):
            print("SATISFIABLE")
            self.verify_assignment()
            with open("assignment.txt", 'w') as assignment_file:
                for var, state in enumerate(self.curr_assignment):
                    if (var == 0):
                        assignment_file.write("State: ")
                        continue
                    assignment_file.write("{} ".format(-1 * var if state == LiteralState.L_FALSE else var))
        else:
            print("UNSATISFIABLE")

    def print_statistics(self, solve_time):
        print("## Statistics: ")
        print("# Restarts: ", self.restart_count)
        print("# Learned clauses: ", self.learnt_clauses_count)
        print("# Decisions: ", self.decision_count)
        print("# Implications: ", self.assignments_count - self.decision_count)
        print("# Max score: ", self.global_max_score)
        print("# Time (s): ", solve_time)

# IO function
def read_and_solve_cnf(input_file):
    # Read the specified input cnf file
    input_file = open(input_file, 'r')
    current_line = input_file.readline()
    tokens = current_line.split()
    while (tokens[0] != "p"):
        # Some inputs have redundant starting lines like "c 1 = P9_0[0]"
        current_line = input_file.readline()
        tokens = current_line.split()
    var_count = int(tokens[-2])
    clause_count = int(tokens[-1])
    solver = Solver(var_count, clause_count)
    # Read each clause of the CNF
    for _ in range(clause_count):
        current_line = input_file.readline()
        tokens = current_line.split()
        assert(tokens.pop() == "0")
        
        # set removes duplicate literals from the clause
        literals = set([get_literal(int(literal)) for literal in tokens])
        curr_clause = Clause(list(literals))
        # unary clauses are processed at ground level
        # this also gives some false literals to process in the bcp_stack
        if (curr_clause.is_unary):
            lit = curr_clause.literals[0]
            solver.assert_unary_literal(lit)
            solver.bcp_stack.append(get_opposite_literal(lit))
            solver.unary_clauses.append(curr_clause)
        else:
            x = random.randrange(len(literals))
            y = random.randrange(len(literals))
            while x == y:
                y = random.randrange(len(literals))
            solver.insert_clause(curr_clause, x, y)

    # solver.print_clauses()
    start_time = time.process_time()
    solver.solve()
    finish_time = time.process_time()
    solver.print_statistics(finish_time - start_time)

if __name__ == "__main__":
    random.seed(0)
    input_file = "input/sat/bmc-1.cnf"
    read_and_solve_cnf(input_file)