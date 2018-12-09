import argparse
import numpy as np
from itertools import compress
from numpy import sign, floor

class Solver:
    def __init__(self, clauses):
        '''
        Create CDCL Solver object and preprocess the CNF clauses.
        '''
        # Things we need to keep track of
        self.clauses = clauses
        self.literals = []  # List of literals
        self.decision = []  # Literal decisions (0, u, or 1)
        self.w1 = []  # List of watched literals, two per clause
        self.w2 = []
        self.iw1 = []  # List of indices of watched literals, two per clause
        self.iw2 = []
        self.wpos = []  # List of clauses containing positive version of this literal (one per literal)
        self.wneg = []  # Negative literal
        self.levels = []  # List of levels at which each decision was made
        self.polarity = []  # Literal VSIDS score
        self.level = 0  # Current decision level
        self.conflict_clause = []
        self.propagate_queue = []
        self.implied_by = []

        # Preprocess
        self.preprocess()

    def preprocess(self):
        '''
        Set up variables/graph for CDCL solving.
        '''
        # Initialize all our tracking variables
        # NOTE: We assume all clauses have length > 0
        for i in range(len(self.clauses)):
            # Remove duplicates in the clause
            self.clauses[i] = list(set(self.clauses[i]))

            # It's fine to initialize the two watched 
            # literals to the first two literals in the clause
            # or the first literal in the clause if length = 1
            if len(self.clauses[i]) > 1:
                self.w1.append(self.clauses[i][0])
                self.w2.append(self.clauses[i][1])
                self.iw1.append(0)
                self.iw2.append(1)
                self.implied_by.append(-1)
            else:
                self.w1.append(self.clauses[i][0])
                self.w2.append(self.clauses[i][0])
                self.iw1.append(0)
                self.iw2.append(0)
                self.implied_by.append(-1)
            for lit in self.clauses[i]:
                if abs(lit) not in self.literals:
                    # We need to establish a new literal
                    # and all of its trappings
                    self.literals.append(abs(lit))
                    self.polarity.append(1)
                    self.decision.append(0)
                    self.levels.append(0)
                    self.implied_by.append(-1)
                    if lit > 0:
                        self.wpos.append([i])
                        self.wneg.append([])
                    else:
                        self.wpos.append([])
                        self.wneg.append([i])
                else:
                    j = self.literals.index(abs(lit))
                    self.polarity[j] += 1
                    if lit > 0:
                        self.wpos[j].append(i)
                    else:
                        self.wneg[j].append(i)
                        
    def print_state(self):
        '''
        Print the current state of the solver. For debugging.
        '''
        print('Clauses: ', self.clauses)
        print('Literals: ', self.literals)
        print('Decision:', self.decision)
        print('Watched 1: ', self.w1)
        print('Watched 2:', self.w2)
        print('Watched 1 Index: ', self.iw1)
        print('Watched 2 Index:', self.iw2)
        print('Watched positive: ', self.wpos)
        print('Watched negative: ', self.wneg)
        print('Levels: ', self.levels)
        print('Polarity: ', self.polarity)    
        
    def decide_literal(self):
        '''
        VSIDS check for new literal.
        '''
        literals_sorted = [x for _,x in sorted(zip(self.polarity,self.literals))]
        literals_undecided = [x for x in literals_sorted if self.decision[self.literals.index(x)] == 0]
        lit = literals_undecided[-1]
        self.apply_literal(lit)
        

    def resolve(self, clause):
        '''
        Used to resolve the conflict clause. See resolve rule in Handbook of Satisfiability,
        Chapter 4.
        '''
        decision_made = [x for x in clause if self.decision[self.literals.index(abs(x))] != 0]
        return list(set([x for x in decision_made if ((not ((x in clause) and (-x in clause))))]))
    
    def analyze_conflict(self):
        '''
        Analyze the conflict, return a conflict clause and a backtrack level.
        '''
        # Grab the literals we need to backtrack
        backtrack_idxs = [self.literals.index(abs(x)) for x in self.conflict_clause\
                              if (self.levels[self.literals.index(abs(x))] == self.level)]

        conflict = []
        # Add all of the clauses containing these literals to conflict
#         for idx in backtrack_idxs:
#             # If decision was -1, this was implied by negative watched clauses
#             if self.decision[idx] > 0:
#                 for clause in self.wpos[idx]:
#                     conflict.extend(self.clauses[clause])
#             elif self.decision[idx] == 0:
#                 continue
#             else:
#                 for clause in self.wneg[idx]:
#                     conflict.extend(self.clauses[clause])
                    
        for idx in backtrack_idxs:
            if self.implied_by[idx] > 0:
                conflict.extend(self.clauses[self.implied_by[idx]])
                    
        conflict.extend(self.conflict_clause)

        learned_clause = self.resolve(conflict)
        
#         print('Backtrack vars: ', [self.literals[x] for x in backtrack_idxs])
#         print('Conflict: ', conflict)
#         print('Learned clause: ', learned_clause)

        levels = [self.levels[self.literals.index(abs(x))] for x in learned_clause]
#         print('Levels: ', levels)
        b = max(levels)
#         if len(levels) > 0:
#             b = max(levels)
#         else:
#             b = 0
        #b = max(levels)
        if b == 0:
            b = -1
        return b, learned_clause
    
    def backtrack(self, b, learned_clause):
        '''
        Undo whatever created a conflict.
        '''
        # Add the learned clause to our clauses
        self.clauses.append(learned_clause)
        if len(learned_clause) > 1:
            self.w1.append(learned_clause[0])
            self.iw1.append(0)
            self.w2.append(learned_clause[1])
            self.iw2.append(1)
            self.implied_by.append(-1)
        else:
            self.w1.append(learned_clause[0])
            self.iw1.append(0)
            self.w2.append(learned_clause[0])
            self.iw2.append(0)
            self.implied_by.append(-1)
            
        temp_levels = [self.levels[self.literals.index(abs(x))] for x in learned_clause]
                
        # Update "pointers"
        clause_idx = len(self.clauses)-1
        for lit in learned_clause:
            lit_idx = self.literals.index(abs(lit))
            self.implied_by[lit_idx] = -1
            # Update the polarity
            self.polarity[lit_idx] += 1
            # Update the watched positives/negatives
            if lit > 0:
                self.wpos[lit_idx].append(clause_idx)
            else:
                self.wneg[lit_idx].append(clause_idx)
                
        # Undo variable assignments
        for level_idx in range(len(self.levels)):
            if self.levels[level_idx] >= b:
                self.levels[level_idx] = 0
                self.decision[level_idx] = 0
        
        # Set the level
        self.level = b
                
        # Flip the variables that need flipping
        for i in range(len(learned_clause)):
            if temp_levels[i] == b:
                self.apply_literal(learned_clause[i])
                
    def has_unassigned_literals(self):
        '''
        Checks if there is an undecided literal.
        '''
        return (True in [x == 0 for x in self.decision])
                
    def solve(self):
        '''
        Apply CDCL solver to self.clauses.
        '''
        if self.unit_propagation() == 'CONFLICT':
#             print('ALREADY?')
            return 'UNSATISFIABLE'
        self.level = 0
        polarity_count = 0
        while self.has_unassigned_literals():
            #self.print_state()
            self.level += 1
            self.decide_literal()
            while self.unit_propagation() == 'CONFLICT':
                polarity_count += 1
                if polarity_count > 49:
                    self.polarity = [int(floor(x/2)) for x in self.polarity]
                    polarity_count = 0
                
                b, c = self.analyze_conflict()
                
                if b < 0:
                    return 'UNSATISFIABLE'
                else:
                    # Implicitly sets self.level = b
                    self.backtrack(b, c)
        
        return 'SATISFIABLE'
    
    def get_model(self):
        '''
        Get the current solution. Obviously this has no meaning if self.solve()
        returned 'UNSATISFIED'.
        '''
        return [x*d for x,d in zip(self.literals,self.decision)]
    
    def apply_literal(self, lit):
        '''
        Let's update the literal and watched literals in the graph
        '''
        i = self.literals.index(abs(lit))
        self.decision[i] = sign(lit)
        self.levels[i] = self.level
        
        self.propagate_queue.insert(0,lit)

    def unit_propagation(self):
        '''
        Repeatedly apply UnitProp rule until no longer possible.
        '''

        #If we have unit clauses, make a decision, add them to the queue
        for i in range(len(self.clauses)):
            if (len(self.clauses[i]) == 1) and (self.decision[self.literals.index(abs(self.clauses[i][0]))] == 0):
                self.apply_literal(self.clauses[i][0])

        while len(self.propagate_queue) > 0:
            # Grab a literal from the queue
            lit = self.propagate_queue.pop()
            lit_idx = self.literals.index(abs(lit))
            
            # Find the clauses to consider
            watched = self.wneg[lit_idx]
            if lit < 0:
                watched = self.wpos[lit_idx]
            
            # Loop over said clauses
            for i in watched:
                i1 = self.literals.index(abs(self.w1[i]))
                i2 = self.literals.index(abs(self.w2[i]))
                s1 = sign(self.w1[i])
                s2 = sign(self.w2[i])
                d1 = self.decision[i1] * s1
                d2 = self.decision[i2] * s2
                
                if (d1 == 1) or (d2 == 1):
                    # Already satisfied, we're done
                    continue
                
                u = [x for x in self.clauses[i] if (((self.decision[self.literals.index(abs(x))] == 0) or (self.decision[self.literals.index(abs(x))]*sign(x) == 1)) and (x != self.w1[i]) and (x != self.w2[i]))]

                # If so, do it
                if (len(u) > 0) and ((d1 == -1) or (d2 == -1)):
                    if abs(lit) == abs(self.w1[i]):
                        self.w1[i] = u[0]
                        self.iw1[i] = self.clauses[i].index(u[0])
                    else:
                        self.w2[i] = u[0]
                        self.iw2[i] = self.clauses[i].index(u[0])
                elif ((d1 == -1) and (d2 == -1)):
                    # If both of the watch pointers are unsatisifed,
                    # we have a conflict
#                     print(self.clauses[i])
#                     print(self.w1[i])
#                     print(self.w2[i])
#                     print(u)
                    self.conflict_clause = [self.w1[i], self.w2[i]]
                    return 'CONFLICT'
                elif ((d1 == 0) or (d2 == 0)) and not ((d1 == 0) and (d2 == 0)):
                    if d1 == 0:
                        self.apply_literal(self.clauses[i][self.iw1[i]])
                        self.implied_by[i1] = i
                    else:
                        self.apply_literal(self.clauses[i][self.iw2[i]])
                        self.implied_by[i2] = i
                else:
                    pass
            
        return 'GOOD'

def basic_dpll(clauses):
    '''
    Apply basic DPLL algorithm to a list of CNF clauses.

    Parameters
    ----------
    clauses : list
        A list of CNF clauses.
    '''

    model, clauses = unit_prop(clauses)
    if len(clauses) == 0:
        return model
    elif (True in list(map(lambda x: len(x) == 0, clauses))):
        return 'UNSATISFIABLE'
    else:
        # Choose a literal
        return_list = model
        lit = choose_literal(clauses, return_list)
        clauses_1 = subsume_literal(lit, clauses)
        clauses_1 = apply_literal(-lit, clauses_1)
        clauses_2 = subsume_literal(-lit, clauses)
        clauses_2 = apply_literal(lit, clauses_2)
        
        # Redundancy check
        if clauses_1 == clauses:
            clauses_1 = [[]]
        if clauses_2 == clauses:
            clauses_2 = [[]]
        
        # Branch
        l1 = basic_dpll(clauses_1)
        l2 = basic_dpll(clauses_2)
        if l1 != 'UNSATISFIABLE':
            return_list.extend(l1)
            return_list.extend([lit])
            return(return_list)
        elif l2 != 'UNSATISFIABLE':
            return_list.extend(l2)
            return_list.extend([-lit])
            return(return_list)
        else:
            return 'UNSATISFIABLE'

def choose_literal(clauses, current_model):
    flat_list = sorted( \
                [item for sublist in clauses for item in sublist], \
                key=abs)
    idx = 0
    lit = flat_list[idx]
    while lit in current_model or -lit in current_model:
        idx = idx+1
        lit = flat_list[idx]
    return lit

def unit_prop(clauses):
    '''
    Split the remaining values into a model and the remaining CNF.
    '''
    model = []
    # Unit propagate
    while (True in list(map(lambda x: len(x) == 1, clauses))):
        for clause in clauses:
            if len(clause) == 1:
                try:
                    clauses = subsume_literal(clause[0], clauses)
                except:
                    pass
                model.append(clause[0])
                clauses = apply_literal(clause[0], clauses)

    return model, clauses

def apply_literal(l, clauses):
    '''
    Propagate literal l's truth value through the list.

    NOTE: Modification not in place is commented out.

    Parameters
    ----------
    l : int
        CNF literal.
    clauses : list
        A list of CNF clauses.
    '''
    new_clauses = []
    for clause in clauses:
        new_clauses.append([x for x in clause if abs(x) != abs(l)])
    return new_clauses

def subsume_literal(l, clauses):
    return list(compress(clauses, [l not in x for x in clauses])) 

def parse_cnf_file(fn, method='basic'):
    '''
    Parameters
    ----------
    fn : string
        CNF file name

    Returns
    -------
    string
        SATISFIABLE or UNSATISFIABLE
    '''
    # Split the file
    cnf_split = fn.split('\n')
    delta = []

    # Rely on structure to check for nbvar, nbclauses
    cnf_properties = cnf_split[0].split()
    if cnf_properties[0] == 'p' and cnf_properties[1] == 'cnf':
        n_var = int(cnf_properties[2])
        n_clauses = int(cnf_properties[3])
        # Create a list of clauses
        for i in range(n_clauses):
            clause = list(map(int, cnf_split[i+1].split()))
            # Make sure all values in our CNF file are within 
            # [-n_var, nvar]
            if any(abs(i) > n_var for i in clause) or clause[-1] != 0:
                # File contains improper predicates, so it's unsat
                return('UNSATISFIABLE')
            # Append to our list of clauses
            delta.append(clause[:-1])
        # Now apply DPLL
        #print(delta)
        decision = dpll(delta, method)
        # sat
        if decision != 'UNSATISFIABLE':
            return ' SATISFIABLE ' + \
                   ' '.join(str(d) for d in sorted(decision, key=abs))
        # unsat
        return decision
    else:
        # File is in the wrong format, so it's unsat
        return 'UNSATISFIABLE', []

def dpll(clauses, method='basic'):
    if method == 'basic':
        return basic_dpll(clauses)
    if method == 'cdcl':
        model = Solver(clauses)
        sat = model.solve()
        if sat == 'SATISFIABLE':
            return model.get_model()
        else:
            return 'UNSATISFIABLE'
    else:
        return 'UNSATISFIABLE'
    return 'UNSATISFIABLE'

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('fn', type=str, help='CNF file to analyze.')
    parser.add_argument('-m', '--method', type=str, default='cdcl',
                        choices = ['basic', 'cdcl'],
                        help='DPLL method. Options are "basic"')
    args = parser.parse_args()
    with open(args.fn, 'r') as f:
        cnf = f.read()
        decision = parse_cnf_file(cnf, args.method)
        print(decision)
