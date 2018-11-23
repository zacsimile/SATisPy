import sys
import numpy as np
from itertools import compress

def dpll(clauses):
    '''
    Apply basic DPLL algorithm to a list of CNF clauses.

    Parameters
    ----------
    clauses : list
        A list of CNF clauses.
    '''
    #print(clauses)
    model, clauses = unit_prop(clauses)
    if len(clauses) == 0:
        return model
    elif (True in list(map(lambda x: len(x) == 0, clauses))):
        return 'UNSATISFIABLE'
    else:
        # Choose a literal
        return_list = model
        lit = clauses[0][0]
        clauses_1 = list(compress(clauses, [lit not in x for x in clauses])) # apply_literal(lit, clauses)
        clauses_2 = list(compress(clauses, [-lit not in x for x in clauses])) # apply_literal(-lit, clauses)
        # Redundancy check
        if clauses_1 == clauses:
            clauses_1 = [[]]
        if clauses_2 == clauses:
            clauses_2 = [[]]
        l1 = dpll(clauses_1)
        l2 = dpll(clauses_2)
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
                    #clauses.remove(clause)
                    #print('delete' + clause[0])
                    #print(clauses)
                    clauses = list(compress(clauses, [clause[0] not in x for x in clauses]))
                    #print(clauses)
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
    #for i in range(len(clauses)):
    for clause in clauses:
        new_clauses.append([x for x in clause if abs(x) != abs(l)])
        # new_clauses.append(list(map(lambda x: \
        #     True if x == l else (False if x == -l else x), clause)))
    return new_clauses
    # return new_clauses

def parse_cnf_file(fn):
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
            clause = list(map(int, cnf_split[i+1].split()))[:-1]
            # Make sure all values in our CNF file are within 
            # [-n_var, nvar]
            if any(abs(i) > n_var for i in clause):
                # File contains improper predicates, so it's unsat
                return('UNSATISFIABLE')
            # Append to our list of clauses
            delta.append(clause)
        # Now apply DPLL
        decision = dpll(delta)
        # sat
        if decision != 'UNSATISFIABLE':
            return 'SATISFIABLE ' + \
                   ' '.join(str(d) for d in sorted(decision, key=abs))
        # unsat
        return decision
    else:
        # File is in the wrong format, so it's unsat
        return 'UNSATISFIABLE', []

if __name__ == '__main__':
    with open(sys.argv[1], 'r') as f:
        cnf = f.read()
        decision = parse_cnf_file(cnf)
        print(decision)
