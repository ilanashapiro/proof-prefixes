### Proof Prefixes in z3

from z3 import *
# file = "hard_140_QF_UNIA.smt2"
file = "toy.smt2"

s = SimpleSolver()
s.from_file(file)
pos_atoms = {}
neg_atoms = {}
rounds = 0
s.set(relevancy=0)
s.set("smt.case_split", 0)

def on_clause(p, deps, clause):
    global rounds
    print(p, clause)
    rounds += 1

    if rounds % 100 == 0:
        max_occ = 0
        max_atom = None
        for k, v in pos_atoms.items():
            if v > max_occ:
                max_atom = k
                max_occ = v
        print(max_occ, max_atom)
        max_occ = 0
        max_atom = None
        for k, v in neg_atoms.items():
            if v > max_occ:
                max_atom = k
                max_occ = v
        print(max_occ, max_atom)
        #print(pos_atoms)
        #print(neg_atoms)
    for lit in clause:
        if is_false(lit):
            continue
        if is_not(lit):
            lit = lit.arg(0)
            if lit in neg_atoms:
                neg_atoms[lit] += 1
            else:
                neg_atoms[lit] = 1
        else:
            if lit in pos_atoms:
                pos_atoms[lit] += 1
            else:
                pos_atoms[lit] = 1

    
#print(s.statistics())
OnClause(s, on_clause) 
print(s.check())

# Use OnClause callback to collect generated clauses.
# Collect stats of atoms and polarities of generated clauses
# Run with timeout
# Select atom based on scoring criteria
# Iterate and sample