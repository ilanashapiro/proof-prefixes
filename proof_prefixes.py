from z3 import *
import itertools
import time
import random
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from collections import defaultdict

base_file = "hard_140_QF_UNIA.smt2"
# base_file = "toy.smt2"

# num variables, d, to use in static partition, generates 2^d cubes
partition_depth = 8

# clause collection globals
rounds = 0
cutoff = 1000
num_samples = 32

def collect_proof_prefix_stats(file_name, assumptions=[]):
    # ctx = Context()
    s = SimpleSolver()
    s.set(relevancy=0)
    s.set("smt.case_split", 0)
    s.set("smt.max_conflicts", 10000)
    s.from_file(file_name)
 
    pos_atoms = defaultdict(float)
    neg_atoms = defaultdict(float)
 
    for a in assumptions:
        s.add(a)
 
    rounds = 0
    def on_clause(p, deps, clause):
        nonlocal rounds
        rounds += 1
        size = len(clause)
        for lit in clause:
            if is_false(lit):
                continue
            # From paper: https://arxiv.org/pdf/1711.08076
            # Given a literal l and a formula F, let occ(F,l) denote the number of occurrences of l in F. The weight of a clause C ∈F, denoted by w(F,C), is computed as follows:
            # w(F,C) = \frac{\sum_{l \in C}occ(F, \bar{l})}{2^{|C|}\cdot|C|}
            # The |C| in the denominator reduces the sum to the average and 2^|C| ensures a larger weight for shorter clauses.
            weight = 1.0 / (size * 2**size)
            if is_not(lit):
                lit = lit.arg(0)
                neg_atoms[lit] += weight
            else:
                pos_atoms[lit] += weight
        if rounds >= cutoff:
            s.interrupt()
 
    OnClause(s, on_clause)
    res = s.check()
    # print(res == unsat)
 
    return pos_atoms, neg_atoms, res

# From paper: https://www.cs.cmu.edu/~mheule/publications/proofix-SAT25.pdf (background: https://www.cs.utexas.edu/%7Emarijn/publications/cube.pdf)
# Reference: https://github.com/zaxioms0/proofix/blob/main/drat_lit_count.py
def build_static_partition(starting_cube, cube_size=partition_depth):
    to_split = [starting_cube]
    split_lits = set()
    result = []
 
    while to_split:
        # sample num_samples cubes from the current layer
        if len(to_split) <= num_samples:
            sampled_cubes = to_split
        else:
            sampled_cubes = random.sample(to_split, num_samples)
        # Collect stats for each sampled cube
        atom_scores = defaultdict(int)
        for cube in sampled_cubes:
            assumptions = cube
            pos_atoms, neg_atoms, partial_run_result = collect_proof_prefix_stats(base_file, assumptions)
            if partial_run_result == unsat:
                # print("Cube is unsat, skipping:", cube)
                continue
            # print(pos_atoms, neg_atoms)
            for v in pos_atoms:
                if v in neg_atoms: # give preference to atoms that appear in both polarities
                    atom_scores[v] = 100*pos_atoms[v]*neg_atoms[v]
                else:
                    atom_scores[v] = pos_atoms[v] # otherwise just use the score for the single polarity that exists
            for v in neg_atoms:
                if v not in pos_atoms:
                    atom_scores[v] = neg_atoms[v]
 
        # Remove already-used splitting atoms from scoring
        for v in split_lits:
            atom_scores.pop(v, None)
 
        if not atom_scores:
            print("No more atoms to split on, stopping at depth {}.".format(len(to_split[0])))
            return to_split
 
        # Select best atom to split on
        split_lit = max(atom_scores, key=atom_scores.get)
        split_lits.add(split_lit)
 
        # Extend all cubes with both polarities of the chosen variable
        new_to_split = []
        for cube in to_split:
            if len(cube) + 1 < cube_size:
                new_to_split.append(cube + [split_lit])
                new_to_split.append(cube + [Not(split_lit)])
            else:
                # print("Cube size limit reached, not splitting further:", cube)
                result.append(cube + [split_lit])
                result.append(cube + [Not(split_lit)])
        to_split = new_to_split
 
    return result

def solve_cube(cube):
    s = SimpleSolver()
    s.from_file(base_file)
    s.add(*cube)
    timeout_secs = 10
    s.set("timeout", timeout_secs * 1000)  # Z3 timeout in milliseconds
    # set_param("verbose", 10)
    res = s.check()
    if res == unknown:
        print("⚠️ Timeout or resource limit hit:", s.reason_unknown())
    else:
        print("✅ Result:", res)

if __name__ == "__main__":
    start = time.time()
    partition = build_static_partition([])
    print("Generated {} cubes in {:.2f}s\n".format(len(partition), time.time() - start))
    # for cube in partition:
    #     print("Solving cube", cube)
    #     solve_cube(cube)
    # with ProcessPoolExecutor() as executor: # CRASHES DUE TO PICKLING ISSUE OF Z3 OBJECTS
    #     results = list(executor.map(solve_cube, partition))
    # for i, r in enumerate(results):
    #     print(f"Cube {i+1}: {r}")

