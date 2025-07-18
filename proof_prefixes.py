from z3 import *
import itertools
import time
import random
import threading
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from collections import defaultdict

BASE_FILE = "hard_140_QF_UNIA.smt2"
# BASE_FILE = "toy.smt2"

# num variables, d, to use in static partition, generates 2^d cubes
PARTITION_DEPTH = 4

# clause collection globals
ROUNDS = 0
CUTOFF = 1000
NUM_SAMPLES = 32

# Shared queue of cubes to be protected by a lock
CUBE_QUEUE = []
CUBE_QUEUE_LOCK = threading.Lock()
BATCH_SIZE = 4  # You can tune this based on experiments
NUM_WORKERS = os.cpu_count() or 4  # Use number of logical CPUs

def get_next_batch():
    with CUBE_QUEUE_LOCK:
        if not CUBE_QUEUE:
            return None
        batch = CUBE_QUEUE[:BATCH_SIZE]
        del CUBE_QUEUE[:BATCH_SIZE]
        return batch

def solver_thread():
    ctx = Context()
    s = SimpleSolver(ctx)
    s.from_file(BASE_FILE)
    timeout_secs = 10
    s.set("timeout", timeout_secs * 1000)
    set_param("verbose", 0)

    while True:
        batch = get_next_batch()
        if batch is None:
            break
        for cube in batch:
            cube_with_ctx = [lit.translate(ctx) for lit in cube]
            s.push()
            res = s.check(cube_with_ctx)
            if res == unknown:
                print("⚠️ Timeout or resource limit hit:", s.reason_unknown())
            else:
                print("✅ Result:", res)
            s.pop()

def collect_proof_prefix_stats(s, assumptions=[]):
    pos_atoms = defaultdict(float)
    neg_atoms = defaultdict(float)
 
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
        if rounds >= CUTOFF:
            s.interrupt()
 
    OnClause(s, on_clause)
    res = s.check(assumptions)

    return pos_atoms, neg_atoms, res

# From paper: https://www.cs.cmu.edu/~mheule/publications/proofix-SAT25.pdf (background: https://www.cs.utexas.edu/%7Emarijn/publications/cube.pdf)
# Reference: https://github.com/zaxioms0/proofix/blob/main/drat_lit_count.py
def build_static_partition(starting_cube, cube_size=PARTITION_DEPTH):
    to_split = [starting_cube]
    split_lits = set()
    result = []
    sampling_timeout = 30 # seconds

    s = SimpleSolver()
    s.set(relevancy=0)
    s.set("smt.case_split", 0)
    s.set("smt.max_conflicts", 10000)
    s.from_file(BASE_FILE)

    sampling_start = time.time()
    while to_split:
        # sample NUM_SAMPLES cubes from the current layer
        if len(to_split) <= NUM_SAMPLES:
            sampled_cubes = to_split
        else:
            sampled_cubes = random.sample(to_split, NUM_SAMPLES)

        atom_scores = defaultdict(int)
        for cube in sampled_cubes:
            assumptions = cube
            pos_atoms, neg_atoms, partial_run_result = collect_proof_prefix_stats(s, assumptions)
            if partial_run_result == unsat:
                # print("Cube is unsat, skipping:", cube)
                continue
            
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
            elapsed = time.time() - sampling_start
            if elapsed < sampling_timeout:
                continue  # Retry if we still have time
            else:
                print(f"⏱️Could not find new atoms to split on within {sampling_timeout} seconds, stopping at depth {len(to_split[0])}.")
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

def solve_cube_synchronous(cube):
    s = SimpleSolver()
    s.from_file(BASE_FILE)

    timeout_secs = 10
    s.set("timeout", timeout_secs * 1000)  # Z3 timeout in milliseconds
    set_param("verbose", 0)
    
    res = s.check(cube) # add cube as list of assumptions
    if res == unknown:
        print("⚠️ Timeout or resource limit hit:", s.reason_unknown())
    else:
        print("✅ Result:", res)
    return res

if __name__ == "__main__":
    start = time.time()
    partition = build_static_partition([])
    CUBE_QUEUE.extend(partition)
    print("Generated {} cubes in {:.2f}s\n".format(len(partition), time.time() - start))

    # for cube in partition:
    #     print("Solving cube", cube)
    #     solve_cube_synchronous(cube)
    # sys.exit(0)

    # need to reassign contexts sequentially, parallel access to current context or its objects will result in segfault
    # see: https://github.com/Z3Prover/z3/pull/1631/files/e32dfad81e7fc14816c034d1a527975d0cc97138

    with ThreadPoolExecutor(max_workers=NUM_WORKERS) as executor:
        futures = [executor.submit(solver_thread) for _ in range(NUM_WORKERS)]
    for future in futures:
        future.result()  # Raise any exceptions that occurred

# max threads (i.e. contexts happening at once) is num processes I have * 2


# also, need to measure STABILITY: same/very similar times across runs 
# http://mtzguido.tplinkdns.com:8081/z3/compare_stats.html pick some examples that are unstable (i.e. different seeds give drastically different runtimes) and then run the same thing with the new cubing (try to get as shallow as possible, experiment with it) and see if it's stable across runs on the same partition depth
# up to me if i want to solve the cubing with multiprocess