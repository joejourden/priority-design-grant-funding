#!/usr/bin/env python3
"""Joint satisfiability of Axioms A, B and C* in floor problems.

Searches for a floor problem admitting NO allocation that satisfies all of

    Axiom A   non-wastefulness
    Axiom B   respecting priorities
    Axiom C*  strong feasible floors

This is the existence question left open in Appendix A.4 of the paper. No such
problem has been found; see README.md for the configurations searched.

Grants are indexed in merit order: index 0 is the paper's grant 1, which has
the highest merit, so i ranks above j iff i < j as indices. Category eligibility rho(i) is carried as
a bitmask. All data are integral; README.md explains why that is without loss.

Usage
-----
    python3 cstar_search.py validate          # reproduce Proposition 1
    python3 cstar_search.py sweep --jobs 4    # the whole search; about a day
    python3 cstar_search.py --jobs 4 sweep    # --jobs works on either side
    python3 cstar_search.py exhaustive --grants 3 --categories 2 --budget 8
    python3 cstar_search.py random --trials 1000000 --seed 1

`sweep` appends each finished configuration to sweep_results.log and skips
configurations already recorded there, so an interrupted run can be restarted.
"""

from __future__ import annotations

import argparse
import itertools
import math
import os
import random
import sys
import time
from typing import Iterator, NamedTuple, Sequence

INF = 1 << 40

# (grants, categories, budget), cheapest first.
CONFIGURATIONS = [
    (2, 1, 10), (2, 2, 9), (2, 3, 8), (3, 1, 8), (3, 2, 8), (3, 3, 7),
    (4, 1, 7), (4, 2, 6), (4, 3, 5), (5, 1, 5), (5, 2, 4), (5, 3, 3),
    (6, 1, 4), (6, 2, 3),
]
LOG = "sweep_results.log"


class Problem(NamedTuple):
    """A floor problem with integral data, grants in merit order."""

    lo: tuple[int, ...]      # minimum costs, underline{b}_i
    hi: tuple[int, ...]      # maximum costs, overline{b}_i
    rho: tuple[int, ...]     # category eligibility, as bitmasks
    q: tuple[int, ...]       # floors, q_c
    budget: int              # B

    @property
    def n(self) -> int:
        return len(self.lo)

    @property
    def m(self) -> int:
        return len(self.q)

    def __str__(self) -> str:
        grants = "  ".join(
            f"[{lo},{hi}] rho={{{','.join(str(c) for c in range(self.m) if r >> c & 1)}}}"
            for lo, hi, r in zip(self.lo, self.hi, self.rho)
        )
        return f"B={self.budget}  q={self.q}  {grants}"


# --------------------------------------------------------------------------
# The axioms, as stated in Sections 4.3 and 4.4
# --------------------------------------------------------------------------


def non_wasteful(xi: Sequence[int], p: Problem) -> bool:
    """Axiom A: no grant could receive more of the unspent budget.

    With unspent budget R = s(xi), an unfunded grant must be unable to absorb
    it (lo > R), and a grant funded short of its maximum cost needs R == 0.
    """
    residual = p.budget - sum(xi)
    if residual < 0:
        return False
    for x, lo, hi in zip(xi, p.lo, p.hi):
        if x == 0:
            if lo <= residual:
                return False
        elif x < hi and residual > 0:
            return False
    return True


def respects_priorities(xi: Sequence[int], p: Problem) -> bool:
    """Axiom B.

    Clause 1: an unfunded grant's claim cannot be covered by the funding held by
    grants it dominates in the priority partial order >_rho, together with the
    unspent budget, provided at least one such grant holds funds.
    Clause 2: a grant funded at or above its minimum cost but short of its
    maximum cost leaves nothing funded below it in >_rho.
    """
    n = p.n
    residual = p.budget - sum(xi)
    for i in range(n):
        dominated = [
            j for j in range(i + 1, n)
            if xi[j] > 0 and p.rho[j] & p.rho[i] == p.rho[j]
        ]
        if xi[i] == 0:
            if dominated and sum(xi[j] for j in dominated) + residual >= p.lo[i]:
                return False
        elif p.lo[i] <= xi[i] < p.hi[i]:
            if dominated:
                return False
    return True


def floors_satisfied(xi: Sequence[int], p: Problem, *, key: str) -> bool:
    """Axiom C (key='merit') or Axiom C* (key='cost').

    Writing d_c(xi) = q_c - sum_{i in I_c} xi_i for the shortfall and
    A_c(xi) = {i in I_c : xi_i < hi_i} for the grants not fully funded:

        Axiom C   for every c with d_c > 0, the highest-merit i* in A_c(xi)
                  has xi_{i*} = 0 and lo_{i*} > d_c(xi)
        Axiom C*  for every c with d_c > 0, EVERY i in A_c(xi)
                  has xi_i = 0 and lo_i > d_c(xi)

    The two differ only in the quantifier, which is what makes C an immediate
    relaxation of C*. A category with A_c(xi) empty satisfies both vacuously.
    """
    for c, q_c in enumerate(p.q):
        bit = 1 << c
        eligible = [i for i in range(p.n) if p.rho[i] & bit]
        shortfall = q_c - sum(xi[i] for i in eligible)
        if shortfall <= 0:
            continue
        available = [i for i in eligible if xi[i] < p.hi[i]]
        targets = available[:1] if key == "merit" else available
        for i in targets:                       # grants are merit-ordered
            if xi[i] != 0 or p.lo[i] <= shortfall:
                return False
    return True


def satisfies_all(xi: Sequence[int], p: Problem, *, key: str = "cost") -> bool:
    return (
        non_wasteful(xi, p)
        and respects_priorities(xi, p)
        and floors_satisfied(xi, p, key=key)
    )


def allocations(p: Problem) -> Iterator[tuple[int, ...]]:
    """Every integral allocation: xi_i in {0} u [lo_i, hi_i], within budget.

    Fine for the shapes the sweep enumerates, where the budget is at most ten.
    At the budgets the random draws reach it would be hopeless, which is why
    `find_witness` searches rather than filters.
    """
    options = [[0] + list(range(lo, hi + 1)) for lo, hi in zip(p.lo, p.hi)]
    for xi in itertools.product(*options):
        if sum(xi) <= p.budget:
            yield xi


def find_witness(p: Problem, *, key: str = "cost"):
    """An allocation satisfying A, B and the floor axiom, or None.

    Grants are funded one at a time so a partial allocation already over budget
    is abandoned rather than completed and discarded, and the search stops at
    the first witness. Without the pruning a nine-grant problem at budget forty
    would enumerate around 10^14 tuples to keep a handful. Order matches
    `allocations`: zero first, then ascending, first grant varying slowest.
    """
    lo, hi, budget, n = p.lo, p.hi, p.budget, p.n
    current = [0] * n

    def extend(i: int, used: int):
        if i == n:
            xi = tuple(current)
            return xi if satisfies_all(xi, p, key=key) else None
        current[i] = 0
        found = extend(i + 1, used)
        if found is not None:
            return found
        for v in range(lo[i], hi[i] + 1):
            if used + v > budget:
                break
            current[i] = v
            found = extend(i + 1, used + v)
            if found is not None:
                return found
        current[i] = 0
        return None

    return extend(0, 0)


# --------------------------------------------------------------------------
# Sweeping a whole configuration
#
# Two facts make the sweep tractable. Axioms A and B never mention the floors,
# so they are checked once per grant configuration rather than once per floor
# vector; and the floor axiom at a category reduces to an upper bound on q_c,
# so each floor vector costs a handful of integer comparisons. Nothing else
# here is an optimization.
# --------------------------------------------------------------------------


def floor_bound(xi: Sequence[int], p: Problem, *, key: str) -> tuple[int, ...]:
    """Bounds U with: xi satisfies the floor axiom at q iff q_c < U_c for all c.

    At a category, the axiom is vacuous when q_c <= S_c (the funding its
    eligible grants already hold), and otherwise demands that every target be
    unfunded and cost more than the shortfall. Since every lo_i >= 1 the two
    cases collapse into one bound.
    """
    bounds = []
    for c in range(p.m):
        bit = 1 << c
        total = 0
        available = []
        for i in range(p.n):
            if p.rho[i] & bit:
                total += xi[i]
                if xi[i] < p.hi[i]:
                    available.append(i)
        if not available:                       # vacuous at every floor
            bounds.append(INF)
            continue
        targets = available[:1] if key == "merit" else available
        if all(xi[i] == 0 for i in targets):
            bounds.append(total + min(p.lo[i] for i in targets))
        else:
            bounds.append(total + 1)            # only q_c <= S_c will do
    return tuple(bounds)


def maximal_bounds(vectors: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    """Drop bound vectors dominated componentwise by another."""
    keep = []
    for u in vectors:
        if any(u != v and all(a <= b for a, b in zip(u, v)) for v in vectors):
            continue
        if u not in keep:
            keep.append(u)
    return keep


def grant_types(m: int, budget: int) -> list[tuple[int, int, int]]:
    return [
        (lo, hi, mask)
        for lo in range(1, budget + 1)
        for hi in range(lo, budget + 1)
        for mask in range(1 << m)
    ]


def floor_vectors(m: int, budget: int) -> list[tuple[int, ...]]:
    """Floors q_c >= 1 with sum_c q_c <= B, which a floor problem requires."""
    return [
        q for q in itertools.product(range(1, budget + 1), repeat=m)
        if sum(q) <= budget
    ]


def count_problems(n: int, m: int, budget: int) -> int:
    """(B(B+1)/2 * 2^m)^n * C(B, m) -- the number of problems in a shape."""
    return len(grant_types(m, budget)) ** n * math.comb(budget, m)


def _sweep_shard(task) -> tuple[int, int, list[str]]:
    n, m, budget, show, shard, shards, reference = task
    vectors = floor_vectors(m, budget)
    dummy = tuple([1] * m)
    types = grant_types(m, budget)
    seen = flagged = 0
    examples: list[str] = []

    for head in types[shard::shards]:
        for rest in itertools.product(types, repeat=n - 1):
            combo = (head,) + rest
            lo = tuple(g[0] for g in combo)
            hi = tuple(g[1] for g in combo)
            rho = tuple(g[2] for g in combo)

            base = Problem(lo, hi, rho, dummy, budget)
            bounds = maximal_bounds([
                floor_bound(xi, base, key="cost")
                for xi in allocations(base)
                if non_wasteful(xi, base) and respects_priorities(xi, base)
            ])

            for q in vectors:
                seen += 1
                covered = any(all(q[c] < u[c] for c in range(m)) for u in bounds)
                if reference:               # audit against the definition
                    p = Problem(lo, hi, rho, q, budget)
                    assert covered == (find_witness(p) is not None), p
                if not covered:
                    flagged += 1
                    if len(examples) < show:
                        examples.append(str(Problem(lo, hi, rho, q, budget)))
    return seen, flagged, examples


def run_configuration(n, m, budget, *, jobs=1, show=5, reference=False):
    """Sweep one (grants, categories, budget) shape. Returns a report line."""
    jobs = max(1, jobs)
    started = time.time()
    tasks = [(n, m, budget, show, s, jobs, reference) for s in range(jobs)]
    if jobs == 1:
        results = [_sweep_shard(tasks[0])]
    else:
        import multiprocessing

        with multiprocessing.Pool(jobs) as pool:
            results = pool.map(_sweep_shard, tasks)
    seen = sum(r[0] for r in results)
    flagged = sum(r[1] for r in results)
    for example in [e for r in results for e in r[2]][:show]:
        print(f"  NO A+B+C* ALLOCATION:  {example}", flush=True)
    minutes = (time.time() - started) / 60
    return (
        f"({n},{m},{budget}): {seen:,} problems, {flagged:,} with no "
        f"A+B+C* allocation [{minutes:.1f} min]"
    ), flagged


# --------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------


def cmd_validate(_args) -> int:
    """Reproduce the example of Proposition 1, which pins down the axiom tests."""
    lo, hi = (2, 1, 4, 2), (2, 1, 4, 2)
    rho = (0b0, 0b1, 0b1, 0b1)                  # only grant 1 is ineligible
    full = Problem(lo, hi, rho, (3,), 4)
    reduced = Problem(lo[:3], hi[:3], rho[:3], (3,), 4)
    expected = {
        ("reduced", "cost"): [(2, 1, 0)],
        ("reduced", "merit"): [(2, 1, 0)],
        ("full", "cost"): [(0, 1, 0, 2)],
        ("full", "merit"): [(0, 1, 0, 2), (2, 1, 0, 0)],
    }
    ok = True
    for name, p in (("reduced", reduced), ("full", full)):
        for key in ("cost", "merit"):
            got = [xi for xi in allocations(p) if satisfies_all(xi, p, key=key)]
            match = got == expected[(name, key)]
            ok &= match
            label = "grants 1-4" if name == "full" else "grants 1-3"
            axiom = "C*" if key == "cost" else "C "
            print(f"  A + B + {axiom}  on {label}: {got}   "
                  f"{'ok' if match else 'MISMATCH'}")
    print("\nProposition 1 reproduced." if ok else "\nFAILED to reproduce.")
    return 0 if ok else 1


def cmd_exhaustive(args) -> int:
    line, flagged = run_configuration(
        args.grants, args.categories, args.budget,
        jobs=args.jobs, show=args.show, reference=args.reference,
    )
    print(line, flush=True)
    return 1 if flagged else 0


def random_problem(rng, max_grants: int, max_categories: int,
                   max_budget: int) -> Problem:
    """Draw a floor problem, reaching shapes no enumeration can cover.

    The floors are drawn uniformly over {q : q_c >= 1, sum_c q_c <= B}, using
    the bijection with m-subsets of {1,...,B} that gives the C(B, m) count: take
    the sorted subset's successive gaps. Drawing each q_c in turn from whatever
    budget remains would instead put two thirds of the floor mass on the first
    category and leave 40% of draws with a category carrying no floor at all,
    which tests nothing -- so the multi-category reach would be illusory, and
    that is where a C* counterexample is most likely to live.
    """
    n = rng.randint(2, max_grants)
    budget = rng.randint(2, max_budget)
    m = rng.randint(1, min(max_categories, budget))   # need m <= B for q_c >= 1
    cuts = sorted(rng.sample(range(1, budget + 1), m))
    q = tuple(b - a for a, b in zip((0,) + tuple(cuts[:-1]), cuts))
    lo, hi, rho = [], [], []
    for _ in range(n):
        a = rng.randint(1, budget)
        lo.append(a)
        hi.append(rng.randint(a, budget))
        rho.append(rng.randrange(1 << m))
    return Problem(tuple(lo), tuple(hi), tuple(rho), q, budget)


def cmd_random(args) -> int:
    rng = random.Random(args.seed)
    started, flagged = time.time(), 0
    for _ in range(args.trials):
        p = random_problem(rng, args.max_grants, args.max_categories,
                           args.max_budget)
        if find_witness(p) is None:
            flagged += 1
            if flagged <= args.show:
                print(f"  NO A+B+C* ALLOCATION:  {p}", flush=True)
    minutes = (time.time() - started) / 60
    print(f"random seed {args.seed}: {args.trials:,} trials, {flagged:,} with "
          f"no A+B+C* allocation [{minutes:.1f} min]", flush=True)
    return 1 if flagged else 0


def cmd_sweep(args) -> int:
    """Run every configuration, then the random draws. Resumable."""
    done = set()
    if os.path.exists(LOG):
        with open(LOG) as fh:
            done = {line.split(":")[0] for line in fh if line.startswith("(")}
            fh.seek(0)
        with open(LOG) as fh:
            done |= {line.split(":")[0] for line in fh if line.startswith("random")}
    total_flagged = 0
    with open(LOG, "a") as log:
        for n, m, budget in CONFIGURATIONS:
            key = f"({n},{m},{budget})"
            if key in done:
                print(f"{key}: already recorded, skipping", flush=True)
                continue
            print(f"{key}: {count_problems(n, m, budget):,} problems ...",
                  flush=True)
            line, flagged = run_configuration(
                n, m, budget, jobs=args.jobs, show=args.show)
            total_flagged += flagged
            print(line, flush=True)
            log.write(line + "\n")
            log.flush()
        for seed in range(1, 4):
            key = f"random seed {seed}"
            if key in done:
                print(f"{key}: already recorded, skipping", flush=True)
                continue
            sub = argparse.Namespace(
                seed=seed, trials=args.random_trials, max_grants=9,
                max_categories=4, max_budget=40, show=args.show)
            before = time.time()
            rc = cmd_random(sub)
            total_flagged += rc
            log.write(f"{key}: {args.random_trials:,} trials, {rc} flagged "
                      f"[{(time.time() - before) / 60:.1f} min]\n")
            log.flush()
    print(f"\nSweep complete. Configurations with no A+B+C* allocation: "
          f"{total_flagged}", flush=True)
    return 1 if total_flagged else 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--jobs", type=int, default=1,
                        help="parallel worker processes")
    parser.add_argument("--show", type=int, default=5,
                        help="max flagged problems to print")
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("validate", help="reproduce the example of Proposition 1")

    sw = sub.add_parser("sweep", help="every configuration, then random draws")
    sw.add_argument("--random-trials", type=int, default=4_000_000)

    ex = sub.add_parser("exhaustive", help="one configuration")
    ex.add_argument("--grants", type=int, required=True)
    ex.add_argument("--categories", type=int, required=True)
    ex.add_argument("--budget", type=int, required=True)
    ex.add_argument("--reference", action="store_true",
                    help="assert the sweep against find_witness on every problem")

    rd = sub.add_parser("random", help="sample larger problems at random")
    rd.add_argument("--trials", type=int, default=100_000)
    rd.add_argument("--max-grants", type=int, default=9)
    rd.add_argument("--max-categories", type=int, default=4)
    rd.add_argument("--max-budget", type=int, default=40)
    rd.add_argument("--seed", type=int, default=1)

    # Accept --jobs/--show on either side of the subcommand. SUPPRESS keeps an
    # absent subparser copy from overwriting the value given before it.
    for sp in (sw, ex, rd):
        sp.add_argument("--jobs", type=int, default=argparse.SUPPRESS,
                        help=argparse.SUPPRESS)
        sp.add_argument("--show", type=int, default=argparse.SUPPRESS,
                        help=argparse.SUPPRESS)

    args = parser.parse_args(argv)
    return {
        "validate": cmd_validate,
        "sweep": cmd_sweep,
        "exhaustive": cmd_exhaustive,
        "random": cmd_random,
    }[args.command](args)


if __name__ == "__main__":
    sys.exit(main())
