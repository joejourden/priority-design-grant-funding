#!/usr/bin/env python3
"""Independence of Axioms A, B, D and E for earmark problems.

Checks the four allocations used in the proof of Proposition 2 (the earmark
axioms are independent): each satisfies three of the axioms and fails the
fourth. The axioms are coded directly from their statements in Sections 4.3
and 4.6, not from any property of the serial-SR rule.

Grants are indexed in merit order: index 0 is the paper's grant 1, which has
the highest merit, so i ranks above j iff i < j. Category 0 is the open category o, which lies in
every rho(i) by assumption; eligibility rho(i) is carried as a set of category
indices. A disaggregate allocation x is a list of rows, x[i][c] giving the
assignment from category c's reserve to grant i.

Usage
-----
    python3 earmark_independence.py
"""

from __future__ import annotations

import sys
from typing import Sequence


class Problem:
    """An earmark problem: cost bounds, eligibility sets and reserves."""

    def __init__(self, lo: Sequence[int], hi: Sequence[int],
                 rho: Sequence[set], q: Sequence[int]) -> None:
        self.lo, self.hi, self.rho, self.q = lo, hi, rho, q
        self.n, self.m = len(lo), len(q)

    @property
    def budget(self) -> int:
        return sum(self.q)


def row_sums(x):
    return [sum(row) for row in x]


def col_sums(x):
    return [sum(row[c] for row in x) for c in range(len(x[0]))]


def attainable(x, p: Problem) -> bool:
    """Every grant is unfunded or within its bounds; no reserve is overdrawn."""
    for i, xi in enumerate(row_sums(x)):
        if xi != 0 and not (p.lo[i] <= xi <= p.hi[i]):
            return False
    return all(0 <= xc <= p.q[c] for c, xc in enumerate(col_sums(x)))


def eligibility_compliant(x, p: Problem) -> bool:
    """Axiom D: x[i][c] = 0 whenever c is not in rho(i)."""
    return all(x[i][c] == 0
               for i in range(p.n) for c in range(p.m)
               if c not in p.rho[i])


def non_wasteful(x, p: Problem) -> bool:
    """Axiom A, with the comparison restricted to eligibility-compliant matrices.

    An eligibility-compliant expansion exists exactly when some single grant can
    absorb more from the reserves of its own categories: if several grants can
    be raised at once, dropping all but one still leaves a valid expansion.
    """
    xi, xc = row_sums(x), col_sums(x)
    for i in range(p.n):
        idle = sum(p.q[c] - xc[c] for c in p.rho[i])
        if idle <= 0:
            continue
        if 0 < xi[i] < p.hi[i]:                 # raise a partially funded grant
            return False
        if xi[i] == 0 and idle >= p.lo[i]:      # or start an unfunded one
            return False
    return True


def respects_priorities(x, p: Problem) -> bool:
    """Axiom B, earmark version.

    Clause 1: for an unfunded grant i, no J that actually reclaims something
    from grants i outranks can cover lo_i once idle eligible reserve is added.
    Taking J = I maximises the reclaimable total, so one test suffices.
    Clause 2: a grant funded at or above its minimum cost but short of its
    maximum cost leaves nothing funded, in its own categories, to a grant of
    lower merit.
    """
    xi, xc = row_sums(x), col_sums(x)
    for i in range(p.n):
        if xi[i] == 0:
            reclaimable = sum(x[j][c]
                              for j in range(i + 1, p.n)
                              for c in p.rho[i] & p.rho[j])
            idle = sum(p.q[c] - xc[c] for c in p.rho[i])
            if reclaimable > 0 and reclaimable + idle >= p.lo[i]:
                return False
        elif p.lo[i] <= xi[i] < p.hi[i]:
            for j in range(i + 1, p.n):
                if sum(x[j][c] for c in p.rho[i]) > 0:
                    return False
    return True


def category_neutral(x, p: Problem) -> bool:
    """Axiom E: a category contributes less than another eligible one only when
    it is exhausted on i together with the higher-merit grants eligible for it."""
    for i in range(p.n):
        if not p.rho[i]:
            continue
        top = max(x[i][c] for c in p.rho[i])
        for c in p.rho[i]:
            if x[i][c] < top:
                spent = x[i][c] + sum(x[k][c] for k in range(i) if c in p.rho[k])
                if spent != p.q[c]:
                    return False
    return True


AXIOMS = {"A": non_wasteful,
          "B": respects_priorities,
          "D": eligibility_compliant,
          "E": category_neutral}

# Witnesses from the proof. Category 0 is o; category 1, where present, is alpha.
WITNESSES = {
    "A": (Problem([1], [2], [{0}], [2]), [[1]]),
    "B": (Problem([2, 2], [2, 2], [{0}, {0}], [2]), [[0], [2]]),
    "D": (Problem([2], [2], [{0}], [1, 1]), [[1, 1]]),
    "E": (Problem([2], [2], [{0, 1}], [2, 2]), [[2, 0]]),
}


def main() -> int:
    ok = True
    for target, (p, x) in WITNESSES.items():
        if not attainable(x, p):
            print("witness for %s is not attainable" % target)
            ok = False
            continue
        held = {k: f(x, p) for k, f in AXIOMS.items()}
        failed = sorted(k for k, v in held.items() if not v)
        satisfied = ",".join(sorted(k for k in AXIOMS if held[k])) or "none"
        print("witness for Axiom %s (B = %d):  satisfies %s,  fails %s"
              % (target, p.budget, satisfied, ",".join(failed) or "none"))
        if failed != [target]:
            print("    expected it to fail %s alone" % target)
            ok = False
    print()
    print("independence verified." if ok else "independence NOT verified.")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
