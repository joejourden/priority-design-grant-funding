# Priority Design for Grant-Funding Policies: code

Code accompanying *Priority Design for Grant-Funding Policies* by Joe Jourden.
There are two scripts. The main one, `cstar_search.py`, supports Appendix A.4
("Strong Feasible Floors"): it searches for a floor problem in which **no**
allocation satisfies non-wastefulness (Axiom A), respecting priorities (Axiom B)
and strong feasible floors (Axiom C\*) at the same time.

No such problem has been found. The appendix reports this as a negative
computational result, not a proof.

The code in this repository was written with the assistance of Claude (Anthropic),
a generative AI model, and reviewed by the author; the paper's declaration of
generative AI use describes this.

## Contents and requirements

| File | What it is for |
| --- | --- |
| `cstar_search.py` | The search reported in Appendix A.4. Its `validate` command also reproduces the example in the proof of Proposition 1. |
| `earmark_independence.py` | Checks the four allocations in the proof of Proposition 2. |
| `sweep_results.log` | Record of the run behind the figures in Appendix A.4. |

Both scripts need Python 3.8 or later and use only the standard library.
`python3 earmark_independence.py` and `python3 cstar_search.py validate` each
finish in seconds; the full sweep takes about a day on four cores (see
below).

## What the search enumerates

For a fixed $(|I|, |\mathscr{C}|, \mathcal{B})$, every floor problem with
integral data:

- cost bounds $1 \le \underline{b}_i \le \overline{b}_i \le \mathcal{B}$
- eligibility $\rho(i)$ over all subsets of $\mathscr{C}$
- floors $q_c \ge 1$ with $\sum_c q_c \le \mathcal{B}$

Grants are indexed by merit position, and cost bounds and eligibility are
assigned to each position independently; in the code, index 0 is the paper's
grant 1, the highest-merit grant. The axioms refer to grants
only through their data and the merit order, so every problem of these dimensions
is a relabeling of exactly one problem in this class: fixing the order is without
loss, and all counts below are of problems up to relabeling of grants (a count over
labeled rankings would be $|I|!$ times larger with no new problems).

For each problem the search then enumerates every integral allocation
$\xi_i \in \{0\} \cup [\underline{b}_i, \overline{b}_i]$ within budget. A problem
is flagged only if no allocation passes all three axiom tests.

Partial funding is in the space on both sides. Grants are not all-or-nothing: a
grant with bounds $[2, 9]$ takes every integral level $0, 2, 3, \ldots$ up to its maximum cost or the budget. Over all 2,985,984 problems at $(3,1,8)$, 98.9% have at
least one grant with $\underline{b}_i < \overline{b}_i$ — matching the closed
form $1 - \left(\frac{2}{\mathcal{B}+1}\right)^{|I|}$ — and 51% of the allocations that satisfy all three axioms fund some grant
strictly between zero and its maximum cost (49% of problems have at least one
such allocation). The result is
not an artifact of a full-funding special case.

The floor-sum restriction matters. Dropping $\sum_c q_c \le \mathcal{B}$ produces
millions of apparent counterexamples, none of which are floor problems in the
sense of Section 4.2.

## How the axioms are tested

Each axiom is tested directly against its statement in Sections 4.3 and 4.4:

- **Axiom A**: with unspent budget $R = s(\xi)$, an unfunded grant needs
  $\underline{b}_i > R$ and a grant funded short of its maximum cost needs
  $R = 0$.
- **Axiom B**: an unfunded grant's claim cannot be covered by funding held by
  grants below it in $\succ_\rho$ together with the unspent budget (provided
  at least one such grant holds funds), and a grant funded at or above its minimum cost but short of its maximum
  cost leaves nothing funded below it in $\succ_\rho$.
- **Axiom C\***: at every category with a positive shortfall $d_c(\xi)$, every grant in $A_c(\xi)$ (the grants eligible for $c$ that are not
  fully funded) is unfunded and has a minimum cost above $d_c(\xi)$.

Axioms C and C\* differ only in a quantifier — C constrains the highest-merit
member of $A_c(\xi)$, C\* every member — so `floors_satisfied` implements both,
selected by `key`. `validate` compares them on the example in the proof of Proposition 1, where
the difference is visible: the same allocation satisfies both before grant 4
arrives, and only C afterwards.

## Configurations searched

| $(\|I\|, \|\mathscr{C}\|, \mathcal{B})$ | problems | | $(\|I\|, \|\mathscr{C}\|, \mathcal{B})$ | problems |
| --- | --- | --- | --- | --- |
| (2, 1, 10) | 121,000 | | (4, 2, 6) | 746,807,040 |
| (2, 2, 9) | 1,166,400 | | (4, 3, 5) | 2,073,600,000 |
| (2, 3, 8) | 4,644,864 | | (5, 1, 5) | 121,500,000 |
| (3, 1, 8) | 2,985,984 | | (5, 2, 4) | 614,400,000 |
| (3, 2, 8) | 83,607,552 | | (5, 3, 3) | 254,803,968 |
| (3, 3, 7) | 393,379,840 | | (6, 1, 4) | 256,000,000 |
| (4, 1, 7) | 68,841,472 | | (6, 2, 3) | 573,308,928 |

5,195,167,048 problems in total (up to relabeling of grants), plus three sets of four million random draws
with $|I| \le 9$, $|\mathscr{C}| \le 4$ and $\mathcal{B} \le 40$.

The draws are not redundant with the sweep. About 93% of drawn shapes lie
outside every configuration above — nine grants, four categories, budget forty —
where enumeration is hopeless, so they are the only probe of whether the result
survives at scale. What they buy is weaker than the sweep, though: a density
bound, not certainty. Twelve million draws with no hit put the density of
counterexamples below roughly 1 in 4 million at 95% confidence.

For a drawn problem the allocations are searched depth first (`find_witness`)
rather than listed and filtered, which at budget forty would mean around $10^{14}$
tuples. Grants are funded one at a time in merit order, a branch is abandoned only
once its partial allocation exceeds the budget, each completed allocation goes
through the same three axiom tests as the sweep, and the search stops at the
first allocation that passes. The pruning only discards vectors that are not
allocations, so a draw is flagged exactly when no integral allocation satisfies
A, B and C\* — the same test as the sweep, applied to sampled problems.

Floors are drawn uniformly over $\{q : q_c \ge 1,\ \sum_c q_c \le \mathcal{B}\}$
via the bijection with $m$-subsets of $\{1, \ldots, \mathcal{B}\}$. Drawing each
$q_c$ in turn from the remaining budget instead puts two thirds of the floor
mass on the first category and leaves 40% of draws with a category carrying no
floor at all — so the multi-category reach would be illusory, and that is where
a C\* counterexample is most likely to live.

## Results

No problem was flagged, in any of the fourteen configurations or in any of the
twelve million random draws. `sweep_results.log` records the complete sweep
under Axiom B as stated in the paper: one line per configuration and per set of
random draws, with the number of problems, the number flagged and the elapsed
time. The figures quoted in Appendix A.4 come from it.

## Running the sweep

```sh
cd code
python3 cstar_search.py validate            # reproduce Proposition 1 first
python3 cstar_search.py sweep --jobs 4      # the whole search
```

Run it from this directory: `sweep_results.log` is written to the working
directory. `--jobs` may go on either side of the subcommand. On macOS, prefix
with `caffeinate -i` so the machine does not sleep partway through, and add
`nohup ... &` if you want it to outlive the terminal window:

```sh
nohup caffeinate -i python3 cstar_search.py sweep --jobs 4 > sweep_console.log 2>&1 &
tail -f sweep_results.log
```

`sweep` runs all fourteen configurations and then three sets of four million
random draws. On four cores it takes about a day: the times recorded in
`sweep_results.log` sum to 22 hours, about 20 of them on the configurations
(the random draws run in a single process). It prints each
configuration as it finishes and appends the line to `sweep_results.log`,
skipping anything already recorded there, so an interrupted run can simply be
restarted.

The number of problems in a configuration is exact and closed-form. A grant
type is a pair $1 \le \underline{b} \le \overline{b} \le \mathcal{B}$ together
with a subset of the categories, the $|I|$ grants are chosen independently, and
the floor vectors are the $q$ with $\sum_c q_c \le \mathcal{B}$, of which there
are $\left({\mathcal{B} \atop |\mathscr{C}|}\right)$:

$$N = \left(\tfrac{\mathcal{B}(\mathcal{B}+1)}{2} \cdot 2^{|\mathscr{C}|}\right)^{|I|} \left({\mathcal{B} \atop |\mathscr{C}|}\right).$$

Cost is driven by $|I|$ and $\mathcal{B}$: each extra grant multiplies the count
by the number of grant types, and raising the budget grows that number as
$\mathcal{B}^2$. That is why the configuration list pairs more grants with
smaller budgets, and why the list stops where it does.

### The one optimization in the code

A configuration sweeps the same grant configurations against every floor
vector. Axioms A and B never mention the floors, so they are checked once per
grant configuration rather than once per floor vector. What survives is reduced
to a bound: at a category, writing $S_c$ for the funding its eligible grants hold and $A_c(\xi)$ for
those not fully funded, the floor axiom holds exactly when $q_c < U_c$, where
$U_c = S_c + \min_{i} \underline b_i$ over the targets if every target is
unfunded, $S_c + 1$ otherwise, and $\infty$ when $A_c(\xi)$ is empty. The
targets are the members of $A_c(\xi)$ the axiom constrains: all of them for
C\*, the highest-merit one for C. Each
floor vector is then a few integer comparisons.

Without it, the A and B tests would be repeated for every floor vector,
multiplying their cost by $\left({\mathcal{B} \atop |\mathscr{C}|}\right)$. `--reference` on a single configuration asserts the reduced path against
`find_witness` on every problem it sweeps, and is the check that it is faithful.

## Why integer problems and integer witnesses suffice

Searching integer problems for *integer* allocations is enough to establish
existence over the class, and the two halves of that claim work differently.

**Integer witnesses need no defence.** Restricting the allocation space can only
make a counterexample *easier* to find: if some problem had no integral witness,
the search would flag it, and only then would the fractional question arise. It
never does. So every problem searched is settled affirmatively by an allocation
the search actually exhibits, and no argument about fractional allocations is
needed anywhere.

**Integer data covers the commensurable case.** The axioms are invariant to a
common rescaling of $\mathcal{B}$, the cost bounds and the floors. So a problem
whose data are rational, after clearing denominators, *is* one of the integer
problems in the class — provided its rescaled budget falls within the bound
searched. Clearing denominators inflates $\mathcal{B}$, which is the real
limitation: a problem with fine-grained data rescales to a budget past anything
enumerable. Problems with irrationally-related data are outside the class
altogether, and no finite search reaches them.

**This is still not a proof.** What it establishes is that non-existence, if it
occurs at all, occurs nowhere near the scale at which C\*'s other defects
appear — the independence failure of Proposition 1 needs only four grants and a
single category.

## Why the floors-first argument doesn't settle the question

$C^f_\Delta$ advances an unsatisfied category by funding its highest-merit
not-fully-funded eligible grant, and doing so never creates a priority
violation. Under C\* the grant whose funding closes the deficit is the *cheapest*
eligible one, and funding it ahead of a higher-priority grant in the same
category is precisely what Axiom B forbids. Proposition 1 resolves that tension by defunding grant 1 altogether.

## A separate script: independence of the earmark axioms

`earmark_independence.py` is unrelated to the search above and needs no
arguments. It codes Axioms A, B, D and E for earmark problems directly from their statements in Sections 4.3 and 4.6 and checks the four
allocations used in the proof of Proposition 2, which shows that the axioms are
independent: each satisfies three of them and
fails the fourth. Axiom A is coded with its comparison restricted to
eligibility-compliant matrices, as the axiom is stated.

    python3 earmark_independence.py

It prints one line per witness and exits non-zero if any of them fails to
behave as the proof claims.

## Citation

Jourden, J. (2026). *Code for: Priority Design for Grant-Funding Policies*
[Dataset]. Mendeley Data, Version 1. https://doi.org/10.17632/w3c4wtgtdc.1

## License

MIT; see `LICENSE`.
