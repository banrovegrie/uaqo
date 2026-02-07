# Findings - Experiment 12 Hardening Pass

## Confirmed Results

- Proposition 6 (rank-2 obstruction) is now internally consistent for general fixed degeneracy `1 <= d0 < N`.
- Proposition 6A (rank-k two-level scaling law) is numerically robust under deep randomized tests.
- Proposition 6B (commuting multilevel extension) is proved and numerically verified.
- Proposition 6C (general noncommuting multilevel trace no-go) is proved and numerically verified.
- Circumvention landscape references are exact:
  - Exp 05 Theorem 1
  - Exp 10 Theorem 2
  - Exp 13 Theorem 2
  - Exp 08 Propositions 8, 9, 13

## Robustness Findings

- Raw determinant/polynomial residuals can be numerically ill-conditioned for tiny excited-support branches.
- Scale-normalized residuals stabilize deep randomized verification without changing the verified equation.
- Additional multi-seed sweeps (`1,2,3,11,19`) passed for both Proposition 6 and Proposition 6A deep tests.
- Expanded multi-seed sweeps (`1,2,3,4,5,11,13,17,19,23`) passed for both Proposition 6 and Proposition 6A deep tests.
- Additional 6B seed sweeps (`2,5,11,29,37`) passed for commuting multilevel deep verification.
- Additional 6C seed sweeps (`3,7,13,23,37`) passed for noncommuting multilevel trace no-go deep verification.
- Explicit branchwise closed-form identity checks `s=A1/(A1 + kappa*(N-d0)/N)` now pass in both standard and deep modes.

## Formalization Findings

- Local Lean package builds with zero axioms and zero sorry/admit.
- Theorem 5 core package now explicitly includes all component statements (1-4),
  not only selected consequences.
- Added operator-reduction core formalization for Theorems 1/3/4 (`OperatorCore134.lean`).
- Added Proposition 6C core formalization in `RankKMultilevelTraceNoGo.lean`.
- Current Lean scope is still below full Hilbert-space mechanization.
- Remaining full-mechanization frontier is explicit and documented.

## Novelty Assessment

- Novel negative extension beyond prior Theorems 1-5:
  - rank-2 obstruction generalized across fixed-degeneracy two-level families
  - rank-k two-level scaling obstruction (excited-support branches)
  - commuting multilevel rank-k no-go extension (Proposition 6B)
  - noncommuting multilevel root-set no-go via trace drift (Proposition 6C)
- Novel synthesis contribution:
  - explicit CAN/CANNOT circumvention landscape across experiments 05/08/10/13 and 12.
