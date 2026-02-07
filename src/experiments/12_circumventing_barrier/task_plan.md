# Task Plan - Experiment 12 Hardening Pass

## Goal
Finalize Experiment 12 with maximal confidence on correctness, completeness, robustness, and novelty, while staying inside this experiment directory.

## Phases

1. Re-validate all existing outputs [completed]
- Python suite (`--quiet`, `--deep`)
- Lean build
- Non-ASCII hygiene

2. Audit mathematical consistency [completed]
- Cross-check Part VIII/IX formulas and constants
- Confirm external theorem/proposition numbering references

3. Harden numerical robustness [completed]
- Add scale-normalized residual metrics for deep checks
- Add multi-seed stress sweep beyond default deep run

4. Strengthen formalization envelope [completed]
- Add Lean statement-level algebraic support for rank-2 scaling (Proposition 6 core)
- Keep zero-axiom local Lean package

5. Final closure [completed]
- Full rerun of Python + Lean + hygiene
- Update progress/findings docs
- Produce final certainty/novelty report

6. Extend beyond two-level boundary [completed]
- Add and prove commuting multilevel rank-k theorem (Proposition 6B)
- Add matching numerics + deep stress checks
- Add Lean algebraic core for multilevel commuting non-constancy

7. Tighten Theorems 1/3/4 formal core [completed]
- Add operator-reduction lemmas for product-sector invariance and reduced-action equality (Theorem 1 core)
- Add coupled asymptotic crossing non-constancy lemma (Theorem 3 core)
- Add segment-2 rigidity map lemma (Theorem 4 core)

8. Close Proposition 6C Lean formalization gap [completed]
- Add a dedicated noncommuting multilevel trace no-go Lean module
- Integrate module into package imports and checks
- Re-run Lean + numerical closure suite

## Errors Encountered

| Error | Attempt | Resolution |
|-------|---------|------------|
| Deep rank-k residual instability from raw determinant magnitude | 1 | Switched to scale-normalized spectral residual in reduced matrix space |
| Deep rank-2 residual instability for large x branches | 1 | Switched to scale-normalized polynomial residual |
| Multi-seed rank-k false non-variation on near-zero eigenvalue branches | 1 | Filtered roots with numeric positive tolerance and relaxed deep spread threshold to machine-resolvable scale |
| Shell heredoc chained with `&&` produced syntax error | 1 | Re-ran as separate commands |
