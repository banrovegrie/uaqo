# Experiments

New ideas, explorations, and rough drafts extending the published work on adiabatic quantum optimization.


## Purpose

This directory is a staging area for content that is not yet ready for `src/chapters/`. Ideas are developed here before they mature into formal thesis sections.

The thesis is built on a single published paper (`paper/`). This directory is where we go beyond it. The paper establishes the foundation. The experiments here aim to extend that foundation with new contributions: generalizations, alternative approaches, open questions pursued further. A thesis that merely explains existing work is a report. A thesis that advances it is a contribution.


## Structure

Each experiment lives in a numbered directory `0x_name/` with standardized contents:

```
0x_experiment_name/
├── main.md              # Problem statement, conjectures, results
├── lib/                 # Supporting code (Python, numerical experiments)
│   ├── *.py
│   └── requirements.txt
├── lean/                # Formal proofs (Lean 4 + Mathlib)
│   ├── lakefile.lean
│   ├── lean-toolchain
│   └── ExperimentName/
│       ├── Basic.lean
│       └── *.lean
└── notes/               # Working notes, literature, scratchpad
    └── *.md
```

Not all experiments need all components. Use what is appropriate:
- `main.md` is always required
- `lib/` for numerical validation or computational experiments
- `lean/` for formal verification of theorems
- `notes/` for literature surveys, failed attempts, working notes


## Guidelines

Work here is expected to be rough. The goal is exploration rather than polish. However:
- Notation should align with the published paper to ease later integration.
- Claims should be clearly labeled as CONJECTURE, THEOREM (with proof), or EMPIRICAL.
- Failed attempts are valuable and should be documented honestly.
- Literature surveys should verify novelty before deep investment.

When an experiment matures sufficiently, extract the relevant content into the appropriate chapter file and archive the experiment with a note.


## Current Experiments

| ID | Name | Status | Description |
|----|------|--------|-------------|
| 01 | precision_gap | Exploratory | Complexity at intermediate precision |
| 02 | robust_schedules | Exploratory | Numerical experiments on robust schedules |
| 03 | structured_tractability | Exploratory | When is A_1 tractable? |
| 04 | separation_theorem | Complete | Gap-uninformed separation theorem (Lean formalized) |
| 05 | adaptive_schedules | Proposed | Fundamental limits of adaptive probing |
| 06 | measure_condition | Proposed | When does Guo-An break? |
| 07 | partial_information | Proposed | Interpolation between informed/uninformed |
| 08 | structured_tractability | Proposed | When is A_1 easy? (refined from 03) |
| 09 | guo_an_gap | Proposed | Circularity in Guo-An's assumptions |
| 10 | information_theoretic | Proposed | Limits beyond adiabatic framework |


## Research Thread Template

When starting a new experiment, create `main.md` with:

```markdown
# [Experiment Name]

## Problem Statement
What question are we trying to answer?

## Why Novel
- What existing work is related?
- What gap does this fill?

## Conjectures
State precise mathematical claims.

## Approach
How do we plan to prove/disprove the conjectures?

## Results
- CONJECTURE: [unproven claim]
- THEOREM: [proven claim with proof sketch]
- EMPIRICAL: [numerical observation]

## Status
Current state of the experiment.

## References
Related papers and prior work.
```


## Lifecycle

1. **Proposed**: Idea identified, main.md created with problem statement
2. **Exploratory**: Actively investigating, may have partial results
3. **Complete**: Main results proven/validated, ready for thesis integration
4. **Archived**: Moved to archive/ (either succeeded and integrated, or documented failure)


## References

These papers form the basis for all experiments:

1. Original paper (`paper/`): A_1 NP-hard, optimal AQO runtime O(2^{n/2})
2. Guo-An 2025 (`citations/`): Power-law schedules, measure condition, p=3/2 optimality
3. Other relevant papers (`references/`) that our original paper refers to
