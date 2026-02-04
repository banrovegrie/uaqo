# Task Plan: Master's Thesis Implementation

## Objective
Write a 10-chapter thesis on Unstructured Adiabatic Quantum Optimization based on arXiv:2411.05736 that is:

| Goal | Meaning in practice |
|---|---|
| Teachable | A reader can learn AQC/AQO from it without constant external lookup |
| Rigorous | Math and parameter dependence match the paper; no hidden assumptions |
| Coherent | One spine: model -> spectrum -> schedule -> information barrier -> responses |
| Honest | Clear about limitations, what is proved, and what is conjectural |

## Chapter Structure

| Ch | Title | Status |
|----|-------|--------|
| 1 | Introduction | Pending |
| 2 | Physics and Computation | Pending |
| 3 | Quantum Computation | Pending |
| 4 | Adiabatic Quantum Computation | Pending |
| 5 | Adiabatic Quantum Optimization | Pending |
| 6 | Spectral Analysis | Pending |
| 7 | The Optimal Schedule | Pending (Alapan's contribution) |
| 8 | Hardness of Optimality | Pending |
| 9 | Exploring the Hardness Barrier | Pending (Thesis extensions) |
| 10 | Conclusion | Pending |

## Spine (what keeps the thesis coherent)

| Part | Chapters | What the reader should walk away with |
|---|---|---|
| Framing | 1 | The paradox and why it matters; scope and ground rules |
| Foundations | 2-4 | Computation as physics; Grover baseline; adiabatic theorem -> algorithm |
| Core technical story | 5-7 | The unstructured AQO model; gap profile; optimal schedule runtime |
| Information barrier | 8-9 | Optimality needs hard-to-compute spectral information; what can be done instead |
| Closing | 10 | Synthesis and open problems |

## Phases

### Phase 0: Setup (COMPLETE)
- [x] Update main.tex with 10-chapter structure
- [x] Create chapter files 5-9
- [x] Update chapter file headers

### Phase 1: Foundations (Chapters 2, 3, 4)
- [ ] Chapter 2: Physics and Computation
- [ ] Chapter 3: Quantum Computation
- [ ] Chapter 4: Adiabatic Quantum Computation

### Phase 2: Core Technical (Chapters 5, 6, 7, 8)
- [ ] Chapter 5: Adiabatic Quantum Optimization
- [ ] Chapter 6: Spectral Analysis
- [ ] Chapter 7: The Optimal Schedule (Alapan's contribution)
- [ ] Chapter 8: Hardness of Optimality

### Phase 3: Extensions (Chapter 9)
- [ ] Section 9.1: Separation Theorem (experiment 04)
- [ ] Section 9.2: Robust Schedules (experiment 02)
- [ ] Section 9.3: Partial Information (experiment 07)
- [ ] Section 9.4: Adaptive Schedules (experiment 05)
- [ ] Section 9.5: Measure Condition (experiment 06)
- [ ] Section 9.6: Synthesis

### Phase 4: Bookends (Chapters 1, 10)
- [ ] Chapter 1: Introduction (write last, informed by content)
- [ ] Chapter 10: Conclusion

### Throughout: Lean Formalization
- [ ] Document axiom status (refer to src/lean/)
- [ ] Attempt combinatorial axiom reductions
- [ ] Update Lean README with design decisions

## Critical Sources

### Paper (truth for all math)
- paper/v3-quantum.tex

### Experiments (thesis extensions)
- src/experiments/02_robust_schedules/
- src/experiments/04_separation_theorem/
- src/experiments/05_adaptive_schedules/
- src/experiments/06_measure_condition/
- src/experiments/07_partial_information/

### Lean Formalization
- src/lean/UAQO/ (refer directly, not cached metrics)

### Quality Control
- src/tests/check-format.md
- src/tests/check-math.md
- src/tests/check-taste.md

## Writing Approach

Per chapter:
1. Draft from paper/experiment sources
2. Run check-math.md (notation consistency)
3. Run check-taste.md (no filler, scaffolding)
4. Run check-format.md (ASCII, LaTeX)
5. Iterate until all tests pass

## Decisions Log
| Decision | Rationale | Date |
|----------|-----------|------|
| 10 chapters | Comprehensive coverage of paper + extensions | 2026-02-04 |
| Write bookends last | Introduction and conclusion informed by content | 2026-02-04 |
| Reference src/lean/ directly | Avoid stale metrics in plan | 2026-02-04 |

## Current Status
**Phase 0 Complete** - Chapter structure set up. Ready for Phase 1.
