# Experiments Index (Updated)

Summary of all research explorations, with final status.


## Main Contribution: Value of Information Analysis

**Status**: VALIDATED - Novel finding

### Summary
First quantitative characterization of the "value of A_1 knowledge" for AQO scheduling.

### Key Results
- Instance-independent schedules achieve 15-25% improvement over uniform
- Knowing A_1 provides additional 3-23% improvement (varies with system size)
- ~50% of total scheduling benefit achievable without calibration
- Theoretical local schedule underperforms simple "slow around s*" approach

### Files
- `FINAL_CONTRIBUTION.md` - Main writeup
- `CONTRIBUTION.md` - Detailed analysis
- `careful_verification.py` - Primary validation
- `robust_schedule_analysis.py` - Robust schedule testing
- `verify_robust_result.py` - Instance-independent schedule verification
- `scaling_check.py` - Scaling with system size


## Validated Background Results

### Gap Formula for H(r)
**Status**: VALIDATED (but not novel - implicit in paper)

Files: `refined_resonance_analysis.py`, `find_resonance_empirical.py`


### Imprecision-Fidelity Tradeoff
**Status**: VALIDATED

Files: `local_schedule_simulation.py`


## Explored but Non-Novel Directions

### Precision Gap Analysis
**Status**: Identified as open question (paper already acknowledges)

The complexity at precision 2^{-n/2} is genuinely unknown, but this is stated in the paper.

File: `precision_gap_analysis.md`


### Structured Tractability
**Status**: Correct but trivial - symmetric Hamiltonians have tractable A_1 but the problems themselves are trivial.

Files: `structured_tractability.md`, `verify_complete_graph.py`


### Spherically Symmetric Costs
**Status**: Formula correct but doesn't apply to real problems (MAX-CUT is NOT spherically symmetric).

Files: `planted_structure_analysis.md`, `verify_planted_A1.py`, `planted_maxcut_analysis.py`


## Failed Approaches

### Loschmidt Echo Calibration
**Status**: FAILED - Multi-level interference destroys signal

### QPE-Based Calibration
**Status**: NEGATIVE - Complexity worse than uncalibrated AQO

### Ensemble A_1 for Random Problems
**Status**: NEGATIVE - A_1 variance exceeds required precision for MAX-CUT


## File Manifest (Complete)

| File | Description | Status |
|------|-------------|--------|
| **Main Contribution** | | |
| `FINAL_CONTRIBUTION.md` | Main contribution writeup | CURRENT |
| `CONTRIBUTION.md` | Detailed value-of-info analysis | CURRENT |
| `careful_verification.py` | Primary validation code | Validated |
| `robust_schedule_analysis.py` | Robust schedule study | Validated |
| `verify_robust_result.py` | Instance-independent check | Validated |
| `scaling_check.py` | System size scaling | Validated |
| **Background** | | |
| `RESEARCH_STATUS.md` | Status of all directions | Reference |
| `MAIN_FINDING.md` | Early main finding (superseded) | Superseded |
| `HONEST_ASSESSMENT.md` | Critical self-review | Reference |
| `FINAL_SYNTHESIS.md` | Previous synthesis | Superseded |
| `precision_gap_analysis.md` | Complexity gap analysis | Reference |
| **Tractability** | | |
| `structured_tractability.md` | Symmetric Hamiltonians | Validated (trivial) |
| `verify_complete_graph.py` | Complete graph A_1 | Validated |
| `planted_structure_analysis.md` | Planted problem theory | Negative |
| `verify_planted_A1.py` | Spherical cost validation | Validated |
| `planted_maxcut_analysis.py` | MAX-CUT analysis | Negative result |
| `self_critique_structured.md` | Self-critique | Reference |
| **Failed Approaches** | | |
| `local_schedule_simulation.py` | Imprecision testing | Validated |
| `loschmidt_dynamics.py` | Echo analysis | Shows failure |
| `qpe_calibration.md` | QPE approach | Negative |
| **Legacy** | | |
| `research_proposals.md` | Initial proposals | Reference |
| `INDEX.md` | Original index | Superseded |


## Open Questions Remaining

1. Does the value-of-information scaling continue at n > 12?
2. What about specific NP-hard problems (not random instances)?
3. Can we prove bounds on instance-independent schedule performance?
4. Why does the theoretical local schedule underperform?


## Potential Publication

**Title**: "Quantifying the Value of Calibration in Adiabatic Quantum Optimization"

**Thesis**: While exact A_1 estimation is NP-hard, numerical experiments show that ~50% of the scheduling benefit is achievable with instance-independent schedules, and rough A_1 estimates capture most of the remaining benefit.

**Novelty**: First quantitative "value of information" analysis for AQO calibration.

**Strength**: Novel angle, honest characterization, practical implications.

**Weakness**: Limited scale (n ≤ 12), random instances only, no rigorous bounds.
