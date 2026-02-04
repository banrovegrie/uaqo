# Findings: Formatting Compliance Audit

## Repository Overview
*To be populated after study*

## Check Criteria (from src/tests/check-format.md)

### 1. ASCII Only
- All characters must be in ASCII range (0-127)
- Common violations: curly quotes, em/en dashes, accented letters, math symbols, Greek letters

### 2. No Horizontal Rule Separators
- No `---`, `***`, or `___` as section separators
- Exception: YAML frontmatter at file start

### 3. Math Delimiters in Markdown
- Math expressions must use `$...$` (inline) or `$$...$$` (display)
- Exception: Simple variable names in prose context

### 4. LaTeX Basics
- Delimiter balance
- No bare `_` outside math mode
- No bare `<` or `>` outside math
- No double spaces
- No space before punctuation

## Files Inventory (51 files, excluding .lake/)

### experiments/archive/ (14 files)
- error_analysis_imprecise_A1.md
- FINAL_SYNTHESIS.md
- HONEST_ASSESSMENT.md
- INDEX_UPDATED.md
- INDEX.md
- loschmidt_echo_proofs.md
- non_adiabatic_oscillation.md
- numerical_framework.md
- qaoa_connection.md
- qpe_calibration.md
- quantum_calibration_theorem.md
- research_proposals.md
- RESEARCH_STATUS.md
- RIGOROUS_ASSESSMENT.md
- SUMMARY_novel_contributions.md

### experiments/02_robust_schedules/ (5 files)
- lean/README.md, main.md, proof.md
- notes/CONTRIBUTION.md, FINAL_CONTRIBUTION.md, MAIN_FINDING.md

### experiments/04_separation_theorem/ (14 files)
- main.md, proof.md
- lib/corrections.md, critical_assessment.md, key_references.md, literature_survey.md, shantanav_message.md
- notes/formal_proof.md, formal_proof_v2.md, gap_uninformed_optimality.md, gap_uninformed_theorem.md, main_theorem.md, separation_theorem.md, theoretical_separation.md

### experiments/05_adaptive_schedules/ (4 files)
- main.md, proof.md, notes/key_insight.md, notes/literature_survey.md

### experiments/06_measure_condition/ (2 files)
- main.md, proof.md

### experiments/07_partial_information/ (2 files)
- main.md, proof.md

### experiments/08_structured_tractability_v2/ (2 files)
- main.md, proof.md

### experiments/10_information_theoretic/ (2 files)
- main.md, proof.md

### Other (5 files)
- experiments/README.md
- lean/README.md
- tests/check-format.md, check-math.md, check-taste.md, README.md

## Issues Found

### Check 1: Non-ASCII Characters

Files with violations (need to wrap math in $..$ and replace Unicode):

| File | Line | Issue | Fix |
|------|------|-------|-----|
| archive/RIGOROUS_ASSESSMENT.md | 83, 94 | `≈` (approx) | `$\approx$` |
| archive/qpe_calibration.md | 8 | `≈`, `<` | `$\approx$`, `$<$` |
| archive/INDEX_UPDATED.md | 127 | `≤` | `$\leq$` |
| 04_separation_theorem/main.md | 75-83 | Box chars `├└│` | Use plain ASCII tree |
| 04_separation_theorem/notes/main_theorem.md | many | `Δ`, `∈`, `Ω`, `Θ` | Wrap in `$...$` |
| 04_separation_theorem/notes/theoretical_separation.md | many | `α`, `ε`, `Δ`, `∈`, `Ω`, `Θ`, `∫`, `⟩`, `⟨` | Wrap in `$...$` |
| 04_separation_theorem/notes/separation_theorem.md | many | `α`, `ε`, `Δ`, `Θ`, `Ω` | Wrap in `$...$` |

### Check 2: Horizontal Rule Separators
**PASS** - No `---`, `***`, or `___` separators found.

### Check 3: Math Delimiters
Many files have undelimited math expressions (detected via non-ASCII math symbols).
Will be fixed along with Check 1.

### Check 4: LaTeX Basics
To be checked after ASCII fixes.

## Fixes Applied

### All 11 Files Fixed
1. **archive/RIGOROUS_ASSESSMENT.md** - `approx` symbol
2. **archive/qpe_calibration.md** - `approx`, `<` symbols
3. **archive/INDEX_UPDATED.md** - `leq` symbol
4. **02_robust_schedules/notes/CONTRIBUTION.md** - `times`, `pm` symbols
5. **02_robust_schedules/notes/FINAL_CONTRIBUTION.md** - `times`, `pm` symbols
6. **04_separation_theorem/main.md** - box-drawing chars
7. **04_separation_theorem/notes/main_theorem.md** - Greek letters, math ops
8. **04_separation_theorem/notes/theoretical_separation.md** - Greek letters, integrals, bra-ket
9. **04_separation_theorem/notes/separation_theorem.md** - Greek letters, math ops
10. **04_separation_theorem/notes/gap_uninformed_optimality.md** - Greek, math ops
11. **04_separation_theorem/notes/gap_uninformed_theorem.md** - Greek, math ops

### Verification Status: COMPLETE
- All git diffs reviewed
- 240 insertions, 240 deletions (symmetric changes)
- Only formatting changed, content preserved
- Mathematical meaning intact
