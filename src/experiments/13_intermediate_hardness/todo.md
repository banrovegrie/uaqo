# Experiment 13: Intermediate Hardness -- `todo.md`

Purpose: maintain a single consolidated place for open threads, partial results, and
next actions while the experiment is evolving.


## Plans

### A. Precision landscape (complexity transitions across precisions)

**A0. Map the full precision-complexity diagram**
- [ ] Classify complexity at each precision regime:
      - \(\varepsilon = \Theta(1)\): trivial (output 0).
      - \(\varepsilon = 1/\mathrm{poly}(n)\): NP-hard (paper Thm 2).
        Quantum \(O(\mathrm{poly}(n))\), classical \(\Omega(\mathrm{poly}(n))\).
      - \(\varepsilon = 2^{-cn}\) for \(c < 1/2\): intermediate.
        Quantum \(O(2^{cn})\), classical \(\Omega(2^{2cn})\).
      - \(\varepsilon = 2^{-n/2}\): algorithmically relevant threshold.
        Quantum \(\Theta(2^{n/2})\), classical \(\Theta(2^n)\).
      - \(\varepsilon = 2^{-cn}\) for \(c > 1/2\): \#P-hard territory.
      - \(\varepsilon = 2^{-\mathrm{poly}(n)}\): exact degeneracy extraction.
- [ ] Identify the structural boundary: \(\varepsilon = 2^{-n/2}\) is where polynomial
      interpolation breaks (Theorem 6). Is there a phase transition in proof technique,
      or is it smooth?

**A1. Write as a proposition**
- [ ] State the precision landscape as a structured proposition with cited sources.
- [ ] Add a summary table to proof.md.
- [ ] Add numerical verification: compute quantum/classical bounds at multiple
      \(\varepsilon\) values and verify scaling.


### B. Structured instance investigation (connection to Exp 08)

**B0. Check Theorem 7 against structural constraints**
- [ ] Read Exp 08 Props 8--13: identify the structural constraints (bounded treewidth,
      ferromagnetic Ising with consistent fields).
- [ ] Does Theorem 7's worst-case construction ("concentrate degeneracy in first two
      levels") violate these constraints? Specifically: can a two-level spectrum arise
      from a bounded-treewidth CSP or ferromagnetic Ising model?
- [ ] If yes: Theorem 7 applies even for structured families (worst-case still hard).
- [ ] If no: structured families may have easier worst-case instances.

**B1. Determine structured-family complexity at \(2^{-n/2}\)**
- [ ] For bounded-treewidth CSPs: if \(A_1\) is exactly computable in poly time
      (Exp 08, Prop 8), then estimation at \(2^{-n/2}\) is also poly time.
      State this as a corollary.
- [ ] For ferromagnetic Ising: if \(A_1\) is approximable to additive \(\eta\) in
      randomized poly time (Exp 08, Prop 13), determine whether \(\eta\) can reach
      \(2^{-n/2}\). If not, what is the best achievable precision?
- [ ] Write as a proposition connecting Exps 08 and 13.


### C. Promise class characterization (speculative, low priority)

**C0. Identify candidate classes**
- [ ] \(A_1\) estimation at precision \(\varepsilon\) is in
      \(\mathrm{BQTIME}(1/\varepsilon \cdot \mathrm{poly}(n))\).
      At \(\varepsilon = 2^{-n/2}\): \(\mathrm{BQTIME}(2^{n/2} \cdot \mathrm{poly}(n))\).
- [ ] Is there a natural promise class capturing this intermediate regime?
      Candidates: \(\mathrm{PromiseSBP}\), quantum approximate counting class.
- [ ] If no clean characterization: write a Remark documenting why standard classes
      don't fit (function problem, promise, intermediate precision).

**C1. Non-interpolation hardness (open question #3)**
- [ ] Can non-interpolation techniques establish hardness at \(2^{-n/2}\)?
      Theorem 6 rules out polynomial extrapolation but not all proof strategies.
- [ ] Candidates: information-theoretic reductions from counting problems,
      communication complexity lower bounds.
- [ ] If progress: state as a proposition. If not: document the barrier.


### D. Chapter 9 integration

**D0. Determine placement**
- [ ] Read Chapter 9 outline in `README.md`. Natural placement: bridge between
      the Ignorance Taxonomy and the model-separation capstone (Exp 10).
- [ ] Narrative: "The paper proves \(A_1\) is hard. At what precision? The
      algorithmically relevant \(2^{-n/2}\) exhibits a quadratic quantum-classical
      separation, quantifying the information cost of the adiabatic model."

**D1. Write insertion outline**
- [ ] Map proof.md theorems to Chapter 9:
      - Theorems 1, 6 (barrier analysis): one subsection on why \#P-hardness
        doesn't extend
      - Theorems 2--4 (tight bounds): one subsection on quantum-classical separation
      - Theorem 5 (ETH): one remark on computational model
      - Theorem 7 (structure irrelevance): one remark
      - Gap A (precision landscape): summary table
      - Gap B (structured instances): connection to tractability
- [ ] Note which open questions carry into the Conclusion.


### E. Paper-grade checklist

- [x] Tight query complexity bounds (Theorems 2--4).
- [x] Computational complexity under ETH (Theorem 5).
- [x] Generic proof barrier (Theorems 1, 6).
- [x] Structure irrelevance (Theorem 7).
- [x] Comprehensive numerical verification (two scripts, 11+ tests).
- [x] Novelty positioning paragraph.
- [ ] Precision landscape (complexity vs precision map).
- [ ] Structured instance investigation (connection to Exp 08).
- [ ] Chapter 9 insertion outline.


## Progress

- 2026-02-06: Theorems 1--7 proved in `proof.md`. Two numerical verification
  scripts (`verify.py`, `deep_verify.py`) all tests pass. Addresses paper's
  explicit open problem (Discussion p.983). Created `todo.md`.


## Findings

### Solid (already correct)

- Polynomial interpolation technique fails at \(\varepsilon = 2^{-n/2}\): error
  amplification exceeds 1/2 and rounding fails (Theorem 1).
- Quantum estimation achieves \(\Theta(2^{n/2})\) queries via amplitude estimation
  + minimum finding (Theorems 2, 4). Both bounds tight.
- Classical estimation requires \(\Theta(2^n)\) queries via Le Cam / KL divergence
  (Theorem 3). Tight with brute force.
- Generic barrier: ANY polynomial extrapolation of degree \(d\) amplifies by
  \(\geq 2^{d-1}\) (Theorem 6). Not specific to paper's construction.
- \(M = 2\) instances are worst-case: sum-of-reciprocals structure of \(A_1\)
  provides no advantage (Theorem 7).
- Under ETH: quadratic quantum speedup holds in computational model (Theorem 5).

### Missing (needed for novelty)

- A precision landscape mapping the full complexity-vs-precision diagram.
- Investigation of whether structured families (Exp 08) escape Theorem 7's
  worst-case hardness at precision \(2^{-n/2}\).
- Chapter 9 insertion outline.

### Chapter 9 insertion outline (draft)

- **Placement:** bridge between Ignorance Taxonomy and model-separation capstone.
- **Narrative:** the paper proves \(A_1\) is hard at two extreme precisions. At the
  algorithmically relevant \(2^{-n/2}\), the complexity is neither NP-hard nor
  \#P-hard but exhibits a clean quantum-classical separation.
- **Content:** (1) interpolation barrier and why \#P techniques fail; (2) tight
  quantum-classical bounds; (3) precision landscape table; (4) connection to
  structured tractability; (5) implication for AQO practicality.
- **Deferred:** promise class characterization, non-interpolation hardness (to
  Conclusion/future work).
