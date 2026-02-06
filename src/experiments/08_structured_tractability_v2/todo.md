# Experiment 08: Structured Tractability (v2) — `todo.md`

Purpose: maintain a single consolidated place for open threads, partial results, and
next actions while the experiment is evolving.


## Plans

### A. Partition-function route (turn “spectral complexity” into theorems)

**A0. Identity hygiene**
- [x] Add an “assumptions + interchange justification” note for the Laplace identity
      (when swapping sum/integral is valid).
- [x] Add a corollary: if \(Z(\beta)\) is efficiently computable/approximable on a
      grid, then \(A_1\) is efficiently approximable (state the model precisely).

**A1. Approximation theorem (core publishable lemma)**
- [x] Pick approximation model: additive \(\eta\) vs relative error; oracle access to
      \(Z(\cdot)\) vs explicit algorithm for \(Z(\cdot)\); define input size.
- [x] Prove a deterministic quadrature bound for
      \(\frac{1}{N}\int_0^1 (Z(t)-d_0)/t\,dt\) (integer-spectrum case).
- [x] Prove an analogous bound for the Laplace form
      \(\frac{1}{N}\int_0^\infty (Z(\beta)-d_0)\,d\beta\) with truncation at
      \(\beta_{\max}\) and tail control.
- [ ] Make error parameters explicit (energy normalization, minimum excited energy,
      mass near the ground, etc.).

**A2. Structured-family positive theorem**
- [x] Choose 1–2 families where \(Z\) is tractable and derive a polynomial-time
      algorithm for approximating \(A_1\) (to a specified precision regime).
- [ ] Choose a *second* family where \(Z\) is nontrivially approximable (e.g. a known
      FPRAS regime for a spin system / matching polynomial) and write a clean corollary.
- [x] Write as a theorem + proof, not just an observation.

**A3. Structured-family negative theorem**
- [ ] Choose 1–2 families where approximating \(Z\) is hard in a regime that implies
      hardness for approximating \(A_1\).
- [ ] Ensure this is not a restatement of the paper’s interpolation reduction.


### B. No-go theorem for “natural NP-hard with easy \(A_1\)” (high risk/high reward)

**B0. Make the statement precise first**
- [ ] Fix input model: diagonal \(k\)-local Hamiltonians, bounded weights, bit
      complexity, and what the input/oracle access is.
- [ ] Fix approximation: additive precision \(\eta(n)\) (candidates:
      \(\eta=2^{-n/2}\) or \(\eta=1/\mathrm{poly}(n)\)).
- [ ] Write a conjecture/theorem template: “If \(A_1\) is polytime computable for all
      instances in family \(\mathcal{F}\), then …”.

**B1. Attempt reductions not relying on exponentially accurate interpolation**
- [ ] Try decision-to-\(A_1\) “signal amplification” producing a robust \(\Theta(1)\)
      separation in \(A_1\) at inverse-poly precision.
- [ ] Try promise reductions (satisfiable vs far-from-satisfiable) so that \(E_0=0\)
      and the signal is stable.

**B2. If it fails**
- [ ] Document the obstruction crisply (can still be publishable if it reveals a
      genuine barrier and motivates Target A/C).


### C. Precision-aware story (bridge to Chapter 9 + Experiment 13)

**C0. Map precisions to “what AQO needs”**
- [ ] Extract from the paper: the required \(\delta_{A_1}\) scale for schedule
      correctness; restate it in this experiment’s notation.
- [ ] Decide which precision regimes are worth targeting for “structured
      tractability” results.

**C1. Connect the structured-family theorem(s) to algorithmic precision**
- [ ] For the chosen structured family, determine whether we can compute/estimate
      \(A_1\) to \(\eta=2^{-n/2}\) (or the correct derived scale) in polytime /
      quasi-poly / etc.
- [ ] If only constant-factor or inverse-poly additive error is feasible, determine
      whether that is meaningful for near-optimal schedules.

**C2. Integration**
- [x] Draft a “Chapter 9 insertion outline”: where 08 fits, and which theorems from
      A/B/C become section-level content.


### D. Structured family selection (choose a motivating class)

Selection criteria:
- Natural/recognizable for quantum optimization or classical complexity.
- Has a nontrivial partition-function story (tractable or provably hard).
- Lets us say something new about \(A_1\) beyond “counting is hard”.

Candidates:
- [ ] **Bounded treewidth CSPs / factor graphs**: exact dynamic programming for
      partition functions \(\Rightarrow\) exact/approx \(A_1\).
- [ ] **Ferromagnetic Ising / monotone systems**: known FPRAS regimes for partition
      functions in some parameter ranges.
- [ ] **XOR-SAT / linear codes**: counting is in P \(\Rightarrow\) exact \(Z(t)\);
      check if it yields a clean, nontrivial \(A_1\) theorem.
- [ ] **Horn-SAT / monotone CNF**: possible clean theorems in restricted regimes.
- [ ] **Submodular energies / cut functions**: if \(Z\) or related transforms are
      tractable, could yield a strong positive theorem.

Immediate action:
- [ ] Choose the “main family” and write a 1-page mini-brief: input model, known
      \(Z\) facts, target precision, likely theorem statement.


### E. Paper-grade checklist (what “done” looks like)

- [x] 1–2 main theorems (new) + 2–4 supporting lemmas.
- [x] Clear model definition (input encoding + approximation notion).
- [x] At least one positive structured-family theorem.
- [x] At least one negative/boundary theorem OR a sharp barrier lemma not already in
      the original paper.
- [x] Small computational appendix: scripts validating toy cases / identities.
- [x] “Novelty positioning” paragraph: explicitly state what is new vs the original
      paper and Guo–An 2025.


## Progress

- 2026-02-06: added partition-function identities in `proof.md`; consolidated the
  running plan/progress here; hardened CSP hardness proof to satisfiable-only
  reduction; fixed `lib/verify_a1.py` vacuity print for small \(n\); created this
  `todo.md`.
- 2026-02-06: added Proposition 8 (bounded treewidth / variable elimination route) and
  a correctness-checked demo in `lib/variable_elimination_a1.py`; removed redundant
  `notes/roadmap.md`.
- 2026-02-06: added Proposition 9 (Monte Carlo additive approximation when \(E_0\) is
  known) and a demo in `lib/estimate_a1_sampling.py`.
- 2026-02-06: added Proposition 10 (additive $A_1$ approximation from $Z(t)$ without
  computing $d_0$) as a bridge from partition-function algorithms to $A_1$.
- 2026-02-06: added Proposition 11 (Laplace-side anchored proxy without $d_0$) and
  Proposition 12 (oracle reduction $Z$-approx $\Rightarrow$ additive $A_1$); added
  numerical sanity checks for the bounds in `lib/verify_a1.py` and a Laplace-side
  quadrature demo in `lib/approx_a1_from_laplace_partition_function.py`.


## Findings

### Solid (already correct)

- Counterexamples: \(\Delta\) and \(d_0=1\) do not determine \(A_1\).
- Optimization hardness and \(A_1\)-hardness are independent (counting vs decision).
- Sufficient condition: poly levels + efficiently computable \((E_k,d_k)\)
  \(\Rightarrow\) polytime \(A_1\).
- CSP clause-violation Hamiltonians inherit \#P-hardness for computing \(A_1\).
- Structural lemma: \(A_1\) can be expressed as a transform of the partition function
  \(Z\), connecting tractability/hardness of \(A_1\) to tractability/hardness of \(Z\).
- Additive \(A_1\) approximation can avoid computing \(d_0\) via anchoring at
  \(Z(\varepsilon)\) (ordinary) or \(Z(B)\) (Laplace), with explicit truncation bounds.

### Missing (needed for novelty)

- A nontrivial **positive** tractability theorem for a natural broad family where the
  result is not “degeneracies are given”.
- A nontrivial **necessary/boundary** theorem under explicit structural hypotheses.
- A clean, precision-aware bridge to the algorithmic precision regime relevant for
  Chapter 9 (and Experiment 13).

### Chapter 9 insertion outline (draft)

- **Motivation:** predicting the avoided crossing requires $A_1$ to precision
  $O(\delta_s)$, which can be exponentially small.
- **Key structural lemma:** $A_1$ as a partition-function transform (Laplace + ordinary
  generating function).
- **Positive structure:** bounded treewidth gives exact $Z(t)$ coefficients and exact
  $A_1$ (Prop 8); more generally, approximate $Z$ over a temperature window implies
  additive $A_1$ (Props 10–12).
- **Precision-aware message:** coarse $A_1$ is often “moderate temperature”, but the
  schedule-relevant regime $\eta\approx 2^{-n/2}$ is “low temperature”, aligning with
  the paper’s information barrier.
