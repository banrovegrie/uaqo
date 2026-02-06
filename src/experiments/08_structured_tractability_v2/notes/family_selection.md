# Experiment 08 Family Selection Memo

## Decision

Main family selected: **ferromagnetic Ising with consistent external fields**.

Form used in this experiment:
\[
C(\sigma)=\sum_{(i,j)\in E} J_{ij}\frac{1-\sigma_i\sigma_j}{2}
          +\sum_{i=1}^n h_i\frac{1-\sigma_i}{2},
\]
with $J_{ij},h_i\in\mathbb{Z}_{\ge 0}$ after an optional global spin flip.

This is natural for AQO (diagonal 2-local Hamiltonian), standard in counting
complexity, and has a nontrivial partition-function approximation story.

## Why This Family

Selection criteria from `todo.md`:

1. Natural/recognizable in quantum optimization and classical complexity.
2. Nontrivial partition-function tractability story.
3. Lets us prove something beyond "counting is hard."

Ferromagnetic Ising with consistent fields satisfies all three:

- It is a canonical spin system and directly maps to diagonal AQO instances.
- Partition-function approximation is known to be tractable in this monotone regime.
- The result is not exact counting; it is a **multiplicative-to-additive transfer**
  theorem: approximate $Z$ on a temperature window implies additive approximation of
  $A_1$ with explicit error drivers.

## Known Partition-Function Facts Used

- In this regime, multiplicative approximation of $Z(\beta)$ is available via
  classical randomized approximation algorithms (FPRAS-type guarantees).
- For our bridge, only the guarantee shape is needed:
  \[
  (1-\mu)Z(\beta)\le \widehat Z(\beta)\le (1+\mu)Z(\beta)
  \]
  on queried temperatures.

This plugs directly into Proposition 11 style anchored integration.

## Target Precision

Two precision regimes are relevant:

1. **Coarse/inverse-polynomial**: $\eta=1/\mathrm{poly}(n)$.
2. **Schedule-level**: $\eta\asymp 2^{-n/2}$ (from crossing-window precision).

The family is expected to give positive results for (1), while (2) exposes the
low-temperature precision barrier through required multiplicative accuracy in $Z$.

## Likely Theorem Statement (Implemented as Proposition 13)

Given:

- normalized energies in $[0,R]$,
- minimum excitation $\Delta_{\min}$,
- ground mass $\rho_0=d_0/N$,
- multiplicative approximation access to $Z(\beta)$ on $[0,B]$,

the anchored midpoint estimator satisfies:
\[
|A_1-\widehat A_1|
\le (1-\rho_0)e^{-B\Delta_{\min}}\!\left(B+\frac{1}{\Delta_{\min}}\right)
   + 2\mu B + \frac{RB^2}{2K}.
\]

Consequences:

- inverse-poly additive error in randomized polynomial time when parameters are
  inverse-polynomially bounded;
- schedule-level precision requires exponentially small $\mu$, so this route is not
  polynomial at $\eta\asymp 2^{-n/2}$.

## Why Not the Other Candidates as Main Family

- **Bounded treewidth CSPs:** already used for exact tractability (Prop 8); not the
  strongest "nontrivial approximation" story.
- **XOR-SAT / linear codes:** very clean but mainly exact-algebraic tractability.
- **Horn-SAT / monotone CNF:** promising but less standard for a broad partition-function theorem.
- **Submodular/cut families:** strong potential, but requires additional setup not yet in this run.

These remain useful secondary families for follow-on work, especially for negative or
boundary results.
