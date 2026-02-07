# Circumventing the Barrier: Modified Hamiltonians and the A_1 Dependence

## Problem Statement

The paper proves that the optimal adiabatic schedule requires knowledge of $s^* = A_1 / (A_1 + 1)$, and that computing $A_1$ is NP-hard. The Discussion section explicitly poses the question: can we modify the adiabatic Hamiltonian (adding ancilla qubits, intermediate Hamiltonians) so that $s^*$ no longer depends on the problem spectrum?

**Central Question**: Can Hamiltonian modifications (ancillas, multi-segment paths, higher-rank initial projectors) eliminate the dependence of $s^*$ on $A_1(H_z)$?

**Answer**: No, within rank-one instance-independent design (Theorems 1-5). Higher-rank fixed projectors also fail on fixed-degeneracy two-level families (Propositions 6 and 6A), on a multilevel commuting-block class (Proposition 6B), and in general multilevel root-set invariance via trace no-go (Proposition 6C).


## Why Novel

The paper identifies this as the central open problem (Discussion, p.983):
> "expanding the dimension of the Hamiltonian (by adding qubits) and introducing intermediate Hamiltonians at various points in the adiabatic path. These strategies can potentially shift the position of the avoided crossing to a point independent of the spectrum of the problem Hamiltonian."

This experiment directly attacks the question. The result is negative: neither ancillas nor multi-segment paths can eliminate the $A_1$ dependence within the rank-one framework. The proof is constructive and identifies the precise mechanism (universality of the uniform superposition).

The same $A_1$ barrier applies to the non-adiabatic oscillation algorithm (forthcoming [Eduardo]), since it uses the same Hamiltonian family.


## Results

**Status**: COMPLETE

### Theorem 1 (Product State Invariance)
For any product initial state $|\Psi\rangle = |\psi_0\rangle \otimes |\phi\rangle$ and uncoupled final Hamiltonian $H_z \otimes I_{2^m}$, the eigenvalue branches participating in the avoided crossing are identical to the bare system. The crossing position is exactly $s^* = A_1/(A_1+1)$, unchanged by the ancilla.

This is STRONGER than the original Conjecture 1, which predicted a correction. There is no correction: the ancilla does literally nothing to the crossing.

### Theorem 2 (Universality of Uniform Superposition)
Among all states $|\psi\rangle \in \mathbb{C}^N$, the uniform superposition $|\psi_0\rangle = (1/\sqrt{N})\sum_z |z\rangle$ is the unique state (up to phases on individual basis states) for which the weights $w_k = \sum_{z \in \Omega_k} |\langle z|\psi\rangle|^2$ depend only on $\{E_k, d_k\}$ and not on the specific assignment of energies to basis states. This extends to entangled initial states on $\mathbb{C}^N \otimes \mathbb{C}^{2^m}$: the reduced weights $q(z) = \sum_a |\langle z,a|\Psi\rangle|^2$ must satisfy $q(z) = 1/N$ for all $z$.

This is the key structural result. Any instance-independent algorithm must use the uniform superposition, fixing the crossing at $A_1/(A_1+1)$.

### Theorem 3 (Coupled Ancilla Extension)
No fixed instance-independent system-ancilla coupling $V$ makes $A_1^{\text{eff}}$ constant across all problem instances. The effective crossing position $s^*_{\text{ext}}$ remains a non-constant function of the spectrum. Proved via large-$\Delta$ asymptotics: $A_1^{\text{eff}}(\Delta) = C_{\text{ground}}(V) + \Theta(1/\Delta)$ where the excited-cluster contribution varies with $\Delta$. Numerically verified across coupling strengths $\lambda \in \{0.01, 0.05, 0.1, 0.5, 1.0\}$.

### Theorem 4 (Multi-Segment Rigidity)
For a multi-segment adiabatic path, the crossing in the final segment depends on $B_1 = \sum_k w_k(\psi_{\text{mid}})/(E_k - E_0)$. By Theorem 2, instance-independence forces $|\psi_{\text{mid}}\rangle = |\psi_0\rangle$, giving $B_1 = A_1$.

### Theorem 5 (No-Go)
For any adiabatic algorithm using rank-one initial Hamiltonian, encoding the same unstructured optimization problem, with instance-independent design: the crossing position cannot be made spectrum-independent. In the uncoupled case, $\partial s^*/\partial A_1 = 1/(A_1+1)^2 > 0$ quantitatively. In the coupled case, $A_1^{\text{eff}}$ is non-constant across instances (Theorem 3).

### Proposition 6 (Rank-2 Obstruction on Two-Level Families)
For $H_0 = -(|\psi_0\rangle\langle\psi_0| + |\phi\rangle\langle\phi|)$ with fixed instance-independent $|\phi\rangle \perp |\psi_0\rangle$, and any fixed-degeneracy two-level family $E_0=0$, $E_1=\Delta$ with $1 \le d_0 < N$, the reduced crossing equation has roots $x(\Delta)=\kappa\Delta$ with $\kappa>0$ independent of $\Delta$. Hence $s(\Delta)=1/(1+\kappa\Delta)$ is non-constant in $\Delta$ (equivalently non-constant in $A_1$). Fixed rank-2 projectors do not make crossing position spectrum-independent on these two-level families.

### Proposition 6A (Rank-k Two-Level Scaling Law)
For any fixed rank-$k$ projector $P=UU^\dagger$ and fixed-degeneracy two-level family, the reduced crossing equation is $\det(I_k - xB/\Delta)=0$ with $B=U_{\mathrm{exc}}^\dagger U_{\mathrm{exc}}$ and $x=(1-s)/s$. Every branch with $\mu>0$ eigenvalue of $B$ has $x(\Delta)=\Delta/\mu$ and $s(\Delta)=1/(1+\Delta/\mu)$, hence depends nontrivially on $\Delta$ and $A_1$. Only the degenerate case $B=0$ (projector entirely in ground subspace) removes this dependence.

### Proposition 6B (Commuting Multilevel Extension)
For multilevel families, if the excited Gram blocks $B_\ell = U_\ell^\dagger U_\ell$ commute pairwise, the reduced determinant diagonalizes branchwise: each active branch satisfies $x_r(\Delta)=1/G_r(\Delta)$ with $G_r(\Delta)=\sum_{\ell\ge1}\mu_{\ell r}/(E_\ell-E_0)$ and $s_r=G_r/(1+G_r)$. Varying any level gap with coefficient $\mu_{\ell r}>0$ changes $s_r$ monotonically, so crossing positions remain spectrum-dependent in this commuting multilevel class.

### Proposition 6C (General Multilevel Trace No-Go)
Without any commutation assumption, the reduced matrix is $A(\Delta)=\sum_{\ell\ge1}(E_\ell-E_0)^{-1}B_\ell$. If a varied level has $B_j \neq 0$, then $\mathrm{tr}(A(\Delta))=\sum_\ell \mathrm{tr}(B_\ell)/(E_\ell-E_0)$ changes strictly with that gap, so the multiset of positive reduced roots cannot remain constant. Thus full root-set spectrum-independence is impossible even in noncommuting multilevel families.

### Remaining Multilevel Obstruction
For noncommuting multilevel spectra, Proposition 6C rules out full root-set invariance, but closed-form branchwise decoupling (as in Proposition 6B) is still unavailable in general.

### Proposition 7 (Circumvention Landscape)
The barrier can be circumvented by leaving fixed-schedule rank-one instance-independent AQO (Experiment 10, Theorem 2; Experiment 05, Theorem 1; Experiment 13, Theorem 2; Experiment 08, Propositions 8/9/13), but cannot be circumvented by product ancillas, non-uniform fixed initial states, fixed couplings, multi-segment rank-one paths, or any rank-one instance-independent Hamiltonian modification (Theorems 1-5), nor by fixed rank-2/rank-$k$ projectors on fixed-degeneracy two-level families (Propositions 6 and 6A), nor by fixed rank-$k$ projectors on commuting multilevel block families with varied supported levels (Proposition 6B), nor by full noncommuting multilevel root-set flattening under varied supported levels (Proposition 6C).

### Lean Formalization (Statement-Level Core)
Created `lean/` with local buildable files for this experiment:
- `CircumventingBarrier/Basic.lean`: spectral data, weights, crossing map
- `CircumventingBarrier/Universality.lean`: Theorem 2 core proved (singleton-assignment permutation form), with singleton-invariance iff uniform characterization under normalization
- `CircumventingBarrier/NoGo.lean`: Theorem 5 core composition proved from component core abstractions
- `CircumventingBarrier/Rank2TwoLevel.lean`: Proposition 6 algebraic core (reduced equation normalization and linear scaling form)
- `CircumventingBarrier/RankKTwoLevel.lean`: Proposition 6A algebraic core (branch rewrite and non-constancy)
- `CircumventingBarrier/RankKMultilevelCommuting.lean`: Proposition 6B algebraic core (single-gap variation non-constancy in commuting multilevel branch form)
- `CircumventingBarrier/RankKMultilevelTraceNoGo.lean`: Proposition 6C algebraic core (trace-drift contradiction against root-multiset invariance)
- `CircumventingBarrier/OperatorCore134.lean`: operator-reduction cores for Theorems 1/3/4 (product-sector invariance, coupled asymptotic non-constancy, segment rigidity map)
- `lean/README.md`: build instructions and formalization scope notes (zero-axiom local package)

### Corollary (Non-Adiabatic Oscillation)
The $A_1$ barrier applies to the non-adiabatic oscillation algorithm (forthcoming [Eduardo]) since it uses the same Hamiltonian $H(s) = -(1-s)|\psi_0\rangle\langle\psi_0| + sH_z$.


## Conjecture Status

### Conjecture 1 (Single Ancilla Failure): DISPROVED
Original claim: $A_1^{\text{combined}} = (1/2)A_1(H_z) + \text{correction}$. Actual result: $A_1^{\text{combined}} = A_1(H_z)$ exactly (no factor of 1/2, no correction). The ancilla subspace decouples completely, and the crossing branches are identical to the bare system.

### Conjecture 2 (General Ancilla Suppression): DISPROVED
Original claim: correction is $O(d_0/N)$. Actual result: for uncoupled product ancilla, the correction is exactly ZERO (Theorem 1). The claim about $d_0/N$ suppression is irrelevant.

### Conjecture 3 (Multi-Segment Rigidity): PROVED (Theorem 4)
The crossing in the final segment depends on $A_1$ through the overlaps. Instance-independence forces $B_1 = A_1$.

### Conjecture 4 (Informal No-Go): PROVED (Theorem 5)
Stronger than originally stated. The mechanism is the universality of the uniform superposition (Theorem 2), not $d_0/N$ suppression.

### Conjecture 5 (Escape Requires Spectral Knowledge): PROVED (Theorem 2 converse)
Non-uniform states can change the effective $A_1$, but computing the right state requires knowing which basis states have which energies.


## Approach

### What Worked
1. Subspace decomposition of the extended Hamiltonian (Theorem 1)
2. Permutation argument for universality (Theorem 2)
3. Secular equation analysis throughout
4. Matrix determinant lemma for rank-$k$ secular reduction and explicit rank-2 quadratic analysis
5. Numerical verification for all theorems/propositions via exact diagonalization

### What Changed from Original Plan
1. The original perturbative analysis for Theorem 3 was wrong: naive $O(\|V\|/\Delta)$ bounds fail because coupling can split ground levels, creating $1/\|V\|$ divergences in $A_1^{\text{eff}}$. Replaced with a qualitative argument showing instance-independent $V$ cannot collapse $s^*$.
2. Conjecture 1 was completely wrong: predicted a correction where there is none.


## Open Questions

1. Can Proposition 6B be extended from commuting multilevel blocks to the fully noncommuting multilevel regime?
2. In the noncommuting multilevel regime, can one classify which individual branches can remain constant despite Proposition 6C root-set drift?
3. Can time-dependent couplings $V(s)$ eliminate the $A_1$ dependence? (Theorem 3 covers fixed $V$ only.)
4. Can non-rank-one intermediate Hamiltonians circumvent Theorem 4? (The rank-one secular form is essential there.)
5. Is there a polynomial-time quantum algorithm that estimates $A_1$ to algorithmically useful precision?
6. Can non-adiabatic protocols (beyond oscillation with the same Hamiltonian family) bypass the barrier entirely?
7. For structured problems, which structural classes make the barrier operationally irrelevant?


## Connection to Other Experiments

- Experiment 05, Theorem 1: adaptive measurement circumvents within the adiabatic model with $O(n)$ measurements and $T=O(T_{\inf})$.
- Experiment 10, Theorem 2: circuit-model minimum finding achieves $\Theta(\sqrt{N/d_0})$ without spectral side information.
- Experiment 13, Theorem 2: quantum estimation of $A_1$ at precision $2^{-n/2}$ in $O(2^{n/2}\mathrm{poly}(n))$.
- Experiment 08, Propositions 8/9/13: bounded-treewidth exact tractability and partition-function based additive approximation regimes for $A_1$.
- This experiment (Theorems 1-5, Propositions 6/6A/6B/6C): fixed instance-independent Hamiltonian engineering does not eliminate spectrum dependence.


## References

1. Paper Discussion, p.983 - Explicit open problem statement
2. Paper Section 3 - Hardness of $A_1$
3. Paper Section 2.1 - Spectral analysis and crossing position
4. Roland-Cerf 2002 - Local adiabatic schedule (motivates the $s^*$ dependence)


## Status

**Phase**: Complete (extended with rank-2 higher-rank analysis and cross-experiment landscape)

**Open problem note**: Directly addresses the paper's central open problem (Discussion, p.983). The answer is negative within the rank-one framework. Also applies as a corollary to the non-adiabatic oscillation setting (same $A_1$ barrier).
