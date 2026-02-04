# Unstructured Adiabatic Quantum Optimization

My master's thesis on Unstructured Adiabatic Quantum Optimization, supervised by Shantanav Chakraborty. Built on the published paper [Unstructured Adiabatic Quantum Optimization: Optimality with Limitations](https://arxiv.org/abs/2411.05736) (Braida, Chakraborty, Chaudhuri, Cunningham, Menavlikar, Novo, Roland, 2025).

Make sure that the way this thesis would be written is satisfactory to Prof. Shantanav Chakraborty (check `taste/` for papers by him). We also aim to beat the baseline expectations of the theses we have with us in `taste/` (of Zeeshan Ahmed and Ronald de Wolf).

## Table of Contents

### Frontmatter

- Epigraph
- Abstract
- Acknowledgments
- List of Theorems / List of Figures

### Chapter 1: Introduction (~15 pages)

| Section | Content |
|---------|---------|
| 1.1 The Ground State Problem | Nature finds ground states. Can we harness this for computation? Physical motivation for Hamiltonian-based quantum computing. |
| 1.2 Quantum Speedups for Optimization | Grover's $\sqrt{N}$ speedup. Circuit model achieves it via amplitude amplification. |
| 1.3 The Adiabatic Alternative | Condensed matter connections, quantum annealing. Universality: AQC equivalent to circuit model. |
| 1.4 The Central Question | Can AQO match Grover? The $\Omega(2^{n/2})$ lower bound. |
| 1.5 What This Thesis Establishes | Main Result 1: optimal runtime. Main Result 2: NP-hard. Main Result 3: #P-hard. The central paradox. |
| 1.6 How to Read This Thesis | Roadmap. Running example: unstructured search. |

### Chapter 2: Physics and Computation (~25 pages)

| Section | Content |
|---------|---------|
| 2.1 Linearity in Physics | Why linear theories are special. Superposition principle. |
| 2.2 Non-linearity and Chaos | The contrast: sensitivity to initial conditions, unpredictability. |
| 2.3 How Quantum Mechanics Emerged | Historical and philosophical context. The measurement problem. |
| 2.4 Adiabaticity in Classical Systems | Slow vs fast timescales. Hierarchical dynamics. |
| 2.5 Computational Complexity | P, NP, NP-completeness. 3-SAT. Decision vs search. |
| 2.6 Computability | Turing machines. The halting problem. What computers cannot do. |
| 2.7 Information Theory | Entropy, bits, communication. Physical basis of information. |
| 2.8 The Convergence | Why physics constrains computation. Landauer's principle. |

### Chapter 3: Quantum Computation (~25 pages)

| Section | Content |
|---------|---------|
| 3.1 Hilbert Spaces and States | Finite-dimensional spaces. Dirac notation. Normalization. |
| 3.2 Operators | Hermitian, unitary, projectors. Spectral decomposition. |
| 3.3 Measurement | Born rule. Projective measurement. Post-measurement states. |
| 3.4 Composite Systems | Tensor products. Entanglement. The strangeness that enables speedups. |
| 3.5 The Circuit Model | Gates, circuits, BQP. Universal gate sets. |
| 3.6 Grover's Algorithm | Unstructured search in $O(\sqrt{N})$. Geometric visualization. Optimality proof. |
| 3.7 Amplitude Amplification | Generalization. Finding ground states in the circuit model. |
| 3.8 Quantum Complexity Classes | BQP, QMA. Relationship to classical classes. |

### Chapter 4: Adiabatic Quantum Computation (~25 pages)

| Section | Content |
|---------|---------|
| 4.1 The Adiabatic Theorem | Born-Fock (1928). Intuition: slow enough means staying in ground state. |
| 4.2 Rigorous Bounds | Jansen-Ruskai-Seiler formulation. The bound $T \geq \mathrm{poly}(1/g_{\min}, 1/\varepsilon)$. |
| 4.3 Schedule Design | Global vs local adiabaticity. Constant rate vs adaptive. |
| 4.4 Historical Development | Farhi-Goldstone-Gutmann (2000). Roland-Cerf for Grover. |
| 4.5 Equivalence to Circuit Model | Aharonov et al. AQC is universal. |
| 4.6 The Spectral Gap Challenge | For general problems, where is the avoided crossing? Why gap bounds are hard. |
| 4.7 Related Work | Guo-An (2025), other recent developments. |

### Chapter 5: Adiabatic Quantum Optimization (~20 pages)

| Section | Content |
|---------|---------|
| 5.1 From AQC to Optimization | The special case: diagonal problem Hamiltonians. |
| 5.2 The Problem Hamiltonian | $H_z$ diagonal in computational basis. Eigenvalues $E_0 < E_1 < \cdots < E_{M-1}$. |
| 5.3 NP-hard Problems as Hamiltonians | Ising formulation: $H = \sum J_{ij} \sigma_z^i \sigma_z^j + \sum h_j \sigma_z^j$. 3-SAT encoding. |
| 5.4 The Interpolation | $H(s) = -(1-s)\ket{\psi_0}\bra{\psi_0} + sH_z$. Initial state $\ket{\psi_0} = \ket{+}^{\otimes n}$. |
| 5.5 The Symmetric Subspace | $\mathcal{H}_S = \mathrm{span}\{\ket{k}\}$. Reduction from $N = 2^n$ to $M$ dimensions. |
| 5.6 Setup for Spectral Analysis | The eigenvalue equation. Structure of the problem. |

### Chapter 6: Spectral Analysis (~30 pages)

| Section | Content |
|---------|---------|
| 6.1 The Spectral Parameters | $A_p = (1/N) \sum_{k \geq 1} d_k/(E_k - E_0)^p$. Central role of $A_1$. |
| 6.2 The Avoided Crossing | Position $s^* = A_1/(A_1+1)$. Width $\delta_s$. Minimum gap $g_{\min}$. |
| 6.3 The Three Regions | Left of crossing, at crossing, right of crossing. Why different techniques needed. |
| 6.4 Gap Bounds: Left Region | Variational principle with ansatz. Bound: $g(s) \geq (A_1(A_1+1)/A_2)(s^*-s)$. |
| 6.5 Gap Bounds: Crossing Region | Window analysis. $g_{\min}/2 \leq g(s) \leq 2g_{\min}$. |
| 6.6 Gap Bounds: Right Region | Resolvent method. Sherman-Morrison. Bound: $g(s) \geq (\Delta/30)(s-s_0)/(1-s_0)$. |
| 6.7 Synthesis | Three-region picture unified. The complete gap profile. |

### Chapter 7: The Optimal Schedule (~25 pages) [ALAPAN'S CONTRIBUTION]

| Section | Content |
|---------|---------|
| 7.1 The Local Schedule Construction | $ds/dt \propto g(s)^2$. Gap-adaptive evolution. |
| 7.2 Running Time: The Three Integrals | $I_{\text{left}} + I_{\text{window}} + I_{\text{right}}$. Dominant contribution analysis. |
| 7.3 Main Result 1 | **Theorem**: $T = O((1/\varepsilon) (\sqrt{A_2}/(A_1^2 \Delta^2)) \sqrt{2^n/d_0})$. |
| 7.4 Matching the Grover Lower Bound | For Ising Hamiltonians with $\Delta \geq 1/\mathrm{poly}(n)$: $T = \widetilde{O}(\sqrt{2^n/d_0})$. |
| 7.5 What Knowledge the Algorithm Requires | $s^*$ to precision $O(\delta_s)$, meaning $A_1$ to precision $\sim 2^{-n/2}$. |
| 7.6 Optimality for Ising Hamiltonians | When $A_1$, $A_2$ are bounded. |

### Chapter 8: Hardness of Optimality (~25 pages)

| Section | Content |
|---------|---------|
| 8.1 The Hidden Requirement | Precision of $s^*$ determines everything. |
| 8.2 3-SAT to Hamiltonian Encoding | The reduction. Modified Hamiltonian $H' = H \otimes (I + \sigma_z)/2$. |
| 8.3 Main Result 2: NP-Hardness | **Theorem**: Two calls to $A_1$ oracle at precision $\varepsilon < 1/(72(n-1))$ solve 3-SAT. |
| 8.4 Polynomial Interpolation | Query $A_1(H'(\beta))$ for $O(\mathrm{poly}(n))$ values. Berlekamp-Welch. |
| 8.5 Main Result 3: #P-Hardness | **Theorem**: $O(\mathrm{poly}(n))$ calls to exact $A_1$ oracle extract all degeneracies. |
| 8.6 The Fundamental Asymmetry | Circuit model has no such barrier. The precision gap. |

### Chapter 9: Exploring the Hardness Barrier (~35 pages) [THESIS EXTENSIONS]

| Section | Content |
|---------|---------|
| 9.1 The Separation Theorem | Gap-uninformed schedules incur $\Omega(2^{n/2})$ overhead. Adversarial construction. Minimax lower bound. |
| 9.2 Robust Schedules | Hedging with bounded uncertainty $[u_L, u_R]$. Constant-factor approximation without exact $A_1$. |
| 9.3 Partial Information | The interpolation theorem: $T(\epsilon) = T_{\inf} \cdot \max(1, \epsilon/\delta_{A_1})$. Linear degradation. |
| 9.4 Adaptive Schedules | Key insight: COMPUTING vs DETECTING. Binary search with phase estimation. $O(n)$ measurements achieve $T = O(T_{\inf})$. Measurement lower bound: $\Omega(n)$ necessary. |
| 9.5 The Measure Condition | Gap geometry near $s^*$: flatness parameter $\alpha$. Scaling spectrum: $T = \Theta(1/\Delta^{3-2/\alpha})$. Dichotomy conjecture is FALSE. |
| 9.6 Synthesis | Complete picture of what ignorance costs. How adaptive methods change the landscape. |

### Chapter 10: Conclusion (~10 pages)

| Section | Content |
|---------|---------|
| 10.1 Summary of Results | The trilogy: optimal algorithm, NP-hard preprocessing, #P-hard exactly. |
| 10.2 The Lean Formalization | Status and axiom analysis. What is proved, what is axiomatized. |
| 10.3 Open Questions | Structured tractability. Information-theoretic limits. Intermediate precisions. |
| 10.4 Reflections | What these barriers tell us about quantum speedups. The adiabatic paradigm. |
