# Chapter Sketches

Chapter sketches for remaining unwritten chapters. Chapters 5-8 are already written and their sketches have been retired.

**NOTE**: The following chapter sketches attempt at structuring the thesis but are not final and feel free to edit them or build the chapters irrespective of them.

### Chapter 1: Introduction

**Overview:** Sets up the thesis problem, states main results upfront, and provides roadmap. Written last to reflect actual content.

**Depends on:** Knowing content of all other chapters.

- **Section: The Puzzle**
  - Ground states as computational answers: physical systems seek low-energy configurations
  - Encode computational problem in Hamiltonian $H$; ground state encodes solution
  - "Let nature compute" - attractive idea
  - The question: Can physical systems solve hard problems efficiently? Can quantum beat classical for optimization?
  - TODO: Build tension before resolution; don't answer too quickly
  - REVIEWER: presentation_quality - Hook the reader

- **Section: Unstructured Search as Canonical Target**
  - The search problem: find marked item among $N$ items, no structure (oracle model)
  - Classical: $O(N)$ queries required (must check every item)
  - Quantum: $O(\sqrt{N})$ queries via Grover, provably optimal (BBBV)
  - Why this is the right benchmark: clean problem, clear lower bound, quadratic speedup achieved by circuits
  - Question: can AQO match this?
  - FORWARD: Chapters 3 (Grover), 7 (AQO matches it)

- **Section: Adiabatic Quantum Optimization**
  - AQC idea: encode problem in $H_z$, start with easy $H_0$, interpolate $H(s) = (1-s)H_0 + sH_z$, evolve slowly
  - AQO = AQC with restrictions: $H_z$ diagonal, $H_0$ is projector, only schedule $s(t)$ adjustable
  - The appeal: "Nature computes for you", no explicit gates, potentially robust
  - The catch (preview): schedule requires gap knowledge, gap info is expensive
  - TODO: Make AQO appealing before showing limitations
  - FORWARD: Chapter 4 (AQC), Chapter 5 (AQO setup)

- **Section: The Trilogy - Main Results Frontloaded**
  - SOURCE: paper/v3-quantum.tex Theorems 1-3
  - (i) Optimality exists: $T = \tilde{O}(\sqrt{N/d_0})$, matches Grover (Chapter 7)
  - (ii) Computing schedule parameters is NP-hard: $A_1$ to $1/\text{poly}(n)$ reduces 3-SAT (Chapter 8)
  - (iii) Exact parameter values are $\#P$-hard: polynomial interpolation attack (Chapter 8)
  - The tension: optimal speedup exists but requires solving NP-hard problem first
  - "Optimality with limitations"
  - TODO: State results crisply, create tension
  - REVIEWER: significance - This is the paper's contribution

- **Section: The Central Question**
  - When does "nature computes for you" actually work?
  - Naive view: set up Hamiltonian, wait, measure
  - Reality: must choose schedule $s(t)$, optimal requires gap info, gap info is NP-hard
  - Reframing: not "can AQO achieve speedup?" but "when is gap information tractable?"
  - This thesis: proves optimality/hardness (5-8), characterizes tradeoff (9), machine-checks (10)
  - FORWARD: Chapter 9 (information gap)

- **Section: Thesis Contributions**
  - Exposition of published work: deep explanation (Chapters 5-8), pedagogical, broader context
  - Original extensions (Chapter 9): separation theorem, partial information, robust/adaptive schedules
  - Chapter 9 context: extends Guo-An 2025's gap-informed baseline to uninformed/partial/adaptive regimes
  - Formalization (Chapter 10): Lean 4, machine-checked, errors caught
  - Goal: best single source, clear enough to teach, rigorous enough to build on
  - REVIEWER: originality - Clear about contributions

- **Section: Chapter Overview and Reading Paths**
  - Background (can skim): Chapters 2-4
  - Core paper results (essential): Chapters 5-8
  - Extensions (original): Chapter 9
  - Verification: Chapter 10
  - Conclusion: Chapter 11
  - Reading paths: QC expert (skim 2-3), complexity theorist (read 2-8), full (1-11)
  - REVIEWER: presentation_quality - Roadmap helps navigation

### Chapter 2: Physics and Computation

**Overview:** First-principles foundation connecting physics to computation. Builds intuition before formalism.

**Forward:** Chapter 3 (Quantum computation), Chapter 4 (AQC bridge), Chapter 8 (complexity classes)

**Definitions introduced:** P, NP, NP-complete, NP-hard, #P, reduction

- **Section: Reality**
  - Setting the stage philosophically (brief): ontology, epistemology, mathematics as model
  - Physics provides substrate for computation; computation provides tools to analyze physics
  - TODO: Keep brief - not a philosophy thesis
  - OPTION: Could be very brief or omitted
  - REVIEWER: presentation_quality - Don't overdo philosophy

- **Section: Physics**
  - Three pillars: classical mechanics (Hamiltonian, phase space, determinism), statistical mechanics (entropy, equilibrium, optimization), quantum mechanics (preview)
  - For thesis: Hamiltonian formulation connects to QM, ground state as optimization target
  - TODO: Balance breadth vs depth; foreshadow quantum advantage
  - FORWARD: Chapter 3 develops quantum mechanics fully

- **Section: Computation**
  - SOURCE: Arora-Barak, Sipser
  - Turing machines, Church-Turing thesis, universality
  - Computability: decidable vs undecidable, halting problem
  - Complexity: P (polynomial time), NP (verifiable solutions), NP-complete (hardest in NP, SAT/3-SAT), NP-hard
  - TODO: Define reduction precisely; SAT and 3-SAT as canonical examples
  - FORWARD: Chapter 8 uses NP-hardness for $A_1$ estimation
  - REVIEWER: technical_soundness - Standard definitions

- **Section: The $\#P$ Complexity Class**
  - SOURCE: paper/v3-quantum.tex lines 208-209, Valiant (1979)
  - $\#P$: counting problems ("how many?" vs "does solution exist?")
  - $\#P$-complete: $\#$SAT is $\#P$-complete
  - Relation to thesis: $d_0$ = counting ground states, $A_1$ exactly is $\#P$-hard
  - TODO: Define formally; explain why counting harder than decision
  - FORWARD: Chapter 8 uses #P-hardness
  - REVIEWER: technical_soundness - Definition needed for hardness

- **Section: Linearity and Its Limits**
  - Linearity is powerful: superposition, tractable systems, perturbation theory
  - Quantum mechanics is exactly linear: Schrodinger equation, superposition of solutions
  - Nonlinearity and hardness: chaos, phase transitions, computational hardness
  - For thesis: $H(s)$ linear in $|\psi\rangle$ but ground state changes nonlinearly in $s$
  - TODO: Connect linearity of QM to computational structure
  - FORWARD: Chapters 5-6 show gap as nonlinear behavior

- **Section: Adiabaticity**
  - SOURCE: Griffiths QM
  - Thermodynamic adiabatic: slow, reversible, no heat exchange
  - Quantum adiabatic: slow $H(t)$ evolution, system stays in ground state
  - Key condition: "slow" means $d/dt \ll \text{gap}^2$
  - Landau-Zener transitions: probability of jumping, exponential suppression $\sim 1/\text{gap}^2$
  - TODO: Distinguish thermodynamic vs quantum; give gap-slowness intuition
  - FORWARD: Chapter 4 formalizes adiabatic theorem
  - REVIEWER: presentation_quality - Physical intuition first

- **Section: Energy Landscapes and Optimization**
  - Ground states as optimization solutions: minimize $H$, ground state = optimal
  - Complex landscapes: spin glasses, local minima, NP-hard = rugged
  - Classical methods: simulated annealing, gradient descent, limitations
  - Quantum approach: tunneling, adiabatic tracking, but gap determines speed
  - For thesis: AQO finds ground state, question is how fast vs classical
  - TODO: Connect to SAT, MAX-CUT; be honest about what quantum helps
  - FORWARD: Chapter 5 formalizes AQO setup

- **Section: Bridge to Quantum Computation**
  - Quantum speedup sources: superposition, interference, entanglement
  - BQP preview: problems solvable efficiently on quantum computers
  - Adiabatic quantum computation preview: encode, evolve, measure
  - Central question: Can AQO achieve provable speedup? (Yes, with info requirements)
  - TODO: Foreshadow main results
  - FORWARD: Chapters 3-4 develop quantum computation and AQC
  - REVIEWER: significance - Connect to thesis contribution

### Chapter 3: Quantum Computation

**Overview:** Establishes quantum mechanics and computation background. Introduces Hilbert spaces, Hamiltonians, quantum speedup paradigm.

**Needs:** Chapter 2 (Computation basics, complexity classes)

**Forward:** Chapter 4 (AQC foundation), Chapter 5 (Hamiltonians, eigenvalues), Chapter 6 (variational principle)

**Definitions introduced:** Hilbert space, qubit, Hamiltonian, eigenvalue, eigenvector, spectral gap, unitary, measurement, BQP

- **Section: Quantum Mechanics Essentials**
  - SOURCE: Sakurai, Nielsen-Chuang
  - States: vectors in Hilbert space, superposition
  - Measurement: Born rule, collapse, probabilistic outcomes
  - Unitary evolution: Schrodinger equation, reversibility
  - Key concepts: $|\psi\rangle$ in complex Hilbert space, $|\langle\phi|\psi\rangle|^2$ probabilities, $U(t)|\psi(0)\rangle$
  - TODO: Decide level of detail (physics vs CS audience)
  - REVIEWER: presentation_quality - Accessible to CS reader

- **Section: Hilbert Spaces and the Computational Basis**
  - SOURCE: Nielsen-Chuang Chapter 2
  - Qubit: $\mathbb{C}^2$, basis $\{|0\rangle, |1\rangle\}$
  - $n$-qubit system: $(\mathbb{C}^2)^{\otimes n} = \mathbb{C}^{2^n}$, dimension $N = 2^n$
  - Computational basis: $|x\rangle$ for $x \in \{0,1\}^n$
  - Inner product, norm, superposition with normalization
  - For thesis: $N = 2^n$ exponential, computational basis where $H_z$ diagonal
  - TODO: Define notation (bra-ket), tensor product
  - FORWARD: Chapter 5 uses N = 2^n, computational basis

- **Section: Hamiltonians as Energy**
  - SOURCE: Standard QM, Nielsen-Chuang
  - Hermitian operator: $H = H^\dagger$, real eigenvalues $E_k$, eigenvectors $|k\rangle$
  - Spectral decomposition: $H = \sum_k E_k |k\rangle\langle k|$ (non-degenerate), $H = \sum_k E_k P_k$ (degenerate)
  - Ground state: lowest eigenvalue $E_0$, encodes solution for optimization
  - Spectral gap: $g = E_1 - E_0$, central to adiabatic computation
  - TODO: Handle degeneracy ($d_k$-fold); emphasize spectral gap
  - NOTE: "Spectral gap" defined here; Chapter 4 discusses computational role
  - FORWARD: Chapters 5-6 analyze spectral gap of $H(s)$
  - REVIEWER: technical_soundness - Definitions must be precise

- **Section: Time Evolution**
  - SOURCE: Nielsen-Chuang Chapter 2
  - Schrodinger equation (time-independent): $i \, d|\psi\rangle/dt = H|\psi\rangle$
  - Solution: $|\psi(t)\rangle = e^{-iHt}|\psi(0)\rangle = U(t)|\psi(0)\rangle$, unitary
  - Time-dependent $H(t)$: more complex, time-ordered exponential, relevant for AQC
  - TODO: Clarify units ($\hbar = 1$); time-dependent case
  - FORWARD: Chapter 4 uses time-dependent $H(s)$
  - REVIEWER: technical_soundness - Units and conventions

- **Section: Why Quantum Helps**
  - Superposition: $N = 2^n$ amplitudes in $n$ qubits (NOT parallel computation)
  - Interference: amplitudes add, cancel wrong, amplify correct - key to speedups
  - Tunneling: traverse classically forbidden regions (debated for optimization)
  - Entanglement: non-classical correlations (less central to AQO)
  - TODO: Be honest about proven vs hoped; tunneling claims controversial
  - REVIEWER: significance - Motivate quantum computation

- **Section: Circuits and Query Complexity**
  - SOURCE: Nielsen-Chuang, Arora-Barak
  - Gate model: universal gates, circuit depth/width, polynomial = BQP
  - BQP: polynomial-time quantum, probability $\geq 2/3$, $P \subseteq BQP \subseteq PSPACE$
  - Oracle model: black-box $f$, quantum oracle $|x,y\rangle \to |x, y \oplus f(x)\rangle$, query count
  - For thesis: Grover $O(\sqrt{N})$ optimal, AQO doesn't use oracles but $H_z$ encodes $f$
  - TODO: Define BQP precisely; oracle vs non-oracle
  - FORWARD: Chapters 7/8 compare AQO to circuit model
  - REVIEWER: literature - Standard definitions

- **Section: Grover as Geometry**
  - SOURCE: Grover (1996), Nielsen-Chuang
  - Search problem: find marked $w$ among $N$, oracle $f(x) = 1$ iff $x = w$
  - Geometric picture: 2D subspace $\text{span}\{|w\rangle, |s\rangle\}$, rotation by $\theta \sim 1/\sqrt{N}$
  - Runtime: $\pi/(4\theta) \sim \sqrt{N}$ iterations
  - Why geometric view matters: optimality transparent, connects to AQO two-level structure
  - TODO: Draw rotation picture; connect to Roland-Cerf
  - FORWARD: Chapter 5 has similar two-level structure near $s^*$
  - REVIEWER: presentation_quality - Geometry before algebra

- **Section: Why Grover is Optimal**
  - SOURCE: Bennett-Bernstein-Brassard-Vazirani (1997)
  - BBBV: $\Omega(\sqrt{N})$ queries needed for constant probability
  - Proof idea: query complexity limited by amplitude movement, polynomial method
  - Implication: quadratic speedup fundamental, AQO matching is optimal
  - TODO: Sketch proof or intuition; connect to AQO runtime
  - FORWARD: Chapter 7 achieves $\tilde{O}(\sqrt{N/d_0})$
  - REVIEWER: technical_soundness - Lower bound important

- **Section: The Decoherence Challenge**
  - Practical issues: maintaining quantum states, environmental decoherence
  - Error correction: encode logical in physical, threshold theorem
  - Why adiabatic might help: gap provides protection, ground state stable (but gap can be small)
  - For thesis: assume ideal evolution, noise beyond scope, focus on complexity
  - TODO: Be clear about assumptions
  - OPTION: Expand or minimize depending on scope
  - REVIEWER: presentation_quality - Set expectations clearly

### Chapter 4: Adiabatic Quantum Computation

**Overview:** Introduces AQC and sets up framework for AQO. Bridges general quantum computation to specific AQO setting.

**Needs:** Chapter 3 (Hamiltonians, eigenvalues, time evolution, Grover), Chapter 2 (complexity, optimization)

**Forward:** Chapter 5 (AQO with diagonal $H_z$), Chapter 7 (Roland-Cerf schedule)

**Definitions introduced:** adiabatic theorem, spectral gap as computational resource, avoided crossing, local schedule

- **Section: Physical Motivation**
  - SOURCE: Sakurai, Griffiths
  - Adiabatic theorem: slow evolution stays in ground state
  - Gap determines how slow is slow enough
  - Physical intuition: system tracks changing potential
  - TODO: Concrete physical example; distinguish quantum vs thermodynamic "adiabatic"
  - REVIEWER: presentation_quality - Physical intuition before formalism

- **Section: The Computational Idea**
  - SOURCE: Farhi et al. (2001)
  - Encode problem in $H_z$ (ground state = solution), start with easy $H_0$
  - Interpolate: $H(s) = (1-s)H_0 + sH_z$ for $s \in [0,1]$
  - Read answer: measure at $s=1$
  - Chapter 5 specializes: $H_0 = -|\psi_0\rangle\langle\psi_0|$, $H_z$ diagonal
  - TODO: Explain encoding of optimization problems
  - FORWARD: Chapter 5 uses $H(s) = -(1-s)|\psi_0\rangle\langle\psi_0| + sH_z$

- **Section: The Adiabatic Theorem**
  - SOURCE: Born-Fock (1928), Kato (1950), Jansen-Ruskai-Seiler (2007)
  - Statement: if slow enough, stay in instantaneous ground state
  - Quantitative: Error $\leq C \cdot \max|dH/ds| / \min g(s)^2$
  - Implications: runtime $\sim 1/g_{\min}^2$ worst case
  - Note: Chapter 7 uses a NEW simplified version with local gap bounds (not just Jansen-Ruskai-Seiler)
  - TODO: State precisely with conditions; distinguish from original qualitative theorem
  - FORWARD: Chapter 7 uses this for runtime
  - REVIEWER: technical_soundness - State conditions carefully

- **Section: The Spectral Gap as Central Bridge**
  - Gap connects physics to complexity
  - Physics: large gap = robust, fast; small gap = fragile, slow
  - Computational: large = easy, small = hard/slow
  - Gap as bottleneck: $T \sim 1/g_{\min}^2$, QMA-hardness from gap estimation
  - TODO: Connect to QMA and local Hamiltonian problem
  - FORWARD: Chapters 5-6 analyze gap structure
  - REVIEWER: significance - Gap is central object of thesis

- **Section: Avoided Crossings**
  - SOURCE: Landau (1932), Zener (1932)
  - Definition: energy levels approach but don't cross (repel due to coupling)
  - Landau-Zener: $P \sim \exp(-\pi g_{\min}^2 / (2v))$, must slow near crossings
  - Gap minimum typically at avoided crossing; single crossing simplifies (AQO case)
  - TODO: Derive Landau-Zener or give intuition; non-crossing theorem
  - FORWARD: Chapter 5 has single crossing at $s^*$, Chapter 6 bounds three regions
  - REVIEWER: presentation_quality - Intuition before formula

- **Section: Schedules**
  - Linear: $s(t) = t/T$, simple but not optimal, wastes time where gap large
  - Adaptive: $ds/dt \sim g(s)^2$, slow where small, fast where large
  - Gap-aware vs gap-unaware: knows $g(s)$ or must work for all instances
  - TODO: Compare runtimes; set up gap-uninformed problem (Chapter 9)
  - FORWARD: Chapter 7 constructs optimal, Chapter 9 analyzes uninformed

- **Section: Roland-Cerf Construction**
  - SOURCE: Roland-Cerf (2002)
  - First AQC achieving Grover speedup
  - Setup: $H_0 = -|s\rangle\langle s|$, $H_z = I - |w\rangle\langle w|$, single marked item
  - Key insight: slow only where gap small, adapt $ds/dt \sim g(s)^2$
  - Result: $T = O(\sqrt{N})$, matches circuit Grover
  - Why matters: shows AQO can match Grover, Chapter 5 generalizes
  - TODO: Present as special case of AQO; emphasize single crossing
  - FORWARD: Chapter 5 generalizes
  - REVIEWER: significance - Foundation for Chapter 5

- **Section: Universality**
  - SOURCE: Aharonov et al. (2007)
  - AQC computationally equivalent to circuit model (polynomial overhead both ways)
  - Implications: universal, no fundamental power difference, but different resources
  - TODO: Cite properly; explain equivalence briefly
  - OPTION: Could be brief or detailed
  - REVIEWER: literature - Must cite universality

- **Section: Why AQO is More Restricted**
  - SOURCE: paper/v3-quantum.tex
  - AQO restrictions: $H_z$ diagonal, no entanglement in $H_z$, $H_0$ projector, only schedule adjustable
  - General AQC: any Hamiltonians
  - Why study AQO? Natural for combinatorics, simpler spectral structure, clean analysis
  - TODO: Explain diagonal constraint; list encodable problems
  - FORWARD: Chapter 5 formalizes

- **Section: The No-Free-Lunch Reality**
  - Misconception: "Just let nature compute"
  - Reality: gap determines runtime, can't run uniformly slow, optimal schedule needs gap info, gap info is NP-hard
  - Tension: AQO achieves Grover (Ch 7) but requires solving hard problem (Ch 8)
  - Preview: $T = \tilde{O}(\sqrt{N/d_0})$, needs $s^*$ to exponential precision, $A_1$ is NP-hard
  - TODO: Frame central tension; set up Chapters 5-9
  - FORWARD: Chapters 5-9 resolve this
  - REVIEWER: significance - Sets up thesis problem

### Chapter 9: Information Gap

**Overview:** Original contributions characterizing information-optimality tradeoff. Extensions beyond published paper. Central thesis: AQO optimality is fundamentally an information question.

**Context:** Extends Guo-An 2025's gap-informed baseline to uninformed/partial/adaptive regimes. Recent work (Guo-An 2025) shows gap-informed scheduling achieves optimal $O(1/\Delta_*)$. This chapter asks: what if gap information is unavailable, uncertain, or costly?

**Needs:** Chapter 5 ($H(s)$, $A_1$, $s^*$, $\delta_s$, $g_{\min}$), Chapter 7 (runtime, schedule), Chapter 8 (hardness)

**Status:** Most results have Lean formalization (noted per section)

**RELATED WORK:** Guo-An 2025 (gap-informed baseline, measure condition), Han-Park-Choi 2025 (adaptive measurement), Roland-Cerf 2002 (original adaptive schedule)

- **Section: The Separation Theorem**
  - SOURCE: src/experiments/04_separation_theorem/main.md
  - LEAN: Complete, no sorry
  - Problem: How much slower is gap-uninformed vs gap-informed?
  - Main Result: $T_{\text{uninformed}} / T_{\text{informed}} \geq (s_R - s_L) / \Delta_*$
  - Corollary: $\Omega(2^{n/2})$ separation for $n$-qubit search
  - Proof: adversarial construction, velocity bound, time lower bound
  - Why novel: no prior minimax lower bound for FIXED uninformed schedules
  - Assumptions from literature: error model, informed achievability
  - Caveats: minimax not single-instance, fixed schedules only
  - TODO: Present adversarial construction; contrast fixed vs adaptive
  - REVIEWER: originality - First minimax lower bound

- **Section: The Partial Information Tradeoff**
  - SOURCE: src/experiments/07_partial_information/main.md
  - LEAN: Complete, no sorry
  - Problem: If $A_1$ known to precision $\epsilon$, what runtime?
  - Main Result: $T(\epsilon) = T_{\inf} \cdot \Theta(\max(1, \epsilon/\delta_{A_1}))$
  - For unstructured: $T(\epsilon) = T_{\inf} \cdot \Theta(\max(1, \epsilon \cdot 2^{n/2}))$
  - Key Finding: Interpolation is LINEAR in $\epsilon$
  - Implications: no threshold, smooth degradation, NP-hard precision still exponential overhead
  - Resolution: smooth confirmed, threshold refuted, graceful $1/\epsilon$ refuted (it's $T \sim \epsilon$)
  - Lean: interpolation bounds, crossingPosition_deriv
  - TODO: Present formula; connect to NP-hardness operationally
  - REVIEWER: originality - First intermediate precision characterization

- **Section: Robust Schedules**
  - SOURCE: src/experiments/02_robust_schedules/main.md
  - LEAN: Partial
  - Problem: Can fixed schedule handle bounded uncertainty $[u_L, u_R]$?
  - Main Result: Hedging achieves constant-factor approximation
  - Error formula: $\text{Error}_{\text{hedge}} / \text{Error}_{\text{unif}} \to (u_R - u_L)$ as interval narrows
  - Example: $[0.4, 0.8]$ achieves ~60% reduction vs uniform
  - Key insight: NP-hardness is "soft" - bounded uncertainty = constant factor
  - Strategy: distribute slowdown across interval $[u_L, u_R]$
  - TODO: Present hedging; connect to practical AQO; derive error formula
  - OPTION: Constructive response to hardness
  - REVIEWER: significance - Hardness not absolute

- **Section: Adaptive Schedules**
  - SOURCE: src/experiments/05_adaptive_schedules/main.md
  - LEAN: Partial
  - Problem: Can adaptive measurement overcome gap-uninformed limitation?
  - Key Insight: Detecting $s^*$ quantumly EASY, computing classically HARD
  - Theorem 1: Adaptive with $O(n)$ measurements achieves $T_{\text{adaptive}} = O(T_{\inf})$
  - Theorem 2: $\Omega(n)$ measurements required (binary search optimal)
  - Complete characterization: $T_{\text{uninformed}} = \Omega(2^{n/2} \cdot T_{\inf})$, $T_{\text{adaptive}} = O(T_{\inf})$
  - Protocol: $O(n)$ measurements to locate $s^*$, then $O(T_{\inf})$ execution
  - Why works: classical NP-hard doesn't block quantum detection
  - TODO: Present protocol; explain phase estimation
  - REVIEWER: originality - First rigorous adaptive protocol

- **Section: Measure Condition and Scaling**
  - SOURCE: src/experiments/06_measure_condition/main.md
  - LEAN: Complete, no sorry
  - Problem: Guo-An (2025) requires "measure condition" for $O(1/\Delta_*)$. When fails?
  - Measure condition: $\mu(\{s : \Delta(s) \leq x\}) \leq C \cdot x$
  - Theorem 1 (Geometric): For $\Delta(s) = \Delta_* + \Theta(|s - s^*|^\alpha)$, $\alpha \leq 1$ holds, $\alpha > 1$ fails
  - Theorem 2 (Scaling): $T = \Theta(1/\Delta_*^{3 - 2/\alpha})$
  - Examples: $\alpha=1 \to T \sim 1/\Delta_*$; $\alpha=2 \to T \sim 1/\Delta_*^2$; $\alpha \to \infty \to T \to 1/\Delta_*^3$
  - Resolution: necessity partially true, dichotomy FALSE (continuous spectrum)
  - Key Finding: NO sharp dichotomy - spectrum from 1 to 3
  - TODO: Present scaling spectrum; physical meaning of flat minimum
  - REVIEWER: originality - Refutes dichotomy, establishes spectrum

- **Section: The Ignorance Taxonomy**
  - Synthesis of all results:
  - Level 0: No information -> $T = T_{\inf} \cdot \Omega(2^{n/2})$ [separation]
  - Level 1: Precision $\epsilon$ -> $T = T_{\inf} \cdot \Theta(\epsilon/\delta_{A_1})$ [partial info]
  - Level 2: Bounded interval -> $T = O(T_{\inf} \cdot (u_R - u_L))$ [robust]
  - Level 3: Quantum measurement -> $T = O(T_{\inf})$ with $O(n)$ measurements [adaptive]
  - Taxonomy shows: information determines achievable speedup
  - TODO: Table or figure; connect to practical scenarios
  - REVIEWER: presentation_quality - Unified picture is key

- **Section: Central Claim**
  - AQO optimality is fundamentally an INFORMATION question
  - Paper's result: Grover speedup but NP-hard schedule
  - This chapter: characterize information-runtime tradeoff precisely
  - Key messages: information determines runtime, gap is information barrier, circuit vs adiabatic have different info requirements
  - "Information gap": gap in spectrum (physics), knowledge (information), models (computation)
  - All connected through $A_1$ and $s^*$
  - TODO: Frame as unifying perspective; connect to broader QC
  - REVIEWER: significance - Thesis's novel perspective

- **Section: Formalization Status**
  - Summary (see src/lean/README.md):
  - Exp 04 (Separation): COMPLETE, no sorry
  - Exp 07 (Partial): COMPLETE, no sorry
  - Exp 02 (Robust): PARTIAL
  - Exp 05 (Adaptive): PARTIAL
  - Exp 06 (Measure): COMPLETE, no sorry
  - Total: 27 axioms in code (25 unproved, 2 have proofs but kept for imports), 76 theorems, 0 sorry in core
  - TODO: Reference lean files; note axiomatized physics
  - REVIEWER: reproducibility - Formalization provides verification

### Chapter 10: Formalization

**Overview:** Documents Lean 4 formalization of thesis results. Shows machine-checked vs axiomatized, and errors caught.

**Needs:** Chapters 5-9 (results being formalized)

**Source:** src/lean/README.md

**Status:** 27 axioms, 76+ theorems, 0 sorries

- **Section: Why Formalization**
  - Motivations: catching errors (5+ issues found), reproducibility (machine-checked), clarity (forces precision)
  - Issues discovered: A2_lower_bound direction, avoidedCrossing_bound hypothesis, betaModifiedHam ordering, shermanMorrison sign
  - TODO: Discuss formalization as methodology
  - REVIEWER: significance - Formalization is novel contribution

- **Section: Lean 4 and Mathlib**
  - SOURCE: src/lean/README.md
  - Lean 4: dependent type theory, tactics, type-checking
  - Mathlib4: community library, linear algebra, analysis
  - Strategy: axiomatize physics, prove mathematics
  - Coverage: ~5,800 lines, 27 axioms, 76+ theorems, 0 sorries
  - TODO: Brief Lean intro; axiom vs theorem
  - REVIEWER: reproducibility - Build instructions

- **Section: Core Paper Formalization**
  - SOURCE: src/lean/README.md, UAQO/ directory
  - Structure: Foundations/, Spectral/, Adiabatic/, Complexity/
  - Key abstractions: `EigenStructure` (eigenvalue/degeneracy data), matches paper notation
  - Fully proved (21 eliminated): `eigenvalue_condition`, `groundEnergy_variational_bound`, `shermanMorrison_resolvent`, `variational_principle`, `lagrange_interpolation`, hardness lemmas
  - TODO: Highlight proof techniques; show notation correspondence
  - REVIEWER: technical_soundness - Verification against paper

- **Section: Axiom Taxonomy**
  - SOURCE: src/lean/README.md (Axiom Tracking)
  - Total: 27 in code, 25 unproved (2 have proofs but kept for imports)
  - External Foundations (9): Cook-Levin, Valiant, adiabatic theorem, resolvent spectral
  - Gap Bounds (6): firstExcited, left/crossing/right/all bounds, minimum location
  - Running Time (4): mainResult1, Ising bound, BBBV lower, matching
  - Hardness (6): A1_polynomial_in_beta, mainResult2, mainResult3, etc.
  - TODO: Which could be eliminated; axiom boundary as trust assumption
  - REVIEWER: reproducibility - Axiom list complete

- **Section: Extension Formalizations (Chapter 9)**
  - SOURCE: src/experiments/*/lean/
  - Separation (04): COMPLETE, no sorry
  - Partial Information (07): COMPLETE, no sorry
  - Measure Condition (06): COMPLETE, no sorry
  - Robust (02): PARTIAL
  - Adaptive (05): PARTIAL
  - TODO: Summarize per experiment
  - REVIEWER: originality - Extensions machine-verified

- **Section: Formulation Issues Discovered**
  - SOURCE: src/lean/README.md (Formulation Fixes)
  - 5+ errors found:
    1. `A2_lower_bound`: was upper bound, reversed
    2. `avoidedCrossing_bound`: missing `spectralConditionForBounds`
    3. `betaModifiedHam_eigenval_ordered_strict`: missing `allGapsGreaterThan`
    4. `betaModifiedHam_eigenval_ordered`: missing gap constraint
    5. `shermanMorrison_resolvent`: sign error
  - Lesson: formalization as debugging tool
  - TODO: Before/after for key fixes; implications for publishing
  - REVIEWER: significance - Demonstrates formalization value

- **Section: Proof Highlights**
  - Selected proofs:
    1. Eigenvalue Condition: Matrix Determinant Lemma, non-degenerate case
    2. Lagrange Interpolation: Mathlib.Lagrange + uniqueness
    3. Sherman-Morrison Resolvent: matrix inverse, sign correction
    4. Variational Principle: Parseval, spectral decomposition
  - `EigenStructure` abstraction: avoids $2^n$ matrices, uses (eigenvalue, degeneracy) pairs
  - TODO: Proof sketches with code excerpts
  - OPTION: Include snippets or keep abstract
  - REVIEWER: presentation_quality - Balance detail and accessibility

- **Section: Verification and Status**
  - SOURCE: src/lean/README.md
  - Building: lake update, lake build
  - Type-checking ensures: well-formed, valid proofs, explicit axioms
  - Current: 27 axioms, 76+ theorems, 0 sorries, ~5,800 lines
  - Complete formalization would require: Cook-Levin, adiabatic theorem, parametric spectral
  - Current captures: all novel math, all reductions, all explicit formulas
  - Axiomatized: external results, physics, some gap bounds
  - TODO: Document build; explain verification workflow
  - REVIEWER: reproducibility - Readers should verify

### Chapter 11: Conclusion

**Overview:** Synthesizes thesis results, discusses implications, lists open problems. Written last to reflect actual content.

**Depends on:** Knowing content of all other chapters

- **Section: The Trilogy Revisited**
  - SOURCE: Chapters 5-8
  - One-page summary of main results:
    - Main Result 1 (Chapter 7): $T = \tilde{O}(\sqrt{N/d_0})$, matches Grover, requires local adaptive schedule
    - Main Result 2 (Chapter 8): $A_1$ to $1/\text{poly}(n)$ is NP-hard (two oracle calls, 3-SAT)
    - Main Result 3 (Chapter 8): $A_1$ exactly is $\#P$-hard (polynomial interpolation, $d_0$ extraction)
  - The synthesis: optimality exists but requires NP-hard problem
  - "Optimality with limitations" captures this tension
  - TODO: Crisp one-paragraph per result
  - REVIEWER: presentation_quality - Clear summary

- **Section: The Conceptual Takeaway**
  - "Optimality with limitations" as paradigm
  - What we learned: information determines speedup, gap is both bottleneck and barrier, same Grover speedup has different costs in different models
  - Gap as bridge: physics (energy), computation (runtime/hardness), information (NP-hard to compute)
  - New perspective: not "does AQO work?" but "when is gap information tractable?"
  - TODO: Frame as paradigm shift
  - REVIEWER: significance - Conceptual contribution matters

- **Section: Comparison with Circuit Model**
  - AQO vs Grover circuit: same $\tilde{O}(\sqrt{N/d_0})$ speedup
  - Different information requirements: Grover needs oracle access only, AQO needs $A_1$ to exponential precision
  - Asymmetry: Grover queries adaptively DURING execution; AQO needs schedule UPFRONT
  - Key insight: circuit gathers spectral info through queries as it runs; AQO must commit before evolution
  - This is a genuine model difference, not an artifact of analysis
  - TODO: Make asymmetry vivid
  - REVIEWER: significance - Important conceptual point

- **Section: What This Changes**
  - Implications for AQO research:
  - Evaluating proposals: not just "what is gap?" but "how hard to compute gap?"
  - New question: from "can AQO be fast?" to "when is $A_1$ tractable?"
  - Experimental: scheduling needs $A_1$ or adaptive measurement, deviations may be fundamental
  - TODO: Connect to practical AQO/annealing
  - REVIEWER: significance - Practical relevance

- **Section: Original Contributions (Chapter 9)**
  - Context: extends Guo-An 2025's gap-informed baseline to uninformed/partial/adaptive regimes
  - Summary of extensions:
    1. Separation Theorem: $T_{\text{uninformed}} / T_{\text{informed}} \geq (s_R - s_L) / \Delta_*$, $\Omega(2^{n/2})$, LEAN complete
    2. Partial Information: $T(\epsilon) = T_{\inf} \cdot \Theta(\max(1, \epsilon/\delta_{A_1}))$, linear, LEAN complete
    3. Measure Condition: $T = \Theta(1/\Delta_*^{3-2/\alpha})$, dichotomy FALSE, LEAN complete
    4. Robust Schedules: hedging constant-factor, LEAN partial
    5. Adaptive Schedules: $O(n)$ measurements suffice, LEAN partial
  - Ignorance taxonomy: no info (exponential), intermediate (linear in $\epsilon$), bounded (constant), quantum measurement (logarithmic)
  - TODO: Connect back to central thesis
  - REVIEWER: originality - These are novel contributions

- **Section: The Formalization Standard (Chapter 10)**
  - What formalization achieved:
    1. Error detection: 5+ issues found (sign, hypotheses, direction)
    2. Verification: 27 axioms, 76+ theorems, 0 sorries
    3. Reproducibility: Lean compiles = proofs valid
  - Axiom boundary: external foundations, gap bounds (parametric spectral), novel math fully proved
  - TODO: Advocate for formalization in QC
  - REVIEWER: significance - Formalization contribution

- **Section: Open Problems**
  - Research directions:
    1. Structured instances: when is $A_1$ efficiently computable? (planted SAT, specific graphs)
    2. Noise models: decoherence effects on tradeoffs, open-system adiabatic
    3. Intermediate precision: what can polynomial precision achieve? useful regimes?
    4. Alternative paths: non-linear interpolations, catalyst Hamiltonians, counterdiabatic
    5. Quantum annealing: real devices use thermal, what does analysis say?
    6. Ultimate question: is there a family where AQO beats circuits? (needs tractable $A_1$)
  - TODO: Be specific about what is open
  - REVIEWER: significance - Guide future work

- **Section: Final Remarks**
  - What we set out to do: explain UAQO deeply, broader context, extend, verify
  - What we achieved: complete exposition, information characterization, Lean with errors fixed, unified perspective
  - Central message: AQO matches Grover but optimality requires NP-hard info, "optimality with limitations", gap bridges physics/computation/information
  - For reader: understand what AQO can and cannot do, tools to analyze instances, know open questions
  - TODO: End with central insight
  - REVIEWER: presentation_quality - Strong closing
