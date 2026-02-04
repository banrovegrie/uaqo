# Unstructured Adiabatic Quantum Optimization

My master's thesis on Unstructured Adiabatic Quantum Optimization, supervised by Shantanav Chakraborty. Built on the published paper [Unstructured Adiabatic Quantum Optimization: Optimality with Limitations](https://arxiv.org/abs/2411.05736) (Braida, Chakraborty, Chaudhuri, Cunningham, Menavlikar, Novo, Roland, 2025).

Make sure that the way this thesis would be written is satisfactory to Prof. Shantanav Chakraborty (check `taste/` for papers by him). We also aim to beat the baseline expectations of the theses we have with us in `taste/` (of Zeeshan Ahmed and Ronald de Wolf).

## Thesis Architecture

This thesis aims to be a single coherent path from first principles to the main results of arXiv:2411.05736, and to the extensions in `src/experiments/`. The structure follows three design principles:

| Principle | What it forces | How it shows up here |
|---|---|---|
| Lead with the puzzle | The reader should know what is at stake before any machinery appears | Chapter 1 opens with the paradox (optimal runtime vs hard-to-achieve optimality), states scope, and frontloads the results map |
| Treat computation as physics | "Runtime" is not the only resource; precision and control matter | Chapter 2 frames computation as controlled dynamics, setting up the later precision/hardness theme |
| Make theorems the skeleton | Every chapter should have a clear statement/proof/discussion cadence | Chapters 5-9 follow the paper's spine: model -> spectrum -> schedule -> hardness -> beyond |

### Reading paths

| If you are... | Suggested path | What you can skip on first pass |
|---|---|---|
| New to QC/AQC | 1 -> 2 -> 3 -> 4 -> 5 -> 6 -> 7 -> 8 -> 9 -> 10 | None |
| Comfortable with QC, new to AQC/AQO | 1 -> 4 -> 5 -> 6 -> 7 -> 8 -> 9 -> 10 | Most of 2-3 (keep Grover as the baseline) |
| Comfortable with AQC basics, here for the paper | 1 -> 5 -> 6 -> 7 -> 8 -> 9 -> 10 | Most of 2-4 (keep 4.3-4.6 for schedule and gap framing) |
| Here for the limitations story | 1 -> 7.5-7.6 -> 8 -> 9 -> 10 | Most of 2-6 after you know the model and what $A_1$ is |

### Parts

| Part | Chapters | Purpose |
|---|---|---|
| I. Framing | 1 | Hook, scope, results map, running example |
| II. Foundations | 2-4 | Physics/computation lens, QC baseline (Grover), adiabatic theorem -> algorithm |
| III. Core technical story | 5-7 | Unstructured AQO model, spectral analysis, optimal schedule and runtime |
| IV. The information barrier | 8-9 | What optimality requires knowing; NP/#P hardness; robust/adaptive responses |
| V. Closing | 10 | Synthesis, open problems, what to take away |

## Table of Contents (proposed; 10 main chapters match `src/main.tex`)

### Frontmatter

| Item | Purpose |
|---|---|
| Epigraph | One-line theme: "what computation can ask of physics" |
| Abstract | Results + what they mean (no suspense) |
| Acknowledgments | Intellectual debts, not just names |
| Notation and conventions | Symbols, norms, asymptotic notation, error parameters |
| List of Theorems / Algorithms / Figures | Navigation for technical readers |

### Part I: Framing

### Chapter 1: Introduction

| Section | Content |
|---------|---------|
| 1.1 The puzzle | Why "ground states as answers" is both natural and suspicious as computation |
| 1.2 The running baseline | Unstructured search as the canonical target (Grover in circuits, Roland-Cerf in AQC) |
| 1.3 Model preview | AQO as a restricted AQC model; what is fixed vs what is a choice |
| 1.4 Results map (frontloaded) | (i) optimal schedule exists, (ii) computing what it needs is NP-hard, (iii) exact knowledge is #P-hard |
| 1.5 Scope and ground rules | Closed system, Hamiltonian model, what "optimality" means, what is out of scope |
| 1.6 How to read | Multiple paths, how later chapters depend on earlier ones |

### Part II: Foundations

### Chapter 2: Physics and Computation

| Section | Content |
|---------|---------|
| 2.1 Computation as dynamics | What an "algorithm" means when evolution is continuous-time physics |
| 2.2 Resources beyond time | Precision, energy scales, and what it means to specify a Hamiltonian or schedule |
| 2.3 Linearity and superposition | Why linear evolution supports interference and makes spectral structure meaningful |
| 2.4 Adiabaticity as timescale separation | Intuition for slow driving and why gaps control transitions |
| 2.5 Complexity and oracles | P/NP/#P at the level used later; query access models and promise problems |
| 2.6 The thesis lens | Precision as an information resource (foreshadowing Chapters 7-9) |

### Chapter 3: Quantum Computation

| Section | Content |
|---------|---------|
| 3.1 States and observables | Finite-dimensional QM, postulates in the form used later |
| 3.2 Composite systems | Tensor products, entanglement, reduced states (only what is needed) |
| 3.3 Circuits and query complexity | BQP and the oracle model as a clean baseline for "unstructured" |
| 3.4 Grover as geometry | The two-dimensional rotation picture and why it is optimal |
| 3.5 Amplitude amplification | The reusable abstraction: "find the good subspace" |
| 3.6 Complexity classes (minimal) | Only what will be referenced later (BQP, QMA, NP, #P) |

### Chapter 4: Adiabatic Quantum Computation

| Section | Content |
|---------|---------|
| 4.1 The model | Continuous-time Hamiltonian computation and the AQC promise |
| 4.2 Adiabatic theorem (one clean version) | What it guarantees, what it does not, and the error parameterization |
| 4.3 Schedules and the role of the gap | Why local schedules matter; how $g(s)$ enters runtime |
| 4.4 AQC as Grover (Roland-Cerf) | The canonical success case and what it teaches us |
| 4.5 Universality (what we need) | Equivalence to circuits at a high level; why AQO is more restricted |
| 4.6 Why gaps are hard | Avoided crossings, instance dependence, and what analysis must accomplish |
| 4.7 Related work | Only work that the later technical chapters will compare against |

### Part III: Core Technical Story (the paper's spine)

### Chapter 5: Adiabatic Quantum Optimization

| Section | Content |
|---------|---------|
| 5.1 AQO as a restriction | What is fixed in AQO (diagonal $H_z$) vs what we choose (schedule) |
| 5.2 Problem Hamiltonian data | Spectrum, degeneracies, and the parameters that matter later |
| 5.3 The interpolation studied | The specific $H(s)$ in the paper and why it is the clean unstructured testbed |
| 5.4 Symmetry reduction | From $2^n$ to the relevant subspace and what is lost/kept |
| 5.5 The eigenvalue equation | The central object that makes spectral analysis possible |
| 5.6 Roadmap for Chapters 6-7 | What we must prove about $g(s)$ to talk about optimal schedules |

### Chapter 6: Spectral Analysis

| Section | Content |
|---------|---------|
| 6.1 Spectral parameters | $A_p$, why $A_1$ is the lever, and what can/cannot be inferred from them |
| 6.2 Avoided crossing anatomy | $s^*$, $\delta_s$, $g_{\min}$, and what "unstructured" buys us |
| 6.3 The three-region strategy | Why one proof technique cannot cover all s |
| 6.4 Left region bound | Variational bound and its parameter dependence |
| 6.5 Window bound | How the minimum gap is localized and controlled |
| 6.6 Right region bound | Resolvent/Sherman-Morrison and the role of $\Delta$ |
| 6.7 Complete gap profile | A single picture the schedule analysis can plug into |

### Chapter 7: The Optimal Schedule

| Section | Content |
|---------|---------|
| 7.1 Local schedule | $ds/dt$ proportional to $g(s)^2$ and the error model |
| 7.2 Runtime as an integral | Why it splits into left/window/right contributions |
| 7.3 Main runtime theorem | Full parameter dependence and where each factor comes from |
| 7.4 Grover matching regime | Conditions under which the schedule achieves $\sim\sqrt{2^n/d_0}$ |
| 7.5 What this already assumes | Preview: locating $s^*$ (and thus $A_1$) to window scale precision |
| 7.6 Discussion | Why this is "optimality with limitations" even before hardness enters |

### Part IV: The Information Barrier and Beyond

### Chapter 8: Hardness of Optimality

| Section | Content |
|---------|---------|
| 8.1 The hidden requirement | Making the preview from 7.5 explicit as a computational task |
| 8.2 Formal access model | $A_1$ oracle and the precision regime the results quantify |
| 8.3 Reduction from 3-SAT | Encoding satisfiability into the needed spectral statistic |
| 8.4 NP-hardness theorem | Why even approximate optimality can hide NP-hard preprocessing |
| 8.5 Interpolation as amplification | Turning multiple approximate queries into a decision procedure |
| 8.6 #P-hardness theorem | Exact $A_1$ reveals full degeneracy data |
| 8.7 The asymmetry | Why the circuit model does not have the same "parameter knowledge" barrier |

### Chapter 9: Exploring the Hardness Barrier [THESIS EXTENSIONS]

| Section | Content |
|---------|---------|
| 9.1 A minimax lower bound | What happens when schedules are gap-uninformed (separation theorem) |
| 9.2 Robustness to uncertainty | Hedging when $s^*$ is only known to an interval |
| 9.3 Partial information tradeoff | How runtime degrades with imperfect knowledge (interpolation theorem) |
| 9.4 Adaptive schedules | Computing vs detecting; binary search with measurements; optimal measurement scaling |
| 9.5 Gap geometry refinements | When the local shape near $s^*$ changes the runtime law (measure condition) |
| 9.6 Synthesis | A unified "ignorance taxonomy": what costs exponential, what costs only logs or constants |

### Chapter 10: Conclusion

| Section | Content |
|---------|---------|
| 10.1 Results in one page | The trilogy and the conceptual takeaway: "optimality is an information question" |
| 10.2 What this changes | How to interpret AQO claims, and what "speedup" means when precision is a resource |
| 10.3 Lean status (optional) | What has been formalized, what assumptions remain |
| 10.4 Open problems | Structured instances, noise models, intermediate precision regimes, new schedule primitives |

### Appendices (planned, optional but useful for "first principles")

| Appendix | Purpose |
|---|---|
| A. Linear algebra and spectral facts | Statements used repeatedly (norms, perturbation, variational bounds) |
| B. Complexity and oracle basics | P/NP/#P, reductions, query models as used in Chapter 8 |
| C. Adiabatic theorem variants | One-page comparison of common formulations and their hypotheses |
| D. Notation index | Symbols and where they are first defined |
