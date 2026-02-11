# Chapter 3 and 4 Spines

Planning document. Delete after chapters are finalized.

## Chapter 3: The Search Frontier

### Central question
What computational model makes quantum speedup claims precise, and where
does unstructured search land?

### Spine (questions that determine order)
1. What does quantum mechanics provide as a computational substrate?
   (States, amplitudes, measurement, the exponential-vs-single-shot tension)
2. What operations are allowed between preparation and measurement?
   (Unitarity, Hamiltonians, spectral gaps)
3. How do we formalize "efficient quantum algorithm"?
   (Circuits, BQP, query complexity, oracle model)
4. What is the simplest non-trivial quantum speedup?
   (Grover as plane rotation in a huge space)
5. Is Grover optimal?
   (BBBV: yes. The frontier is closed.)
6. Does the model matter?
   (Farhi et al.: the barrier survives continuous time. Bridge to Ch4.)

### Recurring motif
Effective low-dimensional dynamics controlling exponentially large systems.
Grover reduces to 2D rotation. Adiabatic search reduces to a two-level
avoided crossing. Same structural idea, different physical implementation.

### What the reader can do after each section
- After S1: Understands why 2^n amplitudes do not give 2^n parallel computations
- After S2: Understands unitarity as probability conservation; knows what "spectral gap" means
- After S3: Can define BQP; understands query vs gate complexity
- After S4: Can derive Grover's runtime from the rotation angle
- After S5: Can explain why sqrt(N) is a barrier, not just a known algorithm

### Definitions needed (in order of appearance)
Qubit, n-qubit Hilbert space, amplitude expansion, entanglement,
global/relative phase, projective measurement, Born rule, density operator,
Hamiltonian, spectral decomposition, spectral gap, Schrodinger equation,
unitary evolution, time-ordered exponential, universal gate set, BQP,
promise problem, query complexity, oracle (standard + phase), Grover iterate,
marked/unmarked subspace, BBBV hybrid bound.

### Key equations to preserve (referenced by later chapters)
- State expansion: eq:ch3-state-expansion
- Born rule: eq:ch3-born-rule
- Spectral gap: eq:ch3-spectral-gap
- Schrodinger equation: eq:ch3-schrodinger
- Unitary evolution: eq:ch3-unitary-evolution
- Grover iterate: eq:ch3-grover-iterate
- Grover runtime: eq:ch3-grover-complexity
- BBBV bound: eq:ch3-bbbv-bound
- Closed frontier: eq:ch3-search-frontier

---

## Chapter 4: The Adiabatic Alternative

### Central question
Does continuous-time Hamiltonian evolution offer anything beyond circuits
for optimization, or does it just relocate the same difficulties?

### Spine
1. What is the adiabatic idea? (Ground-state tracking under slow deformation)
2. How slow must "slow" be? (Adiabatic theorem: the gap is the resource)
3. What controls the bottleneck? (Avoided crossings, two-level reduction)
4. Can adiabatic evolution match Grover? (Roland-Cerf: yes, for one marked item)
5. What is the catch? (Schedule design requires spectral information that
   may itself be hard to compute. Universality of model power does not
   remove information bottlenecks.)

### The twist
Roland-Cerf matches Grover's sqrt(N), but only because the gap profile
is analytically known. For general diagonal H_z, the crossing location,
width, and minimum gap all depend on the full spectral profile. Optimal
schedule design demands information that is, in general, computationally
hard to obtain. This is the thesis's central tension, set up here and
resolved across Chapters 5-8.

### Recurring motif (continued from Ch3)
Two-level effective dynamics. In Grover, it was span{|w>,|r>}. In
Roland-Cerf, it is the avoided crossing between instantaneous ground and
first excited states. Same structural reduction, now parameterized by a
continuous schedule variable s instead of a discrete iteration count k.

### Key equations to preserve
- AQO interpolation: eq:ch4-interpolation
- Schrodinger in s: eq:ch4-schrodinger-s
- JRS adiabatic bound: eq:ch4-jrs
- Local schedule rate: eq:ch4-local-rate
- Roland-Cerf gap: eq:ch4-rc-gap
- Roland-Cerf runtime: eq:ch4-rc-runtime
- Rank-one spectral formulas: eq:ch4-sstar, eq:ch4-deltas, eq:ch4-gmin
