# Literature Survey: Adaptive Strategies in AQO

## Executive Summary

Fundamental lower bounds on what adaptive/measurement-based strategies can achieve in AQO remain largely unexplored. This is a genuine gap in the literature.


## Key Papers

### Gap-Informed Adaptive Strategies

**Roland-Cerf 2002** - "Quantum Search by Local Adiabatic Evolution"
- Local schedule ds/dt = epsilon * g^2(t) achieves O(sqrt(N)) vs O(N) for linear schedule
- Requires knowing the gap function g(s) analytically
- Lower bound proven: T >= (epsilon/4) * sqrt(N) optimal for any schedule

**Guo-An 2025** - "Improved gap dependence in adiabatic state preparation"
- Power-law u'(s) ~ Delta^p with p in (1,2) achieves O(1/Delta_*) vs O(1/Delta_*^2)
- Requires "measure condition" on gap
- Acknowledges: "a priori knowledge on the spectral gap... is a QMA-hard computational task"
- Optimality: p=3/2 minimizes error functional under linear gap profiles

### Gap-Uninformed Adaptive Strategies

**Han-Park-Choi 2025** - "The Constant Speed Schedule"
- Segmented constant speed, path lengths from eigenstate overlaps "on the fly"
- Uses overlap measurements during evolution
- Achieves 1/Delta scaling numerically (Grover, molecules)
- NO fundamental limits proven

**Shingu-Hatomura 2025** - "Geometrical scheduling without energy spectra"
- Quantum adiabatic brachistochrone without spectrum info
- Uses counterdiabatic driving
- NO complexity analysis

**Matsuura et al. 2021** - Variational adiabatic (VAQC)
- Predictor-corrector framework
- NO fundamental limits

### Gap Oracle Model

**Jarret-Lackey-Liu-Wan 2018** - "QAO without heuristics"
- Assumes gap oracle Gamma with gamma_min = Theta(min_s Gamma(s))
- O(gamma_min^-1) time with O(log(1/gamma_min)) oracle queries
- CRITICAL: Assumes oracle exists, doesn't prove limits on constructing one


## Quantum Metrology and Estimation

**Pang et al. 2021** - "Adiabatic critical metrology cannot reach Heisenberg limit"
- Quantum Fisher information in adiabatic metrology cannot achieve 1/T scaling
- Critical slowing down is fundamental barrier
- Implication: time-precision tradeoff in adiabatic approaches


## Query Complexity

**Lin-Tong 2020** - "Near-optimal ground state preparation"
- Achieves optimal dependence on gap Delta and overlap gamma
- Reduction: unstructured search -> ground state preparation
- Key: query lower bounds via adversary method

**Spectral Gap Complexity 2025**
- Estimating spectral gap is P^{UQMA[log]}-hard
- Even approximate gap estimation is hard in general


## The Gap in Literature

### What IS Known
1. Local adiabatic optimal for unstructured search (Roland-Cerf)
2. Power-law p=3/2 optimal when gap is linear (Guo-An)
3. O(log(1/gamma_min)) oracle queries suffice (Jarret et al.)
4. Gap estimation is computationally hard

### What is NOT Known
1. NO lower bounds on number of measurements needed
2. NO information-theoretic bounds on learning gap function
3. NO query complexity for adaptive stopping
4. NO comparison in measurement-limited regime
5. NO proven tradeoff: given k measurements, what runtime achievable?


## Assessment

This is a NOVEL research direction because:
1. Existing work assumes oracles or full knowledge
2. No measurement complexity theorems exist
3. Natural extension of published hardness results
4. Connects quantum metrology + AQO complexity

Potential contributions:
1. Information-theoretic lower bound on gap estimation from measurements
2. Query-time tradeoff: T * k >= f(Delta)
3. Separation between measurement models
4. Prove poly(n) measurements cannot achieve optimal scheduling


## References

1. Roland-Cerf 2002: quant-ph/0107015
2. Guo-An 2025: arxiv:2512.10329
3. Han-Park-Choi 2025: arxiv:2510.01923
4. Shingu-Hatomura 2025: arxiv:2501.11846
5. Jarret et al. 2018: arxiv:1810.04686
6. Lin-Tong 2020: Quantum 4, 372
7. Spectral Gap Complexity 2025: arxiv:2503.02747
8. Pang et al. 2021: Quantum 5, 489
