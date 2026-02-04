# Key References for Gap-Uninformed Separation

## Must-Cite Papers

### For the Error Bounds

**Jansen-Ruskai-Seiler 2007**
- arXiv:quant-ph/0603175
- "Bounds for the adiabatic approximation with applications to quantum computation"
- Provides: Rigorous error bounds, gap dependence analysis
- Key result: Error ~ (1/tau) * ||H'||/g^2 + higher order terms

### For Optimal Informed Schedules

**Roland-Cerf 2002**
- arXiv:quant-ph/0107015
- "Quantum search by local adiabatic evolution"
- Provides: Local adiabatic evolution, O(sqrt(N)) for search
- Key insight: Adapting ds/dt to local gap is crucial

**Guo-An 2025**
- arXiv:2512.10329
- "Improved gap dependence in adiabatic state preparation"
- Provides: Power-law p=3/2 is optimal, achieves O(1/Delta)
- Key limitation: Requires gap knowledge (QMA-hard)

### For the NP-Hardness

**UAQO Paper (Chaudhuri et al. 2025)**
- arXiv:2411.05736, Quantum Journal 2025
- "Unstructured Adiabatic Quantum Optimization: Optimality with Limitations"
- Provides: A_1 computation is NP-hard (approx), #P-hard (exact)
- Key result: s* = A_1/(A_1+1), delta_s = Theta(Delta*)

### For Distinguishing Adaptive Methods

**Han-Park-Choi 2025**
- arXiv:2510.01923
- "The Constant Speed Schedule for Adiabatic State Preparation"
- Provides: O(1/Delta) without prior spectral knowledge
- Key distinction: ADAPTIVE (measures during evolution)

## Secondary References

### Foundational

**van Dam-Mosca-Vazirani 2001**
- arXiv:quant-ph/0206003
- Shows gap-informed variable delay achieves quadratic speedup

**Farhi et al. 2000**
- arXiv:quant-ph/0001106
- Original adiabatic quantum computation proposal

### Lower Bound Techniques

**Garcia-Pintos et al. 2024**
- arXiv:2410.14779
- Quantum speed limit lower bounds (schedule-independent)

**Bennett et al. 1997**
- SIAM J. Computing 26(5)
- Oracle lower bounds for quantum search

## Papers That Do NOT Prove Our Result

These were checked and do not contain minimax bounds for uninformed schedules:

1. Nayak et al. 2011 (adaptive probing)
2. Matsuura et al. 2021 (variational, constructive)
3. Shingu-Hatomura 2025 (geometrical, constructive)
4. Albash-Lidar 2018 review (no uninformed analysis)
