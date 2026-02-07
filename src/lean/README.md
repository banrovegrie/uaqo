# UAQO: Lean 4 Formalization

Formal verification of "Unstructured Adiabatic Quantum Optimization: Optimality with Limitations" (arXiv:2411.05736) in Lean 4 with Mathlib4.

## Build

```bash
lake update
lake build
```

## Status: 0 sorry, 15 explicit axioms, ~32 genuine theorems

Every assumption is a Lean `axiom` with a paper citation, visible via
`#print axioms`. Zero sorry, zero vacuous `True` proofs. The spectral gap
lower bound (Proposition 1) is an explicit hypothesis via `FullSpectralHypothesis`.

## Structure

```
UAQO/
    Foundations/
        Basic.lean              Qubit states, operators, norms
        HilbertSpace.lean       Inner products, Mathlib bridges
        Operators.lean          Hermitian operators, resolvents
        SpectralTheory.lean     Eigenvalues, spectral decomposition
        Qubit.lean              Qubit systems, tensor products
    Spectral/
        DiagonalHamiltonian.lean  Diagonal Hamiltonians, EigenStructure
        SpectralParameters.lean   A1, A2, avoided crossing, gap formulas
        AdiabaticHamiltonian.lean H(s) = -(1-s)|psi0><psi0| + s*Hz
        GapBounds.lean            Gap bounds, Sherman-Morrison
    Adiabatic/
        Hamiltonian.lean        Time-dependent Hamiltonians, schedules
        Schedule.lean           Local schedules, piecewise construction
        Theorem.lean            Adiabatic theorem, eigenpath traversal
        RunningTime.lean        Main Result 1, optimality
    Complexity/
        Basic.lean              Decision problems, polynomial time
        NP.lean                 NP, 3-SAT
        SharpP.lean             #P, counting problems, interpolation
        Hardness.lean           Main Results 2 and 3
    Proofs/
        Spectral/               Eigenvalue condition, gap bound proofs
        Complexity/             SAT semantics, Lagrange, beta-modified Ham
        Foundations/             Variational principle
        Adiabatic/              Schedule properties
        Mathlib/                Finset arithmetic bridge
    Test/
        Verify.lean             Compilation and paper correspondence tests
    Experiments/                Structured tractability, barrier circumvention
```

## Formalization Scope

The formalization captures the structure of the paper: definitions, theorem
statements, and type dependencies. The mathematical content splits into two
layers.

### Layer 1: Genuine Mathematical Proofs

| Theorem | Technique |
|---------|-----------|
| `resolvent_distance_to_spectrum` | Frobenius positivity |
| `isEigenvalue_iff_det_eq_zero` | Standard linear algebra |
| `eigenvalue_condition` | Matrix Determinant Lemma |
| `isEigenvalue_is_mathlib_eigenvalue` | Eigenbasis expansion + Parseval |
| `spectral_gap_pair_exists` | Finset.min' |
| `variational_principle` | Spectral decomposition |
| `lagrange_interpolation` | Mathlib Lagrange.interpolate |
| `berlekamp_welch` | Error-correcting structure |
| `A1_numerator_polynomial_in_beta` | (X+1)^(M-1) + Finset even/odd bijection |
| `betaModified_A1_diff_pos` | Finset.sum_nbij |
| `threeSAT_satisfiable_iff_degPositive` | Encoding correctness |
| `extractDegeneracy_correct` | Paper's extraction formula (line 912) |
| `numeratorPoly_eval` | Lagrange evaluation identity |
| `secularFun_strictMono_on_interval` | IVT + monotonicity |
| `exists_unique_root_below_ground` | IVT + uniqueness |
| `theorem3_coupled_nonconstant` | Explicit 1-qubit construction |
| `theorem4_multisegment_rigidity` | Two-instance contradiction |

Plus ~40 supporting lemmas (Sherman-Morrison, A2 bounds, Cauchy-Schwarz,
measurement probability bounds, schedule monotonicity, etc.).

### Layer 2: Theorems Proved from Axioms

These theorems invoke axioms for their proof content. Each axiom
represents a formalization boundary beyond Lean 4/Mathlib scope
and carries a paper citation.

| Theorem | Axiom(s) Used | Paper Reference |
|---------|---------------|-----------------|
| `adiabaticTheorem` | `adiabatic_evolution_bound` | Jansen et al. (2007), Thm 3 |
| `adiabaticTheorem_localSchedule` | `adiabaticTheorem_localSchedule_bound` | Roland-Cerf (2002) |
| `phaseRandomization` | `phaseRandomization_bound` | Cunningham et al. (2023) |
| `eigenpath_traversal` | `eigenpath_evolution_bound` | Jansen et al. (2007), Cor. |
| `mainResult1` | `mainResult1_evolution` | arXiv:2411.05736, Thm 1 |
| `mainResult2` | `gareyJohnsonEncoding` | arXiv:2411.05736, Thm 2 |
| `sharpThreeSAT_complete` | axioms 5 + 6 | Valiant (1979) |
| `theorem3_coupled_nonconstant` | explicit construction | Experiment 12, Thm 3 |
| `theorem4_multisegment_rigidity` | explicit construction | Experiment 12, Thm 4 |

`mainResult2` is a genuine proof: it uses `gareyJohnsonEncoding` to obtain
the Garey-Johnson Hamiltonian (E_0 = 0 iff SAT), then proves algebraically
that the two-query difference D is zero iff E_0 = 0 (`twoQuery_sat`,
`twoQuery_unsat`). `mainResult3` is fully genuine (no axiom dependencies
beyond propext/Classical.choice/Quot.sound).

## FullSpectralHypothesis

The paper's Proposition 1 (spectral gap lower bound) is an explicit hypothesis:

```lean
structure FullSpectralHypothesis (es : EigenStructure n M) (hM : M >= 2) where
  cond : spectralConditionForBounds es hM
  gap  : forall s E0 E1, ... -> E1 - E0 >= minimumGap es hM
```

The paper proves this from secular equation analysis. The formalization assumes
it. Infrastructure exists (secular equation continuity, strict monotonicity,
IVT, root uniqueness) but the perturbation-theoretic analysis is not completed.

## Faithfulness to Paper

| Item | Paper Reference | Rating |
|------|----------------|--------|
| H(s) = -(1-s)\|psi_0><psi_0\| + s H_z | Eq. 1 | EXACT |
| A_p = (1/N) sum d_k/(E_k-E_0)^p | Eq. 5 | EXACT |
| s* = A_1/(A_1+1) | Eq. 6 | EXACT |
| delta_s = 2/(A_1+1)^2 sqrt(d_0 A_2/N) | Eq. 7 | EXACT |
| g_min = (1-2eta) * 2A1/(A1+1) * sqrt(d0/(A2*N)) | Eq. 311 (eta=0.1) | EXACT |
| EigenStructure | Definition 1 | EXACT |
| Gap region formulas | Eqs. 317, 347 | EXACT |
| Extraction: d_k = N*P(-2Delta_k)/prod(Delta_l-Delta_k) | Line 912 | EXACT |
| mainResult1 statement | Theorem 1 | EXACT |
| mainResult2 (two-query protocol) | Theorem 2 | GENUINE |
| mainResult3 extraction | Theorem 3 | GENUINE |

## Verification

```bash
grep -rn "^axiom " UAQO/           # 15 axioms
grep -rn "sorry" UAQO/ --include="*.lean" | grep -v "comment\|--"  # 0 results
grep -rn ": True " UAQO/ --include="*.lean"                        # 0 results
lake build 2>&1 | tail -1           # "Build completed successfully (2541 jobs)."
```

## References

- Unstructured Adiabatic Quantum Optimization (arXiv:2411.05736)
- Roland-Cerf local adiabatic search (arXiv:quant-ph/0107015)
- Mathlib4: https://leanprover-community.github.io/mathlib4_docs/
