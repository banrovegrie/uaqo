# UAQO Proofs Directory

Proof files for axioms defined in the main UAQO modules.

See the main [README.md](../../README.md) for:
- Complete axiom status and tracking
- Eliminated axioms list
- Formulation fixes applied
- Future work priorities

## Directory Structure

```
Proofs/
    Foundations/           Variational principle proofs
    Spectral/              Eigenvalue condition, Sherman-Morrison, A2 bounds
    Adiabatic/             Schedule properties
    Complexity/            SAT semantics, beta-modified Hamiltonian, Lagrange interpolation
    Mathlib/               Bridge lemmas for Finset arithmetic
    ProofVerify.lean       Master verification file - imports all proofs
```

## Key Proof Files

### Spectral/EigenvalueCondition.lean
Main eigenvalue characterization theorem for adiabatic Hamiltonian H(s).
- Uses `det_adiabaticHam_factored` from MatrixDetLemma
- Uses `resolvent_expectation_formula` for resolvent calculations
- Fully proved for degenerate eigenvalues (d_k > 1) and secular equation cases
- 2 sorries for non-degenerate case (d_k = 1) - theorem statement limitation

### Spectral/MatrixDetLemma.lean
Bridge file connecting our definitions to Mathlib's matrix determinant lemma.
- `outerProd_eq_replicateCol_mul_replicateRow`: our outerProd -> Mathlib form
- `dotProduct_star_eq_innerProd`: our innerProd -> Mathlib dotProduct
- Uses Mathlib's `det_add_replicateCol_mul_replicateRow` from SchurComplement

## Mathlib Dependencies

### Core Linear Algebra
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` - determinant definitions
- `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` - matrix inverse
- `Mathlib.LinearAlgebra.Matrix.SchurComplement` - rank-1 determinant lemma

### Inner Product Spaces
- `Mathlib.Analysis.InnerProductSpace.Basic` - inner product definitions
- `Mathlib.Analysis.InnerProductSpace.PiL2` - finite-dimensional spaces

### Complex Numbers
- `Mathlib.Data.Complex.Basic` - complex number operations
- `Mathlib.Data.Complex.Exponential` (deprecated, use Mathlib.Analysis.Complex.Exponential)

### Key Mathlib Theorems Used

| UAQO Lemma | Mathlib Theorem | Module |
|------------|-----------------|--------|
| matrix_det_lemma | `det_add_replicateCol_mul_replicateRow` | SchurComplement |
| det_one_add_outerProd | `det_one_add_replicateCol_mul_replicateRow` | SchurComplement |
| conj_mul' | `map_mul (starRingEnd C)` | star operations |
| conj_ofReal' | `Complex.conj_ofReal` | Complex.Basic |

## Architecture

The UAQO formalization uses custom definitions (Ket, Operator, outerProd, innerProd, applyOp)
to match physics notation and make proofs more readable. Bridge lemmas in this directory
connect these to Mathlib equivalents when needed for complex proofs.

Pattern: Custom Definition -> Bridge Lemma -> Mathlib Theorem -> Result
