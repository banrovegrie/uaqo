# Hedging Theorem Lean Formalization

Lean 4 formalization of the Hedging Theorem for adiabatic quantum optimization.

## Main Result

When the crossing position is known to lie in `[u_L, u_R]`, a hedging schedule
achieves error ratio `(u_R - u_L)` compared to uniform schedule.

For `[u_L, u_R] = [0.4, 0.8]`, this means 60% error reduction.

## Files

- `HedgingTheorem/Basic.lean`: Core definitions and numerical verification
- `HedgingTheorem/Proofs.lean`: Formal algebraic proofs
- `HedgingTheorem.lean`: Root module
- `Main.lean`: Executable that runs verification

## Building

```bash
lake build
```

## Running Verification

```bash
lake env lean --run Main.lean
```

Output:
```
Hedging Theorem Verification
============================

1. Constraint Verification:
   R = 10.000000: constraint satisfied = true
   R = 100.000000: constraint satisfied = true
   R = 1000.000000: constraint satisfied = true

2. Asymptotic Ratio (should approach w = 0.4):
   R = 10.000000: ratio = 0.699853
   R = 100.000000: ratio = 0.498990
   R = 1000.000000: ratio = 0.431153
   R = 10000.000000: ratio = 0.409817
   R = 100000.000000: ratio = 0.403100

3. Optimal Velocity (v_slow - w should approach 0):
   R = 10.000000: v_slow = 0.554919, v_slow - w = 0.154919
   R = 100.000000: v_slow = 0.448990, v_slow - w = 0.048990
   R = 1000.000000: v_slow = 0.415492, v_slow - w = 0.015492
   R = 10000.000000: v_slow = 0.404899, v_slow - w = 0.004899
```

## Key Theorems

1. **Schedule Constraint** (`constraint_algebra`):
   When `v_fast = (1-w)*v_slow/(v_slow-w)`, we have `w/v_slow + (1-w)/v_fast = 1`.

2. **Optimal Velocity** (`optimal_velocity_identity`):
   The optimal slow velocity is `v_slow = w + sqrt((1-w)*w/R)`.

3. **Main Theorem** (`main_theorem_convergence`):
   As `R -> infinity`, the error ratio `E_hedge/E_unif -> w`.

4. **Practical Result** (`corollary_04_08`):
   For `w = 0.4`, hedging achieves 60% error reduction.

## Verification Status

- No `sorry` statements
- No custom `axiom` declarations
- All proofs compile without errors
- Numerical verification confirms theoretical predictions

## Mathematical Content

See `proof.md` in the parent directory for the full mathematical treatment.
