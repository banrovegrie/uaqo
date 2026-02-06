"""
Monte Carlo estimation of A_1 under the promise that E0 is known.

This script demonstrates Proposition 9 on a toy structured instance:
an OR-chain CSP with integer energies (normalized by m).

We compute:
  (1) the exact A_1 via variable elimination (Z(t) coefficients -> A_1)
  (2) an empirical estimate via uniform sampling
and compare them.
"""

from __future__ import annotations

import random
from fractions import Fraction
from typing import Tuple

from variable_elimination_a1 import (
    a1_from_distribution,
    distribution_from_zpoly,
    make_cost_factor,
    zpoly_via_elimination,
)


def main() -> None:
    random.seed(0)

    n = 20
    clauses = [(i, i + 1) for i in range(n - 1)]
    m = len(clauses)
    max_deg = m

    def clause_cost(bits_ij: Tuple[int, int]) -> int:
        a, b = bits_ij
        return 0 if (a or b) else 1

    factors = [make_cost_factor([i, j], clause_cost, max_deg=max_deg) for (i, j) in clauses]
    order = list(range(n))

    poly = zpoly_via_elimination(factors, order, max_deg=max_deg)
    d = distribution_from_zpoly(poly, max_deg=max_deg)
    a1_exact_int, E0_int, _ = a1_from_distribution(d)
    if E0_int != 0:
        raise RuntimeError("Expected satisfiable OR-chain example to have E0=0.")

    # Normalized energy: E(x)=cost/m, so Delta_min=1/m and 1/(E-E0)=m/cost.
    def g(cost: int) -> Fraction:
        return Fraction(0) if cost == 0 else Fraction(m, cost)

    # Sampling
    T = 20000
    total = Fraction(0)
    for _ in range(T):
        x = [random.getrandbits(1) for _ in range(n)]
        cost = sum(clause_cost((x[i], x[j])) for (i, j) in clauses)
        total += g(cost)

    a1_hat = total / T

    # Exact A_1 for normalized energy is m times the integer-spectrum A_1.
    a1_exact = a1_exact_int * m

    err = abs(float(a1_hat) - float(a1_exact))

    print("=" * 72)
    print("EXPERIMENT 08: MONTE CARLO A_1 ESTIMATION DEMO")
    print("=" * 72)
    print(f"Instance: OR-chain, n={n}, m={m}")
    print(f"Exact A_1 (normalized energy): {float(a1_exact):.6f} = {a1_exact}")
    print(f"Sampled A_1 (T={T}): {float(a1_hat):.6f} = {a1_hat}")
    print(f"Absolute error: {err:.6f}")


if __name__ == "__main__":
    main()
