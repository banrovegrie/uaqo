"""
Approximate A_1 from Laplace partition-function evaluations Z(beta).

This is a concrete implementation of Proposition 11:

  A_1 = (1/N) ∫_0^∞ (Z(beta) - d0) d beta

and the anchored, truncated proxy

  A_1^[B] = (1/N) ∫_0^B (Z(beta) - Z(B)) d beta,
  0 <= A_1 - A_1^[B] <= e^{-B} (1+B)   (integer spectra, Delta_min >= 1).

We demonstrate the idea on a toy structured instance (OR-chain CSP). We compute:
  (1) exact A_1 from the full cost distribution (via variable elimination)
  (2) A_1^[B] via midpoint-rule quadrature using only Z(beta) evaluations
and compare them, along with the truncation bound.
"""

from __future__ import annotations

import math
from typing import List, Tuple

from variable_elimination_a1 import (
    a1_from_distribution,
    distribution_from_zpoly,
    make_cost_factor,
    zpoly_via_elimination,
)


def z_beta_from_distribution(d: List[int], beta: float) -> float:
    # Z(beta) = sum_q d_q e^{-beta q}
    acc = 0.0
    for q, dq in enumerate(d):
        if dq:
            acc += dq * math.exp(-beta * q)
    return acc


def approx_a1_laplace_anchored(
    z_beta, *, N: int, B: float, num_steps: int
) -> float:
    """
    Approximate A_1^[B] = (1/N) ∫_0^B (Z(beta) - Z(B)) d beta
    by the midpoint rule on a uniform grid in beta.
    """
    h = B / num_steps
    zB = z_beta(B)
    total = 0.0
    for i in range(num_steps):
        beta_mid = (i + 0.5) * h
        total += z_beta(beta_mid) - zB
    return (total * h) / N


def main() -> None:
    n = 18
    clauses = [(i, i + 1) for i in range(n - 1)]
    m = len(clauses)
    max_deg = m

    def clause_cost(bits_ij: Tuple[int, int]) -> int:
        a, b = bits_ij
        return 0 if (a or b) else 1

    factors = [make_cost_factor([i, j], clause_cost, max_deg=max_deg) for (i, j) in clauses]
    poly = zpoly_via_elimination(factors, list(range(n)), max_deg=max_deg)
    d = distribution_from_zpoly(poly, max_deg=max_deg)
    a1_exact, E0, d0 = a1_from_distribution(d)
    if E0 != 0:
        raise RuntimeError("Expected satisfiable example to have E0=0.")

    N = 2**n

    def z_beta(beta: float) -> float:
        return z_beta_from_distribution(d, beta)

    # Choose B so that truncation is very small in practice.
    B = 6.0
    num_steps = 6000
    a1_hat_B = approx_a1_laplace_anchored(z_beta, N=N, B=B, num_steps=num_steps)

    trunc_bound = math.exp(-B) * (1.0 + B)  # Delta_min >= 1 (integer energies)
    err = abs(a1_hat_B - float(a1_exact))

    print("=" * 72)
    print("EXPERIMENT 08: A_1 APPROX FROM Z(beta) (ANCHORED LAPLACE QUADRATURE)")
    print("=" * 72)
    print(f"Instance: OR-chain, n={n}, m={m}, N=2^{n}")
    print(f"E0={E0}, d0={d0}")
    print(f"B: {B}")
    print(f"Truncation bound (Prop 11): <= {trunc_bound:.6e}")
    print(f"Quadrature steps: {num_steps}")
    print(f"Exact A_1 (integer energies): {float(a1_exact):.6f} = {a1_exact}")
    print(f"Estimated A_1^[B]: {a1_hat_B:.6f}")
    print(f"|A_1 - A_1^[B]|: {err:.6f}")


if __name__ == "__main__":
    main()

