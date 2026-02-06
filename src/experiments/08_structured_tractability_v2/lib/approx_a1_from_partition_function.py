"""
Approximate A_1 from partition-function evaluations Z(t).

This is a concrete implementation of the reduction idea in Proposition 10:
  A_1 = (1/N) ∫_0^1 (Z(t)-d0)/t dt
and the observation that for additive approximation we can avoid d0 by anchoring at
Z(ε) and integrating only over t∈[ε,1].

We implement a simple log-grid quadrature:
  let u = ln t, so dt/t = du, and integrate over u∈[ln ε, 0].

This script validates correctness by comparing against an exact A_1 computed from
the full cost distribution (via variable elimination / Z(t) coefficients).
"""

from __future__ import annotations

import math
from fractions import Fraction
from typing import Callable, List, Tuple

from variable_elimination_a1 import (
    a1_from_distribution,
    distribution_from_zpoly,
    make_cost_factor,
    zpoly_via_elimination,
)


def z_from_distribution(d: List[int], t: float) -> float:
    # Compute Z(t) = sum_q d_q t^q in double precision.
    # For the toy instances we use, this is stable enough.
    acc = 0.0
    pow_t = 1.0
    for q, dq in enumerate(d):
        if dq:
            acc += dq * pow_t
        pow_t *= t
    return acc


def choose_epsilon_for_eta(eta: float) -> float:
    # Solve ε(1+ln(1/ε)) <= eta/4 by a conservative explicit choice.
    # For small eta, η/(8 ln(8/η)) is safe up to constants; we keep it simple.
    if not (0.0 < eta < 1.0):
        raise ValueError("eta must be in (0,1).")
    return min(0.25, eta / (8.0 * (1.0 + math.log(8.0 / eta))))


def approx_a1_from_z(
    z: Callable[[float], float],
    *,
    N: int,
    m: int,
    eta: float,
    num_steps: int,
) -> float:
    """
    Approximate A_1 for an integer-spectrum model with E0=0 using:

      A_1 ≈ (1/N) ∫_{ε}^{1} (Z(t) - Z(ε))/t dt

    by a midpoint rule on a uniform grid in u = ln t.
    """
    eps = choose_epsilon_for_eta(eta)
    u0 = math.log(eps)
    u1 = 0.0
    h = (u1 - u0) / num_steps
    z_eps = z(eps)

    total = 0.0
    for i in range(num_steps):
        u_mid = u0 + (i + 0.5) * h
        t = math.exp(u_mid)
        total += (z(t) - z_eps)
    integral_est = total * h  # since dt/t = du
    return integral_est / N


def main() -> None:
    # Toy structured instance: OR-chain CSP (bounded width).
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

    a1_exact_int, E0, _ = a1_from_distribution(d)
    if E0 != 0:
        raise RuntimeError("Expected satisfiable example to have E0=0.")

    # Normalize energy as E = cost/m so that A_1(normalized) = m * A_1(integer).
    a1_exact = float(a1_exact_int) * m
    N = 2**n

    def z_normalized(t: float) -> float:
        # Z_norm(t) corresponds to energies cost (integers): Z(t) = sum d_q t^q.
        # For normalized energy E=cost/m, Z_beta(beta)=sum exp(-beta*cost/m) = Z(t) with t=exp(-beta/m).
        # Here we keep the integer-spectrum Z(t) and scale A1 by m at the end.
        return z_from_distribution(d, t)

    eta = 0.01
    eps = choose_epsilon_for_eta(eta)
    num_steps = 2000
    a1_hat_int = approx_a1_from_z(z_normalized, N=N, m=m, eta=eta, num_steps=num_steps)
    a1_hat = a1_hat_int * m

    trunc_bound = eps * (1.0 + math.log(1.0 / eps)) * m  # scaling by m for normalized energy
    err = abs(a1_hat - a1_exact)

    print("=" * 72)
    print("EXPERIMENT 08: A_1 APPROX FROM Z(t) (LOG-GRID QUADRATURE)")
    print("=" * 72)
    print(f"Instance: OR-chain, n={n}, m={m}, N=2^{n}")
    print(f"Target eta: {eta}")
    print(f"Chosen eps: {eps:.3e}")
    print(f"Truncation bound (Prop 10, scaled): <= {trunc_bound:.6f}")
    print(f"Quadrature steps: {num_steps}")
    print(f"Exact A_1 (normalized): {a1_exact:.6f}")
    print(f"Estimated A_1 (normalized): {a1_hat:.6f}")
    print(f"Absolute error: {err:.6f}")


if __name__ == "__main__":
    main()

