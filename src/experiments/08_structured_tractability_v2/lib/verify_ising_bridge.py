"""
Numerical checks for Proposition 13 and Proposition 14 in Experiment 08.

Proposition 13 check:
- Build a small ferromagnetic Ising chain with integer couplings.
- Compute exact A_1 for normalized energies.
- Estimate A_1 from noisy multiplicative partition-function evaluations.
- Verify the observed error stays below the analytic bound.

Proposition 14 check:
- Verify the exact crossing-shift identity numerically.
- Verify the stated linear sensitivity bound in the admissible error regime.
"""

from __future__ import annotations

import math
import random
from itertools import product
from typing import Dict, List


def ising_chain_distribution(n: int, coupling: int = 1) -> Dict[str, object]:
    """
    Ferromagnetic chain with spins in {-1,+1} and cost
      C(sigma) = sum_i J * (1 - sigma_i sigma_{i+1}) / 2.
    """
    if n < 2:
        raise ValueError("n must be >= 2.")
    if coupling <= 0:
        raise ValueError("coupling must be positive.")

    edges = [(i, i + 1) for i in range(n - 1)]
    W = coupling * len(edges)
    d = [0] * (W + 1)

    for sigma in product([-1, 1], repeat=n):
        cost = 0
        for i, j in edges:
            cost += coupling * ((1 - sigma[i] * sigma[j]) // 2)
        d[cost] += 1

    return {"d": d, "W": W, "N": 2**n}


def a1_normalized_from_distribution(d: List[int], W: int) -> float:
    """
    A_1 for normalized energies E = C / W, with E0 = 0 for the chain.
    """
    N = sum(d)
    total = 0.0
    for c, dc in enumerate(d):
        if c == 0 or dc == 0:
            continue
        total += dc * (W / c)
    return total / N


def z_beta_normalized(d: List[int], W: int, beta: float) -> float:
    # Z(beta) = sum_c d_c exp(-beta * c / W)
    return sum(dc * math.exp(-beta * c / W) for c, dc in enumerate(d) if dc)


def estimate_a1_from_noisy_partition(
    d: List[int], W: int, *, B: float, K: int, mu: float, rng: random.Random
) -> float:
    """
    Midpoint estimator of A_1^[B] using multiplicative-noisy Z(beta) calls.
    """
    N = sum(d)
    h = B / K

    def noisy(beta: float) -> float:
        z = z_beta_normalized(d, W, beta)
        rel = rng.uniform(-mu, mu)
        return z * (1.0 + rel)

    zB_hat = noisy(B)
    total = 0.0
    for i in range(K):
        beta_mid = (i + 0.5) * h
        total += noisy(beta_mid) - zB_hat
    return (h * total) / N


def prop13_bound_terms(d: List[int], W: int, *, B: float, K: int, mu: float) -> Dict[str, float]:
    N = sum(d)
    rho0 = d[0] / N
    delta_min = 1.0 / W  # integer spectrum with normalization by W

    tail = (1.0 - rho0) * math.exp(-B * delta_min) * (B + 1.0 / delta_min)
    oracle = 2.0 * mu * B
    quadrature = (B * B) / (2.0 * K)  # R = 1 for normalized energies
    total = tail + oracle + quadrature

    return {
        "rho0": rho0,
        "delta_min": delta_min,
        "tail": tail,
        "oracle": oracle,
        "quadrature": quadrature,
        "total": total,
    }


def check_proposition_13() -> None:
    print("=" * 72)
    print("PROPOSITION 13 CHECK: FERROMAGNETIC ISING BOUND")
    print("=" * 72)

    instance = ising_chain_distribution(n=8, coupling=1)
    d = instance["d"]
    W = instance["W"]
    N = instance["N"]

    a1_exact = a1_normalized_from_distribution(d, W)

    B = 35.0
    K = 30000
    mu = 0.002
    trials = 20
    rng = random.Random(7)

    bound = prop13_bound_terms(d, W, B=B, K=K, mu=mu)
    max_err = 0.0

    for _ in range(trials):
        a1_hat = estimate_a1_from_noisy_partition(d, W, B=B, K=K, mu=mu, rng=rng)
        err = abs(a1_hat - a1_exact)
        max_err = max(max_err, err)
        if err > bound["total"] + 1e-12:
            raise AssertionError(
                f"Observed error {err:.6e} exceeds bound {bound['total']:.6e}."
            )

    print(f"n=8 chain, N={N}, W={W}")
    print(f"Exact A_1 (normalized): {a1_exact:.8f}")
    print(f"B={B}, K={K}, mu={mu}, trials={trials}")
    print(
        "Bound terms: "
        f"tail={bound['tail']:.6e}, "
        f"oracle={bound['oracle']:.6e}, "
        f"quadrature={bound['quadrature']:.6e}"
    )
    print(f"Total bound: {bound['total']:.6e}")
    print(f"Max observed |error|: {max_err:.6e}")
    print("[PASS] Proposition 13 inequality holds on all trials.")


def check_proposition_14() -> None:
    print("\n" + "=" * 72)
    print("PROPOSITION 14 CHECK: CROSSING SENSITIVITY")
    print("=" * 72)

    for A in [0.2, 0.75, 2.0, 5.0]:
        for sign in (-1.0, 1.0):
            eps = sign * 0.4 * (1.0 + A)  # safely inside |eps| <= (1+A)/2
            s = A / (1.0 + A)
            s_hat = (A + eps) / (1.0 + A + eps)
            lhs = abs(s_hat - s)
            rhs = 2.0 * abs(eps) / ((1.0 + A) ** 2)
            if lhs > rhs + 1e-12:
                raise AssertionError(
                    f"Sensitivity bound failed for A={A}, eps={eps}: {lhs} > {rhs}"
                )

    # Check the paper-scale substitution:
    # eta_A1 = ((1+A1)^2 / 2) * delta_s = sqrt(d0 A2 / N)
    A1 = 0.75
    d0 = 1.0
    A2 = 1.0
    N = float(2**20)
    delta_s = 2.0 / ((1.0 + A1) ** 2) * math.sqrt(d0 * A2 / N)
    eta_required = ((1.0 + A1) ** 2) * delta_s / 2.0
    rhs = math.sqrt(d0 * A2 / N)
    if abs(eta_required - rhs) > 1e-12:
        raise AssertionError("Scale identity check failed.")

    print("[PASS] Numerical checks satisfy Proposition 14 bounds.")
    print(f"Sample scale check: eta_required={eta_required:.6e}, rhs={rhs:.6e}")


def main() -> None:
    check_proposition_13()
    check_proposition_14()
    print("\nALL CHECKS PASSED")


if __name__ == "__main__":
    main()
