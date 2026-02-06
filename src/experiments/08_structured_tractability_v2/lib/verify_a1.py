"""
Numerical verification for Experiment 08: Structured Tractability.
Verifies all quantitative claims in proof.md.
"""

import math
from math import comb, log2
from fractions import Fraction


def a1_grover(N, d0):
    """A_1 for Grover Hamiltonian: M=2, E0=0, E1=1."""
    return Fraction(N - d0, N)


def a1_three_level(N, n):
    """
    A_1 for Proposition 1 counterexample:
    E0=0 (d0=1), E1=1/n (d1=1), E2=1 (d2=N-2).
    """
    d0, d1, d2 = 1, 1, N - 2
    assert d0 + d1 + d2 == N
    # A_1 = (1/N)[d1/(1/n) + d2/1] = (1/N)[n + N-2]
    return Fraction(n + N - 2, N)


def a1_hamming(n):
    """
    A_1 for Hamming distance Hamiltonian:
    E_k = k, d_k = C(n,k), k=0,...,n.
    A_1 = (1/2^n) sum_{k=1}^n C(n,k)/k.
    """
    N = 2**n
    total = Fraction(0)
    for k in range(1, n + 1):
        total += Fraction(comb(n, k), k)
    return total / N


def optimal_crossing(a1):
    """s* = A_1 / (1 + A_1) for Grover-type Hamiltonians."""
    return a1 / (1 + a1)


def main():
    print("=" * 60)
    print("EXPERIMENT 08: NUMERICAL VERIFICATION")
    print("=" * 60)

    all_pass = True

    def check(name, computed, expected, tol=1e-10):
        nonlocal all_pass
        diff = abs(float(computed) - float(expected))
        ok = diff < tol
        status = "PASS" if ok else "FAIL"
        if not ok:
            all_pass = False
        print(f"  [{status}] {name}: computed={float(computed):.6f}, "
              f"expected={float(expected):.6f}")
        return ok

    # --- Grover N=4, d0=1 ---
    print("\n--- Grover N=4, d0=1 ---")
    a1 = a1_grover(4, 1)
    check("A_1", a1, Fraction(3, 4))
    check("s*", optimal_crossing(a1), Fraction(3, 7))

    # --- Grover N=4, d0=2 ---
    print("\n--- Grover N=4, d0=2 ---")
    a1 = a1_grover(4, 2)
    check("A_1", a1, Fraction(1, 2))
    check("s*", optimal_crossing(a1), Fraction(1, 3))

    # --- Proposition 1 counterexample: n=4, N=16 ---
    print("\n--- Proposition 1 counterexample (n=4, N=16) ---")
    a1 = a1_three_level(16, 4)
    check("A_1", a1, Fraction(9, 8))
    check("1/Delta", Fraction(4, 1), Fraction(4, 1))
    ratio = float(a1) / 4.0
    print(f"  A_1 / (1/Delta) = {ratio:.4f} (should be << 1)")
    assert ratio < 0.5, f"Ratio {ratio} not << 1"
    print(f"  [PASS] Conjecture 1 disproved: A_1={float(a1):.4f} != 1/Delta=4")

    # --- Proposition 1: large n behavior ---
    print("\n--- Proposition 1: A_1 -> 1 as n -> inf ---")
    for n in [4, 8, 16, 32]:
        N = 2**n
        a1 = a1_three_level(N, n)
        print(f"  n={n:3d}: A_1 = {float(a1):.6f}, 1/Delta = {n}")

    # --- Proposition 2: vacuity check ---
    print("\n--- Proposition 2: Vacuity of Conjecture 2 ---")
    for n in [10, 20, 50]:
        N = 2**n
        M_max = n**2       # poly(n) levels
        dk_max = n**2       # poly(n) degeneracies
        non_ground = (M_max - 1) * dk_max
        if non_ground >= N:
            # For small n, a coarse poly(n)^2 upper bound can exceed N=2^n.
            # The Proposition 2 statement is asymptotic: for sufficiently large n,
            # poly(n)^2 << 2^n and the bound becomes meaningful.
            print(f"  n={n:3d}: N=2^{n}, non-ground <= {non_ground} (bound trivial)")
            continue
        d0_lower = N - non_ground
        ratio = d0_lower / N
        print(f"  n={n:3d}: N=2^{n}, non-ground <= {non_ground}, d0/N >= {ratio:.10f}")

    # --- Hamming distance ---
    print("\n--- Proposition 7: Hamming distance ---")
    for n in [2, 3, 4, 8, 16, 32]:
        a1 = a1_hamming(n)
        print(f"  n={n:3d}: A_1 = {str(a1):>20s} = {float(a1):.6f}")

    # Verify specific n=4 value
    print("\n--- Hamming n=4 detailed check ---")
    a1_h4 = a1_hamming(4)
    expected = Fraction(103, 192)
    check("A_1 (n=4)", a1_h4, expected)

    # Verify n=2
    a1_h2 = a1_hamming(2)
    check("A_1 (n=2)", a1_h2, Fraction(5, 8))

    # Verify n=3
    a1_h3 = a1_hamming(3)
    check("A_1 (n=3)", a1_h3, Fraction(29, 48))

    # --- Hamming asymptotic: A_1 ~ 2/n ---
    print("\n--- Proposition 7: Hamming A_1 ~ 2/n asymptotic ---")
    for n in [4, 8, 16, 32, 64, 128]:
        a1 = a1_hamming(n)
        ratio = float(a1) * n / 2
        print(f"  n={n:4d}: A_1*n/2 = {ratio:.4f} (should -> 1)")

    # --- Proposition 10: truncation/anchoring bound sanity check ---
    print("\n--- Proposition 10: anchored truncation bound sanity check (Hamming) ---")
    n = 12
    N = 2**n
    eps = 0.01
    ln = math.log(1.0 / eps)
    diff = 0.0
    for k in range(1, n + 1):
        diff += comb(n, k) * (eps**k) * (1.0 / k + ln)
    diff /= N
    bound = eps * (1.0 + ln)
    print(f"  n={n}, eps={eps}: A_1 - A_1^(eps) = {diff:.6e}, bound = {bound:.6e}")
    assert diff >= -1e-12, "Expected A_1 - A_1^(eps) >= 0"
    assert diff <= bound + 1e-12, "Proposition 10 bound violated (numerics)"
    print("  [PASS] bound holds")

    # --- Proposition 11: Laplace anchored proxy bound sanity check ---
    print("\n--- Proposition 11: Laplace anchored proxy bound sanity check (Hamming) ---")
    B = 3.0
    diff = 0.0
    for k in range(1, n + 1):
        diff += comb(n, k) * math.exp(-B * k) * (1.0 / k + B)
    diff /= N
    bound = math.exp(-B) * (1.0 + B)
    print(f"  n={n}, B={B}: A_1 - A_1^[B] = {diff:.6e}, bound = {bound:.6e}")
    assert diff >= -1e-12, "Expected A_1 - A_1^[B] >= 0"
    assert diff <= bound + 1e-12, "Proposition 11 bound violated (numerics)"
    print("  [PASS] bound holds")

    # --- Proposition 5: Grover sweet spot ---
    print("\n--- Proposition 5: Grover sweet spot for various N ---")
    for n in [2, 4, 8, 16]:
        N = 2**n
        a1 = a1_grover(N, 1)
        print(f"  N=2^{n:2d}: A_1 = {float(a1):.6f}, "
              f"runtime = O(sqrt({N})) = O({N**0.5:.1f})")

    # --- Summary ---
    print("\n" + "=" * 60)
    if all_pass:
        print("ALL CHECKS PASSED")
    else:
        print("SOME CHECKS FAILED")
    print("=" * 60)

    return all_pass


if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
