"""
Numerical verification for Experiment 08: Structured Tractability.
Verifies all quantitative claims in proof.md.
"""

import math
from math import comb, log2
from fractions import Fraction
from itertools import product


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


def prop15_family_a1(B):
    """
    Proposition 15 families:
      U: masses (d0,d1/B,dB)/N = (1/2,1/8,3/8)
      S: masses (d0,d1/B,dcB)/N = (1/2,1/16,7/16), cB = 7B/(B^2+6)
    Returns exact-rational A_1 values and cB.
    """
    cB = Fraction(7 * B, B * B + 6)
    a1_u = Fraction(1, 8) * B + Fraction(3, 8) * Fraction(1, B)
    a1_s = Fraction(1, 16) * B + Fraction(7, 16) * Fraction(1, cB)
    return a1_u, a1_s, cB


def prop15_partition_gap(B):
    """
    Returns Z_U(B)/N, Z_S(B)/N, and absolute gap using closed forms.
    """
    cB = 7.0 * B / (B * B + 6.0)
    z_u = 0.5 + 0.125 * math.exp(-1.0) + 0.375 * math.exp(-B * B)
    z_s = 0.5 + 0.0625 * math.exp(-1.0) + 0.4375 * math.exp(-B * cB)
    return z_u, z_s, abs(z_u - z_s)


def prop15_bruteforce_check(n, B):
    """
    Brute-force sanity check of Proposition 15 construction on n bits.
    Energies are defined directly from the formulas in proof.md.
    """
    if n < 4:
        raise ValueError("n must be at least 4.")
    cB = Fraction(7 * B, B * B + 6)
    N = 2**n

    # Distributions keyed by exact rational energies.
    d_u = {}
    d_s = {}

    for bits in product([0, 1], repeat=n):
        x1, x2, x3, x4 = bits[0], bits[1], bits[2], bits[3]

        if x1 == 0:
            e_u = Fraction(0, 1)
            e_s = Fraction(0, 1)
        else:
            e_u = Fraction(1, B) if (x2 == 0 and x3 == 0) else Fraction(B, 1)
            e_s = Fraction(1, B) if (x2 == 0 and x3 == 0 and x4 == 0) else cB

        d_u[e_u] = d_u.get(e_u, 0) + 1
        d_s[e_s] = d_s.get(e_s, 0) + 1

    # A_1 from brute-force distributions
    def a1_from_dist(d):
        total = Fraction(0, 1)
        for e, cnt in d.items():
            if e == 0:
                continue
            total += Fraction(cnt, 1) * Fraction(1, 1) / e
        return total / N

    a1_u = a1_from_dist(d_u)
    a1_s = a1_from_dist(d_s)

    # Partition values at beta=B
    def z_over_n(d):
        acc = 0.0
        for e, cnt in d.items():
            acc += (cnt / N) * math.exp(-float(B * e))
        return acc

    z_u = z_over_n(d_u)
    z_s = z_over_n(d_s)
    return a1_u, a1_s, z_u, z_s, d_u, d_s


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

    # --- Proposition 15: reverse-bridge obstruction ---
    print("\n--- Proposition 15: reverse-bridge obstruction ---")
    for B in [3, 4, 6, 10]:
        a1_u, a1_s, cB = prop15_family_a1(B)
        check(f"A_1(U)=A_1(S) at B={B}", a1_u, a1_s)
        assert Fraction(1, B) < cB < Fraction(B, 1), "Expected 1/B < cB < B"
        z_u, z_s, gap = prop15_partition_gap(B)
        print(
            f"  B={B:2d}: Z_U(B)/N={z_u:.6f}, Z_S(B)/N={z_s:.6f}, "
            f"gap={gap:.6f}"
        )
        assert gap > 0.01, "Expected order-one low-temperature partition separation"

    # Stress sweep over a wide B-range to guard against arithmetic mistakes.
    min_gap = float("inf")
    min_gap_B = None
    for B in range(3, 5001):
        a1_u, a1_s, cB = prop15_family_a1(B)
        assert a1_u == a1_s, "Expected exact A_1 match for all B >= 3"
        assert Fraction(1, B) < cB < Fraction(B, 1), "Expected 1/B < cB < B"
        _, _, gap = prop15_partition_gap(B)
        if gap < min_gap:
            min_gap = gap
            min_gap_B = B
        assert gap > 0.01, "Expected |Z_U(B)-Z_S(B)|/N > 1/100"
    print(
        f"  Sweep B=3..5000: min gap = {min_gap:.6f} at B={min_gap_B}"
    )

    # brute-force structural check on a concrete n
    n = 8
    B = 3
    a1_u_bf, a1_s_bf, z_u_bf, z_s_bf, d_u, d_s = prop15_bruteforce_check(n, B)
    a1_u_cf, a1_s_cf, _ = prop15_family_a1(B)
    check(f"Brute-force A_1(U), n={n}, B={B}", a1_u_bf, a1_u_cf)
    check(f"Brute-force A_1(S), n={n}, B={B}", a1_s_bf, a1_s_cf)
    gap_bf = abs(z_u_bf - z_s_bf)
    print(
        f"  Brute-force n={n}, B={B}: |Z_U(B)-Z_S(B)|/N = {gap_bf:.6f}"
    )
    assert gap_bf > 0.01, "Brute-force Proposition 15 gap should exceed 1/100"
    print("  [PASS] Proposition 15 obstruction numerically validated")

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
