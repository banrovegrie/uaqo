"""
Compute A_1 for integer-valued diagonal Hamiltonians via variable elimination.

This is a small, dependency-free demonstration of the "structured tractability"
route: if the energy function E(x) decomposes into local integer-valued terms and
admits a low-width elimination ordering (bounded treewidth / induced width), then we
can compute the full cost distribution (the coefficients d_k) and hence A_1 exactly.

The script validates correctness by comparing against brute force on toy instances.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Callable, Dict, Iterable, List, Sequence, Tuple


Poly = List[int]  # coefficients, Poly[j] is coeff of t^j


def poly_trim(poly: Poly, max_deg: int) -> Poly:
    return poly[: max_deg + 1] if len(poly) > max_deg + 1 else poly


def poly_add(a: Poly, b: Poly, *, max_deg: int) -> Poly:
    out_len = max(len(a), len(b))
    out = [0] * out_len
    for i in range(out_len):
        out[i] = (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
    return poly_trim(out, max_deg)


def poly_mul(a: Poly, b: Poly, *, max_deg: int) -> Poly:
    if not a or not b:
        return []
    out_len = min(len(a) + len(b) - 1, max_deg + 1)
    out = [0] * out_len
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            deg = i + j
            if deg > max_deg:
                break
            out[deg] += ai * bj
    return out


@dataclass(frozen=True)
class Factor:
    scope: Tuple[int, ...]
    table: Dict[Tuple[int, ...], Poly]


def make_cost_factor(
    scope: Sequence[int], cost_fn: Callable[[Tuple[int, ...]], int], *, max_deg: int
) -> Factor:
    scope_t = tuple(scope)
    table: Dict[Tuple[int, ...], Poly] = {}
    for bits in product([0, 1], repeat=len(scope_t)):
        cost = cost_fn(tuple(bits))
        if not (0 <= cost <= max_deg):
            raise ValueError(f"Cost {cost} out of range [0,{max_deg}] for {bits}.")
        poly = [0] * (cost + 1)
        poly[cost] = 1
        table[tuple(bits)] = poly
    return Factor(scope=scope_t, table=table)


def factor_multiply(f1: Factor, f2: Factor, *, max_deg: int) -> Factor:
    union_scope = tuple(sorted(set(f1.scope) | set(f2.scope)))
    pos = {v: i for i, v in enumerate(union_scope)}
    idx1 = [pos[v] for v in f1.scope]
    idx2 = [pos[v] for v in f2.scope]

    table: Dict[Tuple[int, ...], Poly] = {}
    for bits in product([0, 1], repeat=len(union_scope)):
        key1 = tuple(bits[i] for i in idx1)
        key2 = tuple(bits[i] for i in idx2)
        table[tuple(bits)] = poly_mul(f1.table[key1], f2.table[key2], max_deg=max_deg)
    return Factor(scope=union_scope, table=table)


def factor_sum_out(f: Factor, var: int, *, max_deg: int) -> Factor:
    if var not in f.scope:
        raise ValueError(f"Variable {var} not in scope {f.scope}.")
    pos = f.scope.index(var)
    new_scope = f.scope[:pos] + f.scope[pos + 1 :]

    table: Dict[Tuple[int, ...], Poly] = {}
    for bits_rest in product([0, 1], repeat=len(new_scope)):
        total: Poly = [0]
        for v in (0, 1):
            bits_full = list(bits_rest)
            bits_full.insert(pos, v)
            total = poly_add(total, f.table[tuple(bits_full)], max_deg=max_deg)
        table[tuple(bits_rest)] = total
    return Factor(scope=new_scope, table=table)


def zpoly_via_elimination(
    factors: Iterable[Factor], elimination_order: Sequence[int], *, max_deg: int
) -> Poly:
    active: List[Factor] = list(factors)
    free_multiplier = 1  # accounts for variables that appear in no factor (binary domain)
    for var in elimination_order:
        bucket = [f for f in active if var in f.scope]
        if not bucket:
            free_multiplier *= 2
            continue
        active = [f for f in active if var not in f.scope]
        combined = bucket[0]
        for f in bucket[1:]:
            combined = factor_multiply(combined, f, max_deg=max_deg)
        combined = factor_sum_out(combined, var, max_deg=max_deg)
        active.append(combined)

    if not active:
        return [1]
    combined = active[0]
    for f in active[1:]:
        combined = factor_multiply(combined, f, max_deg=max_deg)
    if combined.scope != ():
        raise RuntimeError(f"Elimination incomplete; remaining scope {combined.scope}.")
    poly = combined.table[()]
    if free_multiplier != 1:
        poly = [c * free_multiplier for c in poly]
    return poly


def distribution_from_zpoly(poly: Poly, *, max_deg: int) -> List[int]:
    out = poly_trim(poly, max_deg)
    if len(out) < max_deg + 1:
        out = out + [0] * (max_deg + 1 - len(out))
    return out


def a1_from_distribution(d: Sequence[int]) -> Tuple[Fraction, int, int]:
    N = sum(d)
    if N == 0:
        raise ValueError("Empty distribution.")
    E0 = next(k for k, c in enumerate(d) if c > 0)
    d0 = d[E0]
    total = Fraction(0)
    for k, c in enumerate(d):
        if c == 0 or k <= E0:
            continue
        total += Fraction(c, k - E0)
    return total / N, E0, d0


def brute_force_distribution(n: int, cost_fn: Callable[[Tuple[int, ...]], int], *, max_deg: int) -> List[int]:
    d = [0] * (max_deg + 1)
    for bits in product([0, 1], repeat=n):
        cost = cost_fn(tuple(bits))
        d[cost] += 1
    return d


def brute_force_a1(n: int, cost_fn: Callable[[Tuple[int, ...]], int], *, max_deg: int) -> Fraction:
    d = brute_force_distribution(n, cost_fn, max_deg=max_deg)
    a1, _, _ = a1_from_distribution(d)
    return a1


def main() -> None:
    print("=" * 72)
    print("EXPERIMENT 08: VARIABLE ELIMINATION DEMO (Z(t) -> A_1)")
    print("=" * 72)

    # Example 1: a chain of OR clauses (bounded width).
    n = 8
    clauses = [(i, i + 1) for i in range(n - 1)]
    max_deg = len(clauses)

    def clause_cost(bits_ij: Tuple[int, int]) -> int:
        a, b = bits_ij
        return 0 if (a or b) else 1

    factors = [
        make_cost_factor([i, j], clause_cost, max_deg=max_deg) for (i, j) in clauses
    ]

    # A natural elimination order for a chain has small induced width.
    order = list(range(n))

    def total_cost(bits: Tuple[int, ...]) -> int:
        return sum(clause_cost((bits[i], bits[j])) for (i, j) in clauses)

    poly = zpoly_via_elimination(factors, order, max_deg=max_deg)
    d_dp = distribution_from_zpoly(poly, max_deg=max_deg)
    d_bf = brute_force_distribution(n, total_cost, max_deg=max_deg)

    ok_dist = d_dp == d_bf
    a1_dp, E0, d0 = a1_from_distribution(d_dp)
    a1_bf = brute_force_a1(n, total_cost, max_deg=max_deg)
    ok_a1 = a1_dp == a1_bf

    print("\n--- Example 1: OR-chain CSP ---")
    print(f"n={n}, m={len(clauses)}, elimination width ~ 2 (by construction)")
    print(f"E0={E0}, d0={d0}, A_1={float(a1_dp):.6f} = {a1_dp}")
    print(f"[{'PASS' if ok_dist else 'FAIL'}] distribution matches brute force")
    print(f"[{'PASS' if ok_a1 else 'FAIL'}] A_1 matches brute force")

    if not (ok_dist and ok_a1):
        raise SystemExit(1)

    # Example 2: two overlapping parity constraints (still low width).
    n = 6
    max_deg = 2

    def parity_cost(bits_abc: Tuple[int, int, int]) -> int:
        a, b, c = bits_abc
        return 0 if ((a ^ b ^ c) == 0) else 1

    factors = [
        make_cost_factor([0, 1, 2], parity_cost, max_deg=max_deg),
        make_cost_factor([2, 3, 4], parity_cost, max_deg=max_deg),
    ]
    order = [0, 1, 3, 4, 2, 5]  # eliminates non-shared vars first

    def total_cost2(bits: Tuple[int, ...]) -> int:
        return parity_cost((bits[0], bits[1], bits[2])) + parity_cost((bits[2], bits[3], bits[4]))

    poly = zpoly_via_elimination(factors, order, max_deg=max_deg)
    d_dp = distribution_from_zpoly(poly, max_deg=max_deg)
    d_bf = brute_force_distribution(n, total_cost2, max_deg=max_deg)

    ok_dist = d_dp == d_bf
    a1_dp, E0, d0 = a1_from_distribution(d_dp)
    a1_bf = brute_force_a1(n, total_cost2, max_deg=max_deg)
    ok_a1 = a1_dp == a1_bf

    print("\n--- Example 2: overlapping parity constraints ---")
    print(f"n={n}, m=2, elimination order chosen to keep width small")
    print(f"E0={E0}, d0={d0}, A_1={float(a1_dp):.6f} = {a1_dp}")
    print(f"[{'PASS' if ok_dist else 'FAIL'}] distribution matches brute force")
    print(f"[{'PASS' if ok_a1 else 'FAIL'}] A_1 matches brute force")

    if not (ok_dist and ok_a1):
        raise SystemExit(1)

    print("\nALL CHECKS PASSED")


if __name__ == "__main__":
    main()
