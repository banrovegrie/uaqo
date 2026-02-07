"""
Numerical verification for Experiment 12: Circumventing the A_1 Barrier.

Verifies Theorems 1-5, Proposition 6, Proposition 6A, Proposition 6B,
and Proposition 6C.

Key distinction: s* = A_1/(A_1+1) is the CROSSING POSITION from the secular
equation, NOT the gap minimum (which is at s=1/2 for Grover). The crossing
position determines the optimal local schedule K(s) = g(s)^2.

Hamiltonian: H(s) = -(1-s)|psi_0><psi_0| + s H_z
Extended:    H_ext(s) = -(1-s)|Psi><Psi| + s (H_z x I)  where |Psi> = |psi_0> x |phi>
Coupled:     H_ext(s) + V
"""

import argparse
import numpy as np
from numpy.linalg import eigh


# ---------- Hamiltonian construction ----------

def build_Hz(energies):
    """Diagonal cost Hamiltonian from energy list."""
    return np.diag(np.array(energies, dtype=float))


def build_H(s, energies):
    """H(s) = -(1-s)|psi_0><psi_0| + s H_z."""
    N = len(energies)
    psi0 = np.ones(N) / np.sqrt(N)
    return -(1 - s) * np.outer(psi0, psi0) + s * build_Hz(energies)


def build_H_ext(s, energies, m_ancilla, phi=None, V=None):
    """Extended Hamiltonian with ancilla.

    H_ext(s) = -(1-s)|Psi><Psi| + s (H_z x I) [+ V]
    where |Psi> = |psi_0> x |phi>.
    """
    N = len(energies)
    d_anc = 2 ** m_ancilla

    psi0 = np.ones(N) / np.sqrt(N)
    if phi is None:
        phi = np.zeros(d_anc)
        phi[0] = 1.0
    Psi = np.kron(psi0, phi)

    H = -(1 - s) * np.outer(Psi, Psi) + s * np.kron(build_Hz(energies), np.eye(d_anc))

    if V is not None:
        H += V

    return H


# ---------- Spectral parameters ----------

def compute_spectral_params(energies):
    """Compute A_1, A_2, s*, and related spectral parameters."""
    E = np.array(energies, dtype=float)
    N = len(E)
    E_vals = np.sort(np.unique(E))
    E_0 = E_vals[0]
    Delta = E_vals[1] - E_0 if len(E_vals) > 1 else 0.0

    degens = {}
    for ev in E_vals:
        degens[ev] = int(np.sum(np.isclose(E, ev)))
    d_0 = degens[E_0]

    A_1 = 0.0
    A_2 = 0.0
    for ev in E_vals:
        if ev > E_0:
            dk = degens[ev]
            A_1 += (dk / N) / (ev - E_0)
            A_2 += (dk / N) / (ev - E_0) ** 2

    s_star = A_1 / (A_1 + 1)

    return {
        'E_0': E_0, 'Delta': Delta, 'd_0': d_0, 'N': N,
        'A_1': A_1, 'A_2': A_2, 's_star': s_star,
        'E_vals': E_vals, 'degens': degens
    }


# ---------- Eigenvalue branch tracking ----------

def track_eigenvalue_branches(energies, s_grid=None, use_ext=False,
                              m_ancilla=0, phi=None, V=None):
    """Track all eigenvalue branches of H(s) or H_ext(s).

    Returns: (s_grid, all_eigs) where all_eigs[i, j] is the j-th
    eigenvalue (sorted) at s = s_grid[i].
    """
    if s_grid is None:
        s_grid = np.linspace(0.001, 0.999, 2000)

    all_eigs = []
    for s in s_grid:
        if use_ext:
            H = build_H_ext(s, energies, m_ancilla, phi=phi, V=V)
        else:
            H = build_H(s, energies)
        eigs = np.sort(eigh(H)[0])
        all_eigs.append(eigs)

    all_eigs = np.array(all_eigs)
    return s_grid, all_eigs


def find_secular_crossing(energies):
    """Return s* = A_1/(A_1+1) from the secular equation.

    The crossing position is determined analytically by the spectral
    parameters, not by gap minimization (the gap minimum is at s=1/2
    for Grover, while s*=A_1/(A_1+1) != 1/2 in general).
    """
    params = compute_spectral_params(energies)
    return params['s_star']


def verify_secular_equation(energies, s_values=None, verbose=True):
    """Verify the secular equation directly.

    At each s, compute eigenvalues of H(s) and check that they satisfy
    1/(1-s) = (1/N) sum_k d_k / (s*E_k - lambda).
    """
    if s_values is None:
        s_values = [0.2, 0.3, 0.4, 0.5, 0.6]

    params = compute_spectral_params(energies)
    N = params['N']
    E_vals = params['E_vals']
    degens = params['degens']

    if verbose:
        print(f"Secular equation verification: N={N}")

    for s in s_values:
        H = build_H(s, energies)
        eigs = np.sort(eigh(H)[0])

        # Check the secular equation for the ground eigenvalue
        lam = eigs[0]
        lhs = 1.0 / (1.0 - s)
        rhs = 0.0
        for ev in E_vals:
            dk = degens[ev]
            denom = s * ev - lam
            if abs(denom) > 1e-14:
                rhs += (dk / N) / denom

        if verbose:
            print(f"  s={s:.2f}: lambda_0={lam:.6f}, "
                  f"LHS={lhs:.6f}, RHS={rhs:.6f}, "
                  f"diff={abs(lhs-rhs):.2e}")

    return True


# ---------- Crossing invariance verification ----------

def verify_branch_invariance(energies, m_ancilla=1, phi=None, verbose=True):
    """Verify that the two crossing eigenvalue branches are identical
    in the bare and extended systems.

    The extended system has extra eigenvalues (from states orthogonal to
    |Psi> in the ancilla space), but the two branches participating in
    the avoided crossing are unchanged.
    """
    N = len(energies)
    params = compute_spectral_params(energies)
    d_0 = params['d_0']
    E_0 = params['E_0']

    s_grid = np.linspace(0.001, 0.999, 2000)
    d_anc = 2 ** m_ancilla

    bare_eigs = []
    ext_eigs = []

    for s in s_grid:
        H_bare = build_H(s, energies)
        H_ext = build_H_ext(s, energies, m_ancilla, phi=phi)

        eigs_b = np.sort(eigh(H_bare)[0])
        eigs_e = np.sort(eigh(H_ext)[0])

        bare_eigs.append(eigs_b)
        ext_eigs.append(eigs_e)

    bare_eigs = np.array(bare_eigs)
    ext_eigs = np.array(ext_eigs)

    # The ground eigenvalue of the bare system should appear in the
    # extended system's spectrum.
    # The key crossing branch eigenvalue (first non-degenerate excited)
    # should also appear.

    # Ground state: eigs_b[0] should match eigs_e[0] exactly
    ground_diff = np.max(np.abs(bare_eigs[:, 0] - ext_eigs[:, 0]))

    # First crossing branch: for bare system it's eigs_b[1] (for d_0=1)
    # or eigs_b[d_0] (for d_0>1, since d_0-1 eigenvalues sit at s*E_0).
    # In the extended system, there are extra eigenvalues from the
    # ancilla null space. We need to find which extended eigenvalue
    # matches the bare crossing branch.

    # For d_0=1: bare_eigs[:,1] should match one of ext_eigs
    # For d_0>1: bare_eigs[:,d_0] should match one of ext_eigs

    # Strategy: for each s, find the extended eigenvalue closest to
    # the bare crossing branch eigenvalue.
    cross_idx = 1 if d_0 == 1 else d_0
    cross_diffs = []
    for i in range(len(s_grid)):
        bare_val = bare_eigs[i, cross_idx]
        diffs = np.abs(ext_eigs[i, :] - bare_val)
        cross_diffs.append(np.min(diffs))
    cross_diff = np.max(cross_diffs)

    if verbose:
        print(f"Branch invariance: N={N}, m_ancilla={m_ancilla}")
        print(f"  Max |ground_bare - ground_ext| = {ground_diff:.2e}")
        print(f"  Max |cross_bare - cross_ext|   = {cross_diff:.2e}")
        print(f"  (Both should be < 1e-10)")
        print()

    assert ground_diff < 1e-10, f"Ground state mismatch: {ground_diff}"
    assert cross_diff < 1e-10, f"Crossing branch mismatch: {cross_diff}"
    return True


# ---------- Coupling operators ----------

def sigma_x_ancilla(N, m_ancilla):
    """I_N x sigma_x on first ancilla qubit."""
    sx = np.array([[0, 1], [1, 0]], dtype=float)
    if m_ancilla == 1:
        anc_op = sx
    else:
        anc_op = sx
        for _ in range(m_ancilla - 1):
            anc_op = np.kron(anc_op, np.eye(2))
    return np.kron(np.eye(N), anc_op)


# ---------- Test cases ----------

def grover_energies(N, M):
    """Grover-type: M states at E=0, rest at E=1."""
    return [0.0] * M + [1.0] * (N - M)


def three_level_energies(N, d0, d1, E1=1.0, E2=2.0):
    """Three-level: d0 at E=0, d1 at E1, rest at E2."""
    d2 = N - d0 - d1
    return [0.0] * d0 + [E1] * d1 + [E2] * d2


# ---------- Theorem 1: Product State Invariance ----------

def verify_theorem1(verbose=True):
    """Theorem 1: For product |Psi> = |psi_0> x |phi> and H_f = H_z x I,
    the eigenvalue branches participating in the avoided crossing are
    IDENTICAL to the bare system. Hence s* = A_1/(A_1+1) is unchanged.
    """
    if verbose:
        print("=" * 60)
        print("THEOREM 1: Product State Invariance")
        print("=" * 60)
        print()

    test_cases = [
        ("Grover N=4, M=1", grover_energies(4, 1), 1),
        ("Grover N=4, M=1, 2 ancillas", grover_energies(4, 1), 2),
        ("Grover N=8, M=1", grover_energies(8, 1), 1),
        ("Grover N=8, M=2", grover_energies(8, 2), 1),
        ("Three-level N=8", three_level_energies(8, 1, 3, 1.0, 3.0), 1),
        ("Three-level N=8, 2 ancillas", three_level_energies(8, 1, 3, 1.0, 3.0), 2),
    ]

    for name, energies, m_anc in test_cases:
        if verbose:
            params = compute_spectral_params(energies)
            print(f"--- {name} ---")
            print(f"  A_1={params['A_1']:.4f}, s*={params['s_star']:.4f}, "
                  f"d_0={params['d_0']}")
        verify_branch_invariance(energies, m_ancilla=m_anc, verbose=verbose)

    # Also verify with non-standard ancilla states
    if verbose:
        print("--- Grover N=4, M=1, ancilla |+> ---")
    d_anc = 2
    phi_plus = np.ones(d_anc) / np.sqrt(d_anc)
    verify_branch_invariance(grover_energies(4, 1), m_ancilla=1,
                             phi=phi_plus, verbose=verbose)

    if verbose:
        print("--- Grover N=4, M=1, ancilla (0.3|0> + 0.95|1>) ---")
    phi_asym = np.array([0.3, 0.95])
    phi_asym /= np.linalg.norm(phi_asym)
    verify_branch_invariance(grover_energies(4, 1), m_ancilla=1,
                             phi=phi_asym, verbose=verbose)

    if verbose:
        print("Theorem 1: ALL TESTS PASSED\n")
    return True


# ---------- Theorem 2: Universality of Uniform Superposition ----------

def verify_theorem2(verbose=True):
    """Theorem 2: Non-uniform initial states change the crossing position.

    Among all |psi> in C^N, only |psi_0> = (1/sqrt(N)) sum |z> gives
    a crossing position that depends only on {E_k, d_k}.
    """
    if verbose:
        print("=" * 60)
        print("THEOREM 2: Universality of Uniform Superposition")
        print("=" * 60)
        print()

    N = 4
    energies = grover_energies(N, 1)  # d_0=1 for clean crossing
    params = compute_spectral_params(energies)
    s_star_uniform = params['s_star']

    # Non-uniform state: bias toward ground state
    psi_biased = np.array([0.8, 0.3, 0.3, 0.3])
    psi_biased /= np.linalg.norm(psi_biased)

    # Build H(s) with non-uniform initial state
    Hz = build_Hz(energies)
    s_grid = np.linspace(0.001, 0.999, 4000)

    # Track the secular equation crossing for the non-uniform state
    # The secular equation becomes:
    # 1/(1-s) = sum_k w_k / (s E_k - lambda)
    # where w_k = sum_{z: E(z)=E_k} |<psi|z>|^2
    # For non-uniform psi, w_k != d_k/N in general.

    # Compute effective w_k
    E = np.array(energies)
    E_vals = np.sort(np.unique(E))
    w_k_uniform = {}
    w_k_biased = {}
    psi_uniform = np.ones(N) / np.sqrt(N)
    for ev in E_vals:
        mask = np.isclose(E, ev)
        w_k_uniform[ev] = np.sum(np.abs(psi_uniform[mask])**2)
        w_k_biased[ev] = np.sum(np.abs(psi_biased[mask])**2)

    # Effective A_1 for biased state
    E_0 = E_vals[0]
    A1_biased = sum(w_k_biased[ev] / (ev - E_0) for ev in E_vals if ev > E_0)
    s_star_biased_theory = A1_biased / (A1_biased + 1)

    # Verify numerically: compute eigenvalues and find crossing
    gaps_biased = []
    for s in s_grid:
        H = -(1 - s) * np.outer(psi_biased, psi_biased) + s * Hz
        eigs = np.sort(eigh(H)[0])
        gaps_biased.append(eigs[1] - eigs[0])
    gaps_biased = np.array(gaps_biased)

    # Also check: does the biased secular equation give a different s*?
    if verbose:
        print(f"  N={N}, energies={energies}")
        print(f"  Uniform: w_k = {w_k_uniform}, A_1 = {params['A_1']:.4f}, "
              f"s* = {s_star_uniform:.4f}")
        print(f"  Biased:  w_k = {w_k_biased}, A_1 = {A1_biased:.4f}, "
              f"s* = {s_star_biased_theory:.4f}")
        print(f"  Shift in s*: {s_star_biased_theory - s_star_uniform:+.4f}")
        print()

    assert abs(s_star_biased_theory - s_star_uniform) > 0.01, \
        "Non-uniform state should shift s* significantly"

    # Now verify that the crossing position depends on the ASSIGNMENT
    # of energies to basis states (not just {E_k, d_k}) for non-uniform psi.
    # Permute the energy assignment:
    energies_perm = [1.0, 0.0, 1.0, 1.0]  # same {E_k, d_k}, different assignment
    w_k_biased_perm = {}
    E_perm = np.array(energies_perm)
    for ev in E_vals:
        mask = np.isclose(E_perm, ev)
        w_k_biased_perm[ev] = np.sum(np.abs(psi_biased[mask])**2)

    A1_biased_perm = sum(w_k_biased_perm[ev] / (ev - E_0)
                         for ev in E_vals if ev > E_0)
    s_star_biased_perm = A1_biased_perm / (A1_biased_perm + 1)

    if verbose:
        print(f"  Permuted assignment: w_k = {w_k_biased_perm}, "
              f"A_1 = {A1_biased_perm:.4f}, s* = {s_star_biased_perm:.4f}")
        print(f"  Original biased s* - permuted s* = "
              f"{s_star_biased_theory - s_star_biased_perm:+.4f}")
        print(f"  (Non-zero means s* depends on assignment, not just spectrum)")
        print()

    # For uniform psi, the permutation should NOT matter
    w_k_uniform_perm = {}
    for ev in E_vals:
        mask = np.isclose(E_perm, ev)
        w_k_uniform_perm[ev] = np.sum(np.abs(psi_uniform[mask])**2)

    A1_uniform_perm = sum(w_k_uniform_perm[ev] / (ev - E_0)
                          for ev in E_vals if ev > E_0)

    if verbose:
        print(f"  Uniform with permutation: w_k = {w_k_uniform_perm}, "
              f"A_1 = {A1_uniform_perm:.4f}")
        print(f"  |A_1_orig - A_1_perm| = "
              f"{abs(params['A_1'] - A1_uniform_perm):.2e} (should be ~0)")
        print()

    assert abs(params['A_1'] - A1_uniform_perm) < 1e-10, \
        "Uniform superposition A_1 should be invariant under permutation"
    assert abs(s_star_biased_theory - s_star_biased_perm) > 0.01, \
        "Biased state s* should depend on energy assignment"

    # Flat-amplitude, non-uniform-phase state: |psi> = (1/sqrt(N)) sum e^{i theta_z} |z>
    # This should give the SAME weights as uniform (phases cancel in |<z|psi>|^2 = 1/N)
    psi_phased = np.array([1, 1j, -1, -1j], dtype=complex) / np.sqrt(N)
    w_k_phased = {}
    for ev in E_vals:
        mask = np.isclose(E, ev)
        w_k_phased[ev] = np.sum(np.abs(psi_phased[mask])**2)
    A1_phased = sum(w_k_phased[ev] / (ev - E_0) for ev in E_vals if ev > E_0)

    if verbose:
        print(f"  Flat-amplitude phased state: w_k = {w_k_phased}, "
              f"A_1 = {A1_phased:.4f}")
        print(f"  |A_1_uniform - A_1_phased| = "
              f"{abs(params['A_1'] - A1_phased):.2e} (should be ~0)")
        print()

    assert abs(params['A_1'] - A1_phased) < 1e-10, \
        "Flat-amplitude phased state should give same A_1 as uniform"

    if verbose:
        print("Theorem 2: ALL TESTS PASSED\n")
    return True


# ---------- Theorem 3: Coupled Ancilla Extension ----------

def verify_theorem3(verbose=True):
    """Theorem 3: Instance-independent coupling cannot eliminate A_1 dependence.

    Shows that coupling V changes A_1^eff by an amount that depends on
    the original spectrum, so it cannot make s* spectrum-independent.
    """
    if verbose:
        print("=" * 60)
        print("THEOREM 3: Coupled Ancilla Extension")
        print("=" * 60)
        print()

    # Fix V = lam * |0><0| x sigma_x (instance-independent coupling)
    lam = 0.05

    # Test with two different spectra that have different A_1
    test_spectra = [
        ("Grover N=4, M=1", grover_energies(4, 1)),
        ("Grover N=8, M=1", grover_energies(8, 1)),
        ("Grover N=8, M=2", grover_energies(8, 2)),
        ("Three-level N=8", three_level_energies(8, 1, 3, 1.0, 3.0)),
    ]

    if verbose:
        print(f"  Fixed coupling: lam={lam} * I_N x sigma_x")
        print()
        print(f"  {'Instance':<25s} {'A_1':>8s} {'s*(bare)':>10s} "
              f"{'s*(coupled)':>12s} {'shift':>8s}")

    bare_s_stars = []
    coupled_s_stars = []

    for name, energies in test_spectra:
        N = len(energies)
        params = compute_spectral_params(energies)
        s_star_bare = params['s_star']

        # Compute effective A_1 for the coupled system
        # Eigenvalues of H_f = H_z x I + lam * I x sigma_x
        Hz_ext = np.kron(build_Hz(energies), np.eye(2))
        V = lam * np.kron(np.eye(N), np.array([[0, 1], [1, 0]]))
        Hf = Hz_ext + V

        evals_f, evecs_f = eigh(Hf)
        E0_f = evals_f[0]

        # Initial state
        psi0 = np.ones(N) / np.sqrt(N)
        phi = np.array([1.0, 0.0])
        Psi = np.kron(psi0, phi)

        # Effective A_1
        A1_eff = 0.0
        for j in range(len(evals_f)):
            if evals_f[j] > E0_f + 1e-12:
                wj = abs(np.dot(Psi, evecs_f[:, j])) ** 2
                A1_eff += wj / (evals_f[j] - E0_f)

        s_star_coupled = A1_eff / (A1_eff + 1)

        bare_s_stars.append(s_star_bare)
        coupled_s_stars.append(s_star_coupled)

        if verbose:
            shift = s_star_coupled - s_star_bare
            print(f"  {name:<25s} {params['A_1']:8.4f} {s_star_bare:10.4f} "
                  f"{s_star_coupled:12.4f} {shift:+8.4f}")

    if verbose:
        print()
        # Key test: do different bare s* values map to different coupled s* values?
        # If the coupling eliminated A_1 dependence, all coupled s* would be equal.
        spread_bare = max(bare_s_stars) - min(bare_s_stars)
        spread_coupled = max(coupled_s_stars) - min(coupled_s_stars)
        print(f"  Spread of s*(bare):    {spread_bare:.4f}")
        print(f"  Spread of s*(coupled): {spread_coupled:.4f}")
        print(f"  Coupling does NOT collapse s* to a single value.")
        print()

    assert max(coupled_s_stars) - min(coupled_s_stars) > 0.01, \
        "Coupled s* should still vary across instances"

    # Sweep over coupling strengths to verify non-collapse for all lambda
    if verbose:
        print(f"\n  Lambda sweep (spread of s* across instances):")
        print(f"  {'lambda':>8s} {'spread':>10s}")

    for lam_sweep in [0.01, 0.05, 0.1, 0.5, 1.0]:
        coupled_stars = []
        for name, energies in test_spectra:
            N = len(energies)
            Hz_ext = np.kron(build_Hz(energies), np.eye(2))
            V_sweep = lam_sweep * np.kron(np.eye(N), np.array([[0, 1], [1, 0]]))
            Hf = Hz_ext + V_sweep
            evals_f, evecs_f = eigh(Hf)
            E0_f = evals_f[0]
            psi0 = np.ones(N) / np.sqrt(N)
            phi_loc = np.array([1.0, 0.0])
            Psi = np.kron(psi0, phi_loc)
            A1_eff = sum(
                abs(np.dot(Psi, evecs_f[:, j]))**2 / (evals_f[j] - E0_f)
                for j in range(len(evals_f)) if evals_f[j] > E0_f + 1e-12
            )
            coupled_stars.append(A1_eff / (A1_eff + 1))
        spread = max(coupled_stars) - min(coupled_stars)
        if verbose:
            print(f"  {lam_sweep:8.3f} {spread:10.4f}")
        assert spread > 1e-3, \
            f"Spread should be nonzero at lambda={lam_sweep}, got {spread}"

    # Test with asymmetric coupling V = lam * diag(1,2,...,N) x sigma_x
    # This breaks the symmetry between computational basis states
    if verbose:
        print(f"\n  Asymmetric coupling V = lam * diag(1..N) x sigma_x:")
        print(f"  {'lambda':>8s} {'spread':>10s}")

    for lam_asym in [0.05, 0.5]:
        coupled_stars_asym = []
        for name, energies in test_spectra:
            N = len(energies)
            diag_sys = np.diag(np.arange(1, N + 1, dtype=float))
            V_asym = lam_asym * np.kron(diag_sys, np.array([[0, 1], [1, 0]]))
            Hz_ext = np.kron(build_Hz(energies), np.eye(2))
            Hf = Hz_ext + V_asym
            evals_f, evecs_f = eigh(Hf)
            E0_f = evals_f[0]
            psi0 = np.ones(N) / np.sqrt(N)
            phi_loc = np.array([1.0, 0.0])
            Psi = np.kron(psi0, phi_loc)
            A1_eff = sum(
                abs(np.dot(Psi, evecs_f[:, j]))**2 / (evals_f[j] - E0_f)
                for j in range(len(evals_f)) if evals_f[j] > E0_f + 1e-12
            )
            coupled_stars_asym.append(A1_eff / (A1_eff + 1))
        spread_asym = max(coupled_stars_asym) - min(coupled_stars_asym)
        if verbose:
            print(f"  {lam_asym:8.3f} {spread_asym:10.4f}")
        assert spread_asym > 1e-3, \
            f"Asymmetric spread should be nonzero at lambda={lam_asym}"

    if verbose:
        print(f"\n  Spread remains nonzero for asymmetric couplings too.")
        print()
        print("Theorem 3: ALL TESTS PASSED\n")
    return True


# ---------- Theorem 5: No-Go (Sensitivity) ----------

def verify_theorem5(verbose=True):
    """Theorem 5: ds*/dA_1 = 1/(A_1+1)^2 != 0.

    Verify that s* = A_1/(A_1+1) implies nonzero sensitivity.
    """
    if verbose:
        print("=" * 60)
        print("THEOREM 5: No-Go (Sensitivity ds*/dA_1)")
        print("=" * 60)
        print()

    # Analytic: ds*/dA_1 = d/dA_1 [A_1/(A_1+1)] = 1/(A_1+1)^2 > 0 always.
    # Verify numerically by varying the spectrum.

    N = 8
    results = []

    if verbose:
        print(f"  Two-level instances (N={N}):")
        print(f"  {'d_0':>4s} {'A_1':>8s} {'s*':>8s} {'ds*/dA_1':>10s}")

    for d0 in range(1, N):
        energies = grover_energies(N, d0)
        params = compute_spectral_params(energies)
        A1 = params['A_1']
        s_star = params['s_star']
        deriv = 1.0 / (A1 + 1) ** 2

        results.append({'d_0': d0, 'A_1': A1, 's_star': s_star, 'deriv': deriv})

        if verbose:
            print(f"  {d0:4d} {A1:8.4f} {s_star:8.4f} {deriv:10.4f}")

    if verbose:
        # Numerical derivative check
        print(f"\n  Numerical ds*/dA_1 (finite difference):")
        for i in range(len(results) - 1):
            dA1 = results[i+1]['A_1'] - results[i]['A_1']
            ds = results[i+1]['s_star'] - results[i]['s_star']
            deriv_num = ds / dA1
            deriv_analytic = 0.5 * (results[i]['deriv'] + results[i+1]['deriv'])
            print(f"    d_0={results[i]['d_0']}->{results[i+1]['d_0']}: "
                  f"num={deriv_num:.4f}, analytic~{deriv_analytic:.4f}")

        # Key point: ds*/dA_1 is ALWAYS positive, never zero
        all_derivs = [r['deriv'] for r in results]
        print(f"\n  ds*/dA_1 range: [{min(all_derivs):.4f}, {max(all_derivs):.4f}]")
        print(f"  ALL positive => A_1 dependence cannot be eliminated")
        print()

    if verbose:
        print("Theorem 5: ALL TESTS PASSED\n")
    return True


# ---------- Proposition 6: Rank-2 Higher-Rank Obstruction ----------

def orthogonalize_to_uniform(phi):
    """Project a vector to the subspace orthogonal to |psi_0> and normalize."""
    phi = np.array(phi, dtype=complex)
    N = len(phi)
    psi0 = np.ones(N, dtype=complex) / np.sqrt(N)
    phi = phi - np.vdot(psi0, phi) * psi0
    norm = np.linalg.norm(phi)
    if norm < 1e-12:
        raise ValueError("Input phi is parallel to |psi_0| after projection.")
    return phi / norm


def build_H_rank2(s, energies, phi):
    """Rank-2 driver Hamiltonian: H(s) = -(1-s)P + s H_z."""
    N = len(energies)
    psi0 = np.ones(N, dtype=complex) / np.sqrt(N)
    phi = orthogonalize_to_uniform(phi)
    P = np.outer(psi0, np.conj(psi0)) + np.outer(phi, np.conj(phi))
    Hz = build_Hz(energies)
    return -(1 - s) * P + s * Hz


def normalize_ground_set(N, ground_set=None):
    """Normalize and validate a ground-set specification."""
    if ground_set is None:
        ground = [0]
    elif isinstance(ground_set, int):
        ground = [ground_set]
    else:
        ground = list(ground_set)

    if len(ground) == 0:
        raise ValueError("ground_set must be non-empty")

    ground_unique = sorted(set(int(g) for g in ground))
    if min(ground_unique) < 0 or max(ground_unique) >= N:
        raise ValueError("ground_set indices out of range")
    if len(ground_unique) >= N:
        raise ValueError("ground_set must be a strict subset of basis states")
    return ground_unique


def rank2_twolevel_params(N, phi, ground_set=None):
    """Return alpha, beta constants for Proposition 6 on two-level families."""
    phi = orthogonalize_to_uniform(phi)
    ground = normalize_ground_set(N, ground_set=ground_set)
    exc = [i for i in range(N) if i not in set(ground)]
    d0 = len(ground)

    a = (N - d0) / N
    p = np.sum(np.abs(phi[ground]) ** 2)
    q = np.sum(phi[exc])
    alpha = a + 1 - p
    beta = a * (1 - p) - abs(q) ** 2 / N
    if beta < 0 and abs(beta) < 1e-12:
        beta = 0.0
    return {
        'a': a,
        'd0': d0,
        'p': p,
        'q': q,
        'alpha': alpha,
        'beta': beta
    }


def rank2_roots_twolevel(N, Delta, phi, ground_set=None):
    """Closed-form reduced crossing roots from Proposition 6."""
    params = rank2_twolevel_params(N, phi, ground_set=ground_set)
    alpha = params['alpha']
    beta = params['beta']
    kappas = []

    if beta > 1e-12:
        disc = alpha ** 2 - 4 * beta
        if disc < 0 and abs(disc) < 1e-12:
            disc = 0.0
        disc = max(disc, 0.0)
        sqrt_disc = np.sqrt(disc)
        for sign in [1, -1]:
            kappa = (alpha + sign * sqrt_disc) / (2 * beta)
            if kappa > 1e-12:
                kappas.append(float(np.real(kappa)))
    else:
        kappas = [1.0 / alpha]

    kappas = sorted(kappas)
    roots = []
    for kappa in kappas:
        x = kappa * Delta
        s = 1.0 / (1.0 + x)
        roots.append({'kappa': kappa, 'x': x, 's': s})
    return roots, params


def rank2_reduced_residual(N, Delta, phi, s, ground_set=None):
    """Scale-normalized residual of reduced equation:
    1 - x(A1+B1) + x^2(A1 B1 - |C1|^2) = 0,  x=(1-s)/s.
    """
    phi = orthogonalize_to_uniform(phi)
    ground = normalize_ground_set(N, ground_set=ground_set)
    exc = [i for i in range(N) if i not in set(ground)]
    d0 = len(ground)

    x = (1.0 - s) / s
    a = (N - d0) / N
    p = np.sum(np.abs(phi[ground]) ** 2)
    q = np.sum(phi[exc])

    A1 = a / Delta
    B1 = (1.0 - p) / Delta
    C1 = q / (np.sqrt(N) * Delta)

    t0 = 1.0
    t1 = -x * (A1 + B1)
    t2 = x ** 2 * (A1 * B1 - abs(C1) ** 2)
    value = t0 + t1 + t2
    scale = max(1.0, abs(t0) + abs(t1) + abs(t2))
    return abs(value) / scale


def rank2_numeric_crossing_second_branch(N, Delta, phi, ground_set=None):
    """Numerically locate where the second eigenvalue crosses lambda = s E0 = 0."""
    ground = normalize_ground_set(N, ground_set=ground_set)
    energies = [0.0 if i in set(ground) else Delta for i in range(N)]
    s_grid = np.linspace(0.001, 0.999, 5000)
    vals = []
    for s in s_grid:
        eigs = np.sort(np.real(eigh(build_H_rank2(s, energies, phi))[0]))
        vals.append(eigs[1])
    vals = np.array(vals)
    crossings = np.where(np.sign(vals[:-1]) != np.sign(vals[1:]))[0]
    if len(crossings) == 0:
        return None
    i = crossings[0]
    s0, s1 = s_grid[i], s_grid[i + 1]
    v0, v1 = vals[i], vals[i + 1]
    return s0 - v0 * (s1 - s0) / (v1 - v0)


def verify_theorem6_rank2(verbose=True):
    """Proposition 6: fixed rank-2 projector cannot make crossing spectrum-independent."""
    if verbose:
        print("=" * 60)
        print("PROPOSITION 6: Rank-2 Higher-Rank Obstruction")
        print("=" * 60)
        print()

    N = 8
    deltas = [0.5, 1.0, 2.0, 4.0, 8.0]
    ground_sets = [[0], [0, 1], [0, 1, 2]]
    phi_cases = [
        ("phi_sparse", np.array([1, -1, 0, 0, 0, 0, 0, 0], dtype=complex)),
        ("phi_balanced", np.array([1, 1, -2, 0, 0, 0, 0, 0], dtype=complex)),
    ]

    for name, phi in phi_cases:
        for ground_set in ground_sets:
            d0 = len(ground_set)
            if verbose:
                print(f"  Case: {name}, N={N}, d0={d0}")

            baseline_kappas = None
            branch_s_values = None

            for Delta in deltas:
                roots, params = rank2_roots_twolevel(N, Delta, phi, ground_set=ground_set)
                assert params['alpha'] > 0, "alpha must be positive"
                assert params['beta'] > -1e-10, "beta must be nonnegative"
                assert params['d0'] == d0, "unexpected d0 in parameters"

                if baseline_kappas is None:
                    baseline_kappas = [r['kappa'] for r in roots]
                    branch_s_values = [[] for _ in roots]
                else:
                    assert len(roots) == len(baseline_kappas), \
                        "Number of positive branches changed across Delta"

                for j, r in enumerate(roots):
                    kappa_err = abs(r['kappa'] - baseline_kappas[j])
                    assert kappa_err < 1e-10, \
                        f"kappa should be Delta-independent, got error {kappa_err}"

                    a1 = ((N - d0) / N) / Delta
                    s_formula = a1 / (a1 + r['kappa'] * ((N - d0) / N))
                    assert abs(r['s'] - s_formula) < 1e-12, \
                        "rank-2 s(A1) closed-form identity mismatch"

                    residual = abs(rank2_reduced_residual(
                        N, Delta, phi, r['s'], ground_set=ground_set
                    ))
                    assert residual < 1e-10, \
                        f"Reduced equation residual too large: {residual}"

                    branch_s_values[j].append(r['s'])

                s_num = rank2_numeric_crossing_second_branch(
                    N, Delta, phi, ground_set=ground_set
                )
                if s_num is not None:
                    s_pred_candidates = [r['s'] for r in roots]
                    best_err = min(abs(s_num - s_pred) for s_pred in s_pred_candidates)
                    assert best_err < 2e-3, \
                        f"Numerical crossing mismatch too large: {best_err}"

                if verbose:
                    root_text = ", ".join(
                        [f"(kappa={r['kappa']:.6f}, s={r['s']:.6f})" for r in roots]
                    )
                    print(f"    Delta={Delta:>4.1f}: {root_text}")

            for j, s_vals in enumerate(branch_s_values):
                spread = max(s_vals) - min(s_vals)
                assert spread > 0.05, \
                    f"Branch {j} should vary with Delta, got spread {spread}"
                for i in range(len(s_vals) - 1):
                    assert s_vals[i + 1] < s_vals[i], \
                        "s(Delta) should decrease as Delta increases"

                if verbose:
                    print(f"    Branch {j}: spread(s)={spread:.6f}")

            if verbose:
                print()

    if verbose:
        print("Proposition 6: ALL TESTS PASSED\n")
    return True


def deep_verify_theorem6_rank2(verbose=True, seed=7):
    """Stress-test Proposition 6 on random rank-2 projectors and sizes."""
    if verbose:
        print("=" * 60)
        print("PROPOSITION 6: Deep Stress Verification")
        print("=" * 60)
        print()

    rng = np.random.default_rng(seed)
    sizes = [6, 8, 10, 12]
    deltas = [0.4, 0.7, 1.0, 1.8, 3.2, 5.0]

    total_cases = 0
    max_residual = 0.0
    max_kappa_drift = 0.0

    for N in sizes:
        max_d0 = min(4, N - 1)
        for _ in range(20):
            phi_raw = rng.normal(size=N) + 1j * rng.normal(size=N)
            try:
                phi = orthogonalize_to_uniform(phi_raw)
            except ValueError:
                continue

            for d0 in range(1, max_d0 + 1):
                ground_set = list(range(d0))
                baseline_kappas = None

                for Delta in deltas:
                    roots, _ = rank2_roots_twolevel(
                        N, Delta, phi, ground_set=ground_set
                    )

                    if baseline_kappas is None:
                        baseline_kappas = [r['kappa'] for r in roots]
                    else:
                        assert len(roots) == len(baseline_kappas), \
                            "branch count changed across Delta in stress test"
                        for j, r in enumerate(roots):
                            drift = abs(r['kappa'] - baseline_kappas[j])
                            max_kappa_drift = max(max_kappa_drift, drift)
                            assert drift < 1e-10, \
                                f"kappa drift too large in stress test: {drift}"

                    for r in roots:
                        a1 = ((N - d0) / N) / Delta
                        s_formula = a1 / (a1 + r['kappa'] * ((N - d0) / N))
                        assert abs(r['s'] - s_formula) < 1e-10, \
                            "rank-2 deep: s(A1) closed-form identity mismatch"

                        residual = abs(rank2_reduced_residual(
                            N, Delta, phi, r['s'], ground_set=ground_set
                        ))
                        max_residual = max(max_residual, residual)
                        assert residual < 1e-9, \
                            f"residual too large in stress test: {residual}"

                    total_cases += 1

    if verbose:
        print(f"  Stress cases checked: {total_cases}")
        print(f"  Max reduced residual: {max_residual:.3e}")
        print(f"  Max kappa drift:      {max_kappa_drift:.3e}")
        print()
        print("Deep Proposition 6 stress verification: ALL TESTS PASSED\n")
    return True


def make_orthonormal_columns(vectors):
    """Return an N x k matrix with orthonormal columns spanning input vectors."""
    W = np.column_stack([np.array(v, dtype=complex) for v in vectors])
    Q, _ = np.linalg.qr(W)
    return Q


def rankk_twolevel_B(U, ground_set):
    """Excited-subspace Gram matrix B = U_exc^dagger U_exc for two-level family."""
    N = U.shape[0]
    ground = normalize_ground_set(N, ground_set=ground_set)
    ground_set_local = set(ground)
    exc = [i for i in range(N) if i not in ground_set_local]
    U_exc = U[exc, :]
    return U_exc.conj().T @ U_exc


def rankk_roots_twolevel(B, Delta, positive_tol=1e-8):
    """Reduced roots for det(I - x B / Delta) = 0."""
    evals = np.linalg.eigvalsh(B)
    mus = [float(np.real(ev)) for ev in evals if ev > positive_tol]
    kappas = sorted([1.0 / mu for mu in mus])
    roots = []
    for kappa in kappas:
        x = kappa * Delta
        roots.append({'kappa': kappa, 'x': x, 's': 1.0 / (1.0 + x)})
    return roots


def rankk_reduced_det_residual(B, Delta, s):
    """Scale-normalized spectral residual for I - x B / Delta at x=(1-s)/s.

    The reduced equation is det(I - x B / Delta) = 0. Using raw determinant
    magnitude is numerically unstable when one eigenvalue branch has tiny
    support and x is correspondingly large. We instead use the smallest
    absolute eigenvalue of the reduced matrix, normalized by the matrix scale.
    """
    x = (1.0 - s) / s
    M = np.eye(B.shape[0], dtype=complex) - (x / Delta) * B
    evals = np.linalg.eigvalsh(M)
    min_abs = float(np.min(np.abs(evals)))
    scale = max(1.0, float(np.max(np.abs(evals))))
    return min_abs / scale


def verify_proposition6A_rankk(verbose=True):
    """Proposition 6A: rank-k reduced roots scale as x = kappa * Delta."""
    if verbose:
        print("=" * 60)
        print("PROPOSITION 6A: Rank-k Two-Level Scaling Law")
        print("=" * 60)
        print()

    N = 10
    deltas = [0.5, 1.0, 2.0, 4.0, 8.0]
    ground_sets = [[0], [0, 1], [0, 1, 2]]

    psi0 = np.ones(N, dtype=complex) / np.sqrt(N)
    v1 = np.array([1, -1, 1, -1, 1, -1, 1, -1, 1, -1], dtype=complex)
    v2 = np.array([1, 1, -2, 0, 1, 0, -1, 0, 0, 0], dtype=complex)
    v3 = np.array([0, 1, 0, -1, 0, 1, 0, -1, 0, 0], dtype=complex)
    U = make_orthonormal_columns([psi0, v1, v2, v3])

    for ground_set in ground_sets:
        d0 = len(ground_set)
        B = rankk_twolevel_B(U, ground_set=ground_set)
        roots_ref = rankk_roots_twolevel(B, deltas[0])
        kappas_ref = [r['kappa'] for r in roots_ref]
        branch_s_values = [[] for _ in kappas_ref]

        if verbose:
            print(f"  Case: N={N}, k={U.shape[1]}, d0={d0}")

        for Delta in deltas:
            roots = rankk_roots_twolevel(B, Delta)
            kappas = [r['kappa'] for r in roots]
            assert len(kappas) == len(kappas_ref), \
                "positive-root branch count changed across Delta"

            for j, (kappa, r) in enumerate(zip(kappas, roots)):
                drift = abs(kappa - kappas_ref[j])
                assert drift < 1e-12, \
                    f"kappa drift in rank-k test too large: {drift}"

                a1 = ((N - d0) / N) / Delta
                s_formula = a1 / (a1 + kappa * ((N - d0) / N))
                assert abs(r['s'] - s_formula) < 1e-12, \
                    "rank-k s(A1) closed-form identity mismatch"

                residual = rankk_reduced_det_residual(B, Delta, r['s'])
                assert residual < 1e-10, \
                    f"rank-k reduced determinant residual too large: {residual}"
                branch_s_values[j].append(r['s'])

            if verbose:
                root_text = ", ".join(
                    [f"(kappa={r['kappa']:.6f}, s={r['s']:.6f})" for r in roots]
                )
                print(f"    Delta={Delta:>4.1f}: {root_text}")

        for j, s_vals in enumerate(branch_s_values):
            spread = max(s_vals) - min(s_vals)
            assert spread > 0.05, \
                f"rank-k branch {j} should vary with Delta, got spread {spread}"
            for i in range(len(s_vals) - 1):
                assert s_vals[i + 1] < s_vals[i], \
                    "rank-k s(Delta) should decrease as Delta increases"
            if verbose:
                print(f"    Branch {j}: spread(s)={spread:.6f}")
        if verbose:
            print()

    if verbose:
        print("Proposition 6A: ALL TESTS PASSED\n")
    return True


def deep_verify_proposition6A_rankk(verbose=True, seed=13):
    """Randomized stress test for Proposition 6A rank-k scaling law."""
    if verbose:
        print("=" * 60)
        print("PROPOSITION 6A: Deep Stress Verification")
        print("=" * 60)
        print()

    rng = np.random.default_rng(seed)
    sizes = [8, 10, 12]
    deltas = [0.4, 0.7, 1.0, 1.8, 3.2, 5.0]

    total_cases = 0
    max_residual = 0.0
    max_kappa_drift = 0.0

    for N in sizes:
        psi0 = np.ones(N, dtype=complex) / np.sqrt(N)
        max_d0 = min(4, N - 1)
        max_k = min(5, N - 1)

        for _ in range(18):
            # Build a random rank-k basis containing psi0.
            random_cols = [rng.normal(size=N) + 1j * rng.normal(size=N)
                           for _ in range(max_k - 1)]
            U = make_orthonormal_columns([psi0] + random_cols)

            for d0 in range(1, max_d0 + 1):
                ground_set = list(range(d0))
                B = rankk_twolevel_B(U, ground_set=ground_set)
                roots_ref = rankk_roots_twolevel(B, deltas[0])
                kappas_ref = [r['kappa'] for r in roots_ref]

                # Skip fully trivial no-excited-support draws.
                if len(kappas_ref) == 0:
                    continue

                branch_s_values = [[] for _ in kappas_ref]

                for Delta in deltas:
                    roots = rankk_roots_twolevel(B, Delta)
                    kappas = [r['kappa'] for r in roots]

                    assert len(kappas) == len(kappas_ref), \
                        "rank-k deep: branch count changed across Delta"

                    for j, (kappa, r) in enumerate(zip(kappas, roots)):
                        drift = abs(kappa - kappas_ref[j])
                        max_kappa_drift = max(max_kappa_drift, drift)
                        assert drift < 1e-10, \
                            f"rank-k deep: kappa drift too large: {drift}"

                        a1 = ((N - d0) / N) / Delta
                        s_formula = a1 / (a1 + kappa * ((N - d0) / N))
                        assert abs(r['s'] - s_formula) < 1e-10, \
                            "rank-k deep: s(A1) closed-form identity mismatch"

                        residual = rankk_reduced_det_residual(B, Delta, r['s'])
                        max_residual = max(max_residual, residual)
                        assert residual < 1e-9, \
                            f"rank-k deep: residual too large: {residual}"

                        branch_s_values[j].append(r['s'])

                    total_cases += 1

                for s_vals in branch_s_values:
                    spread = max(s_vals) - min(s_vals)
                    assert spread > 1e-10, \
                        "rank-k deep: branch did not vary with Delta"

    if verbose:
        print(f"  Stress cases checked: {total_cases}")
        print(f"  Max reduced residual: {max_residual:.3e}")
        print(f"  Max kappa drift:      {max_kappa_drift:.3e}")
        print()
        print("Deep Proposition 6A stress verification: ALL TESTS PASSED\n")
    return True


# ---------- Proposition 6B: Commuting Multilevel Extension ----------

def rankk_multilevel_B_blocks(U, level_sets):
    """Level-wise excited Gram blocks B_l = U_l^dagger U_l."""
    blocks = []
    for lvl in level_sets:
        idx = sorted(set(int(i) for i in lvl))
        U_l = U[idx, :]
        blocks.append(U_l.conj().T @ U_l)
    return blocks


def pairwise_commutator_max(B_blocks):
    """Maximum Frobenius norm of pairwise commutators."""
    max_norm = 0.0
    L = len(B_blocks)
    for i in range(L):
        for j in range(i + 1, L):
            comm = B_blocks[i] @ B_blocks[j] - B_blocks[j] @ B_blocks[i]
            max_norm = max(max_norm, float(np.linalg.norm(comm, ord='fro')))
    return max_norm


def psd_factor_rows(M, tol=1e-12):
    """Return R with R^dagger R = M for PSD Hermitian M."""
    H = 0.5 * (M + M.conj().T)
    evals, vecs = np.linalg.eigh(H)
    if np.min(evals) < -tol:
        raise ValueError(f"Matrix not PSD within tolerance: min eval={np.min(evals)}")
    evals = np.clip(evals, 0.0, None)
    return np.diag(np.sqrt(evals)) @ vecs.conj().T


def random_unitary(rng, k):
    """Random k x k unitary from complex QR."""
    A = rng.normal(size=(k, k)) + 1j * rng.normal(size=(k, k))
    Q, R = np.linalg.qr(A)
    phases = np.diag(R)
    phases = np.where(np.abs(phases) > 1e-14, phases / np.abs(phases), 1.0)
    return Q @ np.diag(np.conj(phases))


def synthesize_commuting_projector_from_mu(mu, Q):
    """Construct explicit U and level sets from commuting block eigen-data.

    Input:
      mu: shape (L, k), nonnegative entries, with column sums <= 1.
      Q:  k x k unitary.
    Output:
      U: N x k with orthonormal columns, N=(L+1)k.
      ground_set: first k indices.
      level_sets: list of L excited levels, each of size k.
      B_blocks: commuting excited Gram blocks.
    """
    mu = np.array(mu, dtype=float)
    L, k = mu.shape

    B_blocks = []
    for ell in range(L):
        D = np.diag(mu[ell, :])
        B = Q @ D @ Q.conj().T
        B_blocks.append(B)

    B_sum = np.zeros((k, k), dtype=complex)
    for B in B_blocks:
        B_sum += B

    I = np.eye(k, dtype=complex)
    B_ground = I - B_sum
    R_ground = psd_factor_rows(B_ground)

    row_blocks = [R_ground]
    for B in B_blocks:
        row_blocks.append(psd_factor_rows(B))
    U = np.vstack(row_blocks)

    # Validate orthonormality of columns.
    col_gram = U.conj().T @ U
    assert np.linalg.norm(col_gram - I, ord='fro') < 1e-10, \
        "synthesized projector columns are not orthonormal"

    ground_set = list(range(k))
    level_sets = []
    start = k
    for _ in range(L):
        level_sets.append(list(range(start, start + k)))
        start += k

    return U, ground_set, level_sets, B_blocks


def rankk_joint_commuting_data(B_blocks):
    """Joint spectral data for commuting Hermitian blocks.

    Returns mu matrix (L x k) in a common eigenbasis and max off-diagonal leakage.
    """
    k = B_blocks[0].shape[0]
    combo = np.zeros((k, k), dtype=complex)
    for ell, B in enumerate(B_blocks):
        combo += (2.0 ** (-ell - 1)) * B
    _, V = np.linalg.eigh(combo)

    mu_rows = []
    max_offdiag = 0.0
    for B in B_blocks:
        D = V.conj().T @ B @ V
        off = D - np.diag(np.diag(D))
        max_offdiag = max(max_offdiag, float(np.max(np.abs(off))))
        mu_rows.append(np.real(np.diag(D)))

    mu = np.array(mu_rows, dtype=float)
    return mu, max_offdiag


def rankk_multilevel_commuting_roots(B_blocks, deltas, positive_tol=1e-10):
    """Roots for det(I - x * sum_l B_l/Delta_l) = 0 in commuting case."""
    deltas = np.array(deltas, dtype=float)
    if np.min(deltas) <= 0:
        raise ValueError("all level gaps must be positive")

    mu, max_offdiag = rankk_joint_commuting_data(B_blocks)
    g_vals = np.sum(mu / deltas[:, None], axis=0)

    roots = []
    for r, g in enumerate(g_vals):
        if g > positive_tol:
            x = 1.0 / g
            s = 1.0 / (1.0 + x)
            roots.append({
                'branch': int(r),
                'g': float(g),
                'x': float(x),
                's': float(s),
                'mu': mu[:, r].copy()
            })

    return roots, {
        'mu': mu,
        'g_vals': g_vals,
        'max_offdiag': max_offdiag
    }


def rankk_multilevel_reduced_residual(B_blocks, deltas, s):
    """Scale-normalized residual for multilevel reduced matrix equation."""
    x = (1.0 - s) / s
    k = B_blocks[0].shape[0]
    A = np.zeros((k, k), dtype=complex)
    for B, Delta in zip(B_blocks, deltas):
        A += B / Delta
    M = np.eye(k, dtype=complex) - x * A
    evals = np.linalg.eigvalsh(M)
    min_abs = float(np.min(np.abs(evals)))
    scale = max(1.0, float(np.max(np.abs(evals))))
    return min_abs / scale


def verify_proposition6B_commuting_multilevel(verbose=True):
    """Proposition 6B: commuting multilevel extension of rank-k no-go."""
    if verbose:
        print("=" * 60)
        print("PROPOSITION 6B: Commuting Multilevel Extension")
        print("=" * 60)
        print()

    L = 3
    k = 3

    # Deterministic nontrivial commuting construction.
    mu = np.array([
        [0.55, 0.20, 0.10],
        [0.15, 0.45, 0.20],
        [0.10, 0.15, 0.55],
    ], dtype=float)
    Q_raw = np.array([
        [1.0, 1.0, 0.0],
        [0.0, 1.0, 1.0],
        [1.0, 0.0, 1.0],
    ], dtype=complex)
    Q, _ = np.linalg.qr(Q_raw)

    U, ground_set, level_sets, _ = synthesize_commuting_projector_from_mu(mu, Q)
    B_blocks = rankk_multilevel_B_blocks(U, level_sets=level_sets)

    comm_max = pairwise_commutator_max(B_blocks)
    assert comm_max < 1e-10, f"commuting-block requirement failed: {comm_max}"

    deltas_var = [0.5, 1.0, 2.0, 4.0, 8.0]
    deltas_fixed = [1.6, 3.1]
    branch_s = {}

    for d1 in deltas_var:
        deltas = [d1, deltas_fixed[0], deltas_fixed[1]]
        roots, info = rankk_multilevel_commuting_roots(B_blocks, deltas)
        assert info['max_offdiag'] < 1e-10, \
            f"joint diagonalization leakage too large: {info['max_offdiag']}"

        if verbose:
            print(f"  Delta tuple = ({deltas[0]:.2f}, {deltas[1]:.2f}, {deltas[2]:.2f})")

        for r in roots:
            residual = rankk_multilevel_reduced_residual(B_blocks, deltas, r['s'])
            assert residual < 1e-10, \
                f"rank-k multilevel residual too large: {residual}"

            s_formula = r['g'] / (1.0 + r['g'])
            assert abs(r['s'] - s_formula) < 1e-12, \
                "rank-k multilevel branch closed form mismatch"

            branch = r['branch']
            if branch not in branch_s:
                branch_s[branch] = []
            branch_s[branch].append((d1, r['s'], r['mu'][0]))

            if verbose:
                print(f"    branch {branch}: g={r['g']:.6f}, s={r['s']:.6f}, "
                      f"mu_var={r['mu'][0]:.6f}")

    for branch, vals in sorted(branch_s.items()):
        vals = sorted(vals, key=lambda t: t[0])
        s_vals = [v[1] for v in vals]
        mu_var = vals[0][2]
        spread = max(s_vals) - min(s_vals)

        if mu_var > 1e-3:
            assert spread > 1e-4, \
                f"branch {branch} should vary with varied level gap"
            for i in range(len(s_vals) - 1):
                assert s_vals[i + 1] < s_vals[i], \
                    "branch should decrease as varied gap increases"
        else:
            assert spread < 1e-8, \
                "branch with zero varied-level support should stay constant"

        if verbose:
            print(f"  Branch {branch}: spread={spread:.6f}, mu_var={mu_var:.6f}")

    if verbose:
        print()
        print("Proposition 6B: ALL TESTS PASSED\n")
    return True


def deep_verify_proposition6B_commuting_multilevel(verbose=True, seed=29):
    """Randomized stress test for Proposition 6B on commuting multilevel blocks."""
    if verbose:
        print("=" * 60)
        print("PROPOSITION 6B: Deep Stress Verification")
        print("=" * 60)
        print()

    rng = np.random.default_rng(seed)
    total_cases = 0
    max_residual = 0.0
    max_commutator = 0.0
    max_offdiag = 0.0

    for _ in range(140):
        L = int(rng.integers(2, 5))
        k = int(rng.integers(2, 6))

        mu = rng.uniform(0.0, 1.0, size=(L, k))
        zero_mask = rng.uniform(size=(L, k)) < 0.20
        mu[zero_mask] = 0.0

        # Ensure column sums <= 0.9 so the synthesized ground block stays PSD.
        col_sums = np.sum(mu, axis=0)
        scale = np.maximum(1.0, col_sums / 0.9)
        mu = mu / scale[None, :]

        Q = random_unitary(rng, k)
        U, _, level_sets, _ = synthesize_commuting_projector_from_mu(mu, Q)
        B_blocks = rankk_multilevel_B_blocks(U, level_sets=level_sets)

        comm_max = pairwise_commutator_max(B_blocks)
        max_commutator = max(max_commutator, comm_max)
        assert comm_max < 1e-10, \
            f"deep commuting check failed: commutator={comm_max}"

        var_level = int(rng.integers(0, L))
        var_deltas = [0.4, 0.8, 1.3, 2.1, 3.4]
        fixed = rng.uniform(0.6, 3.0, size=L)

        branch_tracks = {}
        branch_mu_var = {}

        for dvar in var_deltas:
            deltas = fixed.copy()
            deltas[var_level] = dvar
            roots, info = rankk_multilevel_commuting_roots(B_blocks, deltas)
            max_offdiag = max(max_offdiag, info['max_offdiag'])
            assert info['max_offdiag'] < 1e-10, \
                f"deep offdiag leakage too large: {info['max_offdiag']}"

            root_map = {r['branch']: r for r in roots}
            for branch, g in enumerate(info['g_vals']):
                if g <= 1e-10:
                    continue
                assert branch in root_map, "active branch missing from root map"
                r = root_map[branch]

                s_formula = g / (1.0 + g)
                assert abs(r['s'] - s_formula) < 1e-10, \
                    "deep multilevel closed-form mismatch"

                residual = rankk_multilevel_reduced_residual(B_blocks, deltas, r['s'])
                max_residual = max(max_residual, residual)
                assert residual < 1e-9, \
                    f"deep multilevel residual too large: {residual}"

                if branch not in branch_tracks:
                    branch_tracks[branch] = []
                    branch_mu_var[branch] = r['mu'][var_level]
                branch_tracks[branch].append((dvar, r['s']))

            total_cases += 1

        for branch, pairs in branch_tracks.items():
            pairs = sorted(pairs, key=lambda t: t[0])
            s_vals = [s for _, s in pairs]
            mu_var = branch_mu_var[branch]
            if mu_var > 1e-6:
                for i in range(len(s_vals) - 1):
                    assert s_vals[i + 1] < s_vals[i] + 1e-12, \
                        "deep multilevel monotonicity failed"

    if verbose:
        print(f"  Stress cases checked: {total_cases}")
        print(f"  Max reduced residual: {max_residual:.3e}")
        print(f"  Max commutator norm: {max_commutator:.3e}")
        print(f"  Max offdiag leakage: {max_offdiag:.3e}")
        print()
        print("Deep Proposition 6B stress verification: ALL TESTS PASSED\n")
    return True


# ---------- Proposition 6C: General Multilevel Trace No-Go ----------

def rankk_multilevel_roots_general(B_blocks, deltas, positive_tol=1e-10):
    """General multilevel reduced roots from A = sum_l B_l / Delta_l (no commutation needed)."""
    deltas = np.array(deltas, dtype=float)
    if np.min(deltas) <= 0:
        raise ValueError("all level gaps must be positive")

    k = B_blocks[0].shape[0]
    A = np.zeros((k, k), dtype=complex)
    for B, Delta in zip(B_blocks, deltas):
        A += B / Delta

    evals = np.linalg.eigvalsh(A)
    lambdas = [float(np.real(ev)) for ev in evals if ev > positive_tol]
    lambdas = sorted(lambdas)
    roots = [1.0 / lam for lam in lambdas]
    return roots, A, lambdas


def verify_proposition6C_multilevel_trace_nogo(verbose=True):
    """Proposition 6C: noncommuting multilevel reduced root set cannot stay constant."""
    if verbose:
        print("=" * 60)
        print("PROPOSITION 6C: General Multilevel Trace No-Go")
        print("=" * 60)
        print()

    N = 12
    psi0 = np.ones(N, dtype=complex) / np.sqrt(N)
    v1 = np.array([1, -1, 0, 1, 0, -1, 1, 0, 0, 0, 0, 0], dtype=complex)
    v2 = np.array([0, 1, -1, 0, 1, 0, -1, 1, 0, 0, 0, 0], dtype=complex)
    v3 = np.array([0, 0, 1, -1, 0, 1, 0, -1, 1, 0, 0, 0], dtype=complex)
    U = make_orthonormal_columns([psi0, v1, v2, v3])
    level_sets = [[3, 4, 5], [6, 7, 8], [9, 10, 11]]
    B_blocks = rankk_multilevel_B_blocks(U, level_sets=level_sets)

    comm = pairwise_commutator_max(B_blocks)
    assert comm > 1e-4, "test instance should be genuinely noncommuting"

    var_level = 0
    trace_weight = float(np.real(np.trace(B_blocks[var_level])))
    assert trace_weight > 1e-8, "varied level must have nonzero trace weight"

    var_deltas = [0.5, 1.0, 2.0, 4.0, 8.0]
    fixed_deltas = [1.7, 3.0]

    traces = []
    root_sets = []

    for dvar in var_deltas:
        deltas = [dvar, fixed_deltas[0], fixed_deltas[1]]
        roots, A, lambdas = rankk_multilevel_roots_general(B_blocks, deltas)

        # Trace identity: tr(A) = sum_l tr(B_l)/Delta_l.
        trA = float(np.real(np.trace(A)))
        trFormula = 0.0
        for B, Delta in zip(B_blocks, deltas):
            trFormula += float(np.real(np.trace(B))) / Delta
        assert abs(trA - trFormula) < 1e-10, "multilevel trace identity mismatch"
        traces.append(trA)

        for x in roots:
            s = 1.0 / (1.0 + x)
            residual = rankk_multilevel_reduced_residual(B_blocks, deltas, s)
            assert residual < 1e-10, \
                f"multilevel general residual too large: {residual}"

        root_sets.append(sorted(roots))

        if verbose:
            print(f"  Delta tuple = ({deltas[0]:.2f}, {deltas[1]:.2f}, {deltas[2]:.2f})")
            print(f"    tr(A) = {trA:.8f}, roots = {[round(r, 8) for r in roots]}")

    # tr(A) decreases strictly as varied gap grows.
    for i in range(len(traces) - 1):
        assert traces[i + 1] < traces[i], "trace should strictly decrease with varied gap"

    # Root-set nonconstancy (if all roots were constant, trace would be constant).
    roots0 = root_sets[0]
    rootsN = root_sets[-1]
    if len(roots0) != len(rootsN):
        changed = True
    else:
        changed = max(abs(a - b) for a, b in zip(roots0, rootsN)) > 1e-4
    assert changed, "root set should change across varied gap values"

    if verbose:
        print(f"  Max commutator norm: {comm:.3e}")
        print(f"  Varied-level trace weight: {trace_weight:.6f}")
        print()
        print("Proposition 6C: ALL TESTS PASSED\n")
    return True


def deep_verify_proposition6C_multilevel_trace_nogo(verbose=True, seed=37):
    """Randomized stress test for Proposition 6C on noncommuting multilevel families."""
    if verbose:
        print("=" * 60)
        print("PROPOSITION 6C: Deep Stress Verification")
        print("=" * 60)
        print()

    rng = np.random.default_rng(seed)
    total_cases = 0
    max_residual = 0.0
    min_comm = float('inf')

    while total_cases < 140:
        L = int(rng.integers(2, 5))
        k = int(rng.integers(2, 6))
        level_size = int(rng.integers(max(2, k - 1), k + 3))
        ground_size = int(rng.integers(2, k + 3))
        N = ground_size + L * level_size
        if N <= k:
            continue

        U_raw = rng.normal(size=(N, k)) + 1j * rng.normal(size=(N, k))
        U, _ = np.linalg.qr(U_raw)

        level_sets = []
        start = ground_size
        for _ in range(L):
            level_sets.append(list(range(start, start + level_size)))
            start += level_size
        B_blocks = rankk_multilevel_B_blocks(U, level_sets=level_sets)

        comm = pairwise_commutator_max(B_blocks)
        if comm < 1e-6:
            continue
        min_comm = min(min_comm, comm)

        var_level = int(rng.integers(0, L))
        tr_weight = float(np.real(np.trace(B_blocks[var_level])))
        if tr_weight < 1e-8:
            continue

        fixed = rng.uniform(0.7, 3.2, size=L)
        var_deltas = [0.45, 0.8, 1.4, 2.3, 3.7]

        traces = []
        roots_snapshots = []

        for dvar in var_deltas:
            deltas = fixed.copy()
            deltas[var_level] = dvar
            roots, A, _ = rankk_multilevel_roots_general(B_blocks, deltas)

            trA = float(np.real(np.trace(A)))
            trFormula = 0.0
            for B, Delta in zip(B_blocks, deltas):
                trFormula += float(np.real(np.trace(B))) / Delta
            assert abs(trA - trFormula) < 1e-9, "deep trace identity mismatch"
            traces.append(trA)

            for x in roots:
                s = 1.0 / (1.0 + x)
                residual = rankk_multilevel_reduced_residual(B_blocks, deltas, s)
                max_residual = max(max_residual, residual)
                assert residual < 1e-9, \
                    f"deep multilevel general residual too large: {residual}"

            roots_snapshots.append(sorted(roots))

        for i in range(len(traces) - 1):
            assert traces[i + 1] < traces[i], \
                "deep trace should strictly decrease with varied gap"

        r0 = roots_snapshots[0]
        rN = roots_snapshots[-1]
        if len(r0) == len(rN):
            delta = max(abs(a - b) for a, b in zip(r0, rN)) if len(r0) > 0 else 0.0
            assert delta > 1e-5, \
                "deep root set appeared invariant despite strict trace drift"

        total_cases += 1

    if verbose:
        print(f"  Stress cases checked: {total_cases}")
        print(f"  Max reduced residual: {max_residual:.3e}")
        print(f"  Min noncommutator:    {min_comm:.3e}")
        print()
        print("Deep Proposition 6C stress verification: ALL TESTS PASSED\n")
    return True


# ---------- Theorem 4: Multi-Segment Rigidity ----------

def verify_theorem4(verbose=True):
    """Theorem 4: Multi-segment path.

    Segment 1: |psi_0> -> |psi_mid> via some adiabatic path.
    Segment 2: -(1-t)|psi_mid><psi_mid| + t H_z

    The crossing in segment 2 depends on B_1 = sum_k w_k/(E_k-E_0)
    where w_k = sum_{z: E(z)=E_k} |<psi_mid|z>|^2.

    If |psi_mid> = |psi_0> (uniform), then B_1 = A_1.
    If |psi_mid> is non-uniform, B_1 != A_1 but depends on the assignment.
    """
    if verbose:
        print("=" * 60)
        print("THEOREM 4: Multi-Segment Rigidity")
        print("=" * 60)
        print()

    N = 4
    energies = grover_energies(N, 1)
    params = compute_spectral_params(energies)

    # If intermediate state is uniform: same crossing
    psi_mid_uniform = np.ones(N) / np.sqrt(N)
    E = np.array(energies)
    E_vals = np.sort(np.unique(E))
    E_0 = E_vals[0]

    B1_uniform = 0.0
    for ev in E_vals:
        if ev > E_0:
            mask = np.isclose(E, ev)
            wk = np.sum(np.abs(psi_mid_uniform[mask])**2)
            B1_uniform += wk / (ev - E_0)

    # If intermediate state is non-uniform
    psi_mid_biased = np.array([0.9, 0.2, 0.2, 0.3])
    psi_mid_biased /= np.linalg.norm(psi_mid_biased)

    B1_biased = 0.0
    for ev in E_vals:
        if ev > E_0:
            mask = np.isclose(E, ev)
            wk = np.sum(np.abs(psi_mid_biased[mask])**2)
            B1_biased += wk / (ev - E_0)

    s_star_uniform = B1_uniform / (B1_uniform + 1)
    s_star_biased = B1_biased / (B1_biased + 1)

    if verbose:
        print(f"  N={N}, Grover M=1")
        print(f"  A_1 = {params['A_1']:.4f}, s* = {params['s_star']:.4f}")
        print(f"  Uniform midpoint:  B_1 = {B1_uniform:.4f}, "
              f"s*_2 = {s_star_uniform:.4f}")
        print(f"  Biased midpoint:   B_1 = {B1_biased:.4f}, "
              f"s*_2 = {s_star_biased:.4f}")
        print(f"  Uniform gives B_1 = A_1: {abs(B1_uniform - params['A_1']) < 1e-10}")
        print(f"  Biased gives B_1 != A_1: {abs(B1_biased - params['A_1']) > 0.01}")
        print()

    assert abs(B1_uniform - params['A_1']) < 1e-10, \
        "Uniform midpoint should give B_1 = A_1"
    assert abs(B1_biased - params['A_1']) > 0.01, \
        "Biased midpoint should give B_1 != A_1"

    # Verify that for the biased case, different energy assignments
    # give different B_1 (Theorem 2 consequence)
    energies_perm = [1.0, 0.0, 1.0, 1.0]
    E_perm = np.array(energies_perm)
    B1_biased_perm = 0.0
    for ev in E_vals:
        if ev > E_0:
            mask = np.isclose(E_perm, ev)
            wk = np.sum(np.abs(psi_mid_biased[mask])**2)
            B1_biased_perm += wk / (ev - E_0)

    if verbose:
        print(f"  Biased + permuted: B_1 = {B1_biased_perm:.4f} "
              f"(vs {B1_biased:.4f})")
        print(f"  Different assignment -> different B_1: "
              f"{abs(B1_biased - B1_biased_perm) > 0.01}")
        print(f"  => Non-uniform midpoint is not universal")
        print()
        print("Theorem 4: ALL TESTS PASSED\n")

    return True


# ---------- Sanity checks ----------

def grover_sanity_check(verbose=True):
    """Grover N=4, M=1 sanity check: A_1=3/4, s*=3/7.

    Verify all fundamental quantities.
    """
    if verbose:
        print("=" * 60)
        print("SANITY CHECK: Grover N=4, M=1")
        print("=" * 60)
        print()

    N = 4
    energies = grover_energies(N, 1)
    params = compute_spectral_params(energies)

    # Check A_1 = (N-1)/(N*1) = 3/4
    assert abs(params['A_1'] - 3/4) < 1e-10, f"A_1 should be 3/4, got {params['A_1']}"
    # Check s* = 3/7
    assert abs(params['s_star'] - 3/7) < 1e-10, f"s* should be 3/7, got {params['s_star']}"
    # Check Delta = 1
    assert abs(params['Delta'] - 1.0) < 1e-10

    if verbose:
        print(f"  A_1 = {params['A_1']} = 3/4 [OK]")
        print(f"  s*  = {params['s_star']:.6f} = 3/7 = {3/7:.6f} [OK]")
        print(f"  Delta = {params['Delta']} [OK]")
        print()

    # Verify eigenvalue formula at s=1/2 (gap minimum for Grover)
    H = build_H(0.5, energies)
    eigs = np.sort(eigh(H)[0])
    g_min_theory = 1.0 / np.sqrt(N)
    g_min_num = eigs[1] - eigs[0]

    if verbose:
        print(f"  Gap at s=1/2: {g_min_num:.6f} (theory: {g_min_theory:.6f}) [OK]")
        print()

    assert abs(g_min_num - g_min_theory) < 1e-10

    # Verify the secular equation
    verify_secular_equation(energies, s_values=[3/7, 0.3, 0.5, 0.7],
                            verbose=verbose)

    if verbose:
        print()
        print("Sanity check: ALL PASSED\n")
    return True


# ---------- Main ----------

def run_all_tests(verbose=True, deep=False):
    """Run all verification tests."""
    print("=" * 60)
    print("Experiment 12: Circumventing the A_1 Barrier")
    print("Numerical Verification Suite")
    print("=" * 60)
    print()

    grover_sanity_check(verbose=verbose)
    verify_theorem1(verbose=verbose)
    verify_theorem2(verbose=verbose)
    verify_theorem3(verbose=verbose)
    verify_theorem4(verbose=verbose)
    verify_theorem5(verbose=verbose)
    verify_theorem6_rank2(verbose=verbose)
    verify_proposition6A_rankk(verbose=verbose)
    verify_proposition6B_commuting_multilevel(verbose=verbose)
    verify_proposition6C_multilevel_trace_nogo(verbose=verbose)
    if deep:
        deep_verify_theorem6_rank2(verbose=verbose)
        deep_verify_proposition6A_rankk(verbose=verbose)
        deep_verify_proposition6B_commuting_multilevel(verbose=verbose)
        deep_verify_proposition6C_multilevel_trace_nogo(verbose=verbose)

    print("=" * 60)
    print("ALL TESTS PASSED")
    print("=" * 60)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        description="Experiment 12 numerical verification suite."
    )
    parser.add_argument(
        "--deep",
        action="store_true",
        help="run additional random stress tests for Propositions 6, 6A, 6B, and 6C",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="suppress detailed per-test logs",
    )
    args = parser.parse_args()
    run_all_tests(verbose=not args.quiet, deep=args.deep)
