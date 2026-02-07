# Circumventing the Barrier: Proofs

## Part I: Setup

### Notation

We work with the unstructured adiabatic optimization Hamiltonian

$$H(s) = -(1-s)|\psi_0\rangle\langle\psi_0| + sH_z, \quad s \in [0,1],$$

where $|\psi_0\rangle = \frac{1}{\sqrt{N}}\sum_{z=0}^{N-1}|z\rangle$ is the uniform superposition and $H_z = \sum_z E(z)|z\rangle\langle z|$ is diagonal in the computational basis.

The problem Hamiltonian $H_z$ has $M$ distinct eigenvalues $E_0 < E_1 < \cdots < E_{M-1}$ with degeneracies $d_0, d_1, \ldots, d_{M-1}$, so $\sum_k d_k = N$. The spectral gap is $\Delta = E_1 - E_0$. The spectral parameters are

$$A_p = \frac{1}{N}\sum_{k=1}^{M-1} \frac{d_k}{(E_k - E_0)^p}, \quad p \in \mathbb{N}.$$

The symmetric states are $|k\rangle = \frac{1}{\sqrt{d_k}}\sum_{z \in \Omega_k} |z\rangle$ where $\Omega_k = \{z : E(z) = E_k\}$.

### The secular equation

**Lemma (Eigenvalue equation).** $\lambda$ is an eigenvalue of $H(s)$ in the symmetric subspace $\mathcal{H}_S = \mathrm{span}\{|k\rangle : k=0,\ldots,M-1\}$ if and only if

$$\frac{1}{1-s} = \frac{1}{N}\sum_{k=0}^{M-1} \frac{d_k}{sE_k - \lambda}. \tag{SE}$$

This is proved in the thesis (Lemma 5.1). The key steps: $H(s)|\phi\rangle = \lambda|\phi\rangle$ in $\mathcal{H}_S$ gives $(sE_k - \lambda)\langle k|\phi\rangle = (1-s)\langle\psi_0|\phi\rangle\langle\psi_0|k\rangle$ for each $k$. Using $\langle\psi_0|k\rangle = \sqrt{d_k/N}$ and summing over $k$ yields (SE).

### The crossing position

Setting $\lambda = sE_0$ in (SE) (which represents the ground level of $sH_z$) and separating the $k=0$ term:

$$\frac{1}{1-s} = \frac{d_0}{N \cdot 0^+} + \frac{1}{N}\sum_{k=1}^{M-1}\frac{d_k}{s(E_k - E_0)}.$$

The $k=0$ term diverges, meaning $\lambda = sE_0$ is never an exact eigenvalue (except at $s=0$ or $s=1$). But the point $s^*$ where the secular equation forces the eigenvalue branches closest together (the avoided crossing) satisfies: if we define the reduced secular function $F(s,\lambda) = 1/(1-s) - (1/N)\sum_{k=1}^{M-1}d_k/(sE_k - \lambda)$ and set $\lambda = sE_0$, $d_0 = 0$ (i.e., ignore the ground space contribution which only shifts the eigenvalues by $O(d_0/N)$), we get

$$\frac{1}{1-s} = \frac{A_1}{s}, \quad \text{i.e.,} \quad s = s^* = \frac{A_1}{A_1 + 1}. \tag{Cross}$$

At $s^*$, the ground eigenvalue branch crosses the line $sE_0$ in the secular equation. The actual avoided crossing has gap $g(s^*) = \Theta(\hat{g})$ where $\hat{g} = \frac{2A_1}{A_1+1}\sqrt{\frac{d_0}{NA_2}}$.

### The weights

For any initial state $|\psi\rangle \in \mathbb{C}^N$ (not necessarily uniform), define the weights

$$w_k(\psi) = \sum_{z \in \Omega_k} |\langle z|\psi\rangle|^2. \tag{W}$$

These satisfy $\sum_k w_k = 1$. For the Hamiltonian $H_\psi(s) = -(1-s)|\psi\rangle\langle\psi| + sH_z$, the eigenvalue equation $H_\psi(s)|\phi\rangle = \lambda|\phi\rangle$ with $\gamma = \langle\psi|\phi\rangle \neq 0$ gives $\langle z|\phi\rangle = (1-s)\gamma\langle z|\psi\rangle/(sE(z) - \lambda)$. Taking the inner product with $|\psi\rangle$: $\gamma = (1-s)\gamma\sum_z |\langle z|\psi\rangle|^2/(sE(z) - \lambda)$. Dividing by $\gamma$ and grouping by energy levels, the secular equation generalizes to

$$\frac{1}{1-s} = \sum_{k=0}^{M-1} \frac{w_k}{sE_k - \lambda}, \tag{SE-gen}$$

and the effective $A_1$ becomes

$$A_1^{\text{eff}}(\psi) = \sum_{k=1}^{M-1} \frac{w_k(\psi)}{E_k - E_0}. \tag{A1-eff}$$

For $|\psi\rangle = |\psi_0\rangle$ (uniform superposition), $w_k = d_k/N$ and $A_1^{\text{eff}} = A_1$.

The crossing position for a general initial state is

$$s^*(\psi) = \frac{A_1^{\text{eff}}(\psi)}{A_1^{\text{eff}}(\psi) + 1}. \tag{Cross-gen}$$


## Part II: Product State Invariance (Theorem 1)

**Theorem 1.** For any product initial state $|\Psi\rangle = |\psi_0\rangle \otimes |\phi\rangle$ and uncoupled final Hamiltonian $H_f = H_z \otimes I_{2^m}$, the extended Hamiltonian

$$H_{\text{ext}}(s) = -(1-s)|\Psi\rangle\langle\Psi| + s(H_z \otimes I_{2^m})$$

has the same crossing position $s^* = A_1/(A_1+1)$ as the bare system.

**Proof.** We show that the eigenvalue branches participating in the avoided crossing are identical.

**Step 1: Eigenstates of the extended system.** The extended Hamiltonian acts on $\mathbb{C}^N \otimes \mathbb{C}^{2^m}$. Let $\{|a\rangle\}_{a=0}^{2^m-1}$ be an orthonormal basis of the ancilla space with $|0\rangle$ chosen so that $\phi = \sum_a \phi_a |a\rangle$ with $|\phi\rangle$ normalized.

Consider states of the form $|z\rangle \otimes |a\rangle$ for $a$ orthogonal to $|\phi\rangle$ (i.e., $\langle\phi|a\rangle = 0$). Then:

$$H_{\text{ext}}(s)(|z\rangle \otimes |a\rangle) = -(1-s)\langle\Psi|z,a\rangle|\Psi\rangle + sE(z)|z\rangle \otimes |a\rangle.$$

Since $\langle\Psi|z,a\rangle = \langle\psi_0|z\rangle\langle\phi|a\rangle = 0$, we have

$$H_{\text{ext}}(s)(|z\rangle \otimes |a\rangle) = sE(z)|z\rangle \otimes |a\rangle.$$

So $|z\rangle \otimes |a\rangle$ is an exact eigenstate with eigenvalue $sE(z)$ for any $a \perp |\phi\rangle$. These are $N(2^m - 1)$ eigenstates.

**Step 2: Restriction to the relevant subspace.** The remaining $N$ eigenstates live in the subspace $\mathcal{V}_\phi = \mathbb{C}^N \otimes |\phi\rangle = \{|\psi\rangle \otimes |\phi\rangle : |\psi\rangle \in \mathbb{C}^N\}$. On this subspace, the Hamiltonian acts as:

$$H_{\text{ext}}(s)(|\psi\rangle \otimes |\phi\rangle) = -(1-s)\langle\psi_0|\psi\rangle |\psi_0\rangle \otimes |\phi\rangle + s(H_z|\psi\rangle) \otimes |\phi\rangle.$$

This is unitarily equivalent (via the isomorphism $|\psi\rangle \otimes |\phi\rangle \mapsto |\psi\rangle$) to

$$H_{\text{bare}}(s)|\psi\rangle = -(1-s)\langle\psi_0|\psi\rangle|\psi_0\rangle + sH_z|\psi\rangle = H(s)|\psi\rangle.$$

Therefore, the restriction of $H_{\text{ext}}(s)$ to $\mathcal{V}_\phi$ is unitarily equivalent to $H(s)$.

**Step 3: The crossing branches.** The spectrum of $H_{\text{ext}}(s)$ is the union of:

(a) The spectrum of $H(s)$ (from the restriction to $\mathcal{V}_\phi$).

(b) The values $\{sE(z)\}$ with multiplicities $2^m - 1$ each (from states orthogonal to $|\phi\rangle$).

The two eigenvalue branches that undergo the avoided crossing are in set (a) - they are identical to the bare system's branches. The extra eigenvalues in set (b) are at $sE_k$ for each level $k$, which are exactly the unperturbed eigenvalues of $sH_z$. These do not participate in the avoided crossing.

**Step 4: The crossing position.** Since the crossing branches are identical to the bare system, the secular equation (SE) is unchanged, and $s^* = A_1/(A_1+1)$. $\square$

**Remark.** This result is exact, not perturbative. The ancilla adds eigenvalues to the spectrum but does not change the avoided crossing. The result holds for any ancilla state $|\phi\rangle$ and any number of ancilla qubits $m \geq 1$, as long as the initial state is a product and the final Hamiltonian is uncoupled.

**Remark on the gap.** While $s^*$ is invariant, the spectral gap of $H_{\text{ext}}(s)$ is strictly smaller than the bare gap. For $d_0 = 1$, the extra eigenvalues at $sE_0$ (from states $|z\rangle \otimes |a\rangle$ with $z \in \Omega_0$, $a \perp |\phi\rangle$) sit between the ground eigenvalue $\lambda_0(s) < sE_0$ and the crossing branch eigenvalue $\lambda_1(s) > sE_0$. The gap of $H_{\text{ext}}(s)$ is $sE_0 - \lambda_0(s) < \lambda_1(s) - \lambda_0(s) = g_{\text{bare}}(s)$. The uncoupled ancilla makes the gap worse, not better.

**Numerical verification.** Grover $N=4$, $M=1$: $A_1 = 3/4$, $s^* = 3/7$. Extended system with 1 ancilla qubit: ground eigenvalue branch matches bare system to machine precision ($< 10^{-15}$) for all $s$. Crossing branch also matches to machine precision. Verified for 1 and 2 ancilla qubits, ancilla states $|0\rangle$, $|+\rangle$, and $0.3|0\rangle + 0.95|1\rangle$, and for three-level spectra.


## Part III: Universality of Uniform Superposition (Theorem 2)

**Theorem 2.** Among all states $|\psi\rangle \in \mathbb{C}^N$, the uniform superposition $|\psi_0\rangle = \frac{1}{\sqrt{N}}\sum_z |z\rangle$ is the unique state (up to phases on individual basis states) for which the weights $w_k(\psi)$ depend only on the spectral parameters $\{E_k, d_k\}$ and not on the specific assignment of energies to computational basis states.

**Proof.**

**Step 1: Formalize the independence condition.** The energy assignment is a function $\sigma: \{0,\ldots,N-1\} \to \{E_0,\ldots,E_{M-1}\}$ with $|\sigma^{-1}(E_k)| = d_k$. The weights under assignment $\sigma$ are

$$w_k(\psi, \sigma) = \sum_{z: \sigma(z) = E_k} |\langle z|\psi\rangle|^2.$$

We require: for all assignments $\sigma, \sigma'$ with the same degeneracies $\{d_k\}$,

$$w_k(\psi, \sigma) = w_k(\psi, \sigma') \quad \text{for all } k.$$

**Step 2: Permutation argument.** Any two assignments $\sigma, \sigma'$ with the same degeneracies are related by a permutation $\pi$ of $\{0,\ldots,N-1\}$: $\sigma'(z) = \sigma(\pi(z))$. Then

$$w_k(\psi, \sigma') = \sum_{z: \sigma(\pi(z)) = E_k} |\langle z|\psi\rangle|^2 = \sum_{z': \sigma(z') = E_k} |\langle \pi^{-1}(z')|\psi\rangle|^2.$$

The condition $w_k(\psi, \sigma) = w_k(\psi, \sigma')$ becomes

$$\sum_{z \in \Omega_k} |\langle z|\psi\rangle|^2 = \sum_{z \in \Omega_k} |\langle \pi^{-1}(z)|\psi\rangle|^2$$

for all $k$ and all permutations $\pi$ that preserve the partition into degeneracy classes. But we need this for ALL permutations (since we can choose any assignment), which requires invariance under arbitrary permutations of $\{0,\ldots,N-1\}$.

**Step 3: Necessity.** Consider two-level spectra with $d_0 = 1$, $d_1 = N-1$. For any two basis states $z_a, z_b$ with $z_a \neq z_b$, there exists a permutation $\pi$ that maps the assignment $\sigma$ (with $\sigma(z_a) = E_0$) to $\sigma'$ (with $\sigma'(z_b) = E_0$), i.e., $\pi$ swaps $z_a$ and $z_b$. The condition requires

$$|\langle z_a|\psi\rangle|^2 = w_0(\psi, \sigma) = w_0(\psi, \sigma') = |\langle z_b|\psi\rangle|^2.$$

Since $z_a, z_b$ are arbitrary, all computational basis amplitudes must have equal modulus: $|\langle z|\psi\rangle|^2 = c$ for all $z$. Normalization gives $c = 1/N$.

**Step 4: Sufficiency.** If $|\langle z|\psi\rangle|^2 = 1/N$ for all $z$, then $w_k = d_k/N$ regardless of the assignment. $\square$

**Corollary.** For any instance-independent adiabatic algorithm (same Hamiltonian for all energy assignments), the initial state must be the uniform superposition, and the crossing position is $s^* = A_1/(A_1+1)$.

**Numerical verification.** For $N=4$, Grover $M=1$: with biased initial state $|\psi\rangle = (0.8, 0.3, 0.3, 0.3)/\|{\cdot}\|$, the effective $A_1^{\text{eff}} = 0.2967$ and $s^* = 0.2288$, compared to $A_1 = 0.75$ and $s^* = 0.4286$ for uniform. Permuting the energy assignment changes the biased $s^*$ to $0.4740$, but leaves the uniform $s^*$ unchanged.

**Extension to entangled initial states.** On an extended Hilbert space $\mathbb{C}^N \otimes \mathbb{C}^{2^m}$, consider an entangled initial state $|\Psi\rangle$ (not necessarily a product). For the uncoupled Hamiltonian $H_{\text{ext}}(s) = -(1-s)|\Psi\rangle\langle\Psi| + s(H_z \otimes I)$, the secular equation depends on the reduced weights

$$q(z) = \sum_{a=0}^{2^m-1} |\langle z,a|\Psi\rangle|^2, \quad w_k = \sum_{z \in \Omega_k} q(z).$$

The instance-independence condition requires $w_k(\Psi, \sigma) = w_k(\Psi, \sigma')$ for all assignments $\sigma, \sigma'$. By the same permutation argument as in the proof (applied to $q(z)$ instead of $|\langle z|\psi\rangle|^2$), this forces $q(z) = 1/N$ for all $z$. Therefore $w_k = d_k/N$ and $A_1^{\text{eff}} = A_1$, regardless of the entanglement structure. Entangled initial states do not provide an escape from the barrier as long as the final Hamiltonian is uncoupled.


## Part IV: Coupled Ancilla Extension (Theorem 3)

**Theorem 3.** Consider an extended Hamiltonian with system-ancilla coupling:

$$H_{\text{ext}}(s) = -(1-s)|\Psi\rangle\langle\Psi| + s(H_z \otimes I + V)$$

where $|\Psi\rangle = |\psi_0\rangle \otimes |\phi\rangle$ and $V$ is instance-independent (the same operator for all energy assignments). Then $s^*_{\text{ext}}$ is not independent of the spectrum of $H_z$: no fixed instance-independent coupling $V$ makes $A_1^{\text{eff}}$ constant across all problem instances.

**Proof.** The spectrum of $H_f = H_z \otimes I + V$ determines the crossing. The secular equation for the extended system is

$$\frac{1}{1-s} = \sum_{j} \frac{|\langle\Psi|\tilde{E}_j\rangle|^2}{s\tilde{E}_j - \lambda}, \tag{SE-ext}$$

where $\{\tilde{E}_j, |\tilde{E}_j\rangle\}$ are eigenpairs of $H_f$. The crossing position satisfies

$$s^*_{\text{ext}} = \frac{A_1^{\text{eff}}}{A_1^{\text{eff}} + 1}$$

where $A_1^{\text{eff}} = \sum_{j: \tilde{E}_j > \tilde{E}_0} |\langle\Psi|\tilde{E}_j\rangle|^2 / (\tilde{E}_j - \tilde{E}_0)$ and $\tilde{E}_0$ is the ground energy of $H_f$.

**Step 1: $V$ changes the spectrum of $H_f$.** Since $V$ is instance-independent, it acts the same way regardless of $H_z$. The eigenvalues $\tilde{E}_j$ of $H_z \otimes I + V$ depend on both $V$ and the spectrum of $H_z$. Weyl's inequality gives $|\tilde{E}_j - E_j^{(0)}| \leq \|V\|$, where $E_j^{(0)}$ are eigenvalues of $H_z \otimes I$. The coupling can split degenerate levels and mix system-ancilla states, but the resulting spectrum still carries the information of $\{E_k, d_k\}$.

**Step 2: The effective $A_1$ depends on the spectrum.** The weights $\tilde{w}_j = |\langle\Psi|\tilde{E}_j\rangle|^2$ and energies $\tilde{E}_j$ are functions of both $V$ and $H_z$. Since $V$ is fixed and $H_z$ varies across instances, $A_1^{\text{eff}}$ is a function $A_1^{\text{eff}} = F(V, \{E_k, d_k\})$. The function $F$ depends on the full spectrum of $H_z$, not just through $A_1$ - different spectra with the same $A_1$ may give different $A_1^{\text{eff}}$. But crucially, $A_1^{\text{eff}}$ is NOT independent of the spectrum.

**Step 3: Instance-independent $V$ cannot cancel the dependence.** For $s^*_{\text{ext}}$ to be independent of the spectrum, we would need $A_1^{\text{eff}} = \text{const}$ across all problem instances. We show this is impossible for any fixed $V$ by exhibiting a one-parameter family of spectra along which $A_1^{\text{eff}}$ varies.

Consider the two-level family parametrized by $\Delta > 0$: $E_0 = 0$, $E_1 = \Delta$, $d_0 = 1$, $d_1 = N-1$. The final Hamiltonian $H_f(\Delta) = H_z(\Delta) \otimes I + V$ depends continuously on $\Delta$.

**Large $\Delta$ asymptotics.** For $\Delta > 2\|V\|$, the eigenvalues of $H_f(\Delta)$ split into two well-separated clusters: one within $\|V\|$ of $0$ (of size $d_{\text{anc}}$) and one within $\|V\|$ of $\Delta$ (of size $(N-1)d_{\text{anc}}$). The coupling $V$ may split the ground cluster, contributing a $\Delta$-independent constant $C_{\text{ground}}(V) \geq 0$ to $A_1^{\text{eff}}$ (e.g., for $V = \lambda(I \otimes \sigma_x)$, $C_{\text{ground}} = d_0/(4N\lambda)$). The excited cluster at energy $\sim\Delta$ contributes $\Theta((N-1)/(N\Delta))$, which varies with $\Delta$. Therefore $A_1^{\text{eff}}(\Delta) = C_{\text{ground}}(V) + \Theta(1/\Delta)$, a function whose value changes with $\Delta$.

Since the $\Theta(1/\Delta)$ term varies with $\Delta$, $A_1^{\text{eff}}(\Delta)$ is non-constant across the family. Different spectra give different $A_1^{\text{eff}}$, hence different $s^*_{\text{ext}}$. $\square$

**Remark.** This argument does not give a quantitative bound on how much $V$ shifts $s^*$. For couplings that split the ground level of $H_z$ (e.g., $V = \lambda |z_0\rangle\langle z_0| \otimes \sigma_x$), the effective $A_1^{\text{eff}}$ can change drastically - the split creates new levels near $E_0$ with small gaps, adding terms of order $1/\lambda$ to $A_1^{\text{eff}}$. Such couplings make the algorithm slower, not faster. Couplings that do not mix energy levels (e.g., $V$ commuting with $H_z \otimes I$) reduce to the uncoupled case by Theorem 1.

**Numerical verification.** For the instance-independent coupling $V = \lambda (I_N \otimes \sigma_x)$, we compute $s^*_{\text{ext}}$ across four different spectra (Grover $N=4$ and $N=8$ with varying $d_0$, three-level $N=8$) for coupling strengths $\lambda \in \{0.01, 0.05, 0.1, 0.5, 1.0\}$. In every case, the spread of $s^*_{\text{ext}}$ across instances remains nonzero: the coupling shifts all crossing positions but does not collapse them to a single value. For $\lambda = 0.05$, the spread is comparable to the bare spread. For $\lambda = 1.0$, the spread decreases but remains positive ($> 0.01$), confirming the non-constancy proved above.


## Part V: Multi-Segment Rigidity (Theorem 4)

**Theorem 4.** Consider a two-segment adiabatic path within the rank-one framework:

- Segment 1: evolve to some intermediate state $|\psi_{\text{mid}}\rangle$.
- Segment 2: $H_2(t) = -(1-t)|\psi_{\text{mid}}\rangle\langle\psi_{\text{mid}}| + tH_z$, $t \in [0,1]$.

The crossing position in segment 2 is $s^*_2 = B_1/(B_1+1)$ where

$$B_1 = \sum_{k=1}^{M-1} \frac{w_k(\psi_{\text{mid}})}{E_k - E_0}$$

and $w_k(\psi_{\text{mid}}) = \sum_{z \in \Omega_k} |\langle z|\psi_{\text{mid}}\rangle|^2$. If the algorithm is instance-independent (the same $|\psi_{\text{mid}}\rangle$ for all energy assignments), then by Theorem 2, $|\psi_{\text{mid}}\rangle$ must be the uniform superposition, giving $B_1 = A_1$.

**Proof.** Segment 2 has Hamiltonian $H_2(t) = -(1-t)|\psi_{\text{mid}}\rangle\langle\psi_{\text{mid}}| + tH_z$. This is exactly the adiabatic Hamiltonian with initial state $|\psi_{\text{mid}}\rangle$ instead of $|\psi_0\rangle$.

The secular equation for $H_2(t)$ is

$$\frac{1}{1-t} = \sum_{k=0}^{M-1} \frac{w_k(\psi_{\text{mid}})}{tE_k - \lambda}, \tag{SE-2}$$

where $w_k = \sum_{z \in \Omega_k}|\langle z|\psi_{\text{mid}}\rangle|^2$. Setting $\lambda = tE_0$ and ignoring the $k=0$ term (which contributes $O(w_0)$):

$$\frac{1}{1-t} = \frac{B_1}{t}, \quad \Rightarrow \quad t^* = \frac{B_1}{B_1 + 1}.$$

There are two cases for $|\psi_{\text{mid}}\rangle$:

(a) If segment 1 does not involve $H_z$ (e.g., it evolves under an instance-independent Hamiltonian), then $|\psi_{\text{mid}}\rangle$ is the same for all energy assignments. By Theorem 2, the only state giving assignment-independent weights is the uniform superposition, so $|\psi_{\text{mid}}\rangle = |\psi_0\rangle$ (up to phases), giving $w_k = d_k/N$ and $B_1 = A_1$.

(b) If segment 1 involves $H_z$ (which is necessary for the first segment to make progress toward the solution), then $|\psi_{\text{mid}}\rangle$ depends on the spectrum of $H_z$ through the time evolution. In this case, $B_1$ already depends on the spectrum through $|\psi_{\text{mid}}\rangle$.

In either case, the crossing position in the final segment depends on the problem spectrum.

For the multi-segment case with more than two segments, the same dichotomy applies to the final segment: either the previous segments produce an instance-independent intermediate state (forcing uniform overlaps) or an instance-dependent one (introducing spectrum dependence directly). $\square$

**Remark on scope.** Theorem 4 assumes each segment uses a rank-one initial Hamiltonian $-(1-t)|\psi\rangle\langle\psi|$. The paper's open question also asks about "intermediate Hamiltonians at various points in the adiabatic path," which could include non-rank-one interpolating Hamiltonians (e.g., $H(s) = (1-s)H_0 + sH_z$ with $H_0$ of rank $> 1$). The rank-one restriction is essential for the secular equation analysis. The general case remains open.

**Numerical verification.** For Grover $N=4$, $M=1$: uniform midpoint gives $B_1 = 0.75 = A_1$. Biased midpoint $(0.9, 0.2, 0.2, 0.3)/\|{\cdot}\|$ gives $B_1 = 0.17$. Permuting the energy assignment with the biased midpoint changes $B_1$ to $0.96$, confirming that the biased midpoint is not universal.


## Part VI: No-Go Theorem (Theorem 5)

**Theorem 5 (No-Go).** For any adiabatic algorithm using:

1. A rank-one initial Hamiltonian $H_0 = -|\Psi\rangle\langle\Psi|$ (for efficient ground state preparation).
2. A final Hamiltonian whose ground state encodes the solution to an unstructured optimization problem: $H_f = H_z \otimes I + V$ where $H_z = \sum_z E(z)|z\rangle\langle z|$ is the diagonal cost Hamiltonian and $V$ is a fixed (instance-independent) coupling. The ground state of $H_f$ must overlap with the ground space of $H_z$ for the algorithm to solve the optimization problem.
3. Instance-independent design (the same $|\Psi\rangle$, $V$, and schedule for all energy assignments with the same degeneracy structure $\{d_k\}$).

The crossing position cannot be made independent of the problem spectrum. In the uncoupled case ($V = 0$), $\partial s^*/\partial A_1 = 1/(A_1+1)^2 > 0$. In the coupled case ($V \neq 0$), $s^*_{\text{ext}}$ is a non-constant function of the spectrum.

**Proof.** We combine Theorems 1-4.

**Step 1: Instance independence forces uniform superposition.** By condition 3, the algorithm must use the same initial state for all energy assignments. By Theorem 2, the only state giving assignment-independent weights is the uniform superposition (up to permutations within degeneracy classes). So $|\psi\rangle = |\psi_0\rangle$.

**Step 2: Ancillas cannot help.** By Theorem 1, adding uncoupled ancilla qubits with product initial states does not change the crossing position: $s^* = A_1/(A_1+1)$, giving the quantitative sensitivity $\partial s^*/\partial A_1 = 1/(A_1+1)^2 > 0$. By Theorem 3, adding an instance-independent coupling $V$ changes $A_1^{\text{eff}}$, but the resulting $A_1^{\text{eff}}$ remains a non-constant function of the spectrum (proved via the large-$\Delta$ asymptotic argument). The crossing position $s^*_{\text{ext}} = A_1^{\text{eff}}/(A_1^{\text{eff}}+1)$ therefore varies across instances.

**Step 3: Multi-segment paths cannot help.** By Theorem 4, any multi-segment path within the rank-one framework has its final-segment crossing determined by the overlaps of the intermediate state with the computational basis. Instance independence forces uniform overlaps, giving $B_1 = A_1$.

**Step 4: Conclusion.** In the uncoupled case ($V = 0$), the crossing position is $s^* = A_1/(A_1+1)$ with $\partial s^*/\partial A_1 = 1/(A_1+1)^2 > 0$. In the coupled case ($V \neq 0$), $s^*_{\text{ext}}$ is a non-constant function of the spectrum by Theorem 3. In either case, the crossing position cannot be made spectrum-independent. $\square$

**Remark.** For general spectra, $A_1 = (1/N)\sum_{k \geq 1} d_k/(E_k-E_0) \leq (1-d_0/N)/\Delta$, which can exceed 1 when $\Delta < 1$. The derivative $1/(A_1+1)^2$ is always positive regardless of the value of $A_1$.

**Remark.** The no-go applies specifically to the rank-one framework with instance-independent design. Possible escapes include: higher-rank initial Hamiltonians (breaking condition 1), time-dependent couplings $V(s)$ or non-rank-one intermediate Hamiltonians (exploiting gaps in condition 2), and instance-dependent algorithms that measure or estimate spectral properties during execution (breaking condition 3). See Part VII for detailed analysis of each escape route.


## Part VII: Escape Routes

What modifications COULD circumvent the barrier? We classify approaches by which condition of Theorem 5 they violate.

### Breaking Condition 1: Higher-Rank Initial Hamiltonians

Replace $H_0 = -|\psi_0\rangle\langle\psi_0|$ with a rank-$r$ projector $H_0 = -P$ where $P = \sum_{j=1}^r |\psi_j\rangle\langle\psi_j|$. The secular equation changes structure: instead of one scalar equation, one gets an $r \times r$ determinant condition. Part VIII resolves: (i) the first nontrivial case $r=2$, (ii) the general two-level rank-$k$ scaling law, (iii) a multilevel commuting-block extension, and (iv) a noncommuting multilevel root-set no-go via trace drift. The remaining unresolved point is explicit branch-level decoupling in the noncommuting multilevel regime.

### Breaking Condition 2: Time-Dependent Coupling

The paper's open question includes "introducing intermediate Hamiltonians at various points in the adiabatic path." A time-dependent coupling $V(s)$ that varies along the adiabatic path is not covered by Theorem 3 (which assumes $V$ is fixed). In principle, $V(s)$ could reshape the gap profile so that the crossing position shifts to a spectrum-independent point. Since $V(s)$ is chosen before the instance (instance-independent design), it cannot depend on $\{E_k, d_k\}$, but it has more freedom than a fixed $V$. Whether this suffices to eliminate the $A_1$ dependence is open.

### Breaking Condition 2: Non-Rank-One Intermediate Hamiltonians

Multi-segment paths where the intermediate Hamiltonian is not rank-one (e.g., $H(s) = (1-s)H_0 + sH_z$ with $H_0$ a generic Hamiltonian with known ground state) are not covered by Theorem 4. The secular equation structure changes fundamentally, and the universality argument (Theorem 2) no longer applies directly. This is a genuine gap in the no-go result.

### Breaking Condition 3: Instance-Dependent Schedules

If one could estimate $A_1$ (or equivalently $s^*$) efficiently, the optimal schedule could be adapted. The paper proves that computing $A_1$ is NP-hard in general, but approximate estimation might suffice for a near-optimal schedule. The required precision is $\delta s^* = O(\sqrt{d_0/(NA_2)})$, which is exponentially small. Whether a polynomial-time quantum algorithm can achieve this precision remains open.

### Breaking Condition 3: Catalytic Ancilla States

An entangled ancilla state $|\Psi\rangle$ that is not a product state was shown above (extension to Theorem 2) to give no advantage if the final Hamiltonian is uncoupled ($H_f = H_z \otimes I$): the condition $q(z) = 1/N$ is still forced by instance-independence. However, a catalytic scheme where the ancilla is measured mid-computation and the result used to adapt the schedule would break condition 3 (instance-independence). This reduces to the instance-dependent schedule approach.

### Outside the Framework: Non-Adiabatic Protocols

Quantum walks, variational algorithms, and hybrid classical-quantum methods may avoid the adiabatic framework entirely. The paper's forthcoming result on non-adiabatic oscillation (Eduardo) uses the same Hamiltonian $H(s)$, so the $A_1$ barrier applies there too. But protocols that do not interpolate between $H_0$ and $H_z$ could potentially bypass the barrier.

### Outside the Framework: Structured Problems

The entire analysis assumes unstructured problems (no knowledge of which $z$ maps to which $E_k$). For structured problems where the energy landscape has exploitable features (e.g., local structure, symmetry, planted solutions), the optimal schedule might not require $s^*$ at all - the spectral gap profile could be qualitatively different.


## Part VIII: Higher-Rank Initial Hamiltonians

We now analyze the primary escape route from Part VII: higher-rank initial projectors.

### Rank-$k$ secular determinant

Let
$$H_k(s) = sH_z - (1-s)P, \quad P = UU^\dagger,$$
where $U \in \mathbb{C}^{N \times k}$ has orthonormal columns and $\mathrm{rank}(P) = k$.

For $\lambda$ not equal to any eigenvalue of $sH_z$, set
$$D(\lambda,s) = sH_z - \lambda I,\quad G(\lambda,s) = U^\dagger D(\lambda,s)^{-1}U \in \mathbb{C}^{k \times k}.$$

By the matrix determinant lemma:
$$\det(H_k(s)-\lambda I)=\det(D)\det\!\big(I_k-(1-s)G(\lambda,s)\big).$$
Hence the nontrivial eigenvalue condition is
$$\det\!\big(I_k-(1-s)G(\lambda,s)\big)=0. \tag{SE-k}$$

For $k=1$, (SE-k) reduces to the scalar secular equation (SE). For $k>1$, crossings are controlled by a matrix condition.

### Rank-2 specialization

Take
$$P = |\psi_0\rangle\langle\psi_0| + |\phi\rangle\langle\phi|,$$
where $|\phi\rangle \perp |\psi_0\rangle$, $\|\phi\|=1$. In basis $\{|\psi_0\rangle,|\phi\rangle\}$:
$$G(\lambda,s)=
\begin{pmatrix}
g_{11} & g_{12}\\
\overline{g_{12}} & g_{22}
\end{pmatrix},$$
with
$$
g_{11}=\sum_z \frac{1/N}{sE(z)-\lambda},\quad
g_{22}=\sum_z \frac{|\phi_z|^2}{sE(z)-\lambda},\quad
g_{12}=\sum_z \frac{\phi_z/\sqrt{N}}{sE(z)-\lambda}.
$$
Therefore:
$$\big(1-(1-s)g_{11}\big)\big(1-(1-s)g_{22}\big) - (1-s)^2|g_{12}|^2=0. \tag{SE-2}$$

As in Part I, evaluate the reduced crossing proxy at $\lambda=sE_0$ and drop the $k=0$ pole term. Define
$$B_1(\phi)=\sum_{k\ge 1}\frac{b_k}{E_k-E_0},\quad
b_k=\sum_{z\in\Omega_k}|\phi_z|^2,$$
$$C_1(\phi)=\frac{1}{\sqrt{N}}\sum_{k\ge 1}\frac{c_k}{E_k-E_0},\quad
c_k=\sum_{z\in\Omega_k}\phi_z,$$
and $x=(1-s)/s$. Then (SE-2) becomes
$$1 - x(A_1+B_1) + x^2\big(A_1B_1-|C_1|^2\big)=0. \tag{R2}$$

The quadratic coefficient is nonnegative:
$$A_1B_1-|C_1|^2 \ge 0,$$
by Cauchy applied to $\sqrt{w_z}$ and $\sqrt{w_z}\phi_z$ on excited states, where $w_z=(E(z)-E_0)^{-1}$.

### Proposition 6 (Rank-2 Obstruction on Two-Level Families)

Fix $N\ge 3$, a degeneracy $d_0$ with $1\le d_0 < N$, and a normalized state $|\phi\rangle\perp|\psi_0\rangle$, independent of the instance. Consider the two-level family
$$E_0=0,\quad E_1=\Delta,\quad d_1=N-d_0,\quad \Delta>0,$$
with fixed ground set $\Omega_0$ of size $d_0$ and excited set $\Omega_1=\Omega_0^c$.
For the rank-2 projector $P=|\psi_0\rangle\langle\psi_0|+|\phi\rangle\langle\phi|$, every positive reduced crossing root of (R2) has form
$$x(\Delta)=\kappa \Delta,\qquad \kappa>0\ \text{independent of }\Delta,$$
hence
$$s(\Delta)=\frac{1}{1+\kappa\Delta}
=\frac{A_1}{A_1+\kappa\frac{N-d_0}{N}},\qquad A_1=\frac{N-d_0}{N\Delta}.$$
Therefore $s(\Delta)$ is non-constant in $\Delta$ (equivalently non-constant in $A_1$). No fixed instance-independent rank-2 projector can make the crossing position spectrum-independent even on this one-parameter family.

**Proof.** Define
$$a=\frac{N-d_0}{N},\quad p=\sum_{z\in\Omega_0}|\phi_z|^2,\quad q=\sum_{z\in\Omega_1}\phi_z.$$
Then
$$A_1=\frac{a}{\Delta},\quad B_1=\frac{1-p}{\Delta},\quad C_1=\frac{q}{\sqrt{N}\,\Delta}.$$
Substitute in (R2):
$$1-\frac{\alpha}{\Delta}x+\frac{\beta}{\Delta^2}x^2=0,\quad
\alpha=a+1-p>0,\quad
\beta=a(1-p)-\frac{|q|^2}{N}\ge 0.$$
The inequality $\beta\ge 0$ follows from
$$|q|^2 \le (N-d_0)\sum_{z\in\Omega_1}|\phi_z|^2=(N-d_0)(1-p)=Na(1-p).$$

Case 1: $\beta>0$. The positive roots are
$$x_\pm(\Delta)=\Delta\cdot\frac{\alpha\pm\sqrt{\alpha^2-4\beta}}{2\beta}
=\kappa_\pm\Delta,\quad \kappa_\pm>0.$$

Case 2: $\beta=0$. The equation is linear:
$$1-\frac{\alpha}{\Delta}x=0,\quad x(\Delta)=\frac{\Delta}{\alpha}=\kappa\Delta,\ \kappa>0.$$

In both cases, $x(\Delta)=\kappa\Delta$ with $\kappa$ independent of $\Delta$, so
$$s(\Delta)=\frac{1}{1+x(\Delta)}=\frac{1}{1+\kappa\Delta}.$$
This depends on $\Delta$. Since $A_1=a/\Delta$, rewrite
$$s(\Delta)=\frac{A_1}{A_1+\kappa a},$$
which depends nontrivially on $A_1$. $\square$

**Scope note.** Proposition 6 extends the no-go boundary beyond rank one for the first higher-rank case ($k=2$) on all fixed-degeneracy two-level families. It does not resolve arbitrary multilevel spectra or $k\ge 3$.

**Numerical verification.** `lib/ancilla_spectrum.py` now includes `verify_theorem6_rank2`, which checks two fixed rank-2 projectors on $N=8$ across $\Delta \in \{0.5,1,2,4,8\}$ and ground-set sizes $d_0 \in \{1,2,3\}$. It verifies: (i) reduced roots satisfy the quadratic residual to $<10^{-10}$, (ii) branch constants $\kappa$ are $\Delta$-independent, (iii) each branch has nonzero spread in $s(\Delta)$, (iv) the explicit identity $s=A_1/(A_1+\kappa(N-d_0)/N)$ holds numerically on each branch, and (v) reduced roots agree with full exact diagonalization crossing locations (second branch crossing $\lambda=0$) to numerical tolerance. A randomized stress test `deep_verify_theorem6_rank2` checks 1920 random cases over $N\in\{6,8,10,12\}$ and multiple $\Delta$, all passing.

### Proposition 6A (Rank-$k$ Two-Level Scaling Law)

Fix $N\ge 3$, $1\le d_0 < N$, and a fixed rank-$k$ projector $P=UU^\dagger$ with $U\in\mathbb{C}^{N\times k}$ orthonormal columns. On the two-level family
$$E_0=0,\quad E_1=\Delta,\quad d_1=N-d_0,\quad \Delta>0,$$
with fixed ground set $\Omega_0$ and excited set $\Omega_1=\Omega_0^c$, define
$$U_{\mathrm{exc}}=\Pi_{\Omega_1}U,\qquad B=U_{\mathrm{exc}}^\dagger U_{\mathrm{exc}}\succeq 0,\qquad x=\frac{1-s}{s}.$$
Then the reduced crossing equation (ground-pole removed, at $\lambda=sE_0=0$) is
$$\det\!\Big(I_k-\frac{x}{\Delta}B\Big)=0. \tag{Rk-2lvl}$$
Hence for each positive eigenvalue $\mu$ of $B$, there is a reduced root
$$x(\Delta)=\frac{\Delta}{\mu},\qquad
s(\Delta)=\frac{1}{1+\Delta/\mu}
=\frac{A_1}{A_1+\frac{N-d_0}{N\mu}},\qquad
A_1=\frac{N-d_0}{N\Delta}.$$
Therefore every branch with $\mu>0$ is non-constant in $\Delta$ (equivalently in $A_1$). So fixed rank-$k$ projectors cannot make crossing positions spectrum-independent on fixed-degeneracy two-level families unless $B=0$ (the projector has no support on excited states).

**Proof.** Start from the rank-$k$ determinant condition (SE-k):
$$\det(I_k-(1-s)G(\lambda,s))=0,\qquad G(\lambda,s)=U^\dagger(sH_z-\lambda I)^{-1}U.$$
At $\lambda=0$, each excited basis state contributes denominator $s\Delta$ and each ground basis state contributes a pole $1/0^+$. Removing the ground-pole part gives the reduced matrix
$$\widetilde{G}(0,s)=\sum_{z\in\Omega_1}\frac{u_z u_z^\dagger}{s\Delta}
=\frac{1}{s\Delta}U_{\mathrm{exc}}^\dagger U_{\mathrm{exc}}
=\frac{1}{s\Delta}B.$$
So the reduced determinant is
$$\det(I_k-(1-s)\widetilde{G}(0,s))
=\det\!\Big(I_k-\frac{1-s}{s\Delta}B\Big)
=\det\!\Big(I_k-\frac{x}{\Delta}B\Big),$$
which is (Rk-2lvl). If $\mu>0$ is an eigenvalue of $B$, then
$$\det\!\Big(I_k-\frac{x}{\Delta}B\Big)=0
\iff 1-\frac{x}{\Delta}\mu=0
\iff x=\frac{\Delta}{\mu}.$$
Hence
$$s=\frac{1}{1+x}=\frac{1}{1+\Delta/\mu}.$$
Since $A_1=(N-d_0)/(N\Delta)$, substitute $\Delta=(N-d_0)/(NA_1)$ to obtain
$$s=\frac{A_1}{A_1+\frac{N-d_0}{N\mu}}.$$
For fixed $\mu>0$, this is strictly increasing in $A_1$ and non-constant. $\square$

**Numerical verification.** `lib/ancilla_spectrum.py` includes `verify_proposition6A_rankk`, which checks a fixed rank-4 projector on $N=10$, ground-set sizes $d_0\in\{1,2,3\}$, and $\Delta\in\{0.5,1,2,4,8\}$. It verifies constant $\kappa=1/\mu$ across $\Delta$, reduced-matrix residuals below $10^{-10}$, nonzero spread in each branch $s(\Delta)$, and the closed-form identity $s=A_1/(A_1+\kappa(N-d_0)/N)$ branchwise. A randomized stress test `deep_verify_proposition6A_rankk` checks 1296 random cases over $N\in\{8,10,12\}$ and multiple $\Delta$, all passing.

### Proposition 6B (Commuting Multilevel Extension)

Fix a multilevel family with $L \ge 2$ excited levels:
$$E_0 < E_1 < \cdots < E_L,\qquad \Delta_\ell := E_\ell - E_0 > 0,$$
fixed level sets $\Omega_\ell$, and a fixed rank-$k$ projector $P=UU^\dagger$.
Define
$$U_\ell := \Pi_{\Omega_\ell}U,\qquad B_\ell := U_\ell^\dagger U_\ell \succeq 0\quad (\ell=1,\dots,L).$$
Assume the excited blocks commute pairwise:
$$[B_\ell,B_m]=0\quad\forall \ell,m.$$
Then the reduced crossing equation at $\lambda=sE_0$ is
$$\det\!\Big(I_k - x\sum_{\ell=1}^{L}\frac{1}{\Delta_\ell}B_\ell\Big)=0,\qquad x=\frac{1-s}{s}. \tag{Rk-multi}$$
There exists a unitary $W$ and nonnegative coefficients $\mu_{\ell r}$ such that
$$W^\dagger B_\ell W=\mathrm{diag}(\mu_{\ell 1},\dots,\mu_{\ell k}).$$
Hence each active branch $r$ with
$$G_r(\Delta):=\sum_{\ell=1}^{L}\frac{\mu_{\ell r}}{\Delta_\ell}>0$$
has
$$x_r(\Delta)=\frac{1}{G_r(\Delta)},\qquad
s_r(\Delta)=\frac{G_r(\Delta)}{1+G_r(\Delta)}.$$
If one gap $\Delta_j$ varies while others are fixed, then
$$\frac{\partial s_r}{\partial \Delta_j}
=-\frac{\mu_{jr}}{\Delta_j^2(1+G_r)^2}\le 0,$$
with strict inequality whenever $\mu_{jr}>0$. Therefore any active branch with support on a varied level remains spectrum-dependent.

In particular, fixed instance-independent rank-$k$ projectors cannot make all crossing branches spectrum-independent on this commuting multilevel class unless every active branch has zero support on all varied levels.

**Proof.** The reduced form (Rk-multi) follows from (SE-k) exactly as in Proposition 6A, but with level-dependent denominators. Since the $B_\ell$ are Hermitian and commuting, they are simultaneously diagonalizable by a unitary $W$. Conjugating (Rk-multi):
$$\det\!\Big(I_k - x\,W^\dagger\!\Big(\sum_{\ell}\frac{1}{\Delta_\ell}B_\ell\Big)W\Big)
=\prod_{r=1}^{k}\Big(1-x\sum_{\ell=1}^{L}\frac{\mu_{\ell r}}{\Delta_\ell}\Big)=0.$$
So branch $r$ satisfies $x_r=1/G_r$ whenever $G_r>0$, and
$$s_r=\frac{1}{1+x_r}=\frac{G_r}{1+G_r}.$$
If only $\Delta_j$ varies, $G_r(\Delta_j)=C_r+\mu_{jr}/\Delta_j$ with constant $C_r\ge 0$, so
$$\frac{\partial G_r}{\partial \Delta_j}=-\frac{\mu_{jr}}{\Delta_j^2},\qquad
\frac{\partial s_r}{\partial G_r}=\frac{1}{(1+G_r)^2}>0,$$
hence
$$\frac{\partial s_r}{\partial \Delta_j}
=\frac{\partial s_r}{\partial G_r}\frac{\partial G_r}{\partial \Delta_j}
=-\frac{\mu_{jr}}{\Delta_j^2(1+G_r)^2}.$$
This is strictly negative if $\mu_{jr}>0$, so the branch is non-constant in $\Delta_j$. $\square$

**Numerical verification.** `lib/ancilla_spectrum.py` now includes `verify_proposition6B_commuting_multilevel`, which constructs an explicit commuting multilevel projector decomposition with $L=3$, $k=3$, verifies commutators $\|[B_\ell,B_m]\|_F<10^{-10}$, checks reduced residuals below $10^{-10}$, and confirms branchwise monotone dependence on a varied gap whenever $\mu_{jr}>0$. The randomized stress routine `deep_verify_proposition6B_commuting_multilevel` checks 140 random commuting instances (with explicit synthesized projectors), with all cases passing.

### Proposition 6C (General Multilevel Trace No-Go)

Keep the same multilevel setup, but drop the commutation assumption. Define
$$A(\Delta):=\sum_{\ell=1}^{L}\frac{1}{\Delta_\ell}B_\ell,\qquad
\det(I_k-xA(\Delta))=0.$$
Let $\{\lambda_r(\Delta)\}_{r=1}^{k}$ be eigenvalues of $A(\Delta)$ (with multiplicity), and positive reduced roots $x_r(\Delta)=1/\lambda_r(\Delta)$ for $\lambda_r(\Delta)>0$.

If one gap $\Delta_j$ varies and $B_j\neq 0$ (equivalently $\mathrm{tr}(B_j)>0$), then the multiset of positive reduced roots cannot remain constant in $\Delta_j$.

**Proof.** Since $A(\Delta)$ is Hermitian PSD, its eigenvalues are real nonnegative and satisfy
$$\mathrm{tr}(A(\Delta))=\sum_{r=1}^{k}\lambda_r(\Delta)
=\sum_{\ell=1}^{L}\frac{\mathrm{tr}(B_\ell)}{\Delta_\ell}.$$
If all positive roots were constant as $\Delta_j$ varies, then all positive eigenvalues $\lambda_r(\Delta)=1/x_r(\Delta)$ would be constant, so $\mathrm{tr}(A(\Delta))$ would be constant. But
$$\frac{\partial}{\partial \Delta_j}\mathrm{tr}(A(\Delta))
=-\frac{\mathrm{tr}(B_j)}{\Delta_j^2}<0$$
when $\mathrm{tr}(B_j)>0$. Contradiction. Therefore at least one positive reduced root changes with $\Delta_j$. $\square$

**Numerical verification.** `lib/ancilla_spectrum.py` includes `verify_proposition6C_multilevel_trace_nogo`, which uses a noncommuting multilevel instance and checks: (i) commutator norm is nonzero, (ii) exact trace identity $\mathrm{tr}(A)=\sum_\ell \mathrm{tr}(B_\ell)/\Delta_\ell$, (iii) strict trace drift under a varied gap with nonzero trace weight, and (iv) corresponding non-constancy of the reduced root set. The randomized stress routine `deep_verify_proposition6C_multilevel_trace_nogo` checks 140 noncommuting random instances, all passing.

### Remaining obstruction: noncommuting branch-level decoupling

Proposition 6C removes full multiset invariance in the noncommuting regime. The remaining unresolved point is finer branch-level decoupling without commutation: noncommuting blocks can mix eigenspaces as gaps vary, so explicit closed forms for individual branches (like Proposition 6B) are not generally available.


## Part IX: Circumvention Landscape Across Experiments

**Proposition 7 (Circumvention Landscape).** For unstructured ground-state finding, the status of barrier circumvention is:

1. **Can circumvent by leaving fixed-schedule rank-one AQO:**
   (a) Circuit model minimum finding: zero spectral side information and $\Theta(\sqrt{N/d_0})$ queries (Experiment 10, Theorem 2).
   (b) Adaptive adiabatic measurement: zero communicated classical bits and $O(n)$ measurements with $T=O(T_{\inf})$ (Experiment 05, Theorem 1).
   (c) Quantum pre-estimation of $A_1$: additive precision via $O(2^{n/2}\mathrm{poly}(n))$ quantum queries/time in the algorithmically relevant regime (Experiment 13, Theorem 2).
   (d) Structured instances where $A_1$ is tractable classically (for example, exact bounded-treewidth DP and ferromagnetic partition-function bridge; Experiment 08, Propositions 8 and 13; also coarse approximation in Proposition 9).

2. **Cannot circumvent inside fixed instance-independent Hamiltonian engineering analyzed here:**
   (a) Product ancilla extensions (Theorem 1).
   (b) Non-uniform fixed initial states under instance-independence (Theorem 2).
   (c) Fixed instance-independent couplings (Theorem 3).
   (d) Multi-segment rank-one paths (Theorem 4).
   (e) Any rank-one instance-independent modification in aggregate (Theorem 5).
   (f) Rank-2 fixed projector on the fixed-degeneracy two-level families analyzed in Part VIII (Proposition 6).
   (g) More generally, fixed rank-$k$ projectors on fixed-degeneracy two-level families whenever the projector has excited support (Proposition 6A).
   (h) Fixed rank-$k$ projectors on commuting multilevel block families whenever an active branch has support on a varied level (Proposition 6B).
   (i) Even without commutation, full positive-root-set invariance across varied supported multilevel gaps is impossible by trace drift (Proposition 6C).

Hence the barrier is not absolute across computational models, but it is rigid within fixed instance-independent Hamiltonian engineering in the rank-one framework and its higher-rank two-level/multilevel extensions (commuting branchwise and noncommuting root-set level).


## Corollary: Non-Adiabatic Oscillation

The non-adiabatic oscillation algorithm (forthcoming [Eduardo]) uses the time-independent Hamiltonian $H = -|\psi_0\rangle\langle\psi_0| + rH_z$, where $r$ is a parameter that must be chosen close to $A_1$ (within precision $O(2^{-n/2})$) for the algorithm to oscillate between $|\psi_0\rangle$ and the ground state. The required value $r \approx A_1$ depends on the problem spectrum. By the same arguments as Theorem 5 (instance-independence forces uniform superposition, the secular equation structure is the same), no instance-independent choice of $r$ works for all problem instances.

Therefore, the $A_1$ barrier applies to both the adiabatic schedule (which needs $s^* = A_1/(A_1+1)$) and the non-adiabatic oscillation parameter (which needs $r \approx A_1$).
