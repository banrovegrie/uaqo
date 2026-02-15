# Introduction Draft 6

## Notes
- Physics-first opening (Penrose), matching the paper's story
- Narrative: physical picture → AQO mechanism → can it match Grover? → yes but → catch → deeper implications
- Minimized em dashes, colons, semicolons
- Added unitary-evolution insight (why AQO needs adiabatic tracking, not thermal relaxation)
- Added thesis contributions paragraph
- Chapter numbering: Ch 10 = Lean, Ch 11 = Conclusion
- TODO: verify Guo-An 2025 citation key

## Draft

```latex
% Chapter 1: Introduction

Physical systems find their lowest energy states. A ball rolls to the bottom of
a valley, a spin aligns with an external field, a protein folds into the
configuration that minimizes its free energy. In each case the dynamics are
sufficient. No procedure directs the process, no algorithm guides the search.
If the energy landscape of a quantum system could be shaped so that its ground
state encodes the solution to a computational problem, the system would solve
the problem by reaching that state. The cost function becomes an energy
function, the optimal solution becomes the ground state, and the search for a
minimum becomes a physical process.

But quantum evolution is unitary. A system that starts far from the ground
state stays far. The Schr\"odinger equation preserves amplitudes rather than
dissipating energy, and reaching the ground state of a problem Hamiltonian
requires a more deliberate mechanism than preparing the system and waiting.
Adiabatic quantum optimization provides one. Encode the cost function of an
optimization problem as a diagonal Hamiltonian $H_z$ whose ground state is the
optimal solution. Prepare the system in the ground state of a simpler
Hamiltonian $H_0$, one that can be constructed without knowing the answer.
Interpolate slowly from $H_0$ to $H_z$ along the path
$H(s) = (1-s)H_0 + sH_z$. The adiabatic
theorem~\cite{BornFock1928, Kato1950, jansen2007bounds} guarantees that if the
interpolation is slow enough relative to the energy gap above the ground state,
the system tracks its instantaneous ground state throughout. The answer is
delivered not through energy dissipation but through adiabatic tracking. The
ground state of $H_0$ continuously deforms into the ground state of $H_z$.

Farhi, Goldstone, Gutmann, and Sipser proposed this framework in
2000~\cite{farhi2000adiabatic, farhi2001adiabatic} as a method for solving
NP-hard optimization problems encoded in Ising Hamiltonians. Aharonov et
al.~\cite{aharonov2007adiabatic} proved it polynomially equivalent to the
circuit model, and it has since inspired quantum annealing
hardware~\cite{johnson2011quantum} and connected to the complexity of local
Hamiltonians~\cite{kempe2006complexity} and to a broader landscape linking
condensed matter physics and
computation~\cite{hastings2013obstructions, albash2018adiabatic}. But the
question that first motivated the framework has remained open: can adiabatic
quantum optimization find the minimum of an unstructured cost function as fast
as the best quantum algorithm?

The best quantum algorithm for unstructured optimization is Grover's
search~\cite{Grover1996} and its minimum-finding generalization due to
D\"urr and H\o yer~\cite{durr1996quantum}. Given a cost function
$f : \{0,1\}^n \to \mathbb{R}$ with $d_0$ global minima among $N = 2^n$
inputs, no quantum algorithm can find a minimizer in fewer than
$\Theta(\sqrt{N/d_0})$ evaluations of $f$. The lower bound was established by
Bennett et al.~\cite{bennett1997strengths} and
Boyer et al.~\cite{BBHT1998}, and confirmed for adiabatic algorithms by
Farhi et al.~\cite{farhi2008fail}. The speedup over classical search is
quadratic, unconditional, and generic. It requires no structural assumptions
about the cost function. Any adiabatic approach to unstructured optimization
must be measured against this floor.

How fast an adiabatic algorithm runs depends on the spectral gap of the
interpolating Hamiltonian
$H(s) = -(1-s)\ket{\psi_0}\bra{\psi_0} + sH_z$, where $s$ parameterizes
the interpolation from the initial state $\ket{\psi_0}$ to the problem
Hamiltonian $H_z$. The gap controls how quickly the schedule can advance
without exciting the system out of the ground state. The adiabatic condition
ties the schedule velocity to the square of the local gap, so where the gap is
large the schedule can move fast and where it is small the schedule must crawl.
The narrowest point along the interpolation path dominates the total runtime.
For optimization, this narrowest point occurs at an avoided crossing between
the two lowest energy levels of $H(s)$, and the position and width of this
crossing depend on the full spectrum of $H_z$. The eigenvalues, their
degeneracies, and the gaps between successive energy levels all influence where
the bottleneck occurs and how narrow it gets.

Roland and Cerf~\cite{roland2002quantum} showed that for the simplest
nontrivial case, a problem Hamiltonian with only two distinct energy levels
(one for the marked item and one for everything else), an adaptive schedule
that slows near the avoided crossing achieves the Grover
speedup $O(\sqrt{N})$. In this case the crossing sits at $s = 1/2$ by
symmetry, independent of the problem instance, and the schedule can be written
down without knowing anything about the particular cost function. But realistic
optimization problems have richer spectra. A cost function on $n$ bits
generically produces a Hamiltonian with $M$ distinct energy levels and
arbitrary degeneracies. The position of the primary avoided crossing shifts
away from $s = 1/2$ and depends on the spectral data of $H_z$ through a
parameter
\[
  A_1 = \frac{1}{N}\sum_{k=1}^{M-1}\frac{d_k}{E_k - E_0},
\]
a weighted average of inverse excitation energies, where $d_k$ is the
degeneracy of the $k$-th energy level $E_k$. Whether any adiabatic algorithm
could match the Grover lower bound in this general setting has been open since
the framework was
introduced~\cite{farhi2000adiabatic, farhi2001adiabatic}. Znidari\v{c} and
Horvat~\cite{horvat2006exponential} identified the exponentially small gap and
the crossing position through analytical and heuristic arguments, but without
rigorous bounds. Hen~\cite{hen2014continuous} obtained a quadratic speedup for
a specific random Hamiltonian whose symmetry fixes the crossing position
independently of the spectrum. For the full class of diagonal Hamiltonians, no
matching bound with explicit gap estimates and provable runtime has been known.

The answer, established by Braida et
al.~\cite{braida2024unstructured}, is that adiabatic quantum optimization
achieves the runtime $\widetilde{O}(\sqrt{N/d_0})$, hiding polylogarithmic
factors, for any Hamiltonian $H_z$ diagonal in the computational basis whose
spectral gap $\Delta = E_1 - E_0$ satisfies
$\Delta \geq 1/\mathrm{poly}(n)$ (a simplified form of the full spectral
condition developed in Chapter~5). The Ising spin glass Hamiltonians that
encode NP-hard problems like MaxCut and
QUBO~\cite{barahona1982computational, lucas2014ising} satisfy this condition:
their eigenvalues are integers bounded by $\mathrm{poly}(n)$ and they have
$M \in \mathrm{poly}(n)$ distinct energy levels, so $A_1$ and
$A_2 = (1/N)\sum_{k=1}^{M-1} d_k/(E_k - E_0)^2$ remain polynomially bounded
and the runtime reduces to $\widetilde{O}(\sqrt{N/d_0})$, matching the Grover
lower bound. The result requires two ingredients: a piecewise lower bound on
the spectral gap of $H(s)$ that holds for all $s \in [0,1]$, obtained through
a variational argument on the left of the crossing and a resolvent argument
using the Sherman-Morrison formula on the right; and a closed-form expression
for the crossing position $s^* = A_1/(A_1 + 1)$ accurate enough to construct
the adaptive schedule.

The optimality comes with a catch. The adaptive schedule must slow near $s^*$,
which means $A_1$ must be known to additive accuracy $O(2^{-n/2})$ before
evolution begins. Given the $N$ diagonal entries of $H_z$, computing $A_1$ by
brute-force enumeration takes $O(N)$ time. That is the same cost as classical
search. But the hardness runs deeper. Computing $A_1$ to polynomial precision,
$1/\mathrm{poly}(n)$, is NP-hard: a reduction from 3-SAT shows that two
queries to any classical procedure approximating $A_1$ to this precision
suffice to decide satisfiability. Computing $A_1$ exactly, or to
$2^{-\mathrm{poly}(n)}$ precision, is $\#$P-hard: polynomial interpolation
over modified Hamiltonians recovers the full degeneracy sequence
$d_0, d_1, \ldots, d_{M-1}$, and extracting $d_0$ for an Ising Hamiltonian is
equivalent to counting satisfying assignments of a Boolean formula.

The circuit model faces no such obstacle. The D\"urr-H\o yer algorithm
achieves $O(\sqrt{N/d_0})$ without computing $A_1$, without knowing the gap
profile, without traversing an interpolation path, and without encountering an
avoided crossing. It treats the cost function as a black box and extracts the
minimum adaptively, one query at a time. The discrepancy is not a shortcoming
of a particular adiabatic schedule or a failure of analysis. It is a structural
feature of the adiabatic framework for unstructured optimization. The mechanism
of slow interpolation through a gap minimum creates an information requirement
that is absent from the problem itself.

The information cost has precise mathematical structure. An uninformed fixed
schedule, with no knowledge of $A_1$, loses a factor of $\Omega(2^{n/2})$ in
runtime relative to the informed optimum. The entire quantum speedup is
forfeited. Each additional bit of knowledge about $A_1$ halves the penalty,
with no abrupt phase transition between efficient and inefficient regimes.
Quantum measurement during adiabatic evolution recovers the full speedup using
$\Theta(n)$ binary probes of the instantaneous spectrum (Chapter~9).

The limitation is robust. No instance-independent modification within the
rank-one interpolation framework can eliminate the spectrum dependence: not
adding ancilla qubits, not changing the initial state, not coupling auxiliary
systems, not using multi-segment interpolation paths, and not replacing the
rank-one projector with a higher-rank driver (Chapter~9).

The hardness of $A_1$ is counting hardness, not optimization hardness. It
connects not to the difficulty of finding optima but to the difficulty of
computing partition-function-like sums over the spectrum. The tractability
boundary this creates is orthogonal to the standard complexity-theoretic
divisions. Easy optimization can coexist with hard $A_1$. In 2-SAT, the
optimal assignment is found in polynomial time, but the degeneracy structure
that determines $A_1$ remains intractable. The reverse also holds: in Grover
search with a promised degeneracy structure, optimization is hard but $A_1$ is
easy because the spectrum is known. These distinctions organize into a taxonomy
of the information gap that separates the adiabatic and circuit models for
unstructured optimization (Chapter~9).

This thesis gives a self-contained development of these results and extends
them. Chapters~5 through~8 present the work of Braida et al. with deeper
exposition, fuller motivation, and more accessible proofs than the paper
provides. Chapter~9 is original: it formalizes the information gap as a
tractability boundary, proves a separation between informed and uninformed
schedules, analyzes partial-information regimes, develops robust and adaptive
schedule constructions, and connects the results to the recent work of Guo and
An~\cite{guo2025} on gap-informed adiabatic computation. Chapter~10 formalizes
the core arguments in Lean~4 with
Mathlib~\cite{moura2021lean4, mathlib2020}: 330 named theorems, 15 explicit
axioms organized by trust level, and zero unresolved proof obligations.


\section{Structure}
\label{sec:structure}

The argument builds from physics through computation to the information gap.

\begin{itemize}

\item \textbf{Chapter~2.} What does it mean to solve an optimization problem,
and what does physics have to do with it? Cost functions define landscapes over
$\{0,1\}^n$, diagonal Hamiltonians turn optimal solutions into ground states,
and the classical complexity hierarchy constrains what any procedure can
extract. The adiabatic idea emerges naturally from this picture, but as a
heuristic without runtime guarantees.

\item \textbf{Chapter~3.} The quantum search frontier. No quantum algorithm
can find the minimum of an unstructured cost function in fewer than
$\Theta(\sqrt{N/d_0})$ queries, and Grover's algorithm saturates this bound.
This is the floor against which every later adiabatic claim must be measured.

\item \textbf{Chapter~4.} Can continuous Hamiltonian evolution match this
floor? The adiabatic theorem of Jansen, Ruskai, and Seiler provides the
quantitative link between spectral gap and runtime, and the Roland-Cerf
construction achieves the Grover speedup for two-level Hamiltonians. But the
two-level case is special: general Hamiltonians break its symmetry, and the
crossing drifts to a position that depends on the full spectrum.

\item \textbf{Chapter~5.} Permutation symmetry reduces the dynamics of the
interpolating Hamiltonian to a polynomial-dimensional subspace. A secular
equation locates the eigenvalues, and the crossing position $s^*$ and minimum
gap $g_{\min}$ emerge as explicit functions of the spectral parameters $A_1$
and $A_2$.

\item \textbf{Chapter~6.} The gap profile away from the crossing. A
variational argument bounds the gap to the left, and a resolvent argument
exploiting the Sherman-Morrison formula bounds it to the right. Together they
yield a piecewise lower bound that holds for all $s \in [0,1]$.

\item \textbf{Chapter~7.} An adaptive schedule with velocity scaled to the
square of the local gap converts the gap profile of the previous two chapters
into the optimal runtime $\widetilde{O}(\sqrt{N/d_0})$.

\item \textbf{Chapter~8.} The price of optimality. Computing $A_1$ to
polynomial precision is NP-hard, computing it exactly is $\#$P-hard, and a
quantum amplitude estimation algorithm computes it quadratically faster than
any classical procedure in the query model.

\item \textbf{Chapter~9.} The information gap. The exponential penalty for
ignorance of $A_1$, the linear improvement per bit of knowledge, the quantum
bypass through adaptive measurement, the no-go theorems for
instance-independent modifications, and the connections to counting complexity
organize into a taxonomy that is the central contribution of this thesis.

\item \textbf{Chapter~10.} The core arguments are formalized in Lean~4 with
Mathlib: 330 named theorems, 15 explicit axioms organized by trust level, and
zero unresolved proof obligations.

\item \textbf{Chapter~11.} Open problems and directions beyond the published
work.

\end{itemize}

A reader familiar with quantum computation can skim Chapters~2 and~3 and begin
at Chapter~4. A complexity theorist interested in the hardness results can
focus on Chapters~2 through~8. The full argument runs from Chapter~1 through
Chapter~11.

The thread connecting every chapter is a single discrepancy: adiabatic quantum
optimization can match the best quantum algorithm for unstructured search, but
only if it already knows something that is computationally hard to learn.
```
