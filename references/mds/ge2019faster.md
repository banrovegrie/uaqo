# Faster ground state preparation and high-precision ground energy estimation with fewer qubits

Yimin Ge,1 Jordi Tura,1 and J. Ignacio Cirac1 $^ { 1 }$ Max-Planck-Institut f¨ur Quantenoptik, D-85748 Garching, Germany

We propose a general-purpose quantum algorithm for preparing ground states of quantum Hamiltonians from a given trial state. The algorithm is based on techniques recently developed in the context of solving the quantum linear systems problem [1]. We show that, compared to algorithms based on phase estimation, the runtime of our algorithm is exponentially better as a function of the allowed error, and at least quadratically better as a function of the overlap with the trial state. We also show that our algorithm requires fewer ancilla qubits than existing algorithms, making it attractive for early applications of small quantum computers. Additionally, it can be used to determine an unknown ground energy faster than with phase estimation if a very high precision is required.

# I. INTRODUCTION

Quantum computers are expected to have a deep impact in the simulation of large quantum systems, as originally envisioned by Feynman [2]. Of particular interest is the potential ability to study both, the dynamics and low energy properties of many-body quantum systems, which are usually inaccessible classically due to the exponential dimension of the underlying Hilbert space. Quantum computers do not suffer from this representability problem, as one can store states in a number of qubits that only scales logarithmically with that dimension. This fact can be used to develop very efficient algorithms to simulate the dynamics of quantum systems [3–7]. However, preparing certain physically relevant states, like the ground state of a many-body Hamiltonian, may be significantly more difficult. This can be seen as a consequence of ground state preparation likely being hard in full generality, as indeed many variations of ground state energy problems have been proven to be complete for the class QMA [8]. Nevertheless, preparing ground states of Hamiltonians has profound applications in several fields of science so that more efficient quantum algorithms than the ones existing [9–11] are highly desired. This could allow one, for instance, to prepare the initial states that are required to simulate quenches in quantum many-body systems, thus enabling the study of many intriguing and not fully understood phenomena, such as many-body localisation [12] or the presence of thermalisation in closed systems [13], with quantum comptuters. Other applications include single-copy tomography [14] and the construction of QMA witnesses [10]. Furthermore, the ability to determine the ground energy of a Hamiltonian to a high precision also possesses many applications in the fields of physics and quantum chemistry [15], and possibly even in quantum machine learning [16].

Most existing quantum algorithms for ground state preparation are based on one of two methods. First, one could naively attempt to project a trial state $| \phi \rangle$ onto the ground state by measuring the energy of $| \phi \rangle$ using the phase estimation algorithm [9]. The probabily of success is proportional to $| \phi _ { 0 } | ^ { 2 }$ , where $\phi _ { 0 }$ is the overlap of $| \phi \rangle$ with the ground state. Furthermore, straightforward application of phase estimation becomes expensive if a very high fidelity of the prepared state with the real ground state is required. A second class of algorithms is based on variants of the adiabatic algorithm [17]. Here, the target Hamiltonian $H ( 1 )$ is connected to a trivial Hamiltonian $H ( 0 )$ via a path $H ( s )$ , which is slowly changed from $H ( 0 )$ to $H ( 1 )$ . The adiabatic theorem guarantees that if the initial state is the ground state of $H ( 0 )$ , which is assumed to be easily prepared, then for sufficiently long runtimes, the final state will be close to the ground state of $H ( 1 )$ . Rigorous bounds [18] on the runtime however depend inverse polynomially on the minimum spectral gap along the entire path $H ( s )$ , which is generally exponentially small and moreover extremely difficult to calculate or bound in practice. Thus, adiabatic algorithms are often only employed as heuristic methods to first obtain a state with (hopefully) non-trivial overlap with the ground state, which can then subsequently be used as the trial state in phase estimation [19]. This approach is expected to work significantly better than just using random trial states and is the current paradigm e.g. for quantum chemistry applications [15].

In this paper, we propose a quantum algorithm that significantly improves the part played by phase estimation in this approach. More generally, we consider the problem of preparing a good approximation of the ground state from a given trial state. We show that compared to using phase estimation, the runtime of our ground state preparation algorithm scales exponentially better in the allowed error to the real ground state, and polynomially better with the spectral gap and the overlap of the trial state with the ground state. We also show that, in case the ground energy is not known beforehand, the same algorithm can be used to obtain a good estimate of the ground energy to a high precision faster than is possible with phase estimation.

Unlike algorithms based on the adiabatic theorem, whose runtimes always depend on the minimum spectral gap along an entire path of Hamiltonians, all algorithms analysed in this paper only require a lower bound on the spectral gap of the target Hamiltonian. This is a significantly weaker assumption and indeed, for many systems of interest such as in typical critical points, this gap is known to scale only inverse polynomially with the system size.

The outline of the remainder of the paper is as follows. In Section II, we give an overview of the results and a high-level overview of the ideas. In Section III, we give the technical details of the algorithm in case the ground energy is known beforehand. In Section IV, we present the technical details of the algorithm for both, ground state preparation and high-precision ground energy estimation, in case the ground energy is unknown beforehand. We close the main part of the paper with some concluding remarks and open questions in Section V. Appendix A analyses the cost of finding the ground energy with phase estimation. In Appendix B, we demonstrate that if phase estimation is used for ground state preparation, an extremely precise estimate of the ground energy is required beforehand, and analyse the cost of doing so. In Appendix C, we analyse the filtering algorithm from [10]. Finally, in Appendix D, we sketch an alternative approach (inspired by the “Chebyshev method” of [1]) to the problem.

# II. OVERVIEW OF RESULTS

Throughout this paper, let $\tilde { H }$ be an $N \times N$ Hermitian matrix such that its spectrum is contained in $[ 0 , 1 ]$ . We assume that we are given the ability to efficiently perform Hamiltonian simulation of $\tilde { H }$ . More precisely, we require that $e ^ { \pm i { \bar { H } } }$ can be approximated to error $\epsilon ^ { \prime }$ using ${ \cal O } ( \Lambda t \mathrm { p o l y l o g } ( N , 1 / \epsilon ^ { \prime } ) )$ elementary gates1, where $\Lambda$ is the “base cost” of the simulation (e.g., if the simulation algorithm works in the oracle model [5], $\Lambda$ is the gate cost of the oracles). Let $\lambda _ { 0 }$ be the lowest eigenvalue of $\tilde { H }$ , and $| \lambda _ { 0 } \rangle$ be the corresponding eigenstate. For simplicity of notation, we will assume that $\lambda _ { 0 }$ is non-degenerate (all results in this paper trivially generalise to the case when $\lambda _ { 0 }$ is degenerate, see Section V). Suppose that $\Delta$ is a known lower bound on the spectral gap of $\ddot { H }$ .

Suppose moreover that we are given a circuit $\mathcal { C } _ { \phi }$ using $\Phi$ elementary gates that prepares a trial state $| \phi \rangle$ . Let $\phi _ { 0 } : = \langle \lambda _ { 0 } | \phi \rangle$ be its (generally unknown) overlap with the ground state, and $\chi$ be a known lower bound on $| \phi _ { 0 } |$ . We will throughout this paper assume that $\chi = e ^ { - O ( \log N ) }$ . Notice that this is an extremely weak assumption, indeed, this is satisfied even for random states with high probability. The aim of this paper is to prepare a state $\epsilon$ -close to $| \lambda _ { 0 } \rangle$ by (approximately) projecting $| \phi \rangle$ onto its ground state component.

Throughout this paper, we will use the computer science convention for the big- $O$ notation. We furthermore use $\ddot { O }$ to denote the complexity up to polylogarithmic factors in $N$ , $\Delta ^ { - 1 }$ , $\epsilon ^ { - 1 }$ , $| \phi _ { 0 } | ^ { - 1 }$ and $\chi ^ { - 1 }$ . Our first result can now be stated as follows.

Theorem 1 (Ground state preparation for known ground energy). Suppose that $\lambda _ { 0 }$ is known to a precision of $\begin{array} { r } { O ( \Delta / \log { \frac { 1 } { \chi \epsilon } } ) } \end{array}$ . Then, an $\epsilon$ -close state to $| \lambda _ { 0 } \rangle$ can be prepared with constant probability in a gate complexity of

$$
\tilde { O } \left( { \frac { \Lambda } { | \phi _ { 0 } | \Delta } } + { \frac { \Phi } { | \phi _ { 0 } | } } \right) ,
$$

and using

$$
O \left( \log N + \log \log { \frac { 1 } { \epsilon } } + \log { \frac { 1 } { \Delta } } \right)
$$

qubits. Moreover, a flag qubit indicates success.

<table><tr><td>Preparation (ground energy known)</td><td>Gates Qubits</td><td>Required precision + log</td></tr><tr><td>Ö This paper</td><td>Λ Φ ( log N + log log 1 O |φ0|∆ + |φ0|</td><td>Ö(∆)</td></tr><tr><td>b Phase estimation + amp. amplif.</td><td>Λ $ ( 1og N + log - O |φ0|2∆ |φ|) Λ</td><td>∆ O (|φ0|∆) × log 1</td></tr><tr><td>b Filtering (Poulin &amp; Wocjan)</td><td>+ log log 1 Φ ( 1og N + log1 1 O b + log log 1 |φ0|∆ |φ0| 1</td><td>Ö(∆)</td></tr></table>

Although other quantum algorithms for this or similar purposes have previously been proposed [9–11], to the best of our knowledge, the algorithm in this paper, for the case of known ground energy, exhibits the best scaling for both the runtime and the number of qubits amongst all existing algorithms so far (see Table I). For example, the common approach of combining phase estimation with amplitude amplification [20] has a runtime that is exponentially worse in $\epsilon$ , and moreover quadratically worse in $| \phi _ { 0 } |$ (see Appendix B). In fact, an inverse polynomial dependence on $\epsilon$ is common to almost all algorithms that are based on phase estimation [9, 11]. To the best of our knowledge, the only exception is a filtering method proposed by Poulin and Wocjan [10], which was originally designed to quadratically improve the runtime dependence on $| \phi _ { 0 } |$ to obtain a state with low expected energy, and which, as we prove in Appendix C, can also be used to obtain the ground state with a runtime scaling that is polylogarithmic in $\epsilon ^ { - 1 }$ with a suitable choice of parameters2. This however comes at the cost of requiring significantly more ancilla qubits, which makes it challenging for early applications of small quantum computers.

<table><tr><td rowspan="7">(a)</td><td>Preparation (ground energy unknown)</td><td>Gates Λ Φ</td><td colspan="3">Qubits</td></tr><tr><td>This paper Phase estimation + min. label finding</td><td>b + χ∆3/2 xq Λ Φ Ö χ 4∆ + χ</td><td>o O</td><td>(1og N + log log 1 + log 1 € A O (log N + log − + log - ∆ log \}</td></tr><tr><td>Filtering + min. label finding</td><td>Λ Φ Ö + χ∆3/2 x√q</td><td>€ (log N + log 1 + 1</td><td>× log Δ 1 log log 1</td></tr><tr><td>Combined approaches</td><td>Λ</td><td>1</td><td>O (log N + 1og 10g 1) 1</td></tr><tr><td>This paper + phase estimation</td><td>Ö χ 3∆ x)</td><td>( log N + log 1 O</td><td>log X € 1 × lo = log log 1 ∆</td></tr><tr><td>Filtering + phase estimation</td><td>Λ $xacx b χ 3∆</td><td>Qubits</td><td></td></tr><tr><td>Ground energy estimation</td><td>Gates</td><td>ξ</td><td></td></tr><tr><td rowspan="6"></td><td>This paper</td><td>Λ $ Ö + Xξ3/2</td><td>( lo N + log O</td><td>ξ</td></tr><tr><td>Phase estimation + min. label finding</td><td>Λ Φ Ö | χ3ξ χ</td><td>( log N + log O ξ log 1c }$</td><td></td></tr><tr><td>Filtering + min. label finding</td><td>Λ $ Ö χ√ χξ3/2</td><td> (log N + </td><td>lo $\ log log 1</td></tr><tr><td>Combined approaches</td><td>Λ Φ\</td><td>o (log N + log [1)</td><td></td></tr><tr><td>This paper + phase estimation</td><td>Ö χ 3ξ + X</td><td>log $\frac{{ }$</td><td>× log)</td></tr><tr><td>Filtering + phase estimation</td><td>Λ b χ 3ξ χ</td><td>Φ o ( og N +</td><td>log log 1</td></tr></table>

The algorithm can also be adapted for the case when the ground energy is not known beforehand.

Theorem 2 (Ground state preparation for unknown ground energy). If the ground energy is not known beforehand, the same task as in Theorem 1 can be achieved in a gate complexity of

$$
\tilde { O } \left( \frac { \Lambda } { \chi \Delta ^ { 3 / 2 } } + \frac { \Phi } { \chi \sqrt { \Delta } } \right)
$$

and the same number (2) of qubits.

Provided $\Phi$ is not too large (which can be assumed in most practical scenarios), our algorithm for the case of unknown ground energy also has a better runtime scaling than naive phase estimation, and uses significantly fewer qubits than an adaption of Poulin $\&$ Wocjan’s filtering method [10] for this task (see Table IIa).

Furthermore, for very small $\Delta$ , we show that alternatively, the scaling in $\Delta$ can be improved to $\sim \Delta$ at the expense of worsening the scaling in $\chi$ by combining our algorithm with a prior run of phase estimation to first obtain an estimate of the ground energy.

Theorem 3 (Combined algorithm for ground state preparation). The same task as in Theorem $\cdot$ can be achieved in a gate complexity of

$$
\tilde { \cal O } \left( \frac { \Lambda } { \chi ^ { 3 } \Delta ^ { \kappa } } + \frac { \Lambda } { \chi \Delta ^ { ( 3 - \kappa ) / 2 } } + \frac { \Phi } { \chi \Delta ^ { ( 1 - \kappa ) / 2 } } \right)
$$

for any choice of $\kappa \in [ 0 , 1 ]$ , and the same number (2) of qubits.

In particular, choosing $\kappa = 1$ in Theorem 3 yields the optimal scaling in $\Delta$ of $\sim \Delta$ .

We show moreover that, with high probability, the algorithms for the case of unknown ground energy also find the ground energy to a precision of $\bar { O } ( \Delta )$ . Since $\Delta$ can be any reliable lower bound on the spectral gap, this yields a general algorithm for estimating the energy.

Theorem 4 (High-precision ground energy estimation). Let $\xi = \tilde { O } ( \Delta )$ . Then $\lambda _ { 0 }$ can be estimated to an additive precision of $\xi$ in a gate complexity of

$$
\tilde { O } \left( \frac { \Lambda } { \chi \xi ^ { 3 / 2 } } + \frac { \Phi } { \chi \sqrt { \xi } } \right) ,
$$

using $O ( \log N + \log \xi ^ { - 1 } )$ ) qubits. Alternatively, the combined approach of Theorem $\mathcal { J }$ achieves this task in a gate complexity of

$$
\tilde { O } \left( \frac { \Lambda } { \chi ^ { 3 } \xi ^ { \kappa } } + \frac { \Lambda } { \chi \xi ^ { ( 3 - \kappa ) / 2 } } + \frac { \Phi } { \chi \xi ^ { ( 1 - \kappa ) / 2 } } \right)
$$

and the same number of qubits.

Provided that $\Phi$ is not too large, this also scales better than performing the same task with phase estimation and amplitude amplification (see Table IIb).

In terms of query complexities, the coefficients of $\Phi$ and $\Lambda$ in Tables I–II are, up to polylogarithmic factors, the number of calls to $\zeta _ { \phi }$ and (unit time) Hamiltonian simulation, respectively. Note that the qubit requirements stated in Tables I–II exclude ancilla qubits required to preform Hamiltonian simulation3.

Our algorithms are inspired by classical power iteration methods [22]. They are based on techniques (termed the “Fourier method”) that were recently developed for the quantum linear systems problem [1], and are based on the observation that the Linear Combination of Unitaries, or LCU Lemma [5], can be used to implement other functions of a Hamiltonian [23].

We now briefly outline the basic idea of the algorithms. It is easy to see that for positive-semidefinite $H$ with nondegenerate lowest eigenvalue 0, high powers of $\cos H$ approximately project any given state into a state proportional to the unique ground state of $H$ . In case the ground energy of $\ddot { H }$ is known, $\ddot { H }$ can be easily transformed into another Hamiltonian $H$ such that $| \lambda _ { 0 } \rangle$ is the unique eigenvector of $H$ of eigenvalue $\approx 0$ . The outline of the algorithm in that case is as follows:

1. Approximate cos $^ M H$ as a linear combination of terms of the form $e ^ { - i H t _ { k } }$ .   
2. Using the techniques in [1], we implement this linear combination with some amplitude using Hamiltonian simulation and the LCU Lemma.   
3. We use amplitude amplification to boost the overlap with the target state. Alternatively, the fixed point search algorithm [24] can be used for this step.

The outline of the algorithm in case the ground energy is unknown beforehand is as follows:

1. Adapt the previous algorithm into a circuit controlled on an ancilla register $| E \rangle$ , which runs steps 1 and 2 of the previous algorithm, assuming that the ground energy were $E$ .

2. Divide $[ 0 , 1 ]$ into $L = \tilde { O } ( \Delta ^ { - 1 } )$ equally spaced values $E _ { 0 } , \dots , E _ { L - 1 }$ . Run the algorithm with $\sqrt { L ^ { - 1 } } \sum | E _ { j } \rangle$ on the ancilla register.   
3. Use the minimum label finding algorithm (Section $\cdot$ ) to search for the smallest $j$ such the residual state of $| E _ { j } \rangle$ has large norm.   
4. When this search succeeds, then with high probability the resulting $E _ { j }$ is within $\xi$ of the true ground energy and the residual state is a good approximation of the ground state.

The outline of the combined approaches is as follows:

1. Use phase estimation and amplitude amplification to obtain a “crude” estimate of the ground energy. This provides an interval $I$ which is known to contain the real ground energy.   
2. Take $L \approx | I | / \xi$ equally spaced values $E _ { 0 } , E _ { 1 } , \dots E _ { L - 1 }$ in $I$ , and run the previous algorithm with these values of Ej .

# III. ALGORITHM FOR THE CASE OF KNOWN GROUND ENERGY

In this section, we present the main technical analysis of our algorithm and prove Theorem 1. Suppose that the value of $\lambda _ { 0 }$ is known to a precision of $\delta = { \cal O } \left( \Delta / \log \frac { 1 } { \chi \epsilon } \right)$ Let $E$ be a known value such that $0 ~ \le ~ E ~ \le ~ \lambda _ { 0 }$ and $\delta _ { E } : = \lambda _ { 0 } - E < \delta$ . Define $H : = \ddot { H } - ( E - \tau ) \mathbb { 1 }$ for some small value of $^ { \prime }$ chosen below. Then, $| \lambda _ { 0 } \rangle$ is the (unique) ground state of $H$ with eigenvalue $\tau + \delta _ { E }$ , and by assumption all other eigenvalues of $H$ are $\ge \tau + \delta _ { E } + \Delta$ . The method presented here is based on the observation that high powers of $\cos H$ are approximately proportional to projectors onto the ground state:

$$
\cos ^ { M } H \left| \phi \right. = \phi _ { 0 } \cos ^ { M } ( \tau + \delta _ { E } ) \left( \left| \lambda _ { 0 } \right. + \frac { 1 } { \phi _ { 0 } } \frac { \cos ^ { M } H } { \cos ^ { M } ( \tau + \delta _ { E } ) } \left| \lambda _ { 0 } ^ { \perp } \right. \right) .
$$

The norm of the second term is bounded by $| \phi _ { 0 } | ^ { - 1 } e ^ { - O ( M ( \tau + \delta _ { E } ) \Delta ) }$ . Indeed, since $\mathrm { c o s } x$ is concave and decreasing on $[ \tau , 1 + \tau ]$ ,

$$
\begin{array} { r l } & { \left\| \frac { \cos ^ { M } H } { \cos ^ { M } \left( \tau + \delta _ { E } \right) } \left| \lambda _ { 0 } ^ { \perp } \right. \right\| < \left( \frac { \cos ( \tau + \delta _ { E } ) - \sin ( \tau + \delta _ { E } ) \Delta } { \cos ( \tau + \delta _ { E } ) } \right) ^ { M } } \\ & { ~ = ( 1 - \tan ( \tau + \delta _ { E } ) \Delta ) ^ { M } } \\ & { ~ = e ^ { - \Omega ( M \tan ( \tau + \delta _ { E } ) \Delta ) } = e ^ { - \Omega ( M ( \tau + \delta _ { E } ) \Delta ) } , } \end{array}
$$

where in the last step we used $\tan x \geq x$ for $x \in [ 0 , 1 + \tau ]$ . Thus,

$$
\left\| \frac { \cos ^ { M } H | \phi \rangle } { \left\| \cos ^ { M } H | \phi \rangle \right\| } - | \lambda _ { 0 } \rangle \right\| = O ( \epsilon ) ,
$$

provided that

$$
M = \Omega \left( \frac { 1 } { \Delta ( \tau + \delta _ { E } ) } \mathrm { l o g } \frac { 1 } { | \phi _ { 0 } | \epsilon } \right) .
$$

On the other hand, using that $\cos x > 1 - x ^ { 2 } / 2$ ,

$$
\begin{array} { c } { { \displaystyle \cos ^ { M } ( \tau + \delta _ { E } ) > \left( 1 - \frac { ( \tau + \delta _ { E } ) ^ { 2 } } { 2 } \right) ^ { M } } } \\ { { = e ^ { - O ( ( \tau + \delta _ { E } ) ^ { 2 } M ) } . } } \end{array}
$$

Thus,

$$
\| \cos ^ { M } H | \phi \rangle \| = \Omega ( | \phi _ { 0 } | ) ,
$$

provided that $\tau + \delta _ { E } = O ( 1 / \sqrt { M } )$ . Hence, since by assumption $\delta _ { E } < \delta$ , choosing

$$
\tau = \Theta \left( { \frac { \Delta } { \log { \frac { 1 } { \chi \varepsilon } } } } \right)
$$

and

$$
M = \Theta \left( \frac { 1 } { \Delta ^ { 2 } } \log ^ { 2 } \frac { 1 } { \chi \epsilon } \right)
$$

satisfies both (11) and (15).

Our aim in the following is to prepare $\cos ^ { M } H | \phi \rangle$ . The strategy we employ is as follows. First, we approximate $\cos ^ { M } H$ as a linear combination of few unitaries of the form $e ^ { - i H t _ { k } }$ for suitable values of $t _ { k }$ . Second, we implement this linear combination with some amplitude using Hamiltonian simulation and the LCU Lemma [5]. Third, we use amplitude amplification or fixed point search to boost the overlap with the target state.

In the following, assume for simplicity that $M = 2 m$ is even (the algorithm can be adapted to odd $M$ with minor modifications). Observe that

$$
\cos ^ { 2 m } x = { \bigg ( } { \frac { e ^ { i x } + e ^ { - i x } } { 2 } } { \bigg ) } ^ { 2 m } = 2 ^ { - 2 m } \sum _ { k = - m } ^ { m } { \binom { 2 m } { m + k } } e ^ { 2 i k x } .
$$

Note that

$$
2 ^ { - 2 m } \sum _ { k = m _ { 0 } + 1 } ^ { m } \binom { 2 m } { m + k } \leq e ^ { - m _ { 0 } ^ { 2 } / 4 m } .
$$

Indeed, the LHS is the probability of seeing more than $m + m _ { 0 }$ heads when flipping $2 m$ coins, and (19) follows from the Chernoff bound. Thus,

$$
\cos ^ { 2 m } { \cal H } = \sum _ { k = - m _ { 0 } } ^ { m _ { 0 } } \alpha _ { k } e ^ { - 2 i { \cal H } k } + { \cal O } ( \chi \epsilon ) ,
$$

where

$$
\alpha _ { k } : = 2 ^ { - 2 m } { \binom { 2 m } { m + k } } ,
$$

and

$$
m _ { 0 } = \Theta \left( \sqrt { M \log \frac { 1 } { \chi \epsilon } } \right) = \Theta \left( \frac { 1 } { \Delta } \log ^ { 3 / 2 } \frac { 1 } { \chi \epsilon } \right) .
$$

Next, $e ^ { - 2 i H k }$ can be implemented using Hamiltonian simulation algorithms. To implement the RHS of (20), we employ the LCU Lemma: Let $B$ be a circuit on $b : = \lceil \log _ { 2 } ( 2 m _ { 0 } + 1 ) \rceil$ qubits that maps $\left| 0 \right. ^ { \otimes b }$ to

$$
{ B \left| 0 \right. } ^ { \otimes b } : = \frac { 1 } { \sqrt { \alpha } } \sum _ { k = - m _ { 0 } } ^ { m _ { 0 } } \sqrt { \alpha _ { k } } \left| k \right. ,
$$

$\begin{array} { r } { \alpha = \sum _ { k = - m _ { 0 } } ^ { m _ { 0 } } \alpha _ { k } } \end{array}$ , and let $U$ be the controlled Hamiltonian simulation $U \left| k \right. \left| \phi \right. = \left| k \right. e ^ { - 2 i H k } \left| \phi \right.$

$$
\left( B ^ { \dagger } \otimes \mathbb { 1 } \right) U ( B \otimes \mathbb { 1 } ) \left. \phi \right. = \frac { 1 } { \alpha } \left. 0 \right. ^ { \otimes b } \sum _ { k = - m _ { 0 } } ^ { m _ { 0 } } \alpha _ { k } e ^ { - 2 i H k } \left. \phi \right. + \left. R \right.
$$

where $\left( | 0 \rangle \langle 0 | ^ { \otimes b } \otimes \mathbb { 1 } \right) | R \rangle = 0$

The final step of the algorithm is to boost the overlap with amplitude amplification or fixed point search. Measuring the ancillas will then project the state onto

$$
\left| { \lambda _ { 0 } ^ { \prime } } \right. : = \frac { \sum _ { k = - m _ { 0 } } ^ { m _ { 0 } } \alpha _ { k } e ^ { - 2 i H k } \left| \phi \right. } { \left\| \sum _ { k = - m _ { 0 } } ^ { m _ { 0 } } \alpha _ { k } e ^ { - 2 i H k } \left| \phi \right. \right\| }
$$

with probability close to 1. From (20),

$$
\frac { \sum _ { k = - m _ { 0 } } ^ { m _ { 0 } } \alpha _ { k } e ^ { - 2 i H k } | \phi  } { \| \sum _ { k = - m _ { 0 } } ^ { m _ { 0 } } \alpha _ { k } e ^ { - 2 i H k } | \phi  \| } = \frac { \cos ^ { 2 m } H | \phi  } { \| | \cos ^ { 2 m } H | \phi  \| } + O ( \epsilon )
$$

Thus, (11) implies

$$
\vert \lambda _ { 0 } ^ { \prime } \rangle = \vert \lambda _ { 0 } \rangle + O ( \epsilon ) ,
$$

as required. Eq. (15) implies that the number of repetitions is $O \left( \alpha / \| \sum _ { k = - m _ { 0 } } ^ { m _ { 0 } } \alpha _ { k } e ^ { - 2 i H k } | \phi \rangle \| \right) = O \left( \alpha / | \phi _ { 0 } | \right)$

We now calculate the gate count of the entire algorithm. First note that $B$ can be implemented with $O ( 2 ^ { b } ) = O ( m _ { 0 } )$ elementary gates [25]. Next, the gate cost to implement $e ^ { \pm 2 i H }$ to accuracy $\epsilon ^ { \prime }$ in operator norm is $O ( \Lambda \mathrm { p o l y l o g } ( N , \frac { 1 } { \epsilon ^ { \prime } } ) )$ , depending on the precise model and Hamiltonian simulation algorithm used (see [7, Table 1] for an overview). Here, we require $\epsilon ^ { \prime } = O ( \epsilon \vert \phi _ { 0 } \vert / m _ { 0 } )$ . Thus, the gate cost of $U$ is $\begin{array} { r } { O ( m _ { 0 } \Lambda \mathrm { p o l y l o g } ( N , \frac { m _ { 0 } } { \epsilon | \phi _ { 0 } | } ) ) } \end{array}$ [1, Lemma 8]. Note that Hamiltonian simulation with respect to $H$ can be trivially obtained from Hamiltonian simulation with respect to $\ddot { H }$ , either by a phase shift or absorbing these phases into the values of the $\alpha _ { k }$ . Finally, note that $\alpha = O ( 1 )$ and each iteration of amplitude amplification or fixed point search requires $O ( 1 )$ uses of $\zeta _ { \phi }$ , $B$ and $U$ . The final gate complexity is thus

$$
O \left( \frac { 1 } { \left| \phi _ { 0 } \right| } \left( m _ { 0 } \Lambda _ { \mathrm { { \scriptsize ~ D } O I y l o g } } \left( N , \frac { m _ { 0 } } { \epsilon | \phi _ { 0 } | } \right) + \Phi \right) \right) = O \left( \frac { \Lambda } { \left| \phi _ { 0 } \right| \Delta } \mathrm { p o l y l o g } \left( N , \frac { 1 } { \Delta } , \frac { 1 } { \left| \phi _ { 0 } \right| \epsilon } \right) + \frac { \Phi } { \left| \phi _ { 0 } \right| } \right) .
$$

Note that if fixed point search is used for the final step, we also require a good lower bound of $| \phi _ { 0 } |$ . However, we can simply run the algorithm with $O ( 1 / \chi ^ { \prime } )$ repetitions in fixed point search for $\begin{array} { r } { \chi ^ { \prime } = 1 , \frac { 1 } { 2 } , \frac { 1 } { 4 } , \dots . } \end{array}$ until we successfully project the ancillas into $\left| 0 \right. ^ { \otimes ( b + q ) }$ . Indeed, this only results in an overall multiplicative overhead of $O ( \log 1 / | \phi _ { 0 } | )$ , yielding (1). Moreover, whenever we succeed, the resulting state is $| \lambda _ { 0 } ^ { \prime } \rangle$ independently of the value of $\chi ^ { \prime }$ that was used. The number of ancilla qubits required is $b$ plus any ancillas necessary for performing Hamiltonian simulation. Note that the number of ancilla qubits required for implementing $U$ is essentially the same as the number of ancilla qubits required for a single run of $e ^ { \pm 2 i { \bar { H } } }$ , since the latter can be re-used. Thus, the total number of qubits required is given by (2), plus any ancilla qubits required for Hamiltonian simulation (see also [7, Table 1]). This proves Thm. 1. □

# IV. ALGORITHM FOR THE CASE OF UNKNOWN GROUND ENERGY

The algorithm of Theorem 1 presented in the previous section requires an estimate √ $E$ of $\lambda _ { 0 }$ to a precision of $O ( 1 / \sqrt { M } )$ . Since $E$ can simply be viewed as an input parameter, the algorithm can in principle also be run with different values of $E$ . It is easy to see that for any $E \in [ 0 , \lambda _ { 0 } ]$ , the algorithm would, if successful, produce a good approximation of $| \lambda _ { 0 } \rangle$ , but may have an exponentially small probability of success. Thus, if the ground energy is not√ known beforehand, one could simply run the algorithm for increasing values of $E$ , using a step size $O ( 1 / \sqrt { M } )$ , and stop when first successful. It is moreover easy to see that the value of $E$ at which we first succeed is with high probability√ a good estimate of $\lambda _ { 0 }$ . Clearly, the runtime of this algorithm would result in an overall factor of $O ( \sqrt { M } ) = \ddot { O } ( 1 / \Delta )$ compared to Eq. (1).

It turns out that this “classical search” for the correct value of √ √ $E$ can be replaced by a “quantum search” that quadratically improves the overhead from $O ( { \sqrt { M } } )$ to $\tilde { O } ( \sqrt [ 4 ] { M } )$ . We call this search the minimum label finding algorithm, which we describe in Section IV A as a general subroutine, and which may be of independent interest. We then apply this algorithm to the ground state preparation and ground energy estimation problem in Section IV B.

# A. Minimum label finding

In this section, we describe a general subroutine to find the minimum “label” in an ancilla register amongst terms with at least some given amplitude in a given superposition. To motivate this result, consider the following scenario. Suppose we have $L$ unitaries $U _ { 0 } , \dots U _ { L - 1 }$ that prepare the states $U _ { i } \left| 0 \right. \left| 0 \right. = \left| 0 \right. \left| \Phi _ { i } \right. + \left| R _ { i } \right.$ , where $\left( \left| 0 \right. \left. 0 \right| \otimes \mathbb { 1 } \right) \left| R _ { i } \right. = 0$ . Let $\chi \in ( 0 , 1 )$ be a known real number. Suppose we want to approximately find the smallest $_ i$ (or alternatively, prepare the corresponding $\left| { \Phi _ { i } } \right.$ ) such that $\parallel | \Phi _ { i } \rangle \parallel \geq \chi$ . The naive way to do this is to use amplitude estimation (or fixed point search) to increase the amplitude of $| 0 \rangle$ on the first register of $U _ { i } \left| 0 \right. \left| 0 \right.$ for $i = 0 , 1 , \ldots$ , each time using only $O ( 1 / \chi )$ repetitions of $U _ { i }$ , until we first succeed. This requires √ ${ \tilde { O } } ( L / \chi )$ calls to the individual $U _ { i }$ ’s in total. Below, we show that a quadratic improvement in $L$ to ${ \tilde { O } } ( { \sqrt { L } } / \chi )$ can be achieved, provided that performing the controlled version $\begin{array} { r } { U = \sum _ { i } | i \rangle \langle i | \otimes U _ { i } } \end{array}$ can be done with essentially the same cost as the individual $U _ { i }$ ’s. The algorithm is based on a simple binary search technique to successively find the binary digits of the smallest “label” √ √ $i$ amongst the terms in the superposition $\begin{array} { r } { \sqrt { L ^ { - 1 } } \left. 0 \right. \sum _ { i } \left. i \right. \left. \Phi _ { i } \right. + \left. R \right. } \end{array}$ with a norm of at least $\chi / \sqrt { L }$ .

Proposition 1 (Minimum label finding). Let $\mathcal { C } _ { \Phi }$ be a circuit on $q + n + m$ qubits that prepares the state

$$
\left. \Phi \right. : = \mathcal { C } _ { \Phi } \left. 0 \right. ^ { \otimes ( q + n + m ) } = \left. 0 \right. ^ { \otimes q } \sum _ { i = 0 } ^ { 2 ^ { n } - 1 } \left. i \right. \left. \Phi _ { i } \right. + \left. R \right. ,
$$

where $\left| \Phi _ { i } \right.$ are non-normalised $m$ -qubit states and $| R \rangle$ has no overlap with $| 0 \rangle ^ { \otimes q }$ on the first $q$ qubits. Let $\zeta \in ( 0 , 1 )$ be a known real number, and $\tilde { J } , J \in \{ 0 , \ldots , 2 ^ { n } - 1 \}$ be (unknown) integers such that $\parallel | \Phi _ { J } \rangle \parallel \geq \zeta$ and

$$
\sum _ { i = 0 } ^ { \tilde { J } } \|  { | \Phi _ { i } \rangle } \| ^ { 2 } < \zeta ^ { 2 } \frac { \delta } { 4 n \log \frac { n } { \delta } \ln ^ { 2 } \frac { 2 } { \delta } } ,
$$

where $\delta \in ( 0 , 1 / 5 )$ . Then, there exists a quantum algorithm that prepares the state $| j  | \Phi _ { j }  / | | \Phi _ { j }  | |$ for some $j \in [ \tilde { J } , J ]$ with probability at least $1 - 5 \delta$ using

$$
O \left( \frac { n } { \zeta } \log ^ { 2 } \frac { n } { \delta } \right)
$$

calls to $\mathcal { C } _ { \Phi }$

$$
O \left( { \frac { \mathrm { p o l y } ( q , n , m ) } { \zeta } } \log ^ { 2 } { \frac { n } { \delta } } \right)
$$

additional elementary gates, and $q + n + m + 1$ qubits.

The minimum label finding algorithm uses the fixed-point search algorithm [24], which can be thought of as a variation of amplitude amplification, with the additional features that it is not possible “overshoot” the target state, and that only a lower bound on the initial overlap is required to be known. More precisely, let $\boldsymbol { \mathscr { C } }$ be a circuit on $n ^ { \prime }$ qubits that prepares the state $\mathcal { C } \left| 0 \right. ^ { \otimes n ^ { \prime } } = \lambda \left| T \right. + \sqrt { 1 - \lambda ^ { 2 } } \left| \bar { T } \right.$ with $\left. T \middle | \bar { T } \right. = 0$ , and $U$ be a unitary that that satisfies $U | T \rangle | b \rangle = | T \rangle | 1 - b \rangle$ and $U \left| \bar { T } \right. \left| b \right. = \left| \bar { T } \right. \left| b \right.$ for $b \in \{ 0 , 1 \}$ . Then, given input parameters $\lambda ^ { \prime } , \delta \in ( 0 , 1 )$ , the fixed point search $\mathrm { F P S } ( \mathcal { C } , U , \lambda ^ { \prime } , \delta )$ is a circuit on $n ^ { \prime } + 1$ qubits using ${ \cal O } ( \log ( 1 / \delta ) / \lambda ^ { \prime } )$ calls to ${ \mathcal { C } } , { \mathcal { C } } ^ { \dagger } , U$ and ${ \cal O } ( n ^ { \prime 2 } \log ( 1 / \delta ) / \lambda ^ { \prime } )$ elementary gates such that the following hold4:

(ii) If $\lambda \leq \lambda ^ { \prime }$ , then $\begin{array} { r } { | \langle T , 0 | \mathrm { F P S } ( \mathcal { C } , U , \lambda ^ { \prime } , \delta ) \left| 0 \right. ^ { \otimes ( n ^ { \prime } + 1 ) } | \leq 2 \frac { \lambda } { \lambda ^ { \prime } } \ln \frac { 2 } { \delta } . } \end{array}$

Proof. Part (i) is the central result proven in [24]. To prove part (ii), let $\begin{array} { r } { t : = \lceil \frac { 1 } { \lambda ^ { \prime } } \ln \frac { 2 } { \delta } \rceil } \end{array}$ be the number of calls to $c$ . From [24, Eq (1)], the success probability $P$ can be expressed in terms of (generalised) Chebyshev polynomials $\mathcal T _ { t } ( x )$ of the first kind,

$$
P : = | \langle T , 0 | \mathrm { F P S } ( \mathcal { C } , U , \lambda ^ { \prime } , \delta ) | 0 \rangle ^ { \otimes ( n ^ { \prime } + 1 ) } | ^ { 2 } = 1 - \delta ^ { 2 } \mathcal { T } _ { t } \left( \mathcal { T } _ { 1 / t } ( 1 / \delta ) \sqrt { 1 - \lambda ^ { 2 } } \right) ^ { 2 } .
$$

W.l.o.g. assume that $t \geq 5$ , so $\begin{array} { r } { t ( t + 1 ) \leq 2 \left( \frac { 1 } { \lambda ^ { \prime } } \log \frac { 2 } { \delta } \right) ^ { 2 } } \end{array}$ . It thus suffices to prove that $P \leq 2 t ( t + 1 ) \lambda ^ { 2 }$ . Write $\lambda = \sin \theta$ and $\tau : = \mathcal { T } _ { 1 / t } ( 1 / \delta ) = \cosh ( t ^ { - 1 } \operatorname { a r c c o s h } ( 1 / \delta ) ) \geq 1$ . Note that $\mathcal { T } _ { t } ( \tau ) = 1 / \delta$ . Then, using the mean value theorem on the function $\mathcal { T } _ { t } ( x ) ^ { 2 }$ , we obtain

$$
\begin{array} { r l } & { P = 1 - \frac { { \mathcal T } _ { t } ( \tau \cos \theta ) ^ { 2 } } { { \mathcal T } _ { t } ( \tau ) ^ { 2 } } } \\ & { \quad = \tau ( 1 - \cos \theta ) \frac { 2 { \mathcal T } _ { t } ( \xi ) { \mathcal T } _ { t } ^ { \prime } ( \xi ) } { { \mathcal T } _ { t } ( \tau ) ^ { 2 } } } \\ & { \quad = t \tau ( 1 - \cos \theta ) \frac { 2 { \mathcal T } _ { t } ( \xi ) { \mathcal U } _ { t - 1 } ( \xi ) } { { \mathcal T } _ { t } ( \tau ) ^ { 2 } } } \end{array}
$$

4 Note that unlike [24], where $\sqrt { \lambda }$ denotes the overlap, here we write the overlap as $\lambda$ .

for some $\xi \in [ \tau \cos \theta , \tau ]$ , where we used that $\mathcal { T } _ { t } ^ { \prime } ( x ) = t \mathcal { U } _ { t - 1 } ( x )$ . Note that since $\tau \geq 1$ and $\xi \le \tau$ , $| { \mathcal T } _ { t } ( \xi ) | \le { \mathcal T } _ { t } ( \tau )$ and $| \mathcal { U } _ { t - 1 } ( \xi ) | \le \mathcal { U } _ { t - 1 } ( \tau )$ . Indeed, both $\mathcal T _ { t } ( x )$ and $\mathcal { U } _ { t - 1 } ( x )$ attain their maximum moduli on $\lfloor - 1 , 1 \rfloor$ at $x = 1$ , and are monotonically increasing on $[ 1 , \infty )$ . Finally, using the relations

$$
\mathcal { U } _ { t } ( \tau ) = \left\{ \begin{array} { l l } { 1 + 2 \sum _ { k = 1 } ^ { t / 2 } \mathcal { T } _ { 2 k } ( \tau ) } & { t \mathrm { e v e n } } \\ { 2 \sum _ { k = 0 } ^ { ( t - 1 ) / 2 } \mathcal { T } _ { 2 k + 1 } ( \tau ) } & { t \mathrm { o d d } } \end{array} \right.
$$

and $0 < \mathcal { T } _ { k ^ { \prime } } ( \tau ) \leq \mathcal { T } _ { k } ( \tau )$ for $k ^ { \prime } \leq k$ and $\tau \geq 1$ , we obtain

$$
2 \tau \mathcal { U } _ { t - 1 } ( \tau ) = \mathcal { U } _ { t } ( \tau ) + \mathcal { U } _ { t - 2 } ( \tau ) \leq 2 \mathcal { U } _ { t } ( \tau ) \leq 2 ( t + 1 ) \mathcal { T } _ { t } ( \tau ) .
$$

Hence,

$$
P \leq 2 t ( t + 1 ) ( 1 - \cos \theta ) \leq 2 t ( t + 1 ) \sin ^ { 2 } \theta = 2 t ( t + 1 ) \lambda ^ { 2 } ,
$$

as claimed.

Proof of Proposition 1. The algorithm proceeds by successively attempting to find the binary digits $a _ { 1 } , \ldots , a _ { n } \in \{ 0 , 1 \}$ of an integer such that $2 ^ { n - 1 } a _ { 1 } + \cdot \cdot \cdot + a _ { n } \in [ \tilde { J } , J ]$ . The algorithm runs in two stages. In the first stage of the algorithm, suppose that $a _ { 1 } , \dotsc , a _ { k - 1 }$ have already been found. To obtain $a _ { k }$ , we use fixed point search [24] to search for $| 0 \rangle ^ { \otimes q } | a _ { 1 } \dots a _ { k - 1 } 0 \rangle$ on the first $q + k$ qubits, using at most $\begin{array} { r } { O \big ( \frac { 1 } { \zeta } \log \frac { 1 } { \delta ^ { \prime } } \big ) } \end{array}$ repetitions of $\mathcal { C } _ { \Phi }$ . We repeat this search $K$ times. We choose $\delta ^ { \prime } = \delta / ( 2 n \log ( n / \delta ) )$ and $K = \lceil \log ( n / \delta ) \rceil$ . If it succeeds all $K$ times, we set $a _ { k } = 0$ and move on to the next digit $a _ { k + 1 }$ (unless $k = n$ , in which case the algorithm terminates). Otherwise, we search $K$ times for $\left| 0 \right. ^ { \otimes q } \left| a _ { 1 } \dots a _ { k - 1 } 1 \right.$ on the first $q + k$ qubits. If we succeed all $K$ times, we set $a _ { k } = 1$ and move on to the next digit $a _ { k + 1 }$ (unless $k = n$ , in which case the algorithm terminates). If we fail at least once, we say that the result is ’inconclusive’, and we abort the first stage of the algorithm and move on. In the second stage of the algorithm, we successively search for $| 0 \rangle ^ { \otimes q } | a _ { 1 } \dots a _ { k - 1 } \rangle , | 0 \rangle ^ { \otimes q } | a _ { 1 } \dots a _ { k - 2 } \rangle$ , etc., where each search is repeated $K$ times, using $\begin{array} { r } { O ( \frac { 1 } { \zeta } \log \frac { 1 } { \delta ^ { \prime } } ) } \end{array}$ calls to $\mathcal { C } _ { \Phi }$ , until we succeed. Once successful, we measure the remaining ancillas and the algorithm terminates.

We now show that this algorithm produces the required results. Let $J = 2 ^ { n - 1 } b _ { 1 } + 2 ^ { n - 2 } b _ { 2 } + \cdot \cdot \cdot + b _ { n }$ and ${ \ddot { J } } =$ $2 ^ { n - 1 } c _ { 1 } + 2 ^ { n - 2 } c _ { 2 } + \cdot \cdot \cdot + c _ { n }$ be the binary representations of $J , \tilde { J }$ respectively. Let $i _ { 0 }$ be the maximum integer such that $b _ { l } = c _ { l }$ for all $l = 1 , \ldots , i _ { 0 }$ . Since $\ddot { J } < J$ , it follows that $i _ { 0 } < n$ and $b _ { i _ { 0 } + 1 } = 1 , c _ { i _ { 0 } + 1 } = 0$ . Moreover, we say that binary digits $a _ { 1 } , \ldots , a _ { k }$ are ’consistent’ if they are the dominating $k$ binary digits of at least one integer in $[ \tilde { J } , J ]$ .

We first show that the first stage of the algorithm finds at least $i _ { 0 }$ consistent digits with probability at least $1 - 3 \delta$ . For a given $k$ , the probability of finding the wrong $a _ { k }$ given that $a _ { 1 } , \dotsc , a _ { k - 1 }$ are consistent, is at most $\delta / n$ . Indeed, finding too large a value means that $a _ { l } = b _ { l }$ for $l = 1 , \ldots , k - 1$ , $b _ { k } = 0$ and finding $a _ { k } = 1$ . The probability of not finding $\left| 0 \right. ^ { \otimes q } \left| b _ { 1 } \dots b _ { k } \right.$ $K$ times is $\delta ^ { \prime K } < \delta / n$ [24]. On the other hand, from Lemma 1(ii), the probability of finding too small a value for a single trial of the search is upper bounded by

$$
\begin{array} { l } { \displaystyle \frac { 2 \ln ^ { 2 } \frac { 2 } { \delta } } { \zeta ^ { 2 } } \sum _ { j = 0 } ^ { \cal J } \| | \Phi _ { j } \rangle \| ^ { 2 } < \frac { \delta } { 2 n \log \frac { n } { \delta } } } \\ { \displaystyle ~ < \frac { 1 } { 2 } . } \end{array}
$$

Thus, the probability of finding too small a value is at most $2 ^ { - K } < \delta / n$ . Moreover, for a given $k < i _ { 0 }$ , the probability of finding an inconclusive result is at most $\delta ^ { \prime } K < \delta / n$ . Thus, the probability of not finding at least $i _ { 0 }$ consistent digits in the first stage of the algorithm is at most

$$
n ( \delta ^ { \prime K } + 2 ^ { - K } + \delta ^ { \prime } K ) < 3 \delta .
$$

Suppose now that we found $k \geq i _ { 0 }$ consistent digits and then found an inconclusive result. Let $i _ { 1 } \le k$ be the largest integer such that $a _ { l } = b _ { l }$ for $l = 1 , \ldots , i _ { 1 }$ . Clearly, $i _ { 1 } \geq i _ { 0 }$ . If $i _ { 1 } < k$ , then $a _ { i _ { 1 } + 1 } = 0$ and $b _ { i _ { 1 } + 1 } = 1$ , since $a _ { 1 } , \ldots , a _ { k }$ are consistent. Thus, for all $l > i _ { 1 }$ , if the algorithm successfully finds $\left| 0 \right. ^ { \otimes q } \left| a _ { 1 } \ldots a _ { l } \right.$ , then upon measuring the other ancillas, we obtain a value $j \leq J$ . For a single trial of the search, the probability of finding a value $j < \tilde { J }$ is at most (40). Thus, for a given $\it { \Delta } l$ , the total probability of finding a value $j < j$ is at most $K$ times (40), i.e. at most $\delta / n$ .

The last possibility for the algorithm to fail is if the algorithm fails to find $\left| a _ { 1 } \ldots a _ { i _ { 1 } } \right.$ in the second stage. Let $p _ { i _ { 1 } }$ be the probability of a single run of the search finding $\left| 0 \right. ^ { \otimes q } \left| a _ { 1 } \ldots a _ { i _ { 1 } } \right.$ . Then, conditional on reaching this stage of the algorithm, the probability of failing is $( 1 - p _ { i _ { 1 } } ) ^ { K }$ . Notice however that this event is conditional on first successfully finding $\left| 0 \right. ^ { \otimes q } \left| a _ { 1 } \ldots a _ { i _ { 1 } } \right.$ $K$ times in the first stage of the algorithm. The probability of this event is $p _ { i _ { 1 } } ^ { K }$ . Thus, the overall probability of the algorithm failing in this way is $( p _ { i _ { 1 } } ( 1 - p _ { i _ { 1 } } ) ) ^ { K } \leq 4 ^ { - K }$ . Thus, the probability of the algorithm failing in the second stage is at most

$$
\delta + \sum _ { i _ { 1 } = 1 } ^ { n } ( p _ { i _ { 1 } } ( 1 - p _ { i _ { 1 } } ) ) ^ { K } \leq \delta + n 4 ^ { - K } \leq 2 \delta ,
$$

where the first $\delta$ comes from the upper bound on the probability of finding $j < j$ in the second stage. Thus, the total probability of the algorithm failing is at most (42) plus (43), as claimed. The number of calls to $\mathcal { C } _ { \Phi }$ and additional elementary gates is

$$
O \left( n K \frac { 1 } { \zeta } \log \frac { 1 } { \delta ^ { \prime } } \right) = O \left( \frac { n } { \zeta } \log ^ { 2 } \frac { n } { \delta } \right) ,
$$

as claimed.

Notice that if only the first $n ^ { \prime } < n$ dominant binary digits of an integer in $[ \tilde { J } , J ]$ is needed, $n$ can be replaced with $n ^ { \prime }$ in (30) and (31). Moreover, it is clear that the $\zeta ^ { 2 }$ dependence in (30) is optimal.

# B. Proof of Theorems 2–4

With $M$ and $\tau$ defined as in Section III, let √ $L \ = \ \Theta ( { \sqrt { M } } )$ be a power of 2 and define $E _ { j } : = j / L$ . Clearly, $E _ { j + 1 } - E _ { j } \in O ( 1 / \sqrt { M } )$ . Define $\delta _ { j } : = \lambda _ { 0 } - E _ { j }$ and $H _ { j } : = \tilde { H } - ( E _ { j } - \tau ) \mathbb { 1 }$ . Let $J \in \{ 0 , \ldots , L - 1 \}$ be the largest integer such that $E _ { J } \leq \lambda _ { 0 }$ . Clearly, $\delta _ { J } \in O ( 1 / \sqrt { M } )$ . Using the algorithm from Section III, we have unitaries $V _ { j }$ such that

$$
V _ { j } \left| 0 \right. ^ { \otimes ( b + q ) } \left| \phi \right. = \left| 0 \right. ^ { \otimes ( b + q ) } \mathcal { G } _ { j } \left| \phi \right. + \left| R \right. ,
$$

where

$$
\mathcal { G } _ { j } = \frac { 1 } { \alpha } \sum _ { k = - m _ { 0 } } ^ { m _ { 0 } } \alpha _ { k } e ^ { - 2 i H _ { j } k } ,
$$

and $( | 0   0 | ^ { \otimes ( b + q ) } \otimes \mathbb { 1 } ) | R  = 0$ . The gate cost of a single $V _ { j }$ is given by

$$
\tilde { O } \left( \frac { \Lambda } { \Delta } \right) .
$$

We now introduce an additional ancilla system $\mathcal { L }$ on $l : = \lceil \log _ { 2 } L \rceil$ qubits. Let $V$ be the $V _ { j }$ ’s controlled on $\mathcal { L }$ , i.e. $\begin{array} { r } { V = \sum _ { j = 0 } ^ { L - 1 } | j \rangle \langle j | _ { \mathcal { L } } \otimes V _ { j } } \end{array}$ . Then,

$$
V \left| + \right. _ { \mathscr { L } } ^ { \otimes l } \left| 0 \right. ^ { \otimes \left( b + q \right) } \left| \phi \right. = \frac { 1 } { \sqrt { L } } \sum _ { j = 0 } ^ { L - 1 } \left| j \right. _ { \mathscr { L } } \left| 0 \right. ^ { \otimes \left( b + q \right) } \mathscr { G } _ { j } \left| \phi \right. + \left| R \right. ,
$$

where $\left( \mathbb { 1 } _ { \mathcal { L } } \otimes | 0 \rangle \langle 0 | ^ { \otimes ( b + q ) } \otimes \mathbb { 1 } \right) | R \rangle = 0$ . From (11) and (20),

$$
\left\| \frac { \mathcal { G } _ { j } \left| \phi \right. } { \left\| \mathcal { G } _ { j } \left| \phi \right. \right\| } - \left| \lambda _ { 0 } \right. \right\| = O ( \epsilon ) ,
$$

whenever $E _ { j } \leq \lambda _ { 0 }$ , and $\| \mathcal { G } _ { j } \left| \phi \right. \| = \Theta \left( | \phi _ { 0 } | \cos ( \tau + \delta _ { j } ) ^ { M } \right)$ . In particular, $\| \mathcal { G } _ { J } \left| \phi \right. \| = \Omega ( | \phi _ { 0 } | )$ .

We now show that we can use the minimum label finding algorithm to project (48) onto the state $\left| j \right. _ { \mathcal { L } } \mathcal { G } _ { j } \left| \phi \right. / \left| \left| \mathcal { G } _ { j } \left| \phi \right. \right| \right|$

for some $j \in [ \tilde { J } , J ]$ and suitable $\ddot { J }$ . Indeed, for any integer $\ddot { J }$ ,

$$
\begin{array} { r l } { \displaystyle \sum _ { i = 0 } ^ { J } | E _ { i } | \partial | | ^ { 2 } - \mathcal { O } ( \displaystyle \sum _ { i = 0 } ^ { J } | E _ { i } | ^ { 2 } \cos ( \nu _ { i } ( \cdot + \delta _ { i j } ) | ^ { 2 \delta _ { i j } } ) } & { } \\ & { ~ - \mathcal { O } ( | ( \delta _ { i j } ) | ^ { 2 } \displaystyle \sum _ { j = 0 } ^ { J } \nu _ { i j } ( \cdot ) ^ { 2 } \mathrm { d } | \nu _ { j i } ( \cdot ) } \\ & { ~ - \mathcal { O } ( | ( \delta _ { i j } ) | ^ { 2 } \displaystyle \sum _ { j = 0 } ^ { J } e ^ { - \alpha _ { i } ( \cdot + \delta _ { i j } ) | \nu _ { i j } ( \cdot ) } ) } \\ & { ~ - \mathcal { O } ( | ( \delta _ { i j } ) | ^ { 2 } \displaystyle \sum _ { j = 0 } ^ { J } e ^ { - \alpha _ { i } ( \cdot + \delta _ { i j } ) | \nu _ { i j } ( \cdot ) } ) } \\ & { = \mathcal { O } ( | ( \delta _ { i j } ) | ^ { 2 } \displaystyle \sum _ { j = 0 } ^ { J } e ^ { - \alpha _ { i } ( \cdot + \delta _ { i j } ) | \nu _ { i j } ( \cdot ) } ) } \\ & { = \mathcal { O } ( | ( \delta _ { i j } ) | ^ { 2 } e ^ { - \alpha _ { i } ( \cdot + \delta _ { i j } ) | \nu _ { i j } ( \cdot ) } ) } \\ & { ~ - \mathcal { O } ( | ( \delta _ { i j } ) | ^ { 2 } e ^ { - \alpha _ { i } ( \cdot + \delta _ { i j } ) | \nu _ { i j } ( \cdot ) } ) } \\ & { ~ - \mathcal { O } ( | ( \delta _ { i j } ) | ^ { 2 } e ^ { - \alpha _ { i } ( \cdot + \delta _ { i j } ) | \nu _ { i j } ( \cdot ) } ) . } \end{array}
$$

where the last step follows from (16). Thus, since $\chi$ is a known lower bound on $| \phi _ { 0 } |$ satisfying $\log ( | \phi _ { 0 } | / \chi ) = O ( \log N )$ , we can ensure that

$$
\sum _ { j = 0 } ^ { \tilde { J } } \| \mathcal { G } _ { j } \left| \phi \right. \| ^ { 2 } = O \left( \frac { \chi ^ { 2 } } { \log M } \right) ,
$$

provided that

$$
\delta _ { \tilde { J } } = \Theta \left( \frac { 1 } { \sqrt { M } } \log \frac { | \phi _ { 0 } | ^ { 2 } \log M } { \chi ^ { 2 } } \right) = \tilde { \Theta } ( \Delta ) .
$$

Thus, by Proposition √ $^ { 1 }$ , we can with high probability prepare the state $\left| j \right. _ { \mathcal { L } } \mathcal { G } _ { j } \left| \phi \right. / \left| \left| \mathcal { G } _ { j } \left| \phi \right. \right| \right|$ for some $j \in [ \bar { J } , J ]$ using ${ \tilde { O } } ( { \sqrt { L } } / \chi )$ repetitions of $V$ and $\mathcal { C } _ { \phi }$ . The value in the $\mathcal { L }$ register gives an estimate of the ground energy to a precision of (58). From (49), the second register then contains the desired approximation of the ground state.

Notice that $V$ can be implemented with essentially the same cost as a single $V _ { j }$ . Indeed, the only explicit dependence of $V _ { j }$ on $j$ is in the call to Hamiltonian simulation, $e ^ { \pm 2 i H _ { j } } = e ^ { \pm 2 i ( \tau - E _ { j } ) } e ^ { \pm 2 i \vec { H } }$ . Thus, given access to $e ^ { \pm 2 i { \bar { H } } }$ , it is easy to implement

$$
\sum _ { j = 0 } ^ { L - 1 } | j \rangle \langle j | \otimes e ^ { \pm 2 i H _ { j } } = \sum _ { j = 0 } ^ { L - 1 } | j \rangle \langle j | \otimes e ^ { \pm 2 i ( \tau - E _ { j } ) } e ^ { \pm 2 i \tilde { H } }
$$

with a single call to $e ^ { \pm 2 i { \bar { H } } }$ and $O ( \log L ) = \ddot { O } ( 1 )$ additional elementary gates implementing the phases $e ^ { \pm 2 i ( \tau - E _ { j } ) }$ . Hence, the overall gate cost of this algorithm is

$$
\tilde { O } \left( \frac { \sqrt { L } } { \chi } \left( \frac { \Lambda } { \Delta } + \Phi \right) \right) = \tilde { O } \left( \frac { \Lambda } { \chi \Delta ^ { 3 / 2 } } + \frac { \Phi } { \chi \sqrt { \Delta } } \right) ,
$$

as claimed. This proves Theorem 2.

Alternatively, one can combine this algorithm with the prior use of phase estimation. This approach improves the scaling with $\Delta$ at the cost of a worse scaling in $\chi$ , and is hence useful if $\Delta$ is very small.

First we use the method from Appendix A to obtain a “crude” estimate of the ground energy, to a precision of $\xi = O ( \Delta ^ { \kappa } )$ for some $\kappa \in [ 0 , 1 ]$ to be chosen later. The runtime of this is

$$
\tilde { O } \left( \frac { \Lambda } { \chi ^ { 3 } \Delta ^ { \kappa } } + \frac { \Phi } { \chi } \right)
$$

gates (see Appendix A). This provides us with an interval $[ a , b ] \ni \lambda _ { 0 }$ with $b - a = O ( \Delta ^ { \kappa } )$ . Let $E _ { j } ^ { \prime } = a + ( b - a ) j / L ^ { \prime }$ , where $L ^ { \prime } = \Theta ( M \Delta ^ { \kappa } )$ . Writing $H _ { j } ^ { \prime } = \ddot { H } - ( E _ { j } ^ { \prime } - \tau ) \mathbb { 1 }$ and

$$
\mathcal { G } _ { j } ^ { \prime } = \frac { 1 } { \alpha } \sum _ { k = 0 } ^ { m _ { 0 } } \alpha _ { k } e ^ { - 2 i H _ { j } ^ { \prime } k } ,
$$

we run the previous algorithm but with

$$
V ^ { \prime } \left| + \right. _ { \mathscr { L } ^ { \prime } } ^ { \otimes l ^ { \prime } } \left| 0 \right. ^ { \otimes \left( b + q \right) } \left| \phi \right. = \frac { 1 } { \sqrt { L ^ { \prime } } } \sum _ { j = 0 } ^ { L ^ { \prime } - 1 } \left| j \right. _ { \mathscr { L } ^ { \prime } } \left| 0 \right. ^ { \otimes \left( b + q \right) } \mathscr { G } _ { j } ^ { \prime } \left| \phi \right. + \left| R \right.
$$

instead of (48), and an ancilla system $\mathcal { L } ^ { \prime }$ on $l ^ { \prime } = \lceil \log _ { 2 } L ^ { \prime } \rceil$ qubits instead of $\mathcal { L }$ . The algorithm now requires $O ( \sqrt { L ^ { \prime } / \chi } )$ repetitions of $V ^ { \prime }$ . As before, the cost of $V ^ { \prime }$ is given by (47). Hence, the number of gates for projecting (63) onto the target state is

$$
\tilde { \cal O } \left( \frac { \sqrt { L ^ { \prime } } } { \chi } \left( \frac { \Lambda } { \Delta } + \Phi \right) \right) = \tilde { \cal O } \left( \frac { \Lambda } { \chi \Delta ^ { \left( 3 - \kappa \right) / 2 } } + \frac { \Phi } { \chi \Delta ^ { \left( 1 - \kappa \right) / 2 } } \right) .
$$

The total number of gates for the algorithm is thus (64) plus the gate cost (61) from the prior use of phase estimation, .e.,

$$
\tilde { \cal O } \left( \frac { \Lambda } { \chi ^ { 3 } \Delta ^ { \kappa } } + \frac { \Lambda } { \chi \Delta ^ { ( 3 - \kappa ) / 2 } } + \frac { \Phi } { \chi \Delta ^ { ( 1 - \kappa ) / 2 } } \right) .
$$

This proves Theorem 3.

It is easy to see that both algorithms can be used to estimate the ground energy to an arbitrarily small precision $\xi$ , provided that $\xi$ is less than (58). Indeed, the entire algorithm has $\Delta$ as an input parameter, which is only required to be a lower bound on the spectral gap rather than the spectral gap itself. Hence, if we run the algorithm with $\Delta ^ { \prime } \ll \Delta$ , we obtain an estimate of the ground state to a precision of $\xi = \tilde { O } ( \Delta ^ { \prime } )$ . The algorithm can thus be used to estimate the ground state to an arbitrary precision $\xi < \Delta$ in a gate complexity of

$$
\tilde { O } \left( \frac { \Lambda } { \chi \xi ^ { 3 / 2 } } + \frac { \Phi } { \chi \sqrt { \xi } } \right) ,
$$

for the first algorithm, and

$$
\tilde { O } \left( \frac { \Lambda } { \chi ^ { 3 } \xi ^ { \kappa } } + \frac { \Lambda } { \chi \xi ^ { ( 3 - \kappa ) / 2 } } + \frac { \Phi } { \chi \xi ^ { ( 1 - \kappa ) / 2 } } \right)
$$

for the combined approach. This proves Theorem 4.

Note that choosing $\kappa = 1$ in the combined algorithm gives the optimal scaling of $\sim 1 / \Delta$ with $\Delta$ . However, it is obviously also possible to choose different values of $\kappa$ that also take the other parameters into account.

# V. CONCLUSION

In this paper, we presented quantum algorithms to prepare the ground state of a Hamiltonian faster and with fewer qubits than with previous methods, both in the case of known and unknown ground energy. In the latter scenario, the algorithm also provides a high precision estimate of the ground energy in a complexity faster than with phase estimation and amplitude amplification.

Perhaps surprisingly, the straightforward use of phase estimation and amplitude amplification has a significantly worse scaling in the overlap of the trial state with the ground state than what one would naively expect. In Appendix B, we show that straightforward phase estimation requires

$$
\tilde { O } \left( \frac { \Lambda } { | \phi _ { 0 } | ^ { 2 } \Delta \epsilon } + \frac { \Phi } { | \phi _ { 0 } | } \right)
$$

gates to prepare the ground state, provided the ground energy is known to a precision of $O ( | \phi _ { 0 } | \epsilon \Delta )$ beforehand. Notice in particular the $1 / | \phi _ { 0 } | ^ { 2 }$ scaling, even after using amplitude amplification. The scaling becomes even worse if the ground energy is not known beforehand (see Table IIa).

Previous improvements by Poulin and Wocjan [10] to the phase estimation approach quadratically improved the dependence on $| \phi _ { 0 } |$ . Moreover, we prove in Appendix C that for suitable choices of parameters, this algorithm can prepare the ground state in the same runtime as our algorithm. The algorithms in this paper however use significantly fewer qubits, which make them more attractive for early applications of quantum computing.

In the case of known ground energy, no non-trivial prior knowledge of the value of $| \phi _ { 0 } |$ is required for any algorithm discussed in this paper (although for the filtering method, the number of qubits required becomes worse if no nontrivial lower bound is known). However, in case of unknown ground energy, the runtime dependences on $| \phi _ { 0 } |$ are replaced by dependences on the known lower bound $\chi$ of $| \phi _ { 0 } |$ . There appears to be a systematic reason for this which seems difficult to overcome: broadly speaking, all methods discussed in this paper produce a state of the form $\textstyle \sum _ { j } | E _ { j } \rangle | \Phi _ { j } \rangle$ , where $| \Phi _ { j } \rangle$ is approximately proportional to the ground state and $\parallel | \Phi _ { j } \rangle \parallel \approx | \phi _ { 0 } |$ if $E _ { j } \approx \lambda _ { 0 }$ , and $\| | \Phi _ { j } \rangle \| \ll | \phi _ { 0 } |$ if $E _ { j } \ll \lambda _ { 0 }$ . Any search for the “correct” value of $j$ needs to be able to distinguish the following two cases: (i) $\lambda _ { 0 } = \lambda _ { 0 } ^ { ( 1 ) }$ and $\phi _ { 0 } = \phi _ { 0 } ^ { ( 1 ) }$ , and (ii) $\lambda _ { 0 } = \lambda _ { 0 } ^ { ( 2 ) }$ and $\phi _ { 0 } = \phi _ { 0 } ^ { ( 2 ) }$ , where $\lambda _ { 0 } ^ { ( 1 ) } \ll \lambda _ { 0 } ^ { ( 2 ) }$ and $| \phi _ { 0 } ^ { ( 1 ) } | \ll | \phi _ { 0 } ^ { ( 2 ) } |$ . Any use of amplitude amplification to distinguish these cases would require many, i.e. ${ \cal O } \left( 1 / | \phi _ { 0 } ^ { ( 1 ) } | \right)$ repetitions to “see” if (i) is the case, which means that if in fact (ii) is the case, significantly more repetitions than $O \left( 1 / | \phi _ { 0 } ^ { ( 2 ) } | \right)$ have been performed. On the other hand, if only $O \left( 1 / | \phi _ { 0 } ^ { ( 2 ) } | \right)$ repetitions are performed, one would accidentally find a much larger value (e.g. $\lambda _ { 0 } ^ { ( 2 ) }$ ) than the true ground energy $\lambda _ { 0 } ^ { ( 1 ) }$ (and hence also prepare the wrong state) if in fact (i) is the case. We currently do not see a way to get around this problem.

For simplicity of notation, we assumed throughout this paper that the ground energy of $\ddot { H }$ is non-degenerate. The algorithm however trivially generalises to degenerate ground spaces. Indeed, the only thing that changes in this case is that the resulting state $| \lambda _ { 0 } ^ { \prime } \rangle$ is $\epsilon$ -close to $\left| \lambda _ { 0 } \right. = P \left| \phi \right. / \left| \left| P \left| \phi \right. \right| \right|$ , where $P$ is the projector onto the ground space of $\ddot { H }$ . The algorithm also generalises to the case of only approximately degenerate ground spaces, i.e. when the spectrum of $\ddot { H }$ is contained in $[ \lambda _ { 0 } , \lambda _ { 0 } + \varepsilon ] \cup [ \lambda _ { 0 } + \Delta , 1 ]$ with $\varepsilon \ll \Delta$ .

Finally, given the close relation of this work to [1], it is also natural to expect that the alternative approach of [1] using Chebyshev polynomials and quantum walks can be used to get a different algorithm with the same runtime scaling. This is indeed possible, as we show in Appendix D. These algorithms however are restricted to the case where $\tilde { H }$ is a sparse Hamiltonian with quantum oracle access. By contrast, the advantage of the approach based on Hamiltonian simulation is that it can be applied outside the framework of given oracle access to $H$ , as efficient Hamiltonian simulation algorithms exist for other models of accessing the Hamiltonian [4, 7].

# ACKNOWLEDGMENTS

YG thanks H. Buhrman, V. Dunjko, A. Gily´en, D. Gosset, R. Kothari, G. Low, A. Moln´ar, A. Montanaro, and N. Schuch for helpful discussions. This work was supported by the ERC grant QUENOCOBA, ERC-2016-ADG, grant no. 742102. JT acknowledges funding from the EU’s Horizon 2020 research and innovation programme under the Marie Sk lodowska-Curie grant agreement No 748549.

[15] M.-H. Yung, J. D. Whitfield, S. Boixo, D. G. Tempel, and A. Aspuru-Guzik, “Introduction to quantum algorithms for physics and chemistry,” in Quantum Information and Computation for Chemistry (John Wiley & Sons, Inc., 2014) pp. 67–106.   
[16] J. Biamonte, P. Wittek, N. Pancotti, P. Rebentrost, N. Wiebe, and S. Lloyd, Nature 549, 195 (2017), insight.   
[17] E. Farhi, J. Goldstone, S. Gutmann, and M. Sipser, arXiv preprint (2000), arXiv:quant-ph/0001106 [quant-ph].   
[18] S. Jansen, M.-B. Ruskai, and R. Seiler, Journal of Mathematical Physics 48, 102111 (2007).   
[19] S. Oh, Phys. Rev. A 77, 012326 (2008).   
[20] G. Brassard, P. Høyer, M. Mosca, and A. Tapp, in Quantum Computation and Information, AMS Contemporary Mathematics Series, Vol. 305 (AMS, 2002).   
[21] R. Kothari, Private correspondence.   
[22] R. V. Mises and H. Pollaczek-Geiringer, ZAMM - Journal of Applied Mathematics and Mechanics / Zeitschrift f¨ur Angewandte Mathematik und Mechanik 9, 152 (1929).   
[23] J. van Apeldoorn, A. Gily´en, S. Gribling, and R. de Wolf, arXiv preprint (2017), arXiv:1705.01843 [quant-ph].   
[24] T. J. Yoder, G. H. Low, and I. L. Chuang, Phys. Rev. Lett. 113, 210501 (2014).   
[25] V. V. Shende, S. S. Bullock, and I. L. Markov, IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems 25, 1000 (2006).   
[26] M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information: 10th Anniversary Edition, 10th ed. (Cambridge University Press, New York, NY, USA, 2011).

# Appendix A: Finding the ground energy using phase estimation

We now demonstrate how to combine phase estimation and the minimum label finding algorithm to find the unknown ground energy of a quantum Hamiltonian to a precision of $\xi$ in a gate complexity of

$$
\tilde { O } \left( \frac { \Lambda } { \chi ^ { 3 } \xi } + \frac { \Phi } { \chi } \right) .
$$

Notice that straightforward amplitude amplification cannot be used to amplify the ground energy since the latter is not known.

Let $U$ be an $N \times N$ unitary with eigenvectors $| \lambda _ { i } \rangle$ and eigenvalues $e ^ { 2 \pi \lambda _ { i } }$ with $\lambda _ { i } \in [ 0 , 1 )$ . We are interested in finding a good approximation of the minimum value $\lambda _ { 0 }$ , say to $n = \lceil \log _ { 2 } 1 / \xi \rceil$ binary digits of precision.

Let $\begin{array} { r } { | \phi \rangle = \sum _ { i } \phi _ { i } | \lambda _ { i } \rangle } \end{array}$ be an arbitrary trial state. Suppose that we are given a circuit $\mathcal { C } _ { \phi }$ which prepares $| \phi \rangle$ using $\Phi$ elementary gates. Recall that the phase estimation algorithm [9] takes $\left| \phi \right. \left| 0 \right. ^ { \otimes k }$ for some $k > n$ to

$$
\left| \Phi \right. : = \sum _ { i } \phi _ { i } \left| \lambda _ { i } \right. \left| \tilde { \varphi } _ { i } \right.
$$

using controlled U, U 2, . . . U 2k−1 and an inverse quantum Fourier transform on $k$ qubits, where $| \tilde { \varphi } _ { i } \rangle$ can be shown to have a large overlap with the computational basis state that encodes the first $n$ binary digits of $\lambda _ { i }$ .

Let

$$
\left| { \tilde { \varphi } } _ { i } \right. = \sum _ { x = 0 } ^ { 2 ^ { k } - 1 } \gamma _ { i x } \left| x \right.
$$

be its expansion in the computational basis. Then,

$$
\left| \Phi \right. = \sum _ { x = 0 } ^ { 2 ^ { k } - 1 } \left| \Phi _ { x } \right. \left| x \right. ,
$$

where

$$
\left| { \Phi _ { x } } \right. = \sum _ { i } \phi _ { i } \gamma _ { i x } \left| { \lambda _ { i } } \right.
$$

are non-normalised states.

Naively, one would expect that simply measuring the ancillas would give a good approximation $x \approx 2 ^ { k } \lambda _ { 0 }$ of the ground energy with probability $\approx | \phi _ { 0 } | ^ { 2 }$ , so that $O ( 1 / | \phi _ { 0 } | ^ { 2 } )$ repetitions would be needed to find the ground energy. One would also expect that this could be quadratically reduced to $O ( 1 / | \phi _ { 0 } | )$ using suitable amplitude amplification techniques. However, we show below that the overall gate cost is much higher if the ground energy is not known beforehand. Indeed, due to the finite precision and error in the phase estimation algorithm, $\| | \Phi _ { x } \rangle \| ^ { 2 }$ could in principle be large even when $x \ll 2 ^ { k } \lambda _ { 0 }$ . This means that the algorithm could fail by accidentally finding a value that is much smaller than the true ground energy. We show below that in order to guarantee that this does not happen, one needs to choose $2 ^ { k } = \tilde { O } ( 2 ^ { n } / | \phi _ { 0 } | ^ { 2 } )$ . Since the runtime of phase estimation scales linearly with $2 ^ { k }$ , and only a lower bound $\chi$ on $| \phi _ { 0 } |$ is assumed to be known, this would lead to an overall runtime that scales as $\sim 1 / \chi ^ { 3 }$ . We also demonstrate at the end of this section that this dependence is essentially tight.

Proposition 2 (Ground energy estimation with phase estimation). Phase estimation can be used to find the value of $\lambda _ { 0 }$ to an additive precision of $\xi$ in a gate complexity of (A1), and using $O ( \log N + \log 1 / \xi )$ qubits.

Proof. Recall first the well-known [26] relations

$$
\gamma _ { i x } = \frac { 1 } { 2 ^ { k } } \left( \frac { 1 - e ^ { 2 \pi i ( 2 ^ { k } \lambda _ { i } - x ) } } { 1 - e ^ { 2 \pi i ( \lambda _ { i } - x / 2 ^ { k } ) } } \right)
$$

and

$$
| \gamma _ { i x } | \leq \frac { 1 } { 2 | 2 ^ { k } \lambda _ { i } - x | } .
$$

Let $D : = 2 ^ { k - n }$ . Then, using (A7), we have

$$
\begin{array} { r l } { \underset { \alpha < 2 ^ { \ell } \kappa  \kappa } { \sum } \Vert \Phi _ { 2 } \Vert ^ { 2 } = } & { \underset { x \in \mathbb { Z } ^ { k } \setminus \{ 0 , 1 \} } { \sum } \Vert \phi _ { 1 } \Vert ^ { 2 } \vert _ { \gamma \downarrow \lambda } \vert ^ { 2 } } \\ & { \underset { x \in \mathbb { Z } ^ { k } \setminus \{ 0 , 1 \} } { \sum } \Vert \phi _ { 1 } \vert ^ { 2 } \vert _ { 2  \mathcal { E } ^ { \lambda } \lambda _ { i } - x  } \vert ^ { 2 } } \\ & { \underset { x \in \mathbb { Z } ^ { k } \setminus \{ 0 , 1 \} } { \sum } \vert \phi _ { 1 } \vert ^ { 2 } \vert _ { 2  \mathcal { E } ^ { \lambda } \lambda _ { i } - x  } \vert ^ { 2 } } \\ & { \leq \underset { x \in \mathbb { Z } ^ { k } \setminus \{ 0 , 1 \} } { \sum } \vert \phi _ { 1 } \vert ^ { 2 } \vert _ { 2  \mathcal { E } ^ { \lambda } \lambda _ { i } - x  } \vert ^ { 2 } } \\ & { \underset { x \in \mathbb { Z } ^ { k } \setminus \{ 0 , 1 \} } { \sum } \frac { 1 } { \sum } \vert \frac { 1 } { 2  \lambda _ { i } - x  } \vert ^ { 2 } } \\ & { \leq \underset { x \in \mathbb { Z } ^ { k } \setminus \{ 0 , 1 \} } { \sum } \frac { 1 } { \vert \gamma \vert } < \frac { 1 } { j ! } . } \end{array}
$$

Moreover, when $x$ satisfies $| \lambda _ { i } - x / 2 ^ { k } | < 1 / 2 ^ { k + 1 }$ ,

$$
| \gamma _ { i x } | \geq \frac { 2 } { \pi } ,
$$

using that

$$
| \theta | \geq | 1 - e ^ { i \theta } | \geq 2 | \theta | / \pi
$$

for $\theta \in [ - \pi , \pi ]$ . Thus,

$$
\Bigl | \Bigr | \Phi _ { \lfloor 2 ^ { k } \lambda _ { 0 } \rceil } \Bigr > \Bigr | \Bigr | \ge \frac { 2 } { \pi } | { \phi } _ { 0 } | .
$$

Let $\chi$ be a known lower bound on $| \phi _ { 0 } |$ . Using Proposition $^ { 1 }$ , we can thus find an integer $x \in [ \vert 2 ^ { k } \lambda _ { 0 } ] - D , \lfloor 2 ^ { k } \lambda _ { 0 } ] ]$ with good probability, provided that $1 / D = \ddot { O } ( \chi ^ { 2 } )$ . The number of calls to phase estimation is ${ \tilde { O } } ( 1 / \chi )$ . The number of gates required for each run of phase estimation is ${ \tilde { O } } ( 2 ^ { k } \Lambda )$ . Thus, taking $U = e ^ { - 2 \pi i \vec { H } }$ and $\xi = 2 ^ { - n }$ , we arrive at a total gate count of (A1). Moreover, the number of qubits required is $O ( \log N + k ) = O ( \log N + \log 1 / \xi )$ .

It is not difficult to show that for suitable $\tilde { H }$ and $| \phi \rangle$ , the dependence on $\chi$ of this algorithm is optimal. Indeed, suppose that $\begin{array} { r } { \tilde { H } = \frac { 1 } { 2 ^ { k } } ( H ^ { \prime } + c \mathbb { 1 } ) } \end{array}$ , where $c \in ( 0 , 1 / 2 )$ is a constant and $H ^ { \prime }$ is any Hamiltonian with integer spectrum in $\{ 2 ^ { k - 2 } , \ldots , 2 ^ { k - 1 } - 1 \}$ . Then from (A14),

$$
| \gamma _ { i x } | \geq \frac { 2 c } { \pi | 2 ^ { k } \lambda _ { i } - x | } .
$$

Suppose that our trial state $| \phi \rangle$ is such that $| \phi _ { 1 } | ^ { 2 } \geq 1 / 2$ . Then,

$$
\begin{array} { r l } { \underset { x < 2 ^ { k } \lambda _ { 0 } = - D } { \sum } \Vert \left. \Phi _ { x } \right. \Vert ^ { 2 } = } & { \underset { x < 2 ^ { k } \lambda _ { 0 } = - D } { \sum } \left. \phi _ { i } \right. ^ { 2 } \left. \gamma _ { i x } \right. ^ { 2 } } \\ & { \ge \frac { C } { \pi } \underset { x < 2 ^ { k } \lambda _ { 0 } = - D } { \sum } \frac { 1 } { \left. 2 ^ { k } \lambda _ { 1 } - x \right. ^ { 2 } } } \\ & { = \Omega \left( \int _ { D + 2 ^ { k } \Delta } ^ { 2 ^ { k } \lambda _ { 1 } } \frac { 1 } { x ^ { 2 } } \mathrm { d } x \right) } \\ & { = \Omega \left( \frac { 1 } { 2 ^ { k } } \left( \frac { 1 } { \xi + \Delta } - \frac { 1 } { \lambda _ { 1 } } \right) \right) . } \end{array}
$$

Suppose now that $\Delta = O ( \xi )$ and $\xi = o ( 1 )$ . Then

$$
\sum _ { x < 2 ^ { k } \lambda _ { 0 } - D } \left\| \left. \Phi _ { x } \right. \right\| ^ { 2 } = \Omega \left( \frac { 1 } { 2 ^ { k } \xi } \right) ,
$$

which is much larger than $\chi ^ { 2 }$ unless $\begin{array} { r } { 2 ^ { k } = \Omega \left( \frac { 1 } { \chi ^ { 2 } \xi } \right) } \end{array}$ , and the claim follows.

# Appendix B: Preparing the ground states using phase estimation

Naively, one would expect that upon successfully projecting the ancillas of (A2) into the first $n$ (or even $k$ ) digits of $\lambda _ { 0 }$ , the residual state should be a good approximation of $| \lambda _ { 0 } \rangle$ , provided that $\xi = \tilde { O } ( \Delta )$ . Unfortunately, this is not true, because the “imperfections” in $| \tilde { \varphi } _ { i } \rangle$ build up to a non-negligble error in the residual state. This phenomenon was also observed in [10]. Below, we analyse these errors and show a non-negligible bound on the minimum precision to which the ground energy needs to be known beforehand.

Proposition 3 (Ground state preparation with phase estimation for known ground energy). Suppose that the value of $\lambda _ { 0 }$ is known to a precision of $O ( | \phi _ { 0 } | \epsilon \Delta )$ . Then phase estimation can be used to prepare a state $\epsilon$ -close to the ground state in a gate complexity of

$$
O \left( \frac { \Lambda } { | \phi _ { 0 } | ^ { 2 } \Delta \epsilon } + \frac { \Phi } { | \phi _ { 0 } | } \right) ,
$$

and using $O ( \log N + \log 1 / \epsilon + \log 1 / \Delta )$ qubits.

Proof. Suppose that $z : = \lfloor 2 ^ { k } \lambda _ { 0 } \rceil$ , i.e. $z$ encodes the first $k$ binary digits of $\lambda _ { 0 }$ ( $k$ will be specified below) and we apply phase estimation on $k$ qubits. Then, post-selecting the ancillas of (A2) to be in $| z \rangle$ , the residual state is

$$
| \lambda \rangle : = \frac { \sum _ { i } \phi _ { i } \gamma _ { i z } | \lambda _ { i } \rangle } { \| \sum _ { i } \phi _ { i } \gamma _ { i z } | \lambda _ { i } \rangle \| } .
$$

Thus, the error in the residual state is

$$
\| \left| \lambda \right. - \left| \lambda _ { 0 } \right. \| = \Theta \left( \frac { \| \sum _ { i \neq 0 } \phi _ { i } \gamma _ { i z } \left| \lambda _ { i } \right. \| } { \| \sum _ { i } \phi _ { i } \gamma _ { i z } \left| \lambda _ { i } \right. \| } \right) .
$$

For $i \neq 0$ , (A7) implies that

$$
| \gamma _ { i z } | \leq \frac 1 { 2 ^ { k + 1 } \Delta } .
$$

Moreover, (A13) implies $| \gamma _ { 0 z } | \geq 2 / \pi$ . Hence,

$$
\begin{array} { r } { \left( \frac { \| \sum _ { i \neq 0 } \phi _ { i } \gamma _ { i z } | \lambda _ { i } \rangle \| } { \| \sum _ { i } \phi _ { i } \gamma _ { i z } | \lambda _ { i } \rangle \| } \right) ^ { 2 } = \frac { \sum _ { i \neq 0 } | \phi _ { i } | ^ { 2 } | \gamma _ { i z } | ^ { 2 } } { \sum _ { i } | \phi _ { i } | ^ { 2 } | \gamma _ { i z } | ^ { 2 } } } \\ { \leq \left( \frac { 1 } { \pi | \phi _ { 0 } | 2 ^ { k } \Delta } \right) ^ { 2 } . } \end{array}
$$

Thus, it is sufficient if $k$ satisfies

$$
2 ^ { k } = O \left( \frac { 1 } { | \phi _ { 0 } | \epsilon \Delta } \right)
$$

for an error $\parallel \left| \lambda \right. - \left| \lambda _ { 0 } \right. \parallel = { \cal O } ( \epsilon )$ . Notice in particular the scaling with $| \phi _ { 0 } |$

Suppose that the value of $z$ , i.e. the ground energy to a precision of $k$ binary digits, is known, where $k$ is known to satisfy (B7). The cost of a single run of phase estimation is ${ \tilde { O } } \left( 2 ^ { k } \Lambda \right)$ , up to polylogarithmic factors. Fixed point search requires $O ( 1 / | \phi _ { 0 } | )$ applications of phase estimation and $\mathcal { C } _ { \phi }$ . We thus arrive at a total gate count of

$$
\tilde { O } \left( \frac { 2 ^ { k } \Lambda + \Phi } { | \phi _ { 0 } | } \right) = \tilde { O } \left( \frac { \Lambda } { | \phi _ { 0 } | ^ { 2 } \Delta \epsilon } + \frac { \Phi } { | \phi _ { 0 } | } \right)
$$

as claimed.

Suppose next that the ground energy is not known beforehand. If phase estimation and minimum label finding (Appendix A) is first used to find the ground energy, we require a precision of $O ( | \phi _ { 0 } | \epsilon \Delta )$ . Since $| \phi _ { 0 } |$ is not assumed to be known, we need to run phase estimation to find the energy to a precision of $\xi = O ( \chi \epsilon \Delta )$ . Thus, from Proposition 2, the number of gates to first find the ground energy to the required precision takes

$$
\tilde { O } \left( \frac { \Lambda } { \chi ^ { 4 } \Delta \epsilon } + \frac { \Phi } { \chi } \right)
$$

gates.

Corollary 1 (Ground state preparation with phase estimation for unknown ground energy). If the ground energy is not known beforehand, phase estimation can be used to prepare a state $\epsilon$ -close to the ground state in a gate complexity of

$$
\left. \tilde { O } \left( \frac { \Lambda } { \chi ^ { 4 } \Delta \epsilon } + \frac { \Phi } { \chi } \right) , \right.
$$

and using $O ( \log N + \log 1 / \epsilon + \log 1 / \Delta )$ qubits.

We now argue that the dependence of $2 ^ { k }$ on $| \phi _ { 0 } |$ in (B7), and thus the quadratic dependence on $| \phi _ { 0 } |$ in (B1), is essentially tight for this algorithm. Suppose that

$$
\frac { \sum _ { i \neq 0 } | \phi _ { i } | ^ { 2 } | \gamma _ { i z } | ^ { 2 } } { \sum _ { i } | \phi _ { i } | ^ { 2 } | \gamma _ { i z } | ^ { 2 } } \leq \epsilon ^ { 2 } .
$$

Then,

$$
\begin{array} { r l } & { \epsilon ^ { 2 } \geq \frac { \sum _ { i \neq 0 } \left| \phi _ { i } \right| ^ { 2 } \left| \gamma _ { i z } \right| ^ { 2 } } { \sum _ { i } \left| \phi _ { i } \right| ^ { 2 } \left| \gamma _ { i z } \right| ^ { 2 } } } \\ & { = \frac { \sum _ { i \neq 0 } \left| \phi _ { i } \right| ^ { 2 } \left| \gamma _ { i z } \right| ^ { 2 } } { \left| \phi _ { 0 } \right| ^ { 2 } \left| \gamma _ { 0 z } \right| ^ { 2 } + \sum _ { i \neq 0 } \left| \phi _ { i } \right| ^ { 2 } \left| \gamma _ { i z } \right| ^ { 2 } } } \\ & { \geq ( 1 - \epsilon ^ { 2 } ) \frac { \sum _ { i \neq 0 } \left| \phi _ { i } \right| ^ { 2 } \left| \gamma _ { i z } \right| ^ { 2 } } { \left| \phi _ { 0 } \right| ^ { 2 } \left| \gamma _ { 0 z } \right| ^ { 2 } } } \\ & { \geq ( 1 - \epsilon ^ { 2 } ) \frac { 1 } { \left| \phi _ { 0 } \right| ^ { 2 } } \underset { i \neq 0 } { \sum } \left| \phi _ { i } \right| ^ { 2 } \left| \gamma _ { i z } \right| ^ { 2 } . } \end{array}
$$

Suppose that for all $i \neq 0$ ,

$$
r ( 2 ^ { k } \lambda _ { i } - z ) \geq c ,
$$

where $r ( x ) : = | x - \lfloor x \rceil | \in [ 0 , 1 / 2 ]$ , for some constant $c > 0$ . Notice that this can be achieved for any Hamiltonian of the form $\begin{array} { r } { H = \frac { 1 } { 2 ^ { k } } ( \tilde { H } + c \mathbb { 1 } ) } \end{array}$ , where $\tilde { H }$ is any Hamiltonian with integer spectrum. Then, using Eq. (A14),

$$
\left| \gamma _ { i z } \right| = \frac { 1 } { 2 ^ { k } } \left( \frac { 1 - e ^ { 2 \pi i r ( 2 ^ { k } \lambda _ { i } - z ) } } { 1 - e ^ { 2 \pi i ( \lambda _ { i } - z / 2 ^ { k } ) } } \right) \geq \frac { c } { 2 ^ { k - 1 } } .
$$

Thus,

$$
\epsilon ^ { 2 } \ge ( 1 - \epsilon ^ { 2 } ) \frac { c ^ { 2 } ( 1 - | \phi _ { 0 } | ^ { 2 } ) } { 4 ^ { k - 1 } | \phi _ { 0 } | ^ { 2 } } .
$$

Therefore, $\begin{array} { r } { 2 ^ { k } = \Omega \left( \frac { 1 } { | \phi _ { 0 } | \epsilon } \right) } \end{array}$ , and the claim follows.

One can also show that the linear dependence on $1 / \Delta$ is tight: if our trial state is $\begin{array} { r } { | \phi \rangle = \phi _ { 0 } | \lambda _ { 0 } \rangle + \phi _ { 1 } | \lambda _ { 1 } \rangle } \end{array}$ with $\lambda _ { 1 } = \lambda _ { 0 } + \Delta$ , then (B17) can be replaced by

$$
\left| \gamma _ { i z } \right| = \frac { 1 } { 2 ^ { k } } \left( \frac { 1 - e ^ { 2 \pi i r ( 2 ^ { k } \lambda _ { 1 } - z ) } } { 1 - e ^ { 2 \pi i ( \lambda _ { 1 } - z / 2 ^ { k } ) } } \right) \geq \frac { c } { \pi 2 ^ { k - 1 } \Delta } ,
$$

which follows from Eq. (A14). Thus, $\begin{array} { r } { 2 ^ { k } = \Omega \left( \frac { 1 } { | \phi _ { 0 } | \epsilon \Delta } \right) } \end{array}$ , and the claim follows.

# Appendix C: Filtering method by Poulin & Wocjan

Previously, Poulin and Wocjan proposed a filtering method [10] as an improvement to phase estimation that only has an inverse dependence on the overlap $| \phi _ { 0 } |$ . We briefly review this algorithm here, and show that it can be adapted to achieve a runtime that scales only polylogarithmically in the allowed error (the analysis provided in [10] only yields a state with low expected energy, and only an error analysis for the expected energy rather than the residual state is given there). We also show that this method can be combined with the mimimum label finding algorithm in case the ground energy is not known beforehand to first find the ground energy to the required precision.

The Poulin-Wocjan algorithm is based on the following idea: let $\mathcal { A }$ be the circuit of phase estimation with $k$ ancilla qubits, but without the inverse Fourier transform. Then $\mathcal { A } \left| \lambda _ { i } \right. \left| 0 \right. ^ { \otimes k } = \left| \lambda _ { i } \right. \left| \varphi _ { i } \right.$ , where

$$
\left| \varphi _ { i } \right. : = { \frac { 1 } { \sqrt { 2 ^ { k } } } } \sum _ { x = 0 } ^ { 2 ^ { k } - 1 } e ^ { 2 \pi i \lambda _ { i } x } \left| x \right.
$$

is a momentum state encoding of $\lambda _ { i }$ . Since $\mathcal { A }$ maps $| \lambda _ { i } \rangle | 0 \rangle ^ { \otimes k }$ to $| \lambda _ { i } \rangle | \varphi _ { i } \rangle$ , then for any state $| \mu \rangle$ on $k$ qubits, $\mathcal { A } ^ { \dagger }$ maps $\mathinner { | { \phi } \rangle } \mathinner { | { \mu } \rangle }$ to

$$
\sum _ { i } \phi _ { i } \left. \varphi _ { i } \right| \mu \rangle \left| \lambda _ { i } \right. \left| 0 \right. ^ { \otimes k } + \left| R \right.
$$

where $| R \rangle$ has no overlap with $\left| 0 \right. ^ { \otimes k }$ on the ancillas. Hence, starting with $\eta$ copies of $| \mu \rangle$ on $\eta k$ ancillas ( $\eta$ will be specified later), applying $\eta$ copies of $\mathcal { A } ^ { \dagger }$ maps $\left| \phi \right. \left| \mu \right. ^ { \otimes \eta }$ to

$$
\sum _ { i } \phi _ { i }  \varphi _ { i } | \mu  ^ { \eta } | \lambda _ { i }  | 0  ^ { \otimes \eta k } + | R ^ { \prime }  ,
$$

where $| R ^ { \prime } \rangle$ has no overlap with $| 0 \rangle ^ { \otimes \eta k }$ on the ancillas. The central idea of [10] is that for suitable choices of $\eta$ and $| \mu \rangle$ , $\mid \left. \varphi _ { i } \mid \mu \right. \mid ^ { \eta }$ is a “filter function” that is centered around $\lambda _ { 0 }$ and falls off quickly, thus suppressing all terms in (C3) except for the contribution from $| \lambda _ { 0 } \rangle$ . We now show that this idea can be used to obtain a ground state preparation algorithm whose runtime also only scales polylogarithmically with $\epsilon$ .

Proposition 4 (Ground state preparation with filtering method for known ground energy). Suppose that the value of $\lambda _ { 0 }$ is known to a precision of

$$
O \left( \frac { \Delta } { \sqrt { \log ^ { 3 } \frac { 1 } { | \phi _ { 0 } | \epsilon } \log \log \frac { 1 } { | \phi _ { 0 } | \epsilon } } } \right) .
$$

Then the Filtering method can prepare a state $\epsilon$ -close to $| \lambda _ { 0 } \rangle$ in a gate complexity of

$$
\tilde { O } \left( \frac { \Lambda } { | \phi _ { 0 } | \Delta } + \frac { \Phi } { | \phi _ { 0 } | } \right)
$$

and using

$$
O \left( \log N + \log \frac { 1 } { \epsilon } + \frac { \log \frac { 1 } { \chi \epsilon } } { \log \log \frac { 1 } { \chi \epsilon } } \times \log \frac { 1 } { \Delta } \right)
$$

qubits.

Proof. Suppose that we know a value of $\mu \in [ 0 , 1 )$ such that

$$
\vert \mu - \lambda _ { 0 } \vert < \frac { 1 } { 2 ^ { k + 1 } \pi \sqrt { \eta } } ,
$$

where $k$ and $\eta$ will be specified later. Note that this is the same as assuming that we know √ $\lambda _ { 0 }$ up to $k + l$ binary digits, where $l : = \lceil \log _ { 2 } ( 2 \pi \sqrt { \eta } ) \rceil$ , and we can w.l.o.g. assume that $2 ^ { k + l } \mu \in \mathbb { Z }$ . Choose

$$
\left| \mu \right. : = \frac { 1 } { \sqrt { 2 ^ { k } } } \sum _ { x = 0 } ^ { 2 ^ { k } - 1 } e ^ { 2 \pi i \mu x } \left| x \right. .
$$

Note that $| \mu \rangle$ can be efficiently prepared from the computational basis state $| 2 ^ { k + l } \mu \rangle$ by first applying the quantum Fourier transform on $k + l$ qubits, then applying Hadamard gates on the last $l$ qubits, and finally discarding the last $\it l$ qubits. The circuit $\mathcal { C } _ { \mu }$ preparing $| \mu \rangle$ from $\left| 0 \right. ^ { \otimes ( k + l ) }$ thus only requires $O ( ( k + l ) ^ { 2 } )$ gates [26]. Similarly to (A7) and (B4), for $i \neq 0$ ,

$$
\left| \langle \varphi _ { i } | \ \mu \rangle \right| \leq { \frac { 1 } { 2 ^ { k + 1 } | \lambda _ { i } - \mu | } } \leq { \frac { 1 } { 2 ^ { k + 1 } \Delta } } .
$$

Moreover, it can be shown [10] that (C7) implies

$$
| \langle \varphi _ { 0 } | \mu \rangle | ^ { \eta } \geq { \frac { 1 } { 2 } } .
$$

Thus, using amplitude amplification or fixed point search to search for $\left| 0 \right. ^ { \otimes \eta k }$ on (C3), we obtain with high probability the state

$$
| \sigma  : = \frac { \sum _ { i } \phi _ { i }  \varphi _ { i }  \mu  ^ { \eta }  \lambda _ { i }  } {  \sum _ { i } \phi _ { i }  \varphi _ { i }  \mu  ^ { \eta }  \lambda _ { i }   }
$$

with $O ( \eta / | \phi _ { 0 } | )$ uses of $\mathcal { A } ^ { \dagger }$ and $\mathcal { C } _ { \mu }$ , and $O ( 1 / | \phi _ { 0 } | )$ uses of $\mathcal { C } _ { \phi }$

We now show that $| \sigma \rangle$ is a good approximation of $| \lambda _ { 0 } \rangle$ for appropriate choices of $k$ and $\eta$ . We have that

$$
\begin{array} { r l } & { \frac { 1 } { 2 } \| | \sigma  - | \lambda _ { 0 }  \| ^ { 2 } \leq \frac { \big \| \sum _ { i \neq 0 } \phi _ { i }  \varphi _ { i }  \mu  ^ { \eta } \big \vert \lambda _ { i } \big \rangle \big \| ^ { 2 } } { \big \| \sum _ { i } \phi _ { i }  \varphi _ { i }  \mu  ^ { \eta } \big \vert \lambda _ { i } \big \rangle \big \| ^ { 2 } } } \\ & { \qquad = \frac { \sum _ { i \neq 0 }  \phi _ { i }  ^ { 2 }   \varphi _ { i }  \mu   ^ { 2 \eta } } { \sum _ { i }  \phi _ { i }  ^ { 2 }   \varphi _ { i }  \mu   ^ { 2 \eta } } } \\ & { \qquad \leq 4 ( \frac { 1 } { 2 ^ { k + 1 } \Delta } ) ^ { 2 \eta } \frac { 1 } {  \phi _ { 0 }  ^ { 2 } } . } \end{array}
$$

Thus, in order to obtain

$$
\| \left| \sigma \right. - \left| \lambda _ { 0 } \right. \| < \epsilon ,
$$

it suffices if $k$ and $\eta$ satisfy

$$
k = \left\lceil \log _ { 2 } \frac { 1 } { \Delta } \right\rceil + O \left( \log \log \frac { 1 } { | \phi _ { 0 } | \epsilon } \right)
$$

and

$$
\eta = O \left( \frac { \log \frac { 1 } { | \phi _ { 0 } | \epsilon } } { \log \log \frac { 1 } { | \phi _ { 0 } | \epsilon } } \right) .
$$

But since $\eta$ is a parameter of the algorithm that needs to be chosen beforehand, and $| \phi _ { 0 } |$ is unknown, we need to choose

$$
\eta = O \left( \frac { \log \frac { 1 } { \chi \epsilon } } { \log \log \frac { 1 } { \chi \epsilon } } \right)
$$

to ensure the algorithm works. The full algorithm thus requires

$$
\tilde { O } \left( \frac { \eta 2 ^ { k } \Lambda + \Phi } { | \phi _ { 0 } | } \right) = \tilde { O } \left( \frac { \Lambda } { | \phi _ { 0 } | \Delta } + \frac { \Phi } { | \phi _ { 0 } | } \right)
$$

gates and

$$
O ( \log N ) + \eta k = O \left( \log N + \log { \frac { 1 } { \epsilon } } + { \frac { \log { \frac { 1 } { \chi \epsilon } } } { \log \log { \frac { 1 } { \chi \epsilon } } } } \times \log { \frac { 1 } { \Delta } } \right)
$$

qubits.

There does not appear to be an obvious way, such as a recycling scheme, to reduce the number of qubits required. Suppose now that the value of $\mu$ is not known beforehand. We show now that in this case, one can combine the filtering method with the minimum label finding algorithm to determine a suitable value of $\mu$ beforehand.

Proposition 5 (Ground state preparation with filtering method for unknown ground energy). If the ground energy is not known beforehand, the same task as in Proposition $\cdot$ can be achieved in a gate complexity of

$$
\tilde { O } \left( \frac { \Lambda } { \chi \Delta ^ { 3 / 2 } } + \frac { \Phi } { \chi \sqrt { \Delta } } \right)
$$

and the same number (C6) of qubits.

Proof. Let $k$ and $\eta$ be defined as in the proof of Proposition 4. Let $\mu _ { j } = j / 2 ^ { k _ { 1 } }$ , where $k _ { 1 } \geq k$ will be chosen later. It is easy to prepare the state

$$
\frac { 1 } { \sqrt { 2 ^ { k _ { 1 } } } } \sum _ { j = 0 } ^ { 2 ^ { k _ { 1 } } - 1 } \left| j \right. \left| \mu _ { j } \right. ^ { \otimes \eta _ { 1 } } \left| \phi \right. ,
$$

where

$$
\left| \mu _ { j } \right. = { \frac { 1 } { \sqrt { 2 ^ { k _ { 1 } } } } } \sum _ { x = 0 } ^ { 2 ^ { k } - 1 } e ^ { 2 \pi i \mu _ { j } x } \left| x \right. .
$$

We now run a controlled version of the filtering algorithm with $\eta _ { 1 } \times k _ { 1 }$ ancilla qubits. This produces the state

$$
\sum _ { j = 0 } ^ { 2 ^ { k _ { 1 } } - 1 } \left| j \right. \left| \Phi _ { j } \right. ,
$$

where

$$
| \Phi _ { j }  = \frac { 1 } { \sqrt { 2 ^ { k _ { 1 } } } } \sum _ { i } \phi _ { i }  \varphi _ { i } | \mu _ { j }  ^ { \eta _ { 1 } } | \lambda _ { i }  .
$$

Let J be the smallest integer such that |µJ − λ0| < 12k+2π√η . Then from (C10), k |ΦJ i k ≥ |φ0|2√2k1 ≥ χ2√2k1 . Let J < J ˜ be an integer such that

$$
\sum _ { j = 0 } ^ { \tilde { J } } \| | \Phi _ { j } \rangle \| ^ { 2 } = O \left( \frac { \chi ^ { 2 } } { 2 ^ { k _ { 1 } } } \right) .
$$

Then, the minimum label finding algorithm finds an integer $j \in [ \bar { J } , J ]$ with high probability. To obtain a value of $j$ that gives rise to a good approximation of $\lambda _ { 0 }$ , we need to ensure that $\begin{array} { r } { \mu _ { J } - \mu _ { \tilde { J } } < \frac { 1 } { 2 ^ { k + 2 } \pi \sqrt { \eta } } } \end{array}$ , since the latter then implies $\begin{array} { r } { | \mu _ { j } - \lambda _ { 0 } | < \frac { 1 } { 2 ^ { k + 1 } \pi \sqrt { \eta } } } \end{array}$ for all $j \in [ \bar { J } , J ]$ .

Let $D = J - \tilde { J }$ . We have

$$
\begin{array} { l } { \displaystyle \sum _ { j = 0 } ^ { J } \| \boldsymbol { * } _ { \beta } ) \| ^ { 2 } = \frac { 1 } { 2 ^ { j k } } \displaystyle \sum _ { j = 0 } ^ { J } \sum _ { i } | \phi _ { i } | ^ { 2 } | \langle \phi _ { i } | \mu _ { j } \rangle \Big | ^ { 2 p _ { i } } } \\ { \displaystyle \leq \frac { 1 } { 2 ^ { j k } } \displaystyle \sum _ { j = 0 } ^ { J } \sum _ { i } | \phi _ { i } | ^ { 2 } \displaystyle \frac { 1 } { ( 2 ^ { j k + 1 } | \lambda _ { i } - \mu _ { j } | ) ^ { 2 n _ { i } } } } \\ { \displaystyle < \frac { 1 } { 2 ^ { j k } } \displaystyle \sum _ { j = 0 } ^ { J } \frac { 1 } { ( 2 ^ { j k + 1 } | \lambda _ { 0 } - \mu _ { j } | ) ^ { 2 n _ { i } } } } \\ { \displaystyle < \frac { 1 } { 2 ^ { j k } } \displaystyle \sum _ { j = 0 } ^ { J } \frac { 1 } { j ^ { 2 n _ { i } } } } \\ { \displaystyle < \frac { 1 } { 2 ^ { j k } } \displaystyle \sum _ { j = 0 } ^ { J } \frac { 1 } { j ^ { 2 n _ { i } } } . } \end{array}
$$

We thus require

$$
\frac { 1 } { D ^ { 2 \eta _ { 1 } - 1 } } < \chi ^ { 2 } ,
$$

with $D = O ( 2 ^ { k _ { 1 } } \xi _ { F } )$ , where $\xi _ { F } = 1 / ( 2 ^ { k + 1 } \pi \sqrt { \eta } )$ is the required precision (C7). Thus, it suffices to choose

$$
2 ^ { k _ { 1 } } = O \left( \frac { 1 } { \xi _ { F } } \log \frac { 1 } { \chi } \right) = O \left( \frac { 1 } { \Delta } \log ^ { 3 / 2 } \frac { 1 } { \chi \epsilon } \sqrt { \log \log \frac { 1 } { \chi \epsilon } } \log \frac { 1 } { \chi } \right)
$$

and

$$
\eta _ { 1 } = O \left( \frac { \log \frac { 1 } { \chi } } { \log \log \frac { 1 } { \chi } } \right) .
$$

This will provide an estimate of $\lambda _ { 0 }$ that can be used for the state preparation. The number of gates for this estimation is

$$
\tilde { O } \left( \frac { \sqrt { 2 ^ { k _ { 1 } } } } { \chi } \left( 2 ^ { k _ { 1 } } \Lambda + \Phi \right) \right) = \tilde { O } \left( \frac { \Lambda } { \chi \Delta ^ { 3 / 2 } } + \frac { \Phi } { \chi \Delta ^ { 1 / 2 } } \right) ,
$$

as claimed.

Note that in analogy to Section IV B, the algorithm can be used to estimate the ground energy to an arbitrary precision $\xi = \ddot { O } ( \Delta )$ , by simply running the algorithm with a smaller value of $\Delta$ .

Corollary 2 (Ground energy estimation with filtering method). Let $\xi = \tilde { O } ( \Delta )$ . Then the Filterning method can be used to estimate $\lambda _ { 0 }$ to an additive precision of $\xi$ in a gate complexity of

$$
\tilde { O } \left( \frac { \Lambda } { \chi \xi ^ { 3 / 2 } } + \frac { \Phi } { \chi \sqrt { \xi } } \right) ,
$$

and using

$$
O \left( \log N + { \frac { \log { \frac { 1 } { \chi } } } { \log \log { \frac { 1 } { \chi } } } } \times \log { \frac { 1 } { \xi } } \right)
$$

qubits.

Alternatively, one can also use a combined approach by using a prior run of phase estimation to first get a “crude” estimate of $\lambda _ { 0 }$ , similarly to the method in Section IV of the main text. This approach is useful if $\Delta$ is very small.

Proposition 6 (Combining filtering method with phase estimation). By combining the Filtering method with phase estimation,

(i) The same task as in Proposition 5 can be achieved in a gate complexity of

$$
\tilde { \cal O } \left( \frac { \Lambda } { \chi ^ { 3 } \Delta ^ { \kappa } } + \frac { \Lambda } { \chi \Delta ^ { ( 3 - \kappa ) / 2 } } + \frac { \Phi } { \chi \Delta ^ { ( 1 - \kappa ) / 2 } } \right)
$$

and the same number (C6) of qubits,

(ii) The same task as in Corollary 2 can be achieved in a gate complexity of

$$
\tilde { O } \left( \frac { \Lambda } { \chi ^ { 3 } \xi ^ { \kappa } } + \frac { \Lambda } { \chi \xi ^ { ( 3 - \kappa ) / 2 } } + \frac { \Phi } { \chi \Delta ^ { ( 1 - \kappa ) / 2 } } \right)
$$

and the same number (C37) of qubits, where $\kappa \in [ 0 , 1 ]$ is arbitrary.

Proof. To prove (i), first use the method from Appendix A to obtain the ground energy to a precision of $\xi ^ { \prime } = \Delta ^ { \kappa }$ for some $\kappa \in [ 0 , 1 ]$ chosen below. This provides us with an interval $[ a , b ] \ni \lambda _ { 0 }$ with $b - a = O ( \Delta ^ { \kappa } )$ . Let $\mu _ { j } ^ { \prime } = a + ( b - a ) j / L$ with $L = \Theta ( \Delta ^ { \kappa } / \xi )$ . Note that $\mu _ { j + 1 } ^ { \prime } - \mu _ { j } ^ { \prime } < \xi$ . We now run the algorithm from Proposition 5, but replacing (C22) with

$$
\frac { 1 } { \sqrt { L } } \sum _ { j = 0 } ^ { L } \left| j \right. \left| \mu _ { j } ^ { \prime } \right. ^ { \otimes \eta } \left| \phi \right. .
$$

Then, the total number of gates is

$$
\tilde { \cal O } \left( \frac { \Lambda } { \chi ^ { 3 } \xi ^ { \prime } } + \frac { \sqrt { L } } { \chi } ( 2 ^ { k _ { 1 } } \Lambda + \Phi ) \right) = \tilde { \cal O } \left( \frac { \Lambda } { \chi ^ { 3 } \Delta ^ { \star } } + \frac { \Lambda } { \chi \Delta ^ { ( 3 - \kappa ) / 2 } } + \frac { \Phi } { \chi \Delta ^ { ( 1 - \kappa ) / 2 } } \right) .
$$

This proves part (i). Part (ii) follows from the same argument as Corollary 2.

Note that choosing $\kappa = 1$ gives the optimal inverse scaling in $\Delta$ and $\xi$ , respectively, for this algorithm. Similarly as in Section IV however, other values of $\kappa$ can be chosen to take the other parameters into account.

# Appendix D: Chebyshev method

We now show that the alternative approach of [1] of using quantum walks and Chebyshev polynomials can be used to obtain an algorithm with essentially the same runtime. We assume in this section that $\tilde { H }$ has at most $d = O ( \log N )$ non-zero entries in each row/column5. We also assume that the spectrum of $\tilde { H }$ is contained in $[ 0 , 1 / 2 ]$ for simplicity6. Moreover, as in previous work [1, 5, 7], we assume that we are given quantum oracle access to the positions and values of the non-zero elements of $\tilde { H }$ . Specifically, we assume that we are given unitaries $( \ j _ { 1 } , \mathcal { O } _ { 2 }$ such that $\mathcal { O } _ { 1 } \left| j , l \right. = \left| j , \nu ( j , l ) \right.$ and $\mathcal { O } _ { 2 } \left| j , k , z \right. = \left| j , k , z \oplus \tilde { H } _ { j k } \right.$ , where $\nu ( j , l )$ is the column index of the $l ^ { \mathrm { t h } }$ nonzero entry in the $j ^ { \mathrm { t h } }$ row of $\ddot { H }$ , and the third register on which $\mathcal { O } _ { 2 }$ acts encodes a bit string representation of an entry of $\tilde { H }$ . In this section, let $\Lambda$ denote the gate complexity of the oracles.

Suppose that the value of $\lambda _ { 0 }$ is known to a precision of $\begin{array} { r } { \delta = { O } \left( \Delta / \log \frac { 1 } { \chi \epsilon } \right) } \end{array}$ . Let $E$ be a known real number such that $0 \le E \le \lambda _ { 0 }$ and $\delta _ { E } : = \lambda _ { 0 } - E < \delta$ . Define $H : = \tilde { H } - ( E - \tau ) \mathbb { 1 }$ . Then $| \lambda _ { 0 } \rangle$ is the unique eigenvector of $H$ with minimum eigenvalue $\tau + \delta _ { E }$ and by assumption, all other eigenvalues of $H$ are $\ge \tau + \delta _ { E } + \Delta$ . This method is based on the observation that a high power of $\mathbb { 1 } - ( H / d ) ^ { 2 }$ is approximately proportional to a projector onto $| \lambda _ { 0 } \rangle$ . More precisely, for any trial state $| \phi \rangle = \phi _ { 0 } \left| \lambda _ { 0 } \right. + \left| \lambda _ { 0 } ^ { \perp } \right.$ ,

$$
\left( 1 - \left( \frac { H } { d } \right) ^ { 2 } \right) ^ { M } | \phi \rangle = \phi _ { 0 } \left( 1 - \left( \frac { \tau + \delta _ { E } } { d } \right) ^ { 2 } \right) ^ { M } \left( | \lambda _ { 0 } \rangle + \frac { 1 } { \phi _ { 0 } } \left( \frac { 1 - ( H / d ) ^ { 2 } } { 1 - ( ( \tau + \delta _ { E } ) / d ) ^ { 2 } } \right) ^ { M } | \lambda _ { 0 } ^ { \bot } \rangle \right) .
$$

The norm of the second term in the brackets is bounded by $| \phi _ { 0 } | ^ { - 1 } e ^ { - \Omega ( M ( \tau + \delta _ { E } ) \Delta ) }$ . Indeed, for small $\Delta$ ,

$$
\begin{array} { r } { \| ( \mathbb { 1 } - ( \displaystyle \frac { H } { d } ) ^ { 2 } ) ^ { M } | \lambda _ { 0 } ^ { \perp }  \| < ( \frac { 1 - ( \frac { \Delta + \tau + \delta _ { E } } { d } ) ^ { 2 } } { 1 - ( \frac { \tau + \delta _ { E } } { d } ) ^ { 2 } } ) ^ { M } } \\ { = ( 1 - \frac { 2 \Delta ( \tau + \delta _ { E } ) + \Delta ^ { 2 } } { d ^ { 2 } ( 1 - ( \frac { \tau + \delta _ { E } } { d } ) ^ { 2 } ) } ) ^ { M } } \\ { = e ^ { - \Omega ( M ( \tau + \delta _ { E } ) \Delta / d ^ { 2 } ) } } \end{array}
$$

Thus,

$$
\left\| \frac { \left( \mathbb { 1 } - \left( H / d \right) ^ { 2 } \right) ^ { M } | \phi \rangle } { \left\| \left( \mathbb { 1 } - \left( H / d \right) ^ { 2 } \right) ^ { M } | \phi \rangle \right\| } - | \lambda _ { 0 } \rangle \right\| = O ( \epsilon ) ,
$$

provided that

$$
M = \Omega \left( \frac { d ^ { 2 } } { \Delta ( \tau + \delta _ { E } ) } \log \frac { 1 } { | \phi _ { 0 } | \epsilon } \right) .
$$

On the other hand,

$$
\left( 1 - \left( \frac { \tau + \delta _ { E } } { d } \right) ^ { 2 } \right) ^ { M } = e ^ { - O ( ( \tau + \delta _ { E } ) ^ { 2 } M / d ^ { 2 } ) } .
$$

Thus,

$$
\left\| \left( \mathbb { 1 } - \left( \frac { H } { d } \right) ^ { 2 } \right) ^ { M } | \phi \rangle \right\| = \Omega ( | \phi _ { 0 } | ) ,
$$

provided that $\tau + \delta _ { E } = { \cal O } ( d / \sqrt { M } )$ . Hence, since by assumption $\delta _ { E } < \delta$ , choosing

$$
\tau = \Theta \left( { \frac { \Delta } { \log { \frac { 1 } { \chi \varepsilon } } } } \right)
$$

and

$$
M = \Theta \left( \frac { d ^ { 2 } } { \Delta ^ { 2 } } \log ^ { 2 } \frac { 1 } { \chi \epsilon } \right)
$$

satisfies both (D5) and (D8).

Our aim in the following is to prepare $( \mathbb { 1 } - ( H / d ) ^ { 2 } ) ^ { M } | \phi \rangle$ . The strategy we employ is as follows. First, we approximate $( \mathbb { 1 } - ( H / d ) ^ { 2 } ) ^ { M }$ as a linear combination of low order Chebyshev polynomials in $H / d$ . Second, we implement this linear combination with some amplitude using quantum walks and the non-unitary LCU Lemma [1, Lemma 7]. Third, we use amplitude amplification or fixed point search to boost the overlap with the target state.

In the following, assume for simplicity that $M = 2 m$ is even (the algorithm can also be adapted to odd $M$ with minor modifications). Let $\mathcal { T } _ { k } ( x )$ and $\mathcal { U } _ { k } ( x )$ be the $k ^ { \mathrm { t h } }$ Chebyshev polynomials of the first and second kind, respectively. It is well-known that

$$
( 1 - x ^ { 2 } ) ^ { M } = \sum _ { k = 0 } ^ { M } \alpha _ { k } \mathcal { T } _ { 2 k } ( x ) ,
$$

where

$$
\alpha _ { k } = \left\{ \begin{array} { l l } { 2 ^ { 1 - 2 M } \binom { 2 M } { M } - \frac { ( 2 M - 1 ) ! ! } { 2 ^ { M } M ! } , } & { k = 0 } \\ { ( - 1 ) ^ { k } 2 ^ { 1 - 2 M } \binom { 2 M } { M + k } , } & { k \geq 1 . } \end{array} \right.
$$

Since $\| H \| \leq 1$ and $| \mathcal T _ { k } ( x ) | \le 1$ for $| x | \le 1$ , (19) implies that

$$
\left( \mathbb { 1 } - \left( \frac { H } { d } \right) ^ { 2 } \right) ^ { 2 m } = \sum _ { k = 0 } ^ { m _ { 0 } } \alpha _ { k } \mathcal { T } _ { 2 k } \left( \frac { H } { d } \right) + O ( \chi \epsilon ) ,
$$

provided that

$$
m _ { 0 } = \Theta \left( \sqrt { M \log \frac { 1 } { \chi \epsilon } } \right) = \Theta \left( \frac { d } { \Delta } \log ^ { 3 / 2 } \frac { 1 } { \chi \epsilon } \right) .
$$

Next, recall that $\mathcal { T } _ { k } ( H / d )$ can be implemented with some amplitude using quantum walks (c.f. [1, Section 4.1]) on a larger Hilbert space, which is obtained by first adding an ancilla qubit and then doubling the entire system: For $j \in [ N ] : = \{ 1 , \dots , N \}$ , define $\left| \psi _ { j } \right. \in \mathbb { C } ^ { 2 N } \otimes \mathbb { C } ^ { 2 N }$ as

$$
| \psi _ { j } \rangle : = | j 0 \rangle \otimes \frac { 1 } { \sqrt { d } } \sum _ { \stackrel { l \in [ N ] } { H _ { j l } \neq 0 } } | l \rangle \left( \sqrt { H _ { j l } ^ { * } } | 0 \rangle + \sqrt { 1 - | H _ { j l } | } | 1 \rangle \right)
$$

and

$$
T : = \sum _ { j \in \left[ N \right] } \left| \psi _ { j } \rangle \langle j \right| .
$$

Note that the entries of $H$ have modulus at most 1. Let $S$ be the swap operator on $\mathbb { C } ^ { 2 N } \otimes \mathbb { C } ^ { 2 N }$ , i.e. $S \left| j b _ { 1 } \right. \left| l b _ { 2 } \right. =$ $\left| l b _ { 2 } \right. \left| j b _ { 1 } \right.$ , and $W = S ( 2 T T ^ { \dagger } - \mathbb { 1 } )$ . By [1, Lemma 16], within the invariant subspace span $\left\{ T \left| j \right. , S T \left| j \right. : j \in \left[ N \right] \right\}$ , $W ^ { k }$ has the form

$$
W ^ { k } = \left( \begin{array} { c c } { { \mathcal T _ { k } ( H / d ) } } & { { - \sqrt { 1 - ( H / d ) ^ { 2 } } \mathcal U _ { k - 1 } ( H / d ) } } \\ { { \sqrt { 1 - ( H / d ) ^ { 2 } } \mathcal U _ { k - 1 } ( H / d ) } } & { { \mathcal T _ { k } ( H / d ) } } \end{array} \right) ,
$$

where the first block corresponds to the space $\operatorname { s p a n } \{ T | j \rangle : j \in [ N ] \}$ . Hence, using $k$ steps of the walk, we can implement the transformation

$$
\begin{array} { r } { W _ { k } \left| 0 \right. ^ { \otimes q } \left| \phi \right. = \left| 0 \right. ^ { \otimes q } \mathcal { T } _ { k } ( H / d ) \left| \phi \right. + \left| R _ { k } ^ { \prime } \right. , } \end{array}
$$

where $q : = \lceil \log _ { 2 } N \rceil + 3$ and $\left( | 0 \rangle \langle 0 | ^ { \otimes q } \otimes \mathbb { 1 } \right) | R _ { k } ^ { \prime } \rangle = 0$ .

To implement the RHS of (D13), we employ the non-unitary LCU Lemma: Let $B$ be a circuit on $b = \lceil \log _ { 2 } ( m _ { 0 } + 1 ) \rceil$ qubits that maps $\left| 0 \right. ^ { \otimes b }$ to

$$
B \left| 0 \right. ^ { \otimes b } : = \frac { 1 } { \sqrt { \alpha } } \sum _ { k = 0 } ^ { m _ { 0 } } \sqrt { \alpha _ { k } } \left| k \right. ,
$$

where $\begin{array} { r } { \alpha = \sum _ { k = 0 } ^ { m _ { 0 } } \alpha _ { k } } \end{array}$ . Let $\begin{array} { r } { U = \sum _ { k = 0 } ^ { m _ { 0 } } | k \rangle \langle k | \otimes W _ { 2 k } } \end{array}$ be the controlled quantum walk. Then,

$$
\begin{array} { c } { { ( B ^ { \dagger } \otimes 1 ) U ( B \otimes 1 ) \left| 0 \right. ^ { \otimes ( b + q ) } \left| \phi \right. = \displaystyle \frac { 1 } { \alpha } \left| 0 \right. ^ { \otimes b } \displaystyle \sum _ { k = 0 } ^ { m _ { 0 } } \alpha _ { k } ( \left| 0 \right. ^ { \otimes q } \mathcal { T } _ { 2 k } ( H / d ) \left| \phi \right. + \left| R _ { 2 k } ^ { \prime } \right. ) + \left| R ^ { \prime } \right. } } \\ { { = \displaystyle \frac { 1 } { \alpha } \left| 0 \right. ^ { \otimes ( b + q ) } \displaystyle \sum _ { k = 0 } ^ { m _ { 0 } } \alpha _ { k } \mathcal { T } _ { 2 k } ( H / d ) \left| \phi \right. + \left| R \right. , } } \end{array}
$$

where $\left( \left| 0 \right. \left. 0 \right| ^ { \otimes b } \otimes \mathbb { 1 } \right) \left| R ^ { \prime } \right. = 0$ and $( | 0   0 | ^ { \otimes ( b + q ) } \otimes \mathbb { 1 } ) | R  = 0$

The final step of the algorithm is to boost the overlap with amplitude amplification or fixed point search. Note that amplitude amplification can be used without prior knowledge of the overlap [20]. Alternatively, fixed point search [24] can be used for this step. Measuring the ancillas will then project the state onto

$$
| \lambda _ { 0 } ^ { \prime } \rangle : = \frac { \sum _ { k = 0 } ^ { m _ { 0 } } \alpha _ { k } \mathcal { T } _ { 2 k } ( H / d ) | \phi \rangle } { \big \| \sum _ { k = 0 } ^ { m _ { 0 } } \alpha _ { k } \mathcal { T } _ { 2 k } ( H / d ) | \phi \rangle \big \| } ,
$$

provided we successfully obtain $\left| 0 \right. ^ { \otimes ( b + q ) }$ on the ancillas. From (D13),

$$
| \lambda _ { 0 } ^ { \prime } \rangle = \frac { ( \mathbb { 1 } - ( H / d ) ^ { 2 } ) ^ { 2 m } | \phi \rangle } { \| ( \mathbb { 1 } - ( H / d ) ^ { 2 } ) ^ { 2 m } | \phi \rangle \| } + O ( \epsilon )
$$

thus, (D5) implies

$$
\vert \lambda _ { 0 } ^ { \prime } \rangle = \vert \lambda _ { 0 } \rangle + O ( \epsilon ) ,
$$

as required. The probability of success is close to 1, provided that the number of repetitions is

$$
O \left( \frac { \alpha } { \parallel \sum _ { k = 0 } ^ { m _ { 0 } } \alpha _ { k } \mathcal { T } _ { 2 k } ( H / d ) \mid \phi \rangle \parallel } \right) = O ( \alpha / | \phi _ { 0 } | ) ,
$$

where the last equation follows from (D8).

We now calculate the gate count of the entire algorithm. First note that $B$ can be implemented with $O ( 2 ^ { b } ) = O ( m _ { 0 } )$ elementary gates [25]. Next, note that the oracle to $H$ can be obtained from the oracle to $\tilde { H }$ with ${ \cal O } ( \log M )$ additional gates and qubits. The gate cost to implement $W$ to accuracy $\epsilon ^ { \prime }$ is $O ( \Lambda + \log M + \log N + \log ^ { 5 / 2 } ( 1 / \epsilon ^ { \prime } ) )$ [5]. Here, we require $\epsilon ^ { \prime } = O ( \epsilon \vert \phi _ { 0 } \vert / m _ { 0 } d )$ . Thus, the gate cost of $U$ is $O ( m _ { 0 } ( \Lambda + \log M + \log N + \log ^ { 5 / 2 } ( m _ { 0 } d / \epsilon | \phi _ { 0 } | ) )$ [1, Lemma 8]. Note that $\alpha = O ( 1 )$ , and each iteration of amplitude amplification or fixed point search requires $O ( 1 )$ uses of $\mathcal { C } _ { \phi }$ , $B$ and $U$ . The final gate complexity is thus

$$
\cal O \left( \frac { 1 } { | \phi _ { 0 } | } \left( m _ { 0 } \left( \Lambda + \log M + \log N + \log ^ { 5 / 2 } \frac { m _ { 0 } d } { \epsilon | \phi _ { 0 } | } \right) + \Phi \right) \right) = \cal O \left( \frac { \Lambda } { | \phi _ { 0 } | \Delta } \mathrm { p o l y l o g } \left( N , \frac { 1 } { \Delta } , \frac { 1 } { | \phi _ { 0 } | \epsilon / \phi _ { 0 } | } \right) \right)
$$

The total number of qubits required is $O ( \log N + \log M + \log m _ { 0 }$ ).

It is moreover easy to see that, analogously to Section IV B, this approach can also be used for ground state preparation in the case of unknown ground energy, and for estimating the ground energy.