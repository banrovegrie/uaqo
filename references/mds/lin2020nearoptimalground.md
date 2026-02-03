# Near-optimal ground state preparation

Lin Lin1,2 and Yu Tong1

1Department of Mathematics, University of California, Berkeley, CA 94720, USA   
2Computational Research Division, Lawrence Berkeley National Laboratory, Berkeley, CA 94720, USA

Preparing the ground state of a given Hamiltonian and estimating its ground energy are important but computationally hard tasks. However, given some additional information, these problems can be solved efficiently on a quantum computer. We assume that an initial state with non-trivial overlap with the ground state can be efficiently prepared, and the spectral gap between the ground energy and the first excited energy is bounded from below. With these assumptions we design an algorithm that prepares the ground state when an upper bound of the ground energy is known, whose runtime has a logarithmic dependence on the inverse error. When such an upper bound is not known, we propose a hybrid quantum-classical algorithm to estimate the ground energy, where the dependence of the number of queries to the initial state on the desired precision is exponentially improved compared to the current state-ofthe-art algorithm proposed in [Ge et al. 2019]. These two algorithms can then be combined to prepare a ground state without knowing an upper bound of the ground energy. We also prove that our algorithms reach the complexity lower bounds by applying it to the unstructured search problem and the quantum approximate counting problem.

# 1 Introduction

Estimating ground energy and obtaining information on the ground state of a given quantum Hamiltonian are of immense importance in condensed matter physics, quantum chemistry, and quantum information. Classical methods suffer from the exponential growth of the size of Hilbert space, and therefore quantum computers are expected to be used to overcome this difficulty. However even for quantum computer, estimating the ground energy is a hard problem: deciding whether the smallest eigenvalue of a generic local Hamiltonian is greater than $b$ or smaller than $a$ for some $a < b$ is QMA-complete [1, 27, 29, 39].

Therefore to make the problem efficiently solvable we need more assumptions. We denote the Hamiltonian we are dealing with by $H$ , and consider its spectral decomposition $\begin{array} { r } { H = \sum _ { k } \lambda _ { k } \left| \psi _ { k } \right. \left. \psi _ { k } \right| } \end{array}$ where $\lambda _ { k } \le \lambda _ { k + 1 }$ . The key assumption is that we have an initial state $| \phi _ { 0 } \rangle$ which can be efficiently prepared by an oracle $U _ { I }$ , and has some overlap with the ground state $| \psi _ { 0 } \rangle$ lower bounded by $\gamma$ . This is a reasonable assumption in many practical scenarios. For instance, even for strongly-correlated molecules in quantum chemistry, there is often a considerable overlap between the true ground state and the Hartree-Fock state. The latter can be trivially prepared in the molecular orbital basis, and efficiently prepared in other basis [30]. For the moment we also assume the spectral gap is bounded from below: $\lambda _ { 1 } - \lambda _ { 0 } \ge \Delta$ .

With these assumptions we can already use phase estimation coupled with amplitude amplification [12] to prepare the ground state, if we further know the ground energy to high precision. To our knowledge, the most comprehensive work on ground state preparation and ground state energy estimation was done by Ge et al. [21], which provided detailed complexity estimates for well-known methods such as phase estimation, and proposed new methods to be discussed below. As analyzed in [21, Appendix A], in order to prepare the ground state to fidelity1 $1 - \epsilon$ , the runtime of the controlled-time-evolution of the Hamiltonian is $\widetilde { \cal O } ( 1 / ( \gamma ^ { 2 } \Delta \epsilon ) )$ 2, and the number of queries to $U _ { I }$ is $\widetilde { \mathcal { O } } ( 1 / \gamma )$ , assuming the spectral norm of $H$ is bounded by a constant. This is however far from optimal. Poulin and Wocjan [42] proposed a method that, by executing the inverse of phase estimation to filter out the unwanted components in the initial state, can prepare a state whose energy is in a certain given range. A different choice of parameters yields a way to prepare the ground state to fidelity $1 - \epsilon$ by running the controlled-time-evolution of the Hamiltonian with $\widetilde { \mathcal { O } } ( 1 / ( \gamma \Delta ) \log ( 1 / \epsilon ) )$ runtime, and using $\widetilde { \mathcal { O } } ( 1 / \gamma )$ queries to $U _ { I }$ [21, Appendix C].

A key difference between ground state preparation and Hamiltonian simulation, where significant progress has been made in recent years [8, 9, 17, 32, 33, 34, 35], is its non-unitary nature. The recent development of linear combination of unitaries (LCU) method [9, 15] provided a versatile tool to apply non-unitary operators. Using LCU, Ge et al. proposed a new method to filter the initial state by applying a linear combination of time-evolutions of different time length [21], which achieves the same complexity, up to logarithmic factors, as the modified version of Poulin and Wocjan’s method discussed above.

All of the above methods prepare the ground state assuming the ground energy is known to high precision. When the ground energy is unknown, Ge et al. proposed a method to estimate the ground energy using a search method called minimum label finding [21]. This method can estimate the ground energy to precision $h$ by running the controlled-√ time-evolution of the Hamiltonian for $\mathcal { \tilde { O } } ( 1 / ( \gamma h ^ { 3 / 2 } ) )$ 3, and querying $U _ { I }$ $\widetilde { \cal O } ( 1 / ( \gamma \sqrt { h } ) )$ times. It is worth noting that their method requires $h = \widetilde { \mathcal { O } } ( \Delta )$ , and therefore is very expensive when the gap is extremely small. When the ground energy is not known a priori , Ge et al. proposed a method to first estimate the ground energy and then apply the LCU approach.

In recent years several hybrid quantum-classical algorithms have been developed to estimate the ground energy, or to prepare the ground state, or both. The variational quantum eigenvalue solver (VQE) [41] has gained much attention recently because of its low requirement for circuit depth and its variational structure. However the exact complexity of this algorithm is not clear because it relies on a proper choice of ansatz and needs to solve a non-convex optimization problem. Other such algorithms include quantum imaginary-time evolution, quantum Lanczos [37], and quantum filter diagonalization [40, 44]. Their complexities are either quasi-polynomial or unknown.

The recent development of block-encoding [9] and quantum signal processing (QSP) [23, 33, 36] enables us to apply non-unitary operators, specifically polynomials of a blockencoded matrix efficiently. It uses a minimal number of ancilla qubits, and avoids the Hamiltonian simulation. These will be the basic tools of this work, of which we give a brief introduction below.

Block-encoding is a powerful tool to represent a non-unitary matrix in the quantum circuit. A matrix $A \in \mathbb { C } ^ { N \times N }$ where $N = 2 ^ { n }$ can be encoded in the upper-left corner of an

$( m + n )$ -qubit unitary matrix if

$$
\| A - \alpha ( \langle 0 ^ { m } | \otimes I ) U ( | 0 ^ { m } \rangle \otimes I ) \| _ { 2 } \le \epsilon .
$$

In this case we say $U$ is an $( \alpha , m , \epsilon )$ -block-encoding of $A$ . Many matrices of practical interests can be efficiently block-encoded. In particular we will discuss the block-encoding of Hamiltonians of physical systems in Section 7.

Using the block-encoding of a Hermitian $A$ , QSP enables us to construct blockencodings for a large class of polynomial eigenvalue transformations of $A$ . We pay special attention to even or odd polynomials with real coefficients, because we only apply this type of polynomial eigenvalue transformation in this work. Also for simplicity we assume the block-encoding is done without error. [23, Theorem 2] enables us to perform eigenvalue transformation of $A$ for polynomials of definite parity (even or odd).

Theorem 1 (QSP for polynomials of definite parity). Let $U$ be an $( \alpha , m , 0 )$ -block-encoding of a Hermitian matrix $A$ . Let $P \in \mathbb { R } [ x ]$ be a degree- $\ell$ even or odd real polynomial and $| P ( x ) | \leq 1$ for any $x \in [ - 1 , 1 ]$ . Then there exists an $( 1 , m + 1 , 0 )$ -block-encoding $\widetilde { U }$ of $P ( A / \alpha )$ using $\ell$ queries of $U$ , $U ^ { \dagger }$ , and $\mathcal { O } ( ( m + 1 ) \ell )$ other primitive quantum gates.

Remark 2. [23, Theorem $\mathcal { Z } \rvert$ provides a singular value transformation for any square matrix $A$ and polynomials of definite parity. When $A$ is a Hermitian matrix, the eigenvalue transformation is the same as the singular value transformation [23, Page 203]. A related statement in the same paper is [23, Theorem 31], which describes the eigenvalue transformation of a Hermitian matrix for an arbitrary polynomial, by means of a linear combination of two polynomials of even and odd parities respectively.

Constructing the quantum circuit for QSP requires computing a sequence of phase factors beforehand, and there are classical algorithms capable of doing this [25]. Some recent progress has been made to efficiently compute phase factors for high-degree polynomials to high precision [13, 19]. In this work, unless otherwise specified, we assume the phase factors are computed without error.

Using the tools introduced above, we assume the Hamiltonian $H$ is given in its $( \alpha , m , 0 )$ - block-encoding $U _ { H }$ . This, together with $U _ { I }$ , are the two oracles we assume we are given in this work. QSP enables us to filter eigenstates using fewer qubits than LCU. In [31] a filtering method named optimal eigenstate filtering is introduced. It is based on an explicitly constructed optimal minimax polynomial, and achieves the same asymptotic complexity, ignoring poly-logarithmic factors, as the method by Ge et al. when applied to the ground state preparation problem if the ground energy is known exactly.

In this work we first develop a filtering method that filters out all eigenstates corresponding to eigenvalues above a certain threshold. This filtering method enables us to prepare the ground state of a Hamiltonian with spectral gap bounded away from zero when only an upper bound of the ground energy is known, unlike in the filtering methods discussed above which all require either exact value or high-precision estimate of the ground energy. Our filtering method has an exponentially improved dependence on precision compared to Kitaev’s phase estimation [28] and uses fewer qubits compared to other variants of the phase estimation algorithm [21, 42]. This filtering method, applied to the initial state given in our assumption, also enables us to tell whether the ground energy is smaller than $a$ or greater than $b$ for some $b > a$ , with high probability. Therefore a binary search yields a ground energy estimate with success probability arbitrarily close to one. We then combine the filtering method and ground energy estimation to prepare the ground state when no non-trivial bound for the ground energy is known. A comparison of the query complexities between the method in our work and the corresponding ones in [21], which to our best knowledge achieve state-or-the-art query complexities, are shown in Table 1.

<table><tr><td rowspan=1 colspan=1></td><td rowspan=1 colspan=1></td><td rowspan=1 colspan=1>Preparation(bound known)</td><td rowspan=1 colspan=1>Ground energy</td><td rowspan=1 colspan=1>Preparation(bound unknown)</td></tr><tr><td rowspan=2 colspan=1>UH</td><td rowspan=1 colspan=1>This work</td><td rowspan=1 colspan=1>O ( log(1))</td><td rowspan=1 colspan=1>( g()</td><td rowspan=1 colspan=1> ( log()</td></tr><tr><td rowspan=1 colspan=1>Ge et al.</td><td rowspan=1 colspan=1>$$(\fr{)$</td><td rowspan=1 colspan=1>bα{3/2(γh3/2</td><td rowspan=1 colspan=1>bα3/2γ∆3/2</td></tr><tr><td rowspan=2 colspan=1>UI</td><td rowspan=1 colspan=1>This work</td><td rowspan=1 colspan=1>O(\)</td><td rowspan=1 colspan=1> ( log(r) log(1)</td><td rowspan=1 colspan=1>O (1 log(α) log( 1))</td></tr><tr><td rowspan=1 colspan=1>Ge et al.</td><td rowspan=1 colspan=1>$({)</td><td rowspan=1 colspan=1>δ (t )</td><td rowspan=1 colspan=1>( )</td></tr><tr><td rowspan=2 colspan=1>Extraqubits</td><td rowspan=1 colspan=1>This work</td><td rowspan=1 colspan=1>O(1)</td><td rowspan=1 colspan=1>O(log(1 ))</td><td rowspan=1 colspan=1>O(log( ))</td></tr><tr><td rowspan=1 colspan=1>Ge et al.</td><td rowspan=1 colspan=1>O(log( 1 log( 1 )))</td><td rowspan=1 colspan=1>O(log( 1))</td><td rowspan=1 colspan=1>O(log(  log( 1 )))</td></tr></table>

Table 1: The query complexities of algorithms and number of extra qubits used in our work and the corresponding ones by Ge et al. in [21]. $\alpha , \gamma , \Delta , \epsilon$ are the same as above and $h$ is the precision of the ground energy estimate. By extra qubits we mean the ancilla qubits that are not part of the block-encoding. In this work the ground energy estimation algorithm and the algorithm to prepare ground state without a priori bound have success probabilities lower bounded by $1 - \vartheta$ , while in [21] the corresponding algorithms have constant success probabilities. The complexities for algorithms by Ge et al. are estimated assuming Hamiltonian simulation is done as in [34]. The usage of the notation $\widetilde { \mathcal { O } }$ is [21] different from that in our work, as explained in footnote 3.

From the query complexities in Table 1 we can see our method for ground energy estimation achieves a exponential speedup in terms of the dependence of number of queries√ to $U _ { I }$ on the ground energy estimate precision $h$ and a speedup of $1 / { \sqrt { h } }$ factor in the dependence of number of queries to $U _ { H }$ on the precision. Moreover, Ge et al. assumes in their work that the precision $h = \widetilde { \mathcal { O } } ( \Delta )$ , while we make no such assumptions. This gives our algorithm even greater advantage when the gap is much smaller than desired precision. This becomes useful in the case of preparing a low energy state (not necessarily a ground state). Because Ge et al. used a slightly different query assumption, i.e. access to time-evolution rather than block-encoding, when computing the complexities for methods in [21] in Table 1 we assume the Hamiltonian simulation is done with $\mathcal { O } ( \alpha t )$ queries to $U _ { H }$ , and the error is negligible. This can be achieved using the Hamiltonian simulation in [34], and cannot be asymptotically improved because of the complexity lower bound proved in [9]. Therefore the comparison here is fair even though our work makes use of a different oracle. Also [21] assumed a scaled Hamiltonian $H$ with its spectrum contained in $[ 0 , 1 ]$ . We do not make such an assumption, and therefore the $\alpha$ factor should be properly taken into account as is done in Table 1.

Organization: The rest of the paper is organized as follows. In Section 2 we use QSP to construct block-encodings of reflectors and projectors associated with eigen-subspaces. In Section 3 we use the projectors to prepare ground state when an upper bound of the ground energy is given. In Section 4 we introduce the ground energy estimation algorithm, a hybrid quantum-classical algorithm based on the binary search, and use it to prepare the ground state when no ground energy upper bound is known a priori . In Section 5 we show the dependence of our query complexities on the overlap and gap is essentially optimal by considering the unstructured search problem. We also show the dependence of our ground energy estimation algorithm on the precision is nearly optimal by considering the quantum approximate counting problem. In Section 6 we use our methods to prepare low-energy states when the spectral lower gap is unknown, or even when the ground state is degenerate. In Section 7 we discuss practical issues and future research directions.

# 2 Block-encoding of reflector and projector

A key component in our method is a polynomial approximation of the sign function in the domain $[ - 1 , - \delta ] \cup [ \delta , 1 ]$ . The error scaling of the best polynomial approximation has been studied in [20], and an explicit construction of a polynomial with the same error scaling is provided in [33] based on the approximation of the erf function. We quote [23, Lemma 14] here with some small modification:

Lemma 3 (Polynomial approximation of the sign function). For all $0 ~ < ~ \delta ~ < ~ 1$ , $0 ~ <$ $\epsilon \ < 1$ , there exists an efficiently computable odd polynomial $S ( \cdot ; \delta , \epsilon ) \in \mathbb { R } [ x ]$ of degree $\begin{array} { r } { \ell = \mathcal { O } ( \frac { 1 } { \delta } \log ( \frac { 1 } { \epsilon } ) ) } \end{array}$ , such that

(1) for all $x \in [ - 1 , 1 ]$ , $| S ( x ; \delta , \epsilon ) | \le 1$ , and

Remark 4. Compared to [23, Lemma 14] we have rescaled the interval from $[ - 2 , 2 ]$ to $[ - 1 , 1 ]$ , and this does not result in any substantial change.

When we have the $( \alpha , m , 0 )$ -block-encoding of a Hermitian matrix $\begin{array} { r } { H = \sum _ { k } \lambda _ { k } \left| \psi _ { k } \right. \left. \psi _ { k } \right| \in } \end{array}$ $\mathbb { C } ^ { N \times N }$ , $N = 2 ^ { n }$ , $\lambda _ { k } \le \lambda _ { k + 1 }$ , we can construct a $( \alpha + \mu | , m + 1 , 0 )$ -block-encoding of matrix obtain an using of [23, Lemma 29] for any $( 1 , m + 2 , 0 )$ -block-encoding of $\mu \in \mathbb { R }$ $- S ( \frac { H - \mu I } { \alpha + | \mu | } ; \delta , \epsilon )$ . Then using QSP, by Theorem 1, we can for any $\delta$ and $\epsilon$ . If we assume further that $\Delta / 2 \le \mathrm { m i n } _ { k } | \mu - \lambda _ { k } |$ , then we let $\begin{array} { r } { \delta = \frac { \Delta } { 4 \alpha } } \end{array}$ , and by Lemma 3 all the eigenvalues of $- S ( \frac { H - \mu I } { \alpha + | \mu | } ; \delta , \epsilon )$ are $\epsilon$ -close to either $0$ or $^ 1$ . Therefore $- S ( \frac { H - \mu I } { \alpha + | \mu | } ; \delta , \epsilon )$ is $\epsilon$ -close, in operator norm, to the reflector about the direct sum of eigen-subspaces corresponding to eigenvalues smaller than $\mu$ :

$$
R _ { < \mu } = \sum _ { k : \lambda _ { k } < \mu } \left| \psi _ { k } \right. \left. \psi _ { k } \right| - \sum _ { k : \lambda _ { k } > \mu } \left| \psi _ { k } \right. \left. \psi _ { k } \right| ,
$$

and thus the block-encoding is also an $( 1 , m + 2 , \epsilon )$ -block-encoding of $R _ { < \mu }$ . We denote this block-encoding by $\mathrm { R E F } ( \mu , \delta , \epsilon )$ . We omitted the dependence on $H$ because $H$ as well as its block-encoding is usually fixed in the rest of the paper.

In the above discussion we have used QSP in a black-box manner. For concreteness, we present a single-qubit illustrative example to demonstrate how to use a block-encoded Hamiltonian to construct the reflector in Appendix A.

Because our goal is to prepare the ground state, we will use the projector more often than the reflector. Now we construct a block-encoding of projector using $\mathrm { R E F } ( \mu , \delta , \epsilon )$ by the following circuit

![](images/30b5ee6baf46110b350b6e33af2b622a03a419f5a86da803c411a963e7a56210.jpg)

where $\mathrm { H }$ is the Hadamard gate, and we denote this circuit as PROJ $( \mu , \delta , \epsilon )$ . Note that

$$
\begin{array} { r l } & { ( \langle 0 ^ { m + 3 } | \otimes I ) \mathrm { P R O J } ( \mu , \delta , \epsilon ) ( | 0 ^ { m + 3 } \rangle \otimes I ) } \\ & { = \Big ( \langle + | \langle 0 ^ { m + 2 } | \otimes I \Big ) \Big ( | 0 \rangle \langle 0 | \otimes I \otimes I + | 1 \rangle \langle 1 | \otimes \mathrm { R E F } ( \mu , \delta , \epsilon ) \Big ) \Big ( | + \rangle | 0 ^ { m + 2 } \rangle \otimes I \Big ) } \\ & { = \cfrac { 1 } { 2 } \Big ( I + ( \langle 0 ^ { m + 2 } | \otimes I \rangle \mathrm { R E F } ( \mu , \delta , \epsilon ) ( | 0 ^ { m + 2 } \rangle \otimes I ) \Big ) , } \end{array}
$$

and we have

$$
\begin{array} { r l } & { \| ( \langle 0 ^ { m + 3 } | \otimes I ) \mathrm { P R O J } ( \mu , \delta , \epsilon ) ( | 0 ^ { m + 3 } \rangle \otimes I ) - P _ { < \mu } \| } \\ & { \leq \frac { 1 } { 2 } \| ( \langle 0 ^ { m + 2 } | \otimes I ) \mathrm { R E F } ( \mu , \delta , \epsilon ) ( | 0 ^ { m + 2 } \rangle \otimes I ) - R _ { < \mu } \| } \\ & { \leq \frac { \epsilon } { 2 } . } \end{array}
$$

Here $P _ { < \mu }$ is the projector into the direct sum of eigen-subspaces corresponding to eigenvalues smaller than $\mu$

$$
P _ { < \mu } = \sum _ { k : \lambda _ { k } < \mu } | \psi _ { k } \rangle \langle \psi _ { k } | = \frac { 1 } { 2 } ( I + R _ { < \mu } ) .
$$

Therefore PROJ $( \mu , \delta , \epsilon )$ is an $( 1 , m + 3 , \epsilon / 2 )$ -block-encoding of $P _ { < \mu }$ . In fact this can still be seen as an application of linear combination of block encoding [23, Lemma 29], using the relation $P _ { < \mu } = { \scriptstyle { \frac { 1 } { 2 } } } ( R _ { < \mu } + I )$ .

We use the following lemma to summarize the results

Lemma 5 (Reflector and projector). Given a Hermitian matrix $H$ with its $( \alpha , m , 0 )$ - block-encoding $U _ { H }$ , with the guarantee that $\mu \in \mathbb { R }$ is separated from the spectrum of $H$ by a gap of at least $\Delta / 2$ , we can construct an $( 1 , m + 2 , \epsilon )$ -block-encoding of $R _ { < \mu }$ , and an $( 1 , m + 3 , \epsilon / 2 )$ -block-encoding of $P _ { < \mu }$ , both using $\begin{array} { r } { \mathcal { O } \big ( \frac { \alpha } { \Delta } \log \big ( \frac { 1 } { \epsilon } \big ) \big ) } \end{array}$ applications of $U _ { H }$ and $U _ { H } ^ { \dagger }$ , and $\mathcal { O } ( \frac { m \alpha } { \Delta } \log ( \frac { 1 } { \epsilon } ) )$ other one- and two-qubit gates.

We remark that for the block-encoding PROJ $( \mu , \delta , \epsilon )$ , even a failed application of it can give us potentially useful information. We have

$$
\mathrm { P R O J } ( \mu , \delta , \epsilon ) | 0 ^ { m + 3 } \rangle | \phi \rangle = | 0 \rangle | 0 ^ { m + 2 } \rangle P _ { < \mu } | \phi \rangle + | 1 \rangle | 0 ^ { m + 2 } \rangle P _ { > \mu } | \phi \rangle + { \frac { 1 } { \sqrt { 2 } } } | \ l { - } \rangle | E \rangle ,
$$

where $P _ { > \mu } = I - P _ { < \mu }$ and $| E \rangle$ satisfies $\| \left| E \right. \| \leq \epsilon$ . Thus when we apply the block-encoding and measure the first two registers, i.e. the first $m + 3$ qubits, we have probability at least $1 - \frac { \epsilon ^ { 2 } } { 2 }$ to obtain an outcome with either 0 or 1 followed by $( m + 2 )$ 0’s. In the former case the projection has been successful, and in the latter case we have obtained an approximation of $P _ { > \mu } \left| \phi \right.$ .

If we do not treat the output of 1 followed by $m + 2$ 0’s as failure then there is another interpretation of the circuit PROJ $( \mu , \delta , \epsilon )$ : this is an approximate projective measurement $\{ P _ { < \mu } , P _ { > \mu } \}$ . In fact the whole circuit can be seen as phase estimation on a reflector, which needs only one ancilla qubit.

# 3 Algorithm with a priori ground energy bound

With the approximate projector developed in the previous section we can readily design an algorithm to prepare the ground state. We assume we have the Hamiltonian $H$ given through its block-encoding as in the last section. If we are further given an initial state $| \phi _ { 0 } \rangle$ prepared by a unitary $U _ { I }$ , i.e. $U _ { I } \left| 0 ^ { n } \right. = \left| \phi _ { 0 } \right.$ , and the promises that for some known $\gamma > 0$ , $\mu$ , and $\Delta$ , we have

(P1) Lower bound for the overlap: $| \left. \phi _ { 0 } | \psi _ { 0 } \right. | \geq \gamma$ , (P2) Bounds for the ground energy and spectral gap: $\lambda _ { 0 } \le \mu - \Delta / 2 < \mu + \Delta / 2 \le \lambda _ { 1 }$ .

Here $\mu$ is an upper bound for the ground energy, $\Delta$ is a lower bound for the spectral gap, and $\gamma$ is a lower bound for the initial overlap. Now suppose we want to prepare the ground state to precision $\epsilon$ , we can use Lemma 5 to build a block-encoding of the projector $P _ { < \mu } = \left| \psi _ { 0 } \right. \left. \psi _ { 0 } \right|$ , and then apply it to $| \phi _ { 0 } \rangle$ which we can prepare. This will give us something close to $| \psi _ { 0 } \rangle$ . We use fidelity to measure how close we can get. To achieve $1 - \epsilon$ fidelity we need to use circuit PROJ $( \mu , \Delta / 4 \alpha , \gamma \epsilon )$ , and we denote,

$$
\widetilde { P } _ { < \mu } = ( \langle 0 ^ { m + 3 } | \otimes I ) \mathrm { P R O J } ( \mu , \Delta / 4 \alpha , \gamma \epsilon ) ( | 0 ^ { m + 3 } \rangle \otimes I )
$$

then the resulting fidelity will be

$$
\frac { | \left. \psi _ { 0 } | \tilde { P } _ { < \mu } | \phi _ { 0 } \right. | } { \| \tilde { P } _ { < \mu } | \phi _ { 0 } \rangle \| } \ge \frac { | \left. \psi _ { 0 } | \phi _ { 0 } \right. | - \gamma \epsilon / 2 } { | \left. \psi _ { 0 } | \phi _ { 0 } \right. | + \gamma \epsilon / 2 } \ge 1 - \frac { \gamma \epsilon } { | \left. \psi _ { 0 } | \phi _ { 0 } \right. | } \ge 1 - \epsilon .
$$

Here we have used

$$
\| \widetilde { P } _ { < \mu } \left| \phi _ { 0 } \right. \| \le \| P _ { < \mu } \left| \phi _ { 0 } \right. + ( \widetilde { P } _ { < \mu } - P _ { < \mu } ) \left| \phi _ { 0 } \right. \| \le | \langle \psi _ { 0 } | \phi _ { 0 } \rangle | + \gamma \epsilon / 2 .
$$

This is when we have a successful application of the block-encoding. The success probability is

$$
\| \widetilde { P } _ { < \mu } \left| \phi _ { 0 } \right. \| ^ { 2 } \ge \left( \| P _ { < \mu } \left| \phi _ { 0 } \right. \| - \frac { \gamma \epsilon } { 2 } \right) ^ { 2 } \ge \gamma ^ { 2 } \left( 1 - \frac { \epsilon } { 2 } \right) ^ { 2 } .
$$

With amplitude amplification [12] we can boost the success probability to $\Omega ( 1 )$ with $\mathcal { O } ( { \textstyle \frac { 1 } { \gamma } } )$ applications of PROJ $( \mu , \Delta / 4 \alpha , \gamma \epsilon )$ and its inverse, as well as $\mathcal { O } ( { \scriptstyle { \frac { m } { \gamma } } } )$ other one- and twoqubit gates. Here we are describing the expected complexity since the procedure succeeds with some constant probability. In amplitude amplification we need to use a reflector similar to the oracle used in Grover’s search algorithm [24]. Instead of constructing a reflector from PROJ $( \mu , \Delta / 4 \alpha , \gamma \epsilon )$ we can directly use $\mathrm { R E F } ( \mu , \Delta / 4 \alpha , \gamma \epsilon )$ constructed in the previous section.

We summarize the results in the following theorem

Theorem 6 (Ground state preparation with a priori ground energy bound). Suppose we have Hamiltonian $\begin{array} { r } { H = \sum _ { k } \lambda _ { k } \left| \psi _ { k } \right. \left. \psi _ { k } \right| \in \mathbb { C } ^ { N \times N } } \end{array}$ , where $\lambda _ { k } \le \lambda _ { k + 1 }$ , given through its $( \alpha , m , 0 )$ -block-encoding $U _ { H }$ . Also suppose we have an initial state $| \phi _ { 0 } \rangle$ prepared by circuit $U _ { I }$ , as well as the promises (P1) and (P2). Then the ground state $| \psi _ { 0 } \rangle$ can be prepared to fidelity $1 - \epsilon$ with the following costs:

1. Query complexity: $\begin{array} { r } { \mathcal { O } \big ( \frac { \alpha } { \gamma \Delta } \log \big ( \frac { 1 } { \gamma \epsilon } \big ) \big ) } \end{array}$ queries to $U _ { H }$ and $\mathcal { O } ( { \textstyle \frac { 1 } { \gamma } } )$ queries to $U _ { I }$ ,   
2. Number of qubits: ${ \mathcal { O } } ( n + m )$ ,   
3. Other one- and two- qubit gates: $\begin{array} { r } { \mathcal { O } ( \frac { m \alpha } { \gamma \Delta } \log ( \frac { 1 } { \gamma \epsilon } ) ) } \end{array}$ .

# 4 Algorithm without a priori ground energy bound

Next we consider the case when we are not given a known $\mu$ to bound the ground energy from above. All other assumptions about $H$ and its eigenvalues and eigenstates are identical to the previous sections. The basic idea is to test different values for $\mu$ and perform a binary search. This leads to a quantum-classical hybrid method that can estimate the ground energy as well as preparing the ground state to high precision.

All eigenvalues must be in the interval $[ - \alpha , \alpha ]$ , thus we first partition $[ - \alpha , \alpha ]$ by grid points $- \alpha = x _ { 0 } < x _ { 1 } < . . . < x _ { G } = \alpha$ , where $x _ { k + 1 } - x _ { k } = h$ for all $k$ . Then we attempt to locate $\lambda _ { 0 }$ in a small interval between two grid points (not necessarily adjacent, but close) through a binary search. To do a binary search we need to be able to tell whether a given $x _ { k }$ is located to the left or right of $\lambda _ { 0 }$ . Because of the random nature of measurement we can only do so correctly with some probability, and we want to make this probability as close to 1 as possible. This is achieved using a technique we call binary amplitude estimation.

Lemma 7 (Binary amplitude estimation). Let $U$ be a unitary that acts on two registers, the first register indicating success or failure. Let $A = \| ( \langle 0 | \otimes I ) U ( | 0 \rangle | 0 \rangle ) \|$ be the success amplitude. Given $\gamma _ { 0 }$ and $\gamma _ { 1 }$ , $\Delta : = \gamma _ { 1 } - \gamma _ { 0 } > 0$ , provided that $A$ is either smaller than $\gamma _ { 0 }$ or greater than $\gamma _ { 1 }$ , we can correctly distinguish between the two cases, i.e. output 0 for the former and 1 for the latter, with probability $1 - \delta$ using $\mathcal { O } ( ( 1 / \Delta ) \log ( 1 / \delta ) )$ applications of (controlled-) $U$ and its inverse.

Proof. The proof is essentially identical to the proof for gapped phase estimation in [2, 15]. We can perform amplitude estimation up to error $\Delta / 4$ with $\mathcal { O } ( 1 / \Delta )$ applications of $U$ and $U ^ { \dagger }$ . This has a success probability of $8 / \pi ^ { 2 }$ according to Theorem 12 of [12]. We turn the estimation result into a boolean indicating whether it is larger or smaller than $( \gamma _ { 0 } + \gamma _ { 1 } ) / 2$ . The boolean is correct with probability at least $8 / \pi ^ { 2 }$ . Then we do a majority voting to boost this probability. Chernoff bound guarantees that to obtain a $1 - \delta$ probability of getting the correct output we need to repeat $\mathcal { O } ( \log ( 1 / \delta ) )$ times. Therefore in total we need to run $U$ and $U ^ { \dagger } ~ \mathcal { O } ( ( 1 / \Delta ) \log ( 1 / \delta ) )$ times. □

We then apply binary amplitude estimation to the block-encoding of the projector defined in (2) $\mathrm { P R O J } ( x _ { k } , h / 2 \alpha , \epsilon ^ { \prime } )$ for some precision $\epsilon ^ { \prime }$ to be chosen. We denote the amplitude of the “good” component after applying block-encoding by

$$
A _ { k } = \| ( \langle 0 ^ { m + 3 } | \otimes I ) \mathrm { P R O J } ( x _ { k } , h / 2 \alpha , \epsilon ^ { \prime } ) ( | 0 ^ { m + 3 } \rangle | \phi \rangle ) \| ,
$$

which satisfies the following:

$$
A _ { k } \left\{ \begin{array} { l l } { \geq \gamma - \frac { \epsilon ^ { \prime } } { 2 } , } & { \lambda _ { 0 } \leq x _ { k - 1 } , } \\ { } & { } \\ { \leq \frac { \epsilon ^ { \prime } } { 2 } , } & { \lambda _ { 0 } \geq x _ { k + 1 } . } \end{array} \right.
$$

We can then let

$$
\epsilon ^ { \prime } = \gamma / 2 ,
$$

the two amplitudes are separated by a gap lower bounded by $\gamma / 2$ . Therefore we can run the binary amplitude estimation, letting $U$ in Lemma 7 be

$$
U = { \mathrm { P R O J } } ( x _ { k } , h / 2 \alpha , \epsilon ^ { \prime } ) ( I \otimes U _ { I } ) ,
$$

to correctly distinguish the two cases where $\lambda _ { 0 } \le x _ { k - 1 }$ and $\lambda _ { 0 } \geq x _ { k + 1 }$ with probability $1 - \delta$ , by running PROJ $( x _ { k } , h / 2 \alpha , \epsilon ^ { \prime } )$ , $U _ { I }$ , and their inverses $\mathcal { O } ( ( 1 / \gamma ) \log ( 1 / \delta ) )$ times. The output of the binary amplitude estimation is denoted by $B _ { k }$ .

We then define $\varepsilon$ as the event that an error occurs in the final result of binary amplitude estimation when we are computing $B _ { k }$ for some $k$ such that $x _ { k + 1 } < \lambda _ { 0 }$ or $x _ { k - 1 } > \lambda _ { 0 }$ in our search process. All future discussion is conditional on $\mathcal { E } ^ { c }$ meaning that there is no error in

binary amplitude estimation for $B _ { k }$ when $x _ { k + 1 } < \lambda _ { 0 }$ or $x _ { k - 1 } > \lambda _ { 0 }$ . This has a probability that is at least $( 1 - \delta ) ^ { R }$ where $R$ is the number of times binary amplitude estimation is run.

Conditional on $\mathcal { E } ^ { c }$ , almost surely (with probability 1) $B _ { k } = 1$ when $\lambda _ { 0 } \le x _ { k - 1 }$ and $B _ { k } = 0$ when $\lambda _ { 0 } ~ \ge ~ x _ { k + 1 }$ . Therefore $B _ { k } = 0$ tells us $\lambda _ { 0 } > x _ { k - 1 }$ and $B _ { k } = 1$ tells us $\lambda _ { 0 } < x _ { k + 1 }$ . $B _ { k }$ and $B _ { k + 1 }$ combined give us the information as shown in Table 2.

<table><tr><td rowspan=1 colspan=1>Bk</td><td rowspan=1 colspan=1>Bk+1</td><td rowspan=1 colspan=1>Position of λ0</td></tr><tr><td rowspan=1 colspan=1>1</td><td rowspan=1 colspan=1>1</td><td rowspan=1 colspan=1>λ0 &lt; xk+1</td></tr><tr><td rowspan=1 colspan=1>0</td><td rowspan=1 colspan=1>0</td><td rowspan=1 colspan=1>λ0 &gt; xk</td></tr><tr><td rowspan=1 colspan=1>0</td><td rowspan=1 colspan=1>1</td><td rowspan=1 colspan=1>xk−1 &lt; λ0 &lt; xk+2</td></tr><tr><td rowspan=1 colspan=1>1</td><td rowspan=1 colspan=1>0</td><td rowspan=1 colspan=1>xk &lt; λ0 &lt; xk+1</td></tr></table>

Table 2: Conditional on $\mathcal { E } ^ { c }$ , $B _ { k }$ and $B _ { k + 1 }$ can provide us with the information as shown in the table.

# Algorithm 1 Binary search to locate $\lambda _ { 0 }$

$L \gets 0 , U \gets G$   
while $U - L > 3$ do $k = \lfloor ( L + U ) / 2 \rfloor$ Run binary amplitude estimation to get $B _ { k }$ and $B _ { k + 1 }$ . switch $\left( \boldsymbol { B } _ { k } , \boldsymbol { B } _ { k + 1 } \right)$ case $( 1 , 1 )$ : $U \gets k + 1$ case $( 0 , 0 )$ : $L \gets k$ case $( 0 , 1 )$ : return $k - 1$ , $k + 2$ case $( 1 , 0 )$ : return $k$ , $k + 1$ end switch   
end while   
return $L , U$

Using the Table 2 we can do the binary search as outlined in Algorithm 1. For the $\ell$ -th step in Algorithm 1 we denote the integer variables $U$ and $L$ by $U _ { \ell }$ and $L _ { \ell }$ . In all four outcomes for $\left( \boldsymbol { B } _ { k } , \boldsymbol { B } _ { k + 1 } \right)$ , if the algorithm does not terminate at this step, then the new $U _ { \ell + 1 } - L _ { \ell + 1 }$ will be at most $( U _ { \ell } - L _ { \ell } ) / 2 + 1$ . Since $U _ { 0 } - L _ { 0 } = G$ at the very beginning, we can show inductively $U _ { \ell } - L _ { \ell } \leq ( G - 2 ) / 2 ^ { \ell } + 2$ . Therefore when $\ell \geq \log _ { 2 } ( G - 2 )$ we have $U _ { \ell } - L _ { \ell } \leq 3$ . Thus the algorithm must terminate in $\lceil \log _ { 2 } ( G ) \rceil = \mathcal { O } ( \log ( \alpha / h ) )$ steps. The output we denote by $L$ and $U$ . They satisfy $x _ { L } < \lambda _ { 0 } < x _ { U }$ and $U - L \leq 3$ .

If we want the whole procedure to be successful with probability at least $1 - \vartheta$ , then we need $\operatorname { P r o b } ( { \mathcal { E } } ^ { c } ) \geq 1 - \vartheta$ . Since

$$
\operatorname { P r o b } ( \mathcal { E } ^ { c } ) \geq ( 1 - \delta ) ^ { \lceil \log _ { 2 } ( G ) \rceil } \geq ( 1 - \delta ) ^ { \log _ { 2 } ( 4 \alpha / h ) } ,
$$

we only need, for small $\vartheta$ ,

$$
\delta \leq \frac { \vartheta } { 2 \log _ { 2 } ( 4 \alpha / h ) } .
$$

Algorithm 1 enables us to locate $\lambda _ { 0 }$ within an interval of length at most $3 h$ . In total we need to run binary amplitude estimation at most ${ \mathcal { O } } ( \log ( \alpha / h ) )$ times. Each amplitude estimation queries $\mathrm { P R O J } ( x _ { k } , h / 2 \alpha , \epsilon ^ { \prime } )$ and $U _ { I } ~ { \mathcal { O } } ( ( 1 / \gamma ) \log ( 1 / \delta ) )$ times, where $\epsilon ^ { \prime } = \gamma / 2$ . Therefore the number of queries to $U _ { H }$ and $U _ { I }$ are respectively

$$
\mathcal { O } \left( \frac { \alpha } { \gamma h } \log \left( \frac { \alpha } { h } \right) \log \left( \frac { 1 } { \gamma } \right) \log \left( \frac { \log ( \alpha / h ) } { \vartheta } \right) \right) , \quad \mathcal { O } \left( \frac { 1 } { \gamma } \log \left( \frac { \alpha } { h } \right) \log \left( \frac { \log ( \alpha / h ) } { \vartheta } \right) \right) .
$$

In particular, in the procedure above we did not use (P2) but only used (P1). Therefore we do not need to assume the presence of a gap. The result can be summarized into the following theorem:

Theorem 8 (Ground energy). Suppose we have Hamiltonian $\begin{array} { r } { H \ = \ \sum _ { k } \lambda _ { k } \left| \psi _ { k } \right. \left. \psi _ { k } \right| \ \in } \end{array}$ CN×N , where λk ≤ λk+1, given through its (α, m, 0)-block-encoding UH. Also suppose we have an initial state $| \phi _ { 0 } \rangle$ prepared by circuit $U _ { I }$ , as well as the promise (P1). Then the ground energy can be estimated to precision $h$ with probability $1 - \vartheta$ with the following costs:

1. Query complexity: $\begin{array} { r } { \mathcal { O } \left( \frac { \alpha } { \gamma h } \log \left( \frac { \alpha } { h } \right) \log \left( \frac { 1 } { \gamma } \right) \log \left( \frac { \log \left( \alpha / h \right) } { \vartheta } \right) \right) } \end{array}$ queries to $U _ { H }$ and $\begin{array} { r } { \mathcal { O } \left( \frac { 1 } { \gamma } \log \left( \frac { \alpha } { h } \right) \log \left( \frac { \log \left( \alpha / h \right) } { \vartheta } \right) \right) } \end{array}$ queries to $U _ { I }$ ,

2. Number of qubits: $\begin{array} { r } { \mathcal { O } ( n + m + \log ( \frac { 1 } { \gamma } ) ) } \end{array}$ ,

3. Other one- and two- qubit gates: $\begin{array} { r } { \mathcal { O } \left( \frac { m \alpha } { \gamma h } \log \left( \frac { \alpha } { h } \right) \log \left( \frac { 1 } { \gamma } \right) \log \left( \frac { \log \left( \alpha / h \right) } { \vartheta } \right) \right) . } \end{array}$

The extra $\mathcal { O } ( \log ( 1 / \gamma ) )$ qubits needed come from amplitude estimation, which uses phase estimation. If we use Kitaev’s original version of phase estimation using only a single qubit [28], we can reduce the number of extra qubits to $\mathcal { O } ( 1 )$ . With Theorem 8 we can then use Algorithm 1 to prepare the ground state without knowing an upper bound for the ground energy beforehand, when in addition to (P1) we have a lower bound for the spectral gap:

(P2’) Bound for the spectral gap: $\lambda _ { 1 } - \lambda _ { 0 } \ge \Delta$ .

We first run Algorithm 1 to locate the ground energy in an interval $[ x _ { L } , x _ { U } ]$ of length at most $\Delta$ . Then we simply apply PR $\mathrm { O J } ( ( x _ { L } + x _ { U } ) / 2 , \Delta / 4 \alpha , \gamma \epsilon )$ to $| \phi _ { 0 } \rangle$ . This will give us an approximate ground state with at least $1 - \epsilon$ fidelity. Therefore we have the following corollary:

Corollary 9 (Ground state preparation without $a$ priori bound). Suppose we have Hamiltonian $\begin{array} { r } { H = \sum _ { k } \lambda _ { k } \left| \psi _ { k } \right. \left. \psi _ { k } \right| \in \mathbb { C } ^ { N \times N } } \end{array}$ , where $\lambda _ { k } \le \lambda _ { k + 1 }$ , given through its $( \alpha , m , 0 )$ -blockencoding $U _ { H }$ . Also suppose we have an initial state $| \phi _ { 0 } \rangle$ prepared by circuit $U _ { I }$ , as wel l as the promises (P1) and (P2’). Then the ground state can be can be prepared to fidelity $1 - \epsilon$ with probability $1 - \vartheta$ with the following costs:

1. Query complexity: $\begin{array} { r } { \mathcal { O } \left( \frac { \alpha } { \gamma \Delta } \left( \log \left( \frac { \alpha } { \Delta } \right) \log \left( \frac { 1 } { \gamma } \right) \log \left( \frac { \log \left( \alpha / \Delta \right) } { \vartheta } \right) + \log \left( \frac { 1 } { \epsilon } \right) \right) \right) } \end{array}$ queries to $U _ { H }$ and $\begin{array} { r } { \mathcal { O } \left( \frac { 1 } { \gamma } \log \left( \frac { \alpha } { \Delta } \right) \log \left( \frac { \log \left( \alpha / \Delta \right) } { \vartheta } \right) \right) } \end{array}$ queries to $U _ { I }$ ,

2. Number of qubits: $\begin{array} { r } { \mathcal { O } ( n + m + \log ( \frac { 1 } { \gamma } ) ) } \end{array}$ ,

3. Other one- and two- qubit gates: $\begin{array} { r } { \mathcal { O } \left( \frac { m \alpha } { \gamma \Delta } \left( \log \left( \frac { \alpha } { \Delta } \right) \log \left( \frac { 1 } { \gamma } \right) \log \left( \frac { \log \left( \alpha / \Delta \right) } { \vartheta } \right) + \log \left( \frac { 1 } { \epsilon } \right) \right) \right) . } \end{array}$

It may be sometimes desirable to ignore whether the procedure is successful or not. In this case we will see the output as a mixed state whose density matrix is

$$
\rho = \mathrm { P r o b } ( \mathcal { E } ^ { c } ) \left. \widetilde { \psi } _ { 0 } \right. \left. \widetilde { \psi } _ { 0 } \right. + \rho ^ { \prime } ,
$$

where $| \tilde { \psi _ { 0 } } \rangle$ is the approximate ground state with fidelity at least $1 - \epsilon$ , which is produced conditional on the event $\mathcal { E } ^ { c }$ , and $\mathrm { T r } \rho ^ { \prime } = \mathrm { P r o b } ( \mathcal { E } )$ . Then this mixed state will have a fidelity lower bounded by

$$
\langle \psi _ { 0 } | \rho | \psi _ { 0 } \rangle \geq \mathrm { P r o b } ( \mathcal { E } ^ { c } ) | \langle \widetilde { \psi } _ { 0 } | \psi _ { 0 } \rangle | ^ { 2 } \geq ( 1 - \vartheta ) ( 1 - \epsilon ) ^ { 2 } .
$$

If we want to achieve $\sqrt { 1 - \xi }$ fidelity for the mixed state, we can simply let $\vartheta = \epsilon =$ $\xi / 3$ . Thus the number of queries to $U _ { H }$ and $U _ { I }$ are $\begin{array} { r } { \widetilde { \mathcal { O } } \big ( \frac { \alpha } { \gamma \Delta } \log \big ( \frac { 1 } { \xi } \big ) \big ) } \end{array}$ and $\begin{array} { r } { \tilde { \mathcal { O } } ( \frac { 1 } { \gamma } \log ( \frac { \alpha } { \Delta } ) \log ( \frac { 1 } { \xi } ) ) } \end{array}$ respectively.

# 5 Optimality of the query complexities

In this section we prove for the ground state preparation algorithms outlined in Section 3 and Section 4 the number of queries to $U _ { H }$ and $U _ { I }$ are essentially optimal. We will also show our ground energy estimation algorithm has an nearly optimal dependence on the precision. We first prove the following complexity lower bounds:

Theorem 10. Suppose we have a generic Hamiltonian $\begin{array} { r } { H = \sum _ { k } \lambda _ { k } \left| \psi _ { k } \right. \left. \psi _ { k } \right| \in \mathbb { C } ^ { N \times N } } \end{array}$ , where $\lambda _ { k } \ \leq \ \lambda _ { k + 1 }$ , given through its $( \alpha , m , 0 )$ -block-encoding $U _ { H }$ , and $\alpha = \Theta ( 1 )$ . Also suppose we have an initial state $| \phi _ { 0 } \rangle$ prepared by circuit $U _ { I }$ , as well as the promises (P1) and (P2). Then the query complexities of preparing the ground state √ $| \psi _ { 0 } \rangle$ of $H$ to fidelity at least ${ \sqrt { 3 } } / 2$ satisfy

1. When $\Delta = \Omega ( 1 )$ , and $\gamma  0 ^ { + }$ , the number of queries to $U _ { H }$ is $\Omega ( 1 / \gamma )$ ;

2. When $\gamma = \Omega ( 1 )$ , and $\Delta  0 ^ { + }$ , the number of queries to $U _ { H }$ is $\Omega ( 1 / \Delta )$ ;

3. When $\Delta = \Omega ( 1 )$ , and $\gamma  0 ^ { + }$ , it is not possible to accomplish the above task using $\mathcal { O } ( 1 / \gamma ^ { 1 - \theta } )$ queries to $U _ { I }$ and $\mathcal { O } ( \mathrm { p o l y } ( 1 / \gamma ) )$ queries to $U _ { H }$ for any $\theta > 0$ .

Proof. We prove all three lower bounds by applying the ground state preparation algorithm to the unstructured search problem. In the unstructured search problem we try to find a $n$ -bit string $t$ marked out by the oracle

$$
U _ { t } = I - 2 \left| t \right. \left. t \right| .
$$

It is proved for this problem the number of queries to √ $U _ { t }$ to find $t$ with probability $1 / 2$ is lower bounded by $\Omega ( { \sqrt { N } } )$ where $N = 2 ^ { n }$ [6].

This problem can be seen as a ground state preparation problem. We find that $| t \rangle$ is the ground state of $U _ { t }$ , which is at the same time a unitary and therefore an $( 1 , 0 , 0 )$ - block-encoding of itself. Therefore $U _ { t }$ serves as the $U _ { H }$ in the theorem. The spectral gap is 2. Also, let

$$
| u \rangle = \frac { 1 } { \sqrt { N } } \sum _ { s } | s \rangle
$$

be the uniform superposition of all $n$ -strings, then we have $\begin{array} { r } { \langle u | t \rangle = \frac { 1 } { \sqrt { N } } } \end{array}$ , and $| u \rangle$ can be efficiently prepared by the Hadamard transform since $\mathrm { H } ^ { \otimes n } | 0 ^ { n } \rangle \ : = \ : | u \rangle$ . Therefore $\mathrm { H } ^ { \otimes n }$ serves as the $U _ { I }$ described in the theorem.

If the ground state preparation problem can be solved with $o ( 1 / \gamma )$ queries to √ $U _ { H }$ for fixed $\Delta$ to produce an approximate ground state with fidelity at least √ ${ \sqrt { 3 } } / 2$ , then from the above setup we have $\gamma = 1 / \sqrt { N }$ , and we can first find the approximate ground state and then measure in the computational basis, obtaining $t$ with probability at least $3 / 4$ . Therefore the unstructured search problem can be solved with $o ( \sqrt { N } )$ queries to the oracle $U _ { t }$ , which is impossible. Thus we have proved the first lower bound in our theorem.

To prove the second lower bound we want to create a situation in which the overlap is bounded from below by a constant but the gap vanishes. We need to introduce the Grover diffusion operator

$$
D = I _ { n } - 2 \left| u \right. \left. u \right| .
$$

which can be efficiently implemented. Then we define

$$
H ( \tau ) = ( 1 - \tau ) D + \tau U _ { t } ,
$$

and consider $H ( 1 / 2 )$ . Because both $\operatorname { s p a n } ( \left| u \right. , \left| t \right. )$ and its orthogonal complement are invariant subspaces of $D$ and $U _ { t }$ , and both operators become the identity operator when restricted to the orthogonal complement of $\operatorname { s p a n } ( \left| u \right. , \left| t \right. )$ , we only need to look for the ground state in the 2-dimensional subspace span $( | u \rangle , | t \rangle )$ . In this subspace, relative to the basis $\{ | u \rangle , | t \rangle \}$ , the matrix representation of $H ( 1 / 2 )$ is

$$
\left( \begin{array} { c c } { 0 } & { - \left. u | t \right. } \\ { - \left. t | u \right. } & { 0 } \end{array} \right) = - \frac { 1 } { \sqrt { N } } \left( \begin{array} { l l } { 0 } & { 1 } \\ { 1 } & { 0 } \end{array} \right) .
$$

Therefore the ground state of $H ( 1 / 2 )$ is

$$
| \Psi \rangle = \frac { | u \rangle + | t \rangle } { \sqrt { 2 + \frac { 2 } { \sqrt { N } } } } .
$$

and therefore √ $\langle \Psi | u \rangle = \langle \Psi | t \rangle = 1 / \sqrt { 2 } + \mathcal { O } ( 1 / \sqrt { N } )$ for large $N$ . Furthermore, the gap is $\Delta ( 1 / 2 ) = 2 / \sqrt { N }$ .

Therefore $| t \rangle$ can be prepared in the following way: we first prepare the ground state of $H ( 1 / 2 )$ , whose block-encoding is easy to construct using one application of $U _ { t }$ . The resulting approximate ground state we denote by $| \widetilde { \Psi } \rangle$ . Then we measure $| \tilde { \Psi } \rangle$ in the computational basis. If there is some non-vanishing probability of obtaining $t$ then we can boost the success probability to above $1 / 2$ by repeating the procedure and verifying using $U _ { t }$ .

If the second lower bound in the theorem does not hold, then $| \tilde { \Psi } \rangle$ can be prepared with $o ( 1 / \Delta ( 1 / 2 ) ) = o ( \sqrt { N } )$ queries to the block-encoding of $H ( 1 / 2 )$ and therefore the same number of queries to $U _ { t }$ . Because the angle corresponding to fidelity is the great-circle√ distance on the unit sphere, we have the triangle inequality (using that $| \left. \widetilde { \Psi } | \Psi \right. | \geq \sqrt { 3 } / 2 )$

$$
\operatorname { a r c c o s } | \langle { \widetilde { \Psi } } | t \rangle | \leq \operatorname { a r c c o s } | \langle \Psi | t \rangle | + \operatorname { a r c c o s } | \langle { \widetilde { \Psi } } | \Psi \rangle | \leq { \frac { 5 \pi } { 1 2 } } + { \mathcal { O } } \left( { \frac { 1 } { \sqrt { N } } } \right) .
$$

Therefore for large $N$ we have $| \langle \widetilde { \Psi } | t \rangle | \ge \cos ( 5 \pi / 1 2 ) + \mathcal { O } ( 1 / \sqrt { N } ) > 1 / 4$ . The probability of getting $t$ when performing measurement is at least $1 / 1 6$ . Therefore we can boost the success probability to above $1 / 2$ by $\mathcal { O } ( 1 )$ repetitions and verifications. The total number of queries to $U _ { t }$ is therefore $o ( \sqrt { N } )$ . Again, this is impossible. Therefore we have proved the second lower bound in our theorem.

For the last lower bound we need to create some trade off between the gap and the overlap. We consider preparing the ground state of the Hamiltonian $H ( 1 / 2 - N ^ { - 1 / 2 + \delta } )$ , $0 < \delta < 1 / 6$ , whose block-encoding can be efficiently constructed with a single application of $U _ { t }$ , as an intermediate step. It is shown in Appendix B that the ground state is

$$
\left| \Phi \right. = \left| u \right. + \frac { 1 } { 4 } N ^ { - \delta } \left| t \right. + \mathcal { O } ( N ^ { - 2 \delta } ) .
$$

Therefore

$$
\gamma _ { u } = | \langle \Phi | u \rangle | = 1 + \mathcal { O } ( N ^ { - 2 \delta } ) , \quad \gamma _ { t } = | \langle \Phi | t \rangle | = \frac { 1 } { 4 } N ^ { - \delta } + \mathcal { O } ( N ^ { - 2 \delta } ) .
$$

Also we show in Appendix B that the gap is

$$
\Delta ( 1 / 2 - N ^ { - 1 / 2 + \delta } ) = 4 N ^ { \delta - 1 / 2 } + \mathcal { O } ( N ^ { - 1 / 2 - \delta } ) .
$$

We first apply the algorithm described in Section 3 to prepare the ground state of $H ( 1 / 2 - N ^ { - 1 / 2 + \delta } )$ to fidelity $1 - N ^ { - 2 \partial } / 1 2 8$ . Using the overlap $\gamma _ { u }$ and the gap in (6), the approximate ground state, denoted by $| \widetilde { \Phi } \rangle$ , can be prepared with $\mathcal { O } ( N ^ { 1 / 2 - \delta } \log ( N ) )$ queries to the block-encoding of $H ( 1 / 2 - N ^ { - 1 / 2 + \delta } )$ , and therefore the same number of queries to $U _ { t }$ .

The overlap between $| \widetilde { \Phi } \rangle$ and $| t \rangle$ can again be bounded using the triangle inequality

$$
\begin{array} { r l } & { \operatorname { a r c c o s } | \langle \widetilde { \Phi } | t \rangle | \leq \operatorname { a r c c o s } | \langle \Phi | t \rangle | + \operatorname { a r c c o s } | \langle \widetilde { \Phi } | \Phi \rangle | } \\ & { \qquad \leq \operatorname { a r c c o s } \bigg ( \displaystyle \frac { N ^ { - \delta } } { 4 } \bigg ) + \operatorname { a r c c o s } \bigg ( 1 - \displaystyle \frac { N ^ { - 2 \delta } } { 1 2 8 } \bigg ) + { \mathcal O } ( N ^ { - 2 \delta } ) } \\ & { \qquad \leq \displaystyle \frac { \pi } { 2 } - \displaystyle \frac { N ^ { - \delta } } { 4 } + \sqrt { 2 \times \displaystyle \frac { N ^ { - 2 \delta } } { 1 2 8 } } + { \mathcal O } ( N ^ { - 2 \delta } ) } \\ & { \qquad = \displaystyle \frac { \pi } { 2 } - \displaystyle \frac { N ^ { - \delta } } { 8 } + { \mathcal O } ( N ^ { - 2 \delta } ) . } \end{array}
$$

Therefore we have

$$
\widetilde { \gamma } _ { t } = | \langle \widetilde { \Phi } | t \rangle | \geq \frac { N ^ { - \delta } } { 8 } + { \mathcal O } ( N ^ { - 2 \delta } ) .
$$

If the last lower bound in our theorem does not hold, we can then prepare the ground state of $U _ { t }$ by using the initial state $| \widetilde { \Phi } \rangle$ only $\mathcal { O } ( 1 / \widetilde { \gamma } _ { t } ^ { 1 - \theta } )$ times for some $\theta > 0$ , and the number of queries to $U _ { t }$ at this step, i.e. not including the queries used for preparing $| \widetilde { \Phi } \rangle$ , is $\mathcal { O } ( 1 / \widetilde { \gamma } _ { t } ^ { p } )$ for some $p > 0$ . Therefore the total number of queries to $U _ { t }$ is

$$
\mathcal { O } \left( \frac { N ^ { 1 / 2 - \delta } \log ( N ) } { \widetilde { \gamma } _ { t } ^ { 1 - \theta } } + \frac { 1 } { \widetilde { \gamma } _ { t } ^ { p } } \right) = \mathcal { O } ( N ^ { 1 / 2 - \delta \theta } \log ( N ) + N ^ { \delta p } ) .
$$

This complexity must be $\Omega ( N ^ { 1 / 2 } )$ according to the lower bound for unstructured search problem. Therefore we need $\delta p \ge 1 / 2$ . However we can choose $\delta$ to be arbitrarily small, and no finite $p$ can satisfy this condition. Hence we have a contradiction. This proves the last lower bound in our theorem. □

When we look at the query complexities of the ground state preparation algorithms in Secs. 3 and 4, we can use $\tilde { \mathcal { O } }$ notation to hide the logarithmic factors, and both algorithms use $\tilde { \mathcal { O } } ( \frac { \alpha } { \gamma \Delta } )$ queries to $U _ { H }$ and $\widetilde { \mathcal { O } } ( { \scriptstyle { \frac { 1 } { \gamma } } } )$ queries to $U _ { I }$ when we want to achieve some fixed fidelity. Given the lower bound in Theorem 10 we can see the algorithm with a priori bound for ground energy essentially achieves the optimal dependence on $\gamma$ and $\Delta$ . The algorithm without $a$ priori bound for ground energy achieves the same complexity modulo logarithmic factors, while using less information. This fact guarantees that the dependence is also nearly optimal.

We will then prove the nearly optimal dependence of our ground energy estimation algorithm on the precision $h$ . We have the following theorem:

Theorem 11. Suppose we have a generic Hamiltonian $\begin{array} { r } { H = \sum _ { k } \lambda _ { k } \left| \psi _ { k } \right. \left. \psi _ { k } \right| \in \mathbb { C } ^ { N \times N } } \end{array}$ , where $\lambda _ { k } \ \leq \ \lambda _ { k + 1 }$ , given through its $( \alpha , m , 0 )$ -block-encoding $U _ { H }$ , and $\alpha = \Theta ( 1 )$ . $A l s o$ suppose we have an initial state $| \phi _ { 0 } \rangle$ prepared by circuit $U _ { I }$ , as well as the promise that $| \langle \phi _ { 0 } | \psi _ { 0 } \rangle | = \Omega ( 1 )$ . Then estimating the ground energy to precision $h$ requires $\Omega ( 1 / h )$ queries to $U _ { H }$ .

This time we convert the quantum approximate counting problem, which is closely related to the unstructured search problem, into an eigenvalue problem. The quantum approximate counting problem is defined in the following way. We are given a set of $n$ -bit strings $S \subset \{ 0 , 1 \} ^ { n }$ specified by the oracle $U _ { f }$ satisfying

$$
U _ { f } \left| x \right. = { \left\{ \begin{array} { l l } { - \left| x \right. } & { x \in S , } \\ { \left| x \right. } & { x \not \in S , } \end{array} \right. }
$$

for any $x \in \{ 0 , 1 \} ^ { n }$ . We want to estimate the size $| S | / N$ up to relative error $\epsilon$ . It has been proven that this requires $\Omega \left( \textstyle { \frac { 1 } { \epsilon } } \sqrt { \frac { N } { | S | } } \right)$ queries to $U _ { f }$ for $| S | = o ( N )$ [38, Theorem 1.13], where $N = 2 ^ { n }$ , for the success probability to be greater than $3 / 4$ , and this lower bound can be achieved using amplitude estimation [12].

We convert this problem into an eigenvalue problem of a block-encoded Hamiltonian. Let $| u \rangle$ be the uniform superposition of the computational basis and $D$ be the Grover diffusion operator defined in (3). Then define the following $( n + 1 )$ -qubit unitary ( $\mathrm { H }$ is the Hadamard gate)

$$
U _ { H } = ( \mathrm { H } \otimes I _ { n } ) [ | 0 \rangle \langle 0 | \otimes D - | 1 \rangle \langle 1 | \otimes ( U _ { f } D U _ { f } ) ] ( \mathrm { H } \otimes I _ { n } ) ,
$$

which can be implemented using two applications of controlled- $U _ { f }$ . We define

$$
H = ( \langle 0 | \otimes I _ { n } ) U _ { H } ( | 0 \rangle \otimes I _ { n } ) = \frac { 1 } { 2 } ( D - U _ { f } D U _ { f } ) .
$$

Note that here $H$ is given in its $( 1 , 1 , 0 )$ -block-encoding $U _ { H }$ . Let

$$
\left| u \right. = a \left| u _ { 0 } \right. + \sqrt { 1 - a ^ { 2 } } \left| u _ { 1 } \right.
$$

where the unit vectors $\left| u _ { 0 } \right.$ and $\left| u _ { 1 } \right.$ satisfy

$$
U _ { f } \left| u _ { 0 } \right. = - \left| u _ { 0 } \right. , \quad U _ { f } \left| u _ { 1 } \right. = \left| u _ { 1 } \right. ,
$$

then we find $a = \sqrt { | S | / N }$ . We only need to estimate the value of $a$ to precision $\mathcal { O } ( \epsilon ^ { \prime } \sqrt { N / | S | } )$ in order to estimate $| S | / N$ to precision $\epsilon ^ { \prime }$ .

We analyze the eigenvalues and eigenvectors of $H$ . It can be verified that $\left\{ \left| u _ { 0 } \right. , \left| u _ { 1 } \right. \right\}$ span an invariant subspace of $H$ , and relative to this orthonormal basis $H$ is represented by the matrix

$$
\left( { \begin{array} { c c } { 0 } & { - 2 a { \sqrt { 1 - a ^ { 2 } } } } \\ { - 2 a { \sqrt { 1 - a ^ { 2 } } } } & { 0 } \end{array} } \right) .
$$

In the orthogonal complement of this subspace, $H$ is simply the zero matrix. Therefore $H$ has only two non-zero eigenvalues $\pm 2 a \sqrt { 1 - a ^ { 2 } }$ corresponding to eigenvectors

$$
| \psi _ { \mp } \rangle = \frac { 1 } { \sqrt { 2 } } ( | u _ { 0 } \rangle \mp | u _ { 1 } \rangle ) .
$$

The ground state of $H$ is therefore $| \psi _ { + } \rangle$ with ground energy √ $- 2 a { \sqrt { 1 - a ^ { 2 } } }$ . We can use $| u \rangle$ as the initial state, with an overlap $\begin{array} { r } { \langle \psi _ { + } | u \rangle = \frac { 1 } { \sqrt { 2 } } ( a + \sqrt { 1 - a ^ { 2 } } ) \geq \frac { 1 } { \sqrt { 2 } } } \end{array}$ .

We use this Hamiltonian to prove Theorem 11:

Proof. Assume toward contradiction that there exists an algorithm that estimates the ground energy to precision $h$ using only $o ( 1 / h )$ queries to $U _ { H }$ . Then we use this algorithm to estimate the ground energy of the block-encoded Hamiltonian constructed above, for $a = o ( 1 )$ , which means $| S | = o ( N )$ . Estimating $2 a { \sqrt { 1 - a ^ { 2 } } }$ to precision ${ \mathcal { O } } ( h )$ enables us to estimate $a$ to precision ${ \mathcal { O } } ( h )$ . Setting $h = \epsilon ^ { \prime } \sqrt { N / | S | }$ , then this algorithm can estimate $| S | / N$ to precision $\epsilon ^ { \prime }$ , with success probability at least $3 / 4$ . Since we are interested in the relative error we set $\epsilon ^ { \prime } = \epsilon | S | / N$ . Therefore the whole procedure uses only $o ( 1 / h ) =$ $O \big ( \frac { 1 } { \epsilon } \sqrt { \frac { N } { | S | } } \big )$ queries to $U _ { H }$ and therefore twice the amount of queries to $U _ { f }$ . This contradicts the lower bound for the approximate counting problem in [38].

Remark 12. Theorem 11 can also be viewed as a consequence of the optimality of the quantum phase estimation algorithm [10]. If instead of the block-encoding $U _ { H }$ we have $e ^ { - i \tau H }$ as the oracle for some $\tau$ such that $| \tau | \| H \| \le \pi$ , then even when given the exact ground state of $H$ , [10, Lemma 3] gives a query complexity lower bound $\Omega ( 1 / h )$ for estimating the ground energy to within additive error $h$ . This provides a different proof of the above theorem, since $e ^ { - i \tau H }$ and the block-encoding of $H$ are interconvertible: one can efficiently implement $e ^ { - i \tau H }$ via Hamiltonian simulation starting from a block-encoding of $H$ [34], and can efficiently obtain a block-encoding of $H$ by querying $e ^ { - i \tau H }$ according to [22, Corollary 71].

# 6 Low-energy state preparation

It is known that estimating the spectral gap $\Delta$ is a difficult task [3, 5, 18]. Our algorithm for finding ground energy, as discussed in Theorem 8, does not depend on knowing the spectral gap. However both of our algorithms for preparing the ground state in Theorem 6 and Corollary 9 require a lower bound of the spectral gap. We would like to point out that if we only want to produce a low-energy state $| \psi \rangle$ , making $\langle \psi | H | \psi \rangle \leq \mu$ for some $\mu > \lambda _ { 0 }$ , as in [42], then this can be done without any knowledge of the spectral gap. In fact this is even possible for when the ground state is degenerate.

To do this, we need to first assume we have a normalized initial state $| \phi _ { 0 } \rangle$ with nontrivial overlap with the low-energy eigen-subspaces. Quantitatively this means for some $\gamma , \delta > 0$ , if we expand the initial state in the eigenbasis of $H$ , obtaining $\begin{array} { r } { | \phi _ { 0 } \rangle = \sum _ { k } \alpha _ { k } | \psi _ { k } \rangle } \end{array}$ , then $\begin{array} { r } { \sum _ { k : \lambda _ { k } \leq \mu - 3 \delta } | \alpha _ { k } | ^ { 2 } \geq \gamma ^ { 2 } } \end{array}$ . Then we can use the block-encoded projection operator in (2) to get

$$
| \psi ^ { \prime } \rangle = ( \langle 0 ^ { m + 3 } | \otimes I ) \mathrm { P R O J } ( \mu - 2 \delta , \delta , \epsilon ^ { \prime } ) ( | 0 ^ { m + 3 } \rangle \otimes | \phi _ { 0 } \rangle ) ,
$$

for some precision $\epsilon ^ { \prime }$ . Now we expand $| \psi ^ { \prime } \rangle$ in the eigenbasis to get $\begin{array} { r } { | \psi ^ { \prime } \rangle = \sum _ { k } \beta _ { k } | \psi _ { k } \rangle } \end{array}$ , and denote $\begin{array} { r } { | \varphi ^ { \prime } \rangle = \sum _ { k : \lambda _ { k } < \mu - \delta } \beta _ { k } | \psi _ { k } \rangle } \end{array}$ . We then have, because of the approximation to the sign function,

$$
\parallel | \psi ^ { \prime } \rangle - | \varphi ^ { \prime } \rangle \parallel \leq \frac { \epsilon ^ { \prime } } { 2 } , \quad \langle \varphi ^ { \prime } | \varphi ^ { \prime } \rangle \geq \gamma ^ { 2 } ( 1 - \frac { \epsilon ^ { \prime } } { 2 } ) ^ { 2 } , \quad \langle \varphi ^ { \prime } | H | \varphi ^ { \prime } \rangle \leq \left( \mu - \delta \right) \langle \varphi ^ { \prime } | \varphi ^ { \prime } \rangle .
$$

From the above bounds we further get

$$
\frac { \langle \psi ^ { \prime } | H | \psi ^ { \prime } \rangle } { \langle \psi ^ { \prime } | \psi ^ { \prime } \rangle } \leq \frac { \langle \varphi ^ { \prime } | H | \varphi ^ { \prime } \rangle + \| H \| \epsilon ^ { \prime } + \| H \| \epsilon ^ { \prime 2 } / 4 } { \langle \varphi ^ { \prime } | \varphi ^ { \prime } \rangle - \epsilon ^ { \prime } } \leq \frac { \mu - \delta + \frac { \alpha \epsilon ^ { \prime } + \alpha \epsilon ^ { \prime 2 } / 4 } { \gamma ^ { 2 } ( 1 - \epsilon ^ { \prime } / 2 ) ^ { 2 } } } { 1 - \frac { \epsilon ^ { \prime } } { \gamma ^ { 2 } ( 1 - \epsilon ^ { \prime } / 2 ) ^ { 2 } } } .
$$

Now denoting $\left| \psi \right. = \left| \psi ^ { \prime } \right. / \left| \left| \left| \psi ^ { \prime } \right. \right| \right|$ we can make $\langle \psi | H | \psi \rangle \leq \mu$ by choosing $\epsilon ^ { \prime } = \mathcal { O } ( \gamma ^ { 2 } \delta / \alpha )$ . Therefore the total number of queries to $U _ { H }$ required is $\begin{array} { r } { \mathcal { O } \big ( \frac { 1 } { \delta \gamma } \log \bigl ( \frac { \alpha } { \delta \gamma } \bigr ) \big ) } \end{array}$ and the number of queries to $U _ { I }$ is $\mathcal { O } ( { \textstyle \frac { 1 } { \gamma } } )$ .

From this we can see that if the initial state $| \phi _ { 0 } \rangle$ has a overlap with the the ground state that is at least $\gamma$ , and we want to prepare a state with energy upper bounded by $\lambda _ { 0 } + \delta$ , the required number of queries to $U _ { H }$ and $U _ { I }$ are $\begin{array} { r } { \mathcal { O } ( \frac { 1 } { \delta \gamma } \log ( \frac { \alpha } { \delta \gamma } ) ) } \end{array}$ and $\mathcal { O } ( { \scriptstyle \frac { 1 } { \gamma } } )$ respectively. If we do not know the ground energy beforehand we can use the algorithm in Theorem 8 to estimate it first. Note that none of these procedures assumes a spectral gap.

# 7 Discussions

In this work we proposed an algorithm to prepare the ground state of a given Hamiltonian when a ground energy upper bound is known (Theorem 6), an algorithm to estimate the ground energy based on binary search (Theorem 8), and combining these two to get an algorithm to prepare the ground state without knowing an upper bound a priori (Corollary 9). By solving the unstructured search problem and the approximate counting problem through preparing the ground state, we proved that the query complexities for the tasks above cannot be substantially improved, as otherwise the complexity lower bound for the two problems would be violated.

All our algorithms are based on the availability of the block-encoding of the target Hamiltonian. This is a non-trivial task but we know it can be done for many important settings. For example, Childs et al. proposed an LCU approach to block-encode the Hamiltonian of a quantum spin system [16], in which the Hamiltonian is decomposed into a sum of Pauli matrices. In [35], Low and Wiebe outlined the methods to construct blockencoding of Hubbard Hamiltonian with long-range interaction, and of quantum chemistry Hamiltonian in plane-wave basis, both using fast-fermionic Fourier transform (FFFT) [4]. The FFFT can be replaced by a series of Givens rotations which gives lower circuit depth and better utilizes limited connectivity [26, 30]. Any sparse Hamiltonian whose entries can be efficiently computed can also be block-encoded using a quantum walk operator [7, 9, 15].

We remark that the quantum circuit used in our method for ground energy estimation can be further simplified. The main obstacle to applying this method to near-term devices is the need of amplitude estimation, which requires phase estimation. It is possible to replace amplitude estimation by estimating the success probability classically. In the context of binary amplitude estimation in Lemma 7, we need to determine whether the success amplitude is greater than $3 \gamma / 4$ or smaller than $\gamma / 4$ . This can be turned into a classical hypothesis testing to determine whether the success probability is greater than $9 \gamma ^ { 2 } / 1 6$ or smaller than $\gamma ^ { 2 } / 1 6$ . A simple Chernoff bound argument tells us that we need $\mathcal { O } ( \log ( 1 / \vartheta ) / \gamma ^ { 2 } )$ samples to distinguish the two cases with success probability at least $1 - \vartheta$ , as opposed to the $\mathcal { O } ( \log ( 1 / \vartheta ) / \gamma )$ complexity in amplitude estimation.

In this approach, the only quantum circuit we need to use is the one in (2). The circuit depth is therefore only $\mathcal { O } ( ( \alpha / h ) \log ( 1 / \gamma ) )$ . It also does not require the $\mathcal { O } ( \log ( 1 / \gamma ) )$ qubits that are introduced as a result of using amplitude estimation. These features make it suitable for near-to-intermediate term devices.

In [31] we proposed an eigenstate filtering method (similar in spirit to the method proposed in Section 3), and we combined it with quantum Zeno effect [11, 14] to solve the quantum linear system problem. The resulting algorithm utilizes the fact that the desired eigenstate along the eigenpath always corresponds to the eigenvalue 0. In the setting of quantum Zeno effect based state preparation, in which we have a series of Hamiltonians and wish to incrementally prepare the ground state of each of them, our algorithm in Theorem 6 can be used to go from the ground state of one Hamiltonian to the next one, provided that we have a known upper bound for the ground energy. In the absence of such an upper bound, there is the possibility of using the algorithm in Corollary 9 to solve this problem. However in this setting we only want to use the initial state once for every Hamiltonian, since preparing the initial state involves going through the ground state of all previous Hamiltonians. This presents a challenge and is a topic for our future work.

It is worth pointing out that none of the Hamiltonians used in the proofs of lower bounds in Section 5 is a local Hamiltonian, and therefore our lower bounds do not rule out the possibility that if special properties such as locality are properly taken into consideration, better complexities can be achieved.

# Acknowledgements

This work was partially supported by the Department of Energy under Grant No. DE-SC0017867, the Quantum Algorithm Teams Program under Grant No. DE-AC02-05CH11231, the Google Quantum Research Award (L.L.), and by the Air Force Office of Scientific Research under award number FA9550-18-1-0095 (L.L. and Y.T.). We thank Andr´as Gily´en, and the anonymous referees for helpful suggestions.

# References

[1] D. Aharonov, D. Gottesman, S. Irani, and J. Kempe. The power of quantum systems on a line. Comm. Math. Phys., 287(1):41–65, 2009. DOI: 10.1007/s00220-008-0710-3.   
[2] A. Ambainis. Variable time amplitude amplification and quantum algorithms for linear algebra problems. In STACS’12 (29th Symposium on Theoretical Aspects of Computer Science), volume 14, pages 636–647, 2012.   
[3] A. Ambainis. On physical problems that are slightly more difficult than QMA. In 2014 IEEE 29th Conference on Computational Complexity (CCC), pages 32–43. IEEE, 2014. DOI: 10.1109/CCC.2014.12.   
[4] R. Babbush, N. Wiebe, J. McClean, J. McClain, H. Neven, and G. K.-L. Chan. Low-depth quantum simulation of materials. Phys. Rev. X, 8(1):011044, 2018. DOI: 10.1103/PhysRevX.8.011044.   
[5] J. Bausch, T. Cubitt, A. Lucia, and D. Perez-Garcia. Undecidability of the spectral gap in one dimension. arXiv preprint arXiv:1810.01858, 2018. DOI: 10.1103/Phys-RevX.10.031038.   
[6] C. H. Bennett, E. Bernstein, G. Brassard, and U. Vazirani. Strengths and weaknesses of quantum computing. SIAM J. Comput., 26(5):1510–1523, 1997. DOI: 10.1137/S0097539796300933.   
[7] D. W. Berry and A. M. Childs. Black-box hamiltonian simulation and unitary implementation. arXiv preprint arXiv:0910.4157, 2009.   
[8] D. W. Berry, A. M. Childs, R. Cleve, R. Kothari, and R. D. Somma. Simulating Hamiltonian dynamics with a truncated taylor series. Phys. Rev. Lett., 114(9):090502, 2015. DOI: 10.1103/PhysRevLett.114.090502.   
[9] D. W. Berry, A. M. Childs, and R. Kothari. Hamiltonian simulation with nearly optimal dependence on all parameters. In 2015 IEEE 56th Annual Symposium on Foundations of Computer Science, pages 792–809. IEEE, 2015. DOI: 10.1109/FOCS.2015.54.   
[10] A. J. Bessen. Lower bound for quantum phase estimation. Phys. Rev. A, 71(4): 042313, 2005. DOI: 10.1103/PhysRevA.71.042313.   
[11] S. Boixo, E. Knill, and R. D. Somma. Eigenpath traversal by phase randomization. Quantum Info. Comput., 9:833–855, 2009.   
[12] G. Brassard, P. Hoyer, M. Mosca, and A. Tapp. Quantum amplitude amplification and estimation. Contemp. Math., 305:53–74, 2002. DOI: 10.1090/conm/305/05215.   
[13] R. Chao, D. Ding, A. Gily´en, C. Huang, and M. Szegedy. Finding Angles for Quantum Signal Processing with Machine Precision. 2020.   
[14] A. M. Childs, E. Deotto, E. Farhi, J. Goldstone, S. Gutmann, and A. J. Landahl. Quantum search by measurement. Phys. Rev. A, 66(3):032314, 2002. DOI: 10.1103/PhysRevA.66.032314.   
[15] A. M. Childs, R. Kothari, and R. D. Somma. Quantum algorithm for systems of linear equations with exponentially improved dependence on precision. SIAM J. Comput., 46:1920–1950, 2017. DOI: 10.1137/16M1087072.   
[16] A. M. Childs, D. Maslov, Y. Nam, N. J. Ross, and Y. Su. Toward the first quantum simulation with quantum speedup. Proc. Natl. Acad. Sci, 115(38):9456–9461, 2018. DOI: 10.1073/pnas.1801723115.   
[17] A. M. Childs, Y. Su, M. C. Tran, N. Wiebe, and S. Zhu. A theory of Trotter error. arXiv preprint arXiv:1912.08854, 2019.   
[18] T. S. Cubitt, D. Perez-Garcia, and M. M. Wolf. Undecidability of the spectral gap. Nature, 528(7581):207–211, 2015. DOI: 10.1038/nature16059.   
[19] Y. Dong, X. Meng, K. B. Whaley, and L. Lin. Efficient phase factor evaluation in quantum signal processing. arXiv preprint arXiv:2002.11649, 2020.   
[20] A. Eremenko and P. Yuditskii. Uniform approximation of sgn(x) by polynomials and entire functions. Journal d’Analyse Math´ematique, 101(1):313–324, 2007.   
[21] Y. Ge, J. Tura, and J. I. Cirac. Faster ground state preparation and high-precision ground energy estimation with fewer qubits. J. Math. Phys., 60(2):022202, 2019. DOI: 10.1063/1.5027484.   
[22] A. Gily´en, Y. Su, G. H. Low, and N. Wiebe. Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics. arXiv preprint arXiv:1806.01838, 2018. DOI: 10.1145/3313276.3316366.   
[23] A. Gily´en, Y. Su, G. H. Low, and N. Wiebe. Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics. In Proceedings of the 51st Annual ACM SIGACT Symposium on Theory of Computing, pages 193–204, 2019. DOI: 10.1145/3313276.3316366.   
[24] L. K. Grover. A fast quantum mechanical algorithm for database search. In Proceedings of the twenty-eighth annual ACM symposium on Theory of computing, pages 212–219, 1996. DOI: 10.1145/237814.237866.   
[25] J. Haah. Product decomposition of periodic functions in quantum signal processing. Quantum, 3:190, 2019. DOI: 10.22331/q-2019-10-07-190.   
[26] Z. Jiang, K. J. Sung, K. Kechedzhi, V. N. Smelyanskiy, and S. Boixo. Quantum algorithms to simulate many-body physics of correlated fermions. Phys. Rev. Applied, 9(4):044036, 2018. DOI: 10.1103/PhysRevApplied.9.044036.   
[27] J. Kempe, A. Kitaev, and O. Regev. The complexity of the local Hamiltonian problem. SIAM J. Comput., 35(5):1070–1097, 2006. DOI: 10.1007/978-3-540-30538-5˙31.   
[28] A. Y. Kitaev. Quantum measurements and the abelian stabilizer problem. arXiv preprint quant-ph/9511026, 1995.   
[29] A. Y. Kitaev, A. Shen, and M. N. Vyalyi. Classical and quantum computation. Number 47. American Mathematical Soc., 2002. DOI: 10.1090/gsm/047.   
[30] I. D. Kivlichan, J. McClean, N. Wiebe, C. Gidney, A. Aspuru-Guzik, G. K.-L. Chan, and R. Babbush. Quantum simulation of electronic structure with linear depth and connectivity. Phys. Rev. Lett., 120(11):110501, 2018. DOI: 10.1103/Phys-RevLett.120.110501.   
[31] L. Lin and Y. Tong. Optimal polynomial based quantum eigenstate filtering with application to solving quantum linear systems. Quantum, 4:361, 2020. DOI: 10.22331/q-2020-11-11-361.   
[32] S. Lloyd. Universal quantum simulators. Science, pages 1073–1078, 1996. DOI: 10.1126/science.273.5278.1073.   
[33] G. H. Low and I. L. Chuang. Optimal Hamiltonian simulation by quantum signal processing. Phys. Rev. Lett., 118:010501, 2017. DOI: 10.1103/PhysRevLett.118.010501.   
[34] G. H. Low and I. L. Chuang. Hamiltonian simulation by qubitization. Quantum, 3: 163, 2019. DOI: 10.22331/q-2019-07-12-163.   
[35] G. H. Low and N. Wiebe. Hamiltonian simulation in the interaction picture. arXiv preprint arXiv:1805.00675, 2018.   
[36] G. H. Low, T. J. Yoder, and I. L. Chuang. Methodology of resonant equiangular composite quantum gates. Phys. Rev. X, 6:041067, 2016. DOI: 10.1103/Phys-RevX.6.041067.   
[37] M. Motta, C. Sun, A. T. K. Tan, M. J. O’Rourke, E. Ye, A. J. Minnich, F. G. Brandao, and G. K. Chan. Quantum imaginary time evolution, quantum lanczos, and quantum thermal averaging. arXiv preprint arXiv:1901.07653, 2019.   
[38] A. Nayak and F. Wu. The quantum query complexity of approximating the median and related statistics. In Proceedings of the thirty-first annual ACM symposium on Theory of computing, pages 384–393, 1999. DOI: 10.1145/301250.301349.   
[39] R. Oliveira and B. M. Terhal. The complexity of quantum spin systems on a twodimensional square lattice. arXiv preprint quant-ph/0504050, 2005.   
[40] R. M. Parrish and P. L. McMahon. Quantum filter diagonalization: Quantum eigendecomposition without full quantum phase estimation. arXiv preprint arXiv:1909.08925, 2019.   
[41] A. Peruzzo, J. McClean, P. Shadbolt, M.-H. Yung, X.-Q. Zhou, P. J. Love, A. Aspuru-Guzik, and J. L. O’brien. A variational eigenvalue solver on a photonic quantum processor. Nat. Commun., 5:4213, 2014. DOI: 10.1038/ncomms5213.   
[42] D. Poulin and P. Wocjan. Preparing ground states of quantum many-body systems on a quantum computer. Phys. Rev. Lett., 102(13):130503, 2009. DOI: 10.1103/Phys-RevLett.102.130503.   
[43] E. Remes. Sur le calcul effectif des polynomes d’approximation de tchebichef. C. R. Acad. Sci. Paris, 199:337–340, 1934.   
[44] N. H. Stair, R. Huang, and F. A. Evangelista. A multireference quantum Krylov algorithm for strongly correlated electrons. arXiv preprint arXiv:1911.05163, 2019. DOI: 10.1021/acs.jctc.9b01125.

# A An example of block-encoding and constructing the reflector

In this section we use $\sigma _ { x }$ , $\sigma _ { y }$ , and $\sigma _ { z }$ to denote the three Pauli matrices. We use H to denote the Hadamard gate. We consider a single-qubit illustrative example of blockencoded matrix and obtain the corresponding reflector through QSP.

The matrix we consider is

$$
H ( a ) = a \sigma _ { x } + ( 1 - a ) I ,
$$

for $0 \leq a \leq 1$ . Its block-encoding can be using the following circuit

![](images/e3228a7ebee57002f7160a2f78218e4b76ccbd405d73bda3a21133eecbdbec1a.jpg)

where

$$
V ( a ) = \left( \begin{array} { c c } { { \sqrt { a } } } & { { - \sqrt { 1 - a } } } \\ { { \sqrt { 1 - a } } } & { { \sqrt { a } } } \end{array} \right) .
$$

We denote the above circuit by $U _ { H } ( a )$ . This is a $( \alpha , m , 0 )$ -block-encoding of $H ( a )$ where $\alpha = 1$ and $m = 1$ , since we can readily check that

$$
( \langle 0 | \otimes I ) U _ { H } ( a ) ( | 0 \rangle \otimes I ) = H ( a ) .
$$

The eigendecomposition of $H ( a )$ is

$$
H ( a ) = \left| + \right. \left. + \right| + \left( 1 - 2 a \right) \left| - \right. \left. - \right| ,
$$

with eigenvalues $\lambda _ { + } ( a ) = 1 , \lambda _ { - } ( a ) = 1 - 2 a$ . Our goal is to implement the reflector

$$
R _ { < 0 } ( a ) = - \mathrm { s i g n } ( H ( a ) ) = - \left| + \right. \left. + \right| - \mathrm { s i g n } ( 1 - 2 a ) \left| - \right. \left. - \right| .
$$

To do this we need an odd polynomial $S ( x ; \delta , \epsilon )$ introduced in Lemma 3. Instead of the construction done in Ref. [33] we use the Remez algorithm [43] to obtain this polynomial. We choose $\delta = 0 . 2$ and the $L ^ { \infty }$ error of the residual is required to be less than $1 0 ^ { - 4 }$ , i.e. $\epsilon \leq 1 0 ^ { - 4 }$ .

![](images/26a413d3e56ff32ded58c8e065e2283e766dcf77fae99068e90c6831aea64c86.jpg)  
Figure 1: The circuit implementing the polynomial eigenvalue transformation through QSP for an odd polynomial with phase factors $\{ \varphi _ { j } \} _ { j = 0 } ^ { d }$ . $\mathrm { H }$ is the Hadamard gate and $\sigma _ { z }$ is the Pauli- $Z$ gate.

Given the polynomial $S ( x ; \delta , \epsilon )$ , using the optimization method proposed in Ref. [19], we find a polynomial $P ( x ) \in \mathbb { C } [ x ]$ of odd degree $d$ such that

$$
\operatorname* { m a x } _ { x \in [ - 1 , 1 ] } | \operatorname { R e } P ( x ) - S ( x ; \delta , \epsilon ) | \leq \epsilon ^ { \prime } ,
$$

where $P ( x )$ is characterized by a sequence of phase factors $\{ \varphi _ { j } \} _ { j = 0 } ^ { d }$ satisfying

$$
\left( \begin{array} { c c } { P ( x ) } & { . } \\ { . } & { . } \end{array} \right) = e ^ { i \varphi _ { 0 } \sigma _ { z } } \prod _ { j = 1 } ^ { d } [ R ( x ) e ^ { i \varphi _ { j } \sigma _ { z } } ] ,
$$

where

$$
R ( x ) = \left( \begin{array} { c c } { { x } } & { { \sqrt { 1 - x ^ { 2 } } } } \\ { { \sqrt { 1 - x ^ { 2 } } } } & { { - x } } \end{array} \right) .
$$

The existence of the phase factors is guaranteed by [23, Theorem 5]. Ref. [19] uses quasi-Newton method to solve a least squares problem to obtain these phase factors, and we terminate the iteration only when $L ^ { \infty }$ error of the residual of the real part is smaller than $\epsilon ^ { \prime } = 1 0 ^ { - 4 }$ .

The circuit in Figure 1 with phase factors $\{ \varphi _ { j } \} _ { j = 0 } ^ { d }$ implements the transformation $H / \alpha \mapsto \operatorname { R e } P ( H / \alpha ) \approx S ( H / \alpha ; \delta , \epsilon )$ . The various components of this circuit are explained in detail in [23, Figure 3]. An important component of this circuit is

![](images/c0de898b4e45292361e3cf146507e43ce2e6ea8a15b8b25139d4734a171d7daf.jpg)

where the first register has one qubit, the second register has $m$ -qubits, and the open bullet indicates control-on-zero for multiple control qubits. This component implements the operator

$$
| 0 \rangle  0 | \otimes ( e ^ { i \varphi ( 2 | 0 ^ { m } \rangle \langle 0 ^ { m } | - I ) } ) + | 1 \rangle  1 | \otimes ( e ^ { - i \varphi ( 2 | 0 ^ { m } \rangle \langle 0 ^ { m } | - I ) } ) .
$$

For a detailed discussion see [23, Corollary 11].

![](images/a4c904738f24722c2222f5e56ca989b411c727f96dab2c2f71b03171d4efc8b5.jpg)  
Figure 2: The error of implementing $R _ { < 0 } ( a )$ for $a \in [ 0 , 1 ]$ using QSP, with polynomial $S ( x ; \delta , \epsilon )$ where $\delta = 0 . 2$ and $\epsilon$ is of the order of $1 0 ^ { - 4 }$ . The vertical axis uses logarithmic scale.

Using the above circuit, Lemma 5 guarantees that when the eigenvalues of $H ( a )$ are contained in $[ - 1 , - \delta ] \cup [ \delta , 1 ]$ , we will have a good approximation of $R _ { < 0 } ( a )$ . However when at least one eigenvalue, which in our case can only be $\lambda _ { - } ( a ) = 1 - 2 a$ , is in $( - \delta , \delta )$ , or in other words when $a \in ( 0 . 4 , 0 . 6 )$ , there is no such guarantee. We plot the operator norm error between the approximate reflector obtained through QSP and the exact reflector $R _ { < 0 } ( a )$ in Figure 2. It can be seen in the figure that the error is smaller than $1 0 ^ { - 4 }$ everywhere except for $a \in ( 0 . 4 , 0 . 6 )$ , where the error spikes.

# B Gap and overlap in the unstructured search problem

In this appendix we compute the spectral gap of the Hamiltonian $H ( 1 / 2 - N ^ { - 1 / 2 + \delta } )$ for $H ( \tau )$ defined in (4), $0 < \delta < 1 / 6$ , and the overlap between its ground state and $| u \rangle$ and $| t \rangle$ defined in Section 5.

The first thing we should realize is that we only need to care about the subspace of the Hilbert space spanned by $| u \rangle$ and $| t \rangle$ . In the orthogonal complement of this subspace $H ( \tau )$ is simple a multiple of identity. In this subspace, with respect to the non-orthogonal basis $\{ | u \rangle , | t \rangle \}$ , the operator $H ( 1 / 2 - N ^ { - 1 / 2 + \delta } )$ is represented by the following matrix

$$
N ^ { \delta - 1 / 2 } \left( { - 2 \atop - ( N ^ { - \delta } - 2 N ^ { - 1 / 2 } ) } \right. \left. { - ( N ^ { - \delta } + 2 N ^ { - 1 / 2 } ) } \right) .
$$

Direct calculation shows the eigenvalues are

$$
\lambda _ { \pm } = \pm N ^ { \delta - 1 / 2 } \sqrt { 4 + N ^ { - 2 \delta } - 4 N ^ { - 1 } } = \pm N ^ { \delta - 1 / 2 } ( 2 + \frac { 1 } { 4 } N ^ { - 2 \delta } + \mathcal { O } ( N ^ { - 4 \delta } ) ) .
$$

Thus we obtain the spectral gap in (6). To simplify notation we let $\widetilde { \lambda } = N ^ { 1 / 2 - \delta } \lambda _ { + }$ . We

then compute the ground state. We first find an eigenvector corresponding to $\lambda _ { - }$

$$
\begin{array} { l } { { \displaystyle | \chi \rangle = N ^ { \delta } ( ( N ^ { - \delta } + 2 N ^ { - 1 / 2 } ) | u \rangle + ( - 2 + \widetilde { \lambda } ) | t \rangle ) } } \\ { { \displaystyle ~ = ( 1 + 2 N ^ { \delta - 1 / 2 } ) | u \rangle + ( \frac { 1 } { 4 } N ^ { - \delta } + { \mathcal O } ( N ^ { - 3 \delta } ) ) | t \rangle } } \\ { { \displaystyle ~ = | u \rangle + \frac { 1 } { 4 } N ^ { - \delta } | t \rangle + { \mathcal O } ( N ^ { \delta - 1 / 2 } ) . } } \end{array}
$$

We still need to normalize $| \chi \rangle$ . The normalization factor is

$$
\begin{array} { l } { \displaystyle { | \chi \rangle | = \sqrt { ( 1 + 2 N ^ { \delta - 1 / 2 } ) ^ { 2 } + ( \frac { 1 } { 4 } N ^ { - \delta } + { \mathcal O } ( N ^ { - 3 \delta } ) ) ^ { 2 } + \frac { 2 } { \sqrt { N } } ( 1 + 2 N ^ { \delta - 1 / 2 } ) ( \frac { 1 } { 4 } N ^ { - \delta } + { \mathcal O } ( N ^ { - 3 \delta } ) ) } } } \\ { \displaystyle { = 1 + { \mathcal O } ( N ^ { - 2 \delta } ) . } } \end{array}
$$

Note that the third term under the square root comes from the overlap between $| u \rangle$ and $| t \rangle$ , and it does not play an important role asymptotically. Therefore normalizing we have the expression for the normalized eigenstate (5).