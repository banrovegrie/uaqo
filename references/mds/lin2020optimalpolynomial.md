# Optimal polynomial based quantum eigenstate filtering with application to solving quantum linear systems

Lin Lin1,2 and Yu Tong1

1Department of Mathematics, University of California, Berkeley, CA 94720, USA   
2Computational Research Division, Lawrence Berkeley National Laboratory, Berkeley, CA 94720, USA

We present a quantum eigenstate filtering algorithm based on quantum signal processing (QSP) and minimax polynomials. The algorithm allows us to efficiently prepare a target eigenstate of a given Hamiltonian, if we have access to an initial state with non-trivial overlap with the target eigenstate and have a reasonable lower bound for the spectral gap. We apply this algorithm to the quantum linear system problem (QLSP), and present two algorithms based on quantum adiabatic computing (AQC) and quantum Zeno effect respectively. Both algorithms prepare the final solution as a pure state, and achieves the near optimal ${ \widetilde O } ( d \kappa \log ( 1 / \epsilon ) )$ query complexity for a $d$ -sparse matrix, where $\kappa$ is the condition number, and $\epsilon$ is the desired precision. Neither algorithm uses phase estimation or amplitude amplification.

# 1 Introduction

Eigenvalue problems have a wide range of applications in scientific and engineering computing. Finding ground states and excited states of quantum many-body Hamiltonian operators, Google’s PageRank algorithm, and principle component analysis are just a few prominent examples. Some problems that are not apparently eigenvalue problems may benefit from a reformulation into eigenvalue problems. One noticeable example is the quantum linear systems problem (QLSP), which aims at preparing a state that is proportional to the solution of a given linear system, i.e. $\left| x \right. = { A ^ { - 1 } \left| b \right. } / \left| \left| { A ^ { - 1 } \left| b \right. } \right| \right|$ on a quantum computer ( $\| \cdot \|$ denotes the vector 2-norm). Here $A \in \mathbb { C } ^ { N \times N }$ , and $| b \rangle \in \mathbb { C } ^ { N }$ . We give a more detailed definition of the QLSP in Section 4. All QLSP solvers share the desirable property that the complexity with respect to the matrix dimension can be as low as $\mathcal { O } ( \mathrm { p o l y l o g } ( N ) )$ , which is exponentially faster compared to known classical solvers. Due to the wide applications of linear systems, the efficient solution of QLSP has received significant attention in recent years [5, 14, 16, 17, 21, 34, 38, 56, 61, 62]. By reformulating QLSP into an eigenvalue problem, recent developments have yielded near-optimal query-complexity with respect to $\kappa$ (the condition number of $A$ , defined as the ratio between the largest and the smallest singular value of $A$ , or $\kappa = \| A \| \| A ^ { - 1 } \| ,$ ) [5, 56], which is so far difficult to achieve using alternative methods.

Consider a Hermitian matrix $H \in \mathbb { C } ^ { N \times N }$ , which has a known interior eigenvalue $\lambda$ separated from the rest of the spectrum by a gap (or a lower bound of the gap) denoted by $\Delta$ . Let $P _ { \lambda }$ be the spectral projector associated with the eigenvalue $\lambda$ . The goal of the quantum eigenstate filtering problem is to find a certain smooth function $f ( \cdot )$ , so that $\| f ( H - \lambda I ) - P _ { \lambda } \|$ is as small as possible, and there should be a unitary quantum circuit $U$ that efficiently implements $f ( H - \lambda I )$ . Then given an initial state $\left| x _ { 0 } \right.$ so that $\| P _ { \lambda } \| x _ { 0 } \rangle \| = \gamma > 0$ , $f ( H - \lambda I ) \left| x _ { 0 } \right.$ filters out the unwanted spectral components in $\left| x _ { 0 } \right.$ and is approximately an eigenstate of $H$ corresponding to $\lambda$ . We assume that $H$ can be block-encoded into a unitary matrix $U _ { H }$ [33], which is our input model for $H$ and requires a certain amount of ancilla qubits. The initial state is prepared by an oracle $U _ { x _ { 0 } }$ . In this paper when comparing the number of qubits needed, we focus on the extra ancilla qubits introduced by the various methods used, which exclude the ancilla qubits used in the block-encoding of $H$ .

In this paper, we develop a polynomial-based filtering method, which chooses $f = P _ { \ell }$ to be a $\ell$ -th degree polynomial. We prove that our choice yields the optimal compression ratio among all polynomials. Assume that the information of $H$ can be accessed through its block-encoding. Then we demonstrate that the optimal eigenstate filtering polynomial can be efficiently implemented using the recently developed quantum signal processing (QSP) [34, 43], which allows us to implement a general matrix polynomial with a minimal number of ancilla qubits. More specifically, the query complexity of our method is $\widetilde { \mathcal { O } } ( 1 / ( \gamma \Delta ) \log ( 1 / \epsilon ) )$ for the block-encoding of the Hamiltonian and $\mathcal { O } ( 1 / \gamma )$ for initial state preparation, when using amplitude amplification. The number of extra ancilla qubits is merely 3 when using amplitude amplification, and 2 when we do not (in this case the $1 / \gamma$ factor in both query complexities become $1 / \gamma ^ { 2 }$ ). However in the application to QLSP we can always guarantee $\gamma = \Omega ( 1 )$ , and thus not using amplitude amplification only changes the complexity by a constant factor.

Using the quantum eigenstate filtering algorithm, we present two algorithms to solve QLSP, both achieving a query complexity ${ \widetilde O } ( \kappa \log ( 1 / \epsilon ) )$ , with constant success probability (success is indicated by the outcome of measuring the ancilla qubits). For any $\delta > 0$ , a quantum algorithm that is able to solve a generic QLSP with cost $\mathcal { O } ( \kappa ^ { 1 - \delta } )$ would imply BQP=PSPACE [38]. Therefore our algorithm is near-optimal with respect to $\kappa$ up to a logarithmic factor, and is optimal with respect to $\epsilon$ . The first algorithm (Theorem 8) combines quantum eigenstate filtering with the time-optimal adiabatic quantum computing (AQC) approach [5]. We use the time-optimal AQC to prepare an initial state $\left| x _ { 0 } \right.$ , which achieves a nontrivial overlap with the true solution as $\gamma = | \langle x _ { 0 } | x \rangle | \sim \Omega ( 1 )$ . Then we apply the eigenstate filtering to $\left| x _ { 0 } \right.$ once, and the filtered state is $\epsilon$ -close to $| x \rangle$ upon measurement. The second algorithm (Theorem 11) combines quantum eigenstate filtering with the time-optimal version of the approach based on the quantum Zeno effect (QZE) [12, 56]. Instead of preparing one initial vector satisfying $\gamma \sim \Omega ( 1 )$ , a sequence of quantum eigenstate filtering algorithm are applied to obtain to the instantaneous eigenstate of interest along an eigenpath. The final state is again $\epsilon$ -close to $| x \rangle$ upon measurement. Neither algorithm involves phase estimation or any form of amplitude amplification. The first algorithm achieves slightly better dependence on $\kappa$ than the second algorithm, but this comes at the expense of using a time-dependent Hamiltonian simulation procedure [45] resulting in this algorithm using more ancilla qubits than the second QZE-based algorithm. For both algorithms, because the success is indicated by the outcome of measuring the ancilla qubits, we can repeat the algorithms $\mathcal { O } ( \log ( 1 / \delta ) )$ times to boost the final success probability from $\Omega ( 1 )$ to $1 - \delta$ for arbitrarily small $\delta$ .

# Related works:

A well-known quantum eigenstate filtering algorithm is phase estimation [40], which relies on Hamiltonian simulation [10, 11, 42, 43, 44, 45] and the quantum Fourier transform. We treat the Hamiltonian simulation $e ^ { - \mathrm { i } H \tau }$ with some fixed $\tau$ as an oracle called $U _ { \mathrm { s i m } }$ , where $\tau$ satisfies $\tau \lVert H \rVert < \pi$ . Ref. [30, Appendix B] contains a very detailed analysis of the complexities of using phase estimation together with amplitude amplification. From the analysis in Ref. [30], this approach requires $\mathcal { \tilde { O } } ( 1 / ( \gamma ^ { 2 } \Delta \epsilon ) )$ times of queries for $U _ { \mathrm { s i m } }$ , where $\epsilon$ is the target accuracy (the complexity is the same up to logarithmic factors if we use the block-encoding $U _ { H }$ instead of its time-evolution as an oracle); the number of queries to the circuit $U _ { x _ { 0 } }$ that prepares the initial trial state is $\widetilde { \mathcal { O } } ( 1 / \gamma )$ ; and the number of extra ancilla qubits is $\mathcal { O } ( \log ( 1 / ( \epsilon \Delta ) )$ . This is non-optimal with respect to both $\gamma$ and $\epsilon$ .

Several variants of phase estimation are developed to achieve better dependence on the parameters $\gamma$ and $\epsilon$ [30, 48, 49]. The filtering method developed by Poulin and Wocjan [48] (for a task related to eigenstate filtering) improves the query complexities of $U _ { \mathrm { s i m } }$ and $U _ { x _ { 0 } }$ with respect to $\gamma$ from $\widetilde { \mathcal { O } } ( 1 / \gamma ^ { 2 } )$ to $\widetilde { \mathcal { O } } ( 1 / \gamma )$ . Ge et al. [30, Appendix C] shows that the method by Poulin and Wocjan can be adapted to the ground state preparation problem so that the query complexity of $U _ { \mathrm { s i m } }$ becomes $\widetilde { \mathcal { O } } ( 1 / ( \gamma \Delta ) \log ( 1 / \epsilon ) )$ , while the complexity of $U _ { x _ { 0 } }$ remains $\widetilde { \mathcal { O } } ( 1 / \gamma )$ . The number of extra ancilla qubits is $\mathcal { O } ( \log ( 1 / ( \epsilon \Delta ) )$ . Similar logarithmic dependence on the accuracy in the query complexity has also been achieved in Ref. [49].

Ge et al. [30] also proposed two eigenstate filtering algorithms using linear combination of unitaries (LCU) [11, 21], which uses the Fourier basis and the Chebyshev polynomial basis, respectively. For both methods, the query complexities for $U _ { H }$ and $U _ { x _ { 0 } }$ are $\widetilde { \mathcal { O } } ( 1 / ( \gamma \Delta ) \log ( 1 / \epsilon ) )$ and $\widetilde { \mathcal { O } } ( 1 / \gamma )$ respectively, and the number of extra ancilla qubits can be reduced to $\mathcal { O } ( \log \log ( 1 / \epsilon ) + \log ( 1 / \Delta ) )$ . The $\log \log ( 1 / \epsilon )$ factor comes from the use of LCU. We remark that these methods were developed for finding the ground state, but can be adapted to compute interior eigenstates as well. Our filtering method has the same query complexity up to polylogarithmic factors. The number of extra ancilla qubits is significantly fewer and does not depend on either $\epsilon$ or $\Delta$ , due to the use of QSP. Our method also uses the optimal filtering polynomial, which solves a minimax problem as recorded in Lemma 2. There are several other hybrid quantum-classical algorithms to compute ground state energy and to prepare the ground state [47, 55], whose computational complexities are not yet analyzed and therefore we do not make comparisons here.

For solving QLSP, the query complexity of the original Harrow, Hassidim, and Lloyd (HHL) algorithm [38] scales as $\widetilde { \mathcal { O } } ( \kappa ^ { 2 } / \epsilon )$ , where $\kappa$ is the condition number of $A$ , and $\epsilon$ is the target accuracy. Despite the exponential speedup with respect to the matrix dimension, the scaling with respect to $\kappa$ and $\epsilon$ is significantly weaker compared to that in classical methods. For instance, for positive definite matrices, the complexity of steepest descent (SD) and conjugate gradient (CG) (with respect to both $\kappa$ and $\epsilon$ ) are only ${ \mathcal { O } } ( \kappa \log ( 1 / \epsilon ) )$ and $\mathcal { O } ( \sqrt { \kappa } \log ( 1 / \epsilon ) )$ , respectively [52].

In the past few years, there have been significant progresses towards reducing the preconstants for quantum linear solvers. In particular, the linear combination of unitary (LCU) [11, 21] and quantum signal processing (QSP) or quantum singular value transformation (QSVT) [34, 43] techniques can reduce the query complexity to $\mathcal { O } ( \kappa ^ { 2 } \mathrm { p o l y l o g } ( \kappa / \epsilon ) )$ . Therefore the algorithm is almost optimal with respect to $\epsilon$ , but is still suboptimal with respect to $\kappa$ . The scaling with respect to $\kappa$ can be reduced by the variable-time amplitude amplification (VTAA) [4] technique, and the resulting query complexity for solving QLSP is $\mathcal { O } ( \kappa \mathrm { p o l y l o g } ( \kappa / \epsilon ) ) ,$ ) [17, 21]. However, VTAA requires considerable modification of the LCU or QSP algorithm, and has significant overhead itself. To the extent of our knowledge, the performance of VTAA for solving QLSP has not been quantitatively reported in the literature.

The recently developed randomization method (RM) [56] is the first algorithm that yields near-optimal scaling with respect to $\kappa$ , without using techniques such as VTAA.

<table><tr><td rowspan=1 colspan=1>Algorithm</td><td rowspan=1 colspan=1>Query complexity</td><td rowspan=1 colspan=1>Remark</td></tr><tr><td rowspan=1 colspan=1>HHL [38]</td><td rowspan=1 colspan=1>(κ2/)</td><td rowspan=1 colspan=1>W.VTAA, complexity becomesO(κ/3) [3]</td></tr><tr><td rowspan=1 colspan=1>Linear combination of unitaries(LCU) [17, 21]</td><td rowspan=1 colspan=1>O(κ2 polylog(1/))</td><td rowspan=1 colspan=1>W. VTAA, complexity becomesO(κ polylog(1/))</td></tr><tr><td rowspan=1 colspan=1>Quantum singular value transfor-mation (QSVT) [34]</td><td rowspan=1 colspan=1>O(κ2log(1/))</td><td rowspan=1 colspan=1></td></tr><tr><td rowspan=1 colspan=1>Randomization method (RM) [56]</td><td rowspan=1 colspan=1>(κ/)</td><td rowspan=1 colspan=1>w. repeated phase estimation, com-plexity becomes O(κ polylog(1/e))</td></tr><tr><td rowspan=1 colspan=1>Time-optimal adiabatic quantumcomputing (AQC(exp)) [5]</td><td rowspan=1 colspan=1>O(κpolylog(1/))</td><td rowspan=1 colspan=1>No need for any amplitude amplifi-cation. Use time-dependent Hamil-tonian simulation.</td></tr><tr><td rowspan=1 colspan=1>Eigenstate filtering+AQC (Theo- (κlog(1/))rem 8)</td><td rowspan=1 colspan=1>(k log(1/e))</td><td rowspan=1 colspan=1>No need for any amplitude amplifi-cation.</td></tr><tr><td rowspan=1 colspan=1>Eigenstate filtering+QZE (Theo-rem 11)</td><td rowspan=1 colspan=1>(κlog(1/))</td><td rowspan=1 colspan=1>No need for any amplitude amplifi-cation. Does not rely on any com-plex subroutines.</td></tr></table>

Table 1: The number of queries to the block-encoding of the coefficient matrix $A$ for solving QLSP. Some algorithms were not originally formulated using block-encoding as the input model, but can be converted to use the block-encoding model instead. In the HHL algorithm it is assumed that we have access to time-evolution under the Hermitian coefficient matrix as the Hamiltonian. This assumption can be met when we have the block-encoding of $A$ using Hamiltonian simulation technique that results in small overhead [10, 11, 43, 44, 45]. The LCU method [21] and the gate-based implementation of the RM method [56] both assume oracles to access elements of $A$ . However in both cases the oracles lead to a block-encoding $A$ which can be used in the algorithms. The same can be said of the sparse-access input model in Ref. [17]. Time complexities and gate complexities are converted to query complexities with respect to the oracles in this paper. [32, Thereom 41] gives the implementation of the pseudoinverse using QSVT. This can be used to solve the QLSP by applying this pseudoinverse to the quantum state representing the right-hand side.

RM was inspired by adiabatic quantum computation (AQC) [2, 28, 39], but relies on the quantum Zeno effect. Both RM and AQC reformulate QLSP into an eigenvalue problem. The runtime complexity of RM is ${ \mathcal { O } } ( \kappa \log ( \kappa ) / \epsilon )$ . The recently developed time-optimal AQC(p) and AQC(exp) approaches [5] reduces the runtime complexity to $\mathcal { O } ( \kappa / \epsilon )$ and $\mathcal { O } ( \kappa \mathrm { p o l y l o g } ( \kappa / \epsilon ) )$ , respectively. In particular, AQC(exp) achieves the near-optimal complexity with respect to both $\kappa$ and $\epsilon$ , without relying on any amplification procedure. We also remark that numerical observation indicate that the time complexity of the quantum approximate optimization algorithm (QAOA) [29] can be as low as $\mathcal { O } ( \kappa \mathrm { p o l y l o g } ( 1 / \epsilon ) )$ [5]. The direct analysis of the complexity of QAOA without relying on the complexity of adiabatic computing (such as AQC(exp)) remains an open question. We demonstrate that quantum eigenstate filtering provides a more versatile approach to obtain the near optimal complexity for solving QLSP. In particular, it can be used to reduce the complexity with respect to $\epsilon$ for both adiabatic computing and quantum Zeno effect based methods. In Table 1 we compare these aforementioned algorithms in terms of the number of queries to the block-encoding of $A$ . We note that these algorithms rely on different input models but they can all be slightly modified to use the block-encoding assumed in this work.

Recently quantum-inspired classical algorithms based on $\ell ^ { 2 }$ -norm sampling assumptions [58, 59] have been developed that are only up to polynomially slower than the corresponding quantum algorithms. Similar techniques have been applied to solve low-rank linear systems [19, 31], which achieve exponential speedup in the dependence on the problem size compared to the traditional classical algorithms for the same problem. However, it is unclear whether the classical $\ell ^ { 2 }$ -norm sampling can be done efficiently without access to a quantum computer in the setting of this work. The quantum-inspired classical algorithms also suffer from many practical issues making their application limited to highly specialized problems [8]. Most importantly, the assumption of low-rankness is crucial in these algorithms. Our work is based on the block-encoding model, which could be used to efficiently represent low-rank as well as full-rank matrices on a quantum computer.

Notations: In this paper we use the following asymptotic notations besides the usual $\mathcal { O }$ notation: we write $f = \Omega ( g )$ if $g = \mathcal { O } ( f )$ ; $f = \Theta ( g )$ if $f = \mathcal { O } ( g )$ and $g = \mathcal { O } ( f )$ ; $f = { \widetilde { \cal O } } ( g )$ if $f = \mathcal { O } ( g \mathrm { p o l y l o g } ( g ) )$ .

We use $\| \cdot \|$ to denote vector or matrix 2-norm: when $\boldsymbol { v }$ is a vector we denote by $\lVert v \rVert$ its 2-norm, and when $A$ is matrix we denote by $\| A \|$ its operator norm. For two quantum states $| x \rangle$ and $| y \rangle$ , we sometimes write $| x , y \rangle$ to denote $\left| x \right. \left| y \right.$ . We use fidelity to measure how close to each other two quantum states are. Note there are two common definitions for the fidelity between two pure states $| \phi \rangle$ and $| \varphi \rangle$ : it is either $\mid \langle \phi | \varphi \rangle \mid$ or $\mid \langle \phi \mid \varphi \rangle \mid ^ { 2 }$ . Throughout the paper we use the former definition.

Organization: The rest of the paper is organized as follows. In Section 2 we briefly review block-encoding and QSP, as well as using QSP to directly solve QLSP with a non-optimal complexity. In Section 3 we introduce the minimax polynomial we are using and our eigenstate filtering method based on it. In Section 4 we combine eigenstate filtering with AQC to solve the QLSP. In Section 5 we present another method to solve the QLSP using QZE and eigenstate filtering. In Section 6 we discuss some practical aspects of our algorithms and future work.

# 2 Block-encoding and quantum signal processing

For simplicity we assume $N \ : = \ : 2 ^ { n }$ . An $( m + n )$ -qubit unitary operator $U$ is called an $( \alpha , m , \epsilon )$ -block-encoding of an $n$ -qubit operator $A$ , if

$$
\| A - \alpha ( \langle 0 ^ { m } | \otimes I ) U ( | 0 ^ { m } \rangle \otimes I ) \| \le \epsilon .
$$

Another way to express Eq. (1) is

$$
U = \left( \begin{array} { c c } { { \widetilde { A } / \alpha } } & { { * } } \\ { { * } } & { { * } } \end{array} \right) ,
$$

where $^ *$ can be any block matrices of the correct size and $\| \tilde { A } - A \| \leq \epsilon$ . For instance, when $m = 1$ , $\tilde { A } / \alpha$ is an $n$ -qubit matrix at the upper-left diagonal block of the $( n + 1 )$ -qubit unitary matrix $U$ . Note that the fact $\tilde { A } / \alpha$ is the upper-left block of a unitary matrix implies $\| \tilde { A } / \alpha \| \le \| U \| = 1$ . Therefore $\| { \tilde { A } } \| \leq \alpha$ . Many matrices used in practice can be efficiently block-encoded. For instance, if all entries of $A$ satisfies $| A _ { i j } | \le 1$ , and $A$ is Hermitian and $d$ -sparse (i.e. each row / column of $A$ has no more than $d$ nonzero entries), then $A$ has a $( d , n + 2 , 0 )$ -encoding $U$ . See [21, Section 4.1] and [11, Lemma 10] for details, as well as [32, Lemma 48] for a more general treatment of sparse matrices.

With a block-encoding available, QSP allows us to construct a block-encoding for an arbitrary polynomial eigenvalue transformation of $A$ .

Theorem 1. (Polynomial eigenvalue transformation via quantum signal processing1 [34, Theorem 31]): Let $U$ be an $( \alpha , m , \epsilon )$ -block-encoding of a Hermitian matrix $A$ . Let $P \in \mathbb { R } [ x ]$ be a degree- $\ell$ real polynomial and $| P ( x ) | \le 1 / 2$ for any $x \in [ - 1 , 1 ]$ . Then there exists $a$ $( 1 , m + 2 , 4 \ell \sqrt { \epsilon } / \alpha )$ -block-encoding $\widetilde { U }$ of $P ( A / \alpha )$ using $\ell$ queries of $U , U ^ { \dag }$ , and $\mathcal { O } ( ( m + 1 ) \ell )$ other primitive quantum gates.

We remark that Theorem 1 does not meet all our needs because of the constraint $| P ( x ) | \le 1 / 2$ . This requirement comes from decomposing the polynomial into the sum of an even and an odd polynomial and then summing them up. When $P ( x )$ naturally has a parity this requirement becomes redundant. This enables us to get rid of 1 ancilla qubit. Also for simplicity we assume the block-encoding of $A$ is exact. Therefore we have the following theorem, which can be proved directly from [34, Theorem 2 and Corollary 11].

Theorem 1’. (Polynomial eigenvalue transformation with definite parity via quantum signal processing) Let $U$ be an $( \alpha , m , 0 )$ -block-encoding of a Hermitian matrix $A$ . Let $P \in \mathbb { R } [ x ]$ be a degree- $\ell$ even or odd real polynomial and $| P ( x ) | \le 1$ for any $x \in [ - 1 , 1 ]$ . Then there exists a $( 1 , m + 1 , 0 )$ -block-encoding $\widetilde { U }$ of $P ( A / \alpha )$ using $\ell$ queries of $U$ , $U ^ { \dagger }$ , and $\mathcal { O } ( ( m + 1 ) \ell )$ other primitive quantum gates.

Compared to methods such as LCU, one distinct advantage of QSP is that the number of extra ancilla qubits needed is only 1 as shown in Theorem $1 ^ { \prime }$ . Hence QSP may be possibly carried out efficiently on intermediate-term devices. Furthermore, a polynomial can be expanded into different basis functions as $\begin{array} { r } { P ( x ) = \sum _ { k = 0 } ^ { \ell } c _ { k } f _ { k } ( x ) } \end{array}$ , where $f _ { k }$ can be the monomial $x ^ { k }$ , the Chebyshev polynomial $T _ { k } ( x )$ , or any other polynomial. The performance of LCU crucially depends on the 1-norm $\begin{array} { r } { \| c \| _ { 1 } = \sum _ { k \equiv 0 } ^ { \ell } \left| c _ { k } \right| } \end{array}$ , which can be very different depending on the expansion [21]. The block encoding $U$ in QSP is independent of such a choice, and therefore provides a more intrinsic representation of matrix function. We also remark that in QSP, the construction of the block-encoding $\widetilde { U }$ involves a sequence of parameters called phase factors. For a given polynomial $P ( x )$ , the computation of the phase factors can be efficiently performed on classical computers [32, 37]. There are however difficulties in computing such phase factors, which will be discussed in Section 6. For simplicity we assume that the phase factors are given and computed without error.

As an example, we demonstrate how to use QSP to solve QLSP with a Hermitian coefficient matrix $A$ , given by its $( \alpha , m , 0 )$ -block-encoding $U _ { A }$ . We assume that $A , b$ are normalized as

$$
\| A \| = 1 , \quad \langle b | b \rangle = 1 .
$$

We also assume $A$ is Hermitian, and therefore all the eigenvalues of $A$ are real. General matrices can be treated using the standard matrix dilation method (see Appendix D). Due to the normalization condition, the block-encoding factor satisfies $\alpha \geq \| A \| = 1$ . Furthermore, since $\kappa = \| A \| \| A ^ { - 1 } \| = \| A ^ { - 1 } \|$ , the smallest singular value of $A$ is $1 / \kappa$ . Hence the eigenvalues of $A / \alpha$ are contained in the set $[ - 1 / \alpha , - 1 / ( \alpha \kappa ) ] \cup [ 1 / ( \alpha \kappa ) , 1 / \alpha ] \subseteq \mathcal { D } _ { 1 / ( \alpha \kappa ) }$ , where

$$
\begin{array} { r } { \mathcal { D } _ { \delta } : = [ - 1 , - \delta ] \cup [ \delta , 1 ] . } \end{array}
$$

Later we will keep using this notation $\mathcal { D } _ { \delta }$ to denote sets of this type. We first find a polynomial $P ( x )$ satisfying $| P ( x ) | \leq 1$ for any $x \in [ - 1 , 1 ]$ , and $| P ( x ) - 1 / ( c x ) | \le \epsilon ^ { \prime }$ on ${ \mathcal { D } } _ { 1 / ( \alpha \kappa ) }$ for $c = 4 \alpha \kappa / 3$ . Note that $\epsilon ^ { \prime }$ is the accuracy of the polynomial approximation, so that the unnormalized state $P ( A / \alpha ) \left| b \right.$ would differ from the desired $\left( \alpha / c \right) A ^ { - 1 } \left| b \right.$ by $\epsilon ^ { \prime }$ . In order to obtain a normalized solution $P ( A / \alpha ) \left| b \right. / \| P ( A / \alpha ) \left| b \right. \|$ that is $\epsilon$ -close to the normalized solution $\left| x \right. = A ^ { - 1 } \left| b \right. / \left| \left| A ^ { - 1 } \left| b \right. \right| \right|$ , we first note that $\| A ^ { - 1 } \| b \rangle \| \ge 1$ . So the normalization would amplify the error by a factor of approximately $c / ( \alpha \lVert A ^ { - 1 } | b \rangle \parallel ) \le 4 \kappa / 3$ . Therefore we may choose $\epsilon ^ { \prime } = 3 \epsilon / 4 \kappa$ . Then we can find an odd polynomial of degree ${ \mathcal { O } } ( \alpha \kappa \log ( \kappa / \epsilon ) )$ , where $\epsilon$ is the desired precision, satisfying this by [32, Corollary 69]. Then by Theorem $1 ^ { \prime }$ we have a circuit $\widetilde { U }$ satisfying

$$
\begin{array} { r } { \widetilde { U } \left| 0 ^ { m + 1 } \right. \left| b \right. = \left| 0 ^ { m + 1 } \right. \left( P ( A / \alpha ) \left| b \right. \right) + \left| \phi \right. } \\ { \approx \left| 0 ^ { m + 1 } \right. \left( \frac { \alpha } { c } A ^ { - 1 } \left| b \right. \right) + \left| \phi \right. , } \end{array}
$$

where $| \phi \rangle$ is orthogonal to all states of the form $\left| 0 ^ { m + 1 } \right. \left| \psi \right.$ . Measuring the ancilla qubits, we obtain the a normalized quantum state $P ( A / \alpha ) \left| b \right. / \| P ( A / \alpha ) \left| b \right. \|$ that is $\epsilon$ -close to the normalized solution $| x \rangle$ with probability $\Theta ( ( \frac { \alpha } { c } \| A ^ { - 1 } | b  | | ) ^ { 2 } )$ .

As $\| A ^ { - 1 } | b \rangle \| \geq 1$ , the probability of success is $\Omega ( 1 / \kappa ^ { 2 } )$ . Using amplitude amplification [13], the number of repetitions needed for success can be improved to ${ \mathcal { O } } ( \kappa )$ . Furthermore, the query complexity of application of $\widetilde { U }$ is ${ \mathcal { O } } ( \alpha \kappa \log ( \kappa / \epsilon ) )$ . Therefore the overall query complexity is $\mathcal { O } ( \alpha \kappa ^ { 2 } \log ( \kappa / \epsilon ) )$ .

We observe that the quadratic scaling with respect to $\kappa$ is very much attached to the procedure above: each application of QSP costs ${ \mathcal { O } } ( \kappa )$ queries of $U , U ^ { \dag }$ , and the other from that QSP needs to be performed for ${ \mathcal { O } } ( \kappa )$ times. The same argument applies to other techniques such as LCU. To reduce the $\kappa$ complexity along this line, one must modify the procedure substantially to avoid the multiplication of the two $\kappa$ factors, such as using the modified LCU based on VTAA [21].

# 3 Eigenstate filtering using a minimax polynomial

Now consider a Hermitian matrix $H$ , with a known eigenvalue $\lambda$ that is separated from other eigenvalues by a gap $\Delta$ . $H$ is assumed to have an $( \alpha , m , 0 )$ -block-encoding denoted by $U _ { H }$ . We want to preserve the $\lambda$ -eigenstate while filtering out all other eigenstates. Let $P _ { \lambda }$ denote the projection operator into the $\lambda$ -eigenspace of $H$ . The basic idea is, suppose we have a polynomial $P$ such that $P ( 0 ) = 1$ and $| P ( x ) |$ is small for $x \in \mathcal { D } _ { \Delta / ( 2 \alpha ) }$ , where we use the notation $\mathcal { D } _ { \delta } = [ - 1 , - \delta ] \cup [ \delta , 1 ]$ that has been introduced earlier, then $P ( ( H - \lambda I ) / ( \alpha + | \lambda | ) ) \approx P _ { \lambda }$ . This is the essence of the algorithm we are going to introduce below. The reason we need to introduce the factors $2 \alpha$ and $\alpha + | \lambda |$ is that the block-encoding of $H - \lambda I$ will involve a factor $\alpha + | \lambda |$ , and this is explained in detail in Appendix A. Since $| \lambda | \leq \alpha$ by definition of the operator norm, we have $\alpha + | \lambda | \leq 2 \alpha$ . Therefore when $\lambda$ is separated from the rest of the spectrum of $H$ by a gap $\Delta$ , $0$ is separated from the rest of the spectrum of $( H - \lambda I ) / ( \alpha + | \lambda | )$ by a gap $\Delta / ( \alpha + | \lambda | ) \geq \Delta / ( 2 \alpha ) = \widetilde \Delta$ .

We use the following $2 \ell$ -degree polynomial

$$
R _ { \ell } ( x ; \Delta ) = \frac { T _ { \ell } \left( - 1 + 2 \frac { x ^ { 2 } - \Delta ^ { 2 } } { 1 - \Delta ^ { 2 } } \right) } { T _ { \ell } \left( - 1 + 2 \frac { - \Delta ^ { 2 } } { 1 - \Delta ^ { 2 } } \right) } ,
$$

where $T _ { \ell } ( x )$ is the $\ell$ -th Chebysehv polynomial of the first kind. This polynomial is inspired by the shifted and rescaled Chebyshev polynomial discussed in [52, Theorem 6.25]. A plot of the polynomial is given in Fig. 1. $R _ { \ell } ( x ; \Delta )$ has several nice properties:

Lemma 2. (i) $R _ { \ell } ( x ; \Delta )$ solves the minimax problem

$$
\underset { p ( x ) \in \mathbb { P } _ { 2 \ell } [ x ] , p ( 0 ) = 1 } { \mathrm { m i n i m i z e ~ } } \underset { x \in \mathcal { D } _ { \Delta } } { \mathrm { m a x ~ } } | p ( x ) | .
$$

(ii) $| R _ { \ell } ( x ; \Delta ) | \leq 2 e ^ { - \sqrt { 2 } \ell \Delta }$ for al l $x \in \mathcal { D } _ { \Delta }$ and $0 < \Delta \leq 1 / \sqrt { 1 2 }$ . Also $R _ { \ell } ( 0 ; \Delta ) = 1$ (iii) $| R _ { \ell } ( x ; \Delta ) | \le 1$ for al l $| x | \le 1$ .

![](images/4ce8e385f2e86236d2d5e478c17778cffa871c2d71d8264b1576cecdbad336dd.jpg)  
Figure 1: The polynomial $R _ { \ell } ( x , \Delta )$ for $\ell = 1 6$ and 30, $\Delta = 0 . 1$ .

A proof of the above lemma is provided in Appendix E. If we apply this polynomial to $H - \lambda I$ , Lemma 2 (i) states that $R _ { \ell }$ achieves the best compression ratio of the unwanted components, among all polynomials of degrees up to $2 \ell$ . To prepare a quantum circuit, we define $\tilde { H } = ( H { - } \lambda I ) / ( \alpha { + } | \lambda | )$ . Then we can also construct a $( 1 , m + 1 , 0 )$ -block-encoding for $\tilde { H }$ (see Appendix A). The gap separating 0 from other eigenvalues of $\tilde { H }$ is lower bounded by $\tilde { \Delta } = \Delta / 2 \alpha$ , as explained at the beginning of this section. Together with the fact that $\| \dot { H } \| \leq 1$ , we find that the spectrum of $\tilde { H }$ is contained in $\mathcal { D } _ { \widetilde { \Delta } } \cup \{ 0 \}$ .

eWe then apply Lemma 2. Note that the requirement when $\tilde { \Delta } > 1 / \sqrt { 1 2 }$ might not be satisfied, we can always set $\tilde { \Delta } = 1 / \sqrt { 1 2 }$ and this does not affect the asymptotic complexity as $\widetilde { \Delta }  0$ . Because of (ii) of Lemma 2, we have

$$
\begin{array} { r } { \| R _ { \ell } ( \widetilde { H } , \widetilde { \Delta } ) - P _ { \lambda } \| \leq 2 e ^ { - \sqrt { 2 } \ell \widetilde { \Delta } } . } \end{array}
$$

Also because of (iii), and the fact that $R _ { \ell } ( x ; \tilde { \Delta } )$ is even, we may apply Theorem $1 ^ { \prime }$ to implement $R \ell ( \widetilde { H } ; \widetilde { \Delta } )$ using QSP. This gives the following theorem:

Theorem 3. (Eigenstate filtering): Let $H$ be a Hermitian matrix and $U _ { H }$ is an $( \alpha , m , 0 )$ -block-encoding of $H$ . If $\lambda$ is an eigenvalue of $H$ that is separated from the rest of the spectrum by a gap $\Delta$ , then we can construct a $( 1 , m + 2 , \epsilon )$ -block-encoding of $P _ { \lambda }$ , by $\mathcal { O } ( ( \alpha / \Delta ) \log ( 1 / \epsilon ) )$ applications of (controlled-) $U _ { H }$ and $U _ { H } ^ { \dagger }$ , and $\mathcal { O } ( ( m \alpha / \Delta ) \log ( 1 / \epsilon ) )$ other primitive quantum gates.

Suppose we can prepare a state $| \psi \rangle = \gamma | \psi _ { \lambda } \rangle + | \bot \rangle$ using an oracle $O _ { \psi }$ , where $| \psi _ { \lambda } \rangle$ is a $\lambda$ -eigenvector and $\langle \psi _ { \lambda } | \perp \rangle = 0$ , for some $0 < \gamma \leq 1$ . Theorem 3 states that we can get an $\epsilon$ -approximation to $| \psi _ { \lambda } \rangle$ with $\mathcal { O } ( ( \alpha / \Delta ) \log ( 1 / ( \gamma \epsilon ) ) )$ queries to $U _ { H }$ , with a successful application of the block-encoding of $P _ { \lambda }$ , denoted by $U _ { P _ { \lambda } }$ . The fact we have $1 / ( \gamma \epsilon )$ instead of $1 / \epsilon$ in the logarithm is due to the error amplification going from an unnormalized state to a normalized state, similar to that discussed in the application of QSP to QLSP in

Section 2. The probability of applying this block-encoding successfully, i.e. getting all $0$ ’s when measuring ancilla qubits, is at least $\gamma ^ { 2 }$ . Therefore when $| \psi \rangle$ can be repeatedly prepared by an oracle, we only need to run $U _ { P _ { \lambda } }$ and the oracle on average $\mathcal { O } ( 1 / \gamma ^ { 2 } )$ times to obtain $| \psi _ { \lambda } \rangle$ successfully. With amplitude amplification we can reduce this number to $\mathcal { O } ( 1 / \gamma )$ . However this is not necessary when $\gamma = \Omega ( 1 )$ , when without using amplitude amplification we can already obtain $| \psi _ { \lambda } \rangle$ by using the oracle for initial state and $U _ { P _ { \lambda } }$ $\mathcal { O } ( 1 )$ times.

We remark that the eigenstate filtering procedure can also be implemented by alternative methods such as LCU. The polynomial $R _ { \ell } ( \cdot , \tilde { \Delta } )$ can be expanded exactly into a linear combination of the first $2 \ell + 1$ Chebyshev polynomials. The 1-norm of the expansion coefficients is upper bounded by $2 \ell + 2$ because $| R _ { \ell } ( x , \tilde { \Delta } ) | \leq 1$ . However, this comes at the expense of additional $\mathcal { O } ( \log \ell )$ qubits needed for the LCU expansion [21].

Besides the projection operator, we can use this filtering procedure to implement many other related operators. First we consider implementing the reflection operator about the target $\lambda$ -eigenstate (or $\lambda$ -eigenspace if there is degeneracy), $2 P _ { \lambda } - I$ , which is useful in the amplitude amplification procedure [13, 35]. This problem has been considered in Ref. [22].

For a given Hamiltonian $H$ , with the same assumptions as in Theorem 3, and $\tilde { H } =$ $( H - \lambda I ) / ( \alpha + | \lambda | )$ as constructed above, we define

$$
R _ { \lambda } = 2 P _ { \lambda } - I ,
$$

where $P _ { \lambda }$ is the projection operator into the $\lambda$ -eigenspace of $H$ . Using a polynomial $S _ { \ell } ( x ; \Delta )$ constructed from $R _ { \ell } ( x ; \Delta )$ as introduced in Appendix B, we can implement the reflection operator $R _ { \lambda }$ through QSP. The cost is summarized as follows:

Theorem 4. Under the same assumption as Theorem $\boldsymbol { \mathcal { J } }$ , a $( 1 , m + 2 , \epsilon )$ -block-encoding of $R _ { \lambda }$ , the reflection operator about the $\lambda$ -eigenspace of $H$ , can be constructed using $\mathcal { O } ( ( \alpha / \Delta ) \log ( 1 / \epsilon ) )$ applications of (controlled-) $U _ { H }$ and $U _ { H } ^ { \dagger }$ , and $\mathcal { O } ( ( m \alpha / \Delta ) \log ( 1 / \epsilon ) )$ other primitive quantum gates.

For the proof see Appendix B. This reflection operator further enables us to construct a block-encoding of the $\theta$ -reflection operator.

$$
P _ { \lambda } + e ^ { \mathrm { i } \theta } ( I - P _ { \lambda } ) .
$$

This operator is useful in fixed-point amplitude amplification [36, 63]. The cost is summarized as follows:

Corollary 5. Under the same assumption as Theorem $\mathcal { J }$ , a $( 1 , m + 3 , \epsilon )$ -block-encoding of $P _ { \lambda } + e ^ { \mathrm { i } \theta } ( I - P _ { \lambda } )$ , where $P _ { \lambda }$ is the projection operator into the $\lambda$ -eigenspace of $H$ , can be constructed using $\mathcal { O } ( ( \alpha / \Delta ) \log ( 1 / \epsilon ) )$ applications of (controlled-) $U _ { H }$ and $U _ { H } ^ { \dagger }$ , and $\mathcal { O } ( ( m \alpha / \Delta ) \log ( 1 / \epsilon ) )$ other primitive quantum gates.

The proof can be found in Appendix B.

In this paper we focus on obtaining the eigenstate corresponding to an eigenvalue that is known exactly. If instead of a single known eigenvalue, we want keep all eigenvalues in a certain interval, and filter out the rest, we can use a linear combination of polynomials used to approximate the sign function [34, Lemma 14], together with constant shift. The filtering polynomial for this kind of task can also be obtained numerically through Remez algorithm [51], followed by a optimization based procedure to efficiently identify the phase factors. For more details we refer readers to Ref. [23].

Remark 6. In the special case where $\| H \| = 1$ , the target eigenvalue is 1, and we have access to a $( 1 , m , 0 )$ -block-encoding of $H$ , then a quadratically improved dependence on the gap can be achieved using polynomials such as [52, Eq. (6.113)]. This is useful for obtaining the stationary distribution of an ergodic and reversible Markov chain because the discriminant matrix [6, 7, 57] can be block-encoded efficiently in a reflection operator, and its 1-eigenstate is $\Sigma _ { j } \sqrt { \pi _ { j } } \left| j \right.$ where $\pi = ( \pi _ { j } )$ is the stationary distribution.

# 4 Solving QLSP: eigenstate filtering with adiabatic quantum computing

To define QLSP, we assume that a $d$ -sparse matrix $A$ can be accessed by oracles $O _ { A , 1 }$ , $O _ { A , 2 }$ as

$$
O _ { A , 1 } | j , l \rangle = | j , \nu ( j , l ) \rangle , \quad O _ { A , 2 } | j , k , z \rangle = | j , k , A _ { j k } \oplus z \rangle ,
$$

where $j , k , l , z \in [ N ]$ , and $\nu ( j , l )$ is the row index of the $l$ -th nonzero element in the $j$ -th column. The right hand side vector $| b \rangle$ can be prepared with an oracle $O _ { B }$ as

$$
O _ { B } \left| 0 \right. = \left| b \right. .
$$

This is the same as the assumption used in [21, 56]. The oracles can be used to construct a $( d , n + 2 , 0 )$ -block-encoding of $A$ [11, 21].

We assume the singular values of $A$ are contained in $[ 1 / \kappa , 1 ]$ for some $\kappa > 1$ . Therefore $\kappa$ here is an upper bound for the condition number, which is defined as the ratio between the largest and the smallest singular values. It is thus guaranteed that when $A$ is Hermitian its eigenvalues are contained in $\mathcal { D } _ { 1 / \kappa } = [ - 1 , - 1 / \kappa ] \cup [ 1 / \kappa , 1 ]$ . In Ref. [21] it is assumed that that $\| A \| = 1$ and the condition number is exactly $\kappa$ [21, Problem 1], which is slightly stronger than the assumption we are currently using.

Remark 7. We can always assume without loss of generality that $A$ is Hermitian. Because when $A$ is not Hermitian we can solve an extended linear system as described in Appendix $D$ , where the coefficient matrix is

$$
\left( \begin{array} { l l } { 0 } & { A } \\ { A ^ { \dagger } } & { 0 } \end{array} \right)
$$

This is a Hermitian matrix, and when $A$ is $d$ -sparse, this matrix is $d$ -sparse as well. If $A$ has singular values $\left\{ \sigma _ { k } \right\}$ , then the dilated Hermitian matrix has real eigenvalues $\{ \pm \sigma _ { k } \}$ . Therefore the two matrices have the same condition number, and when the singular values of $A$ are contained in $[ 1 / \kappa , 1 ]$ the spectrum of the above dilated matrix is contained in $[ - 1 , - 1 / \kappa ] \cup [ 1 / \kappa , 1 ]$ .

We will then apply the method we developed in the last section to QLSP. To do this we need to convert QLSP into an eigenvalue problem. For simplicity we assume $A$ is Hermitian positive-definite. The indefinite case is addressed in Appendix D, which uses different Hamiltonians but only requires minor modifications. We define

$$
H _ { 1 } = \left( \begin{array} { c c } { { 0 } } & { { A Q _ { b } } } \\ { { Q _ { b } A } } & { { 0 } } \end{array} \right) = \left. 0 \right. \left. 1 \right. \otimes A Q _ { b } + \left. 1 \right. \left. 0 \right. \otimes Q _ { b } A ,
$$

where $Q _ { b } = I - \left| b \right. \left. b \right|$ . This Hamiltonian has been used in Refs. [5, 56]. As discussed in Appendix A, we can construct a $( d , n + 4 , 0 )$ -block-encoding of $H _ { 1 }$ , denoted by $U _ { H _ { 1 } }$ by applying $O _ { B } , O _ { A , 1 } , O _ { A , 2 }$ twice.

We may readily verify that the 0-eigenspace, i.e. the null space, of $H _ { 1 }$ is spanned by $\left| 0 \right. \left| x \right. = ( x , 0 ) ^ { \top }$ , where $| x \rangle$ is the solution, i.e. $A \left| x \right. \propto \left| b \right.$ , and $\left| 1 \right. \left| b \right. = ( 0 , b ) ^ { \top }$ , by considering the null space of $H _ { 1 } ^ { 2 }$ . The rest of the spectrum is separated from 0 by a gap of $1 / \kappa$ [5, 56]. Therefore to apply the eigenstate filtering method, we only need an initial state2 with non-vanishing overlap with the target eigenstate $\left| 0 \right. \left| x \right.$ that can be efficiently prepared. We will prepare this initial state using the time-optimal adiabatic quantum computing.

# 4.1 Choosing the eigenpath

To use adiabatic quantum computing we need to first specify the eigenpath we are going to follow. We define

$$
H _ { 0 } = \left( \begin{array} { l l } { 0 } & { Q _ { b } } \\ { Q _ { b } } & { 0 } \end{array} \right) = \sigma _ { x } \otimes Q _ { b } .
$$

and

$$
H ( f ) = ( 1 - f ) H _ { 0 } + f H _ { 1 } ,
$$

where $H _ { 1 }$ is defined in Eq. (4).

We will then evolve the system following the 0-eigenstates of each $H ( f )$ . These eigenstates form an eigenpath linking the initial state to the solution to the linear system. There are several important properties of the Hamiltonians $H ( f )$ and of the eigenpath which we discuss below, though some of them we will only use in the algorithm based on the quantum Zeno effect.

The null space of $H ( f )$ is two-dimensional, and we will pay special attention to this fact in our analysis. The non-zero eigenvalues of $H ( f )$ appear in pairs. Let $\lambda _ { j } ( f )$ , $j =$ $1 , 2 , \ldots , N - 1$ be all the positive eigenvalues of $H ( f )$ , and $| z _ { j } ( f ) \rangle$ be the corresponding eigenvectors, then we may readily check

$$
H ( f ) ( \sigma _ { z } \otimes I ) \left| z _ { j } ( f ) \right. = - \lambda _ { j } ( f ) ( \sigma _ { z } \otimes I ) \left| z _ { j } ( f ) \right. .
$$

Therefore $- \lambda _ { j } ( f )$ is also an eigenvalue of $H ( f )$ with corresponding eigenvector $( \sigma _ { z } \otimes$ $I ) | z _ { j } ( f ) \rangle$ , for $j = 1 , 2 , \dots , N - 1$ . Thus we have obtained all the non-zero eigenvalues and corresponding eigenvectors.

The form of the matrices in Eqs. (4) and (5) is important for achieving ${ \mathcal { O } } ( \kappa )$ complexity in our algorithms because they ensure the gap between 0 and other eigenvalues for all $f$ is lower bounded by

$$
\Delta _ { * } ( f ) = 1 - f + \frac { f } \kappa .
$$

A proof can be found in [5].

Now we are ready to specify the eigenpath. For any $f$ , we let $\vert x ( f ) \rangle$ be some vector such that

$$
\left( ( 1 - f ) I + f A \right) | x ( f ) \rangle \propto | b \rangle .
$$

We can then see that the null space of $H ( f )$ is spanned by $| \bar { x } ( f ) \rangle = | 0 \rangle | x ( f ) \rangle$ and $\left| 1 \right. \left| b \right.$ . This requirement pins down the choice for $\vert x ( f ) \rangle$ up to a time-dependent global phase. By requiring the phase to be geometric, i.e.

$$
\begin{array} { r } { \langle x ( f ) | \partial _ { f } | x ( f ) \rangle = 0 , } \end{array}
$$

the eigenpath $\{ | x ( f ) \rangle \}$ becomes uniquely defined when we require $| x ( 0 ) \rangle = | b \rangle$ . Note the above equation is slightly problematic in that we do not know beforehand that $\vert x ( f ) \rangle$ is differentiable. However this turns out not to be a problem because we can establish the differentiability in Appendix F. Furthermore, we have the estimate

$$
\Vert \partial _ { f } \left| x ( f ) \right. \Vert \leq \frac { 2 } { \Delta _ { * } ( f ) } .
$$

The derivation of the existence and uniqueness of the differentiable eigenpath, together with the estimate (9) are given in Appendix F.

An important quantity we need to use in our analysis is the eigenpath length

$$
L = \int _ { 0 } ^ { 1 } \| \partial _ { f } \left| x ( f ) \right. \| \mathrm { d } f ,
$$

and by (9) we have

$$
L \leq \int _ { 0 } ^ { 1 } { \frac { 2 } { \Delta _ { * } ( f ) } } \mathrm { d } f = { \frac { 2 \log ( \kappa ) } { 1 - 1 / \kappa } } .
$$

We also define the eigenpath length $L ( a , b )$ between $0 < a < b < 1$ and it is bounded by

$$
L ( a , b ) = \int _ { a } ^ { b } \| \partial _ { f } | x ( f ) \rangle \| \mathrm { d } f \leq { \frac { 2 } { 1 - 1 / \kappa } } \log \left( { \frac { 1 - ( 1 - 1 / \kappa ) a } { 1 - ( 1 - 1 / \kappa ) b } } \right) = : L _ { * } ( a , b ) .
$$

# 4.2 Time-optimal adiabatic quantum computing

Here we briefly review the procedure of solving QLSP using the recently developed timeoptimal AQC [5] and the eigenpath described in the previous section that has been used in [5, 56].

As noted before, the null space of $H ( f )$ is two-dimensional, which contains an unwanted 0-eigenvector $\left| 1 \right. \left| b \right. = ( 0 , b ) ^ { \top }$ . However this 0-eigenvector is not accessible in the AQC time-evolution

$$
\frac { 1 } { T } { \mathrm { i } } \partial _ { s } \left| \psi _ { T } ( s ) \right. = H ( f ( s ) ) \left| \psi _ { T } ( s ) \right. , \quad \left| \psi _ { T } ( 0 ) \right. = \left| 0 \right. \left| b \right. ,
$$

for scheduling function $f : [ 0 , 1 ] \ \to \ [ 0 , 1 ]$ , which is a strictly increasing mapping with $f ( 0 ) = 0 , f ( 1 ) = 1$ . We find that

$$
\begin{array} { r } { (  1 |  b | ) | \psi _ { T } ( s ) \rangle = 0 , } \end{array}
$$

for all $s \in \left[ 0 , 1 \right]$ . This is due to

$$
\frac { 1 } { T } \mathrm { i } \partial _ { s } ( \langle 1 | \langle b | ) | \psi _ { T } ( s ) \rangle = ( \langle 1 | \langle b | ) H ( f ( s ) ) | \psi _ { T } ( s ) \rangle = 0 ,
$$

and $( \left. 1 \right| \left. b \right| ) \left| \psi _ { T } ( 0 ) \right. = 0$ . This fact gets rid of the problem.

The parameter $T$ needed to reach a certain target accuracy $\epsilon$ is called the runtime complexity (or simply the time complexity). The simplest choice for the scheduling function is $f ( s ) = s$ , which gives the “vanilla AQC”. Besides $\left| 0 \right. \left| x \right.$ , all other eigenstates of $H _ { 1 }$ that can be connected to $\left| 0 \right. \left| b \right.$ through an adiabatic evolution are separated from $\left| 0 \right. \left| x \right.$ by an energy gap of at least $1 / \kappa$ [5, 56]. The time complexity of vanilla AQC is at least $T \sim { \mathcal { O } } ( \kappa ^ { 2 } / \epsilon )$ [2, 5, 24, 39].

By properly choosing a scheduling function $f ( s )$ , the time complexity of AQC can be significantly improved. There are two time-optimal scheduling functions proposed in [5]. The first method is called AQC(p). For $1 < p < 2$ , AQC(p) adopts the schedule

$$
f ( s ) = \frac { \kappa } { \kappa - 1 } \left[ 1 - \Big ( 1 + s ( \kappa ^ { p - 1 } - 1 ) \Big ) ^ { \frac { 1 } { 1 - p } } \right] .
$$

This reduces the time complexity to $\mathcal { O } ( \kappa / \epsilon )$ , which is optimal for $\kappa$ , but the scaling with respect to $\epsilon$ is the same. The second method is called AQC(exp), which uses a different scheduling function to achieve time complexity $\begin{array} { r } { \mathcal { O } \left( \kappa \log ^ { 2 } ( \kappa ) \log ^ { 4 } \left( \frac { \log \kappa } { \epsilon } \right) \right) } \end{array}$ .

All AQC methods are time-dependent Hamiltonian simulation problem, which can be implemented using e.g. truncated Dyson series for simulating the time-dependent Hamiltonian [45]. Although AQC(exp) scales near-optimally with respect to $\kappa$ and $\epsilon$ , numerical evidence indicates that the preconstant of AQC(exp) can be higher than AQC(p). Hence when a low accuracy $\epsilon \sim \mathcal { O } ( 1 )$ is needed, AQC(p) can require a smaller runtime in practice. In the discussion below, we will consider AQC(p).

The details of the time-dependent Hamiltonian simulation for AQC are discussed in Appendix C, and the query complexity for implementing AQC(p) on a gate-based quantum computer is $\widetilde { \mathcal { O } } ( \kappa / \epsilon )$ .

# 4.3 Improved dependence on $\epsilon$

We now use eigenstate filtering to accelerate AQC(p) and reduce the query complexity to $\log ( 1 / \epsilon )$ . As mentioned before, once we have access to $H _ { 1 }$ defined in (4), through the block-encoding $U _ { H _ { 1 } }$ constructed in Appendix A we only need an initial state for eigenstate filtering (note that this is not the initial state of the AQC time-evolution):

$$
\left| \widetilde { x } _ { 0 } \right. = \gamma _ { 0 } \left| 0 \right. \left| x \right. + \gamma _ { 1 } \left| 1 \right. \left| b \right. + \left| \bot \right.
$$

with $| \gamma _ { 0 } | = \Omega ( 1 )$ and $| \bot \rangle$ orthogonal to the null space. The initial state $| \widetilde { x } _ { 0 } \rangle$ can be prepared using the time-optimal AQC procedure. Again we first assume $A$ is Hermitian positive definite. To make $| \gamma _ { 0 } | = \Omega ( 1 )$ we only need to run AQC(p) to constant precision, and thus the linear dependence on precision is no longer a problem. Therefore the time complexity of AQC(p) is ${ \mathcal { O } } ( \kappa )$ . However we still need to implement AQC(p) on a quantum circuit. To do this we use the time-dependent Hamiltonian simulation introduced in [45], which gives a $\mathcal { O } ( d \kappa \log ( d \kappa ) / \log \log ( d \kappa ) )$ query complexity to achieve $\mathcal { O } ( 1 )$ precision, for a $d$ -sparse matrix $A$ . This procedure also needs to be repeated $\mathcal { O } ( 1 )$ times. It should be noted that $\gamma _ { 1 }$ in Eq. (13) comes entirely from the error of the Hamiltonian simulation, since AQC should ensure that the state is orthogonal to $\left| 1 \right. \left| b \right.$ for all $t$ . Details on performing this time-dependent Hamiltonian simulation is given in Appendix C.

Then we can run the eigenstate filtering algorithm described in Section 3 to precision $\epsilon$ to obtain $R _ { \ell } ( H _ { 1 } / d ; 1 / ( d \kappa ) ) \left| \widetilde { x } _ { 0 } \right.$ . The $| \bot \rangle$ component will be filtered out, while the $\left| 0 \right. \left| x \right.$ and $\left| 1 \right. \left| b \right.$ components remain. To further remove the $\left| 1 \right. \left| b \right.$ component, we measure the first qubit. Upon getting an outcome $0$ , the outcome state will just be $\left| 0 \right. \left| x \right. + { \mathcal { O } } ( \epsilon )$ . The success probability of applying the eigenstate filtering is lower bounded by $| \gamma _ { 0 } | ^ { 2 } + | \gamma _ { 1 } | ^ { 2 }$ , and the success probability of obtaining 0 in measurement is $| \gamma _ { 0 } | ^ { 2 } / ( | \gamma _ { 0 } | ^ { 2 } + | \gamma _ { 1 } | ^ { 2 } ) + \mathcal { O } ( \epsilon )$ . Thus the total success probability is $\Omega ( 1 )$ . Each single application of eigenstate filtering applies $U _ { H _ { 1 } }$ , and therefore $O _ { A , 1 }$ , $O _ { A , 2 }$ , and $O _ { B }$ , for ${ \mathcal { O } } ( d \kappa \log ( 1 / \epsilon ) )$ times. It only needs to be repeated $\Omega ( 1 )$ times so the total query complexity of eigenstate filtering is still ${ \mathcal { O } } ( d \kappa \log ( 1 / \epsilon ) )$ .

In eigenstate filtering we need ${ \mathcal { O } } ( n d \kappa \log ( 1 / \epsilon ) )$ additional primitive gates as mentioned in Theorem 3. In time-dependent Hamiltonian simulation the addition number of primitive gates needed is $\begin{array} { r l } { ~ } & { { } \mathcal { O } ( d \kappa ( n + \log ( d \kappa ) ) \frac { \log ( d \kappa ) } { \log \log ( d \kappa ) } ) } \end{array}$ . Both procedures are repeated $\mathcal { O } ( 1 )$ times and therefore in total we need O dκ n log( 1 ) + (n + log(dκ)) log(dκ)log log(dκ)  additional primitive gates.

The number of qubits needed in the eigenstate filtering procedure using QSP is ${ \mathcal { O } } ( n )$ which mainly comes from the original size of the problem and block-encoding. Extra ancilla qubits introduced as a result of eigenstate filtering is only $\mathcal { O } ( 1 )$ . In the Hamiltonian simulation $\mathcal { O } ( n + \log ( d \kappa ) )$ qubits are needed (see Appendix C). Therefore the total number of qubits needed is $\mathcal { O } ( n + \log ( d \kappa ) )$ .

The procedure above can be generalized to Hermitian indefinite matrices, and general matrices that are not necessarily Hermitian (see Appendix D). As discussed in Remark 7, for general matrices we should assume the singular values instead of eigenvalues of $A$ are contained in $[ 1 / \kappa , 1 ]$ . Therefore our QLSP solver can be summarized as

Theorem 8. $A$ is a $d$ -sparse matrix whose singular values are in $[ 1 / \kappa , 1 ]$ and can be queried through oracles $O _ { A , 1 }$ and $O _ { A , 2 }$ in (2), and $| b \rangle$ is given by an oracle $O _ { B }$ in (3). Then $\left| x \right. \propto A ^ { - 1 } \left| b \right.$ can be obtained with fidelity $1 - \epsilon$ , succeeding with probability $\Omega ( 1 )$ with ancilla qubits measurement outcome indicating success, using

2. $\begin{array} { r } { \mathcal { O } \left( d \kappa ( \frac { \log ( d \kappa ) } { \log \log ( d \kappa ) } + \log ( \frac { 1 } { \epsilon } ) ) \right) } \end{array}$ queries to $O _ { A , 1 }$ $O _ { A , 2 }$ prim $O _ { B }$ gates, $\begin{array} { r } { \mathcal { O } \left( d \kappa \left( n \log ( \frac { 1 } { \epsilon } ) + ( n + \log ( d \kappa ) ) \frac { \log ( d \kappa ) } { \log \log ( d \kappa ) } \right) \right) } \end{array}$   
$\mathcal { O } ( n + \log ( d \kappa ) )$ qubits.

When the gate complexity of $O _ { A , 1 }$ , $O _ { A , 2 }$ , and $O _ { B }$ are $\mathrm { p o l y } ( n )$ the total gate complexity, and therefore runtime, by the above theorem, will be $\widetilde { \mathcal { O } } ( \mathrm { p o l y } ( n ) d \kappa \log ( 1 / \epsilon ) )$ .

Remark 9. Although in total we need $\mathcal { O } ( n + \log ( d \kappa ) )$ ancilla qubits, only ${ \mathcal { O } } ( \log ( d \kappa ) )$ comes sources other than the block-encoding of $A$ . In other words, our method only adds ${ \mathcal { O } } ( \log ( d \kappa ) )$ ancilla qubits to those that are unavoidable as long as we use this way of block-encoding of a sparse A. These extra ancilla qubits are mainly a result of using timedependent Hamiltonian simulation. Also, although in the theorem we assumed $A$ is a sparse matrix, we have only used this fact to build its block-encoding. Given the block-encoding of a matrix $A$ that is not necessarily sparse, the above procedure can still be carried out directly. This is also true for Theorem 11 which we are going to introduce later.

We present numerical results obtained on a classical computer in Fig. 2 to validate the complexity estimate. In the numerical test, we solve the linear system $A \left| x \right. \propto \left| b \right.$ , where $A$ is formed by adding a randomly generated symmetric positive definite tridiagonal matrix $B$ , whose smallest eigenvalue is very close to $0$ , to a scalar multiple of the identity matrix. After properly rescaling, the eigenvalues of $A$ lie in $[ - 1 , 1 ]$ . This construction enables us to estimate condition number with reasonable accuracy without computing eigenvalues. The off-diagonal elements of $B$ are drawn uniformly from $[ - 1 , 0 ]$ and the diagonal elements are the negative of sums of two adjacent elements on the same row. The $( 0 , 0 )$ and $( N { - } 1 , N { - } 1 )$ elements of $B$ are slightly larger so that $B$ is positive definite. $| b \rangle$ is drawn from the uniform distribution on the unit sphere.

With $A$ and $| b \rangle$ chosen, we first run the AQC time evolution for time ${ \mathcal { O } } ( \kappa )$ as described at the beginning of this section, and then apply eigenstate filtering using the polynomial $R _ { \ell } ( x ; 1 / d \kappa )$ with degree 2\`. Denoting the resulting quantum state by $| \widetilde x \rangle$ we then compute the fidelity $\eta \ : = \ : | \langle { x } | \widetilde { { x } } \rangle |$ . Fig. 2 shows the relation between $\eta , ~ \kappa$ , and $\ell$ obtained in the numerical experiment.

![](images/d37636cb7c07055c85695a4c26cd48b82889ca24efea625137f77f398fe04e2e.jpg)  
Figure 2: Left: fidelity $\eta$ converges to 1 exponentially as $\ell$ in the eigenvalues filtering algorithm increases, for different $\kappa$ . Right: the smallest $\ell$ needed to achieve fixed fidelity $\eta$ grows linearly with respect to condition number $\kappa$ . The initial state in eigenstate filtering is prepared by running AQC(p) for $T = 0 . 2 \kappa$ , with $p = 1 . 5$ , which achieves an initial fidelity of about 0.6.

# 5 Solving QLSP: eigenstate filtering with quantum Zeno effect

Quantum Zeno effect (QZE) is the phenomenon that frequent measurements hinders a quantum system’s transition from its initial state to other states [9, 15, 26, 27, 46]. A variant of QZE [12, Lemma 1] can be viewed as a particular way for implementing adiabatic quantum computing [41, 50, 54], and this is what we mean by QZE throughout this work unless stated otherwise. The basic idea of this variant of QZE is to follow an adiabatic path through repeated measurement, which acts as projection operators to the instantaneous eigenstate along the adiabatic path. This inspired the randomization method for performing computation based on QZE [12, 56].

In the context of solving QLSP, again for simplicity we first assume $A$ is Hermitian positive definite. Instead of running time-dependent Hamiltonian simulation to evolve from the $0$ -eigenstate of $H _ { 0 }$ to the 0-eigenstate of $H _ { 1 }$ , we consider applying a series of projections to traverse the eigenpath. Choosing $0 = f _ { 0 } < f _ { 1 } < . . . < f _ { M } = 1$ , for each $j = 0 , 1 , \dotsc , M - 1$ , we start from the 0-eigenstate $| 0 \rangle | x ( f _ { j } ) \rangle$ of $H ( f _ { j } )$ , where $| x ( f ) \rangle$ is defined in Eqs. (7) and (8), and project into the null space of $H ( f _ { j + 1 } )$ . In the end we obtain the 0-eigenstate of $H ( 1 ) = H _ { 1 }$ . This is essentially the same as performing projective measurement for each $j$ [12, 20, 56]. If the projective measurements are done approximately using quantum phase estimation or phase randomization, there will be a linear dependence on $1 / \epsilon$ in runtime, $\epsilon$ being the desired precision.

In this section we combine eigenstate filtering with Zeno-based computation to reduce the error dependence from $\mathcal { O } ( 1 / \epsilon )$ to ${ \mathcal { O } } ( \log ( 1 / \epsilon ) )$ , thanks to the possibility of performing approximate projections with high precision. However, several issues demand our attention in the procedure outlined at the beginning of this section. First, we need to specify the choice of $\{ f _ { j } \}$ , which plays an important role in the lower bound of $M$ needed to ensure at least constant success probability. Second, the null space of each $H ( f _ { j } )$ is 2-dimensional. Therefore the eigenpath is not unique, and we need to specify the eigenpath we are going to traverse, which has been done in Sec. 4.1, and to ensure the undesired part of the null space does not interfere with our computation.

# 5.1 The algorithm

As in Section 4, the goal is to produce a state close to the solution state $| x \rangle$ of the QLSP with fidelity at least $1 - \epsilon$ for some given $0 < \epsilon < 1$ . In this section we describe the procedure of the Quantum Zeno effect state preparation. We need to choose a scheduling function

$$
f ( s ) = { \frac { 1 - \kappa ^ { - s } } { 1 - \kappa ^ { - 1 } } }
$$

and define $f _ { j } = f ( s _ { j } )$ where $s _ { j } = j / M$ . Without the scheduling we will end up with an unfavorable square dependence on the minimum spectral gap along the eigenpath [20]. This scheduling is chosen so that

$$
L ( f _ { j } , f _ { j + 1 } ) \le L _ { * } ( f _ { j } , f _ { j + 1 } ) = \frac { 2 \log ( \kappa ) } { M ( 1 - 1 / \kappa ) } ,
$$

which implies we are dividing the interval $\lfloor 0 , 1 \rfloor$ of $f$ into $M$ segments of equal $L _ { * }$ -length.

Before we describe the algorithm we need to first introduce some notations and blockencodings we need to use. From the block-encoding of $H _ { 0 }$ and $H _ { 1 }$ described in Appendix A, we can construct $( 1 - f + f d , n + 6 , 0 )$ -block-encoding for each $H ( f )$ , denoted by $U _ { H } ( f )$ . This construction uses [34, Lemma 29], through

$$
H ( f ) = ( 1 - f + f d ) \left( \langle c | \otimes I \right) \left[ | 0 \rangle \langle 0 | \otimes H _ { 0 } + | 1 \rangle \langle 1 | \otimes \left( H _ { 1 } / d \right) \right] \left( | c \rangle \otimes I \right) ,
$$

where

$$
| c \rangle = \frac { 1 } { \sqrt { 1 - f + f d } } ( \sqrt { 1 - f } | 0 \rangle + \sqrt { f d } | 1 \rangle ) .
$$

We need to use $H _ { 1 } / d$ instead of $H _ { 1 }$ because there is a $d$ factor involved in the blockencoding of $H _ { 1 }$ (see Appendix A) , and the above equation shows we get a $1 - f + f d$ factor in the block-encoding of $H ( f )$ because we need to normalize the coefficient vector $| c \rangle$ . For a more detailed discussion see Appendix A. Applying the eigenstate filtering procedure in Section 3 to precision $\epsilon _ { P }$ gives us an $( 1 , n + 7 , \epsilon _ { P } )$ -block-encoding of

$$
\begin{array} { r } { \bar { P } _ { 0 } ( f ) = \left| 0 \right. \left| x ( f ) \right. \left. 0 \right| \left. x ( f ) \right| + \left| 1 \right. \left| b \right. \left. 1 \right| \left. b \right| , } \end{array}
$$

which we denote by $U _ { P _ { 0 } } ( f )$ . By Theorem 3 this uses $U _ { H } ( f )$ and its inverse $\begin{array} { r } { \mathcal { O } \big ( \frac { d } { \Delta _ { * } ( f ) } \log \big ( \frac { 1 } { \epsilon _ { P } } \big ) \big ) } \end{array}$ times. Note that one ancilla qubit introduced in Theorem 3 is redundant because we do not need to shift by a multiple of the identity matrix. By definition of block-encoding we have

$$
\begin{array} { r } { \left\| \bar { P } _ { 0 } ( f ) - ( \langle 0 ^ { n + 7 } | \otimes I _ { n + 1 } ) U _ { P _ { 0 } } ( f ) ( | 0 ^ { n + 7 } \rangle \otimes I _ { n + 1 } ) \right\| \le \epsilon _ { P } . } \end{array}
$$

Here for clarity we use $I _ { r }$ to denote the identity operator acting on $r$ qubits. Note that we need access to

$$
P _ { 0 } ( f ) = \left| x ( f ) \right. \left. x ( f ) \right| ,
$$

which is the projection operator onto $| x ( f ) \rangle$ , instead of $P _ { 0 } ( f )$ , which is the projection operator onto $\left| 0 \right. \left| x ( f ) \right.$ . We now consider how to approximate $P _ { 0 } ( f )$ . Because of the fact

$$
P _ { 0 } ( f ) = ( \langle 0 | \otimes I _ { n } ) \bar { P } _ { 0 } ( f ) ( | 0 \rangle \otimes I _ { n } ) ,
$$

we denote

$$
\widetilde { P } _ { 0 } ( f ) = ( \langle 0 ^ { n + 7 } | \langle 0 | \otimes I _ { n } \rangle U _ { P _ { 0 } } ( f ) ( | 0 ^ { n + 7 } \rangle | 0 \rangle \otimes I _ { n } )
$$

and $\tilde { P } _ { 0 } ( f )$ approximates $P _ { 0 } ( f )$ by the following inequalities:

$$
\begin{array} { r l } & { \widetilde { P } _ { 0 } ( f ) - P _ { 0 } ( f ) \| = \Big \| ( \langle 0 | \otimes I _ { n } \rangle \left( ( \langle 0 ^ { n + 7 } | \otimes I _ { 1 } \otimes I _ { n } ) U _ { P _ { 0 } } ( f ) ( | 0 ^ { n + 7 } \rangle \otimes I _ { 1 } \otimes I _ { n } ) - \bar { P } _ { 0 } ( f ) \right) ( | 0 \rangle \otimes I _ { n + 1 } ( f ) ) \Big \| } \\ & { \qquad \leq \Big \| ( \langle 0 ^ { n + 7 } | \otimes I _ { 1 } \otimes I _ { n } \rangle U _ { P _ { 0 } } ( f ) ( | 0 ^ { n + 7 } \rangle \otimes I _ { 1 } \otimes I _ { n } ) - \bar { P } _ { 0 } ( f ) \Big \| } \\ & { \qquad \leq \epsilon _ { P } . } \end{array}
$$

Therefore $U _ { P _ { 0 } } ( f )$ is an $( 1 , n + 8 , \epsilon _ { P } )$ -block-encoding of $P _ { 0 } ( f )$

As discussed in Section 4.1, the eigenpath we want to follow is $\{ | 0 \rangle | x ( f ) \rangle \}$ . However the approximate projection using eigenstate filtering only allows us to approximately follow this eigenpath. We denote the approximate states by $| \widetilde { x } ( f _ { j } ) \rangle \approx | x ( f _ { j } ) \rangle$ , and will take into account the error of this approximation in our analysis.

With the block-encoding of $P _ { 0 } ( f )$ we can describe the algorithm is as follows:

1. Given $0 < \epsilon < 1$ and $\kappa > 1$ as well as the oracles mentioned at the beginning of Section 4. Set $\begin{array} { r } { M = \lceil \frac { 4 \log ^ { 2 } ( \kappa ) } { ( 1 - 1 / \kappa ) ^ { 2 } } \rceil } \end{array}$ , $\begin{array} { r } { \epsilon _ { P } = \frac { 1 } { 1 6 2 M ^ { 2 } } } \end{array}$ .

2. Prepare $| \widetilde x ( 0 ) \rangle = | b \rangle$ . Let $j = 1$ .

3. Apply the $( 1 , n \dag 8 , \epsilon _ { P } )$ -block-encoding $U _ { P _ { 0 } } ( f _ { j } )$ of $P _ { 0 } ( f _ { j } )$ , constructed using eigenstate filtering with a polynomial of sufficiently high degree constructed in Lemma 2, to $\left| 0 ^ { n + 8 } \right. \left| \widetilde { x } ( f _ { j - 1 } ) \right.$ to get $U _ { P _ { 0 } } ( f _ { j } ) ( | 0 ^ { n + 8 } \rangle | \widetilde { x } ( f _ { j - 1 } ) \rangle )$ .

4. Measure the $n + 8$ ancilla qubits.

(a) If not all outputs are 0 then abort and return to Step 2.   
(b) If all outputs are 0, and further $j < M - 1$ , then let $| \widetilde { x } ( f _ { j } ) \rangle$ be the state in the main register that has not been measured, let $j  j + 1$ , and go to Step 3. If all outputs are 0 and $j = M - 1$ then go to next step.

5. Apply the $( 1 , n + 8 , \epsilon / 4 )$ -block-encoding $U _ { P _ { 0 } } ( 1 )$ of $P _ { 0 } ( 1 )$ to $\left| 0 ^ { n + 8 } \right. \left| \widetilde { x } ( f _ { M - 1 } ) \right.$ to get $U _ { P _ { 0 } } ( f _ { j } ) ( | 0 ^ { n + 8 } \rangle | \widetilde { x } ( f _ { M - 1 } ) \rangle )$ .

6. Measure the $n + 8$ ancilla qubits.

(a) If not all outputs are 0 then abort and return to Step 2.   
(b) If all outputs are $0$ , then output $| \widetilde { x } ( 1 ) \rangle$ in the main register.

Here $| \widetilde { x } ( f _ { j } ) \rangle$ are defined recursively in Steps 3 and 4 in the algorithm, starting with $| \widetilde { x } ( 0 ) \rangle = | b \rangle$ . We can write down the recursion more concisely:

$$
| \widetilde { x } ( f _ { j } ) \rangle = \frac { \widetilde { P } _ { 0 } ( f _ { j } ) | \widetilde { x } ( f _ { j - 1 } ) \rangle } { \Vert \widetilde { P } _ { 0 } ( f _ { j } ) | \widetilde { x } ( f _ { j - 1 } ) \rangle \Vert } .
$$

Going from $| \widetilde x ( f _ { j - 1 } ) \rangle$ to $| \widetilde { x } ( f _ { j } ) \rangle$ has a success probability $\| \widetilde { P } _ { 0 } ( f _ { j } ) | \widetilde { x } ( f _ { j - 1 } ) \rangle \| ^ { 2 }$ . We will show in the next section as well as in Appendix G that the the final success probability, which is the product of the success probabilities of these individual steps, does not go to 0. We emphasize that $\{ | \widetilde x ( f ) \rangle \}$ is defined only for $f = f _ { j }$ rather than arbitrary $f \in \left[ 0 , 1 \right]$ . We use this notation only to be consistent with the notation $\vert x ( f ) \rangle$ .

Remark 10 (Choice of precision parameters). There are two precision parameters involved in the above discussion:  and $\epsilon _ { P }$ . Here $\epsilon$ is the target accuracy specified as part of our task, while $\epsilon _ { P }$ is a parameter that is chosen by the algorithm according to Step 1, and is used only to ensure that the success probability is lower bounded by a constant. Also note that in the last step with $j = M$ (Steps 5 and $\it 6$ ), we set the target accuracy to be $\epsilon / 4$ instead of $\epsilon _ { P }$ in the previous steps. In fact, the errors of eigenstate filtering for $j = 1 , 2 , \dots , M - 1$ do not directly contribute to the final error. Rather, they only directly affect the success probability. When the overlap $| \left. \widetilde { x } ( f _ { M - 1 } ) | x ( 1 ) \right. |$ is lower bounded by a constant away from $\boldsymbol { \mathit { 0 } }$ , as we will show in Lemma 15, the final error is entirely controlled by the accuracy of the final eigenstate filtering for $j = M$ , which is in turn controlled by the parameter $\epsilon / 4$ . In this way we ensure, as will be shown in the next section, that the output $| \widetilde { x } ( 1 ) \rangle$ satisfies

$$
| \left. \widetilde { x } ( 1 ) | x \right. | \geq 1 - \epsilon .
$$

# 5.2 Success probability, fidelity, and complexities

In this section we discuss the success probability of the algorithm described in the previous section, prove the fidelity of the output state is lower bounded by $1 - \epsilon$ for the given $\epsilon$ when $\epsilon _ { P }$ and $M$ are chosen as in Step 1 of the algorithm, and finally estimate the query and gate complexities.

We first give a lower bound for success probability assuming for simplicity each projection is done without error, i.e. $\epsilon _ { P } = 0$ . This is done so that we do not need to distinguish between eigenstates and approximate eigenstates produced using eigenstate filtering, thus making the derivation less technical. A rigorous lower bound, assuming a finite $\epsilon _ { P } > 0$ , will be given in Appendix G. Under this assumption we have

$$
p _ { \mathrm { s u c c e s s } } = \prod _ { j = 1 } ^ { M } \| P _ { 0 } ( f _ { j } ) | x ( f _ { j - 1 } ) \rangle \| ^ { 2 } = \prod _ { j = 1 } ^ { M } | \langle x ( f _ { j } ) | x ( f _ { j - 1 } ) \rangle | ^ { 2 } .
$$

Since

$$
\begin{array} { r l } & { | \langle x ( f _ { j } ) | x ( f _ { j - 1 } ) \rangle | \ge 1 - \displaystyle \frac { 1 } { 2 } \| | x ( f _ { j - 1 } ) \rangle - | x ( f _ { j } ) \rangle \| ^ { 2 } , } \\ & { \| | x ( f _ { j - 1 } ) \rangle - | x ( f _ { j } ) \rangle \| \le L ( f _ { j - 1 } , f _ { j } ) \le L _ { * } ( f _ { j - 1 } , f _ { j } ) , } \end{array}
$$

we have

$$
\begin{array} { r l } & { p _ { \mathrm { s u c c e s s } } \geq \left( \displaystyle \prod _ { j = 1 } ^ { M } \left( 1 - \frac { 1 } { 2 } \| | \ x ( f _ { j - 1 } ) \rangle - | x ( f _ { j } ) \rangle \| ^ { 2 } \right) \right) ^ { 1 } } \\ & { \qquad \geq \left( 1 - \frac { 2 \log ^ { 2 } ( \kappa ) } { M ^ { 2 } \left( 1 - 1 / \kappa \right) ^ { 2 } } \right) ^ { 2 M } } \\ & { \qquad \geq \left( 1 - \frac { 2 \log ^ { 2 } ( \kappa ) } { M \left( 1 - 1 / \kappa \right) ^ { 2 } } \right) ^ { 2 } } \\ & { \qquad \geq \frac { 1 } { 4 } , } \end{array}
$$

where the we have used Eq. (15). This inequality holds for $\begin{array} { r } { M \ge \frac { 4 \log ^ { 2 } ( \kappa ) } { ( 1 - 1 / \kappa ) ^ { 2 } } } \end{array}$ as required in the previous section.

Therefore we have shown the success probability is lower bounded by $1 / 4$ . The success probability when taking into account errors in each approximate projection, or in other

words when we choose $\epsilon { } _ { P } = 1 / 1 6 2 M ^ { 2 }$ according to our algorithm rather than setting it to $0$ , is still lower bounded by a constant, which is proved in Appendix G.

We then analyze the fidelity and complexities of our algorithm. Here we no longer assume $\epsilon { } _ { P } = 0$ , and the following discussion is therefore rigorous. In Appendix G it is shown that

$$
| \langle \widetilde { x } ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle | \ge 1 - \frac { 1 } { 2 M } - 4 \epsilon _ { P } - 2 \sqrt { 2 \epsilon _ { P } } \ge \frac { 1 } { 2 } , \quad j = 0 , 1 , \dots , M - 1 ,
$$

for $\epsilon _ { P } \leq 1 / 1 2 8$ and $\begin{array} { r } { M \ge \frac { 4 \log ^ { 2 } ( \kappa ) } { ( 1 - 1 / \kappa ) ^ { 2 } } \ge 4 } \end{array}$ . Therefore $| \left. \widetilde { x } ( f _ { M - 1 } ) | x ( f _ { M } ) \right. | \geq 1 / 2$ , which allows us to bound the error as,

$$
\begin{array} { r l } { | \langle x | \widetilde { x } ( 1 ) \rangle | = | \langle \widetilde { x } ( f _ { M } ) | x ( f _ { M } ) \rangle | } & { } \\ & { = \frac { | \langle \widetilde { x } ( f _ { M - 1 } ) | \widetilde { P } _ { 0 } ( f _ { M } ) | x ( f _ { M } ) \rangle | } { \| \sqrt { 0 } ( f _ { M } ) | \widetilde { x } ( f _ { M - 1 } ) \rangle | } } \\ & { \ge \frac { | \langle \widetilde { x } ( f _ { M - 1 } ) | P _ { 0 } ( f _ { M } ) | x ( f _ { M } ) \rangle | - \epsilon / 4 } { \| P _ { 0 } ( f _ { M } ) | \widetilde { x } ( f _ { M - 1 } ) \rangle | + \epsilon / 4 } } \\ & { = \frac { | \langle \widetilde { x } ( f _ { M - 1 } ) | x ( f _ { M } ) \rangle | - \epsilon / 4 } { | \langle \widetilde { x } ( f _ { M - 1 } ) | x ( f _ { M } ) \rangle | + \epsilon / 4 } } \\ & { \ge 1 - \frac { \epsilon / 2 } { | \langle \widetilde { x } ( f _ { M - 1 } ) | x ( f _ { M } ) \rangle | } } \\ & { \ge 1 - \epsilon . } \end{array}
$$

The derivation is similar to that of Eq. (A10), and we have used the fact that $\Vert \widetilde { P } _ { 0 } ( f _ { M } ) -$ $P _ { 0 } ( f _ { M } ) \| \le \epsilon / 4$ because in Step 5 our algorithm in the previous section sets the eigenstate filtering accuracy to be $\epsilon / 4$ instead of $\epsilon { } _ { P }$ . Therefore the state $| \widetilde { x } ( 1 ) \rangle$ prepared in this way has a fidelity at least $1 - \epsilon$ .

We then estimate the computational costs. At each $j$ we need to apply an $( 1 , n + 8 , \epsilon _ { P } )$ - block-encoding $U _ { P _ { 0 } } ( f _ { j } )$ of $P _ { 0 } ( f _ { j } )$ to $| \widetilde x ( f _ { j - 1 } ) \rangle$ obtained form the last step. From the analysis in Appendix G we need $\epsilon _ { P } \leq 1 / 1 6 2 M ^ { 2 }$ . Therefore we need to apply and its inverse $\begin{array} { r } { \mathcal { O } \left( \frac { 1 - f _ { j } + d f _ { j } } { \Delta _ { * } ( f _ { j } ) } \log ( \frac { 1 } { \epsilon _ { P } } ) \right) } \end{array}$ times. In total for $j = 1 , 2 , \dots , M - 1$ the number of queries to $U _ { H } ( f )$ is of the order

$$
\begin{array} { r l r } & { } & { \log \left( \displaystyle \frac { 1 } { \epsilon _ { P } } \right) \displaystyle \sum _ { j = 1 } ^ { M - 1 } \displaystyle \frac { 1 - f ( s _ { j } ) + f ( s _ { j } ) d } { 1 - f ( s _ { j } ) + f ( s _ { j } ) / \kappa } \leq \log \left( \displaystyle \frac { 1 } { \epsilon _ { P } } \right) M \displaystyle \int _ { 0 } ^ { 1 } \displaystyle \frac { 1 - f ( s ) + f ( s ) d } { 1 - f ( s ) + f ( s ) / \kappa } \mathrm { d } s } \\ & { } & { = \log \left( \displaystyle \frac { 1 } { \epsilon _ { P } } \right) M \left( \displaystyle \frac { d \kappa - 1 } { \log ( \kappa ) } - \displaystyle \frac { d - 1 } { 1 - 1 / \kappa } \right) , } \end{array}
$$

for a $d$ -sparse matrix $A$ and $\kappa$ is the condition number of $A$ . Then in the last step for $j = M$ , which is Step 5 in the algorithm in Section 5.1, we need to achieve accuracy $\epsilon / 4$ for the eigenstate filtering. Therefore we need to apply the block-encoding $U _ { P _ { 0 } } ( 1 )$ with $\mathcal { O } ( d \kappa \log ( \frac { 1 } { \epsilon } ) )$ queries to $U _ { H } ( 1 )$ . As $M = \mathcal { O } ( \log ^ { 2 } ( \kappa ) )$ , adding the query complexity of the last step to (23), and using the fact $\epsilon _ { P } = \mathcal { O } ( 1 / M ^ { 2 } )$ , gives us the total query complexity of a single run

$$
\mathcal { O } \left( d \kappa \left( \log ( \kappa ) \log \log ( \kappa ) + \log ( 1 / \epsilon ) \right) \right) .
$$

Because the success probability is $\Omega ( 1 )$ , the procedure needs to be run for an expected $\mathcal { O } ( 1 )$ times to be successful, and therefore the total complexity remains the same. Since $U _ { H } ( f )$ queries $O _ { A , 1 }$ , $O _ { A , 2 }$ , and $O _ { B }$ each $\mathcal { O } ( 1 )$ times, Eq. (24) is also the query complexity to these oracles.

Because the only thing we need to do in this method to solve QLSP is to repeatedly use QSP to do projection, no additional qubits are involved for time-dependent Hamiltonian simulation as in the previous AQC-based method. The total number of qubits is therefore ${ \mathcal { O } } ( n )$ . The number of additional primitive gates required can be estimated similarly to the number of queries, which scales as $\begin{array} { r } { \mathcal { O } \left( n d \kappa \left( \log ( \kappa ) \log \log ( \kappa ) + \log ( \frac { 1 } { \epsilon } ) \right) \right) } \end{array}$ .

For the case when $A$ is indefinite, we use a different pair of $H _ { 0 }$ and $H _ { 1 }$ as discussed in Appendix D. The generalization to non-Hermitian matrices is the same as for Theorem 8, and it can be found in Appendix D as well. All other procedures are almost exactly the same. We summarize the results in the following theorem:

Theorem 11. $A$ is a $d$ -sparse matrix whose singular values are in $[ 1 / \kappa , 1 ]$ and can be queried through oracles $O _ { A , 1 }$ and $O _ { A , 2 }$ in (2), and $| b \rangle$ is given by an oracle $O _ { B }$ . Then $\left| x \right. \propto A ^ { - 1 } \left| b \right.$ can be obtained with fidelity $1 - \epsilon$ , succeeding with probability $\Omega ( 1 )$ with ancilla qubits measurement outcome indicating success, using

1. $\begin{array} { r } { \mathcal { O } \left( d \kappa \left( \log ( \kappa ) \log \log ( \kappa ) + \log ( \frac { 1 } { \epsilon } ) \right) \right) } \end{array}$ queries to $O _ { A , 1 }$ , $O _ { A , 2 }$ , and $O _ { B }$ ,   
2. $\mathcal { O } \left( n d \kappa \left( \log ( \kappa ) \log \log ( \kappa ) + \log ( \frac { 1 } { \epsilon } ) \right) \right)$ other primitive gates,   
3. ${ \mathcal { O } } ( n )$ qubits.

The reason we put requirement on the singular values of $A$ instead of its eigenvalues is stated in Remark 7. Just like in the case of AQC-based QLSP algorithm, here if we have $\mathcal { O } ( \mathrm { p o l y } ( n ) )$ gate complexity for the oracles $O _ { A , 1 }$ , $O _ { A , 2 }$ , and $O _ { B }$ , then the total gate complexity will be $\tilde { \mathcal { O } } ( \mathrm { p o l y } ( n ) d \kappa \log ( 1 / \epsilon ) )$ . Although we use ${ \mathcal { O } } ( n )$ qubits in total, the extra ancilla qubits we introduce in this method is in fact only $\mathcal { O } ( 1 )$ . This is a further improvement from the ${ \mathcal { O } } ( \log ( d \kappa ) )$ ancilla qubits in the AQC-based QLSP algorithm.

We remark that there is the possibility to further slightly improve by a $\log ( \kappa )$ factor (ignoring log log terms) the asymptotic complexity of our QZE-based QLSP solver by using the fixed-point amplitude amplification to go from $| x ( f _ { j } ) \rangle$ to $| x ( f _ { j + 1 } ) \rangle$ for each $j$ , as discussed in [60, Corollary 1]. The bounds in this paper for many constant factors involved, particular those used in estimating the success probability of the QZE-based QLSP solver, are rather loose. However this does not concern us very much because we care mainly about the asymptotic complexity. Tighter estimates can be helpful for the actual implementation of our methods.

# 6 Discussion

In this paper, we have developed a quantum eigenstate filtering algorithm based on quantum signal processing (QSP). Our algorithm achieves the optimal query complexity among all polynomial-based eigenstate filtering methods, and uses a minimal amount of ancilla qubits. We demonstrate the usage of the eigenstate filtering method to solve quantum linear system problems (QLSP) with near-optimal complexity with respect to both the condition number $\kappa$ and the accuracy $\epsilon$ . In the case when the precise value of $\kappa$ is not known a priori, the knowledge of an upper bound of $\kappa$ would suffice.

The problem of directly targeting at the solution $A ^ { - 1 } \left| b \right.$ is that a $( \beta , m , \epsilon )$ blockencoding of $A ^ { - 1 }$ requires at least $\beta \geq \kappa$ to make sure that $\| A ^ { - 1 } / \beta \| \le 1$ . Therefore the probability of success in the worst case is already $\Omega ( \kappa ^ { - 2 } )$ , and the number of rounds of amplitude amplification needed is already ${ \mathcal { O } } ( \kappa )$ . Therefore to achieve near-optimal complexity, this approach can only query the block-encoding of $A$ for $\mathcal { O } ( \mathrm { p o l y l o g } ( \kappa ) )$ times. To our best knowledge, there is no known method to achieve this for general matrices.

However this might be possible for matrices with special structures and will be studied in future work.

Motivated by the success of AQC, our algorithm views QLSP as an eigenvalue problem, which can be implemented via $P \left| \widetilde { x } _ { 0 } \right.$ , where $P$ is an approximate projection operator, and $P \left| \widetilde { x } _ { 0 } \right.$ encodes the solution $| x \rangle$ . The advantage of such a filtering procedure is that $P$ is a projector and $\| \cal { P } \| = 1$ . Hence its $( \beta , m , \epsilon )$ block-encoding only requires $\beta \sim$ $\mathcal { O } ( 1 )$ . Therefore assuming $\mathcal { O } ( 1 )$ overlap between $| \widetilde { x } _ { 0 } \rangle$ and the solution vector, which can be satisfied by running the time-optimal AQC to constant precision, the probability of success of the filtering procedure is already $\Omega ( 1 )$ without any amplitude amplification procedure. This accelerates the query complexity of the recently developed time-optimal AQC from $\widetilde { \mathcal { O } } ( \kappa / \epsilon )$ to ${ \widetilde O } ( \kappa \log ( 1 / \epsilon ) )$ . The efficient gate-based implementation of AQC still requires a time-dependent Hamiltonian simulation procedure (shown in Appendix C). We then demonstrate that the dependence on the time-dependent Hamiltonian simulation procedure can be removed, using an algorithm based on the quantum Zeno effect, and the complexity is ${ \widetilde O } ( \kappa \log ( 1 / \epsilon ) )$ . Both algorithms have constant probability of success, and can prepare the solution in terms of a pure state.

It is worth noting that the eigenstate filtering method developed in this paper works only for the case when the eigenvalue corresponding to the desired eigenstate is known exactly, which is satisfied in the eigenvalue formulation of QLSP. In order to implement the QSP-based eigenstate filtering procedure, one still needs to find the phase factors associated with the block encoding $\widetilde { U }$ . For a given polynomial $R _ { \ell } ( \cdot , \Delta )$ , the phase factors are obtained on a classical computer in time that is polynomial in the degree and the logarithm of precision [32, Theorems 3-5]. However, this procedure requires solution of all roots of a high degree polynomial, which can be unstable for the range of polynomials $\ell \sim 1 0 0$ considered here. The stability of such procedure has recently been improved by Haah [37], though the number of bits of precision needed still scales as ${ \mathcal { O } } ( \ell \log ( \ell / \epsilon ) )$ . Significant progress has been achieved recently, enabling robust computation of phase factors for polynomials of degrees ranging from thousands to tens of thousands [18, 23]. We note that these phase factors in the eigenvalue filtering procedure only depend on $\widetilde { \Delta }$ and $\ell$ , and therefore can be reused for different matrices once they are obtained on a classical computer.

# Acknowledgements

This work was partially supported by the Department of Energy under Grant No. DE-SC0017867, the Quantum Algorithm Teams Program under Grant No. DE-AC02-05CH11231, the Google Quantum Research Award (L.L.), and by the Air Force Office of Scientific Research under award number FA9550-18-1-0095 (L.L. and Y.T.). We thank Dong An, Yulong Dong, Nathan Wiebe for helpful discussions. We also thank the anonymous reviewers for helpful suggestions on improving the presentation of this paper and the applications of eigenstate filtering discussed at the end of Section 3.

# References

[1] D. Aharonov and A. Ta-Shma. Adiabatic quantum state generation and statistical zero knowledge. In Proceedings of the thirty-fifth annual ACM symposium on Theory of computing, pages 20–29. ACM, 2003. DOI: 10.1145/780542.780546.   
[2] T. Albash and D. A. Lidar. Adiabatic quantum computation. Rev. Mod. Phys., 90: 015002, 2018. DOI: 10.1103/RevModPhys.90.015002. for solving systems of linear equations. arXiv preprint arXiv:1010.4458, 2010.   
[4] A. Ambainis. Variable time amplitude amplification and quantum algorithms for linear algebra problems. In STACS’12 (29th Symposium on Theoretical Aspects of Computer Science), volume 14, pages 636–647, 2012.   
[5] D. An and L. Lin. Quantum linear system solver based on time-optimal adiabatic quantum computing and quantum approximate optimization algorithm. arXiv:1909.05500, 2019.   
[6] S. Apers and A. Sarlette. Quantum fast-forwarding: Markov chains and graph property testing. Quantum Information & Computation, 19(3-4):181–213, 2019. URL https://dl.acm.org/doi/10.5555/3370245.3370246.   
[7] S. Apers, A. Gilyén, and S. Jeffery. A unified framework of quantum walk search. arXiv preprint arXiv:1912.04233, 2019.   
[8] J. M. Arrazola, A. Delgado, B. R. Bardhan, and S. Lloyd. Quantum-inspired algorithms in practice. arXiv preprint arXiv:1905.10415, 2019.   
[9] A. Balachandran and S. Roy. Quantum anti-Zeno paradox. Physical review letters, 84 (18):4019, 2000. DOI: 10.1103/PhysRevLett.84.4019.   
[10] D. W. Berry, A. M. Childs, R. Cleve, R. Kothari, and R. D. Somma. Simulating hamiltonian dynamics with a truncated taylor series. Phys. Rev. Lett., 114(9):090502, 2015. DOI: 10.1103/PhysRevLett.114.090502.   
[11] D. W. Berry, A. M. Childs, and R. Kothari. Hamiltonian simulation with nearly optimal dependence on all parameters. In 2015 IEEE 56th Annual Symposium on Foundations of Computer Science, pages 792–809. IEEE, 2015. DOI: 10.1109/FOCS.2015.54.   
[12] S. Boixo, E. Knill, and R. D. Somma. Eigenpath traversal by phase randomization. Quantum Info. Comput., 9:833–855, 2009. URL https://dl.acm.org/doi/10.5555/ 2011804.2011811.   
[13] G. Brassard, P. Hoyer, M. Mosca, and A. Tapp. Quantum amplitude amplification and estimation. Contemp. Math., 305:53–74, 2002. DOI: 10.1090/conm/305/05215.   
[14] C. Bravo-Prieto, R. LaRose, M. Cerezo, Y. Subasi, L. Cincio, and P. J. Coles. Variational quantum linear solver: A hybrid algorithm for linear systems. arXiv:1909.05820, 2019.   
[15] D. Burgarth, P. Facchi, V. Giovannetti, H. Nakazato, S. Pascazio, and K. Yuasa. Non-abelian phases from quantum Zeno dynamics. Physical Review A, 88(4):042107, 2013. DOI: 10.1103/PhysRevA.88.042107.   
[16] Y. Cao, A. Papageorgiou, I. Petras, J. Traub, and S. Kais. Quantum algorithm and circuit design solving the poisson equation. New J. Phys., 15(1):013021, 2013. DOI: 10.1088/1367-2630/15/1/013021.   
[17] S. Chakraborty, A. Gilyén, and S. Jeffery. The power of block-encoded matrix powers: improved regression techniques via faster Hamiltonian simulation. arXiv preprint arXiv:1804.01973, 2018.   
[18] R. Chao, D. Ding, A. Gilyen, C. Huang, and M. Szegedy. Finding angles for quantum signal processing with machine precision. arXiv preprint arXiv:2003.02831, 2020.   
[19] N.-H. Chia, H.-H. Lin, and C. Wang. Quantum-inspired sublinear classical algorithms for solving low-rank linear systems. arXiv preprint arXiv:1811.04852, 2018.   
[20] A. M. Childs, E. Deotto, E. Farhi, J. Goldstone, S. Gutmann, and A. J. Landahl. Quantum search by measurement. Phys. Rev. A, 66(3):032314, 2002. DOI: 10.1103/PhysRevA.66.032314.   
[21] A. M. Childs, R. Kothari, and R. D. Somma. Quantum algorithm for systems of linear equations with exponentially improved dependence on precision. SIAM J. Comput., 46:1920–1950, 2017. DOI: 10.1137/16M1087072.   
[22] A. N. Chowdhury, Y. Subasi, and R. D. Somma. Improved implementation of reflection operators. arXiv preprint arXiv:1803.02466, 2018.   
[23] Y. Dong, X. Meng, K. B. Whaley, and L. Lin. Efficient phase factor evaluation in quantum signal processing. arXiv preprint arXiv:2002.11649, 2020.   
[24] A. Elgart and G. A. Hagedorn. A note on the switching adiabatic theorem. J. Math. Phys., 53(10):102202, 2012. DOI: 10.1063/1.4748968.   
[25] P. Erdös. Some remarks on polynomials. Bulletin of the American Mathematical Society, 53(12):1169–1176, 1947. DOI: 10.1090/S0002-9904-1947-08938-2.   
[26] P. Facchi and S. Pascazio. Quantum Zeno dynamics: mathematical and physical aspects. Journal of Physics A: Mathematical and Theoretical, 41(49):493001, 2008. DOI: 10.1088/1751-8113/41/49/493001.   
[27] P. Facchi, A. Klein, S. Pascazio, and L. Schulman. Berry phase from a quantum Zeno effect. Physics Letters A, 257(5-6):232–240, 1999. DOI: 10.1016/S0375-9601(99)00323- 0.   
[28] E. Farhi, J. Goldstone, S. Gutmann, and M. Sipser. Quantum computation by adiabatic evolution. arXiv preprint quant-ph/0001106, 2000.   
[29] E. Farhi, J. Goldstone, and S. Gutmann. A quantum approximate optimization algorithm. arXiv preprint arXiv:1411.4028, 2014.   
[30] Y. Ge, J. Tura, and J. I. Cirac. Faster ground state preparation and high-precision ground energy estimation with fewer qubits. J. Math. Phys., 60(2):022202, 2019. DOI: 10.1063/1.5027484.   
[31] A. Gilyén, S. Lloyd, and E. Tang. Quantum-inspired low-rank stochastic regression with logarithmic dependence on the dimension. arXiv preprint arXiv:1811.04909, 2018.   
[32] A. Gilyén, Y. Su, G. H. Low, and N. Wiebe. Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics. arXiv preprint arXiv:1806.01838, 2018. DOI: 10.1145/3313276.3316366.   
[33] A. Gilyén, S. Arunachalam, and N. Wiebe. Optimizing quantum optimization algorithms via faster quantum gradient computation. In Proceedings of the Thirtieth Annual ACM-SIAM Symposium on Discrete Algorithms, pages 1425–1444, 2019. DOI: 10.1137/1.9781611975482.87.   
[34] A. Gilyén, Y. Su, G. H. Low, and N. Wiebe. Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics. In Proceedings of the 51st Annual ACM SIGACT Symposium on Theory of Computing, pages 193–204, 2019. DOI: 10.1145/3313276.3316366.   
[35] L. K. Grover. A fast quantum mechanical algorithm for database search. In Proceedings of the twenty-eighth annual ACM symposium on Theory of computing, pages 212–219, 1996. DOI: 10.1145/237814.237866.   
[36] L. K. Grover. Fixed-point quantum search. Physical Review Letters, 95(15):150501, 2005. DOI: 10.1103/PhysRevLett.95.150501.   
[37] J. Haah. Product decomposition of periodic functions in quantum signal processing. Quantum, 3:190, 2019. DOI: 10.22331/q-2019-10-07-190.   
[38] A. W. Harrow, A. Hassidim, and S. Lloyd. Quantum algorithm for linear systems of equations. Phys. Rev. Lett., 103:150502, 2009. DOI: 10.1007/978-3-642-27848-8_771- 1.   
[39] S. Jansen, M.-B. Ruskai, and R. Seiler. Bounds for the adiabatic approximation with applications to quantum computation. J. Math. Phys., 48(10):102111, 2007. DOI: 10.1063/1.2798382.   
[40] A. Y. Kitaev. Quantum measurements and the abelian stabilizer problem. arXiv preprint quant-ph/9511026, 1995.   
[41] J. Lemieux, G. Duclos-Cianci, D. Sénéchal, and D. Poulin. Resource estimate for quantum many-body ground state preparation on a quantum computer. arXiv preprint arXiv:2006.04650, 2020.   
[42] S. Lloyd. Universal quantum simulators. Science, pages 1073–1078, 1996. DOI: 10.1126/science.273.5278.1073.   
[43] G. H. Low and I. L. Chuang. Optimal hamiltonian simulation by quantum signal processing. Phys. Rev. Lett., 118:010501, 2017. DOI: 10.1103/PhysRevLett.118.010501.   
[44] G. H. Low and I. L. Chuang. Hamiltonian simulation by qubitization. Quantum, 3: 163, 2019. DOI: 10.22331/q-2019-07-12-163.   
[45] G. H. Low and N. Wiebe. Hamiltonian simulation in the interaction picture. arXiv preprint arXiv:1805.00675, 2018.   
[46] B. Misra and E. G. Sudarshan. The Zeno’s paradox in quantum theory. Journal of Mathematical Physics, 18(4):756–763, 1977. DOI: 10.1063/1.523304.   
[47] R. M. Parrish and P. L. McMahon. Quantum filter diagonalization: Quantum eigendecomposition without full quantum phase estimation. arXiv preprint arXiv:1909.08925, 2019.   
[48] D. Poulin and P. Wocjan. Preparing ground states of quantum many-body systems on a quantum computer. Phys. Rev. Lett., 102(13):130503, 2009. DOI: 10.1103/Phys-RevLett.102.130503.   
[49] D. Poulin and P. Wocjan. Sampling from the thermal quantum Gibbs state and evaluating partition functions with a quantum computer. Physical review letters, 103 (22):220502, 2009. DOI: 10.1103/PhysRevLett.103.220502.   
[50] D. Poulin, A. Kitaev, D. S. Steiger, M. B. Hastings, and M. Troyer. Quantum algorithm for spectral measurement with a lower gate count. Physical review letters, 121 (1):010501, 2018. DOI: 10.1103/PhysRevLett.121.010501.   
[51] E. Y. Remez. Sur la détermination des polynômes d’approximation de degré donnée. Comm. Soc. Math. Kharkov, 10(196):41–63, 1934.   
[52] Y. Saad. Iterative methods for sparse linear systems, volume 82. SIAM, 2003. DOI: 10.1137/1.9780898718003.   
[53] S. Sachdeva and N. K. Vishnoi. Faster algorithms via approximation theory. Theoretical Computer Science, 9(2):125–210, 2013. DOI: 10.1561/0400000065.   
[54] R. D. Somma, S. Boixo, H. Barnum, and E. Knill. Quantum simulations of classical annealing processes. Physical review letters, 101(13):130504, 2008. DOI: 10.1103/Phys-RevLett.101.130504.   
[55] N. H. Stair, R. Huang, and F. A. Evangelista. A multireference quantum krylov algorithm for strongly correlated electrons. arXiv preprint arXiv:1911.05163, 2019. DOI: 10.1021/acs.jctc.9b01125.   
[56] Y. Subaşı, R. D. Somma, and D. Orsucci. Quantum algorithms for systems of linear equations inspired by adiabatic quantum computing. Phys. Rev. Lett., 122:060504, 2019. DOI: 10.1103/PhysRevLett.122.060504.   
[57] M. Szegedy. Quantum speed-up of Markov chain based algorithms. In 45th Annual IEEE symposium on foundations of computer science, pages 32–41. IEEE, 2004. DOI: 10.1109/FOCS.2004.53.   
[58] E. Tang. Quantum-inspired classical algorithms for principal component analysis and supervised clustering. arXiv preprint arXiv:1811.00414, 2018.   
[59] E. Tang. A quantum-inspired classical algorithm for recommendation systems. In Proceedings of the 51st Annual ACM SIGACT Symposium on Theory of Computing, pages 217–228, 2019. DOI: 10.1145/3313276.3316310.   
[60] P. Wocjan and A. Abeyesinghe. Speedup via quantum sampling. Physical Review A, 78(4):042336, 2008. DOI: 10.1103/PhysRevA.78.042336.   
[61] L. Wossnig, Z. Zhao, and A. Prakash. Quantum linear system algorithm for dense matrices. Phys. Rev. Lett., 120(5):050502, 2018. DOI: 10.1103/PhysRevLett.120.050502.   
[62] X. Xu, J. Sun, S. Endo, Y. Li, S. C. Benjamin, and X. Yuan. Variational algorithms for linear algebra. arXiv:1909.03898, 2019.   
[63] T. J. Yoder, G. H. Low, and I. L. Chuang. Fixed-point quantum search with an optimal number of queries. Physical review letters, 113(21):210501, 2014. DOI: 10.1103/Phys-RevLett.113.210501.

# A Block-encoding

The technique of block-encoding has been recently discussed extensively [34, 44]. Here we discuss how to construct block-encoding for $H - \lambda I$ which is used in eigenstate filtering, and $Q _ { b }$ , $H _ { 0 }$ , and $H _ { 1 }$ which are used in QLSP and in particular the Hamiltonian simulation of AQC. We first introduce a simple technique we need to use repeatedly.

Given $U _ { A }$ , an $( \alpha , m , 0 )$ -block-encoding of $A$ where $\alpha > 0$ , we want to construct a block encoding of $A + c I$ for some $c \in \mathbb { C }$ . This is in fact a special case of the linear combination of unitaries (LCU) technique introduced in [21]. Let

$$
Q = \frac { 1 } { \sqrt { \alpha + | c | } } \left( \begin{array} { c c } { { \sqrt { | c | } } } & { { - \sqrt { \alpha } } } \\ { { \sqrt { \alpha } } } & { { \sqrt { | c | } } } \end{array} \right)
$$

and $\left| q \right. = Q \left| 0 \right.$ . Since $( \langle 0 ^ { m } | \otimes I ) U _ { A } ( | 0 ^ { m } \rangle \otimes I ) = A / \alpha$ , we have

$$
( \langle q | \langle 0 ^ { m } | \otimes I \rangle ( | 0 \rangle \langle 0 | \otimes e ^ { i \theta } I + | 1 \rangle \langle 1 | \otimes U _ { A } ) ( | q \rangle | 0 ^ { m } \rangle \otimes I ) = { \frac { 1 } { \alpha + | c | } } ( A + c I ) ,
$$

where $\theta = \arg ( c )$ . Therefore Fig. A1 gives an $( \alpha + | c | , m + 1 , 0 )$ -block-encoding of $e ^ { - i \theta } ( A +$ $c I$ ).

![](images/b5b189ef02303e555eda81fa4d2b36a2906c4200991f8fcb245c9af0d92323a5.jpg)  
Figure A1: Quantum circuit for block-encoding of $e ^ { - i \theta } ( A + c I )$ , where $c = e ^ { i \theta } | c |$ . $R _ { - \theta } = \left. 0 \right. \left. 0 \right. +$ $e ^ { - i \theta } \left| 1 \right. \left. 1 \right|$ is a phase shift gate. The three registers are the ancilla qubit for $Q$ and $| q \rangle$ , the ancilla register of $U _ { A }$ , and the main register, respectively.

Therefore we may construct an $( \alpha + | \lambda | , m + 1 , 0 ) .$ -block-encoding of $H - \lambda I$ . We remark that since $\lambda \in \mathbb { R }$ , we can replace the phase shift gate with a Pauli- $Z$ gate when $\lambda > 0$ . This is at the same time a $( 1 , m + 1 , 0 )$ -block-encoding of $\tilde { H } = ( H - \lambda I ) / ( \alpha + | \lambda | )$ .

Now we construct a block-encoding of $Q _ { b } = I - \left| b \right. \left. b \right|$ with $\left| b \right. = O _ { B } \left| 0 \right.$ . Let $S _ { 0 } =$ $I - 2 \left| 0 ^ { n } \right. \left. 0 ^ { n } \right|$ be the reflection operator about the hyperplane orthogonal to $| 0 ^ { n } \rangle$ . Then $S _ { b } = O _ { B } S _ { 0 } O _ { B } ^ { \dagger } = I - 2 \left. b \right. \left. b \right.$ is the reflection about the hyperplane orthogonal to $| b \rangle$ . Note that $Q _ { b } = ( S _ { b } { + } I ) / 2$ . Therefore we can use the technique illustrated in Fig. A1 to construct a $( 1 , 1 , 0 )$ -block-encoding of $Q _ { b }$ . Here $\begin{array} { r } { | q \rangle = | + \rangle = \frac { 1 } { \sqrt { 2 } } ( | 0 \rangle + | 1 \rangle ) } \end{array}$ . Since $H _ { 0 } = \sigma _ { x } \otimes Q _ { b }$ , we naturally obtain a $( 1 , 1 , 0 )$ -block-encoding of $H _ { 0 }$ . We denote the block-encoding as $U _ { H _ { 0 } }$ .

For the block-encoding of $H _ { 1 }$ , first note that

$$
H _ { 1 } = \left( \begin{array} { c c } { { I } } & { { 0 } } \\ { { 0 } } & { { Q _ { b } } } \end{array} \right) \left( \begin{array} { c c } { { 0 } } & { { A } } \\ { { A } } & { { 0 } } \end{array} \right) \left( \begin{array} { c c } { { I } } & { { 0 } } \\ { { 0 } } & { { Q _ { b } } } \end{array} \right) .
$$

From the block-encoding of $Q _ { b }$ , we can construct the block-encoding of controlled- $Q _ { b }$ by replacing all gates with their controlled counterparts. The block matrix in the middle is $\sigma _ { x } \otimes A$ . For a $d$ -sparse matrix $A$ , we have a $( d , n + 2 , 0 )$ -block-encoding of $A$ , and therefore we obtain a $( d , n + 2 , 0 )$ -block-encoding of $\sigma _ { x } \otimes A$ . Then we can use the result for the product of block-encoded matrix [34, Lemma 30] to obtain a $( d , n + 4 , 0 )$ -block-encoding of $H _ { 1 }$ , denoted by $U _ { H _ { 1 } }$ .

The block-encodings of $H _ { 0 }$ and $H _ { 1 }$ allow us to block-encode linear combinations of them as well. We need access to $H ( f ) = ( 1 - f ) H _ { 0 } + f H _ { 1 }$ which is used extensively in Section 5. This is done through [34, Lemma 29]. When applying the lemma we need the state preparation pair $( P _ { L } , P _ { R } )$ such that

$$
P _ { L } \left| 0 \right. = P _ { R } \left| 0 \right. = \frac 1 { \sqrt { 1 - f + f d } } ( \sqrt { 1 - f } \left| 0 \right. + \sqrt { f d } \left| 1 \right. ) .
$$

The presence of the factor $d$ is because $H _ { 1 }$ is subnormalized by a factor of $d$ in its blockencoding. By this lemma we obtain a $( 1 - f + f d , n + 6 , 0 )$ -block-encoding of $H ( f )$ . Here $1 - f + f d$ comes from the normalizing factor in the state preparation pair, and $n + 6$ is the sum of the numbers of ancilla qubits used in the block-encodings of $H _ { 0 }$ and $H _ { 1 }$ , plus one additional qubit used for the state preparation pair.

# B Implementing the reflection operator and $\theta$ -reflection operator

In this appendix we prove Theorem 4 and Corollary 5 by constructing the quantum circuits. In both the theorem and the corollary we assume, as in Theorem 3, that $H$ is a Hermitian matrix and $U _ { H }$ is an $( \alpha , m , 0 )$ -block-encoding of $H$ . Also $\lambda$ is an eigenvalue of $H$ that is separated from the rest of the spectrum by a gap $\Delta$ .

We first prove Theorem 4 by constructing the circuit for the reflection operator

$$
R _ { \lambda } = 2 P _ { \lambda } - I ,
$$

where $P _ { \lambda }$ is the projection operator into the $\lambda$ -eigenspace of $H$ . To do this we use the following polynomial

$$
S _ { \ell } ( x ; \delta ) = \frac { 2 R _ { \ell } ( x ; \delta ) - 1 } { \operatorname* { m a x } _ { y \in [ - 1 , 1 ] } | 2 R _ { \ell } ( y ; \delta ) - 1 | } .
$$

The first thing we should notice about this polynomial is that it is even and therefore can be implemented via QSP by Theorem $1 ^ { \prime }$ . The normalization is done so that we have $| S _ { \ell } ( x ; \delta ) | ~ \le ~ 1$ for all $x \ \in \ [ - 1 , 1 ]$ . Because $- \epsilon \le \mathrm { m i n } _ { y \in [ - 1 , 1 ] } R _ { \ell } ( y ; \delta ) < 0$ and $\begin{array} { r } { \operatorname* { m a x } _ { y \in [ - 1 , 1 ] } R _ { \ell } ( y ; \delta ) = 1 } \end{array}$ , we have

$$
1 \leq \operatorname* { m a x } _ { y \in [ - 1 , 1 ] } | 2 R _ { \ell } ( y ; \delta ) - 1 | \leq 1 + 2 \epsilon .
$$

Therefore

$$
- 1 - 2 \epsilon \le S _ { \ell } ( x ; \delta ) \le \frac { - 1 + 2 \epsilon } { 1 + 2 \epsilon } \le - 1 + 4 \epsilon , \quad x \in \mathcal { D } _ { \delta } ,
$$

and

$$
1 - 2 \epsilon \le \frac { 1 } { 1 + 2 \epsilon } \le S _ { \ell } ( 0 ; \delta ) \le 1 .
$$

Now for $H$ , we define $\tilde { H } = ( H - \lambda I ) / ( \alpha + | \lambda | )$ and $\tilde { \Delta } = \Delta / 2 \alpha$ as done in the proof of of Theorem 3. Then applying the polynomial $S _ { \ell } ( x ; \tilde { \Delta } )$ to $\tilde { H }$ , because all eigenvalues of $\bar { H }$ are contained in $\mathcal { D } _ { \widetilde { \Delta } } \cup \{ 0 \}$ , they are mapped to either close to $1$ or close to $^ { - 1 }$ . Thus by eEqs. (A1) and (A2) we have

$$
\begin{array} { r } { \| S _ { \ell } ( \widetilde { H } ; \widetilde { \Delta } ) - R _ { \lambda } \| \le 4 \epsilon . } \end{array}
$$

Since $S _ { \ell } ( x ; \tilde { \Delta } )$ is a real even polynomial that takes value in $[ - 1 , 1 ]$ when $x \in \left[ - 1 , 1 \right]$ , we can implement a $( 1 , m + 2 , 0 )$ -block-encoding of $S _ { \ell } ( \widetilde { H } ; \widetilde { \Delta } )$ through QSP by Theorem $1 ^ { \prime }$ . We denote this block-encoding by $\mathcal { U } _ { R }$ . We have

$$
\begin{array} { r } { \| ( \langle 0 ^ { m + 2 } | \otimes I ) \mathcal { U } _ { R } ( | 0 ^ { m + 2 } \rangle \otimes I ) - R _ { \lambda } \| = \| S _ { \ell } ( \widetilde { H } ; \widetilde { \Delta } ) - R _ { \lambda } \| \le 4 \epsilon . } \end{array}
$$

Therefore $\boldsymbol { \mathcal { U } } _ { R }$ is an $( 1 , m + 2 , 4 \epsilon )$ -block-encoding of $R _ { \lambda }$ . Thus we have proved Theorem 4. We then prove Corollary 5 by constructing a block-encoding of the $\theta$ -reflection operator

$$
P _ { \lambda } + e ^ { \mathrm { i } \theta } ( I - P _ { \lambda } ) .
$$

One might be tempted to directly find a polynomial to approximate this matrix function. However such a polynomial would have complex coefficients, and we would need to apply QSP to the real and imaginary parts separately. This in turn needs an extra LCU step to add the two parts up, resulting in reduced success probability. Therefore instead of using a new polynomial, we use the block-encoding $\boldsymbol { { \mathcal { U } } } _ { R }$ we have already constructed, and then apply a 1-bit phase estimation on it. This enables u s to distinguish between the $\lambda$ -eigenspace and its orthogonal complement, since all the eigenvalues of $R _ { \lambda }$ are either 1 or $- 1$ . We then apply the phase factor $e ^ { \mathrm { i } \theta }$ only to the correct subspace. Finally we uncompute the additional ancilla qubit. The circuit takes the following form, as shown in Figure A2:

![](images/5d23d453937a878d5ad1c79f8a8c4f24c3011d4f81519d4c732733e6845bba4c.jpg)  
Figure A2: The quantum circuit for implementing the $\theta$ -reflection operator. H is the Hadamard gate and $\mathrm { R } ( \theta ) = \left| 0 \right. \left. 0 \right| + e ^ { \mathrm { i } \theta } \left| 1 \right. \left. 1 \right|$ is the phase-shift gate.

We introduced one additional ancilla qubit in the initial state $| 0 \rangle$ , and the second register in the above circuit is for the ancilla qubits in Theorem 4. The last register is the main register prepared in the state $| \psi \rangle$ on which we want to apply the operator $P _ { \lambda } + e ^ { \mathrm { i } \theta } ( I - P _ { \lambda } )$ . Thus we have proved Corollary 5.

# C Gate-based implementation of time-optimal adiabatic quantum computing

In Theorem 8 we used an adiabatic time evolution to prepare an initial state for eigenstate filtering. In this appendix we discuss how to implement this time evolution on a gate-based quantum computer. Consider the adiabatic evolution

$$
\frac { 1 } { T } { \mathrm { i } } \partial _ { s } \left| \psi _ { T } ( s ) \right. = H ( f ( s ) ) \left| \psi _ { T } ( s ) \right. , \quad \left| \psi _ { T } ( 0 ) \right. = \left| 0 \right. \left| b \right. ,
$$

Where $H ( f ) = ( 1 - f ) H _ { 0 } + f H _ { 1 }$ for $H _ { 0 }$ and $H _ { 1 }$ defined in (5) and (4). It is proved in [5, 56] that the gap between 0 and the rest of the eigenvalues of $H ( f )$ is lower bounded by $1 - f + f / \kappa$ . With this bound the scheduling (12) in the AQC(p) scheme results in $\mathcal { O } ( \kappa / \epsilon )$ runtime complexity to solve QLSP. As mentioned before, the fact that the $0$ -eigenspace of $H ( f ( s ) )$ is two dimensional is not a problem because $| \psi _ { T } ( t ) \rangle$ is orthogonal to $\left| 1 \right. \left| b \right.$ for all $t$ .

In order to carry out AQC efficiently using a gate-based implementation, we use the recently developed time-dependent Hamiltonian simulation method based on truncated Dyson series introduced in [45]. In Hamiltonian simulation, several types of input models for the Hamiltonian are in use. Hamiltonians can be input as a linear combination of unitaries [10], using its sparsity structure [1, 43], or using its block-encoding [44, 45]. For a time-dependent Hamiltonian Low and Wiebe designed an input model based on blockencoding named HAM-T [45, Definition 2], as a block-encoding of $\begin{array} { r } { \sum _ { s } | s \rangle \langle s | \otimes H ( s ) } \end{array}$ where $s$ is a time step and $H ( s )$ is the Hamiltonian at this time step.

In the gate-based implementation of the time-optimal AQC, we construct HAM-T in Fig. A3. We need to use the block-encodings $U _ { H _ { 0 } }$ and $U _ { H _ { 1 } }$ introduced in Appendix A, which requires $n _ { 0 } = 1$ and $n _ { 1 } = n + 4$ ancilla qubits, respectively. Our construction of HAM-T satisfies

$$
( \langle s | \langle 0 ^ { l + 1 + n _ { 0 } } | \otimes I \otimes \langle 0 ^ { n _ { 1 } + 1 } | ) \mathrm { H A M - T } ( | s \rangle | 0 ^ { l + 1 + n _ { 0 } } \rangle \otimes I \otimes | 0 ^ { n _ { 1 } + 1 } \rangle ) = H ( f ( s ) ) / d ,
$$

for any $s \in \mathcal S = \{ j / 2 ^ { l } : j = 0 , 1 , \ldots , 2 ^ { l } - 1 \}$ .

![](images/bf2d5aba74eaf7c51af7c5c2ebe3ddc0bb2c76e192d81462bd145a1118730f34.jpg)  
Figure A3: Quantum circuit for HAM-T. The registers from top to bottom are: (1) input register for $s$ (2) register for storing $f ( s )$ (3) register for a control qubit (4) ancilla register for $U _ { H _ { 0 } }$ (5) main register for input state $| \phi \rangle$ (6) ancilla register for $U _ { H _ { 1 } }$ (7) register for changing normalizing factor from $\alpha ( s )$ to $d$ .

In this unitary HAM-T we also need the unitary

$$
U _ { f } \left| s \right. \left| z \right. = \left| s \right. \left| z \oplus f ( s ) \right.
$$

to compute the scheduling function needed in the time-optimal AQC, and the unitaries

$$
\begin{array} { l } { { \displaystyle V _ { 1 } = \sum _ { s \in \mathcal { S } } \left| s \right. \left. s \right| \otimes \frac { 1 } { \sqrt { 1 - s + d s } } \left( \begin{array} { c c } { { \sqrt { 1 - s } } } & { { - \sqrt { d s } } } \\ { { \sqrt { d s } } } & { { \sqrt { 1 - s } } } \end{array} \right) } } \\ { { \displaystyle V _ { 2 } = \sum _ { s \in \mathcal { S } } \left| s \right. \left. s \right| \otimes \left( \begin{array} { c c } { { \frac { \alpha \left( s \right) } { d } } } & { { - \sqrt { 1 - \left( \frac { \alpha \left( s \right) } { d } \right) ^ { 2 } } } } \\ { { \sqrt { 1 - \left( \frac { \alpha \left( s \right) } { d } \right) ^ { 2 } } } } & { { \frac { \alpha \left( s \right) } { d } } } \end{array} \right) , \medskip } } \end{array}
$$

where $\alpha ( s ) = 1 - s + d s$ . Here $V _ { 1 }$ is used for preparing the linear combination $( 1 - f ( s ) ) U _ { H _ { 0 } } +$ $f ( s ) U _ { H _ { 1 } }$ . Without $V _ { 2 }$ the circuit would be a $( \alpha ( s ) , l + n _ { 0 } + n _ { 1 } + 2 , 0 )$ -block-encoding of $\begin{array} { r } { \sum _ { s } | s \rangle \langle s | \otimes H ( s ) } \end{array}$ , but with $V _ { 2 }$ it becomes a $( d , l + n _ { 0 } + n _ { 1 } + 2 , 0 )$ -block-encoding, so that the normalizing factor is time-independent, as is required for the input model in [45].

For the AQC with positive definite $A$ we have $n _ { 0 } = 1$ and $n _ { 1 } = n { + } 4$ . For the Hermitian indefinite case we have $n _ { 0 } = 2$ and $n _ { 1 } = n + 4$ . The increase of $n _ { 0 }$ from 1 to 2 is due to the additional operation of linear combination of matrices. For $H _ { 1 }$ we can perform one less matrix-matrix multiplication, and hence the value of $n _ { 1 }$ remains unchanged (see Appendix D).

Following [45, Corollary 4], we may analyze the different components of costs in the Hamiltonian simulation of AQC. For time evolution from $s = 0$ to $s = 1$ , HAM-T is a $( d T , l + n _ { 0 } + n _ { 1 } + 2 , 0 )$ -block-encoding of $\begin{array} { r } { \sum _ { s } | s \rangle \langle s | \otimes T H ( s ) } \end{array}$ . With the scheduling function given in [5] we have $\| T H ( s ) \| = { \mathcal { O } } ( T d )$ and $\| \frac { \mathrm { d } ( T H ( s ) ) } { \mathrm { d } s } \| = \mathcal { O } ( d T \kappa ^ { p - 1 } )$ . We choose $p = 1 . 5$ and by [5, Theorem 1] we have $T = { \mathcal { O } } ( \kappa )$ . We only need to simulate up to constant precision, and therefore we can set $l = \mathcal { O } ( \log ( d \kappa ) )$ . The costs are then

1. Queries to HAM-T: $\mathcal { O } \left( d \kappa \frac { \log ( d \kappa ) } { \log \log ( d \kappa ) } \right)$ ,   
2. Primitive gates: $\mathcal { O } \left( d \kappa ( n + \log ( d \kappa ) ) \frac { \log ( d \kappa ) } { \log \log ( d \kappa ) } \right)$   
3. Qubits: $\mathcal { O } ( n + \log ( d \kappa ) )$ .

# D The matrix dilation method

In Theorem 8 and Theorem 11, in order to extend the time-optimal AQC method, and the QZE-based method to Hermitian indefinite matrices, we follow [5, Theorem 2], where $H _ { 0 }$ and $H _ { 1 }$ , as constructed in Ref. [56] are given by

$$
\begin{array} { r l } & { H _ { 0 } = \sigma _ { + } \otimes [ ( \sigma _ { z } \otimes I _ { N } ) Q _ { + , b } ] + \sigma _ { - } \otimes [ Q _ { + , b } ( \sigma _ { z } \otimes I _ { N } ) ] , } \\ & { H _ { 1 } = \sigma _ { + } \otimes [ ( \sigma _ { x } \otimes A ) Q _ { + , b } ] + \sigma _ { - } \otimes [ Q _ { + , b } ( \sigma _ { x } \otimes A ) ] . } \end{array}
$$

Here $\sigma _ { \pm } = ( \sigma _ { x } \pm i \sigma _ { y } ) / 2$ and $Q _ { + , b } = I _ { 2 N } - \left| + \right. \left| b \right. \left. + \right| \left. b \right|$ . The dimension of the dilated matrices $H _ { 0 } , H _ { 1 }$ is $4 N$ . The lower bound for the gap of $H ( f )$ then becomes $\sqrt { ( 1 - f ) ^ { 2 } + f ^ { 2 } / \kappa ^ { 2 } }$ [56]. However in order to simplify our analysis we give a weaker lower bound

$$
\Delta _ { * } ( f ) = \frac { 1 } { \sqrt { 2 } } \left( 1 - f + \frac { f } { \kappa } \right) ,
$$

which differs from the gap lower bound in (6) by a factor of $\sqrt { 2 }$ . The initial state is $\left| 0 \right. \left| - \right. \left| b \right.$ , where $\begin{array} { r } { | - \rangle = \frac { 1 } { \sqrt { 2 } } ( | 0 \rangle - | 1 \rangle ) } \end{array}$ , and the goal is to obtain $\left| 0 \right. \left| + \right. \left| x \right.$ . In the AQCbased QLSP solver, after running the AQC we can remove the second qubit by measuring it with respect to the $\{ | + \rangle , | - \rangle \}$ basis and accepting the result corresponding to $| + \rangle$ . The resulting query complexity remains unchanged. We remark that the matrix dilation here is only needed for AQC. The eigenstate filtering procedure can still be applied to the original matrix of dimension $2 N$ . The same is true for the QZE-based method.

For a general matrix, we may first consider the extended linear system. Define an extended QLSP ${ \mathfrak { A } } | { \mathfrak { x } } \rangle = | { \mathfrak { b } } \rangle$ in dimension $2 N$ where

$$
\mathfrak { A } = \sigma _ { + } \otimes A + \sigma _ { - } \otimes A ^ { \dagger } = \left( \begin{array} { c c } { { 0 } } & { { A } } \\ { { A ^ { \dagger } } } & { { 0 } } \end{array} \right) , \quad | \mathfrak { b } \rangle = | 0 , b \rangle .
$$

Here $\mathfrak { A }$ is a Hermitian matrix of dimension $2 N$ , with condition number $\kappa$ and $\| \mathfrak { A } \| = 1$ , and $| { \mathfrak { x } } \rangle = | 1 , x \rangle$ solves the extended QLSP. Therefore the time-optimal AQC and the QZE procedure can be applied to the Hermitian matrix $\mathfrak { A }$ to prepare an $\epsilon$ -approximation of $x$ . The dimension of the corresponding $H _ { 0 } , H _ { 1 }$ matrices is $8 N$ . Again the matrix dilation method used in Eq. (A6) is not needed for the eigenstate filtering step.

# E Optimality of the Chebyshev filtering polynomial

In this section we prove Lemma 2. We define

$$
Q _ { \ell } ( x ; \Delta ) = T _ { \ell } \left( - 1 + 2 \frac { x ^ { 2 } - \Delta ^ { 2 } } { 1 - \Delta ^ { 2 } } \right) ,
$$

then $R _ { \ell } ( x ; \Delta ) = Q _ { \ell } ( x ; \Delta ) / Q _ { \ell } ( 0 ; \Delta )$ . Here $T _ { \ell } ( x )$ is the $\ell$ -th Chebyshev polynomial of the first kind and $0 < \Delta < 1$ . We need to use the following lemma, which is similar to the well-known result discussed in [53, Proposition 2.4], [52, Theorem 6.25], and [25, Theorem 7]:

Lemma 12. For any $p ( x ) \in \mathbb { P } _ { 2 \ell } [ x ]$ satisfying $| p ( x ) | \leq 1$ for al l $x \in \mathcal { D } _ { \Delta }$ , where $\mathcal { D } _ { \Delta } =$ $[ - 1 , - \Delta ] \cup [ \Delta , 1 ]$ , $| Q _ { \ell } ( x ; \Delta ) | \geq | p ( x ) |$ for al l $x \notin \mathcal { D } _ { \Delta }$ .

Proof. We prove by contradiction. If there exists $q ( x ) \ \in \ \mathbb { P } _ { 2 \ell } [ x ]$ such that $| q ( x ) | \leq 1$ for all $x \in \mathcal { D } _ { \Delta }$ and there exists $y \notin \mathcal { D } _ { \Delta }$ such that $| q ( y ) | > | Q _ { \ell } ( y ; \Delta ) |$ , then letting $\begin{array} { r } { h ( x ) = Q _ { \ell } ( x ; \Delta ) - q ( x ) \frac { Q _ { \ell } ( y ; \Delta ) } { q ( y ) } } \end{array}$ , we want to show $h ( x )$ has at least $2 \ell + 1$ distinct zeros.

First note that there exist $- 1 = y _ { 1 } < y _ { 2 } < \cdots < y _ { \ell + 1 } = 1$ such that $\left| T _ { \ell } ( y _ { j } ) \right| =$ 1, and $T _ { \ell } ( y _ { j } ) T _ { \ell } ( y _ { j + 1 } ) = - 1$ . Therefore there exist $\Delta = x _ { 1 } < x _ { 2 } < \cdots < x _ { \ell + 1 } = 1$ such that $| Q _ { \ell } ( \pm x _ { j } ; \Delta ) | = 1$ , and $Q _ { \ell } ( x _ { j } ; \Delta ) Q _ { \ell } ( x _ { j + 1 } ; \Delta ) = - 1$ . In other words, $Q _ { \ell } ( \cdot ; \Delta )$ maps each $( x _ { j } , x _ { j + 1 } )$ and $( - x _ { j + 1 } , - x _ { j } )$ to $( - 1 , 1 )$ , and the mapping is bijective for each interval. Because $| \frac { Q _ { \ell } ( y ; \Delta ) } { q ( y ) } | ~ < ~ 1$ , there exists $z _ { j } , w _ { j } \ \in \ ( x _ { j } , x _ { j + 1 } )$ for each $j$ such that $h ( z _ { j } ) = h ( - w _ { j } ) = 0$ . Therefore $\{ z _ { j } \}$ and $\{ - w _ { j } \}$ give us $2 \ell$ distinct zeros. Another zero can be found at $y$ as $h ( y ) = Q _ { \ell } ( y ) - Q _ { \ell } ( y ) = 0$ . Therefore there are $2 \ell + 1$ distinct zeros.

However $h ( x )$ is of degree at most $2 \ell$ . This shows $h ( x ) \equiv 0$ . This is clearly impossible since $\begin{array} { r } { h ( 1 ) = Q _ { \ell } ( 1 ; \Delta ) - q ( 1 ) \frac { Q _ { \ell } ( y ; \Delta ) } { q ( y ) } = 1 - q ( 1 ) \frac { Q _ { \ell } ( y ; \delta ) } { q ( y ) } > 0 } \end{array}$ . □

Lemma 12 shows that for any $y \notin \mathcal { D } _ { \Delta }$ ,

$$
\operatorname* { m a x } _ { \begin{array} { l } { p ( x ) \in \mathbb { P } _ { 2 \ell } [ x ] } \\ { | p ( x ) | \leq 1 , \forall x \in \mathcal { D } _ { \Delta } } \end{array} } | p ( y ) | = | Q _ { \ell } ( y ; \Delta ) | .
$$

This is equivalent to

$$
\operatorname* { m a x } _ { p ( x ) \in \mathbb { P } _ { 2 \ell } [ x ] } \frac { | p ( y ) | } { \operatorname* { m a x } _ { x \in \mathcal { D } _ { \Delta } } | p ( x ) | } = | Q _ { \ell } ( y ; \Delta ) | ,
$$

which is in turn equivalent to

$$
\operatorname* { m i n } _ { p ( x ) \in \mathbb { P } _ { 2 \ell } [ x ] } \frac { \operatorname* { m a x } _ { x \in \mathcal { D } _ { \Delta } } | p ( x ) | } { | p ( y ) | } = \frac { 1 } { | Q _ { \ell } ( y ; \Delta ) | } ,
$$

and

$$
\operatorname* { m i n } _ { \substack { p ( x ) \in \mathbb { P } _ { 2 \ell } [ x ] } } \operatorname* { m a x } _ { x \in \mathcal { D } _ { \Delta } } | p ( x ) | = \frac { 1 } { | Q _ { \ell } ( y ; \Delta ) | } .
$$

This implies (i) of Lemma 2: we only need to set $y = 0$ and observe that

$$
\operatorname* { m a x } _ { x \in \mathcal { D } _ { \Delta } } | R _ { \ell } ( x ; \Delta ) | = \frac { 1 } { | Q _ { \ell } ( 0 ; \Delta ) | } ,
$$

since the Chebyshev polynomials take value between $[ - 1 , 1 ]$ on the interval $[ - 1 , 1 ]$ . From the above discussion we may derive a more general result, that $R _ { \ell } ( x ; \Delta )$ solves the following minimax problem:

$$
\begin{array} { l l } { \displaystyle \operatorname* { m i n i m i z e } _ { p ( x ) \in \mathbb { P } _ { 2 \ell } [ x ] } \operatorname* { m a x } _ { x \in \mathcal { D } _ { \Delta } } | p ( x ) | . } \\ { p ( y ) = R _ { \ell } ( y ; \Delta ) } \end{array}
$$

To prove (ii) of Lemma 2, we need to use the following lemma, which directly follows from [52, Eq. (6.112)]:

Lemma 13. Let $T _ { \ell } ( x )$ be the $\ell$ -th Chebyshev polynomial, then

$$
T _ { \ell } ( 1 + \delta ) \geq { \frac { 1 } { 2 } } e ^ { \ell { \sqrt { \delta } } }
$$

for $0 \leq \delta \leq 3 - 2 { \sqrt { 2 } }$ .

Proof. The Chebyshev polynomial can be rewritten as $\begin{array} { r } { T _ { \ell } ( x ) = \frac { 1 } { 2 } ( z ^ { \ell } + \frac { 1 } { z ^ { \ell } } ) } \end{array}$ for $\begin{array} { r } { x = \frac { 1 } { 2 } ( z + \frac { 1 } { z } ) } \end{array}$ . Let $x = 1 + \delta$ , then $z = 1 + \delta \pm \sqrt { 2 \delta + \delta ^ { 2 } }$ . The choice of $\pm$ does not change the value of $x$ , so we choose $z = 1 + \delta + \sqrt { 2 \delta + \delta ^ { 2 } } \geq 1 + \sqrt { 2 \delta }$ . Since $\log ( 1 + \sqrt { 2 \delta } ) \geq \sqrt { 2 \delta } - \delta \geq \sqrt { \delta }$ for $0 \leq \delta \leq 3 - 2 { \sqrt { 2 } }$ , we have $z ^ { \ell } \geq e ^ { \ell \sqrt { \delta } }$ . Thus $\begin{array} { r } { T _ { \ell } ( x ) \ge \frac { 1 } { 2 } e ^ { \ell \sqrt { \delta } } } \end{array}$ .

We use this lemma to prove (ii). Since $\begin{array} { r } { | T _ { \ell } ( - 1 + 2 \frac { - \Delta ^ { 2 } } { 1 - \Delta ^ { 2 } } ) | \geq T _ { \ell } ( 1 + 2 \Delta ^ { 2 } ) } \end{array}$ , when $\Delta ^ { 2 } \leq 1 / 1 2$ , we have √ ${ \frac { 1 } { 2 } } e ^ { \ell { \sqrt { 2 \Delta ^ { 2 } } } }$ . Since $2 \Delta ^ { 2 } \leq 1 / 6 < 3 - 2 \sqrt { 2 }$ $\begin{array} { r } { | T _ { \ell } ( - 1 + 2 \frac { x ^ { 2 } - \Delta ^ { 2 } } { 1 - \Delta ^ { 2 } } ) | \leq 1 } \end{array}$ . Thus by the above lemma we have for $x \in \mathcal { D } _ { \Delta }$ , we have the inequality in (ii). $\begin{array} { r } { | T _ { \ell } ( - 1 + 2 \frac { - \Delta ^ { 2 } } { 1 - \Delta ^ { 2 } } ) | \geq } \end{array}$ llows $[ - 1 , 1 ]$

# F Properties of the eigenpath

In this section we construct a smooth one-parameter family of normalized quantum states $\{ | x ( f ) \rangle \}$ satisfying Eqs. (7) and (8). $\{ | 0 \rangle | x ( f ) \rangle \}$ then gives an eigenpath of the oneparameter family of Hamiltonians $\{ H ( f ) \}$ . We also prove the inequality (9).

We define

$$
\left. y ( f ) \right. = ( ( 1 - f ) I + f A ) ^ { - 1 } \left. b \right. .
$$

Then $\langle y ( f ) | y ( f ) \rangle \geq 1$ because $\| ( 1 - f ) I + f A \| \leq 1$ . Also $| y ( f ) \rangle$ is a smooth function of $f$ for $f \in ( 0 , 1 )$ because $( 1 - f ) I + f A$ is invertible in this interval, under the assumption that $A$ is Hermitian positive-definite with eigenvalues in $[ 1 / \kappa , 1 ]$ . We construct $| x ( f ) \rangle$ through

$$
| x ( f ) \rangle = c ( f ) | y ( f ) \rangle ,
$$

with $c ( f )$ solving the following ODE

$$
c ^ { \prime } ( f ) = - c ( f ) \frac { \langle y ( f ) | \partial _ { f } | y ( f ) \rangle } { \langle y ( f ) | y ( f ) \rangle } , \quad c ( 0 ) = 1 .
$$

This is a linear ODE and the right-hand side depends smoothly on $f$ . Therefore the solution exists and is unique for $f \in \left[ 0 , 1 \right]$ . It then follows that this construction of $| x ( f ) \rangle$ satisfies (7). Since

$$
\partial _ { f } \left| x ( f ) \right. = c ^ { \prime } ( f ) \left| y ( f ) \right. + c ( f ) \partial _ { f } \left| y ( f ) \right. ,
$$

we have

$$
\langle x ( f ) | \partial _ { f } | x ( f ) \rangle = c ^ { * } ( f ) [ c ^ { \prime } ( f ) \langle y ( f ) | y ( f ) \rangle + c ( f ) \langle y ( f ) | \partial _ { f } | y ( f ) \rangle ] = 0 .
$$

Therefore Eq. (8) is satisfied, and this in turn ensures $| x ( f ) \rangle$ is normalized. In this way we have constructed $\{ | x ( f ) \rangle \}$ that satisfies all the requirements in Section 4.1. For $H ( f ) =$ $( 1 - f ) H _ { 0 } + f H _ { 1 }$ , where $H _ { 0 }$ and $H _ { 1 }$ are defined in Eqs. (5) and (4) respectively, we can see $H ( f ) \left| \bar { x } ( f ) \right. = 0$ where $\left| \bar { x } ( f ) \right. = \left| 0 \right. \left| x ( f ) \right.$ . Therefore $\{ | \bar { x } ( f ) \rangle \}$ is a smooth eigenpath.

If there is another eigenpath $\{ | 0 \rangle | w ( f ) \rangle \}$ satisfying $\langle w ( f ) | \partial _ { f } | w ( f ) \rangle = 0$ , then it follows that $( ( 1 - f ) I + f A ) \left| w ( f ) \right. \propto \left| b \right.$ . Therefore $| w ( f ) \rangle = e ^ { \mathrm { i } \theta ( f ) } \left| x ( f ) \right.$ for some differentiable $\theta ( f )$ . By the geometric phase condition we can show $e ^ { \mathrm { i } \theta ( f ) } = 1$ for all $f$ by also taking into account the initial condition $| w ( f ) \rangle = | b \rangle$ , and therefore $| w ( f ) \rangle = | x ( f ) \rangle$ . This proves uniqueness.

Now we denote by $\varepsilon _ { j } ( f )$ the eigenvalues of $H ( f )$ . The corresponding eigenstates are denoted by $| w _ { j } ( f ) \rangle$ . Because $( ( 1 - f ) I + f A ) \left| x ( f ) \right. \propto \left| b \right.$ , we have $H ( f ) \left| \bar { x } ( f ) \right. = 0$ . Since $| x ( f ) \rangle$ , and as a result $| \bar { x } ( f ) \rangle$ , is differentiable, taking derivative with respect to $f$ we have

$$
H ^ { \prime } ( f ) \left| \bar { x } ( f ) \right. + H ( f ) \partial _ { f } \left| \bar { x } ( f ) \right. = 0 .
$$

Therefore

$$
\langle w _ { j } ( f ) | H ^ { \prime } ( f ) | \bar { x } ( f ) \rangle + \langle w _ { j } ( f ) | H ( f ) \partial _ { f } | \bar { x } ( f ) \rangle = 0 .
$$

And this leads to

$$
\langle w _ { j } ( f ) | \partial _ { f } | \bar { x } ( f ) \rangle = - \frac { \langle w _ { j } ( f ) | H ^ { \prime } ( f ) | \bar { x } ( f ) \rangle } { \varepsilon _ { j } ( f ) }
$$

for any $j$ such that $\varepsilon _ { j } ( f ) \neq 0$ . The null space of $H ( f )$ is spanned by $\left| 1 \right. \left| b \right.$ and $| \bar { x } ( f ) \rangle$ . We have $(  1 |  b |  | \bar { x } ( f )  =  1 | 0   b | x ( f )  = 0$ , and $\langle \bar { x } ( f ) | \partial _ { f } | \bar { x } ( f ) \rangle = 0$ because of the geometric phase condition (8). Since all $| w _ { j } ( f ) \rangle$ such that $\varepsilon _ { j } ( f ) \neq 0$ , together with $\left| 1 \right. \left| b \right.$ and $\vert \bar { x } ( f ) \rangle$ form a basis of the Hilbert space, we have

$$
\partial _ { f } \left| \bar { x } ( f ) \right. = - \sum _ { j : \varepsilon _ { j } ( f ) \neq 0 } \frac { | w _ { j } ( f ) \rangle \left. w _ { j } ( f ) | H ^ { \prime } ( f ) | \bar { x } ( f ) \right. } { \varepsilon _ { j } ( f ) }
$$

Therefore

$$
\begin{array} { l } { \displaystyle | | \partial _ { f } | \bar { x } ( f ) \rangle | | ^ { 2 } = \displaystyle \sum _ { j : \varepsilon _ { j } ( f ) \neq 0 } \frac { | \langle w _ { j } ( f ) | H ^ { \prime } ( f ) | \bar { x } ( f ) \rangle | ^ { 2 } } { \varepsilon _ { j } ^ { 2 } ( f ) } } \\ { \displaystyle \qquad \leq \frac { 1 } { \Delta _ { * } ( f ) ^ { 2 } } \sum _ { j : \varepsilon _ { j } ( f ) \neq 0 } | \langle w _ { j } ( f ) | H ^ { \prime } ( f ) | \bar { x } ( f ) \rangle | ^ { 2 } } \\ { \displaystyle \qquad \leq \frac { 1 } { \Delta _ { * } ( f ) ^ { 2 } } \| H ^ { \prime } ( f ) | \bar { x } ( f ) \rangle \| ^ { 2 } } \end{array}
$$

From the definition of $H ( f )$ it can be seen that $\| H ^ { \prime } ( f ) \| \leq 2$ . Therefore we have proved the inequality (9).

# G Success probability of Quantum Zeno effect QLSP algorithm

In this appendix we rigorously prove a constant success probability lower bound for the QZE-based QLSP algorithm in Theorem 11. In Section 5.2 we gave a simpler but nonrigorous proof of a constant success probability lower bound by assuming the projection for each $H ( f _ { j } )$ is done without error, i.e. $\epsilon _ { P } = 0$ . Here we do not make such an assumption and show we can still find such a lower bound. We will need to use the following elementary inequality, which can be easily proved using induction.

Lemma 14. If $0 < a _ { j } < 1$ , $0 < b _ { j } < 1$ , $j = 0 , 1 , 2 , \ldots , R - 1$ , then

$$
\prod _ { j = 0 } ^ { R - 1 } ( a _ { j } - b _ { j } ) \geq \prod _ { j = 0 } ^ { R - 1 } a _ { j } - \sum _ { j = 0 } ^ { R - 1 } b _ { j } .
$$

We first recall the definition of the sequence of quantum states $\{ | x ( f _ { j } ) \rangle \}$ , with each $| x ( f _ { j } ) \rangle$ defined through (7) and (8), satisfying $H ( f _ { j } ) \left| 0 \right. \left| x ( f _ { j } ) \right. = 0$ , and the sequence of quantum states $\{ | \widetilde { x } ( f _ { j } ) \rangle \}$ , with each $| \widetilde { x } ( f _ { j } ) \rangle$ defined recursively by (19). We need to use

the following bound for the overlap between $| x ( f _ { j } ) \rangle$ and $| x ( f _ { j + 1 } ) \rangle$ derived from Eqs. (20) (21) and (15).

$$
| \left. x ( f _ { j } ) | x ( f _ { j + 1 } ) \right. | \geq 1 - { \frac { 1 } { 2 } } \| | x ( f _ { j + 1 } ) \rangle - | x ( f _ { j } ) \rangle \| ^ { 2 } \geq 1 - { \frac { 2 \log ^ { 2 } ( \kappa ) } { M ^ { 2 } ( 1 - 1 / \kappa ) ^ { 2 } } } .
$$

With these tools we will first bound several overlaps in the following lemma

Lemma 15. When $\begin{array} { r } { M \geq \frac { 4 \log ^ { 2 } ( \kappa ) } { ( 1 - 1 / \kappa ) ^ { 2 } } } \end{array}$ and $\epsilon { } _ { P } \leq \frac { 1 } { 1 2 8 }$ , we have for $j = 0 , 1 , \ldots , M - 1$

(i) $\begin{array} { r } { |  x ( f _ { j } ) | x ( f _ { j + 1 } \rangle ) | \ge 1 - \frac { 1 } { 2 M } } \end{array}$ , (ii) $| \left. x ( f _ { j } ) | \widetilde x ( f _ { j } ) \right. | \ge 1 - 4 \epsilon _ { P } .$ , (iii) $\begin{array} { r } { | \langle \widetilde { x } ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle | \geq 1 - \frac { 1 } { 2 M } - 4 \epsilon _ { P } - 2 \sqrt { 2 \epsilon _ { P } } . } \end{array}$

Proof. (i) derives directly from (A8). We then want to derive (ii) and (iii) inductively. First we have

$$
\begin{array} { r l } & { | \langle \widetilde { x } ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle | = | \langle \widetilde { x } ( f _ { j } ) | P _ { 0 } ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle + \langle \widetilde { x } ( f _ { j } ) | I - P _ { 0 } ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle | } \\ & { \qquad \ge | \langle x ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle | \cdot | \langle x ( f _ { j } ) | \widetilde { x } ( f _ { j } ) \rangle | - \| ( I - P _ { 0 } ( f _ { j } ) ) | \widetilde { x } ( f _ { j } ) \rangle | . } \end{array}
$$

Because

$$
\begin{array} { r } { \| \vert - P _ { 0 } ( f _ { j } ) ) \vert \widetilde { x } ( f _ { j } ) \rangle \| ^ { 2 } = 1 - \vert \langle x ( f _ { j } ) \vert \widetilde { x } ( f _ { j } ) \rangle \vert ^ { 2 } , } \end{array}
$$

we then have

$$
| \langle \widetilde { x } ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle | \ge | \langle x ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle | \cdot | \langle x ( f _ { j } ) | \widetilde { x } ( f _ { j } ) \rangle | - \sqrt { 1 - | \langle x ( f _ { j } ) | \widetilde { x } ( f _ { j } ) \rangle | ^ { 2 } } .
$$

We denote

$$
| \left. x ( f _ { j } ) | \widetilde x ( f _ { j } ) \right. | = 1 - \nu _ { j } ,
$$

then

$$
\begin{array} { r l r } {  { | \langle \widetilde { x } ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle | \geq ( 1 - \frac { 1 } { 2 M } ) ( 1 - \nu _ { j } ) - \sqrt { 1 - ( 1 - \nu _ { j } ) ^ { 2 } } } } \\ & { } & { \geq 1 - \frac { 1 } { 2 M } - \nu _ { j } - \sqrt { 2 \nu _ { j } } . } \end{array}
$$

We now bound $\nu _ { j + 1 }$ using $\mid \langle \widetilde { x } ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle \mid$ . First using the fact that $\| \widetilde { P } _ { 0 } ( f _ { j } ) -$ $P _ { 0 } ( f _ { j } ) \parallel \le \epsilon _ { P }$ ewhere the approximate projection operator $\tilde { P } _ { 0 } ( f _ { j } )$ is defined in Eq. (18), we have

$$
\begin{array} { r l } & { | \left. \tilde { x } ( f _ { j + 1 } ) | x ( f _ { j + 1 } ) \right. | = \frac { | \left. \tilde { x } ( f _ { j } ) | \tilde { P } _ { 0 } ( f _ { j + 1 } ) | x ( f _ { j + 1 } ) \right. | } { \| \tilde { P } _ { 0 } ( f _ { j + 1 } ) | \tilde { x } ( f _ { j } ) \rangle | } } \\ & { \qquad \ge \frac { | \left. \tilde { x } ( f _ { j } ) | P _ { 0 } ( f _ { j + 1 } ) | x ( f _ { j + 1 } ) \right. | - \epsilon _ { P } } { \| P _ { 0 } ( f _ { j + 1 } ) | \tilde { x } ( f _ { j } ) \rangle | + \epsilon _ { P } } } \\ & { \qquad = \frac { | \left. \tilde { x } ( f _ { j } ) | x ( f _ { j + 1 } ) \right. | - \epsilon _ { P } } { | \left. \tilde { x } ( f _ { j } ) | x ( f _ { j + 1 } ) \right. | + \epsilon _ { P } } } \\ & { \qquad \ge 1 - \frac { 2 \epsilon _ { P } } { | \left. \tilde { x } ( f _ { j } ) | x ( f _ { j + 1 } ) \right. | } . } \end{array}
$$

This leads to

$$
\nu _ { j + 1 } \leq \frac { 2 \epsilon _ { P } } { | \langle \widetilde { x } ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle | } \leq \frac { 2 \epsilon _ { P } } { 1 - \frac { 1 } { 2 M } - \nu _ { j } - \sqrt { 2 \nu _ { j } } } ,
$$

which establishes a recurrence relation for $\nu _ { j }$ . Because $\nu _ { 0 } = 0$ , $\begin{array} { r } { M \ge \frac { 4 \log ^ { 2 } ( \kappa ) } { ( 1 - 1 / \kappa ) ^ { 2 } } \ge 4 } \end{array}$ and $\epsilon { } _ { P } \leq \frac { 1 } { 1 2 8 }$ , we can prove inductively that $\begin{array} { r } { \nu _ { j } \leq \frac { 1 } { 3 2 } } \end{array}$ . Taking this into (A11) we have

$$
\nu _ { j + 1 } \leq 4 \epsilon _ { P } ,
$$

which proves (ii). Taking this into (A9) we have (iii).

An immediate corollary of (iii) in the above lemma is

$$
| \langle \widetilde { x } ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle | \ge 1 - \frac { 1 } { 2 M } - 4 \epsilon _ { P } - 2 \sqrt { 2 \epsilon _ { P } } \ge \frac { 1 } { 2 } ,
$$

for $j = 0 , 1 , \ldots , M - 1$ , $M \geq 4$ , and $\epsilon _ { P } \leq 1 / 1 2 8$ . With these tools we are now ready to estimate the success probability $p _ { \mathrm { s u c c e s s } }$ . We have

$$
\begin{array} { r l } { \mu _ { \mathrm { S a r c e s } } } & { = \displaystyle \sum _ { j = 1 } ^ { M - 1 } \| \widehat { P } _ { 1 } ( f _ { j - 1 } ) \| ^ { \mathcal { X } } ( f _ { j } ) \| ^ { 2 } } \\ & { \geq \left( \displaystyle \prod _ { j = 0 } ^ { M - 2 } \left( \| F _ { 0 } ( f _ { j + 1 } ) \| \widehat { x } ( f _ { j } ) \| - \epsilon _ { P } \right) \right) ^ { 2 } \left( \| F _ { 0 } ( 1 ) \| \widehat { x } ( f _ { M - 1 } ) \| - \frac { \epsilon _ { P } } { 4 } \right) ^ { \lambda } } \\ & { \geq \displaystyle \frac { 1 } { 1 6 } \left( \displaystyle \prod _ { j = 0 } ^ { M - 2 } \left( \| F _ { 0 } ( f _ { j - 1 } ) \| \widehat { x } ( f _ { j } ) \| - \epsilon _ { P } \right) \right) ^ { 2 } \left( \| F _ { 0 } ( 1 ) \| \widehat { x } ( f _ { M - 1 } ) \| - \frac { \epsilon _ { P } } { 4 } \right) ^ { \lambda } } \\ & { \geq \displaystyle \frac { 1 } { 1 6 } \left( \displaystyle \prod _ { j = 0 } ^ { M - 1 } \left( \| F _ { 0 } ( f _ { j - 1 } ) \| \widehat { x } ( f _ { j } ) \| - \epsilon _ { P } \right) \right) ^ { 2 } } \\ & { \geq \displaystyle \frac { 1 } { 1 6 } \left( \displaystyle \prod _ { j = 0 } ^ { M - 1 } \left( \| F _ { 0 } ( f _ { j - 1 } ) \| \widehat { x } ( f _ { j } ) \| - \epsilon _ { P } \right) \right) ^ { 2 } } \\ & { \geq \displaystyle \frac { 1 } { 1 6 } \left( \displaystyle \prod _ { j = 0 } ^ { M - 1 } \| F _ { 0 } ( f _ { j } ) \| \widehat { x } ( f _ { j } ) \| - M \epsilon _ { P } \right) ^ { 2 } . } \end{array}
$$

In the last line we have used Lemma 14. In the second line the $j = M - 1$ case is treated differently because in the last step we need to attain $\epsilon / 4$ precision for eigenstate filtering. We bound the success probability of the last step using

$$
( \lVert P _ { 0 } ( 1 ) | \widetilde { x } ( f _ { M - 1 } )   - \frac { \epsilon } { 4 } ) ^ { 2 } = ( \lVert  x ( f _ { M } ) | \widetilde { x } ( f _ { M - 1 } )  \rVert - \frac { \epsilon } { 4 } ) ^ { 2 } \geq ( \frac { 1 } { 2 } - \frac { 1 } { 4 } ) ^ { 2 } = \frac { 1 } { 1 6 } ,
$$

where we have used Eq. (A12) for $j = M - 1$ . This inequality motivates us to bound $\Pi _ { j = 0 } ^ { M - 1 } \parallel P _ { 0 } ( f _ { j + 1 } ) \left| \widetilde { x } ( f _ { j } ) \right. \parallel$ , for which, by Lemma 15, we have

$$
\begin{array} { l } { \displaystyle \prod _ { j = 0 } ^ { M - 1 } \| P _ { 0 } ( f _ { j + 1 } ) | \tilde { x } ( f _ { j } ) \rangle \| = \displaystyle \prod _ { j = 0 } ^ { M - 1 } | \langle \tilde { x } ( f _ { j } ) | x ( f _ { j + 1 } ) \rangle | } \\ { \displaystyle \qquad \ge \left( 1 - \frac { 1 } { 2 M } - 4 \epsilon _ { P } - 2 \sqrt { 2 \epsilon _ { P } } \right) ^ { M } } \\ { \displaystyle \qquad \ge \frac { 1 } { 2 } - M ( 4 \epsilon _ { P } + 2 \sqrt { 2 \epsilon _ { P } } ) . } \end{array}
$$

In Lemma 15 we have required that $\epsilon { } _ { P } \leq \frac { 1 } { 1 2 8 }$ and $\begin{array} { r } { M \ge \frac { 4 \log ^ { 2 } ( \kappa ) } { ( 1 - 1 / \kappa ) ^ { 2 } } \ge 4 } \end{array}$ . Therefore when we further require $\begin{array} { r } { \epsilon _ { P } \leq \frac { 1 } { 1 6 2 M ^ { 2 } } } \end{array}$ we have

$$
\prod _ { j = 0 } ^ { M - 1 } \| P _ { 0 } ( f _ { j + 1 } ) | \widetilde { x } ( f _ { j } ) \rangle \| \ge \frac { 1 } { 4 } .
$$

Substituting this into (A13) we have

$$
p _ { \mathrm { s u c c e s s } } \geq \frac { 1 } { 1 6 } \left( \frac { 1 } { 4 } - M \epsilon _ { P } \right) ^ { 2 } \geq \frac { 1 } { 1 6 } \left( \frac { 1 } { 4 } - \frac { 1 } { 1 6 2 M } \right) ^ { 2 } \geq \frac { 1 } { 4 0 0 } ,
$$

since $M \ge 4 > 1$ . We remark that because we mostly only care about the asymptotic complexity we did not bound this probability very tightly, and this bound may be a very loose one. The actual success probability can be much larger than this and can be further increased by optimizing the choice of $M$ and $\epsilon _ { P }$ .