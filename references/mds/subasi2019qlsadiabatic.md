# Quantum algorithms for systems of linear equations inspired by adiabatic quantum computing

Yi˘git Suba¸sı and Rolando D. Somma Theoretical Division, Los Alamos National Laboratory, Los Alamos, NM 87545, US.

Davide Orsucci Department of Theoretical Physics, University of Innsbruck, Innsbruck, Austria. (Dated: November 30, 2018)

We present two quantum algorithms based on evolution randomization, a simple variant of adiabatic quantum computing, to prepare a quantum state $| x \rangle$ that is proportional to the solution of the system of linear equations $A { \overrightarrow { x } } = { \overrightarrow { b } }$ . The time complexities of our algorithms are $O ( \kappa ^ { 2 } \log ( \kappa ) / \epsilon )$ and $O ( \kappa \log ( \kappa ) / \epsilon )$ , where $\kappa$ is the condition number of $A$ and $\epsilon$ is the precision. Both algorithms are constructed using families of Hamiltonians that are linear combinations of products of $A$ , the projector onto the initial state $| b \rangle$ , and single-qubit Pauli operators. The algorithms are conceptually simple and easy to implement. They are not obtained from equivalences between the gate model and adiabatic quantum computing. They do not use phase estimation or variable-time amplitude amplification, and do not require large ancillary systems. We discuss a gate-based implementation via Hamiltonian simulation and prove that our second algorithm is almost optimal in terms of $\kappa$ . Like previous methods, our techniques yield an exponential quantum speedup under some assumptions. Our results emphasize the role of Hamiltonian-based models of quantum computing for the discovery of important algorithms.

PACS numbers: 03.67.Ac, 03.67.Lx, 03.65.Xp, 89.70.Eg

Introduction. Recently, there has been significant interest in quantum algorithms to solve various linear algebra problems [1–5], as quantum computers can implement certain linear transformations more efficiently than their classical counterparts. Such algorithms may find applications in a wide range of topics, including machine learning [6–8], graph problems [9], solving differential equations [10], and physics problems [11, 12]. A main example is the algorithm of Harrow, Hassidim, and Lloyd (HHL) of Ref. [1] for the so-called quantum linear systems problem (QLSP), where the goal is to prepare a quantum state $| x \rangle$ that is proportional to the solution of a system of linear equations $A { \overrightarrow { x } } = { \overrightarrow { b } }$ . If the $N \times N$ matrix $A$ and $N$ -dimensional vector $\vec { b }$ are sparse, and for constant precision, the complexity of the algorithm in Ref. [1] is polynomial in $\log N$ and $\kappa$ , where $\kappa$ is the condition number of $A$ . In contrast, classical algorithms to invert matrices are of complexity polynomial in $N$ , suggesting that quantum computers would be able to solve certain problems related to systems of linear equations exponentially faster than classical computers. Improvements of the HHL algorithm can be found in Refs. [3–5].

The referenced algorithms are described in the standard gate-based model of quantum computing, where quantum states are prepared by applying a sequence of elementary (e.g., two-qubit) gates to some initial state. However, Hamiltonian-based alternatives to the gatebased model exist, such as adiabatic quantum computing (AQC) [13]. One advantage of considering these other alternatives is that new and simple quantum algorithms can be found, even if such algorithms will ultimately be implemented using a different but equivalent model.

In AQC, for example, the computation is performed by smoothly changing the parameters of a Hamiltonian that evolves a quantum system. The adiabatic theorem asserts that if the continuously related eigenstates remain non-degenerate and the Hamiltonians change sufficiently slowly, then the evolved state is sufficiently close to the eigenstate of the final Hamiltonian [14]. Such an eigenstate encodes information about the solution to a problem; in our case the final eigenstate would be $| x \rangle$ (or $| \phi \rangle \otimes | x \rangle$ if ancillas are used). A closely related method is the randomization method (RM) described in Ref. [15]. Both, AQC and RM are examples of eigenpath traversal [16]. Nevertheless, an advantage of the RM with respect to AQC is that better convergence guarantees can sometimes be obtained, as shown in Refs. [17, 18].

In this paper, we develop two simple quantum algorithms that solve the QLSP based on the RM. To this end, we construct families of simple Hamiltonians whose continuously related eigenstates connect $| b \rangle$ , the quantum state proportional to $\vec { b }$ , with $| x \rangle$ . The average evolution times of our algorithms, i.e. the time complexities, are nearly order $\kappa ^ { 2 }$ and $\kappa$ , respectively. Here $\kappa$ is the condition number of $A$ . Additionally, the time complexities of both algorithms are linear in $1 / \epsilon$ , where $\epsilon$ is a precision parameter. In contrast to previous approaches, our algorithms do not use any form of phase estimation, amplitude amplification, or function approximation, thus reducing the number of ancillary qubits significantly.

Our first quantum algorithm solves the QLSP by preparing the lowest-energy states of a family of Hamiltonians, whereas our second algorithm achieves this by preparing energy states that lie exactly at the middle of the spectrum, i.e., excited states. Our second algorithm is noteworthy in that it is almost optimal, having time complexity almost linear in $\kappa$ .

Although the Hamiltonians are simple, actual implementations of our algorithms on analog quantum computing devices may be impractical. However, the quantum algorithms could still be implemented in the gatebased model by using the Hamiltonian simulation results of Refs. [19–21]. This will require oracle access to the matrix $A$ as well as a procedure to prepare the state $| b \rangle$ . A resulting gate-model algorithm for the QLSP following this procedure will be nearly optimal according to Ref. [1]. That is, like Refs. [3, 4], the query complexity is almost linear in $\kappa$ , a quadratic improvement over that of the HHL algorithm. We give more specifics below.

Quantum linear systems problem. The QLSP in Refs. [1, 3, 4] is stated as follows. We are given an $N \times N$ Hermitian matrix $A$ and a vector $\vec { b } = ( b _ { 1 } , \ldots , b _ { N } ) ^ { T }$ , with $N = 2 ^ { n }$ . The goal is to prepare an $\epsilon$ -approximation of a quantum state

$$
| x \rangle : = \frac { \sum _ { j = 1 } ^ { N } x _ { j } | j \rangle } { \sqrt { \sum _ { j = 1 } ^ { N } | x _ { j } | ^ { 2 } } } = \frac { \left( 1 / A \right) | b \rangle } { \left. \left( 1 / A \right) | b \rangle \right. } \mathrm { ~ , ~ }
$$

system where $\vec { x } = ( x _ { 1 } , \ldots , x _ { N } ) ^ { T }$ $A { \overrightarrow { x } } = { \overrightarrow { b } }$ $\begin{array} { r } { | b \rangle \ \propto \ \sum _ { j = 1 } ^ { N } b _ { j } \left| j \right. } \end{array}$ is the solution to the linear , and $0 ~ < ~ \epsilon ~ < ~ 1$ is $A$ having condition number $\kappa ~ < ~ \infty$ , and $\| A \| \leq 1$ . The approximated state $| \tilde { x } \rangle$ satisfies $\| | \tilde { x } \rangle - | x \rangle \| \leq \epsilon$ . Here, we consider a slightly modified version of this problem where the goal is to prepare a mixed state $\rho _ { x }$ such that the trace distance satisfies

$$
\frac { 1 } { 2 } \mathrm { T r } | \rho _ { x } - | x \rangle \langle x | | \leq \epsilon .
$$

Note that this modified version is adequate since the ultimate purpose of the QLSP is for obtaining expectation values of observables. Thus, both $| \tilde { x } \rangle$ and $\rho _ { x }$ will provide same-order approximations for such calculations.

Algorithm evolving on ground states. We first define the family of Hamiltonians

$$
{ \cal H } ( s ) : = A ( s ) P _ { \bar { b } } ^ { \perp } A ( s ) .
$$

Here, $A ( s ) : = ( 1 - s ) Z \otimes \mathbb { 1 } + s X \otimes A$ , $\vert b \rangle : = \vert + , b \rangle$ , $P _ { \bar { b } } ^ { \perp } : = 1 1 - | \bar { b } \rangle \langle \bar { b } |$ , and $s \in \lbrack 0 , 1 ]$ is a parameter. $X$ and $Z$ are single-qubit Pauli operators. These Hamiltonians act on a Hilbert space of dimension $2 N$ , i.e., the space of $A$ plus one ancilla qubit. The reason for using an ancilla is to guarantee that $A ( s )$ is invertible for all $s$ .

We introduce the family of states

$$
| x ( s ) \rangle : = { \frac { 1 / ( A ( s ) ) \left| \bar { b } \right. } { \| 1 / ( A ( s ) ) \left| \bar { b } \right. \| } } ,
$$

which satisfy $H ( s ) \left| x ( s ) \right. = 0$ . In Supp. Mat. we show that $| x ( s ) \rangle$ is the unique ground state of $H ( s )$ and the energy gap satisfies $\Delta ( s ) \geq \Delta ^ { * } ( s ) : = ( 1 - s ) ^ { 2 } + ( s / \kappa ) ^ { 2 }$ . As $s$ is increased from $0$ to $1$ , the ground state continuously changes from $| x ( 0 ) \rangle = | - , b \rangle$ to $| x ( 1 ) \rangle = | + , x \rangle$ . Exact preparation of $| x ( 1 ) \rangle$ implies exact preparation of the target state $| x \rangle$ by discarding the ancillary qubit.

In the case $A > 0$ , we can opt for the simpler choice $A ( s ) : = ( 1 - s ) \mathbb { 1 } + s A$ , and still have $A ( s )$ non-singular for all $s$ . Then, $\left| x ( s ) \right. \propto A ( s ) ^ { - 1 } \left| b \right.$ is the unique ground state of $H ( s )$ . The following analysis is for general $A$ .

Randomization method. The details of the RM as well as its complexity analysis can be found in Ref. [15]. Here, we mainly study and describe how to use the RM to solve the QLSP. Roughly, the method can be viewed as a version of AQC, where the parameter $s$ is changed discretely rather than continuously, and the Hamiltonian evolution is for a random time. This process effectively simulates an approximate projective measurement of the desired ground state (or any other eigenstate). It then allows to make transformations within the ground states (eigenstates) of the Hamiltonians. The time complexity of the RM in general is $O ( L ^ { 2 } / ( \epsilon \Delta ) )$ , where $L$ is the socalled path length (which we define later), and $\Delta$ is the minimum gap of the Hamiltonians. We observe that the dependence on $\Delta$ is optimal [18], while general bounds for AQC provide a worse time complexity of ${ \cal O } ( 1 / \Delta ^ { 3 } )$ [22]. This observation is key to achieve our results. Then, obtaining the actual time complexity for the QLSP requires studying the properties of the Hamiltonians $H ( s )$ and eigenstates $| x ( s ) \rangle$ . With this information, we can find discrete values of $s$ as well as values for the evolution times needed to implement the RM.

The full complexity analysis for the QLSP is given in Supp. Mat.. According to Refs. [15, 16, 18], to obtain the discrete values of $s$ , it is convenient to work with a “natural” parametrization $s ( v )$ . This is defined so that the norm of the rate of change of the eigenstate with respect to $v$ can be bounded by a constant. We find that a natural parametrization for this case is

$$
s ( v ) : = \frac { e ^ { v \frac { \sqrt { 1 + \kappa ^ { 2 } } } { \sqrt { 2 } \kappa } } + 2 \kappa ^ { 2 } - \kappa ^ { 2 } e ^ { - v \frac { \sqrt { 1 + \kappa ^ { 2 } } } { \sqrt { 2 } \kappa } } } { 2 ( 1 + \kappa ^ { 2 } ) } .
$$

Here, $v _ { a } \le v \le v _ { b }$ , with

$$
\begin{array} { r c l } { { } } & { { } } & { { v _ { a } : = \displaystyle \frac { \sqrt { 2 } \kappa } { \sqrt { 1 + \kappa ^ { 2 } } } \log ( \kappa \sqrt { 1 + \kappa ^ { 2 } } - \kappa ^ { 2 } ) \ : , \hfill } } \\ { { } } & { { } } & { { v _ { b } : = \displaystyle \frac { \sqrt { 2 } \kappa } { \sqrt { 1 + \kappa ^ { 2 } } } \log ( \sqrt { 1 + \kappa ^ { 2 } } + 1 ) \ : . \hfill } } \end{array}
$$

The discrete values $s ^ { j } = s ( v ^ { j } )$ are obtained from discrete values of $\boldsymbol { v }$ , which are evenly distributed in $q$ points as $v _ { a } < v ^ { 1 } < v ^ { 2 } < \ldots < v ^ { q } = v _ { b }$ . Here, $v ^ { j } = v _ { a } + j \delta$ $( j ~ = ~ 1 , \ldots , q )$ and $s ^ { 0 } = s ( v _ { a } ) = 0$ , $s ^ { q } = s ( v _ { b } ) = 1$ . The number of steps of the RM is $q = \Theta ( \log ^ { 2 } ( \kappa ) / \epsilon )$ , and $\delta = ( v _ { b } - v _ { a } ) / q$ . The choice of $q$ implies

$$
1 - | \langle x ( s ^ { j } ) | x ( s ^ { j + 1 } ) \rangle | ^ { 2 } = O ( \epsilon / q ) .
$$

That is, a sequence of $q$ projective measurements of $| x ( s ^ { j } ) \rangle$ , starting from $| x ( 0 ) \rangle$ , will produce $| x ( 1 ) \rangle$ with probability $1 - O ( \epsilon )$ . These measurements are simulated by evolution randomization.

Our algorithm is as follows. At each step $j = 1 , \dotsc , q$ , we evolve with the Hamiltonian $H ( s ^ { j } )$ for a random time $t ^ { j }$ . The evolution time can be sampled from the uniform distribution $t ^ { j } \in [ 0 , 2 \pi / \Delta ^ { * } ( s ^ { j } ) ]$ [15, 18] and satisfies $\left. t ^ { j } \right. = \pi / ( \Delta ^ { * } ( s ^ { j } ) )$ . The time complexity of this algorithm is $\textstyle T : = \sum _ { j = 1 } ^ { q } \left. t ^ { j } \right.$ and in Supp. Mat. we show

$$
\begin{array} { r } { T = O \left( \kappa ^ { 2 } \log ( \kappa ) / \epsilon \right) . } \end{array}
$$

Note that, in each run, the overall evolution time is always bounded by $2 T$ .

Our first algorithm then uses the RM to prepare a mixed state $\rho _ { x }$ that satisfies Eq. (2), after discarding the ancilla. The time complexity is almost quadratic in $\kappa$ . The pseudocode for the algorithm is shown below.

<table><tr><td>Algorithm</td></tr><tr><td>Given condition number κ and precision e: Compute va and vb. Set q=Θ(log2(κ)/), δ =(vb−va)/q</td></tr><tr><td>− For j = 1, . . . , q, let vj = va +jδ, sj = s(vj), and tj be</td></tr><tr><td>sampled from the uniform distribution [0, 2π/∆*(sj)]</td></tr><tr><td>− Apply e−itqH(sq) . . . e−it1H(s1) to |bi, discard the ancilla</td></tr></table>

Spectral gap amplification. One way to improve the time complexity of the first algorithm is by considering other families of Hamiltonians where the relevant spectral gap is larger than that of $H ( s )$ . This idea was considered in Ref. [23] and resulted in various polynomial quantum speedups for quantum state preparation. A quadratic spectral gap amplification is indeed possible when the Hamiltonians satisfy a so-called frustration free property. Very roughly, a possible Hamiltonian with an amplified gap can be interpreted as the square root of the frustration-free Hamiltonian. A zero eigenvalue remains zero and an eigenvalue √ √ $\lambda > 0$ is transformed into eigenvalues $\pm \sqrt { \lambda }$ . ( $\sqrt { \lambda } \gg \lambda$ if $\lambda \ll 1$ .) To avoid additional complexity overheads, the Hamiltonians with an amplified gap must satisfy certain constrains related to the difficulty of their simulation. We refer to [23] for details.

Motivated by these results, we now consider another family of Hamiltonians for solving the QLSP using the

RM. This family is given by

$$
H ^ { \prime } ( s ) : = \sigma ^ { + } \otimes A ( s ) P _ { \bar { b } } ^ { \perp } + \sigma ^ { - } \otimes P _ { \bar { b } } ^ { \perp } A ( s ) ,
$$

where $\sigma ^ { \pm } = ( X \pm i Y ) / 2$ are single-qubit (raising and lowering) operators, and $s \in [ 0 , 1 ]$ . We note that $H ^ { \prime } ( s )$ acts on a Hilbert space of dimension $4 N$ . Then

$$
( H ^ { \prime } ( s ) ) ^ { 2 } = { \binom { H ( s ) } { 0 } } \ { 0 } _ { { \bar { b } } ^ { \perp } ( A ( s ) ) ^ { 2 } P _ { \bar { b } } ^ { \perp } } ) ,
$$

where each block of the matrix is of dimension $2 N \times 2 N$ . Using $B ( s ) : = A ( s ) { \cal P } _ { \bar { b } } ^ { \perp }$ , the blocks on the diagonal of Eq. (11) can be written as $B ( s ) ^ { \dagger } B ( s )$ and $B ( s ) B ( s ) ^ { \dagger }$ , and thus have the same spectrum. Consequently, the eigenvalues of $H ^ { \prime } ( s )$ are $\{ 0 , 0 , \pm \sqrt { \gamma _ { 1 } ( s ) } , \ldots , \pm \sqrt { \gamma _ { 2 N - 1 } ( s ) } \}$ , where $\gamma _ { j } ( s ) > 0$ are the nonzero eigenvalues of $H ( s )$ . The subspace of $H ^ { \prime } ( s )$ of eigenvalue zero is spanned by $\{ \left| 0 \right. \otimes | x ( s ) \rangle , | 1 \rangle \otimes | b \rangle \}$ .

In contrast to the first algorithm that aimed at preparing the ground state of $H ( s )$ , we now aim at preparing one of the two eigenstates of zero eigenvalue of $H ^ { \prime } ( s )$ that lies exactly at the middle of the spectrum. Nevertheless, the RM can be used to prepare any eigenstate as long as it is separated by a nonzero spectral gap from the other eigenstates. One may wonder if the double degeneracy is a problem for this case. The answer is negative as the Hamiltonian does not allow for transitions between the two eigenstates, that is, $\langle 0 | \otimes \langle x ( s ) | H ^ { \prime } ( s ^ { \prime } ) | 1 \rangle \otimes | \bar { b } \rangle = 0$ . If we initialize our quantum computer in $| 0 \rangle \otimes | x ( 0 ) \rangle$ , a sequence of perfect projective measurements of the eigenstates of $H ^ { \prime } ( s )$ at sufficiently close points will allow us to prepare $| 0 \rangle \otimes | x ( 1 ) \rangle$ with sufficiently high probability. The relevant spectral gap is now bounded by $\sqrt { \Delta ^ { * } ( s ) } > 0$ .

The eigenstate $| 0 \rangle \otimes | x ( s ) \rangle$ has similar properties as $| x ( s ) \rangle$ : the path length and norm of the rate of change are the same. Then, our second algorithm can be constructed by using the same discretization points $s ^ { j }$ that were used for the first algorithm. At each step, we now need to evolve with the Hamiltonian $H ^ { \prime } ( s ^ { j } )$ for a random time $t ^ { j }$ . This time can be sampled from the uniform distribution $t ^ { j } \in [ 0 , 2 \pi / \sqrt { \Delta ^ { * } ( s ^ { j } ) } ]$ . The time complexity of this algorithm is $\textstyle T : = \sum _ { j = 1 } ^ { q } \left. t ^ { j } \right.$ and, in Supp. Mat., we show

$$
T = { \cal O } \left( \kappa \log ( \kappa ) / \epsilon \right) .
$$

After discarding the two ancilla qubits, the final state is $\rho _ { x }$ and satisfies Eq. (2). The time complexity of our second algorithm is then almost linear in $\kappa$ . The pseudocode for this algorithm follows from the previous one by replacing $\Delta ^ { * } ( s ^ { j } )$ with $\sqrt { \Delta ^ { * } ( s ^ { j } ) }$ , $H ( s )$ with $H ^ { \prime } ( s )$ , and $\left| \hat { b } \right.$ with $\left| 0 \right. \otimes \left| b \right.$ , in the second and third lines.

Simulation results. We tested the validity of our quantum algorithms by performing numerical simulations. For this purpose, we randomly generated Hermitian matrices $A$ of dimension $N = 1 6$ that are 4-sparse and $N = 3 2$ that are 5-sparse, both satisfying $\| A \| = 1$ . The generated matrices result in a range of values for the condition number $\kappa$ . We post-selected matrices for which $\kappa \approx 1 0$ and $\kappa \approx 5 0$ (to within absolute error $1 0 ^ { - 3 }$ ), for $N = 1 6$ and $N = 3 2$ respectively. Similarly, we randomly generated 4-sparse and 5-sparse vectors for $\vec { b }$ . The parameters $s ^ { j }$ and $t ^ { j }$ were chosen according to the previous discussion and depend on $\kappa$ and $\epsilon$ (or $q$ ). In each execution, we prepare a pure quantum state that is not guaranteed to be $\epsilon$ -close to the pure eigenstate of the final Hamiltonian. However, the expected error of the prepared pure states from many repeated executions of the algorithms is indeed bounded by $\epsilon$ .

We ran simulations for which the number of repetitions of our algorithms were $n _ { r e p } = 5 0$ and $n _ { r e p } = 2 0 0$ , respectively. For each case, we first construct a finite-sampling density matrix $( 1 / n _ { r e p } ) \sum _ { i = 1 } ^ { n _ { r e p } } | \psi _ { i } \rangle \langle \psi _ { i } |$ . Here, $| \psi _ { i } \rangle$ is the pure state output at the $i$ ’th repetition. Tracing out the ancilla qubits, we get a density matrix $\tilde { \rho } _ { x }$ that describes the state of the system only. Note that $\tilde { \rho } _ { x }$ is, in general, slightly different from $\rho _ { x }$ of Eq. (2). However, $\ddot { \rho } _ { x }  \rho _ { x }$ in the limit of $n _ { r e p }  \infty$ . The error computed in our numerical simulations is then the trace distance between $\bar { \rho } _ { x }$ and $| x \rangle \langle x |$ .

In Fig. 1, we show the dependence of the inverse of the error on the number of steps $q$ . While the results are for two particular matrices $A$ with $\kappa \approx 1 0$ and $\kappa \approx$ 50, other matrices show similar results. We observe that the inverse of the error for the two quantum algorithms, denoted by $\epsilon _ { Q }$ and $\epsilon _ { L }$ respectively, scales almost linearly with $q$ . The dispersion around the linear fit is smaller for larger $n _ { r e p }$ . The results are then in accordance with our theoretical analysis.

Gate-based implementations. Our algorithms are based on Hamiltonian evolutions and can be implemented on a gate-based quantum computer using a Hamiltonian simulation method. We focus on the method of Ref. [20], which implements the truncated Taylor series of the evolution operator. It requires the Hamiltonian to be given as a linear combination $\sum _ { l } \alpha _ { l } V _ { l }$ , where the $V _ { l }$ are unitaries that are easy to apply and $\alpha _ { l } ~ > ~ 0$ . The $V _ { l }$ are applied ${ \ddot { O } } ( \tau )$ times, where $\tau$ is the product of the evolution time and $\sum _ { l } \alpha _ { l }$ . The $\ddot { O }$ notation hides logarithmic factors in $\tau$ .

Our second algorithm applies the evolution under $H ^ { \prime } ( s ^ { j } )$ for time $t ^ { j }$ . The main challenge is then to find a decomposition of the Hamiltonian in terms of unitaries. For technical reasons, we consider another Hamiltonian $\tilde { H } ^ { \prime } ( s ^ { j } )$ , but whose evolution operator mimics that of $H ^ { \prime } ( s ^ { j } )$ . This Hamiltonian is discussed in Supp. Mat.. It turns out that $\begin{array} { r } { \tilde { H } ^ { \prime } ( s ) = \frac { d + 1 } { 1 6 } \sum _ { l = 1 } ^ { 3 2 } V _ { l } ( s ) } \end{array}$ , where $V _ { l } ( s )$ are unitaries. As previous approaches for the QLSP [4], we assume access to a quantum oracle $O _ { A }$ for the matrix $A$ . This oracle outputs the nonzero matrix elements and their indices, for any row of $A$ . We also assume access to a (controlled) unitary $U _ { b }$ that prepares the state $| b \rangle$ and the (controlled) $U _ { b } ^ { \dagger }$ , as in Refs. [1, 3, 4]. Each unitary $V _ { l } ( s )$ can be applied using, at most, a constant number of $\mathcal { O } _ { A }$ and (controlled) $U _ { b }$ and $U _ { b } ^ { \dagger }$ . In addition, it may require $O ( n )$ two-qubit gates – see Supp. Mat..

![](images/b57f2cb96aa427b279941164366f659d117414010acacf27d43652bf2dc270aa.jpg)  
FIG. 1. The inverse of the error for the two quantum algorithms as a function of $q$ , the number of steps in the RM. Subscript $Q$ refers to the quantum algorithm with complexity that is almost quadratic in $\kappa$ and $L$ to the quantum algorithm with complexity almost linear in $\kappa$ . $n _ { r e p }$ is the number of repetitions of the of our algorithm. The results are for two randomly generated matrices $A$ with $N = 1 6$ , $\kappa \approx 1 0$ , and $N = 3 2$ , $\kappa \approx 5 0$ .

In our construction, we have $\tau = O ( t ^ { j } d )$ if the evolution time is $t ^ { j }$ . Since our algorithm implements evolutions with $q$ Hamiltonians, the total number of uses of $O _ { A }$ and (controlled) $U _ { b }$ and $U _ { b } ^ { \dagger }$ , or query complexity, is then ${ \cal \tilde { O } } ( T d )$ , where $T$ is the total evolution time. The number of additional two-qubit gates is a multiplicative factor of order $n$ away from the query complexity.

Substituting $T$ from Eq. (12) gives the query complexity of our approach as ${ \cal \tilde { O } } ( \kappa d / \epsilon )$ . In Ref. [1], it was shown that quantum algorithms for the QLSP must have a query complexity that is, at least, linear in $\kappa$ . Then, the gate-based implementation following Ref. [20] is almost optimal. Note that the query complexity of evolving with $\tilde { H } ^ { \prime } ( s )$ is of the same order as that of evolving directly with $A$ , which is needed for the HHL algorithm.

Discussion. We presented simple quantum algorithms for solving the QLSP that were motivated by AQC and not the standard gate-based model. A nice feature about AQC and related models, such as the RM or general eigenpath traversal methods [16], is that the time complexity is typically dominated by a single quantity, i.e., the inverse of the minimum spectral gap of the Hamiltonians. Then, the root of the quantum speedup is more clear in this case than in the gate-based model, allowing for algorithmic improvements by considering different Hamiltonians with larger spectral gaps. Another nice feature is that some problems are naturally reduced to preparing the eigenstate of a Hamiltonian, and eigenpath traversal methods are useful in that context. We showed that this is the case for the QLSP. Our results emphasize the importance of considering models of quantum computing, which go beyond the gate-based model, for discovering novel quantum algorithms – see Ref. [24] for another example.

The further significance of our results is as follows. Previous algorithms for the QLSP [1, 3, 4] use three main subroutines: (i) Hamiltonian simulation, (ii) phase estimation or function approximation, and (iii) some form of amplitude amplification. The method of “variabletime amplitude amplification” is used in Refs. [3, 4] to achieve near-optimal complexity in terms of $\kappa$ . That method alone requires $\Omega ( \log ( 1 / \epsilon ) \log ( \kappa / \epsilon ) / \epsilon ^ { 2 } )$ and $\Omega ( \log ( \kappa ) \log ( \kappa / \epsilon ) )$ ancillary qubits, respectively, which become excessively large for large $\kappa$ . In contrast, our algorithms use only Hamiltonian simulation (which has the same query complexity as in previous methods) thereby reducing the number of ancillary qubits significantly. Our result additionally implies a significant reduction in the number of conditional operations to solve the QLSP, making our algorithms more attractive for implementations on quantum computers of smaller size. To this point, our algorithm has already been used in Ref. [25] to solve an 8-dimensional linear system on a 4-qubit NMR device, the largest dimension up to date.

The time complexity of our methods is linear in $1 / \epsilon$ . This complexity can be improved to polylogarithmic in $1 / \epsilon$ using the fast methods for eigenpath traversal of Ref. [16]. These methods will provide a different way of obtaining an exponential improvement in terms of precision with respect to the HHL algorithm, as in Ref. [4], but they nevertheless require phase estimation.

Last, it would be interesting to study if our results can also impact classical methods for solving systems of linear equations.

Acknowledgements. We thank Anirban Chowdhury for discussions. Part of this material is based upon work supported by the U.S. Department of Energy, Office of Science, Office of Advanced Scientific Computing Research, Quantum Algorithms Teams program. We also thank the Laboratory Directed Research and Development Program at LANL for support. DO acknowledges the support by the Austrian Science Fund (FWF) through the DK-ALM W1259-N27, the SFB Fo-QuS F4012, and the Templeton World Charity Foundation grant TWCF0078/AB46.

[2] A. Prakash, Quantum Algorithms for Linear Algebra and Machine Learning, Ph.D. thesis, University of California, Berkeley (2008). [3] A. Ambainis, in Proceedings of the 29th International Symposium on Theoretical Aspects of Computer Science (2012) pp. 636–647.   
[4] A. Childs, R. Kothari, and R. D. Somma, SIAM J. Comp. 46, 1920 (2017).   
[5] S. Chakraborty, A. Gily´en, and S. Jeffery, arXiv:1804.01973 (2018).   
[6] N. Wiebe, D. Braun, and S. Lloyd, Phys. Rev. Lett. 109, 050505 (2012).   
[7] S. Lloyd, M. Mohseni, and P. Rebentrost, arXiv:1307.0411 (2013). [8] S. Lloyd, M. Mohseni, and P. Rebentrost, Nature Physics 10(9), 631 (2014).   
[9] G. Wang, Quantum Information & Computation 17, 987 (2017).   
[10] D. W. Berry, J. Phys. A: Math. Theor. 47, 105301 (2014).   
[11] B. D. Clader, B. C. Jacobs, and C. R. Sprouse, Phys. Rev. Lett. 110, 250504 (2013).   
[12] A. Chowdhury and R. D. Somma, Quant. Inf. Comp. 17, 0041 (2016).   
[13] E. Farhi, J. Goldstone, S. Gutmann, and M. Sipser, arXiv:quant-ph/0001106 (2000).   
[14] A. Messiah, Quantum Mechanics (Dover Publications, 1999).   
[15] S. Boixo, E. Knill, and R. Somma, Q. Inf. Comp. 9, 0833 (2009).   
[16] S. Boixo, E. Knill, and R. Somma, arXiv:1005.3034 (2010).   
[17] R. D. Somma, S. Boixo, H. Barnum, and E. Knill, Phys. Rev. Lett. 101, 130504 (2008).   
[18] H.-T. Chiang, G. Xu, and R. D. Somma, Phys. Rev. A 89, 012314 (2014).   
[19] D. Berry, G. Ahokas, R. Cleve, and B. Sanders, Comm. Math. Phys. 270, 359 (2007).   
[20] D. W. Berry, A. M. Childs, R. Cleve, R. Kothari, and R. D. Somma, Phys. Rev. Lett. 114, 090502 (2015).   
[21] G. Low and I. Chuang, Phys. Rev. Lett. 118, 010501 (2017).   
[22] S. Jansen, M. Ruskai, and R. Seiler, J. Math. Phys. 48, 102111 (2007).   
[23] R. D. Somma and S. Boixo, SIAM J. Comp 42, 593 (2013).   
[24] R. Somma, D. Nagaj, and M. Kieferova, Phys. Rev. Lett. 109, 050501 (2012).   
[25] J. Wen, X. Kong, S. Wei, T. Xin, B. Wang, K. Li, Y. Zhu, and G. Long, arXiv:1806.03295 (2018).   
[26] R. Bhatia, Matrix Analysis (Graduate Texts in Mathematics) (Springer, New York, 1997).   
[27] M. Szegedy, in Proceedings of the 45th Annual IEEE Symposium on FOCS. (IEEE, 2004) pp. 32–41.   
[28] D. W. Berry, A. M. Childs, and R. Kothari, in Proceedings of the 56th Symposium on Foundations of Computer Science (2015).

We consider first the Hamiltonians $H ( s )$ of Eq. (3) and note that

$$
\begin{array} { c } { { H ( s ) ( 1 / A ( s ) ) | \bar { b } \rangle = A ( s ) { \cal P } _ { \bar { b } } ^ { \perp } | \bar { b } \rangle } } \\ { { = 0 . } } \end{array}
$$

$A ( s ) \_$ is always invertible and its eigenvalues are $\pm \sqrt { ( 1 - s ) ^ { 2 } + ( s \lambda ) ^ { 2 } }$ , where $\lambda$ is an eigenvalue of $A$ . We let $B ( s ) = A ( s ) P _ { \bar { b } } ^ { \perp }$ and, since $H ( s ) = B ( s ) B ^ { \dagger } ( s )$ , we obtain $H ( s ) \geq 0$ . Also, the only eigenstate of zero eigenvalue of $P _ { \bar { b } } ^ { \perp }$ is $\left| \bar { b } \right.$ , implying that $| x ( s ) \rangle$ is the unique eigenstate of zero eigenvalue (ground state) of $H ( s )$ . Any other eigenvalue is positive and bounded from above by 1, under the assumptions on $A$ .

The Hamiltonian $H ( s )$ has smallest eigenvalue zero and second smallest eigenvalue $\Delta ( s )$ . It can be written as $H ( s ) = A ^ { 2 } ( s ) - A ( s ) | b \rangle \langle b | A ( s )$ . Weyl’s inequalities [26] imply that the second smallest eigenvalue of $H ( s )$ can be lower bounded by the smallest eigenvalue of $A ^ { 2 } ( s )$ plus the second smallest eigenvalue of $- A ( s ) | b \rangle \langle b | A ( s )$ , which is zero. It follows that the spectral gap of $H ( s )$ satisfies

$$
\Delta ( s ) \geq \Delta ^ { * } ( s ) : = ( 1 - s ) ^ { 2 } + ( s / \kappa ) ^ { 2 } ,
$$

where $\Delta ^ { * } ( s )$ is a bound on the square of the smallest eigenvalue of $A ( s )$ .

Under the assumption $\langle x ( s ) | \partial _ { s } x ( s ) \rangle = 0$ , the rate of change $\| | \partial _ { s } { x ( s ) } \rangle \|$ can be obtained as follows. First,

$$
| \partial _ { s } x ( s ) \rangle = \frac { 1 } { A ( s ) } ( Z \otimes \mathbb { 1 } - X \otimes A ) | x ( s ) \rangle + \beta ( s ) | x ( s ) \rangle ,
$$

where $\beta ( s ) \in \mathbb { R }$ . Since Eq. (15) is orthogonal to $| x ( s ) \rangle$ we obtain

$$
| \partial _ { s } x ( s ) \rangle = P _ { x } ^ { \perp } \frac { 1 } { A ( s ) } ( - Z \otimes \mathbb { 1 } + X \otimes A ) \left| x ( s ) \right. ,
$$

with $P _ { x } ^ { \perp } = \mathbb { 1 } - | x ( s ) \rangle \langle x ( s ) |$ the orthogonal projector. Using simple norm properties, it follows that

$$
\begin{array} { r l } & { \| | \partial _ { s } x ( s ) \rangle \| \leq \sqrt { 2 } \| 1 / A ( s ) \| } \\ & { \qquad \leq \sqrt { \frac { 2 } { ( 1 - s ) ^ { 2 } + ( s / \kappa ) ^ { 2 } } } . } \end{array}
$$

The quantity $\| | \partial _ { s } { x ( s ) } \rangle \|$ is useful to compute the path length of the eigenstate. If the assumption $\langle x ( s ) | \partial _ { s } x ( s ) \rangle = 0$ is not satisfied, we need to redefine $| x ( s ) \rangle$ by introducing a phase factor $e ^ { i \phi ( s ) }$ so that the assumption is satisfied. The calculation of $| \partial _ { s } x ( s ) \rangle$ has now an extra term that is due to the rate of change of $\phi ( s )$ . Nevertheless, the bound of Eq. (17) still applies when this extra phase factor is introduced.

Natural parametrization. A natural parametrization $v ( s )$ is such that $\parallel \left| \left. \partial _ { v } x ( s ( v ) ) \right. \right|$ is upper bounded by a constant, e.g. 1. This parametrization can be obtained from Eq. (17) if we require

$$
\partial _ { v } s = \sqrt { \frac { ( 1 - s ) ^ { 2 } + ( s / \kappa ) ^ { 2 } } { 2 } } .
$$

The solution is

$$
s ( v ) = \frac { e ^ { v \frac { \sqrt { 1 + \kappa ^ { 2 } } } { \sqrt { 2 } \kappa } } + 2 \kappa ^ { 2 } - \kappa ^ { 2 } e ^ { - v \frac { \sqrt { 1 + \kappa ^ { 2 } } } { \sqrt { 2 } \kappa } } } { 2 ( 1 + \kappa ^ { 2 } ) } .
$$

This function increases monotonically in the region of interest. We define

$$
\begin{array} { l } { { \displaystyle v _ { a } = \frac { \sqrt 2 \kappa } { \sqrt { 1 + \kappa ^ { 2 } } } \log ( \kappa \sqrt { 1 + \kappa ^ { 2 } } - \kappa ^ { 2 } ) \ , } } \\ { { \displaystyle v _ { b } = \frac { \sqrt 2 \kappa } { \sqrt { 1 + \kappa ^ { 2 } } } \log ( \sqrt { 1 + \kappa ^ { 2 } } + 1 ) \ , } } \end{array}
$$

and note that

$$
s ( v _ { a } ) = 0 , \quad s ( v _ { b } ) = 1 ,
$$

so that the boundary constrains are satisfied.

In the following, we abuse the notation slightly so that $f ( v ) : = f ( s ( v ) )$ . The notation will be clear from the context.

Path length. The path length

$$
\begin{array} { r } { L : = \displaystyle \int _ { 0 } ^ { 1 } d s \parallel \vert \partial _ { s } x ( s ) \rangle \parallel } \\ { = \displaystyle \int _ { v _ { a } } ^ { v _ { b } } d v \parallel \vert \partial _ { v } x ( v ) \rangle \parallel } \end{array}
$$

is a useful quantity for methods based on eigenpath traversal. From the natural parametrization of Eq. (18), it follows that $\| | \partial _ { v } x ( v ) \rangle \| \leq 1$ and

$$
L \leq \int _ { v _ { a } } ^ { v _ { b } } d v = v _ { b } - v _ { a } .
$$

Additionally, we can use the fact that $\kappa + 1 / ( 4 \kappa ) \leq$ $\sqrt { \kappa ^ { 2 } + 1 } \le \kappa + 1$ to show

$$
\begin{array} { l } { { v _ { b } - v _ { a } = \displaystyle \frac { \sqrt 2 \kappa } { \sqrt { 1 + \kappa ^ { 2 } } } \log \left( \displaystyle \frac { \sqrt { 1 + \kappa ^ { 2 } } + 1 } { \kappa \sqrt { 1 + \kappa ^ { 2 } } - \kappa ^ { 2 } } \right) } } \\ { { \mathrm { } \leq \sqrt { 2 } \log \left( \displaystyle \frac { \kappa + 2 } { 1 / 4 } \right) } } \\ { { \mathrm { } \leq \sqrt { 2 } \log ( 1 2 \kappa ) = L ^ { * } . } } \end{array}
$$

Then, the upper bound $L ^ { * }$ on the path length depends logarithmically on the condition number.

Time complexity using $H ( s )$ . The time complexity of our first algorithm is

$$
T = \pi \sum _ { j = 1 } ^ { q } 1 / \Delta ^ { * } ( v ^ { j } ) \ .
$$

According to Ref. [15], we can choose the number of steps $q$ to be $\Theta ( ( L ^ { * } ) ^ { 2 } / \epsilon )$ . We can multiply and divide Eq. (26) by $\delta : = L ^ { * } / q$ . As $\kappa$ gets larger, $\delta$ gets smaller, and we should be able to approximate $T$ by $\begin{array} { r l } { ( \pi / \delta ) \int _ { v _ { a } } ^ { v _ { b } } d v } & { { } ( 1 / \Delta ^ { * } ( v ) ) } \end{array}$ . More precisely, the function $1 / \Delta ^ { * } ( v )$ reaches its maximum value of $\kappa ^ { 2 } + 1$ at $v = v _ { M }$ , and $v _ { a } \leq v _ { M } \leq v _ { b }$ . We let $r$ be the integer in $\{ 1 , \ldots , q \}$ such that $v ^ { r } \leq v _ { M } \leq v ^ { r + 1 }$ . It is then possible to show

$$
\begin{array} { r l r } & { } & { \delta \displaystyle \sum _ { j = 1 } ^ { r } \displaystyle \frac { 1 } { \Delta ^ { * } ( v ^ { j } ) } \leq \int _ { v _ { a } } ^ { v ^ { r } - \delta } d v \displaystyle \frac { 1 } { \Delta ^ { * } ( v + \delta ) } + \delta \frac { 1 } { \Delta ^ { * } ( v ^ { r } ) } , } \\ & { } & { \delta \displaystyle \sum _ { j = r + 1 } ^ { q } \displaystyle \frac { 1 } { \Delta ^ { * } ( v ^ { j } ) } \leq \delta \frac { 1 } { \Delta ^ { * } ( v ^ { r + 1 } ) } + \int _ { v ^ { r + 1 } } ^ { v _ { b } } d v \displaystyle \frac { 1 } { \Delta ^ { * } ( v ) } . } \end{array}
$$

Then,

$$
\sum _ { j = 1 } ^ { q } \frac { 1 } { \Delta ^ { * } ( v ^ { j } ) } \leq \frac { 1 } { \delta } \int _ { v _ { a } } ^ { v _ { b } } d v \ \frac { 1 } { \Delta ^ { * } ( v ) } + \frac { 2 } { \Delta ^ { * } ( v _ { M } ) } .
$$

The second term on the right hand side is $2 ( \kappa ^ { 2 } + 1 )$ . To obtain the first term on the right hand side, we evaluate the integral:

$$
\begin{array} { c } { { \displaystyle \int _ { v _ { a } } ^ { v _ { b } } d v \ \frac { 1 } { \Delta ^ { * } ( v ) } = \int _ { 0 } ^ { 1 } d s \ \frac { \sqrt { 2 } } { [ ( 1 - s ) ^ { 2 } + ( s / \kappa ) ^ { 2 } ] ^ { 3 / 2 } } } } \\ { { = \sqrt { 2 } \kappa ( 1 + \kappa ) . } } \end{array}
$$

These bounds imply

$$
T \leq \pi \left[ \frac { \sqrt { 2 } \kappa ( 1 + \kappa ) } { \delta } + 2 ( \kappa ^ { 2 } + 1 ) \right]
$$

Finally, recalling that $\begin{array} { r c l } { { \delta } } & { { = } } & { { \Theta ( \epsilon / \log ( \kappa ) ) } } \end{array}$ and $q \quad =$ $\Theta ( \log ^ { 2 } ( \kappa ) / \epsilon )$ , we obtain $T = O ( \kappa ^ { 2 } \log ( \kappa ) / \epsilon )$ .

Spectral gap amplification. Consider the Hamiltonian $I ( s ) : = P _ { \bar { b } } ^ { \perp } ( A ( s ) ) ^ { 2 } P _ { \bar { b } } ^ { \perp }$ that appears in one of the diagonal blocks of Eq. (11). This can be written as ${ \cal I } ( s ) = B ^ { \dagger } ( s ) B ( s )$ . Then, if $| \gamma ( s ) \rangle$ is an eigenstate of $H ( s )$ of eigenvalue $\gamma ( s ) > 0$ , $B ^ { \dagger } ( s ) \left| \gamma ( s ) \right. \neq 0$ is an eigenstate of $I ( s )$ with the same eigenvalue. The eigenstate of eigenvalue zero of $I ( s )$ is $| b \rangle$ .

Equation (11) implies that the eigenvalues of $H ^ { \prime } ( s )$ are $) , + \sqrt { \gamma ( s ) }$ , and $- \sqrt { \gamma ( s ) }$ . Moreover, $( Z \otimes \mathbb { 1 } ) H ^ { \prime } ( s ) ( Z \otimes$ $\mathbb { 1 } ) \ = \ - H ^ { \prime } ( s )$ , so if $+ \sqrt { \gamma ( s ) }$ is an eigenvalue of $H ^ { \prime } ( s )$ then $- \sqrt { \gamma ( s ) }$ is also an eigenvalue. In summary, $H ^ { \prime } ( s )$ has a zero eigenvalue of degeneracy two and the other eigenvalues are $\pm \sqrt { \gamma ( s ) }$ for each eigenvalue $\gamma ( s )$ of $H ( s )$ .

This is illustrated in Fig. 2.

![](images/56d89ac0a8b5404298eb23bd86def4be5b12cc81a183f128f5023cd7bb4257ed.jpg)  
FIG. 2. Schematic illustration of the spectral gap amplification method applied to the Hamiltonians $H ( s )$ . The positive (negative) subspace refers to the subspace of $H ^ { \prime } ( s )$ of positive (negative) eigenvalues. The horizontal axis shows the eigenvalues of $H ( s )$ and the vertical axis shows the eigenvalues of $H ^ { \prime } ( s )$ .

Time complexity using $H ^ { \prime } ( s )$ . As described in the main text, the time complexity of our second algorithm is

$$
T = \pi \sum _ { j = 1 } ^ { q } 1 / \sqrt { \Delta ^ { * } \left( v ^ { j } \right) } .
$$

Following Eq. (29) for this case, we obtain

$$
\sum _ { j = 1 } ^ { q } \frac { 1 } { \sqrt { \Delta ^ { * } ( v ^ { j } ) } } \le \frac { 1 } { \delta } \int _ { v _ { a } } ^ { v _ { b } } d v \frac { 1 } { \sqrt { \Delta ^ { * } ( v ) } } + \frac { 2 } { \sqrt { \Delta ^ { * } ( v _ { M } ) } } .
$$

The second term on the right hand side is $2 \sqrt { \kappa ^ { 2 } + 1 }$ . To obtain the first term on the right hand side, we evaluate the integral

$$
\begin{array} { c } { { \displaystyle \int _ { v _ { a } } ^ { v _ { b } } d v \ \frac { 1 } { \sqrt { \Delta ^ { * } ( v ) } } = \int _ { 0 } ^ { 1 } d s \ \frac { \sqrt { 2 } } { ( 1 - s ) ^ { 2 } + ( s / \kappa ) ^ { 2 } } } } \\ { { = \pi \kappa / \sqrt { 2 } . } } \end{array}
$$

These bounds imply

$$
T \leq \pi \left[ \frac { \pi \kappa } { \sqrt { 2 } \delta } + 2 \sqrt { \kappa ^ { 2 } + 1 } \right] ,
$$

and then $T = O ( \kappa \log ( \kappa ) / \epsilon )$ .

Special Case: $A > 0$ . In this case, we can define

$$
A ( s ) : = ( 1 - s ) \mathbb { 1 } + s A \ .
$$

The important property is that $A ( s )$ is invertible for $s \in$ $[ 0 , 1 ]$ , and we achieve this without using an ancilla qubit.

The Hamiltonians for our two algorithms can be modified by simply replacing $A ( s )$ in Eqs. (3) and (10) by the one in Eq. (36). The same bounds for the spectral gap and path length that apply for general $A$ also hold for this case. Then, we can use the same natural parametrization of Eq. (19). As a result, the QLSP for $A > 0$ can be solved with the same time complexity as in the general case, albeit using one fewer ancilla qubit and even a simpler Hamiltonian.

Gate-based implementations. We provide the details of the implementation of the algorithm based on the Hamiltonian of Eq. (10) using a gate-based quantum computer. Our goal is to use the Hamiltonian simulation method of Ref. [20], which requires expressing the Hamiltonian as a linear combination of unitaries. $A ( s )$ can be written as a linear combination of unitaries using a version of Szegedy walks that applies to Hermitian matrices [27, 28]. $A$ is of dimension $N$ , $n = \log _ { 2 } N$ , and $A ( s )$ is of dimension $2 N$ . We define unitary operations $U _ { x }$ , $U _ { y }$ , and $S$ that act as follows:

$$
\begin{array} { l } { { { \cal U } _ { x } \left| j \right. \left| 0 \right. \left| 0 \right. = \displaystyle \frac { 1 } { \sqrt { d + 1 } } \sum _ { i \in { \cal F } _ { j } } \left| j \right. \left| i \right. \left| 0 \right. \left( \sqrt { A ( s ) _ { j i } ^ { * } } \left| 0 \right. + \sqrt { 1 - \left| A ( s ) _ { j i } \right| } \left| 1 \right. \right) , } } \\ { { { \cal U } _ { y } \left| 0 \right. \left| j ^ { \prime } \right. \left| 0 \right. = \displaystyle \frac { 1 } { \sqrt { d + 1 } } \sum _ { i ^ { \prime } \in { \cal F } _ { j ^ { \prime } } } \left| i ^ { \prime } \right. \left| j ^ { \prime } \right. \left( \sqrt { A ( s ) _ { i ^ { \prime } j ^ { \prime } } } \left| 0 \right. + \sqrt { 1 - \left| A ( s ) _ { i ^ { \prime } j ^ { \prime } } \right| } \left| 1 \right. \right) \left| 0 \right. , } } \\ { { { \cal S } \left| j \right. \left| j ^ { \prime } \right. \left| \cdot \right. \left| \cdot \right. = \left| j ^ { \prime } \right. \left| j \right. \left| \cdot \right. \left| \cdot \right. . } } \end{array}
$$

The first two registers have $n + 1$ qubits each, the last two registers have a single qubit each, and $F _ { j }$ is the set of indices $_ i$ for which $A ( s ) _ { j i }$ is nonzero. It follows that

$$
\begin{array} { c } { { A ( s ) \otimes | \tilde { 0 } \rangle \langle \tilde { 0 } | = ( d + 1 ) | \tilde { 0 } \rangle \langle \tilde { 0 } | U _ { x } ^ { \dagger } U _ { y } S | \tilde { 0 } \rangle \langle \tilde { 0 } | } } \\ { { = \displaystyle \frac { d + 1 } { 4 } \left( \mathbb { 1 } - e ^ { i \pi P } \right) U _ { x } ^ { \dagger } U _ { y } S \left( \mathbb { 1 } - e ^ { i \pi P } \right) , } } \end{array}
$$

where we defined $\left| \tilde { 0 } \right. : = \left| 0 \right. \left| 0 \right. \left| 0 \right.$ for the state of the last three registers and $P = | \tilde { 0 } \rangle \langle \tilde { 0 } |$ .

We assume access to an oracle for $A$ that acts as

$$
\begin{array} { c } { { | j  | i  | z   | j  | i  | z \oplus A _ { j i }  ~ , } } \\ { { | j  | l   | j  | f ( j , l )  ~ . } } \end{array}
$$

Here, $j$ and $i$ label the row and column of $A$ , respectively, so that $j , i \in \{ 1 , \dots , N \}$ . $f ( j , l )$ is the column index of the $\mathbf { \xi } ^ { l }$ th nonzero element of $A$ in row $j$ . We refer to this oracle as $\mathcal { O } _ { A }$ . From the oracle $\mathcal { O } _ { A }$ it is straightforward to implement an oracle ${ \mathcal { O } } _ { A ( s ) }$ for the $( d + 1 ) -$ sparse matrix $A ( s )$ . $\mathcal { O } _ { A }$ is the same as that used in previous works for the QLSP and Hamiltonian simulation; cf. Refs. [4, 28].

$U _ { x }$ can then be implemented in five steps as follows:

$$
\begin{array} { r l } { | \vec { j } \rangle | 0 \rangle | 0 \rangle | 0 \rangle | 0 \rangle \frac { \operatorname { I o g } ( \vec { a } + 1 ) } { \operatorname { I n d a m a t e r a g e : } } \displaystyle \sum _ { \vec { \sqrt { d + 1 } } } | j \rangle | i \rangle | 0 \rangle | 0 \rangle | 0 \rangle } & { } \\ & { \frac { \mathcal { O } _ { A ( s ) } } { \sqrt { d + 1 } } \displaystyle \sum _ { i \in E _ { j } } | j \rangle | i \rangle | 0 \rangle | 0 \rangle | 0 \rangle } \\ & { \frac { \mathcal { O } _ { A ( s ) } } { \sqrt { d + 1 } } \displaystyle \sum _ { i \in E _ { j } } | j \rangle | i \rangle | i \rangle | 0 \rangle | 0 \rangle } \\ & { - \frac { \mathcal { O } _ { A ( s ) } } { \sqrt { d + 1 } } \displaystyle \sum _ { i \in E _ { j } } | j \rangle | i \rangle | i \rangle | A ( s ) _ { \vec { j } \rangle } | 0 \rangle | 0 \rangle } \\ & { \frac { \mathcal { O } _ { A ( s ) } } { \sqrt { d + 1 } } \displaystyle \sum _ { i \in E _ { j } } | j \rangle | i \rangle | A ( s ) _ { \vec { j } \rangle } | 0 \rangle \left( \sqrt { A ( s ) _ { \vec { j } \rangle } ^ { * } } | 0 \rangle + \sqrt { 1 - | A ( s ) _ { \vec { j } \rangle } | 1 \rangle } \right) } \\ & { \frac { \mathcal { O } _ { A ( s ) } } { \sqrt { d + 1 } } \displaystyle \sum _ { i \in E _ { j } } | j \rangle | i \rangle | 0 \rangle | 0 \rangle \left( \sqrt { A ( s ) _ { \vec { j } \rangle } ^ { * } } | 0 \rangle + \sqrt { 1 - | A ( s ) _ { \vec { j } \rangle } | 1 \rangle } \right) . } \end{array}
$$

The third register is used to temporarily store the matrix elements of $A ( s )$ and is discarded at the end. $U _ { x }$ can then be implemented with $O ( 1 )$ queries to $\mathcal { O } _ { A }$ . The complexity of the fourth step, where the operation $M$ is implemented, is defined to be $C _ { M }$ . This complexity and the size of the third register depend on the precision with which the matrix elements of $A$ are given. A similar procedure can be followed to implement $U _ { y }$ .

Using Eq. (40), we define

$$
\begin{array} { r l r } & { } & { \tilde { H } ^ { \prime } ( s ) : = H ^ { \prime } ( s ) \otimes P = \displaystyle \frac { d + 1 } { 1 6 } X \left( 1 - Z \right) \otimes \left( 1 - e ^ { i \pi P } \right) U _ { x } ^ { \dagger } U _ { y } S \left( 1 - e ^ { i \pi P } \right) \left( 1 + U _ { \bar { b } } e ^ { i \pi P } U _ { \bar { b } } ^ { \dagger } \right) } \\ & { } & { \qquad + \displaystyle \frac { d + 1 } { 1 6 } X \left( 1 + Z \right) \otimes \left( 1 + U _ { \bar { b } } e ^ { i \pi P } U _ { \bar { b } } ^ { \dagger } \right) \left( 1 - e ^ { i \pi P } \right) U _ { x } ^ { \dagger } U _ { y } S \left( 1 - e ^ { i \pi P } \right) , } \end{array}
$$

where $U _ { \bar { b } } = { \mathrm { H } } \otimes U _ { b }$ is the unitary that prepares the state $| b \rangle$ and $\mathrm { H }$ is the Hadamard operation. This Hamiltonian is a linear combination of 32 unitaries with equal weights of $( d + 1 ) / 1 6$ :

$$
\tilde { H } ^ { \prime } ( s ) = \frac { d + 1 } { 1 6 } \sum _ { l = 1 } ^ { 3 2 } V _ { l } ( s ) \ .
$$

Note that evolving any state $| \psi \rangle$ with $H ^ { \prime } ( s )$ can be done by evolving the state $| \psi \rangle \otimes | \widetilde { 0 } \rangle$ with $\tilde { H } ^ { \prime } ( s )$ . Equation (49) is the desired form for using the results of Ref. [20].

We want to simulate the evolution under $\tilde { H } ^ { \prime } ( s ^ { j } )$ , for fixed $s ^ { j }$ , and evolution time $t ^ { j }$ . Reference [20] describes a simulation method based on an implementation of a truncated Taylor series for the evolution operator. An evolution for time $t ^ { j }$ is split into $r$ shorter-time evolutions (segments) for time $t ^ { j } / r$ each. Each of these segments is executed by using an algorithm that implements a linear combination of unitary operations and by using a technique referred to as oblivious amplitude amplification.

To determine the complexity of the simulation method, we let $K$ be the truncation order of the Taylor series approximation of the evolution associated with each segment. $K$ , as well as the number of segments, can be obtained from the total evolution time under the Hamiltonians $\tilde { H } ^ { \prime } ( s ^ { j } )$ , which we denote by $T$ . In Ref. [20], it is determined that $K = O ( \log ( d T / \epsilon ) / \log \log ( d T / \epsilon ) )$ , since the sum of the weights of the linear combination in Eq. (48) is $O ( d )$ . The number of segments for this case is $r = O ( d T )$ . Since $U _ { x }$ and $U _ { y }$ require $O ( 1 )$ queries to $A$ each, it follows that the total number of $O _ { A }$ to simulate the evolution for time $T$ is $O ( d T K )$ . The number of (controlled) $U _ { b }$ and $U _ { b } ^ { \dagger }$ operations is also $O ( d T K )$ : each $V _ { l } ( s )$ can be applied using, at most, a constant number of these operations. The main gate complexity comes from the implementation of the operations $U _ { x }$ and $U _ { y }$ , which is $C _ { M }$ , and the unitaries $e ^ { i P }$ , which is $O ( \log N ) = O ( n )$ Thus, the gate complexity of the overall simulation is $O ( d T K ( n + C _ { M } ) )$ . Replacing $T$ by the evolution time of our second algorithm, i.e. $T = O ( \kappa \log ( \kappa ) / \epsilon )$ , gives the final query and gate complexities as $\ddot { O } ( d \kappa / \epsilon )$ and ${ \tilde { O } } ( d \kappa ( n + C _ { M } ) / \epsilon )$ , respectively. The $\tilde { O }$ notation hides factors that are polylogarithmic in $d \kappa / \epsilon$ .

We note that, in the query model, evolving with $\ddot { H } ^ { \prime } ( s )$ is not more complicated than evolving with $A$ , as the previous Hamiltonian simulation method yields the same query complexity for both cases.