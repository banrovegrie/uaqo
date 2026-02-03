# Quantum linear system solver based on time-optimal adiabatic quantum computing and quantum approximate optimization algorithm

DONG AN, Department of Mathematics, University of California, Berkeley, USA LIN LIN, Department of Mathematics and Challenge Institute of Quantum Computation, University of California, Berkeley, USA and Computational Research Division, Lawrence Berkeley National Laboratory, USA

We demonstrate that with an optimally tuned scheduling function, adiabatic quantum computing (AQC) can readily solve a quantum linear system problem (QLSP) with $O ( \kappa \mathrm { p o l y } ( \log ( \kappa / \epsilon ) ) )$ runtime, where $\kappa$ is the condition number, and $\epsilon$ is the target accuracy. This is near optimal with respect to both $\kappa$ and $\epsilon$ , and is achieved without relying on complicated amplitude amplification procedures that are difficult to implement. Our method is applicable to general non-Hermitian matrices, and the cost as well as the number of qubits can be reduced when restricted to Hermitian matrices, and further to Hermitian positive definite matrices. The success of the time-optimal AQC implies that the quantum approximate optimization algorithm (QAOA) with an optimal control protocol can also achieve the same complexity in terms of the runtime. Numerical results indicate that QAOA can yield the lowest runtime compared to the time-optimal AQC, vanilla AQC, and the recently proposed randomization method.

# CCS Concepts: $\bullet$ Theory of computation Quantum computation theory; $\bullet$ Mathematics of computing Numerical analysis.

Additional Key Words and Phrases: quantum linear system problem, adiabatic quantum computing, quantum approximate optimization algorithm

# ACM Reference Format:

Dong An and Lin Lin. 2022. Quantum linear system solver based on time-optimal adiabatic quantum computing and quantum approximate optimization algorithm. ACM Trans. Quantum Comput. 3, 2, Article 5 (February 2022), 28 pages. https://doi.org/10.1145/3498331

# 1 INTRODUCTION

Linear system solvers are used ubiquitously in scientific computing. Quantum algorithms for solving large systems of linear equations, also called the quantum linear system problem (QLSP), have received much attention recently [8, 10–12, 16, 17, 30, 33, 34]. The goal of QLSP is to efficiently compute $| x  = { A ^ { - 1 } | b  } / | | A ^ { - 1 } | b  | | _ { 2 }$ on a quantum computer, where $A \in \mathbb { C } ^ { N \times N }$ , and $| b \rangle \in \mathbb { C } ^ { N }$ is a normalized vector (for simplicity we assume $N = 2 ^ { n }$ , and $\| A \| _ { 2 } = 1 ,$ ). The ground-breaking Harrow, Hassidim, and Lloyd (HHL) algorithm obtains $| x \rangle$ with cost $O ( \mathrm { p o l y } ( n ) \kappa ^ { 2 } / \epsilon )$ , where $\kappa = \| A \| \| A ^ { - 1 } \|$ is the condition number of $A$ , and $\epsilon$ is the target accuracy. On the other hand, the best classical iterative algorithm is achieved by the conjugate gradient method, where the cost is at least ${ \cal O } ( N \sqrt { \kappa } \log ( 1 / \epsilon ) )$ , with the additional assumptions that $A$ should be Hermitian positive definite and a matrix-vector product can be done with $O ( N )$ cost [29]. The complexity of direct methods based on the Gaussian elimination procedure removes the dependence on $\kappa$ , but the dependence on $N$ is typically superlinear even for sparse matrices [21]. Therefore the HHL algorithm can potentially be exponentially faster than classical algorithms with respect to $N$ . The undesirable dependence with respect to $\epsilon$ is due to the usage of the quantum phase estimation (QPE) algorithm. Recent progresses based on linear combination of unitaries (LCU) [12] and quantum signal processing (QSP) [16, 22] have further improved the scaling to $O ( \kappa ^ { 2 } \mathrm { p o l y } ( \log ( \kappa / \epsilon ) ) )$ under different query models, without using QPE. However, the $O ( \kappa ^ { 2 } )$ scaling can be rather intrinsic to the methods, at least before complex techniques such as variable time amplitude amplification (VTAA) algorithm [2] are applied.

The VTAA algorithm is a generalization of the standard amplitude amplification algorithm, and allows to quadratically amplify the success probability of quantum algorithms in which different branches stop at different time. In [2], VTAA is first used to successfully improve the complexity of HHL algorithm to $\widetilde { \cal O } ( \kappa / \epsilon ^ { 3 } )$ . In [12], the authors further combine VTAA algorithm and a low-precision phase estimate to improve the complexity of LCU to $\widetilde { \cal O } ( \kappa \mathrm { p o l y } ( \log ( \kappa / \epsilon ) ) )$ , which is near-optimal with respect to both $\kappa$ and $\epsilon$ . It is worth noting that the VTAA algorithm is a complicated procedure and can be difficult to implement. Thus, it remains of great interest to obtain alternative algorithms to solve QLSP with near-optimal complexity scaling without resorting to VTAA.

Some of the alternative routes for solving QLSP are provided by the adiabatic quantum computing (AQC) [1, 19] and a closely related method called the randomization method (RM) [6, 30]. The key idea of both AQC and RM is to solve QLSP as an eigenvalue problem with respect to a transformed matrix. Assume that a Hamiltonian simulation can be efficiently performed on a quantum computer, it is shown that the runtime of RM scales as $O ( \kappa \log ( \kappa ) / \epsilon )$ [30], which achieves near-optimal complexity with respect to $\kappa$ without using VTAA algorithm as a subroutine. The key idea of the RM is to approximately follow the adiabatic path based on the quantum Zeno effect (QZE) using a Monte Carlo method. Although RM is inspired by AQC, the runtime complexity of the (vanilla) AQC is at least $O ( \kappa ^ { 2 } / \epsilon )$ [1, 7, 30]. Therefore the RM is found to be at least quadratically faster than AQC with respect to $\kappa$ .

In this paper, we find that with a simple modification of the scheduling function to traverse the adiabatic path, the gap between AQC and RM can be fully closed, along with the following two aspects. 1) We propose a family of rescheduled AQC algorithms called $\mathsf { A Q C } ( \mathsf { p } )$ . Assuming $\kappa$ (or its upper bound) is known, we demonstrate that for any matrix $A$ (possibly non-Hermitian or dense), when $1 < p < 2$ , the runtime complexity of $\mathsf { A Q C } ( \mathsf { p } )$ can be only $O ( \kappa / \epsilon )$ . Thus $\mathsf { A Q C } ( \mathsf { p } )$ removes a logarithmic factor with respect to $\kappa$ compared to RM. 2) We propose another rescheduled algorithm called AQC(exp), of which the runtime is $O ( \kappa \mathrm { p o l y } ( \log ( \kappa / \epsilon ) ) )$ . The main benefit of AQC(exp) is the improved dependence with respect to the accuracy $\epsilon$ , and this is the near-optimal complexity (up to logarithmic factors) with respect to both $\kappa$ and $\epsilon$ . The scheduling function of AQC(exp) is also universal because we do not even need the knowledge of an upper bound of $\kappa$ . Existing works along this line [15, 25] only suggest that runtime complexity is $O ( \kappa ^ { 3 } \mathrm { p o l y } ( \log ( \kappa / \epsilon ) ) )$ , which improves the dependence with respect to $\epsilon$ at the expense of a much weaker dependence on $\kappa$ . Our main technical contribution is to again improve the dependence on $\kappa$ . Since the cost of any generic QLSP solver can not be less than $O ( \kappa )$ [17], our result achieves the near-optimal complexity up to logarithmic factors. We remark that in the AQC based algorithm, only the total runtime $T$ depends on $\kappa$ .

Beyond the runtime complexity, we also discuss gate-efficient approaches to implement our $\mathsf { A Q C } ( \mathsf { p } )$ and AQC(exp) methods. In particular, assume that we are given access to the same query models as those in [12]: the sparse input model of a $d$ -sparse matrix $A$ and the prepare oracle of the state $| b \rangle$ . We demonstrate that, when the adiabatic dynamics is simulated using the truncated Dyson series method [23], the query complexity of the $\mathsf { A Q C } ( \mathsf { p } )$ method scales $O ( d \kappa / \epsilon \log ( d \kappa / \epsilon ) )$ , and that of the $\mathsf { A Q C } ( \exp )$ method scales $O ( d \kappa \mathrm { p o l y l o g } ( d \kappa / \epsilon ) )$ . Both algorithms scale almost linearly in terms of $\kappa$ , and the AQC(exp) method can achieve near-optimal scaling in both $\kappa$ and $\epsilon$ . Furthermore, the asymptotic scaling of the $\mathsf { A Q C } ( \exp )$ method is the same as that of LCU with VTAA method [12, Theorem 5]. However, the AQC(exp) method avoids the usage of complex VTAA routine, which significantly simplifies its practical implementation.

The quantum approximate optimization algorithm (QAOA) [14], as a quantum variational algorithm, has received much attention recently thanks to the feasibility of being implemented on near-term quantum devices. Due to the natural connection between AQC and QAOA, our result immediately suggests that the time-complexity for solving QLSP with QAOA is also at most ${ \cal O } ( \kappa \mathrm { \ p o l y } ( \log ( \kappa / \epsilon ) ) )$ ), which is also confirmed by numerical results. We also remark that both QAOA and AQC schemes prepare an approximate solution to the QLSP in a pure state, while RM prepares a mixed state. Moreover, all methods above can be efficiently implemented on gate-based computers and are much simpler than those using the VTAA algorithm as a subroutine.

# 2 QUANTUM LINEAR SYSTEM PROBLEM AND VANILLA AQC

Assume $A \in \mathbb { C } ^ { N \times N }$ is an invertible matrix with condition number $\kappa$ and $\| A \| _ { 2 } = 1$ . Let $| b \rangle \in$ $\mathbb { C } ^ { N }$ be a normalized vector. Given a target error $\epsilon$ , the goal of QLSP is to prepare a normalized state $\left| x _ { \mathrm { a } } \right.$ , which is an $\epsilon$ -approximation of the normalized solution of the linear system $| x \rangle =$ $A ^ { - 1 } \left| b \right. / \| A ^ { - 1 } \left| b \right. \| _ { 2 }$ , in the sense that $\| \left| x _ { \mathrm { a } } \right. \left. x _ { \mathrm { a } } \right| - \left| x \right. \left. x \right| \| _ { 2 } \leq \epsilon$ .

For simplicity, we first assume $A$ is Hermitian and positive definite and will discuss the generalization to non-Hermitian case later.

The first step to design an AQC-based algorithm for solving QLSP is to transform the QLSP to an equivalent eigenvalue problem. Here we follow the procedure introduced in [30]. Let $Q _ { b } =$ $I _ { N } - \left| b \right. \left. b \right|$ . We introduce

$$
H _ { 0 } = \sigma _ { x } \otimes Q _ { b } = \left( \begin{array} { c c } { { 0 } } & { { Q _ { b } } } \\ { { Q _ { b } } } & { { 0 } } \end{array} \right) ,
$$

then $H _ { 0 }$ is a Hermitian matrix and the null space of $H _ { 0 }$ is $\mathrm { N u l l } ( H _ { 0 } ) = \operatorname { s p a n } \{ | \widetilde { b } \rangle , | \bar { b } \rangle \}$ . Here $| \widetilde { b } \rangle =$ $| 0 , b \rangle : = ( b , 0 ) ^ { \top } , | \bar { b } \rangle = | 1 , b \rangle : = ( 0 , b ) ^ { \top } \mathrm { ~ }$ . The dimension of $H _ { 0 }$ is $2 N$ and one ancilla qubit is needed to enlarge the matrix block. We also define

$$
H _ { 1 } = \sigma _ { + } \otimes ( A Q _ { b } ) + \sigma _ { - } \otimes ( Q _ { b } A ) = \left( \begin{array} { c c } { { 0 } } & { { A Q _ { b } } } \\ { { Q _ { b } A } } & { { 0 } } \end{array} \right) .
$$

Here $\begin{array} { r } { \sigma _ { \pm } = \frac { 1 } { 2 } ( \sigma _ { x } \pm \mathrm { i } \sigma _ { y } ) . } \end{array}$ . Note that if $| x \rangle$ satisfies $A \left| x \right. \propto \left| b \right.$ , we have $Q _ { b } A \left| x \right. = Q _ { b } \left| b \right. = 0$ . Then $\mathrm { N u l l } ( H _ { 1 } ) = \operatorname { s p a n } \{ | { \widetilde { x } } \rangle , | { \bar { b } } \rangle \}$ with $\left| \widetilde { x } \right. = \left| 0 , x \right.$ . Since $Q _ { b }$ is a projection operator, the gap between 0 eand the rest of the eigenvalues of $H _ { 0 }$ is 1. The gap between 0 and the rest of the eigenvalues of $H _ { 1 }$ is bounded from below by $1 / \kappa$ (see Appendix A).

QLSP can be solved if we can prepare the zero-energy state $\vert \widetilde { x } \rangle$ of $H _ { 1 }$ , which can be achieved by the AQC approach. Let $H ( f ( s ) ) = ( 1 - f ( s ) ) H _ { 0 } + f ( s ) H _ { 1 } , 0 \leq s \leq 1 .$ . The function $f : [ 0 , 1 ] \to [ 0 , 1 ]$ is called a scheduling function, and is a strictly increasing mapping with $f ( 0 ) = 0 , f ( 1 ) = 1$ . The simplest choice is $f ( s ) = s$ , which gives the “vanilla AQC”. We sometimes omit the $s$ -dependence as $H ( f )$ to emphasize the dependence on $f$ . Note that for any $s$ , $\mathinner { | { \bar { b } } \rangle }$ is always in $\mathrm { N u l l } ( H ( f ( s ) ) )$ , and there exists a state $| \widetilde { x } ( s ) \rangle = | 0 , x ( s ) \rangle$ , such that ${ \mathrm { N u l l } } ( H ( f ( s ) ) ) = \{ | \widetilde { x } ( s ) \rangle , | \bar { b } \rangle \}$ . In particular, $| \widetilde { x } ( 0 ) \rangle =$ $\mathinner { | { \widetilde { b } } \rangle }$ and $| \widetilde { x } ( 1 ) \rangle = | \widetilde { x } \rangle$ , and therefore $| \widetilde { x } ( s ) \rangle$ is the desired adiabatic path. Let $P _ { 0 } ( s )$ be the projection to the subspace $\mathrm { N u l l } ( H ( f ( s ) ) )$ , which is a rank-2 projection operator $P _ { 0 } ( s ) = | \widetilde { x } ( s ) \rangle \langle \widetilde { x } ( s ) | + | \bar { b } \rangle \langle \bar { b } |$ .

Furthermore, the eigenvalue 0 is separated from the rest of the eigenvalues of $H ( f ( s ) )$ by a gap

$$
\Delta ( f ( s ) ) \geq \Delta _ { * } ( f ( s ) ) : = 1 - f ( s ) + f ( s ) / \kappa .
$$

We refer to Appendix A for the derivation.

Consider the adiabatic evolution

$$
\frac { 1 } { T } { \mathrm { i } } \partial _ { s } \left| \psi _ { T } ( s ) \right. = H ( f ( s ) ) \left| \psi _ { T } ( s ) \right. , \quad \left| \psi _ { T } ( 0 ) \right. = \left| \widetilde { b } \right. ,
$$

where $0 ~ \leq ~ s ~ \leq ~ 1$ , and the parameter $T$ is called the runtime of AQC. The quantum adiabatic theorem [19, Theorem 3] states that for any $0 \leq s \leq 1$ ,

$$
| 1 - \langle \psi _ { T } ( s ) | P _ { 0 } ( s ) | \psi _ { T } ( s ) \rangle | \le \eta ^ { 2 } ( s ) ,
$$

where

$$
\eta ( s ) = C \Big \{ \frac { \| H ^ { ( 1 ) } ( 0 ) \| _ { 2 } } { T \Delta ^ { 2 } ( 0 ) } + \frac { \| H ^ { ( 1 ) } ( s ) \| _ { 2 } } { T \Delta ^ { 2 } ( f ( s ) ) } + \frac { 1 } { T } \int _ { 0 } ^ { s } \left( \frac { \| H ^ { ( 2 ) } ( s ^ { \prime } ) \| _ { 2 } } { \Delta ^ { 2 } ( f ( s ^ { \prime } ) ) } + \frac { \| H ^ { ( 1 ) } ( s ^ { \prime } ) \| _ { 2 } ^ { 2 } } { \Delta ^ { 3 } ( f ( s ^ { \prime } ) ) } \right) d s ^ { \prime } \Big \} .
$$

The derivatives of $H$ are taken with respect to $s$ , i.e. $\begin{array} { r } { H ^ { ( k ) } ( s ) : = \frac { d ^ { k } } { d s ^ { k } } H ( f ( s ) ) , k = 1 , 2 . } \end{array}$ Throughout the paper, we shall use a generic symbol $C$ to denote constants independent of $s , \Delta , T$ .

Intuitively, the quantum adiabatic theorem in Eq. (3) says that, if the initial state is an eigenstate corresponding to the eigenvalue 0, then for large enough $T$ the state $| \psi _ { T } ( s ) \rangle$ will almost stay in the eigenspace of $H ( s )$ corresponding to the eigenvalue 0, where there is a double degeneracy and only one of the eigenstate $| \widetilde { x } ( s ) \rangle$ is on the desired adiabatic path. However, such degeneracy will not break the effectiveness of AQC for the following reason. Note that $\langle \bar { b } | \psi _ { T } ( 0 ) \rangle = 0$ , and ${ \cal H } ( f ( s ) ) | \bar { b } \rangle = 0$ for all $0 \leq s \leq 1$ , so the Schrödinger dynamics (2) implies $\langle \bar { b } | \psi _ { T } ( s ) \rangle = 0$ , which prevents any transition of $| \psi _ { T } ( s ) \rangle$ to $\mathinner { | { \bar { b } } \rangle }$ . Therefore the adiabatic path will stay along $| \widetilde { x } ( s ) \rangle$ . Using $\bar { \langle b | } \psi _ { T } ( s ) \rangle = \bar { 0 }$ , we have $P _ { 0 } ( s ) | \psi _ { T } ( s ) \rangle = | \widetilde { x } ( s ) \rangle \ \langle \widetilde { x } ( s ) | \psi _ { T } ( s ) \rangle$ . Therefore the estimate in Equation (3) becomes

$$
1 - | \langle \psi _ { T } ( s ) | \widetilde { x } ( s ) \rangle | ^ { 2 } \le \eta ^ { 2 } ( s ) .
$$

This also implies that (see Appendix B)

$$
\| | \psi _ { T } ( s ) \rangle \langle \psi _ { T } ( s ) | - | \widetilde { x } ( s ) \rangle \langle \widetilde { x } ( s ) | \| _ { 2 } \leq \eta ( s ) .
$$

Therefore $\eta ( 1 )$ can be an upper bound of the distance of the density matrix.

If we simply assume $\| H ^ { ( 1 ) } \| _ { 2 } , \| H ^ { ( 2 ) } \| _ { 2 }$ are bounded by constants, and use the worst case bound that $\Delta \geq \kappa ^ { - 1 }$ , we arrive at the conclusion that in order to have $\eta ( 1 ) \leq \epsilon$ , the runtime of vanilla AQC is $T \gtrsim \kappa ^ { 3 } / \epsilon$ .

# 3 AQC(P) METHOD

Our goal is to reduce the runtime by choosing a proper scheduling function. The key observation is that the accuracy of AQC depends not only on the gap $\Delta ( f ( s ) )$ but also on the derivatives of $H ( f ( s ) )$ , as revealed in the estimate in Equation (4). Therefore it is possible to improve the accuracy if a proper time schedule allows the Hamiltonian $H ( f ( s ) )$ to slow down when the gap is close to 0. We consider the following schedule [1, 19]

$$
\dot { f } ( s ) = c _ { \phi } \Delta _ { * } ^ { p } ( f ( s ) ) , \quad f ( 0 ) = 0 , \quad p > 0 .
$$

Here $\Delta _ { * }$ is defined in Eq. (1) and $\begin{array} { r } { c _ { p } = \int _ { 0 } ^ { 1 } \Delta _ { * } ^ { - p } ( u ) d u } \end{array}$ is a normalization constant chosen so that $f ( 1 ) = 1$ . When $1 < p \leq 2$ , Eq. (5) can be explicitly solved as

$$
f ( s ) = \frac { \kappa } { \kappa - 1 } \left[ 1 - \left( 1 + s ( \kappa ^ { p - 1 } - 1 ) \right) ^ { \frac { 1 } { 1 - p } } \right] .
$$

ACM Trans. Quantum Comput., Vol. 3, No. 2, Article 5. Publication date: February 2022.

Note that as $s \to 1$ , $\Delta _ { * } ( f ( s ) ) \to \kappa ^ { - 1 }$ , and therefore the dynamics of $f ( s )$ slows down as $f  1$ and the gap decreases towards $\kappa ^ { - 1 }$ . We refer to the adiabatic dynamics (Equation (2)) with the schedule in Equation (5) as the $\mathsf { A Q C } ( \mathsf { p } )$ scheme. Our main result is given in Theorem 1 (See Appendix D for the proof).

Theorem 1. Let $A \in \mathbb { C } ^ { N \times N }$ be a Hermitian positive definite matrix with condition number $\kappa$ . For any choice of $1 < p < 2$ , the error of the $A Q C ( p )$ scheme satisfies

$$
\| | \psi _ { T } ( 1 ) \rangle \langle \psi _ { T } ( 1 ) | - | \widetilde { x } \rangle \langle \widetilde { x } | \| _ { 2 } \leq C \kappa / T .
$$

Therefore in order to prepare an $\epsilon -$ approximation of the solution of QLSP it suffices to choose the runtime $T = O ( \kappa / \epsilon )$ . Furthermore, when $ p = 1 , 2$ , the bound for the runtime becomes $T = O ( \kappa \log ( \kappa ) / \epsilon )$ .

The runtime complexity of the AQC(p) method with respect to $\kappa$ is only $O ( \kappa )$ . Compared to Ref. [30], AQC(p) further removes the $\log ( \kappa )$ dependence when $1 < p < 2$ , and hence reaches the optimal complexity with respect to $\kappa$ . Interestingly, though not explicitly mentioned in [30], the success of RM for solving QLSP relies on a proper choice of the scheduling function, which approximately corresponds to $\mathrm { { A Q C } ( p { = } 1 ) }$ . It is this scheduling function, rather than the QZE or its Monte Carlo approximation per se that achieves the desired $O ( \kappa \log \kappa )$ scaling with respect to $\kappa$ . Furthermore, the scheduling function in RM is similar to the choice of the schedule in the $\mathrm { { A Q C } ( p { = } 1 ) }$ scheme. The speedup of AQC(p) versus the vanilla AQC is closely related to the quadratic speedup of the optimal time complexity of AQC for Grover’s search [1, 19, 27, 28], in which the optimal time scheduling reduces the runtime from √ $T \sim O ( N )$ (i.e. no speedup compared to classical algorithms) to $T \sim \tilde { \cal O ( \sqrt { N } ) }$ (i.e. Grover speedup). In fact, the choice of the scheduling function in Ref. [28] corresponds to $\scriptstyle \mathrm { A Q C } ( \mathrm { p } = 2 )$ and that in Ref. [19] corresponds to ${ \mathsf { A Q C } } ( 1 { < } { \mathsf { p } } { < } 2 )$ .

# 4 AQC(EXP) METHOD

Although $\mathsf { A Q C } ( \mathsf { p } )$ achieves the optimal runtime complexity with respect to $\kappa$ , the dependence on $\epsilon$ is still $O ( \epsilon ^ { - 1 } )$ , which limits the method from achieving high accuracy. It turns out that when $T$ is sufficiently large, the dependence on $\epsilon$ could be improved to $O ( \mathrm { p o l y } \log ( 1 / \epsilon ) )$ , by choosing an alternative scheduling function.

The basic observation is as follows. In the AQC(p) method, the adiabatic error bound we consider, i.e. Eq. (4), is the so-called instantaneous adiabatic error bound, which holds true for all $s \in [ 0 , 1 ]$ . However, when using AQC for solving QLSP, it suffices only to focus on the error bound at the final time $s \ = \ 1$ . It turns out that this allows us to obtain a tighter error bound. In fact, such an error bound can be exponentially small with respect to the runtime [1, 15, 25, 32]. Roughly speaking, with an additional assumption for the Hamiltonian $H ( f ( s ) )$ that the derivatives of any order vanish at $s = 0 , 1$ , the adiabatic error can be bounded by $c _ { 1 } \exp ( - c _ { 2 } T ^ { \alpha } )$ for some positive constants $c _ { 1 } , c _ { 2 } , \alpha$ . Furthermore, it is proved in [15] that if the target eigenvalue is simple, then $c _ { 1 } = O ( \Delta _ { * } ^ { - 1 } )$ and $c _ { 2 } = O ( \Delta _ { * } ^ { 3 } )$ . Note that $\Delta _ { * } \geq \kappa ^ { - 1 }$ for QLSP, thus, according to this bound, to obtain an $\epsilon$ -approximation, it suffices to choose $T = O ( \kappa ^ { 3 } \mathrm { p o l y } ( \log ( \kappa / \epsilon ) ) )$ . This is an exponential speedup with respect to $\epsilon$ , but the dependence on the condition number becomes cubic again.

However, it is possible to reduce the runtime if the change of the Hamiltonian is slow when the gap is small, as we have already seen in the $\mathsf { A Q C } ( \mathsf { p } )$ method. For QLSP, the gap monotonically decreases, and the smallest gap occurs uniquely at the final time, where the Hamiltonian $H ( s )$ can be set to vary slowly by requiring its derivatives to vanish at the boundary.

We consider the following schedule

$$
f ( s ) = c _ { e } ^ { - 1 } \int _ { 0 } ^ { s } \exp \left( - \frac { 1 } { s ^ { \prime } ( 1 - s ^ { \prime } ) } \right) \mathrm { d } s ^ { \prime }
$$

ACM Trans. Quantum Comput., Vol. 3, No. 2, Article 5. Publication date: February 2022.

where $\begin{array} { r } { c _ { e } = \int _ { 0 } ^ { 1 } \exp \left( - 1 / ( s ^ { \prime } ( 1 - s ^ { \prime } ) ) \right) \mathrm { d } } \end{array}$ $\mathrm { d } s ^ { \prime }$ is a normalization constant such that $f ( 1 ) = 1$ . This schedule can assure that $H ^ { ( k ) } ( 0 ) = H ^ { ( k ) } ( 1 ) = 0$ for all $k \geq 1$ . We refer to the adiabatic dynamics (Equation (2)) with the schedule in Equation (8) as the AQC(exp) scheme. Our main result is given in Theorem 2 (see Appendix E for the proof).

Theorem 2. Let $A \in \mathbb { C } ^ { N \times N }$ be a Hermitian positive definite matrix with condition number $\kappa$ . Then for large enough $T > 0$ , the final time error $\parallel | \psi _ { T } ( 1 ) \rangle \left. \psi _ { T } ( 1 ) | - | \widetilde { x } \right. \langle \widetilde { x } | \parallel _ { 2 }$ of the $A Q C ( e x p )$ scheme is bounded by

$$
C \log ( \kappa ) \exp \left( - C \left( \frac { \kappa \log ^ { 2 } \kappa } { T } \right) ^ { - \frac { 1 } { 4 } } \right) .
$$

Therefore for any $\kappa > e$ , $0 < \epsilon < 1$ , in order to prepare an $\epsilon -$ approximation of the solution of QLSP, it suffices to choose the runtime $T = O \left( \kappa \log ^ { 2 } ( \kappa ) \log ^ { 4 } \left( \frac { \log \kappa } { \epsilon } \right) \right)$ .

Compared with RM and $\mathsf { A Q C } ( \mathsf { p } )$ , although the $\log ( \kappa )$ dependence reoccurs, AQC(exp) achieves an exponential speedup over RM and AQC(p) with respect to $\epsilon$ (and hence giving its name), and thus is more suitable for preparing the solution of QLSP with high fidelity. Furthermore, the time scheduling of $\mathsf { A Q C } ( \exp )$ is universal and AQC(exp) does not require knowledge on the bound of $\kappa$

We remark that the performance of the $\mathsf { A Q C } ( \exp )$ method is sensitive to the perturbations in the scheduling function, which can affect the final error in the AQC(exp) method. This is similar to the finite precision effect in the adiabatic Grover search reported in [18]. Therefore the scheduling function should be computed to sufficient accuracy on classical computers using numerical quadrature, and implemented accurately as a control protocol on quantum computers.

# 5 GATE-BASED IMPLEMENTATION OF AQC

We briefly discuss how to implement $\mathsf { A Q C } ( \mathsf { p } )$ and $\mathsf { A Q C } ( \exp )$ on a gate-based quantum computer. Since $| \psi _ { T } ( s ) \rangle = \mathcal { T } \exp ( - \mathrm { i } T \int _ { 0 } ^ { s } H ( f ( s ^ { \prime } ) ) d s ^ { \prime } ) \bar { | \psi _ { T } ( 0 ) \rangle }$ , where $\mathcal { T }$ is the time-ordering operator, it is sufficient to implement an efficient time-dependent Hamiltonian simulation of $H ( f ( s ) )$ .

One straightforward approach is to use the Trotter splitting method. The lowest order approximation takes the form

$$
\begin{array} { r l r } {  { \mathcal { T } \exp ( - \mathrm { i } T \int _ { 0 } ^ { s } H ( f ( s ^ { \prime } ) ) \mathrm { d } s ^ { \prime } ) \approx \prod _ { m = 1 } ^ { M } \exp ( - \mathrm { i } T h H ( f ( s _ { m } ) ) ) } } \\ & { } & { \approx \displaystyle \prod _ { m = 1 } ^ { M } \exp ( - \mathrm { i } T h ( 1 - f ( s _ { m } ) ) H _ { 0 } ) \exp ( - \mathrm { i } T h f ( s _ { m } ) H _ { 1 } ) } \end{array}
$$

where $h = s / M , s _ { m } = m h .$ . It is proved in [31] that the error of such an approximation is $O ( \mathrm { p o l y } ( \log ( N ) ) T ^ { 2 } / M )$ , which indicates that to achieve an $\epsilon$ -approximation, it suffices to choose ${ \cal M } = { \cal O } ( \mathrm { p o l y } ( \log ( N ) ) T ^ { 2 } / \epsilon )$ . On a quantum computer, the operations $e ^ { - \mathrm { i } \tau H _ { 0 } }$ , $e ^ { - \mathrm { i } \tau H _ { 1 } }$ require a timeindependent Hamiltonian simulation process, which can be implemented via techniques such as LCU and QSP [4, 22]. For a $d$ -sparse matrix $A$ , according to [5], the query complexity is $\widetilde { \cal O } ( d \tau \log ( d \tau / \epsilon ) )$ for a single step. Here $f = \widetilde { O } ( g )$ if $f = O ( g { \mathrm { p o l y l o g } } ( g ) )$ . Note that the total sum of the simulation time of single steps is exactly $T$ regardless of the choice of $M$ , and the total query complexity is $\widetilde { O } ( d T \log ( d T / \epsilon ) )$ . Using Theorem 1 and 2, the query complexity of $\mathsf { A Q C } ( \mathsf { p } )$ and $\mathsf { A Q C } ( \exp )$ i s $\widetilde { O } ( d \kappa / \epsilon \log ( d \kappa / \epsilon ) )$ and $\widetilde { \cal O } ( d \kappa \mathrm { \ p o l y } ( \log ( d \kappa / \epsilon ) ) )$ , respectively. Nevertheless, $M$ scales as $O ( T ^ { 2 } )$ with respect to the runtime $T$ , which implies that the number of time slices should be at least $O ( \kappa ^ { 2 } )$ . Therefore the gate complexity scales superlinearly with respect to $\kappa$ . The scaling of the

<table><tr><td></td><td>AQC(p)</td><td>AQC(exp)</td></tr><tr><td>Queries</td><td>O(dκ/ log(dκ/))</td><td>O(dκ poly(log(dκ/e)))</td></tr><tr><td>Qubits</td><td>O(n + log(dκ/e))</td><td>(n + log(dκ/))</td></tr><tr><td>Primitive gates</td><td>O(ndκ/e poly(log(dκ/e)))</td><td>O(ndk poly(log(dκ/e)))</td></tr></table>

Table 1. Computational costs of $\mathsf { A O C } ( \mathsf { p } )$ and AQC(exp) via a time-dependent Hamiltonian simulation using the truncated Dyson expansion [23].

Trotter expansion can be improved using high order Trotter-Suzuki formula as well as the recently developed commutator-based error analysis [13], but we will not pursue this direction here.

There is an efficient way to directly perform the time evolution of $H ( f ( s ) )$ without using the splitting strategy, following the algorithm proposed by Low and Wiebe in [23], where the timedependent Hamiltonian simulation is performed based on a truncated Dyson expansion. A detailed discussion on how to implement this algorithm in a gate-efficient way is presented in [20, Appendix C], and here we summarize the basic idea as follows. Assume that we are given two input query models: ${ \mathcal { P } } _ { A }$ that gives the locations and values of the nonzero entries of the matrix $A$ , and $\mathcal { P } _ { B }$ that produces the quantum state $| b \rangle$ . Here the input query models are the same as those in [12]. Then one can construct the block-encoding representations of the matrix $A$ [16] and the matrix $Q _ { b }$ with $O ( 1 )$ additional primitive gates. Next, the block-encodings of $A$ and $Q _ { b }$ can be applied to build the block-encodings of $H _ { 0 }$ and $H _ { 1 }$ , and then the HAM-T model, which is a block-encoding of the select oracle of the time-dependent Hamiltonian $H ( s )$ evaluated at different time steps and serves as the input model in the truncated Dyson series method [23]. Finally, after the construction of HAM-T, the adiabatic dynamics can be simulated following the procedure for solving time-dependent Schrödinger equations discussed in [23].

The costs of $\mathsf { A Q C } ( \mathsf { p } )$ and AQC(exp) are summarized in Table 1, where for both $\mathsf { A Q C } ( \mathsf { p } )$ and $\mathsf { A Q C } ( \exp )$ , almost linear dependence with respect to $\kappa$ is achieved. The almost linear dependence on $\kappa$ cannot be expected to be improved to $\bar { O ( \kappa ^ { 1 - \delta } ) }$ with any $\delta > 0$ [17]. Thus both AQC(p) and $\mathsf { A Q C } ( \exp )$ are almost optimal with respect to $\kappa$ , and AQC(exp) further achieves an exponential speedup with respect to $\epsilon$ .

# 6 QAOA FOR SOLVING QLSP

The quantum approximate optimization algorithm (QAOA) [14] considers the following parameterized wavefunction

$$
\left. \psi _ { \theta } \right. : = e ^ { - \mathrm { i } \gamma _ { P } H _ { 1 } } e ^ { - \mathrm { i } \beta _ { P } H _ { 0 } } \cdot \cdot \cdot e ^ { - \mathrm { i } \gamma _ { 1 } H _ { 1 } } e ^ { - \mathrm { i } \beta _ { 1 } H _ { 0 } } \left. \psi _ { i } \right. .
$$

Here $\theta$ denotes the set of $2 P$ adjustable real parameters $\{ \beta _ { i } , \gamma _ { i } \} _ { i = 1 } ^ { P }$ , and $| \psi _ { i } \rangle$ is an initial wavefunction. The goal of QAOA is to choose $| \psi _ { i } \rangle$ and to tune $\theta$ , so that $| \psi _ { \theta } \rangle$ approximates a target state. In the context of QLSP, we may choose $\left| \psi _ { i } \right. = \left| \widetilde { b } \right.$ , and each step of the QAOA ansatz in Eq. (11) can be efficiently implemented using the quantum singular value transformation [16]. More specifically, as discussed in Section 5 and in [20], the block-encodings of $H _ { 0 }$ and $H _ { 1 }$ can be efficiently constructed via the input models for the matrix $A$ and the vector $| b \rangle$ . Then the quantum singular value transformation can be directly applied to simulate $e ^ { - \mathrm { i } \beta H _ { 0 } }$ and $e ^ { - \mathrm { i } \gamma H _ { 1 } }$ . According to [16, Corollary 62], the cost of each single simulation scales linearly in time and logarithmically in precision, and hence the total complexity of implementing a QAOA ansatz scales linearly in total runtime of QAOA, defined to be $\begin{array} { r } { T : = \sum _ { i = 1 } ^ { P } \dot { ( | \beta _ { i } | + \rvert \gamma _ { i } | ) } } \end{array}$ , and logarithmically in precision. Notice that with a sufficiently large $P$ , the optimal Trotter splitting method becomes a special form of Eq. (11). Hence Theorem 2 implies that with an optimal choice of $\{ \beta _ { i } , \gamma _ { i } \} _ { i = 1 } ^ { P }$ , the QAOA runtime $T$ is at most $O ( \kappa \mathrm { p o l y } ( \log ( \kappa / \epsilon ) ) )$ . We remark that the validity of such an upper bound requires a sufficiently large $P$ and an optimal choice of $\theta$ . On the other hand, our numerical results suggest that the same scaling can be achieved with a much smaller $P$ .

For a given $P$ , the optimal $\theta$ maximizes the fidelity as

$$
\operatorname* { m a x } _ { \theta } F _ { \theta } : = \mid \langle \psi _ { \theta } | { \widetilde { x } } \rangle \mid ^ { 2 } .
$$

However, the maximization of the fidelity requires the knowledge of the exact solution $\vert \widetilde { x } \rangle$ which is not practical. We may instead solve the following minimization problem

$$
\operatorname* { m i n } _ { \theta } \langle \psi _ { \theta } | H _ { 1 } ^ { 2 } | \psi _ { \theta } \rangle .
$$

Since the null space of $H _ { 1 }$ is of dimension 2, the unconstrained minimizer $| \psi _ { \boldsymbol { \theta } } \rangle$ seems possible to only have a small overlap with $\vert \widetilde { x } \rangle$ . However, this is not a problem due to the choice of the initial state $| \psi _ { i } \rangle = | \widetilde { b } \rangle$ . Notice that by the variational principle the minimizer $| \psi _ { \theta } \rangle$ maximizes $\langle \psi _ { \theta } | P _ { 0 } ( 1 ) | \psi _ { \theta } \rangle$ . Using the fact that $e ^ { - \mathrm { i } \beta H _ { 0 } } \left| \bar { b } \right. = e ^ { - \mathrm { i } \gamma H _ { 1 } } \left| \bar { b } \right. = \left| \bar { b } \right.$ for any $\beta , \gamma$ , we obtain $\langle { \bar { b } } | \psi _ { \theta } \rangle = \langle { \bar { b } } | { \widetilde { b } } \rangle = 0$ , which means the QAOA ansatz prevents the transition to $| \bar { b } \rangle$ , similar to AQC. Then $\langle \psi _ { \theta } | P _ { 0 } ( 1 ) | \psi _ { \theta } \rangle =$ $\left. \psi _ { \theta } | \widetilde { x } \right. \left. \widetilde { x } | \psi _ { \theta } \right. = F _ { \theta }$ , so the minimizer of Eq. (12) indeed maximizes the fidelity.

For every choice of $\theta$ , we evaluate the expectation value $\langle \psi _ { \boldsymbol \theta } | H _ { 1 } ^ { 2 } | \psi _ { \boldsymbol \theta } \rangle$ . Then the next $\theta$ is adjusted on a classical computer towards minimizing the objective function. The process is repeated till convergence. Efficient classical algorithms for the optimization of parameters in QAOA are currently an active topic of research, including methods using gradient optimization [24, 36], Pontryagin’s maximum principle (PMP) [3, 35], reinforcement learning [9, 26], to name a few. Algorithm 1 describes the procedure using QAOA to solve QLSP.

# Algorithm 1 QAOA for solving QLSP

1: Initial parameters $\theta ^ { ( 0 ) } = \{ \beta _ { i } , \gamma _ { i } \} _ { i = 1 } ^ { 2 P }$ .   
2: for $k = 0 , 1 , \ldots$ do   
3: Perform Hamiltonian simulation to obtain 𝜓 (𝑘)𝜃   
4: Measure $O ( \theta ^ { ( k ) } ) = \langle \psi _ { \theta } ^ { ( k ) } | H _ { 1 } ^ { 2 } | \psi _ { \theta } ^ { ( k ) } \rangle$ .   
5: If $O ( \theta ^ { ( k ) } ) < \epsilon ^ { 2 } / \kappa ^ { 2 }$ , exit the loop.   
6: Choose $\theta ^ { ( k + 1 ) }$ using a classical optimization method.   
7: end for

Compared to $\mathsf { A Q C } ( \mathsf { p } )$ and AQC(exp), QAOA has the following two potential advantages. The first advantage is that QAOA provides the possibility of going beyond AQC-based algorithms. Notice that the Trotter splitting method is a special form of the QAOA ansatz in Eq. (11). If the angles $\{ \beta _ { i } , \gamma _ { i } \} _ { i = 1 } ^ { P }$ have been properly optimized (which is a very strong assumption and will be further discussed later), the total QAOA runtime $T$ will be by definition comparable to or even shorter than the runtime of AQC with the best scheduling function (after discretization). Second, one way of implementing AQC(p) and AQC(exp) using an operator splitting method requires the time interval to be explicitly split into a large number of intervals, while numerical results indicate that the number of intervals $P$ in QAOA can be much smaller. This could reduce the depth of the quantum circuit. Compared to AQC, QAOA has the additional advantage that it only consists of $2 P$ time-independent Hamiltonian simulation problem, once $\theta$ is known.

Despite the potential advantages, several severe caveats of using QAOA for QLSP arise when we consider beyond the time complexity. The first is that classical optimization of the angles $\{ \beta _ { i } , \gamma _ { i } \} _ { i = 1 } ^ { P }$ can be difficult. Commonly used classical optimization algorithms, such as the gradient descent method, are likely to be stuck at local optimizers and thus result in sub-optimal performance. The cost for the classical optimization is also hard to known a priori. The optimization may require many iterations, which can diminish the gain of the runtime reduction. The second is related to the accurate computation of the objective function $O ( \theta ^ { ( k ) } )$ . Note that the minimal spectrum gap of $H _ { 1 }$ is $O ( \kappa ^ { - 1 } )$ . In order to obtain an $\epsilon$ -approximation, the precision of measuring $O ( \theta ) = \langle \psi _ { \theta } | H _ { 1 } ^ { 2 } | \psi _ { \theta } \rangle$ should be at least $O ( \epsilon ^ { 2 } / \kappa ^ { 2 } )$ . Hence $O ( \kappa ^ { 4 } / \epsilon ^ { 4 } )$ repeated measurements can be needed to achieve the desired accuracy.

# 7 GENERALIZATION TO NON-HERMITIAN MATRICES

Now we discuss the case when $A$ is not Hermitian positive definite. First, we still assume that $A$ is Hermitian (but not necessarily positive definite). In this case, we adopt the family of Hamiltonians introduced in [30], which overcomes the difficulty brought by the indefiniteness of $A$ at the expense of enlarging the Hilbert space to dimension $4 N$ (so two ancilla qubits are needed to enlarge the matrix block). Here we define

$$
H _ { 0 } = \sigma _ { + } \otimes \left[ ( \sigma _ { z } \otimes I _ { N } ) Q _ { + , b } \right] + \sigma _ { - } \otimes \left[ Q _ { + , b } ( \sigma _ { z } \otimes I _ { N } ) \right]
$$

where $Q _ { + , b } ~ = ~ I _ { 2 N } - \left| + , b \right. \left. + , b \right|$ , and $\begin{array} { r } { | \pm \rangle \ = \ \frac { 1 } { \sqrt { 2 } } \big ( | 0 \rangle \pm | 1 \rangle \big ) } \end{array}$ . The null space of $H _ { 0 }$ is $\mathrm { N u l l } ( H _ { 0 } ) =$ $s \mathrm { p a n } \{ \left| 0 , - , b \right. , \left| 1 , + , b \right. \}$ . We also define

$$
H _ { 1 } = \sigma _ { + } \otimes \left[ ( \sigma _ { x } \otimes A ) Q _ { + , b } \right] + \sigma _ { - } \otimes \left[ Q _ { + , b } ( \sigma _ { x } \otimes A ) \right]
$$

Note that $\mathrm { N u l l } ( H _ { 1 } ) = \operatorname { s p a n } \{ \left| 0 , + , x \right. , \left| 1 , + , b \right. \}$ . Therefore the solution of the QLSP can be obtained if we can prepare the zero-energy state $\left| 0 , + , x \right.$ of $H _ { 1 }$ .

The family of Hamiltonians for $\mathsf { A Q C } ( \mathsf { p } )$ is still given by $H ( f ( s ) ) = ( 1 - f ( s ) ) H _ { 0 } + f ( s ) H _ { 1 } , 0 \leq s \leq 1$ . Similar to the case of Hermitian positive definite matrices, there is a double degeneracy of the eigenvalue 0, and we aim at preparing one of the eigenstate via time-optimal adiabatic evolution. More precisely, for any $s$ , $| 1 , + , b \rangle$ is always in $\mathrm { N u l l } ( H ( f ( s ) ) )$ , and there exists a state $| \widetilde { x } ( s ) \rangle$ with $\left| \widetilde { x } ( 0 ) \right. = \left| 0 , - , b \right. , \left| \widetilde { x } ( 1 ) \right. = \left| 0 , + , x \right.$ , such that $\mathrm { N u l l } ( H ( f ( s ) ) ) = \left\{ \left| \widetilde { x } ( s ) \right. , \left| 1 , + , b \right. \right\}$ e. Such degeneracy will not influence the adiabatic computation starting with $\left| 0 , - , b \right.$ for the same reason we discussed for Hermitian positive definite case (also discussed in [30]), and the error of $\mathsf { A Q C } ( \mathsf { p } )$ is still bounded by $\eta ( s )$ given in Eq. (4).

Furthermore, the eigenvalue 0 is separated from the rest of the eigenvalues of $H ( f ( s ) )$ by a gap $\Delta ( f ( s ) ) \geq { \sqrt { ( 1 - f ( s ) ) ^ { 2 } + ( f ( s ) / \kappa ) ^ { 2 } } }$ [30]. For technical simplicity, note that $\sqrt { ( 1 - f ) ^ { 2 } + ( f / \kappa ) ^ { 2 } } \geq$ $( 1 - f + f / \kappa ) / \sqrt { 2 }$ for all $0 \leq f \leq 1$ , we define the lower bound of the gap to be $\Delta _ { * } ( f ) = ( 1 - f +$ $f / \kappa ) / \sqrt { 2 }$ , which is exactly proportional to that for the Hermitian positive definite case. Therefore, we can use exactly the same time schedules as the Hermitian positive definite case to perform $\mathsf { A Q C } ( \mathsf { p } )$ and AQC(exp) schemes, and properties of AQC(p) and AQC(exp) are stated in the following theorems (see Appendices $\mathrm { D }$ and E for the proof).

Theorem 3. Let $A \in \mathbb { C } ^ { N \times N }$ be a Hermitian matrix (not necessarily positive definite) with condition number $\kappa$ . For any choice of $1 < p < 2$ , the $A Q C ( p )$ scheme gives

$$
\| \ | \psi _ { T } ( s ) \rangle \langle \psi _ { T } ( s ) | - | 0 , + , x \rangle \langle 0 , + , x | \| _ { 2 } \leq C \kappa / T .
$$

Therefore, in order to prepare an $\epsilon -$ approximation of the solution of $Q L S P ,$ it suffices to choose the runtime $T = O ( \kappa / \epsilon )$ . Furthermore, when $p \ = \ 1 , 2$ , the bound of the runtime becomes $T \ =$ $O ( \kappa \log ( \kappa ) / \epsilon )$ .

Theorem 4. Let $A \in \mathbb { C } ^ { N \times N }$ be a Hermitian matrix (not necessarily positive definite) with condition number $\kappa$ . Then for large enough $T > 0$ , the final time error $\| | \psi _ { T } ( 1 )   \psi _ { T } ( 1 ) | - | 0 , + , x   0 , + , x | \| _ { 2 }$ of

<table><tr><td>methods</td><td>scaling w.r.t. K</td><td>scaling w.r.t. 1/e</td></tr><tr><td>vanilla AQC</td><td>2.2022</td><td>/</td></tr><tr><td>RM</td><td>1.4912</td><td>1.3479</td></tr><tr><td>AQC(1)</td><td>1.4619</td><td>1.0482</td></tr><tr><td>AQC(1.25)</td><td>1.3289</td><td>1.0248</td></tr><tr><td>AQC(1.5)</td><td>1.2262</td><td>1.0008</td></tr><tr><td>AQC(1.75)</td><td>1.1197</td><td>0.9899</td></tr><tr><td>AQC(2)</td><td>1.1319</td><td>0.9904</td></tr><tr><td>AQC(exp)</td><td>1.3718</td><td>0.5377</td></tr><tr><td>AQC(exp)</td><td>/</td><td>1.7326 (w.r.t. log(1/e))</td></tr><tr><td>QAOA</td><td>1.0635</td><td>0.4188</td></tr><tr><td>QAOA</td><td>/</td><td>1.4927 (w.r.t. log(1/e))</td></tr></table>

Table 2. Numerical scaling of the runtime as a function of the condition number and the accuracy, respectively, for the Hermitian positive definite example.

the $A Q C ( e x p )$ scheme is bounded by

$$
C \log ( \kappa ) \exp \left( - C \left( \frac { \kappa \log ^ { 2 } \kappa } { T } \right) ^ { - \frac { 1 } { 4 } } \right) .
$$

Therefore, for any $\kappa > e$ , $0 < \epsilon < 1$ , in order to prepare an $\epsilon -$ approximation of the solution of QLSP, it suffices to choose the runtime $T = O \left( \kappa \log ^ { 2 } ( \kappa ) \log ^ { 4 } \left( \frac { \log \kappa } { \epsilon } \right) \right)$ .

For a most general square matrix $A \ \in \ \mathbb { C } ^ { N \times N }$ , following [17] we may transform it into the Hermitian case at the expense of further doubling the dimension of the Hilbert space. Consider an extended QLSP ${ \mathfrak { A } } | { \mathfrak { x } } \rangle = | { \mathfrak { b } } \rangle$ in dimension $2 N$ where

$$
\mathfrak { A } = \sigma _ { + } \otimes A + \sigma _ { - } \otimes A ^ { \dag } = \left( \begin{array} { c c } { { 0 } } & { { A } } \\ { { A ^ { \dag } } } & { { 0 } } \end{array} \right) , \quad \left| \mathfrak { b } \right. = \left| 1 , b \right. .
$$

Note that $\mathfrak { Y }$ is a Hermitian matrix of dimension $2 N$ , with condition number $\kappa$ and $\| \mathfrak { A } \| _ { 2 } = 1$ , and $| { \mathfrak { x } } \rangle : = | 1 , x \rangle$ solves the extended QLSP. Therefore we can directly apply $\mathsf { A Q C } ( \mathsf { p } )$ and AQC(exp) for Hermitian matrix $\mathfrak { Y }$ to prepare an $\epsilon$ -approximation of $x$ . The total dimension of the Hilbert space becomes $8 N$ for non-Hermitian matrix $A$ (therefore three ancilla qubits are needed).

# 8 NUMERICAL RESULTS

We first report the performance of AQC(p), AQC(exp), and QAOA for a series of Hermitian positive definite dense matrices with varying condition numbers, together with the performance of RM and vanilla AQC. The details of the setup of the numerical experiments are given in Appendix F.

Figure 1 shows how the total runtime $T$ depends on the condition number $\kappa$ and the accuracy $\epsilon$ for the Hermitian positive definite case. The numerical scaling is reported in Table 2. For the $\kappa$ dependence, despite that RM and AQC(1) share the same asymptotic linear complexity with respect to $\kappa$ , we observe that the preconstant of RM is larger due to its Monte Carlo strategy and the mixed state nature resulting in the same scaling of errors in fidelity and density (see Appendix C for a detailed explanation). The asymptotic scaling of the vanilla AQC is at least $O ( \kappa ^ { 2 } )$ . When higher fidelity (0.999) is desired, the cost of vanilla AQC becomes too expensive, and we only report the timing of AQC(p), AQC(exp), and QAOA. For the $\kappa$ dependence tests, the depth of QAOA ranges from 8 to 60. For the $\epsilon$ dependence test, the depth of QAOA is fixed to be 20. We find that the runtime for AQC(p), AQC(exp), and QAOA depends approximately linearly on $\kappa$ , while QAOA has the smallest runtime overall. It is also interesting to observe that although the asymptotic scalings of AQC(1) and AQC(2) are both bounded by $O ( \kappa \log \kappa )$ instead of $O ( \kappa )$ , the numerical performance of AQC(2) is much better than AQC(1); in fact, the scaling is very close to that with the optimal value of $\boldsymbol { p }$ . For the $\epsilon$ dependence, the scaling of RM and $\mathsf { A Q C } ( \mathsf { p } )$ is $O ( 1 / \epsilon )$ , which agrees with the error bound. Again the preconstant of RM is slightly larger. Our results also confirm that AQC(exp) only depends poly logarithmically on $\epsilon$ . Note that when $\epsilon$ is relatively large, $\mathsf { A Q C } ( \exp )$ requires a longer runtime than that of $\mathsf { A Q C } ( \mathsf { p } )$ , and it eventually outperforms $\mathsf { A Q C } ( \mathsf { p } )$ when $\epsilon$ is small enough. The numerical scaling of QAOA with respect to $\epsilon$ is found to be only ${ \cal O } ( \log ^ { 1 . 5 } ( 1 / \epsilon ) )$ together with the smallest preconstant.

![](images/b0dce1a614c50f19bdcf13d7e809e89b6a992db0d63eeff32e2f3c07fa7c75ac.jpg)  
Fig. 1. Simulation results for the Hermitian positive definite example. Top (left/right): the runtime to reach desired fidelity $0 . 9 9 / 0 . 9 9 9$ as a function of the condition number. Bottom: a log-log plot of the runtime as a function of the accuracy with $\kappa = 1 0$ .

Figure 2 and Table 3 demonstrate the simulation results for non-Hermitian matrices. We find that numerical performances of RM, AQC(p), AQC(exp), and QAOA are similar to that of the Hermitian positive definite case. Again QAOA obtains the optimal performance in terms of the runtime. The numerical scaling of the optimal $\mathsf { A Q C } ( \mathsf { p } )$ is found to be $O ( \kappa / \epsilon )$ , while the time complexity of QAOA and AQC(exp) is only ${ \cal O } ( \kappa \mathrm { p o l y } ( \log ( \kappa / \epsilon ) ) ) ,$ ) .

![](images/14c0aa51b300fcc53936e12679d2e373f23798f1fcf0e8c90bdbdb02dbbe961e.jpg)  
Fig. 2. Simulation results for the non-Hermitian example. Top: the runtime to reach 0.999 fidelity as a function of the condition number. Bottom: a log-log plot of the runtime as a function of the accuracy with $\kappa = 1 0$ .   
Table 3. Numerical scaling of the runtime as a function of the condition number and the accuracy, respectively, for the non-Hermitian example.

<table><tr><td>methods</td><td>scaling w.r.t. K</td><td>scaling w.r.t. 1/€</td></tr><tr><td>vanilla AQC</td><td>2.1980</td><td>/</td></tr><tr><td>RM</td><td>/</td><td>1.2259</td></tr><tr><td>AQC(1)</td><td>1.4937</td><td>0.9281</td></tr><tr><td>AQC(1.25)</td><td>1.3485</td><td>0.9274</td></tr><tr><td>AQC(1.5)</td><td>1.2135</td><td>0.9309</td></tr><tr><td>AQC(1.75)</td><td>1.0790</td><td>0.9378</td></tr><tr><td>AQC(2)</td><td>1.0541</td><td>0.9425</td></tr><tr><td>AQC(exp)</td><td>1.3438</td><td>0.4415</td></tr><tr><td>AQC(exp)</td><td></td><td>0.9316 (w.r.t. log(1/e))</td></tr><tr><td>QAOA</td><td>0.8907</td><td>0.3283</td></tr><tr><td>QAOA</td><td>/</td><td>0.7410 (w.r.t. log(1/e))</td></tr></table>

# 9 DISCUSSION

By reformulating QLSP into an eigenvalue problem, AQC provides an alternative route to solve QLSP other than those based on phase estimation (such as HHL) and those based on approximation of matrix functions (such as LCU and QSP). However, the scaling of the vanilla AQC is at least $O ( \kappa ^ { 2 } / \epsilon )$ , which is unfavorable with respect to both $\kappa$ and $\epsilon$ . Thanks to the explicit information of the energy gap along the adiabatic path, we demonstrate that we may reschedule the AQC and dramatically improve the performance of AQC for solving QLSP. When the target accuracy $\epsilon$ is relatively large, the runtime complexity of the $\mathsf { A Q C } ( \mathsf { p } )$ method $\left( 1 < p < 2 \right)$ ) is reduced to $O ( \kappa / \epsilon )$ ; for highly accurate calculations with a small $\epsilon$ , the AQC(exp) method is more advantageous, and its runtime complexity is $O ( \kappa \mathrm { p o l y } ( \log ( \kappa / \epsilon ) ) )$ . To our knowledge, our ACP(exp) method provides the first example that an adiabatic algorithm can simultaneously achieve near linear dependence on the spectral gap, and poly-logarithmic dependence on the precision.

Due to the close connection between AQC and QAOA, the runtime complexity of QAOA for solving QLSP is also bounded by $O ( \kappa \mathrm { p o l y } ( \log ( \kappa / \epsilon ) ) )$ . Both AQC and QAOA can be implemented on gate-based quantum computers. Our numerical results can be summarized using the following

relation:

Here $A \ < \ B$ means that the runtime of $A$ is smaller than that of $B$ . The two exceptions are: $Q \mathrm { A O A } \lesssim \mathrm { A Q C } ( \exp )$ means that the runtime of QAOA is smaller only when the optimizer $\theta$ is found, while $\mathrm { A Q C } ( \exp ) \lesssim \mathrm { A Q C } ( p )$ holds only when $\epsilon$ is sufficiently small. While the runtime complexity of AQC(exp) readily provides an upper bound of the runtime complexity of QAOA, numerical results indicate that the optimizer of QAOA often involves a much smaller depth, and hence the dynamics of QAOA does not necessarily follow the adiabatic path. Therefore, it is of interest to find alternative routes to directly prove the scaling of the QAOA runtime without relying on AQC. In the work [20], our AQC based algorithm has been combined with the eigenvector filtering technique. Ref. [20] also proposed another AQC inspired quantum linear system solver, which is based on the quantum Zeno effect. Both methods can scale linearly in $\kappa$ and logarithmically in $1 / \epsilon$ . We expect our AQC based QLSP solvers may serve as useful subroutines in other quantum algorithms as well.

# ACKNOWLEDGMENTS

This work was partially supported by the Department of Energy under Grant No. DE-SC0017867, the Quantum Algorithm Teams Program under Grant No. DE-AC02-05CH11231 (L.L.), by a Google Quantum Research Award, and by the NSF Quantum Leap Challenge Institute (QLCI) program through grant number OMA-2016245 (D. A. and L.L.). We thank Rolando Somma, Yu Tong and Nathan Wiebe for helpful discussions.

# REFERENCES

[1] Tameem Albash and Daniel A. Lidar. 2018. Adiabatic quantum computation. Rev. Mod. Phys. 90 (2018), 015002.   
[2] Andris Ambainis. 2012. Variable time amplitude amplification and quantum algorithms for linear algebra problems. In STACS’12 (29th Symposium on Theoretical Aspects of Computer Science), Vol. 14. LIPIcs, Paris, France, 636–647.   
[3] Seraph Bao, Silken Kleer, Ruoyu Wang, and Armin Rahmani. 2018. Optimal control of superconducting gmon qubits using Pontryagin’s minimum principle: Preparing a maximally entangled state with singular bang-bang protocols. Phys. Rev. A 97 (2018), 062343.   
[4] Dominic W. Berry, Andrew M. Childs, Richard Cleve, Robin Kothari, and Rolando D. Somma. 2015. Simulating Hamiltonian dynamics with a truncated Taylor series. Phys. Rev. Lett. 114 (2015), 090502.   
[5] Dominic W. Berry, Andrew M. Childs, and Robin Kothari. 2015. Hamiltonian Simulation with Nearly Optimal Dependence on all Parameters. In 2015 IEEE 56th Annual Symposium on Foundations of Computer Science. IEEE, Piscataway, NJ, USA, 792–809.   
[6] Sergio Boixo, Emanuel Knill, and Rolando D Somma. 2009. Eigenpath traversal by phase randomization. Quantum Info. Comput. 9 (2009), 833–855.   
[7] Sergio Boixo and Rolando D. Somma. 2010. Necessary condition for the quantum adiabatic approximation. Phys. Rev. A 81 (2010), 032308.   
[8] Carlos Bravo-Prieto, Ryan LaRose, M. Cerezo, Yigit Subasi, Lukasz Cincio, and Patrick J. Coles. 2020. Variational Quantum Linear Solver. arXiv:1909.05820   
[9] Marin Bukov, Alexandre G. R. Day, Dries Sels, Phillip Weinberg, Anatoli Polkovnikov, and Pankaj Mehta. 2018. Reinforcement Learning in Different Phases of Quantum Control. Phys. Rev. X 8, 3 (2018), 031086.   
[10] Yudong Cao, Anargyros Papageorgiou, Iasonas Petras, Joseph Traub, and Sabre Kais. 2013. Quantum algorithm and circuit design solving the Poisson equation. New J. Phys. 15, 1 (2013), 013021.   
[11] Shantanav Chakraborty, András Gilyén, and Stacey Jeffery. 2019. The Power of Block-Encoded Matrix Powers: Improved Regression Techniques via Faster Hamiltonian Simulation. In 46th International Colloquium on Automata, Languages, and Programming (ICALP 2019) (Leibniz International Proceedings in Informatics (LIPIcs), Vol. 132). Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik, Dagstuhl, Germany, 33:1–33:14.   
[12] Andrew M. Childs, Robin Kothari, and Rolando D. Somma. 2017. Quantum Algorithm for Systems of Linear Equations with Exponentially Improved Dependence on Precision. SIAM J. Comput. 46 (2017), 1920–1950.   
[13] Andrew M. Childs, Yuan Su, Minh C. Tran, Nathan Wiebe, and Shuchen Zhu. 2021. Theory of Trotter Error with Commutator Scaling. Physical Review X 11, 1 (2021), 011020.   
[14] Edward Farhi, Jeffrey Goldstone, and Sam Gutmann. 2014. A Quantum Approximate Optimization Algorithm. arXiv:1411.4028   
[15] Yimin Ge, András Molnár, and J. Ignacio Cirac. 2016. Rapid Adiabatic Preparation of Injective Projected Entangled Pair States and Gibbs States. Phys. Rev. Lett. 116 (2016), 080503.   
[16] András Gilyén, Yuan Su, Guang Hao Low, and Nathan Wiebe. 2019. Quantum Singular Value Transformation and beyond: Exponential Improvements for Quantum Matrix Arithmetics. In Proceedings of the 51st Annual ACM SIGACT Symposium on Theory of Computing (STOC 2019). Association for Computing Machinery, New York, NY, USA, 193–204.   
[17] Aram W. Harrow, Avinatan Hassidim, and Seth Lloyd. 2009. Quantum algorithm for linear systems of equations. Phys. Rev. Lett. 103 (2009), 150502.   
[18] Itay Hen. 2019. How quantum is the speedup in adiabatic unstructured search? Quant. Inf. Proc. 18, 6 (2019), 162.   
[19] Sabine Jansen, Mary-Beth Ruskai, and Ruedi Seiler. 2007. Bounds for the adiabatic approximation with applications to quantum computation. J. Math. Phys. 48, 10 (2007), 102111.   
[20] Lin Lin and Yu Tong. 2020. Optimal polynomial based quantum eigenstate filtering with application to solving quantum linear systems. Quantum 4 (2020), 361.   
[21] Joseph W. H. Liu. 1992. The multifrontal method for sparse matrix solution: Theory and practice. SIAM Rev. 34 (1992), 82–109.   
[22] Guang Hao Low and Isaac L. Chuang. 2017. Optimal Hamiltonian Simulation by Quantum Signal Processing. Phys. Rev. Lett. 118 (2017), 010501.   
[23] Guang Hao Low and Nathan Wiebe. 2019. Hamiltonian Simulation in the Interaction Picture. arXiv:1805.00675   
[24] Yvon Maday and Gabriel Turinici. 2003. New formulations of monotonically convergent quantum control algorithms. J. Chem. Phys. 118, 18 (2003), 8191–8196.   
[25] Gheorghe Nenciu. 1993. Linear adiabatic theory. Exponential estimates. Comm. Math. Phys. 152 (1993), 479–496.   
[26] Murphy Yuezhen Niu, Sergio Boixo, Vadim N. Smelyanskiy, and Hartmut Neven. 2019. Universal quantum control through deep reinforcement learning. npj Quantum Info. 5 (2019), 33.   
[27] Ali T. Rezakhani, W.-J. Kuo, Alioscia Hamma, Daniel A. Lidar, and Paolo Zanardi. 2009. Quantum Adiabatic Brachistochrone. Phys. Rev. Lett. 103 (2009), 080502.   
[28] Jérémie Roland and Nicolas J. Cerf. 2002. Quantum search by local adiabatic evolution. Phys. Rev. A 65, 4 (2002), 042308.   
[29] Yousef Saad. 2003. Iterative methods for sparse linear systems. Vol. 82. SIAM, Philadelphia, PA, USA.   
[30] Yiğit Subaşı, Rolando D. Somma, and Davide Orsucci. 2019. Quantum Algorithms for Systems of Linear Equations Inspired by Adiabatic Quantum Computing. Phys. Rev. Lett. 122 (2019), 060504.   
[31] Wim van Dam, Michele Mosca, and Umesh Vazirani. 2001. How powerful is adiabatic quantum computation?. In Proceedings 42nd IEEE Symposium on Foundations of Computer Science. IEEE, Piscataway, NJ, USA, 279–287.   
[32] Nathan Wiebe and Nathan S. Babcock. 2012. Improved error-scaling for adiabatic quantum evolutions. New J. Phys. 14 (2012), 1–10.   
[33] Leonard Wossnig, Zhikuan Zhao, and Anupam Prakash. 2018. Quantum Linear System Algorithm for Dense Matrices. Phys. Rev. Lett. 120, 5 (2018), 050502.   
[34] Xiaosi Xu, Jinzhao Sun, Suguru Endo, Ying Li, Simon C. Benjamin, and Xiao Yuan. 2021. Variational algorithms for linear algebra. Science Bulletin in press (2021).   
[35] Zhi-Cheng Yang, Armin Rahmani, Alireza Shabani, Hartmut Neven, and Claudio Chamon. 2017. Optimizing Variational Quantum Algorithms Using Pontryagin’s Minimum Principle. Phys. Rev. X 7 (2017), 021027.   
[36] Wusheng Zhu and Herschel Rabitz. 1998. A rapid monotonically convergent iteration algorithm for quantum optimal control over the expectation value of a positive definite operator. J. Chem. Phys. 109, 2 (1998), 385–391.

# A THE GAP OF $H ( f ( s ) )$ FOR HERMITIAN POSITIVE DEFINITE MATRICES

The Hamiltonian $H ( f )$ can be written in the block matrix form as

$$
H ( f ) = \left( \begin{array} { c c } { { 0 } } & { { ( ( 1 - f ) I + f A ) Q _ { b } } } \\ { { Q _ { b } ( ( 1 - f ) I + f A ) } } & { { 0 } } \end{array} \right) .
$$

Let $\lambda$ be an eigenvalue of $H$ , then

$$
\begin{array} { c } { { 0 = \operatorname * { d e t } \left( \begin{array} { c c } { { \lambda I } } & { { - ( ( 1 - f ) I + f A ) Q _ { b } } } \\ { { - Q _ { b } ( ( 1 - f ) I + f A ) } } & { { \lambda I } } \end{array} \right) } } \\ { { = \operatorname * { d e t } \left( \lambda ^ { 2 } I - ( ( 1 - f ) I + f A ) Q _ { b } ^ { 2 } ( ( 1 - f ) I + f A ) \right) } } \end{array}
$$

where the second equality holds because the bottom two blocks are commutable. Thus $\lambda ^ { 2 }$ is an eigenvalue of $( ( 1 - f ) I + f A ) Q _ { b } ^ { 2 } ( ( 1 - f ) I + f A )$ , and $\Delta ^ { 2 } ( f )$ equals the smallest non-zero eigenvalue of

$( ( 1 - f ) I + f A ) Q _ { b } ^ { 2 } ( ( 1 - f ) I + f A )$ . Applying a proposition of matrices that $X Y$ and $Y X$ have the same non-zero eigenvalues, $\Delta ^ { 2 } ( f )$ also equals the smallest non-zero eigenvalue of $Q _ { b } ( ( 1 - f ) I + f A ) ^ { 2 } Q _ { b }$ .

Now we focus on the matrix $Q _ { b } ( ( 1 - f ) I + f A ) ^ { 2 } Q _ { b }$ . Note that $| b \rangle$ is the unique eigenstate corresponding to the eigenvalue 0, and all eigenstates corresponding to non-zero eigenvalues must be orthogonal to $| b \rangle$ . Therefore

$$
\begin{array} { r l } & { \Delta ^ { 2 } ( f ) = \underset { \left. b \mid \varphi \right. = 0 , \left. \varphi \mid \varphi \right. = 1 } { \mathrm { i n f } } \left. \varphi \left. Q _ { b } ( ( 1 - f ) I + f A ) ^ { 2 } Q _ { b } \right. \varphi \right. } \\ & { \quad \quad = \underset { \left. b \mid \varphi \right. = 0 , \left. \varphi \mid \varphi \right. = 1 } { \mathrm { i n f } } \left. \varphi \left. ( ( 1 - f ) I + f A ) ^ { 2 } \right. \varphi \right. } \\ & { \quad \quad \geq \underset { \left. \varphi \mid \varphi \right. = 1 } { \mathrm { i n f } } \left. \varphi \left. ( ( 1 - f ) I + f A ) ^ { 2 } \right. \varphi \right. } \\ & { \quad \quad = ( 1 - f + f / \kappa ) ^ { 2 } , } \end{array}
$$

and $\Delta ( f ) \ge \Delta _ { * } ( f ) = 1 - f + f / \kappa$ .

# B RELATIONS AMONG DIFFERENT MEASUREMENTS OF ACCURACY

We show two relations that connect the error of density matrix distance and the error of fidelity, which are used in our proof for $\mathsf { A Q C } ( \mathsf { p } )$ and $\mathsf { A Q C } ( \exp )$ . Following the notations in the main text, let $| \widetilde { x } ( s ) \rangle$ denote the desired eigenpath of $H ( f ( s ) )$ corresponding to the 0 eigenvalue, and $\mathrm { N u l l } ( H ( f ( s ) ) ) = \{ | \widetilde { x } ( s ) \rangle , | \bar { b } \rangle \} . P _ { 0 } ( s$ denotes the projector onto the eigenspace corresponding to the 0 eigenvalue.

Lemma 5. (i) The following equation holds,

$$
\begin{array} { r } { | 1 - \langle \psi _ { T } ( s ) | P _ { 0 } ( s ) | \psi _ { T } ( s ) \rangle | = 1 - | \langle \psi _ { T } ( s ) | \widetilde { x } ( s ) \rangle | ^ { 2 } = \| | \psi _ { T } ( s ) \rangle \langle \psi _ { T } ( s ) | - | \widetilde { x } ( s ) \rangle \langle \widetilde { x } ( s ) | \| _ { 2 } ^ { 2 } . } \end{array}
$$

(ii) Assume that

$$
| 1 - \langle \psi _ { T } ( s ) | P _ { 0 } ( s ) | \psi _ { T } ( s ) \rangle | \leq \eta ^ { 2 } ( s ) .
$$

Then the fidelity can be bounded from below $b y 1 - \eta ^ { 2 } ( s )$ , and the 2-norm error of the density matrix can be bounded from above $b y \eta ( s )$ .

Proof. It suffices only to prove part (i). Note that $\mathinner { | { \bar { b } } \rangle }$ is the eigenstate for both $H _ { 0 }$ and $H _ { 1 }$ corresponding the 0 eigenvalue, we have $H ( f ( s ) ) \left| \bar { b } \right. = ( ( 1 - f ( s ) ) \bar { H } _ { 0 } + f ( s ) H _ { 1 } ) \left| \bar { b } \right. = 0$ , and thus $\begin{array} { r } { \frac { d } { d s } \langle \bar { b } | \bar { \psi } _ { T } ( s ) \rangle = 0 } \end{array}$ . Together with the initial condition $\langle \bar { b } | \psi _ { T } ( 0 ) \rangle = 0$ , the overlap of $| \bar { b } \rangle$ and $| \psi _ { T } ( s ) \rangle$ remains to be 0 for the whole time period, i.e. $\langle \bar { b } | \psi _ { T } ( s ) \rangle = 0$ . Since $P _ { 0 } ( s ) = | \widetilde { x } ( s ) \rangle \langle \widetilde { x } ( s ) | + | \bar { b } \rangle \langle \bar { b } |$ , we have $P _ { 0 } ( s ) \left| \psi _ { T } ( s ) \right. = | \widetilde { x } ( s ) \rangle \langle \widetilde { x } ( s ) | \psi _ { T } ( s ) ) \rangle$ . Therefore

$$
\begin{array} { r } { | 1 - \left. \psi _ { T } ( s ) | P _ { 0 } ( s ) | \psi _ { T } ( s ) \right. | = | 1 - \left. \psi _ { T } ( s ) | \widetilde { x } ( s ) \right. \left. \widetilde { x } ( s ) | \psi _ { T } ( s ) \right. | = 1 - | \left. \psi _ { T } ( s ) | \widetilde { x } ( s ) \right. | ^ { 2 } . } \end{array}
$$

To prove the second equation, let ${ \cal M } \ = \ | \psi _ { T } ( s ) \rangle \langle \psi _ { T } ( s ) | - | \widetilde { x } ( s ) \rangle \langle \widetilde { x } ( s ) |$ . Note that $\| M \| _ { 2 } ^ { 2 } ~ =$ $\lambda _ { \operatorname* { m a x } } ( M ^ { \dagger } M )$ , we study the eigenvalues of $M ^ { \dagger } M$ by first computing that

$M ^ { \dagger } M = | \psi _ { T } ( s )   \psi _ { T } ( s ) | + | { \widetilde { x } } ( s )   { \widetilde { x } } ( s ) | -  \psi _ { T } ( s ) | { \widetilde { x } } ( s )  | \psi _ { T } ( s )   { \widetilde { x } } ( s ) | -  { \widetilde { x } } ( s ) | \psi _ { T } ( s )  | { \widetilde { x } } ( s )   \psi _ { T } ( s )  .$ ⟨𝜓𝑇 (𝑠) | . Since for any $| y \rangle \in \mathrm { s p a n } \{ | \psi _ { T } ( s ) \rangle , | \widetilde { x } ( s ) \rangle \} ^ { \bot } , M ^ { \dagger } M | y \rangle = 0$ , and

$$
\begin{array} { r l r } & { } & { M ^ { \dagger } M \left| \psi _ { T } ( s ) \right. = \left( 1 - \left| \langle \psi _ { T } ( s ) \vert \widetilde { x } ( s ) \rangle \right| ^ { 2 } \right) \left| \psi _ { T } ( s ) \right. , } \\ & { } & { M ^ { \dagger } M \left| \widetilde { x } ( s ) \right. = \left( 1 - \left| \langle \psi _ { T } ( s ) \vert \widetilde { x } ( s ) \rangle \right| ^ { 2 } \right) \left| \widetilde { x } ( s ) \right. , } \end{array}
$$

we have $\| M \| _ { 2 } ^ { 2 } = \lambda _ { \operatorname* { m a x } } ( M ^ { \dagger } M ) = 1 - | \langle \psi _ { T } ( s ) | \widetilde x ( s ) \rangle | ^ { 2 } .$

# C DIFFERENCE BETWEEN THE SCALINGS OF AQC(P) AND RM WITH RESPECT TOINFIDELITY

In our numerical test, we observe that to reach a desired fidelity, RM encounters a much larger pre-constant than AQC(p). This is due to the following reason. Although the runtime of both RM and AQC(p) scales as $O ( 1 / \epsilon )$ where $\epsilon$ is the 2-norm error of the density matrix, the scalings with respect to the infidelity are different. More specifically, Lemma 5 shows that for AQC, the square of the 2-norm error is exactly equal to the infidelity. Thus in order to reach infidelity √ $1 - F$ using $\mathsf { A Q C } ( \mathsf { p } )$ , it suffices to choose the runtime to be $T = O ( \kappa / { \sqrt { 1 - F } } )$ . Meanwhile, it has been proved in [6] that the runtime complexity of RM is $\widetilde { O } ( \kappa / ( 1 - F ) )$ . Therefore, to reach a desired fidelity, the runtime of $\mathsf { A Q C } ( \mathsf { p } )$ will be smaller than that of RM, as shown in our numerical examples.

We further verify the statement above by studying the relation between the 2-norm error of the density matrix and the infidelity for $\mathsf { A Q C } ( \mathsf { p } )$ , AQC(exp) and RM using the positive definite example with $\kappa = 1 0$ . In $\mathsf { A Q C } ( \mathsf { p } )$ and AQC(exp), we change the runtime to obtain approximations with different errors and infidelity. In RM we vary the number of exponential operators to obtain different levels of accuracy. All other numerical treatments remain unchanged. As shown in Figure 3, the infidelity is exactly the square of 2-norm error in the case of AQC(p) and AQC(exp), while the infidelity of RM only scales approximately linearly with respect to 2-norm error. This also verifies that although the runtime of both AQC(p) and RM scales linearly with respect to $\epsilon$ , the runtime of $\mathsf { A Q C } ( \mathsf { p } )$ can be much smaller to reach desired fidelity.

![](images/d921c71a9b1a45d068d132469d34b125741df7af47b02a405d562d25974aa2e0.jpg)  
Fig. 3. Relation between 2-norm error and infidelity of AQC and RM.

# D PROOF OF THEOREM 1 AND THEOREM 3

The proof of Theorem 1 and Theorem 3 rests on some delicate cancellation of the time derivatives $\| H ^ { ( 1 ) } \| _ { 2 } , \| H ^ { ( 2 ) } \| _ { 2 }$ and the gap $\Delta ( f ( s ) )$ in the error bound, and can be completed by carefully analyzing the $\kappa$ -dependence of each term in $\eta ( s )$ given in Eq. (4). Note that in both cases √ $H ( f ) =$ $( 1 - f ) H _ { 0 } + f H _ { 1 }$ , and we let $\Delta _ { * } ( f ) = ( 1 - f + f / \kappa ) / \sqrt { 2 }$ since such a choice of $\Delta _ { * }$ can serve as a lower bound of the spectrum gap for both the case of Theorem 1 and Theorem 3. We first compute

the derivatives of $H ( f ( s ) )$ by chain rule as

$$
H ^ { ( 1 ) } ( s ) = { \frac { d } { d s } } H ( f ( s ) ) = { \frac { d H ( f ( s ) ) } { d f } } { \frac { d f ( s ) } { d s } } = ( H _ { 1 } - H _ { 0 } ) c _ { p } \Delta _ { * } ^ { p } ( f ( s ) ) ,
$$

and

$$
\begin{array} { l } { { \displaystyle { H ^ { ( 2 ) } ( s ) = \frac { d } { d s } H ^ { ( 1 ) } ( s ) = \frac { d } { d s } \left( ( H _ { 1 } - H _ { 0 } ) c _ { p } \Delta _ { * } ^ { p } ( f ( s ) ) \right) } } } \\ { { \displaystyle { \quad = ( H _ { 1 } - H _ { 0 } ) c _ { p } p \Delta _ { * } ^ { p - 1 } ( f ( s ) ) \frac { d \Delta _ { * } ( f ( s ) ) } { d f } \frac { d f ( s ) } { d s } } } } \\ { { \displaystyle { \quad = \frac { 1 } { \sqrt { 2 } } ( - 1 + 1 / \kappa ) ( H _ { 1 } - H _ { 0 } ) c _ { p } ^ { 2 } p \Delta _ { * } ^ { 2 p - 1 } ( f ( s ) ) . } } } \end{array}
$$

Then the first two terms of $\eta ( s )$ can be rewritten as

$$
\begin{array} { l } { \displaystyle \frac { \| H ^ { ( 1 ) } ( 0 ) \| _ { 2 } } { T \Delta ^ { 2 } ( 0 ) } + \frac { \| H ^ { ( 1 ) } ( s ) \| _ { 2 } } { T \Delta ^ { 2 } ( f ( s ) ) } \le \frac { \| H ^ { ( 1 ) } ( 0 ) \| _ { 2 } } { T \Delta _ { * } ^ { 2 } ( 0 ) } + \frac { \| H ^ { ( 1 ) } ( s ) \| _ { 2 } } { T \Delta _ { * } ^ { 2 } ( f ( s ) ) } } \\ { \displaystyle = \frac { \| ( H _ { 1 } - H _ { 0 } ) c _ { p } \Delta _ { * } ^ { p } ( f ( 0 ) ) \| _ { 2 } } { T \Delta _ { * } ^ { 2 } ( 0 ) } + \frac { \| ( H _ { 1 } - H _ { 0 } ) c _ { p } \Delta _ { * } ^ { p } ( f ( s ) ) \| _ { 2 } } { T \Delta _ { * } ^ { 2 } ( f ( s ) ) } } \\ { \displaystyle \le \frac { C } { T } \left( c _ { p } \Delta _ { * } ^ { p - 2 } ( 0 ) + c _ { p } \Delta _ { * } ^ { p - 2 } ( f ( s ) ) \right) } \\ { \displaystyle \le \frac { C } { T } \left( c _ { p } \Delta _ { * } ^ { p - 2 } ( 0 ) + c _ { p } \Delta _ { * } ^ { p - 2 } ( 1 ) \right) } \end{array}
$$

Here $C$ stands for a general positive constant independent of $s , \Delta , T .$ . To compute the remaining two terms of $\eta ( s )$ , we use the following change of variable

$$
u = f ( s ^ { \prime } ) , \quad d u = \frac { d } { d s ^ { \prime } } f ( s ^ { \prime } ) d s ^ { \prime } = c _ { \hat { p } } \Delta _ { * } ^ { p } ( f ( s ^ { \prime } ) ) d s ^ { \prime } ,
$$

and the last two terms of $\eta ( s )$ become

$$
\begin{array} { r l } & { \frac { 1 } { T } \int _ { 0 } ^ { \infty } \frac { | H | ^ { ( 2 ) } \| _ { 2 } } { \Lambda ^ { 2 } } d s ^ { \prime } \le \frac { 1 } { T } \int _ { 0 } ^ { \infty } \frac { | H | ^ { ( 2 ) } \| _ { 2 } } { \Lambda _ { s } ^ { 2 } } d s ^ { \prime } } \\ & { = \frac { 1 } { T } \int _ { 0 } ^ { s } \frac { \| \frac { 1 } { \gamma \tilde { \varepsilon } } ( - 1 + 1 / \kappa ) ( H _ { 1 } - T  { \mathbb { I } _ { 0 } } ) c _ { p } ^ { 2 } \Lambda _ { s } ^ { 2 } e ^ { - 1 } ( f ( s ^ { \prime } ) ) \| _ { 2 } } { \Delta _ { s } ^ { 2 } ( f ( s ^ { \prime } ) ) } d s ^ { \prime } } \\ & { = \frac { 1 } { T } \int _ { 0 } ^ { f ( s ) } \frac { \| \frac { 1 } { \gamma \tilde { \varepsilon } } ( - 1 + 1 / \kappa ) ( H _ { 1 } - H ) c _ { p } ^ { 2 }  { \mathbb { I } _ { \partial s } } ^ { \tilde { \varepsilon } ^ { \varepsilon } \setminus 1 } ( u ) \| _ { 2 } } { \Delta _ { s } ^ { 2 } ( u ) } \frac { d u } { c _ { p } \Delta _ { s } ^ { 2 } ( u ) } } \\ & { \le \frac { C } { T } \left( ( 1 - 1 / \kappa ) c _ { p } \int _ { 0 } ^ { f ( s ) } \delta _ { s } ^ { 2 - 3 } ( u ) d u \right) } \\ & { \le \frac { C } { T } \left( ( 1 - 1 / \kappa ) c _ { p } \int _ { 0 } ^ { 1 } \Lambda _ { s } ^ { p - 3 } ( u ) d u \right) , } \end{array}
$$

ACM Trans. Quantum Comput., Vol. 3, No. 2, Article 5. Publication date: February 2022.

and similarly

$$
\begin{array} { r l } & { \frac { 1 } { T } \int _ { 0 } ^ { s } \frac { \| H ^ { ( 1 ) } \| _ { 2 } ^ { 2 } d s ^ { \prime } } { \Lambda ^ { 3 } } \le \frac { 1 } { T } \int _ { 0 } ^ { s } \frac { \| H ^ { ( 1 ) } \| _ { 2 } ^ { 2 } } { \Lambda ^ { 3 } } d s ^ { \prime } } \\ & { = \frac { 1 } { T } \int _ { 0 } ^ { s } \frac { \| \left( H _ { 1 } - H _ { 0 } \right) c _ { p } \Lambda ^ { p } ( f ( s ^ { \prime } ) ) \| _ { 2 } ^ { 2 } } { \Lambda ^ { 3 } ( f ( s ^ { \prime } ) ) } d s ^ { \prime } } \\ & { = \frac { 1 } { T } \int _ { 0 } ^ { f ( s ) } \frac { \| \left( H _ { 1 } - H _ { 0 } \right) c _ { p } \Lambda ^ { p } ( u ) \| _ { 2 } ^ { 2 } } { \Lambda _ { * } ^ { 3 } ( u ) } \frac { d u } { c _ { p } \Delta _ { * } ^ { p } ( u ) } } \\ & { \le \frac { C } { T } \left( c _ { p } \int _ { 0 } ^ { f ( s ) } \Delta _ { * } ^ { p - s } ( u ) d u \right) } \\ & { \le \frac { C } { T } \left( c _ { p } \int _ { 0 } ^ { 1 } \Delta _ { * } ^ { p - s } ( u ) d u \right) . } \end{array}
$$

Summarize all terms above, an upper bound of $\eta ( s )$ is

$$
\begin{array} { c } { { \eta ( s ) \leq \displaystyle \frac { C } { T } \bigg \{ \Big ( c _ { p } \Delta _ { * } ^ { p - 2 } ( 0 ) + c _ { p } \Delta _ { * } ^ { p - 2 } ( 1 ) \Big ) + \left( ( 1 - 1 / \kappa ) c _ { p } \int _ { 0 } ^ { 1 } \Delta _ { * } ^ { p - 3 } ( u ) d u \right) + \left( c _ { p } \int _ { 0 } ^ { 1 } \Delta _ { * } ^ { p - 3 } ( u ) d u \right) } } \\ { { = \displaystyle \frac { C } { T } \Big \{ 2 ^ { - ( p - 2 ) / 2 } \left( c _ { p } + c _ { p } \kappa ^ { 2 - p } \right) + \left( ( 1 - 1 / \kappa ) c _ { p } \int _ { 0 } ^ { 1 } \Delta _ { * } ^ { p - 3 } ( u ) d u \right) + \left( c _ { p } \int _ { 0 } ^ { 1 } \Delta _ { * } ^ { p - 3 } ( u ) d u \right) \Big \} . } } \end{array}
$$

Finally, since for $1 < p < 2$

$$
c _ { \hat { p } } = \int _ { 0 } ^ { 1 } \Delta _ { * } ^ { - \hat { p } } ( u ) d u = \frac { 2 ^ { { p } / { 2 } } } { \hat { p } - 1 } \frac { \kappa } { \kappa - 1 } ( \kappa ^ { \hat { p } - 1 } - 1 ) ,
$$

and

$$
\int _ { 0 } ^ { 1 } \Delta _ { * } ^ { p - 3 } ( u ) d u = \frac { 2 ^ { - ( p - 3 ) / 2 } } { 2 - p } \frac { \kappa } { \kappa - 1 } ( \kappa ^ { 2 - p } - 1 ) ,
$$

we have

$$
\begin{array} { r l } & { \eta ( s ) \le \displaystyle \frac { C } { T } \biggl \{ \displaystyle \frac { \kappa } { \kappa - 1 } \bigl ( \kappa ^ { p - 1 } - 1 \bigr ) + \frac { \kappa } { \kappa - 1 } \bigl ( \kappa - \kappa ^ { 2 - p } \bigr ) } \\ & { \qquad + \displaystyle \frac { \kappa } { \kappa - 1 } \bigl ( \kappa ^ { p - 1 } - 1 \bigr ) \bigl ( \kappa ^ { 2 - p } - 1 \bigr ) + \Bigl ( \frac { \kappa } { \kappa - 1 } \Bigr ) ^ { 2 } \bigl ( \kappa ^ { p - 1 } - 1 \bigr ) \bigl ( \kappa ^ { 2 - p } - 1 \bigr ) \biggr \} . } \end{array}
$$

The leading term of the bound is $O ( \kappa / T )$ when $1 < p < 2$

Now we consider the limiting case when $\hbar = 1 , 2$ . Note that the bound for $\eta ( s )$ can still be written as

$$
\begin{array} { l } { \eta ( s ) \leq \displaystyle \frac { C } { T } \Big \{ \Big ( c _ { \rho } \Delta _ { * } ^ { \rho - 2 } ( 0 ) + c _ { \rho } \Delta _ { * } ^ { \rho - 2 } ( 1 ) \Big ) + \left( ( 1 - 1 / \kappa ) c _ { \rho } \int _ { 0 } ^ { 1 } \Delta _ { * } ^ { \rho - 3 } ( u ) d u \right) + \left( c _ { P } \int _ { 0 } ^ { 1 } \Delta _ { * } ^ { \rho - 3 } ( u ) d u \right) } \\ { \displaystyle = \displaystyle \frac { C } { T } \Big \{ 2 ^ { - ( p - 2 ) / 2 } \left( c _ { p } + c _ { p } \kappa ^ { 2 - p } \right) + ( 1 - 1 / \kappa ) c _ { p } c _ { 3 - p } + c _ { p } c _ { 3 - p } \Big \} . } \end{array}
$$

Straightforward computation shows that

$$
c _ { 1 } = \int _ { 0 } ^ { 1 } \Delta _ { * } ^ { - 1 } ( u ) d u = \sqrt { 2 } \frac { \kappa } { \kappa - 1 } \log ( \kappa )
$$

and

$$
c _ { 2 } = \int _ { 0 } ^ { 1 } \Delta _ { * } ^ { - 2 } ( u ) d u = 2 \frac { \kappa } { \kappa - 1 } ( \kappa - 1 ) .
$$

ACM Trans. Quantum Comput., Vol. 3, No. 2, Article 5. Publication date: February 2022.

Hence when $\hbar = 1 , 2$ ,

$$
\eta ( s ) \leq \frac { C } { T } \Bigl \{ 2 ^ { - ( p - 2 ) / 2 } \left( c _ { \hat { p } } + c _ { \hat { p } } \kappa ^ { 2 - \hat { p } } \right) + \left( 1 - 1 / \kappa \right) c _ { 1 } c _ { 2 } + c _ { 1 } c _ { 2 } \Bigr \} \leq C \frac { \kappa \log ( \kappa ) } { T } .
$$

This completes the proof of Theorem 1 and Theorem 3.

# E PROOF OF THEOREM 2 AND THEOREM 4

We provide a rigorous proof of the error bound for the $\mathsf { A Q C } ( \exp )$ scheme. We mainly follow the methodology of [25] and a part of technical treatments of [15]. Our main contribution is carefully revealing an explicit constant dependence in the adiabatic theorem, which is the key to obtain the $\widetilde { O } ( \kappa )$ scaling. In the $\mathsf { A Q C } ( \exp ( \exp ( $ scheme, the Hamiltonian $H ( s ) = ( 1 - f ( s ) ) H _ { 0 } + f ( s ) H _ { 1 }$ with $\| H _ { 0 } \| , \| H _ { 1 } \| \leq 1$ and

$$
f ( s ) = \frac { 1 } { c _ { e } } \int _ { 0 } ^ { s } \exp \left( - \frac { 1 } { s ^ { \prime } ( 1 - s ^ { \prime } ) } \right) \mathrm { d } s ^ { \prime } .
$$

The normalization constant $\begin{array} { r } { c _ { e } = \int _ { 0 } ^ { 1 } \exp ( - \frac { 1 } { t ( 1 - t ) } ) d t \approx 0 . 0 0 7 0 . } \end{array}$ . Let $U _ { T } ( s )$ denote the corresponding unitary evolution operator, and $P _ { 0 } ( s )$ denote the projector onto the eigenspace corresponding to 0. We use $\Delta _ { * } ( f ) = ( 1 - f + f / \kappa ) / \sqrt { 2 }$ since this can serve as a lower bound of the spectrum gap for both the cases of Theorem 2 and Theorem 4.

We first restate the theorems universally with more technical details as following.

Theorem 6. Assume the condition number $\kappa ~ > ~ e$ . Then the final time adiabatic error $| 1 -$ $\langle \psi _ { T } ( 1 ) | P _ { 0 } ( 1 ) | \psi _ { T } ( 1 ) \rangle \mid$ of $\cdot { \cal A } Q C ( e x p )$ can be bounded $b y \eta _ { 1 } ^ { 2 }$ where (a) for arbitrary $N$ ,

$$
\eta _ { 1 } ^ { 2 } = A _ { 1 } D \log ^ { 2 } \kappa \left( C _ { 2 } \frac { \kappa \log ^ { 2 } \kappa } { T } N ^ { 4 } \right) ^ { N }
$$

where $A _ { 1 } , D$ , and $C _ { 2 }$ are positive constants which are independent of $T , \kappa$ and $N$ , $( b )$ if 𝑇 is large enough such that

$$
1 6 e A _ { 1 } ^ { - 1 } D \left( \frac { 4 \pi ^ { 2 } } { 3 } \right) ^ { 3 } \frac { \kappa \log ^ { 2 } \kappa } { T } \leq 1 ,
$$

then

$$
\eta _ { 1 } ^ { 2 } = C _ { 1 } \log ^ { 2 } \kappa \exp \left( - \left( C _ { 2 } \frac { \kappa \log ^ { 2 } \kappa } { T } \right) ^ { - \frac { 1 } { 4 } } \right)
$$

where $A _ { 1 } , D , C _ { 1 }$ , and $C _ { 2 }$ are positive constants which are independent of $T$ and $\kappa$ .

Corollary 7. For any $\kappa > e , 0 < \epsilon < 1$ , to prepare an $\epsilon$ -approximation of the solution of QLSP using $A Q C ( e x p ) ;$ , it is sufficient to choose the runtime $T = O \left( \kappa \log ^ { 2 } \kappa \log ^ { 4 } \left( \frac { \log \kappa } { \epsilon } \right) \right)$ .

Proof. We start the proof by considering the projector $P ( s )$ onto an invariant space of $H$ , then $P ( s )$ satisfies

$$
\mathrm { i } \frac { 1 } { T } \partial _ { s } P ( s ) = [ H ( s ) , P ( s ) ] , \quad P ^ { 2 } ( s ) = P ( s ) .
$$

We try the ansatz (only formally)

$$
P ( s ) = \sum _ { j = 0 } ^ { \infty } E _ { j } ( s ) T ^ { - j } .
$$

ACM Trans. Quantum Comput., Vol. 3, No. 2, Article 5. Publication date: February 2022.

Substitute it into the Heisenberg equation and match terms with the same orders, we get

$$
[ H ( s ) , E _ { 0 } ( s ) ] = 0 , \quad \mathrm { i } \partial _ { s } E _ { j } ( s ) = [ H ( s ) , E _ { j + 1 } ( s ) ] , \quad E _ { j } ( s ) = \sum _ { m = 0 } ^ { j } E _ { m } ( s ) E _ { j - m } ( s ) .
$$

It has been proved in [25] that the solution of (20) with initial condition $E _ { 0 } = P _ { 0 }$ is given by

$$
\begin{array} { l } { { E _ { 0 } ( s ) = P _ { 0 } ( s ) = - ( 2 \pi \mathbf { i } ) ^ { - 1 } \displaystyle \oint _ { \Gamma ( s ) } ( H ( s ) - z ) ^ { - 1 } d z , } } \\ { { \displaystyle E _ { j } ( s ) = ( 2 \pi ) ^ { - 1 } \displaystyle \oint _ { \Gamma ( s ) } ( H ( s ) - z ) ^ { - 1 } [ E _ { j - 1 } ^ { ( 1 ) } ( s ) , P _ { 0 } ( s ) ] ( H ( s ) - z ) ^ { - 1 } d z + S _ { j } ( s ) - 2 P _ { 0 } ( s ) S _ { j } ( s ) P _ { 0 } ( s ) } } \end{array}
$$

where $\Gamma ( s ) = \{ z \in \mathbb { C } : | z | = \Delta ( s ) / 2 \}$ and

$$
S _ { j } ( s ) = \sum _ { m = 1 } ^ { j - 1 } E _ { m } ( s ) E _ { j - m } ( s ) .
$$

Furthermore given $E _ { 0 } = P _ { 0 }$ , such a solution is unique.

In general, Eq. (19) does not converge, so for arbitrary positive integer $N$ we define a truncated series as

$$
{ \cal P } _ { N } ( s ) = \sum _ { j = 0 } ^ { N } E _ { j } ( s ) T ^ { - j } .
$$

Then

$$
\mathrm { i } \frac { 1 } { T } P _ { N } ^ { ( 1 ) } - [ H , P _ { N } ] = \mathrm { i } \frac { 1 } { T } \sum _ { j = 0 } ^ { N } E _ { j } ^ { ( 1 ) } T ^ { - j } - \sum _ { j = 0 } ^ { N } [ H , E _ { j } ] T ^ { - j } = \mathrm { i } T ^ { - ( N + 1 ) } E _ { N } ^ { ( 1 ) } .
$$

In Lemma 10, we prove that $P _ { N } ( 0 ) = P _ { 0 } ( 0 )$ and $P _ { N } ( 1 ) = P _ { 0 } ( 1 )$ , then the adiabatic error becomes

$$
\begin{array} { r l } { \displaystyle | 1 - \langle \psi _ { T } ( 1 ) | P _ { 0 } ( 1 ) | \psi _ { T } ( 1 ) \rangle | = | \langle \psi _ { T } ( 0 ) | P _ { 0 } ( 0 ) | \psi _ { T } ( 0 ) \rangle - \langle \psi _ { T } ( 0 ) | U _ { T } ( 1 ) ^ { - 1 } P _ { 0 } ( 1 ) U _ { T } ( 1 ) | \psi _ { T } ( 0 ) \rangle | } & { } \\ { \displaystyle } & { \leq \| P _ { 0 } ( 1 ) - U _ { T } ( 1 ) ^ { - 1 } P _ { 0 } ( 0 ) U _ { T } ( 1 ) \| } \\ { \displaystyle } & { = \| P _ { N } ( 1 ) - U _ { T } ( 1 ) ^ { - 1 } P _ { N } ( 0 ) U _ { T } ( 1 ) \| } \\ { \displaystyle } & { = \left\| \int _ { 0 } ^ { 1 } d s \frac { d } { d s } \left( U _ { T } ^ { - 1 } P _ { N } U _ { T } \right) \right\| . } \end{array}
$$

Straightforward computations show that

$$
\frac { d } { d s } \bigl ( U _ { T } ^ { - 1 } \bigr ) = - U _ { T } ^ { - 1 } \frac { d } { d s } \bigl ( U _ { T } \bigr ) U _ { T } ^ { - 1 } = - U _ { T } ^ { - 1 } \frac { T } { \mathrm { i } } H U _ { T } U _ { T } ^ { - 1 } = - \frac { T } { \mathrm { i } } U _ { T } ^ { - 1 } H ,
$$

$$
\begin{array} { l } { { { \displaystyle { \frac { d } { d s } } \left( U _ { T } ^ { - 1 } P _ { N } U _ { T } \right) = { \frac { d } { d s } } ( U _ { T } ^ { - 1 } ) P _ { N } U _ { T } + U _ { T } ^ { - 1 } { \frac { d } { d s } } ( P _ { N } ) U _ { T } + U _ { T } ^ { - 1 } P _ { N } { \frac { d } { d s } } ( U _ { T } ) } } } \\  { \mathrm { ~ } = - { \displaystyle { \frac { T } { \mathbf { i } } } U _ { T } ^ { - 1 } H P _ { N } U _ { T } + U _ { T } ^ { - 1 } { \displaystyle { \frac { T } { \mathbf { i } } } \left[ H , P _ { N } \right] U _ { T } + U _ { T } ^ { - 1 } T ^ { - N } E _ { N } ^ { ( 1 ) } U _ { T } + { \displaystyle { \frac { T } { \mathbf { i } } } U _ { T } ^ { - 1 } P _ { N } H U _ { T } } } } } \\ { { \mathrm { ~ } = T ^ { - N } U _ { T } ^ { - 1 } E _ { N } ^ { ( 1 ) } U _ { T } , } } \end{array}
$$

therefore

$$
| 1 - \langle \psi _ { T } ( 1 ) | P _ { 0 } ( 1 ) | \psi _ { T } ( 1 ) \rangle | \leq \left\| \int _ { 0 } ^ { 1 } T ^ { - N } U _ { T } ^ { - 1 } E _ { N } ^ { ( 1 ) } U _ { T } d s \right\| \leq T ^ { - N } \operatorname* { m a x } _ { s \in [ 0 , 1 ] } \| E _ { N } ^ { ( 1 ) } \| .
$$

ACM Trans. Quantum Comput., Vol. 3, No. 2, Article 5. Publication date: February 2022.

In Lemma 15, we prove that (the constant $c _ { f } = 4 \pi ^ { 2 } / 3 \rangle$ )

$$
\begin{array} { l } { \displaystyle \| E _ { N } ^ { ( 1 ) } \| \leq A _ { 1 } A _ { 2 } ^ { N } A _ { 3 } \frac { [ ( N + 1 ) ! ] ^ { 4 } } { ( 1 + 1 ) ^ { 2 } ( N + 1 ) ^ { 2 } } } \\ { = \frac { A _ { 1 } } { 4 } D \log ^ { 2 } \kappa \left[ A _ { 1 } ^ { - 1 } c _ { f } ^ { 3 } \frac { 1 6 } { \Delta } D \log ^ { 2 } \kappa \right] ^ { N } \frac { [ ( N + 1 ) ! ] ^ { 4 } } { ( N + 1 ) ^ { 2 } } } \\ { \displaystyle \leq \frac { A _ { 1 } } { 4 } D \log ^ { 2 } \kappa \left[ 1 6 A _ { 1 } ^ { - 1 } D c _ { f } ^ { 3 } \kappa \log ^ { 2 } \kappa \right] ^ { N } \frac { [ ( N + 1 ) ! ] ^ { 4 } } { ( N + 1 ) ^ { 2 } } } \\ { \displaystyle \leq A _ { 1 } D \log ^ { 2 } \kappa \left[ 1 6 A _ { 1 } ^ { - 1 } D c _ { f } ^ { 3 } \kappa \log ^ { 2 } \kappa N ^ { 4 } \right] ^ { N } } \end{array}
$$

where the last inequality comes from the fact that $[ ( N + 1 ) ! ] ^ { 4 } / ( N + 1 ) ^ { 2 } \le 4 N ^ { 4 N } .$ . This completes the proof of part (a).

When $T$ is large enough, we now choose

$$
N = \left\lfloor \left( 1 6 e A _ { 1 } ^ { - 1 } D c _ { f } ^ { 3 } \frac { \kappa \log ^ { 2 } \kappa } { T } \right) ^ { - \frac { 1 } { 4 } } \right\rfloor \ge 1 ,
$$

then

$$
\begin{array} { r l } & { | 1 - \langle \psi _ { T } ( 1 ) | P _ { 0 } ( 1 ) | \psi _ { T } ( 1 ) \rangle | \le A _ { 1 } D \log ^ { 2 } \kappa \left[ 1 6 A _ { 1 } ^ { - 1 } D c _ { f } ^ { 3 } \frac { \kappa \log ^ { 2 } \kappa } { T } N ^ { 4 } \right] ^ { N } } \\ & { \qquad \le A _ { 1 } D \log ^ { 2 } \kappa \exp \left( - \left( 1 6 e A _ { 1 } ^ { - 1 } D c _ { f } ^ { 3 } \frac { \kappa \log ^ { 2 } \kappa } { T } \right) ^ { - \frac { 1 } { 4 } } \right) . } \end{array}
$$

This completes the proof of part (b).

The remaining part is devoted to some preliminary results regarding $H , E$ and the technical estimates for the growth of $E _ { j }$ . It is worth mentioning in advance that in the proof we will encounter many derivatives taken on a contour integral. In fact all such derivatives taken on a contour integral will not involve derivatives on the contour. Specifically, since $( H ( s ) - z ) ^ { - 1 }$ is analytic for any $0 < | z | < \Delta ( s )$ , for any $s _ { 0 } \in ( 0 , 1 )$ , there exists a small enough neighborhood $B _ { \delta } ( s _ { 0 } )$ such that $\forall s \in B _ { \delta } ( s _ { 0 } )$ $, \oint _ { \Gamma ( s ) } G ( s , ( H ( s ) - z ) ^ { - 1 } ) d z = \oint _ { \Gamma ( s _ { 0 } ) } G ( s , ( H ( s ) - z ) ^ { - 1 } ) d z$ for any smooth mapping $G$ . This means locally the contour integral does not depend on the smooth change of the contour, and thus the derivatives will not involve derivatives on the contour. In the spirit of this trick, we write the resolvent $R ( z , s , s _ { 0 } ) = ( H ( s ) - z ) ^ { - 1 }$ for $0 \leq s \leq 1 , 0 \leq s _ { 0 } \leq 1 , z \in \mathbb { C }$ and $| z | = \Delta ( s _ { 0 } ) / 2$ and let $R ^ { ( k ) }$ denote the partial derivative with respect to 𝑠, i.e. $\textstyle { \frac { \partial } { \partial s } } R ( z , s , s _ { 0 } )$ , which means by writing $R ^ { ( k ) }$ we only consider the explicit time derivatives brought by $H$ .

Lemma 8. $( a ) H ( s ) \in C ^ { \infty }$ with $H ^ { ( k ) } ( 0 ) = H ^ { ( k ) } ( 1 ) = 0$ for all √ $k \geq 1$ . (b) There is a gap $\Delta ( s ) \geq \Delta _ { * } ( s ) = ( ( 1 - f ( s ) ) + f ( s ) / \kappa ) / \sqrt { 2 }$ which separates $o$ from the rest of the   
spectrum.

The following lemma gives the bound for the derivatives of $H$ .

Lemma 9. For every $k \geq 1 , 0 < s < 1$ ,

$$
\| H ^ { ( k ) } ( s ) \| \leq b ( s ) a ( s ) ^ { k } \frac { ( k ! ) ^ { 2 } } { ( k + 1 ) ^ { 2 } } ,
$$

where

$$
b ( s ) = \frac { 2 e } { c _ { e } } \exp \left( - \frac { 1 } { s ( 1 - s ) } \right) [ s ( 1 - s ) ] ^ { 2 } , \quad a ( s ) = \left( \frac { 2 } { s ( 1 - s ) } \right) ^ { 2 } .
$$

ACM Trans. Quantum Comput., Vol. 3, No. 2, Article 5. Publication date: February 2022.

Proof. We first compute the derivatives of $f$ . Let $g ( s ) = - s ( 1 - s )$ and $h ( y ) = \exp ( 1 / y )$ , then $f ^ { \prime } ( s ) = c _ { e } ^ { - 1 } h ( g ( s ) )$ . By the chain rule of high order derivatives (also known as Faà di Bruno’s formula),

$$
f ^ { ( k + 1 ) } ( s ) = c _ { e } ^ { - 1 } \sum _ { \substack { m _ { 1 } ! 1 ! ^ { m _ { 1 } } m _ { 2 } ! 2 ! ^ { m _ { 2 } } \cdots m _ { k } ! k ! m _ { k } } } h ^ { ( m _ { 1 } + m _ { 2 } + \cdots + m _ { k } ) } \left( g ( s ) \right) \prod _ { j = 1 } ^ { k } \left( g ^ { ( j ) } ( s ) \right) ^ { m _ { j } }
$$

where the sum is taken over all $k$ -tuples of non-negative integers $( m _ { 1 } , \cdots , m _ { k } )$ satisfying $\begin{array} { r l } { ~ } & { { } \sum _ { j = 1 } ^ { k } j m _ { j } = } \end{array}$ $k$ . Note that $g ^ { ( j ) } ( s ) = 0$ for $j \geq 3$ , and the sum becomes

$$
\begin{array} { l } { { f ^ { ( k + 1 ) } ( s ) = c _ { e } ^ { - 1 } \displaystyle \sum _ { m _ { 1 } + 2 m _ { 2 } = k } \frac { k ! } { m _ { 1 } ! 1 ! ^ { m _ { 1 } } m _ { 2 } ! 2 ! ^ { m _ { 2 } } } h ^ { ( m _ { 1 } + m _ { 2 } ) } \left( g ( s ) \right) \left( g ^ { ( 1 ) } ( s ) \right) ^ { m _ { 1 } } \left( g ^ { ( 2 ) } ( s ) \right) ^ { m _ { 2 } } } } \\ { { \displaystyle ~ = c _ { e } ^ { - 1 } \displaystyle \sum _ { m _ { 1 } + 2 m _ { 2 } = k } \frac { k ! } { m _ { 1 } ! m _ { 2 } ! 2 ^ { m _ { 2 } } } h ^ { ( m _ { 1 } + m _ { 2 } ) } \left( g ( s ) \right) \left( 2 s - 1 \right) ^ { m _ { 1 } } 2 ^ { m _ { 2 } } } } \\ { { \displaystyle ~ = c _ { e } ^ { - 1 } \displaystyle \sum _ { m _ { 1 } + 2 m _ { 2 } = k } \frac { k ! } { m _ { 1 } ! m _ { 2 } ! } h ^ { ( m _ { 1 } + m _ { 2 } ) } \left( g ( s ) \right) \left( 2 s - 1 \right) ^ { m _ { 1 } } . } } \end{array}
$$

To compute the derivatives of $h$ , we use the chain rule again to get (the sum is over $\begin{array} { r } { \sum _ { j = 1 } ^ { m } j n _ { j } = m \Big ) } \end{array}$

$$
{ \begin{array} { l } { { \displaystyle h ^ { ( m ) } ( y ) = \sum \frac { m ! } { n _ { 1 } ! 1 ! ^ { n _ { 1 } } n _ { 2 } ! 2 ! ^ { n _ { 2 } } \cdots n _ { m } ! m ! ^ { n _ { m } } } \exp ( 1 / y ) \prod _ { j = 1 } ^ { m } \left( \frac { d ^ { j } ( 1 / y ) } { d y ^ { j } } \right) ^ { n _ { j } } } } \\ { { = \sum \frac { m ! } { n _ { 1 } ! 1 ! ^ { n _ { 1 } } n _ { 2 } ! 2 ! ^ { n _ { 2 } } \cdots n _ { m } ! m ! ^ { n _ { m } } } \exp ( 1 / y ) \prod _ { j = 1 } ^ { m } \left( ( - 1 ) ^ { j } j ! y ^ { - j - 1 } \right) ^ { n _ { j } } } } \\ { { = \sum \frac { \left( - 1 \right) ^ { m } m ! } { n _ { 1 } ! n _ { 2 } ! \cdots n _ { m } ! } \exp ( 1 / y ) y ^ { - m - \sum n _ { j } } } } \end{array} }
$$

Since $0 \leq n _ { j } \leq m / j$ , the number of tuples $( m _ { 1 } , \cdots , m _ { n } )$ is less than $( m + 1 ) ( m / 2 + 1 ) ( m / 3 +$ $1 ) \cdot \cdot \cdot ( m / m + 1 ) = \binom { 2 m } { m } < 2 ^ { 2 m }$ , so for $0 < y < 1$ and $m \leq k$ we have

$$
| h ^ { ( m ) } ( y ) | \leq 2 ^ { 2 k } k ! \exp ( 1 / y ) y ^ { - 2 k } .
$$

Therefore $f ^ { ( k + 1 ) }$ can be bounded as

$$
\begin{array} { r l } & { \displaystyle | f ^ { ( k + 1 ) } ( s ) | \le c _ { e } ^ { - 1 } \sum _ { m _ { 1 } + 2 m _ { 2 } = k } \frac { k ! } { m _ { 1 } ! m _ { 2 } ! } 2 ^ { 2 k } k ! \exp ( - \frac { 1 } { s ( 1 - s ) } ) \left( \frac { 1 } { s ( 1 - s ) } \right) ^ { 2 k } | 2 s - 1 | ^ { m _ { 1 } } } \\ & { \qquad \le c _ { e } ^ { - 1 } \exp ( - \frac { 1 } { s ( 1 - s ) } ) \left( \frac { 2 } { s ( 1 - s ) } \right) ^ { 2 k } ( k ! ) ^ { 2 } \displaystyle \sum _ { m _ { 1 } \le k } \frac { 1 } { m _ { 1 } ! } } \\ & { \qquad \le e c _ { e } ^ { - 1 } \exp ( - \frac { 1 } { s ( 1 - s ) } ) \left( \frac { 2 } { s ( 1 - s ) } \right) ^ { 2 k } ( k ! ) ^ { 2 } . } \end{array}
$$

Substitute $k + 1$ by $k$ and for every $k \geq 1$

$$
\begin{array} { r l r } & { } & { | f ^ { ( k ) } ( s ) | \le e c _ { e } ^ { - 1 } \exp \left( - \frac { 1 } { s ( 1 - s ) } \right) \left( \frac { 2 } { s ( 1 - s ) } \right) ^ { 2 ( k - 1 ) } ( ( k - 1 ) ! ) ^ { 2 } } \\ & { } & { \le 4 e c _ { e } ^ { - 1 } \exp \left( - \frac { 1 } { s ( 1 - s ) } \right) \left( \frac { 2 } { s ( 1 - s ) } \right) ^ { 2 ( k - 1 ) } \frac { ( k ! ) ^ { 2 } } { ( k + 1 ) ^ { 2 } } . } \end{array}
$$

ACM Trans. Quantum Comput., Vol. 3, No. 2, Article 5. Publication date: February 2022.

Noting that $\left\| H _ { 0 } \right\| \le 1 , \left\| H _ { 1 } \right\| \le 1$ and $H ^ { ( k ) } = ( H _ { 1 } - H _ { 0 } ) f ^ { ( k ) }$ , we complete the proof of bounds for $H ^ { ( k ) }$ . □

The following result demonstrates that $E _ { j }$ ’s for all $j \geq 1$ vanish on the boundary.

Lemma 10. (a) For all $k \geq 1$ , $E _ { 0 } ^ { ( k ) } \left( 0 \right) = P _ { 0 } ^ { ( k ) } \left( 0 \right) = 0 , E _ { 0 } ^ { ( k ) } \left( 1 \right) = P _ { 0 } ^ { ( k ) } \left( 1 \right) = 0 .$ (b) For all $j \geq 1 , k \geq 0 , E _ { j } ^ { ( k ) } ( 0 ) = E _ { j } ^ { ( k ) } ( 1 ) = 0 $ .

Proof. We will repeatedly use the fact that $R ^ { ( k ) } ( 0 ) = R ^ { ( k ) } ( 1 ) = 0$ . This can be proved by taking the $k$ -th order derivative of the equation $( H - z ) R = I$ and

$$
R ^ { ( k ) } = - R \sum _ { l = 1 } ^ { k } { \binom { k } { l } } ( H - z ) ^ { ( l ) } R ^ { ( k - l ) } = - R \sum _ { l = 1 } ^ { k } { \binom { k } { l } } H ^ { ( l ) } R ^ { ( k - l ) } .
$$

(a) This is a straightforward result by the definition of $E _ { 0 }$ and the fact that $R ^ { ( k ) }$ ’s vanish on the boundary.

(b) We prove by induction with respect to $j$ . For $j = 1$ , Eq. (22) tells that

$$
{ \cal E } _ { 1 } = ( 2 \pi ) ^ { - 1 } \oint _ { \Gamma } R [ P _ { 0 } ^ { ( 1 ) } , P _ { 0 } ] R d z .
$$

Therefore each term in the derivatives of $E _ { 1 }$ must involve the derivative of $R$ or the derivative of $P _ { 0 }$ which means the derivatives of $E _ { 1 }$ much vanish on the boundary.

Assume the conclusion holds for $< j$ , then for $j$ , first each term of the derivatives of $S _ { j }$ must involve the derivative of some $E _ { m }$ with $m < j$ , which means the derivatives of $S _ { j }$ must vanish on the boundary. Furthermore, for the similar reason, Eq. (22) tells that the derivatives of $E _ { j }$ must vanish on the boundary. □

Before we process, we recall three technical lemmas introduced in [15, 25]. Throughout let $c _ { f } = 4 \pi ^ { 2 } / 3$ denote an absolute constant.

Lemma 11. Let $\alpha > 0$ be a positive real number, $\hbar , q$ be non-negative integers and $r = p + q$ . Then

$$
\sum _ { l = 0 } ^ { k } { \binom { k } { l } } \frac { [ ( l + p ) ! ( k - l + q ) ! ] ^ { 1 + \alpha } } { ( l + p + 1 ) ^ { 2 } ( k - l + q + 1 ) ^ { 2 } } \leq c _ { f } \frac { [ ( k + r ) ! ] ^ { 1 + \alpha } } { ( k + r + 1 ) ^ { 2 } } .
$$

Lemma 12. Let $k$ be a non-negative integer, then

$$
\sum _ { l = 0 } ^ { k } \frac { 1 } { ( l + 1 ) ^ { 2 } ( k + 1 - l ) ^ { 2 } } \leq c _ { f } \frac { 1 } { ( k + 1 ) ^ { 2 } } .
$$

Lemma 13. Let $A ( s ) , B ( s )$ be two smooth matrix-valued functions defined on [0, 1] satisfying

$$
\| A ^ { ( k ) } ( s ) \| \leq a _ { 1 } ( s ) a _ { 2 } ( s ) ^ { k } \frac { [ ( k + p ) ! ] ^ { 1 + \alpha } } { ( k + 1 ) ^ { 2 } } , \quad \| B ^ { ( k ) } ( s ) \| \leq b _ { 1 } ( s ) b _ { 2 } ( s ) ^ { k } \frac { [ ( k + q ) ! ] ^ { 1 + \alpha } } { ( k + 1 ) ^ { 2 } }
$$

for some non-negative functions $a _ { 1 } , a _ { 2 } , b _ { 1 } , b _ { 2 }$ , non-negative integers $\hbar , q$ and for all $k \geq 0$ . Then for every $k \geq 0 , 0 \leq s \leq 1$ ,

$$
\| ( A ( s ) B ( s ) ) ^ { ( k ) } \| \leq c _ { f } a _ { 1 } ( s ) b _ { 1 } ( s ) \operatorname* { m a x } \{ a _ { 2 } ( s ) , b _ { 2 } ( s ) \} ^ { k } { \frac { [ ( k + r ) ! ] ^ { 1 + \alpha } } { ( k + 1 ) ^ { 2 } } }
$$

where 𝑟 = 𝑝 + 𝑞.

Next we bound the derivatives of the resolvent. This bound provides the most important improvement of the general adiabatic bound.

ACM Trans. Quantum Comput., Vol. 3, No. 2, Article 5. Publication date: February 2022.

Lemma 14. For all $k \geq 0$ ,

$$
\| R ^ { ( k ) } ( z , s _ { 0 } , s _ { 0 } ) \| \leq \frac { 2 } { \Delta ( s _ { 0 } ) } \left( D \log ^ { 2 } \kappa \right) ^ { k } \frac { ( k ! ) ^ { 4 } } { ( k + 1 ) ^ { 2 } }
$$

where

$$
D = c _ { f } \frac { 2 0 4 8 \sqrt { 2 } e ^ { 2 } } { c _ { e } }
$$

Proof. We prove by induction, and for simplicity we will omit explicit dependence on arguments $z , s$ , and $s _ { 0 }$ . The estimate obviously holds for $k = 0$ . Assume the estimate holds for $< k$ . Take the $k$ th order derivative of the equation $( H - z ) R = I$ and we get

$$
R ^ { ( k ) } = - R \sum _ { l = 1 } ^ { k } { \binom { k } { l } } ( H - z ) ^ { ( l ) } R ^ { ( k - l ) } = - R \sum _ { l = 1 } ^ { k } { \binom { k } { l } } H ^ { ( l ) } R ^ { ( k - l ) } .
$$

Using Lemma 9 and the induction hypothesis, we have

$$
\| R ^ { ( k ) } \| _ { 2 } \leq \frac { 2 } { \Delta } \sum _ { l = 1 } ^ { k } { \binom { k } { l } } b a ^ { l } \frac { ( l ! ) ^ { 2 } } { ( l + 1 ) ^ { 2 } } \frac { 2 } { \Delta } \left( D \log ^ { 2 } \kappa \right) ^ { k - l } \frac { [ ( k - l ) ! ] ^ { 4 } } { ( k - l + 1 ) ^ { 2 } }
$$

To proceed we need to bound the term $\Delta ^ { - 1 } b a ^ { l }$ for $l \geq 1$ . Let us define

$$
F ( s ) = \frac { c _ { e } } { 2 ^ { 2 l } 2 \sqrt 2 e } \Delta _ { * } ^ { - 1 } ( s ) b ( s ) a ( s ) ^ { l } = \frac { \exp ( - \frac { 1 } { s ( 1 - s ) } ) } { ( 1 - f ( s ) + f ( s ) / \kappa ) [ s ( 1 - s ) ] ^ { 2 l - 2 } } .
$$

Note that $F ( 0 ) = F ( 1 ) = 0 , F ( s ) > 0$ for $s \in ( 0 , 1 )$ and $F \left( 1 / 2 + t \right) > F \left( 1 / 2 - t \right)$ for $t \in ( 0 , 1 / 2 )$ , then there exists a maximizer $s _ { * } \in [ 1 / 2 , 1 )$ such that $F ( s ) \leq F ( s _ { * } ) , \forall s \in [ 0 , 1 ]$ . Furthermore, $F ^ { \prime } ( s _ { * } ) = 0$ . Now we compute the $F ^ { \prime }$ as

$$
\begin{array} { r l } & { \quad [ ( 1 - f + f / \kappa ) ] \left[ s ( 1 - s ) ] ^ { 2 l - 2 } \right] ^ { 2 - 2 } F ^ { \prime } ( s ) } \\ & { = \exp \left( - \displaystyle \sum _ { s ( 1 - s ) } \right) \frac { 1 } { s ^ { 2 } ( 1 - s ) ^ { 2 } } \left( 1 - f + f / \kappa \right) \left[ s ( 1 - s ) \right] ^ { 2 l - 2 } } \\ & { \qquad - \exp \left( - \displaystyle \sum _ { s ( 1 - s ) } \right) \left[ ( - f ^ { \prime } + f ^ { \prime } / \kappa ) \left[ s ( 1 - s ) \right] ^ { 2 l - 2 } + ( 1 - f + f / \kappa ) ( 2 l - 2 ) \left[ s ( 1 - s ) \right] ^ { 2 l - 3 } ( \log ( \log ( \log ( \kappa ) ) ) - 1 ) \right] ^ { 2 l - 2 } } \\ & { = \exp \left( - \displaystyle \frac { 1 } { s ( 1 - s ) } \right) \left[ s ( 1 - s ) \right] ^ { 2 l - 4 } } \\ & { \qquad \times \left[ ( 1 - f + f / \kappa ) ( 1 - 2 s ) \left[ 1 - ( 2 l - 2 ) s ( 1 - s ) \right] - \exp \left( - \displaystyle \frac { 1 } { s ( 1 - s ) } \right) c _ { \epsilon } ^ { - 1 } ( - 1 + 1 / \kappa ) s ^ { 2 } ( 1 - s ) \right] ^ { 2 l - 4 } } \\ & { = \exp \left( - \displaystyle \frac { 1 } { s ( 1 - s ) } \right) \left[ s ( 1 - s ) \right] ^ { 2 l - 4 } G ( s ) } \end{array}
$$

where

$$
G ( s ) = ( 1 - f + f / \kappa ) ( 1 - 2 s ) \left[ 1 - ( 2 l - 2 ) s ( 1 - s ) \right] + \exp \left( - \frac { 1 } { s ( 1 - s ) } \right) c _ { e } ^ { - 1 } ( 1 - 1 / \kappa ) s ^ { 2 } ( 1 - s ) \left[ \frac { 1 - ( l - 2 ) s ( 1 - s ) } { l - 2 ( l - 2 ) s } \right] .
$$

The sign of $F ^ { \prime } ( s )$ for $s \in ( 0 , 1 )$ is the same as the sign of $G ( s )$ .

We now show that√ $s _ { * }$ cannot be very close to 1. Precisely, we will prove that for all $s \in \big [ 1 - \frac { c } { l \log { \kappa } } , 1 \big )$ with $c = \sqrt { c _ { e } } / 4 \approx 0 . 0 2 1$ , $G ( s ) < 0$ . For such $s$ , we have

$$
1 - f + f / \kappa \geq f ( 1 / 2 ) / \kappa > 0 ,
$$

ACM Trans. Quantum Comput., Vol. 3, No. 2, Article 5. Publication date: February 2022.

Quantum linear system solver based on time-optimal adiabatic quantum computing and quantum approximate optimization algorithm

$$
1 - 2 s < - 1 / 2 ,
$$

and

$$
1 - ( 2 l - 2 ) s ( 1 - s ) \geq 1 - ( 2 l - 2 ) ( 1 - s ) \geq 1 - { \frac { 2 c } { \log \kappa } } \geq 1 / 2 ,
$$

then

$$
\big ( 1 - f + f / \kappa \big ) \big ( 1 - 2 s \big ) \big [ 1 - \big ( 2 l - 2 \big ) s \big ( 1 - s \big ) \big ] \leq - \frac { f \big ( 1 / 2 \big ) } { 4 \kappa } = - \frac { 1 } { 8 \kappa } .
$$

On the other hand,

$$
\begin{array} { l } { \displaystyle \exp \left( - \frac { 1 } { s ( 1 - s ) } \right) \leq \exp \left( - ( 1 - \frac { c } { l \log { \kappa } } ) ^ { - 1 } \frac { l \log { \kappa } } { c } \right) } \\ { \displaystyle = \kappa ^ { - ( 1 - \frac { c } { l \log { \kappa } } ) ^ { - 1 } \frac { l } { c } } } \\ { \leq \kappa ^ { - l / c } } \\ { \leq \kappa ^ { - 1 } , } \end{array}
$$

then

$$
\begin{array} { r l } & { \quad \exp \left( - \displaystyle \frac { 1 } { s ( 1 - s ) } \right) c _ { e } ^ { - 1 } ( 1 - 1 / \kappa ) s ^ { 2 } ( 1 - s ) ^ { 2 } } \\ & { \quad \le \displaystyle \frac { 1 } { \kappa } \displaystyle \frac { 1 } { c _ { e } } \left( \displaystyle \frac { c } { l \log \kappa } \right) ^ { 2 } } \\ & { \quad \le \displaystyle \frac { 1 } { 1 6 \kappa } . } \end{array}
$$

Therefore for all $s \in \left[ 1 - \frac { c } { l \log \kappa } , 1 \right]$ we have $G ( s ) \leq - 1 / ( 1 6 \kappa ) < 0$ , which indicates $\begin{array} { r } { s _ { * } \leq 1 - \frac { c } { l \log { \kappa } } } \end{array}$ We are now ready to bound $F ( s )$ . From the equation $G ( s _ { * } ) = 0$ , we get

$$
\frac { \exp \left( - \frac { 1 } { s _ { * } ( 1 - s _ { * } ) } \right) } { 1 - f + f / \kappa } = \frac { ( 1 - 2 s _ { * } ) \left[ 1 - ( 2 l - 2 ) s _ { * } ( 1 - s _ { * } ) \right] } { c _ { e } ^ { - 1 } ( - 1 + 1 / \kappa ) s _ { * } ^ { 2 } ( 1 - s _ { * } ) ^ { 2 } } ,
$$

which gives

$$
\begin{array} { r l } & { F ( s ) \leq F ( s ) , } \\ & { \qquad \quad ( \frac { 1 - 2 s } { c } ) [ 1 - ( 2 l - 2 ) s , ( 1 - s , * ) ] } \\ & { \qquad \quad = \frac { ( l - 1 - 2 s ) [ 1 - ( l - 3 ) s , ( 1 - s , * ) ] ^ { 2 } } { c ^ { * } ( 1 - 1 ) [ \epsilon ] s ( 1 - s , * ) } } \\ & { \qquad \leq \frac { 2 s - 1 } { c \epsilon ^ { * } ( 1 - 1 ) [ \epsilon ] s ( 1 - s , * ) ] ^ { 2 } } } \\ & { \qquad \leq 2 c _ { \epsilon } \epsilon ^ { 2 } \epsilon ^ { 2 l } ( \frac { 1 - s _ { \epsilon } \epsilon ^ { 2 } } { c } ) ^ { 2 l } } \\ & { \qquad \leq 2 c _ { \epsilon } \epsilon ^ { 2 l } ( \frac { l \log \kappa } { c } ) ^ { 2 l } } \\ & { \qquad = 2 c _ { \epsilon } ( \frac { 6 4 } { c \epsilon } ) ^ { 2 l } ( \log \kappa ) ^ { 2 } l ^ { 2 l } } \\ & { \qquad \leq \frac { 2 c _ { \epsilon } } { \epsilon ^ { 2 } } ( \frac { 6 4 \epsilon ^ { 2 } } { c \epsilon } ) ^ { 2 l } ( \log \kappa ) ^ { 2 l } ( l ) ^ { 2 } . } \end{array}
$$

ACM Trans. Quantum Comput., Vol. 3, No. 2, Article 5. Publication date: February 2022.

The last inequality comes from the fact $l ^ { l } \le e ^ { l - 1 } l ! .$ , which can be derived from the fact that

$$
\sum _ { i = 1 } ^ { n } \log i \geq \int _ { 1 } ^ { n } \log x \mathrm { d } x = n \log n - ( n - 1 ) .
$$

By definition of $F ( s )$ we immediately get

$$
\Delta ^ { - 1 } b a ^ { l } \leq \frac { 2 \sqrt { 2 } e } { c _ { e } } 4 ^ { l } F \leq \frac { 4 \sqrt { 2 } } { e } \left( \frac { 2 5 6 e ^ { 2 } } { c _ { e } } \right) ^ { l } ( \log \kappa ) ^ { 2 l } ( l ! ) ^ { 2 } .
$$

Now we go back to the estimate of $R ^ { ( k ) }$ . By Lemma 11,

$$
\begin{array} { l } { \displaystyle \| R ^ { ( k ) } \| _ { 2 } \le \displaystyle \frac { 2 } { \Lambda } \displaystyle \sum _ { l = 1 } ^ { k } \bigg ( \displaystyle \mathit { \hat { k } } _ { l } \bigg ) b a ^ { l } \frac { ( l ! ) ^ { 2 } } { ( l + 1 ) ^ { 2 } } \frac { 2 } { \Delta } \left( D \log ^ { 2 } \kappa \right) ^ { k - l } \frac { \left[ ( k - l ) ! \right] ^ { 4 } } { ( k - l + 1 ) ^ { 2 } } } \\ { \displaystyle \le \frac { 2 } { \Delta } \displaystyle \sum _ { l = 1 } ^ { k } \bigg ( \displaystyle \mathit { \hat { k } } _ { l } \bigg ) \frac { 8 \sqrt { 2 } } { e } \left( \frac { 2 5 6 e ^ { 2 } } { c _ { e } } \right) ^ { l } ( \log \kappa ) ^ { 2 l } ( l ! ) ^ { 2 } \frac { ( l ! ) ^ { 2 } } { ( l + 1 ) ^ { 2 } } \left( D \log ^ { 2 } \kappa \right) ^ { k - l } \frac { \left[ ( k - l ) ! \right] ^ { 4 } } { ( k - l + 1 ) ^ { 2 } } } \\ { \displaystyle \le \frac { 2 } { \Lambda } ( D \log ^ { 2 } \kappa ) ^ { k } c _ { f } ^ { - 1 } \displaystyle \sum _ { l = 1 } ^ { k } \bigg ( \displaystyle \mathit { \hat { k } } _ { l } \bigg ) \frac { ( l ! ) ^ { 4 } [ ( k - l ) ! ] ^ { 4 } } { ( l + 1 ) ^ { 2 } ( k - l + 1 ) ^ { 2 } } } \\ { \displaystyle \le \frac { 2 } { \Delta } ( D \log ^ { 2 } \kappa ) ^ { k } \frac { ( k ! ) ^ { 4 } } { ( k + 1 ) ^ { 2 } } . } \end{array}
$$

This completes the proof.

The next lemma is the main technical result, which gives the bound of derivatives of $E _ { j }$ defined in Equation (20).

Lemma 15. (a) For all $k \geq 0$ ,

$$
\| E _ { 0 } ^ { ( k ) } \| = \| P _ { 0 } ^ { ( k ) } \| \le ( D \log ^ { 2 } \kappa ) ^ { k } \frac { ( k ! ) ^ { 4 } } { ( k + 1 ) ^ { 2 } } .
$$

$( b ) F o r a l l k \ge 0 , j \ge 1 ;$ ,

$$
\| E _ { j } ^ { ( k ) } \| \leq A _ { 1 } A _ { 2 } ^ { j } A _ { 3 } ^ { k } \frac { [ ( k + j ) ! ] ^ { 4 } } { ( k + 1 ) ^ { 2 } ( j + 1 ) ^ { 2 } }
$$

with

$$
\begin{array} { l } { { \displaystyle { \cal A } _ { 1 } = \frac { 1 } { 2 } \left[ c _ { f } ^ { 2 } \left( 1 + 2 c _ { f } ^ { 2 } \right) \right] ^ { - 1 } , } } \\ { { \displaystyle } } \\ { { \displaystyle { \cal A } _ { 2 } = { \cal A } _ { 1 } ^ { - 1 } c _ { f } ^ { 3 } \frac { 1 6 } { \Delta } D \log ^ { 2 } \kappa , } } \\ { { \displaystyle } } \\ { { \displaystyle { \cal A } _ { 3 } = D \log ^ { 2 } \kappa . } } \end{array}
$$

Remark 16. The choice of $A _ { 1 } , A _ { 2 }$ can be rewritten as

$$
\begin{array} { c } { { c _ { f } ^ { 3 } \displaystyle \frac { 1 6 } { \Delta } D \log ^ { 2 } \kappa = A _ { 1 } A _ { 2 } , } } \\ { { \displaystyle c _ { f } ^ { 2 } \left( 1 + 2 c _ { f } ^ { 2 } \right) A _ { 1 } = \displaystyle \frac { 1 } { 2 } . } } \end{array}
$$

Furthermore, using $c _ { f } > 1$ , we have

$$
c _ { f } ^ { 3 } \frac { 1 6 } { \Delta } \frac { A _ { 3 } } { A _ { 2 } } = A _ { 1 } \leq \frac { 1 } { 2 } .
$$

These relations will be used in the proof later.

ACM Trans. Quantum Comput., Vol. 3, No. 2, Article 5. Publication date: February 2022.

Proof. (a) By Lemma 14,

$$
\| P _ { 0 } ^ { ( k ) } ( s _ { 0 } ) \| = \left\| ( 2 \pi \mathrm { i } ) ^ { - 1 } \oint _ { \Gamma ( s _ { 0 } ) } R ^ { ( k ) } ( z , s _ { 0 } , s _ { 0 } ) d z \right\| \leq ( D \log ^ { 2 } \kappa ) ^ { k } \frac { ( k ! ) ^ { 4 } } { ( k + 1 ) ^ { 2 } }
$$

(b) We prove by induction with respect to $j$ . For $j = 1$ , Eq. (22) tells

$$
\| E _ { 1 } ^ { ( k ) } \| = \left\| ( 2 \pi ) ^ { - 1 } \oint _ { \Gamma } \frac { d ^ { k } } { d s ^ { k } } ( R [ P _ { 0 } ^ { ( 1 ) } , P _ { 0 } ] R ) d z \right\| \leq \frac { \Delta } { 2 } \left\| \frac { d ^ { k } } { d s ^ { k } } ( R [ P _ { 0 } ^ { ( 1 ) } , P _ { 0 } ] R ) \right\| .
$$

By Lemma 13 and Lemma 14,

$$
\begin{array} { l } { { \displaystyle \| E _ { 1 } ^ { ( k ) } \| \le \Delta c _ { f } ^ { 3 } \left( \frac { 2 } { \Delta } \right) ^ { 2 } D \log ^ { 2 } \kappa ( D \log ^ { 2 } \kappa ) ^ { k } \frac { [ ( k + 1 ) ! ] ^ { 4 } } { ( k + 1 ) ^ { 2 } } } } \\ { { \displaystyle \qquad \le A _ { 1 } A _ { 2 } A _ { 3 } ^ { k } \frac { [ ( k + 1 ) ! ] ^ { 4 } } { ( k + 1 ) ^ { 2 } ( 1 + 1 ) ^ { 2 } } . } } \end{array}
$$

Now assume $< j$ the estimate holds, for $j$ , by Lemma 12, Lemma 13 and the induction hypothesis,

$$
\begin{array} { l } { \displaystyle \| S _ { j } ^ { ( k ) } \| \le \sum _ { m = 1 } ^ { j - 1 } c _ { f } A _ { 1 } A _ { 2 } ^ { m } A _ { 1 } A _ { 2 } ^ { j - m } A _ { 3 } ^ { k } \frac { [ ( k + j ) ! ] ^ { 4 } } { ( k + 1 ) ^ { 2 } ( m + 1 ) ^ { 2 } ( j - m + 1 ) ^ { 2 } } } \\ { = A _ { 1 } ^ { 2 } A _ { 2 } ^ { j } A _ { 3 } ^ { k } \frac { [ ( k + j ) ! ] ^ { 4 } } { ( k + 1 ) ^ { 2 } } c _ { f } \sum _ { m = 1 } ^ { j - 1 } \frac { 1 } { ( m + 1 ) ^ { 2 } ( j - m + 1 ) ^ { 2 } } } \\ { \le c _ { f } ^ { 2 } A _ { 1 } ^ { 2 } A _ { 2 } ^ { j } A _ { 3 } ^ { k } \frac { [ ( k + j ) ! ] ^ { 4 } } { ( k + 1 ) ^ { 2 } ( j + 1 ) ^ { 2 } } . } \end{array}
$$

Again by Lemma 13, Lemma 14 and the induction hypothesis,

$$
\begin{array} { r l } & { \| E _ { j } ^ { ( k ) } \| \leq \| \frac { d ^ { k ^ { \prime } } } { d ^ { k ^ { \prime } } } \Big ( | 2 \pi ) ^ { - 1 } \ f _ { 1 } ^ { ( k ) ( \underline { { p } } _ { \cdot } ^ { ( k ) } , { D } _ { \cdot } \in [ | 2 d _ { j } ^ { k } ] ) } \| + \| \frac { d ^ { k ^ { \prime } } } { d ^ { k ^ { \prime } } } s _ { i } ^ { 2 } \| + \| \frac { d ^ { k ^ { \prime } } } { d ^ { k ^ { \prime } } } [ 2 \bar { D } _ { 0 } S , { D } _ { \cdot } ^ { k } ] \| } \\ & { \qquad \leq \Delta \hat { a } _ { j } ^ { ' } \left( \frac { 2 } { \Delta } \right) ^ { 2 } \bigg | \frac { d ^ { k ^ { \prime } } } { \Delta } A _ { 2 } ^ { k ^ { \prime } } \Delta _ { \underline { { s } } } \frac { 1 } { j ^ { 2 } } \lambda _ { \underline { { s } } } \frac { 1 } { ( k + 1 ) ^ { 2 } } + \mathcal { S } _ { j } ^ { ' } \lambda _ { 1 } ^ { 4 } \mathcal { A } _ { 2 } ^ { k ^ { \prime } } \frac { 1 } { ( k + 1 ) ^ { 2 } ( j + 1 ) ^ { 2 } } } \\ & { \qquad + 2 v _ { j } ^ { 2 ^ { \prime } } s _ { i } ^ { 2 } \lambda _ { \underline { { s } } } ^ { 2 } \| \frac { d ^ { k ^ { \prime } } } { ( j + 1 ) ^ { 2 } } \lambda _ { \underline { { s } } } ^ { 2 } \| \frac { ( k + 1 ) ^ { 1 } } { ( k + 1 ) ^ { 2 } } } \\ &  \qquad \leq v _ { j } ^ { 1 } \frac { 1 6 } { \Delta } A _ { 4 } ^ { k ^ { \prime } } \lambda _ { \underline { { s } } } ^ { 2 } \frac { d ^ { k ^ { \prime } } } { ( k + 1 ) ^ { 2 } ( j + 1 ) ^ { 2 } } + \mathcal { S } _ { j } ^ { 2 } A _ { 4 } ^ { 2 } \ \end{array}
$$

# F DETAILS OF THE NUMERICAL TREATMENTS AND EXAMPLES

For simulation purpose, the AQC schemes are carried out using the first-order Trotter splitting method with a time step size 0.2. We use the gradient descent method to optimize QAOA and record the running time corresponding to the lowest error in each case. In QAOA we also use the true fidelity to measure the error. RM is a Monte Carlo method, and each RM calculation involves performing 200 independent runs to obtain the density matrix $\rho ^ { ( i ) }$ for $i$ -th repetition, then we use the averaged density $\bar { \rho } = 1 / n _ { \mathrm { r e p } } \sum \rho ^ { ( i ) }$ to compute the error. We report the averaged runtime of each single RM calculation. We perform calculations for a series of 64-dimensional Hermitian positive definite dense matrices $A _ { 1 }$ , and 32-dimensional non-Hermitian dense matrices $A _ { 2 }$ with varying condition number $\kappa$ .

For concreteness, for the Hermitian positive definite example, we choose $A = U \Lambda U ^ { \dagger }$ . Here $U$ is an orthogonal matrix obtained by Gram-Schmidt orthogonalization (implemented via a QR factorization) of the discretized periodic Laplacian operator given by

$$
L = \left( \begin{array} { c c c c c c c } { { 1 } } & { { - 0 . 5 } } & { { } } & { { } } & { { } } & { { - 0 . 5 } } \\ { { - 0 . 5 } } & { { 1 } } & { { - 0 . 5 } } & { { } } & { { } } & { { } } \\ { { } } & { { - 0 . 5 } } & { { 1 } } & { { - 0 . 5 } } & { { } } & { { } } \\ { { } } & { { } } & { { \ddots } } & { { \ddots } } & { { \ddots } } & { { } } \\ { { } } & { { } } & { { } } & { { - 0 . 5 } } & { { 1 } } & { { - 0 . 5 } } \\ { { - 0 . 5 } } & { { } } & { { } } & { { } } & { { - 0 . 5 } } & { { 1 } } \end{array} \right) .
$$

$\Lambda$ is chosen to be a diagonal matrix with diagonals uniformly distributed in $[ 1 / \kappa , 1 ]$ . More precisely, $\Lambda = \mathrm { d i a g } ( \lambda _ { 1 } , \lambda _ { 2 } , \cdot \cdot \cdot , \lambda _ { N } )$ with $\lambda _ { k } = 1 / \kappa + ( k - 1 ) h , h = ( 1 - 1 / \kappa ) / ( N - 1 ) .$ Such construction ensures $A$ to be a Hermitian positive definite matrix which satisfies $\| A \| _ { 2 } = 1$ and the condition number of $A$ is $\kappa$ . We choose $\begin{array} { r } { | b \rangle = \sum _ { k = 1 } ^ { N } u _ { k } / \| \sum _ { k = 1 } ^ { N } u _ { k } \| _ { 2 } } \end{array}$ where $\left\{ u _ { k } \right\}$ is the set of the column vectors of $U$ Here $N = 6 4$ .

For the non-Hermitian positive definite example, we choose $A = U \Lambda V ^ { \dagger }$ . Here $U$ is the same as those in the Hermitian positive definite case, except that the dimension is reduced to $N = 3 2$ $\Lambda = \mathrm { d i a g } ( \lambda _ { 1 } , \lambda _ { 2 } , \cdot \cdot \cdot , \lambda _ { N } )$ with $\lambda _ { k } = ( - 1 ) ^ { k } ( 1 / \kappa + ( k - 1 ) h ) , h = ( 1 - 1 / \kappa ) / ( N - 1 ) . V$ is an orthogonal matrix obtained by Gram-Schmidt orthogonalization of the matrix

$$
K = \left( \begin{array} { c c c c c c c } { { 2 } } & { { - 0 . 5 } } & { { } } & { { } } & { { } } & { { - 0 . 5 } } \\ { { - 0 . 5 } } & { { 2 } } & { { - 0 . 5 } } & { { } } & { { } } & { { } } \\ { { } } & { { - 0 . 5 } } & { { 2 } } & { { - 0 . 5 } } & { { } } & { { } } \\ { { } } & { { } } & { { \ddots } } & { { \ddots } } & { { \ddots } } & { { } } \\ { { } } & { { } } & { { } } & { { - 0 . 5 } } & { { 2 } } & { { - 0 . 5 } } \\ { { - 0 . 5 } } & { { } } & { { } } & { { } } & { { - 0 . 5 } } & { { 2 } } \end{array} \right) .
$$

Such construction ensures $A$ to be non-Hermitian, satisfying $\| A \| _ { 2 } = 1$ and the condition number of $A$ is $\kappa$ . We choose the same $| b \rangle$ as that in the Hermitian positive definite example.