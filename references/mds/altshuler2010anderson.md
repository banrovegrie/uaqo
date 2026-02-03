# Adiabatic quantum optimization fails for random instances of NP-complete problems

Boris Altshuler,1, 2, ∗ Hari Krovi,2, † and Jeremie Roland $2$ , ‡

$\mathit { 1 }$ Columbia University ${ \boldsymbol { \mathcal { Z } } }$ NEC Laboratories America Inc.

(Dated: October 24, 2018)

Abstract

Adiabatic quantum optimization has attracted a lot of attention because small scale simulations gave hope that it would allow to solve NP-complete problems efficiently. Later, negative results proved the existence of specifically designed hard instances where adiabatic optimization requires exponential time. In spite of this, there was still hope that this would not happen for random instances of NP-complete problems. This is an important issue since random instances are a good model for hard instances that can not be solved by current classical solvers, for which an efficient quantum algorithm would therefore be desirable. Here, we will show that because of a phenomenon similar to Anderson localization, an exponentially small eigenvalue gap appears in the spectrum of the adiabatic Hamiltonian for large random instances, very close to the end of the algorithm. This implies that unfortunately, adiabatic quantum optimization also fails for these instances by getting stuck in a local minimum, unless the computation is exponentially long.

# I. INTRODUCTION

Adiabatic quantum computing is a computational paradigm (introduced in [1]) where the solution to an optimization problem is encoded in the ground state of some Hamiltonian $H _ { P }$ . An adiabatic algorithm would proceed as follows: prepare the ground state of another Hamiltonian $H _ { 0 }$ (chosen so that its ground state is easy to prepare), then slowly modify the Hamiltonian of the system from $H _ { 0 }$ to $H _ { P }$ , using an interpolation $H ( s ) = ( 1 - s ) H _ { 0 } + s H _ { P }$ . If this is done slowly enough, the Adiabatic Theorem of Quantum Mechanics [2] ensures that the system will stay close to the ground state of the instantaneous Hamiltonian throughout the evolution, so that we finally obtain a state close to the ground state of $H _ { P }$ . At this point, measuring the state will give us the solution of our problem with high probability. To put this in more quantitative terms, if the problem size (number of bits) is $N$ , then one requires the instantaneous eigenvalue gap $\Delta ( s )$ between the ground state and the first excited state to be inverse polynomial in $N$ at each step $s$ of the evolution. The computation time $T$ scales as the inverse square of the gap $T \sim 1 / \Delta ^ { 2 }$ , where $\Delta = \mathrm { m i n } _ { s } \Delta ( s )$ . This means that if the eigenvalue gap becomes exponentially small at any point in the evolution, then the computation requires exponential time. This eigenvalue gap provides a possible advantage of adiabatic quantum computing compared to the usual model based on quantum circuits. Since the system stays in its ground state throughout the evolution, robustness against thermal noise and decoherence could be provided by the eigenvalue gap [3, 4, 5]. It was also shown that adiabatic quantum computing is universal for quantum computing [6], i.e., any algorithm expressed as a quantum circuit may be translated into an adiabatic algorithm, and vice versa.

Adiabatic quantum computing was first proposed as a new approach to solve hard optimization problems, and has attracted a lot of attention because numerical evidence [7] seemed to indicate that the time required to solve NP-complete problems scaled only polynomially with the problem size, at least for small sizes. But later work gave strong evidence that this may not be the case. Refs. [8, 9] show that adiabatic algorithms can fail if one does not choose the initial Hamiltonian carefully by taking into account the structure of the problem. In Ref. [10] the Hamiltonians of certain instances of 3-SAT were mapped to an Ising model and diagonalized analytically. It was shown that the gap is exponentially small in some cases. Refs. [11] and [12] construct special instances of 3-SAT which are hard for the adiabatic algorithm to solve. More recently, it was shown that very small gaps could appear in the spectrum of the Hamiltonian due to an avoided crossing between the ground state and another level corresponding to a local minimum of the optimization problem [13, 14]. However, these results show the failure of adiabatic quantum optimization for specifically designed hard instances. In this paper, we show that adiabatic quantum optimization fails with high probability for randomly generated instances of the NP-complete problem Exact Cover 3 (EC3), also known as 1-in-3 SAT. Since the core of the argument leading to this conclusion only relies on general properties shared by other NP-complete problems such as 3-SAT, this provides a strong evidence that adiabatic quantum optimization typically cannot solve hard instances of NP-complete problems efficiently.

Our argument relies on different elements. In Section II, we introduce the problem Exact Cover 3 and the adiabatic algorithm proposed to solve it. In Section III, we study some statistical properties of random instances of EC3, which will be crucial to the result. In Section IV, we study the perturbation expansion of eigenenergies of the adiabatic Hamiltonian. In Section V, we show that perturbation theory predicts an avoided crossing and therefore a small gap occurring close to the end of the adiabatic evolution, where perturbation theory becomes valid. We also performed numerical simulations to confirm the predictions of perturbation theory and estimate the position of the avoided crossing. Finally, in Section VI, we show that this avoided crossing induces an exponentially small gap. Since these results rely on perturbation expansions, we discuss in Section VII the applicability of perturbation theory. We show how this problem is intimately related to the phenomenon of Anderson localization [15], which implies that the eigenstates of the Hamiltonian are localized for small perturbation, corresponding in our case to the end of the algorithm, close to $s = 1$ . An important observation is that the adiabatic Hamiltonian $H ( s )$ has exactly the same form as the model used by Anderson to describe localization, except that the particle evolves on an $N$ -dimensional hypercube instead of a $d$ -dimensional lattice. This emphasizes the relevance of Anderson localization for the study of quantum algorithms, even though it is currently not commonly used in this context, one example being Ref. [16] where it has been used to show weaknesses in quantum walk algorithms.

# II. PRELIMINARIES

A. Exact Cover

Exact Cover 3 (EC3) is an NP-complete problem which was considered for adiabatic algorithms in [7]. Consider an $N$ -bit string $\mathbf { x } = ( x _ { 1 } , x _ { 2 } , \ldots , x _ { N } )$ , where $x _ { i } \in \{ 0 , 1 \}$ . An instance of EC3 consists of many clauses each containing three bits. A clause $C = ( x _ { i _ { C } } , x _ { j _ { C } } , x _ { k _ { C } } )$ is said to be satisfied if and only if one of the three bits is one and the other two are zero, i.e., $x _ { i _ { C } } + x _ { j _ { C } } + x _ { k _ { C } } = 1$ . A solution is an assignment of the bits which satisfies all the clauses. The solutions of an instance of EC3 can be encoded into a cost function given by

$$
f ( \mathbf { x } ) = \sum _ { C } ( x _ { i _ { C } } + x _ { j _ { C } } + x _ { k _ { C } } - 1 ) ^ { 2 } .
$$

A solution is therefore an assignment which yields a zero cost.

We will call random instances of EC3 with $N$ bits and $M$ clauses those generated by picking uniformly at random $M$ clauses of three bits, with replacement. This distribution of instances is important since it generates hard instances that can not be solved by current classical solvers. The hardness of random instances depends highly on the clausesto-variables ratio $\textstyle \alpha = { \frac { M } { N } }$ . As $\alpha$ increases, we observe two phase transitions [17, 18]. For low $\alpha$ , the density of the solutions is high and essentially uniform. As $\alpha$ increases to the clustering threshold $\alpha _ { c }$ , the first phase transition occurs where the problem goes from having many solutions to clustered solutions with different clusters isolated from each other. The other phase transition occurs at the satisfiability threshold $\alpha _ { s }$ after which the problem is unsatisfiable with high probability. Therefore, the hard instances with only a few isolated solutions, which cannot be solved efficiently by known classical algorithms, lie just before this second phase transition, and this is the regime we will be interested in. The satisifiability threshold of EC3 has been studied in [19], where it is shown that $\alpha _ { s } = 0 . 6 2 6 3 \pm 1 0 ^ { - 4 }$ .

# B. Adiabatic Algorithm for Exact Cover

To design an adiabatic quantum algorithm for this problem, we build a problem Hamiltonian $H _ { P }$ acting on a space of $N$ qubits such that each state $| \mathbf { x } \rangle$ of the computational basis is an eigenstate of $H _ { P }$ with energy $E _ { \mathbf { x } } = f ( \mathbf { x } )$ . Using the mapping $x _ { i }  ( 1 - \sigma _ { z } ^ { ( i ) } ) / 2$ in Eq. (1), where $\sigma _ { z } ^ { ( i ) }$ is the Pauli operator $\sigma _ { z }$ acting on the $i$ -th bit, we get the following expression for

the problem Hamiltonian

$$
H _ { P } = M \mathbf { 1 } - \frac { 1 } { 2 } \sum _ { i = 1 } ^ { N } B _ { i } \sigma _ { z } ^ { ( i ) } + \frac { 1 } { 4 } \sum _ { i , j = 1 } ^ { N } J _ { i j } \sigma _ { z } ^ { ( i ) } \sigma _ { z } ^ { ( j ) } ,
$$

where $\mathbf { 1 }$ is the identity operator, $M$ is the total number of clauses, $B _ { i }$ is the number of clauses in which the bit $i$ participates and $J _ { i j }$ is the number of clauses where the bits $i$ and $j$ participate together (so $J _ { i j } = J _ { j i }$ and we set $J _ { i i } = 0$ for convenience). The solution to the EC3 instance is now given by the ground state of $H _ { P }$ . As for the initial Hamiltonian $H _ { 0 }$ , a standard choice is

$$
H _ { 0 } = - \sum _ { i = 1 } ^ { N } \sigma _ { x } ^ { ( i ) } ,
$$

where $\sigma _ { x } ^ { \left( i \right) }$ is the Pauli operator $\sigma _ { x }$ on the $i$ -th bit. $H _ { 0 }$ is therefore a 1-local Hamiltonian accepting as unique ground state the uniform superposition

$$
\vert \psi _ { 0 } \rangle = 2 ^ { - { \frac { N } { 2 } } } \sum _ { \mathbf { x } \in \{ 0 , 1 \} ^ { N } } \vert \mathbf { x } \rangle .
$$

The adiabatic quantum algorithm consists in preparing $| \psi _ { 0 } \rangle$ , applying the Hamiltonian $H _ { 0 }$ and slowly modifying the system Hamiltonian, following an interpolation

$$
H ( s ( t ) ) = ( 1 - s ( t ) ) H _ { 0 } + s ( t ) H _ { P } ,
$$

where $s ( t ) = t / T$ and $T$ is the computation time. Let $\Delta ( s )$ be the eigenvalue gap between the ground state and the first excited state of $H ( s )$ . If $T$ is large compared to $1 / \Delta ^ { 2 }$ , where $\Delta = \mathrm { m i n } _ { s } \Delta ( s )$ , we will obtain a state close to the ground state of $H _ { P }$ at the end of the evolution, so that a measurement in the computational basis will yield the solution to the problem with high probability. To evaluate the complexity of this algorithm, we therefore need to find the minimum gap of $H ( s )$ .

# III. STATISTICAL PROPERTIES OF RANDOM INSTANCES

Since we are are interested in random instances of EC3, our results will rely on some statistical properties of such instances. Recall that a random instance is obtained by picking uniformly and independently $M$ clauses of 3 bits among a set of $N$ bits. Let us study the statistical properties of such instances in the limit of large $N$ , for fixed clauses-to-variables ratio $\textstyle \alpha = { \frac { M } { N } }$ .

From Eq. (2), we see that an EC3 instance over $N$ bits is completely specified by the $N \times N$ matrix $( J _ { i j } ) _ { i , j = 1 } ^ { N }$ (note that $\begin{array} { r } { B _ { i } = \frac 1 2 \sum _ { j } J _ { i j } } \end{array}$ and $\begin{array} { r } { M = \frac { 1 } { 3 } \sum _ { i } B _ { i } ) } \end{array}$ . Such a matrix defines a graph $G$ over $N$ vertices such that there is an edge $( i , j )$ if and only if $J _ { i j } \neq 0$ . We will now show that for random instances, the local properties of $G$ are independent of $N$ .

Let us first focus on the degree of the graph. Since each clause involves two other bits, the degree of vertex $i$ is at most twice $B _ { i }$ , the number of clauses involving bit $i$ . Since the probability that bit $i$ appears in one random clause is $3 / N$ , and the $M$ clauses are picked uniformly at random and with replacement, $B _ { i }$ follows a binomial distribution

$$
\mathrm { P r } [ B _ { i } = b ] = \binom { M } { b } \left( \frac { 3 } { N } \right) ^ { b } \left( 1 - \frac { 3 } { N } \right) ^ { M - b } .
$$

In the limit $N \to \infty$ , for fixed $b$ and $\textstyle \alpha = { \frac { M } { N } }$ , we have

$$
\operatorname* { l i m } _ { N  \infty } \mathrm { P r } [ B _ { i } = b ] = e ^ { - 3 \alpha } \frac { ( 3 \alpha ) ^ { b } } { b ! } .
$$

The fact that this distribution converges for large $N$ , as well as other properties of the graph $G$ , will be crucial to our results. In particular, the fact that $B _ { i }$ follows the binomial distribution in Eq. (6) immediately implies the following (we denote by $\langle V \rangle$ and $\sigma ^ { 2 } \left( V \right)$ the mean value and variance of a random variable $V$ ).

Fact 1. For random EC3 instances with $\textstyle \alpha = { \frac { M } { N } }$ , we have $\langle B _ { i } \rangle = 3 \alpha$ and $\begin{array} { r } { \sigma ^ { 2 } \left( B _ { i } \right) = 3 \alpha ( 1 - \frac { 3 } { N } ) } \end{array}$

From Markov’s inequality, this implies that $B _ { i }$ , and in turn the degree of each vertex, remains bounded with high probability in the limit $N \to \infty$ .

From Eq. (7), we also see that $\begin{array} { r } { \operatorname* { l i m } _ { N \to \infty } \operatorname* { P r } [ B _ { i } = 0 ] = e ^ { - 3 \alpha } } \end{array}$ , so that a given bit will not appear in any clause with probability $e ^ { - 3 \alpha }$ . This implies that when we generate a random instance with $N$ bits, only a fraction of the bits will actually play a role in the instance. For a given random instance, let $N ^ { \prime }$ be the number of bits present in some clause. From Eq. (6), we can show that the fraction of present bits $N ^ { \prime } / N$ becomes more and more peaked around its mean value $1 - e ^ { - 3 \alpha }$ in the limit $N \to \infty$ .

$$
\begin{array} { r } { \operatorname* { l i m } _ { N \to \infty } \frac { \langle N ^ { \prime } \rangle } { N } = 1 - e ^ { - 3 \alpha } \ a n d \operatorname* { l i m } _ { N \to \infty } \frac { \sigma ^ { 2 } ( N ^ { \prime } ) } { N } = e ^ { - 3 \alpha } ( 1 - e ^ { - 3 \alpha } ) . } \end{array}
$$

For any set of bits $S \subseteq [ N ]$ , let us define the induced subgraph $G _ { S }$ as the graph on the set of vertices $S$ such that $( i , j ) \in S \times S$ is an edge of $G _ { S }$ if and only if it is also an edge of $G$ . When there is no ambiguity, we will sometimes use $S$ to denote the subgraph itself. For a given EC3 instance on $N$ bits, we denote by $\mathcal { G } _ { u }$ the set of subsets $S \subseteq \left\lfloor N \right\rfloor$ of size $u$ whose associated subgraphs are connected, or in short the set of connected graphs of size $u$ . Let $G _ { u } = | \mathcal { G } _ { u } |$ be the number of connected graphs of size $u$ . We will later use the fact that $G _ { u }$ is linear in $N$ (the proof is given in Appendix A).

Lemma 1. For any u ∈ N, we have $\left. G _ { u } \right. = \Theta ( N )$ .

# IV. PERTURBATION THEORY FOR THE ADIABATIC HAMILTONIAN

# A. Perturbation theory using Green’s functions

In the following sections, we will show that the Hamiltonian $H ( s )$ exhibits an exponentially small gap close to $s = 1$ . To study the spectrum of $H ( s )$ around $s = 1$ , let us consider the Hamiltonian $\begin{array} { r } { H ( \lambda ) = \frac { H ( s ) } { s } = H _ { P } + \lambda V } \end{array}$ , where $\begin{array} { r } { \lambda = \frac { 1 - s } { s } } \end{array}$ and $V = H _ { 0 }$ acts as a time independent perturbation on $H _ { P }$ . We describe how the spectrum of this Hamiltonian can be written as a perturbation expansion in powers of $\lambda$ . Let $| \mathbf { x } \rangle$ be a non-degenerate eigenstate of $H _ { P }$ with energy $E _ { \mathbf { x } } ^ { \prime }$ . We define the self-energy as

$$
\Sigma _ { \mathbf { x } } ( E ) = \sum _ { q = 1 } ^ { \infty } \lambda ^ { q } \Sigma _ { \mathbf { x } } ^ { ( q ) } ( E ) ,
$$

where

$$
\Sigma _ { \mathbf { x } } ^ { ( q ) } ( E ) = \sum _ { \mathbf { y } ^ { 1 } , \ldots , \mathbf { y } ^ { q - 1 } } { \frac { V _ { \mathbf { x y } ^ { 1 } } V _ { \mathbf { y } ^ { 1 } \mathbf { y } ^ { 2 } } \cdot \cdot \cdot \cdot V _ { \mathbf { y } ^ { q - 1 } \mathbf { x } } } { ( E - E _ { \mathbf { y } ^ { 1 } } ) ( E - E _ { \mathbf { y } ^ { 2 } } ) \cdot \cdot \cdot \cdot ( E - E _ { \mathbf { y } ^ { q - 1 } } ) } } ,
$$

$V _ { \mathbf { y } ^ { i } \mathbf { y } ^ { j } } = \langle \mathbf { y } ^ { i } | V | \mathbf { y } ^ { j } \rangle$ , and the sum in the last expression is over all eigenstates of $H _ { P }$ different from $\mathbf { x }$ . The perturbed eigenvalue $E _ { \mathbf { x } } ( \boldsymbol { \lambda } )$ is then given by the pole of the Green’s function

$$
G _ { \mathbf { x } } ( E ) = \frac { 1 } { E - E _ { \mathbf { x } } - \Sigma _ { \mathbf { x } } ( E ) } .
$$

Therefore, a perturbation expansion

$$
E _ { \mathbf { x } } ( \lambda ) = E _ { \mathbf { x } } + \sum _ { q = 1 } ^ { \infty } \lambda ^ { q } E _ { \mathbf { x } } ^ { ( q ) }
$$

may be obtained by solving the equation $E = E _ { \mathbf { x } } + \Sigma _ { \mathbf { x } } ( E )$ recursively using the perturbation expansion (8) for the self-energy. The energy up to first order is

$$
E _ { \mathbf { x } } ( \lambda ) = E _ { \mathbf { x } } + \lambda \Sigma _ { \mathbf { x } } ^ { ( 1 ) } ( E _ { \mathbf { x } } ) + O ( \lambda ^ { 2 } ) ,
$$

so that $E _ { \mathbf { x } } ^ { ( 1 ) } = \Sigma _ { \mathbf { x } } ^ { ( 1 ) }$ , where, when not explicitly written, all $\Sigma _ { \mathbf { x } } ^ { ( q ) } ( E )$ (and later also their derivatives) are evaluated at $E = E _ { \mathbf { x } }$ . The energy up to second order term is

$$
\begin{array} { l } { { E _ { \bf x } ( \lambda ) = E _ { \bf x } + \lambda \Sigma _ { \bf x } ^ { ( 1 ) } ( E _ { \bf x } + \lambda \Sigma _ { \bf x } ^ { ( 1 ) } ) + \lambda ^ { 2 } \Sigma _ { \bf x } ^ { ( 2 ) } ( E _ { \bf x } ) + O ( \lambda ^ { 3 } ) } } \\ { { \mathrm { } } } \\ { { \mathrm { } = E _ { \bf x } + \lambda \Sigma _ { \bf x } ^ { ( 1 ) } + \lambda ^ { 2 } \left( \Sigma _ { \bf x } ^ { ( 1 ) \prime } \Sigma _ { \bf x } ^ { ( 1 ) } + \Sigma _ { \bf x } ^ { ( 2 ) } \right) + O ( \lambda ^ { 3 } ) , } } \end{array}
$$

where we have used Taylor series expansion and kept terms up to second order in $\lambda$ . The second order correction $E _ { \mathbf { x } } ^ { ( 2 ) }$ is then given by the coefficient of $\lambda ^ { 2 }$ . Similarly, the energy up to third order is given by

$$
{ \begin{array} { r l } & { E _ { \mathbf { x } } ( \lambda ) = E _ { \mathbf { x } } + \lambda \Sigma _ { \mathbf { x } } ^ { ( 1 ) } \left( E _ { \mathbf { x } } + \lambda \Sigma _ { \mathbf { x } } ^ { ( 1 ) } + \lambda ^ { 2 } \left( \Sigma _ { \mathbf { x } } ^ { ( 1 ) \prime } \Sigma _ { \mathbf { x } } ^ { ( 1 ) } + \Sigma _ { \mathbf { x } } ^ { ( 2 ) } \right) \right) } \\ & { \quad \quad + \lambda ^ { 2 } \Sigma _ { \mathbf { x } } ^ { ( 2 ) } ( E _ { \mathbf { x } } + \lambda \Sigma _ { \mathbf { x } } ^ { ( 1 ) } ) + \lambda ^ { 3 } \Sigma _ { \mathbf { x } } ^ { ( 3 ) } ( E _ { \mathbf { x } } ) + O ( \lambda ^ { 4 } ) } \\ & { = E _ { \mathbf { x } } + \lambda \Sigma _ { \mathbf { x } } ^ { ( 1 ) } + \lambda ^ { 2 } \left( \Sigma _ { \mathbf { x } } ^ { ( 1 ) \prime } \Sigma _ { \mathbf { x } } ^ { ( 1 ) } + \Sigma _ { \mathbf { x } } ^ { ( 2 ) } \right) } \\ & { \quad \quad + \lambda ^ { 3 } \left( { \frac { 1 } { 6 } } ( ( \Sigma _ { \mathbf { x } } ^ { ( 1 ) } ) ^ { 3 } ) ^ { \prime \prime } + ( \Sigma _ { \mathbf { x } } ^ { ( 1 ) } \Sigma _ { \mathbf { x } } ^ { ( 2 ) } ) ^ { \prime } + \Sigma _ { \mathbf { x } } ^ { ( 3 ) } \right) + O ( \lambda ^ { 4 } ) . } \end{array} }
$$

We can now take $\begin{array} { r } { V = H _ { 0 } = - \sum _ { i } \sigma _ { x } ^ { ( i ) } } \end{array}$ and give the first few orders of the expansion. First note that in this case $\Sigma _ { \mathbf { x } } ^ { ( q ) } ( E ) = 0$ for every odd $q$ . This is because $\left. \mathbf { x } \right| H _ { 0 } \left| \mathbf { y } \right. \neq 0$ if and only if $\mathbf { x }$ and $\mathbf { y }$ differ by one bit. Since at least one $\Sigma _ { \mathbf { x } } ^ { ( q ^ { \prime } ) }$ (or some derivative of it) of odd order $q ^ { \prime }$ will appear in each term of the correction $E _ { \mathbf { x } } ^ { \left( q \right) }$ for odd order $q$ , all odd orders in the perturbation expansion vanish. In this case, the first three non-zero terms are given below.

$$
\begin{array} { l } { { \displaystyle E _ { \bf x } ^ { ( 2 ) } = \Sigma _ { \bf x } ^ { ( 2 ) } } } \\ { { \displaystyle E _ { \bf x } ^ { ( 4 ) } = \frac { 1 } { 2 } ( ( \Sigma _ { \bf x } ^ { ( 2 ) } ) ^ { 2 } ) ^ { \prime } + \Sigma _ { \bf x } ^ { ( 4 ) } } } \\ { { \displaystyle E _ { \bf x } ^ { ( 6 ) } = \frac { 1 } { 6 } ( ( \Sigma _ { \bf x } ^ { ( 2 ) } ) ^ { 3 } ) ^ { \prime \prime } + ( \Sigma _ { \bf x } ^ { ( 2 ) } \Sigma _ { \bf x } ^ { ( 4 ) } ) ^ { \prime } + \Sigma _ { \bf x } ^ { ( 6 ) } . } } \end{array}
$$

We would like to express each of these corrections as a sum over paths going from the assignment $\mathbf { x }$ and back. Consider

$$
E _ { \mathbf { x } } ^ { ( 2 ) } = \Sigma _ { \mathbf { x } } ^ { ( 2 ) } = \sum _ { \mathbf { y } } { \frac { \langle \mathbf { x } | H _ { 0 } | \mathbf { y } \rangle \langle \mathbf { y } | H _ { 0 } | \mathbf { x } \rangle } { E _ { \mathbf { x } } - E _ { \mathbf { y } } } } .
$$

Since the only non-zero terms arise when $\mathbf { y }$ is a single bit flip away from $\mathbf { x }$ , we can think of $E _ { \mathbf { x } } ^ { ( 2 ) }$ as a sum over all paths going from the assignment $\mathbf { x }$ and back which consist in flipping (and flipping back) only one bit. Similarly, we can think of $E _ { \mathbf { x } } ^ { \left( q \right) }$ as a sum over all paths on the hypercube which consist in flipping any $q / 2$ bits and flipping them back in all possible

sequences. Thus, we define $A ( P )$ such that

$$
E _ { \bf x } ^ { ( q ) } = \sum _ { P : \sum _ { i } p _ { i } = q / 2 } A ( P ) ,
$$

where $P = ( p _ { i } ) _ { i = 1 } ^ { N } \in \mathbb { N } ^ { N }$ is a vector whose $i$ -th component specifies half the number of times bit $i$ is flipped (we take half the number since any bit that is flipped must be flipped back.) Of course, specifying $P$ does not uniquely specify a path, so $A ( P )$ involves a sum over all paths corresponding to $P$ .

# B. Scaling of corrections at successive orders

In this section, we will show that when evaluating eigenvalues of the Hamiltonian $H ( \lambda )$ around $\lambda = 0$ by perturbation theory as described in the previous subsection, corrections for successive orders are all of order $\Theta ( N )$ . Since all corrections are of the same order, this means that for large $N$ , the leading behavior is given by the first non-zero correction in the expansion. This also suggests that the range of $\lambda$ for which the leading order in the perturbation expansion gives an accurate approximation is $N$ -independent (this statement will be discussed in Section VII).

Let us consider the corrections $E _ { \mathbf { x } } ^ { \left( q \right) }$ in Eq. (19). We denote as $S ( P ) \subseteq [ N ]$ the set of bits that are flipped at least once in the paths corresponding to $P$ , i.e., $S ( P ) = \{ i \in [ N ] : p _ { i } > 0 \}$ . By extension, $S ( P )$ then also defines, via the matrix $( J _ { i j }$ ), a graph where vertices correspond to elements of $S ( P )$ . In order to show that all corrections $E _ { \mathbf { x } } ^ { \left( q \right) }$ scale as $\Theta ( N )$ , we prove that we do not need to consider all vectors $\textstyle \{ P : \sum _ { i } p _ { i } = q / 2 \}$ but only those associated to connected graphs $S ( P )$ (we say that the graph is disconnected if $S ( P )$ can be expressed as a disjoint union $S _ { 1 } \cup S _ { 2 }$ such that $J _ { i j } = 0$ for all $i \in S _ { 1 }$ and $j \in S _ { 2 }$ ).

Lemma 2. Let $P _ { 0 } \in \mathbb { N } ^ { N }$ be such that the graph associated to $S ( P _ { 0 } )$ is disconnected. Then, $A ( P _ { 0 } ) = 0$ .

Proof. Let $\vec { \lambda } = ( \lambda _ { 1 } , \ldots , \lambda _ { N } )$ denote a multi-dimensional perturbation parameter, and let us consider the following generalized Hamiltonian

$$
H ^ { \prime } ( \vec { \lambda } ) = M \mathbf { 1 } - \frac { 1 } { 2 } \sum _ { i = 1 } ^ { N } B _ { i } \sigma _ { z } ^ { ( i ) } + \frac { 1 } { 4 } \sum _ { i , j = 1 } ^ { N } J _ { i j } \sigma _ { z } ^ { ( i ) } \sigma _ { z } ^ { ( j ) } - \sum _ { i = 1 } ^ { N } \lambda _ { i } \sigma _ { x } ^ { ( i ) } .
$$

It can be seen that the perturbation expansion of the eigenvalues of this Hamiltonian can be written as

$$
E _ { \mathbf { x } } ^ { \prime } ( \vec { \lambda } ) = \sum _ { q = 0 } ^ { \infty } \sum _ { P : \sum _ { i } p _ { i } = q / 2 } A ( P ) \prod _ { i } \lambda _ { i } ^ { 2 p _ { i } } ,
$$

with the same coefficients $A ( P )$ as for $E _ { \mathbf { x } } ( \boldsymbol { \lambda } )$ .

Now, let $S = S ( P _ { 0 } )$ , and consider the Hamiltonian obtained from the generalized Hamiltonian by substituting $\lambda _ { j } = 0$ if $j \not \in S$ ,

$$
H ^ { \prime } ( \vec { \lambda } _ { S } ) = M \mathbf { 1 } - \frac { 1 } { 2 } \sum _ { i = 1 } ^ { N } B _ { i } \sigma _ { z } ^ { ( i ) } + \frac { 1 } { 4 } \sum _ { i , j = 1 } ^ { N } J _ { i j } \sigma _ { z } ^ { ( i ) } \sigma _ { z } ^ { ( j ) } - \sum _ { i \in S } \lambda _ { i } \sigma _ { x } ^ { ( i ) } ,
$$

where $\vec { \lambda } _ { S }$ is the vector obtained from $\vec { \lambda }$ by performing this substitution. It is easy to see that the perturbation expansion of the eigenvalue corresponding to assignment $\mathbf { x }$ is given by

$$
E _ { \mathbf { x } } ^ { \prime } ( \vec { \lambda } _ { S } ) = \sum _ { q = 0 } ^ { \infty } \sum _ { P : \left\{ \sum _ { i } p _ { i } = q / 2 \right. }  A ( P ) \prod _ { i } \lambda _ { i } ^ { 2 p _ { i } } ,
$$

again with the same coefficients $A ( P )$ as above. Now, observe that the operators $\sigma _ { z } ^ { \left( i \right) }$ fo r $i \not \in S$ commute with the Hamiltonian $H ^ { \prime } ( \vec { \lambda } _ { S } )$ . Therefore, the bits outside of $S$ fall out of the dynamics, and it suffices to study the Hamiltonian obtained from $H ^ { \prime } ( \vec { \lambda } _ { S } )$ by substituting $\sigma _ { z } ^ { ( i ) }$ with $( - 1 ) ^ { x _ { j } }$ , where $x _ { j }$ is the value of the $j$ -th bit in assignment $\mathbf { x }$ , that is,

$$
H _ { S } ^ { \prime } ( \vec { \lambda } _ { S } ) = - \frac { 1 } { 2 } \sum _ { i \in S } B _ { i } ^ { \prime } \sigma _ { z } ^ { ( i ) } + \frac { 1 } { 4 } \sum _ { i , j \in S } J _ { i j } \sigma _ { z } ^ { ( i ) } \sigma _ { z } ^ { ( j ) } - \sum _ { i \in S } \lambda _ { i } \sigma _ { x } ^ { ( i ) }
$$

where

$$
B _ { i } ^ { \prime } = B _ { i } - \frac { 1 } { 2 } \sum _ { j \notin { \cal S } } J _ { i j } ( - 1 ) ^ { x _ { j } } ,
$$

and we have ignored an irrelevant term proportional to $\mathbf { 1 }$ . The eigenvalue $E _ { S , { \bf x } } ^ { \prime } ( \vec { \lambda } _ { S } )$ of this Hamiltonian then coincides with that of Hamiltonian $H ^ { \prime } ( \vec { \lambda } _ { S } )$ , given in Eq. (23), up to this irrelevant constant.

By assumption, the graph associated to $S$ is disconnected, so there exist disjoint nonempty sets $S _ { 1 }$ and $S _ { 2 }$ such that $S = S _ { 1 } \cup S _ { 2 }$ and $J _ { i j } = 0$ for all $i \in S _ { 1 }$ and $j \in S _ { 2 }$ . Therefore, we can write $H _ { S } ^ { \prime } ( \vec { \lambda } _ { S } )$ as

$$
H _ { S } ^ { \prime } ( \vec { \lambda } _ { S } ) = H _ { S _ { 1 } } ^ { \prime } ( \vec { \lambda } _ { S _ { 1 } } ) + H _ { S _ { 2 } } ^ { \prime } ( \vec { \lambda } _ { S _ { 2 } } ) .
$$

The perturbation expansion of the eigenvalue $E _ { S _ { k } , { \bf x } } ^ { \prime } ( \vec { \lambda } _ { S _ { k } } )$ of Hamiltonian $H _ { S _ { k } } ^ { \prime }$ can be written similarly as above

$$
E _ { S _ { k } , \mathbf { x } } ^ { \prime } ( \vec { \lambda } _ { S _ { k } } ) = \sum _ { q = 0 } ^ { \infty } \sum _ { P : \left\{ \sum _ { \cal { S } ( P ) \subseteq { \cal { S } } _ { k } } A ( P ) \prod _ { i } \lambda _ { i } ^ { 2 p _ { i } } . \right. }
$$

Moreover, the Hamiltonians $H _ { S _ { 1 } } ^ { \prime } ( \vec { \lambda } _ { S _ { 1 } } )$ and $H _ { S _ { 2 } } ^ { \prime } ( \vec { \lambda } _ { S _ { 2 } } )$ commute since they only act nontrivially on different qubits, so by Eq. (26) we have

$$
E _ { S , { \bf x } } ^ { \prime } ( \vec { \lambda } _ { S } ) = E _ { S _ { 1 } , { \bf x } } ^ { \prime } ( \vec { \lambda } _ { S _ { 1 } } ) + E _ { S _ { 2 } , { \bf x } } ^ { \prime } ( \vec { \lambda } _ { S _ { 2 } } ) .
$$

Since there are no terms proportional to $\Pi _ { i } \lambda _ { i } ^ { p _ { i } }$ in the expansion (27) for any $P = \left( p _ { i } \right)$ such that $S ( P ) = S$ , we must have that $A ( P ) = 0$ for any such $P$ . □

We now show that for connected graphs, the coefficients are finite.

Lemma 3. Let $P _ { 0 } \in \mathbb { N } ^ { N }$ such that the graph associated to $S ( P _ { 0 } )$ is connected and of size $u = O ( 1 )$ . Then, $\left. A ( P _ { 0 } ) \right. = \Theta ( 1 )$ .

Proof. Let $S = S ( P _ { 0 } )$ . Then, for any $P$ such that $S ( P ) \subseteq S$ , the amplitude $A ( P )$ in the perturbation expansion of the eigenvalue of $H$ is the same as for the Hamiltonian $H _ { S } ^ { \prime } ( \vec { \lambda } _ { S } )$ in Eq. (24). From $\textstyle \sum _ { j } J _ { i j } = 2 B _ { i }$ and the fact that for any $i \in S$ , there exists $j \in S$ such that $J _ { i j } \geq 1$ (which follows from the fact that $S$ is connected), we also see that $\begin{array} { r } { \frac { 1 } { 2 } \le B _ { i } ^ { \prime } \le 3 B _ { i } } \end{array}$ . From Fact 1, this implies that $\langle B _ { i } ^ { \prime } \rangle = \Theta ( 1 )$ . Since the Hamiltonian $H _ { S } ^ { \prime }$ acts on a finite number of bits $u$ , the perturbation expansion of its eigenvalues is $N$ independent, which proves the lemma.

We may now prove the following theorem.

Theorem 1. For any $q = O ( 1 )$ , the $q$ -th order correction $E _ { \mathbf { x } } ^ { \left( q \right) }$ of an eigenvalue of Hamiltonian $H$ scales as $\left. E _ { \mathbf { x } } ^ { ( q ) } \right. = \Theta ( N )$ .

Proof. From Lemma 2, this $q$ -th order correction may be written as

$$
E _ { \mathbf { x } } ^ { ( q ) } = \sum _ { P : \left\{ \underset { S ( P ) \mathrm { \scriptsize ~ C o n n e c t e d } } { \sum _ { i } p _ { i } = q / 2 } \right. } \left. A ( P ) . \right.
$$

From Lemma 1, the number of terms in this sum is $\Theta ( N )$ on average, and from Lemma 3, each of these terms is $\Theta ( 1 )$ on average, which implies the theorem. □

V. AVOIDED CROSSING

# A. General idea

In this section, we will show that for random instances of EC3, perturbation theory predicts that the spectrum of the Hamiltonian $H ( s )$ will exhibit an avoided crossing, and therefore a small eigenvalue gap, close to $s = 1$ . The general strategy will be the following. We first consider an instance of EC3 with at least two satisfying assignments which are isolated i.e., the Hamming distance between the solutions (the number of bits in which the two solutions differ) is of order $\Theta ( N )$ . Then, we modify the instance by adding a clause which is satisfied by one of the solutions, but not by the other, which will now correspond to a local minimum of the new cost function. We show that this can create an avoided crossing between the levels corresponding to the solution and the local minimum, and therefore a small gap in the spectrum of $H ( s )$ .

# B. Analysis by perturbation theory

As detailed in Section IV A, perturbation theory allows to evaluate the energy $E _ { \mathbf { x } } ( \boldsymbol { \lambda } )$ of an eigenstate corresponding to an assignment $\mathbf { x }$ as

$$
E _ { \mathbf { x } } ( \lambda ) = E _ { \mathbf { x } } + \sum _ { q = 1 } ^ { \infty } \lambda ^ { ( q ) } \ E _ { \mathbf { x } } ^ { ( q ) } .
$$

For two solutions $\mathbf { x } ^ { 1 } , \mathbf { x } ^ { 2 }$ , let $E _ { 1 2 } ( \lambda ) = E _ { 1 } ( \lambda ) - E _ { 2 } ( \lambda )$ be the splitting between the two energies, and $E _ { 1 2 } ^ { ( q ) }$ be the $q$ -th order correction to this splitting. We know from Section IV that the first non-zero correction to $E _ { \mathbf { x } } ( \boldsymbol { \lambda } )$ yields the leading behavior even as $N$ increases since all corrections scale as $\Theta ( N )$ . Moreover, recall from Section IV A that all odd order corrections are zero so that the first non-zero correction to $E _ { \mathbf { x } } ( \boldsymbol { \lambda } )$ appears at second order. From Eq. (18), we have

$$
\begin{array} { c } { { \displaystyle E _ { \mathbf { x } } ^ { ( 2 ) } = \sum _ { \mathbf { y } } \frac { \left. \mathbf { x } \right| H _ { 0 } \left| \mathbf { y } \right. \left. \mathbf { y } \right| H _ { 0 } \left| \mathbf { x } \right. } { E _ { \mathbf { x } } - E _ { \mathbf { y } } } } } \\ { { = - \displaystyle \sum _ { i = 1 } ^ { N } \frac { 1 } { B _ { i } } } } \end{array}
$$

where we used the fact that $E _ { \mathbf { x } } = 0$ since $\mathbf { x }$ is a solution, and that $E _ { \mathbf { y } } = B _ { i }$ if $\mathbf { y }$ differs from $\mathbf { x }$ only in the $i$ -th bit, since assignment y will violate all the clauses where this bit appears.

Since this correction does not depend on the particular solution $\mathbf { x }$ we start from, we have $E _ { 1 2 } ^ { ( 2 ) } = 0$ , so the correction to the splitting $E _ { 1 2 } ( \lambda )$ between two solutions can only appear at order 4. Eq. (16) yields

$$
E _ { \mathrm { x } } ^ { ( 4 ) } = \sum _ { i = 1 } ^ { N } \frac { 1 } { B _ { i } ^ { 3 } } + \frac { 1 } { 2 } \sum _ { \stackrel { i , j = 1 } { i \neq j } } ^ { N } \left( \frac { 1 } { B _ { i } } + \frac { 1 } { B _ { j } } \right) ^ { 2 } \left( \frac { 1 } { B _ { i } + B _ { j } } - \frac { 1 } { E _ { i j } ^ { \mathrm { x } } } \right)
$$

where $E _ { i j } ^ { \mathbf { x } } = E _ { \mathbf { y } }$ for the assignment $\mathbf { y }$ obtained from the solution $\mathbf { x }$ by flipping bits $i$ and $j$ [28]. When bits $i$ and $j$ never appear together in a clause, i.e., $J _ { i j } = 0$ , we have $E _ { i j } ^ { \bf x } = B _ { i } + B _ { j }$ and the corresponding term in Eq. (32) is zero. Therefore, we only need to sum over $i , j$ such that $J _ { i j } \neq 0$ , that is,

$$
E _ { \mathbf { x } } ^ { ( 4 ) } = \sum _ { i = 1 } ^ { N } \frac { 1 } { B _ { i } ^ { 3 } } + \frac { 1 } { 2 } \sum _ { { i , j = 1 } \atop { J _ { i j } \neq 0 } } ^ { N } \left( \frac { 1 } { B _ { i } } + \frac { 1 } { B _ { j } } \right) ^ { 2 } \left( \frac { 1 } { B _ { i } + B _ { j } } - \frac { 1 } { E _ { i j } ^ { \mathrm { x } } } \right) ,
$$

so that this expression only involves $\Theta ( N )$ terms, as was shown in Section IV. The first non-zero correction for the splitting $E _ { 1 2 } ( \lambda )$ is then given by

$$
E _ { 1 2 } ^ { ( 4 ) } = \frac { 1 } { 2 } \sum _ { { i , j = 1 \atop j } \atop i j \ne 0 } ^ { N } \left( \frac { 1 } { B _ { i } } + \frac { 1 } { B _ { j } } \right) ^ { 2 } \left( \frac { 1 } { E _ { i j } ^ { \bf x ^ { 2 } } } - \frac { 1 } { E _ { i j } ^ { \bf x ^ { 1 } } } \right) ,
$$

so that $E _ { 1 2 } ( \lambda ) = \lambda ^ { 4 } ~ E _ { 1 2 } ^ { ( 4 ) } + { \cal O } ( \lambda ^ { 6 } )$ . For random instances, $B _ { i }$ , $B _ { j }$ and $E _ { i j } ^ { \bf { x } }$ will become random numbers. Since $E _ { 1 2 } ^ { ( 4 ) }$ is given by a sum of $\Theta ( N )$ random terms with zero mean, we can expect the variance of $E _ { 1 2 } ^ { ( 4 ) }$ to be of order $\Theta ( N )$ ,

$$
\left. ( E _ { 1 2 } ^ { ( 4 ) } ) ^ { 2 } \right. \approx C ^ { ( 4 ) } N ,
$$

and similarly for the $p$ -th percentiles,

$$
P _ { p } \left( ( E _ { 1 2 } ^ { ( 4 ) } ) ^ { 2 } \right) \approx C _ { p } ^ { ( 4 ) } N ,
$$

so that $\begin{array} { r } { \operatorname* { P r } [ ( E _ { 1 2 } ^ { ( 4 ) } ) ^ { 2 } \geq C _ { p } ^ { ( 4 ) } N ] \approx 1 - \frac { p } { 1 0 0 } } \end{array}$ . In the next subsection, we will check by numerical simulations that this is a good approximation, and also estimate the constant $C ^ { ( 4 ) }$ , but from now on assume that this is correct.

Therefore, for sufficiently large $N$ , we have that the energy difference $| E _ { 1 } ( \lambda ) - E _ { 2 } ( \lambda ) |$ becomes larger than 4 with probability $1 - { \frac { p } { 1 0 0 } }$ for

$$
\lambda > \lambda _ { c } = \sqrt { 2 } ~ ( C _ { p } ^ { ( 4 ) } N ) ^ { - 1 / 8 } .
$$

![](images/27d21379d3405029a9c065df890a884198e879d7aa5c74fa46108520460a0525.jpg)  
FIG. 1: Schematical representation of a level crossing. (a) Before adding the clause, we have $E _ { 1 } ( \lambda _ { * } ) - E _ { 2 } ( \lambda _ { * } ) > 4$ . (b) By adding a clause satisfied by solution 1 but not solution 2, we create a level crossing since $E _ { 1 } ^ { \prime } ( 0 ) < E _ { 2 } ^ { \prime } ( 0 )$ but $E _ { 1 } ^ { \prime } ( \lambda _ { * } ) > E _ { 2 } ^ { \prime } ( \lambda _ { * } )$ .

Suppose that $E _ { 1 } ( \lambda _ { * } ) - E _ { 2 } ( \lambda _ { * } ) > 4$ for a given $\lambda _ { * } > \lambda _ { c }$ (the situation is depicted in Fig. 1). If we modify the problem by introducing one additional clause, we would still have $E _ { 1 } ^ { \prime } ( \lambda _ { * } ) >$ $E _ { 2 } ^ { \prime } ( \lambda _ { * } )$ since, by definition of $H _ { P }$ , one clause can only increase the energy by 4. However, if this clause is such that it is satisfied by $\mathbf { x } ^ { 1 }$ but not by $\mathbf { x } ^ { 2 }$ , we have $E _ { 1 } ^ { \prime } ( 0 ) = 0$ and $E _ { 2 } ^ { \prime } ( 0 ) > 0$ , meaning that we now have a level crossing between $\lambda = \lambda _ { * }$ and $\lambda = 0$ .

If the Hamming distance $n$ between the two solutions scales as the total number of bits $N$ , which is typically the case for instances close to the satisfiability threshold [17, 18], the crossing will only be avoided at the $n$ -th order of perturbation theory, so that the minimum gap for the new problem will scale as $\lambda _ { c } ^ { n }$ , which is exponentially small in $N$ . A more detailed study of the scaling of this gap will be provided in Section VI.

# C. Numerical simulations

To demonstrate the fact that $( E _ { 1 2 } ^ { ( 4 ) } ) ^ { 2 }$ scales as $\Theta ( N )$ and obtain an estimation of the slope, we performed the following numerical simulations. Since we are interested in hard instances, accepting very few isolated solutions, we fixed the clauses-to-variables ratio to $\alpha = 0 . 6 2$ , which is close to the satisfiability threshold $\alpha _ { s }$ [19]. For each number of bits $N$ from 15 to 200 by steps of 5, we generated 5000 random instances with $M = \lfloor \alpha N \rfloor$ clauses, and then computed the energy splitting $E _ { 1 2 } ^ { ( 4 ) }$ between the ground state of $H ( \lambda )$ and the level that would correspond to the ground state of the Hamiltonian obtained by adding a final clause (the details of this procedure are given in Appendix B).

![](images/f417f0f7b9b9088fdd390449bddedcf8bc1dcdaca9f29c397d1fec31028a3eb4.jpg)  
FIG. 2: Statistics of the fourth order correction of the splitting $( E _ { 1 2 } ^ { ( 4 ) } ) ^ { 2 }$ . Each data point is obtained from 5000 EC3 instances with $\alpha \approx 0 . 6 2$ .

In Fig. 2, we plotted the mean and some percentiles of $( E _ { 1 2 } ^ { ( 4 ) } ) ^ { 2 }$ obtained by our simulation as a function of $N$ . The mean closely agree with the linear regression in Eq. (35), with $C ^ { ( 4 ) } \approx 0 . 0 3 3$ .

Recall that we have shown in Section IV that corrections $E _ { \mathbf { x } } ^ { \left( q \right) }$ up to any order involves $\Theta ( N )$ terms. Therefore, just as for order 4, higher order corrections to the splitting squared $( E _ { 1 2 } ^ { ( q ) } ) ^ { 2 }$ are also expected to scale linearly in $N$ , so that the 4-th order gives the leading behavior of the splitting. To numerically confirm this, we also computed the 6-th order correction to the splitting for each instance. In Fig 3, we plotted the mean and some percentiles of $( E _ { 1 2 } ^ { ( 6 ) } ) ^ { 2 }$ . As expected, they also agree closely with linear regressions, and in particular, we obtain for the mean $\left. ( E _ { 1 2 } ^ { ( 6 ) } ) ^ { 2 } \right. \approx C ^ { ( 6 ) } N$ with $C ^ { ( 6 ) } \approx 0 . 4 4$ . This also allows us to give a very rough first approximation for the range of $\lambda$ where the perturbation expansion of the splitting

$$
E _ { 1 2 } ( \lambda ) = E _ { 1 2 } ^ { ( 4 ) } \lambda ^ { 4 } + E _ { 1 2 } ^ { ( 6 ) } \lambda ^ { 6 } + O ( \lambda ^ { 8 } ) ,
$$

gives an accurate estimation. Indeed, for the second term to be less than the first term,

![](images/2c8e5a1515b6af2d260aab2a3d66c05cee0c9e56ca268f3519487944e637c0f8.jpg)  
FIG. 3: Statistics of the sixth order correction of the splitting $( E _ { 1 2 } ^ { ( 6 ) } ) ^ { 2 }$ . Each data point is obtained from 5000 EC3 instances with $\alpha \approx 0 . 6 2$ .

we need $\lambda < \sqrt { | E _ { 1 2 } ^ { ( 4 ) } | / | E _ { 1 2 } ^ { ( 6 ) } | } \approx \lambda _ { r }$ , and using the linear regression for the means yields $\lambda _ { r } \approx ( C ^ { ( 4 ) } / C ^ { ( 6 ) } ) ^ { 1 / 4 } \approx 0 . 5 2$ .

# VI. SCALING OF THE GAP

In this section, we will study the scaling of the gap as the size of the problem increases, and confirm that the gap decreases exponentially. Recall how that gap is created (see Fig. 1), and consider the modified Hamiltonian with the additional clause, which exhibits an avoided crossing for some $\lambda = \lambda _ { c }$ . Let us study what happens when we evolve adiabatically from a large $\lambda$ to $\lambda = 0$ . For $\lambda > \lambda _ { c }$ , the ground state corresponds to the energy level $E _ { 2 } ^ { \prime } ( \lambda )$ , so the system is in the corresponding eigenstate $| \mathbf { x } ^ { 2 } , \lambda \rangle$ , while the energy level $E _ { 1 } ^ { \prime } ( \lambda )$ corresponds to an excited state $| \mathbf { x } ^ { 1 } , \lambda \rangle$ . However, when $\lambda < \lambda _ { c }$ , the ground state now corresponds to the energy level $E _ { 1 } ^ { \prime } ( \lambda )$ , so this means that the system has to tunnel from $| \mathbf { x } ^ { 2 } , \lambda \rangle$ to $| \mathbf { x } ^ { 1 } , \lambda \rangle$ . For small enough $\lambda$ , these states will be localized, so that the tunneling amplitude will be small if $\mathbf { x } ^ { 1 }$ and $\mathbf { x } ^ { 2 }$ are far apart. More precisely, the minimal gap $\Delta$ , that is, the width of the avoided crossing, may be evaluated in the regime of small $\lambda$ by computing the tunneling

amplitude

$$
A _ { 1 2 } ( \lambda ) = \langle \mathbf { x } ^ { 1 } | \mathbf { x } ^ { 2 } , \lambda \rangle
$$

between $| \mathbf { x } ^ { 2 } , \lambda \rangle$ and $\left| \mathbf { x } ^ { 1 } \right.$ , at $\lambda = \lambda _ { c }$ . We will show that this amplitude, and therefore the gap $\Delta$ itself, becomes exponentially small if the avoided crossing happens for small enough $\lambda _ { c }$ . This implies that unless the evolution is exponentially long, the system will not have the time to tunnel from $| \mathbf { x } ^ { 2 } , \lambda \rangle$ to $| \mathbf { x } ^ { 1 } , \lambda \rangle$ , and therefore end up in the state $\left| \mathbf { x } ^ { 2 } \right.$ , which does not correspond to a solution but only to a local minimum.

# A. The Disagree problem

We will show that computing the tunneling amplitude between two solutions of EC3 reduces to computing the same quantity for an instance of the Disagree problem. An instance of Disagree over $n$ bits consists in a set of clauses of the form ( $x _ { i _ { C } } \neq x _ { j _ { C } }$ ), where $i _ { C } , j _ { C } \in [ n ]$ . As for EC3, a solution of Disagree is a bit string $\mathbf { x } \in \{ 0 , 1 \} ^ { n }$ satisfying all clauses, and therefore corresponds to the minimum of a cost function

$$
f ( \mathbf { x } ) = \sum _ { C } ( x _ { i _ { C } } + x _ { j _ { C } } - 1 ) ^ { 2 } .
$$

Therefore, we can design an adiabatic quantum algorithm for Disagree using as final Hamiltonian

$$
H _ { P } = \frac { m } { 2 } \mathbf { 1 } + \frac { 1 } { 4 } \sum _ { i , j = 1 } ^ { n } \tilde { J } _ { i j } \sigma _ { z } ^ { ( i ) } \sigma _ { z } ^ { ( j ) } ,
$$

where, similarly to EC3, $\tilde { J } _ { i j }$ is the number of clauses where bits $i , j$ appear together, and $m$ is the total number of clauses.

Since each clause involves exactly two bits, an instance may be associated to a graph where each vertex $i \in [ n ]$ represents a bit, and each edge $( i , j ) \in [ n ] ^ { 2 }$ represents a clause ( $x _ { i } \neq x _ { j }$ ). Note that unless the graph is bipartite, it may include odd cycles and therefore the corresponding problem would have no solution. Here, we will focus on instances associated to connected bipartite graphs, which admit exactly two solutions, where all bits are set to $0$ in one partition and to $1$ in the other. Note that by negating all the bits in one partition, we may map such an instance of Disagree to an instance of Agree, where all clauses are of the type ( $x _ { i _ { C } } = x _ { j _ { C } }$ ), and where the solutions are the all-0 and all-1 strings. The Agree problem has been previously studied in the context of adiabatic quantum computing, and it has been shown that when the graph is a cycle, the gap is only polynomially small, but it can be made exponentially small by modifying the weights on the different clauses [10]. Here we show that the Disagree problem is also relevant to the study of EC3.

# B. Reduction to the Disagree problem

Claim 1. Up to leading order in perturbation theory, the tunneling amplitude between two solutions $\mathbf { x } ^ { 1 } , \mathbf { x } ^ { 2 }$ of an instance of EC3 over $N$ bits, is the same as for an instance of Disagree over n bits where the associated graph is bipartite and $n = d _ { H } ( { \bf x } ^ { \mathrm { 1 } } , { \bf x } ^ { \mathrm { 2 } } )$ is the Hamming distance between the solutions.

Proof. By perturbation theory, the amplitude of the $\mathbf { x } ^ { 1 }$ to $\mathbf { x } ^ { 2 }$ transition is given by

$$
A _ { 1 2 } = \lambda ^ { n } \sum _ { \mathbf { y } ^ { 1 } , \mathbf { y } ^ { 2 } , \ldots , \mathbf { y } ^ { n - 1 } } \frac { V _ { \mathbf { x } ^ { 1 } \mathbf { y } ^ { 1 } } V _ { \mathbf { y } ^ { 1 } \mathbf { y } ^ { 2 } } \ldots V _ { \mathbf { y } ^ { n - 2 } \mathbf { y } ^ { n - 1 } } V _ { \mathbf { y } ^ { n - 1 } \mathbf { x } ^ { 2 } } } { E _ { \mathbf { x } ^ { 2 } \mathbf { y } ^ { 1 } } E _ { \mathbf { x } ^ { 2 } \mathbf { y } ^ { 2 } } \ldots E _ { \mathbf { x } ^ { 2 } \mathbf { y } ^ { n - 1 } } } + O ( \lambda ^ { n + 1 } ) ,
$$

where the sum is over bit strings $\mathbf { y } ^ { i } \in \{ 0 , 1 \} ^ { N }$ . Since $\mathbf { x } ^ { 2 }$ is a solution, we have $E _ { \mathbf { x } ^ { 2 } } = 0$ and $E _ { { \bf x } ^ { 2 } { \bf y } ^ { i } } = - E _ { { \bf y } ^ { i } }$ . Moreover, we have $V _ { \bf x y } = 0$ unless $d _ { H } ( \mathbf { x } , \mathbf { y } ) = 1$ , so each two successive strings in a path $( \mathbf { x } ^ { 1 } , \mathbf { y } ^ { 1 } , \mathbf { y } ^ { 2 } , \ldots , \mathbf { y } ^ { n - 1 } , \mathbf { x } ^ { 2 } )$ should only differ in one bit, otherwise the corresponding term is zero. Let us assume w.l.o.g. that the bits are labeled so that $x _ { i } ^ { 1 } \neq x _ { i } ^ { 2 }$ for $1 \leq i \leq n$ , and $x _ { i } ^ { 1 } = x _ { i } ^ { 2 }$ otherwise. For a given permutation $p$ in the symmetric group $S _ { n }$ , we will denote by $\mathbf { y } ^ { ( p , j ) }$ the string obtained from $\mathbf { x } ^ { 1 }$ by flipping bits $p ( 1 ) , p ( 2 ) , . . . , p ( j )$ . We may now write the tunneling amplitude as

$$
| A _ { 1 2 } | = \lambda ^ { n } \sum _ { p \in S _ { n } } \frac { 1 } { E _ { { \bf y } ^ { ( p , 1 ) } } E _ { { \bf y } ^ { ( p , 2 ) } } \ldots E _ { { \bf y } ^ { ( p , n - 1 ) } } } + { \cal O } ( \lambda ^ { n + 1 } ) .
$$

Note that for all the strings in this expression, the bits $y _ { i } ^ { ( p , j ) } = x _ { i } ^ { 1 } = x _ { i } ^ { 2 }$ are constant for $i > n + 1$ , so these bits are irrelevant and we may consider the restriction of the EC3 instance where these bits are fixed to the same value as for $\mathbf { x } ^ { 1 }$ and $\mathbf { x } ^ { 2 }$ . In that case, all clauses only involving irrelevant bits are trivially satisfied, since they are satisfied for the solutions $\mathbf { x } ^ { 1 } , \mathbf { x } ^ { 2 }$ , so these clauses are also irrelevant and may be discarded. Starting from a satisfying assignment for three bits in an EC3 clause, flipping one or three of these bits always makes the clause violated, so relevant clauses may only involve two relevant and one irrelevant bit. Moreover, the relevant bits have to differ in the original assignment to keep the clause satisfied as we flip both of them, so the two relevant bits $i _ { C } , j _ { C }$ in a relevant clause are such that $x _ { i _ { C } } ^ { 1 } \neq x _ { j _ { C } } ^ { 1 }$ (similarly for $\mathbf { x } ^ { 2 }$ ). Therefore, discarding irrelevant bits, each relevant clause reduces to a Disagree clause ( $x _ { i _ { C } } \neq x _ { j _ { C } }$ ). Since the instance of Disagree that we obtain admits two solutions (the restrictions of $\mathbf { x } ^ { 1 } , \mathbf { x } ^ { 2 }$ to the first $n$ bits), the associated graph does not contain any odd cycle and is therefore bipartite. □

Since the graph associated with the Disagree instance is bipartite, we may further reduce it to an Agree instance (by negating all bits in one of the partitions). Therefore, it suffices to study the tunneling amplitude for the Agree problem.

# C. Upper bound for the tunneling amplitude

Lemma 4. For any connected graph $G$ on n vertices, the tunneling amplitude between the all-0 and all-1 solutions of the associated Agree instance is $\begin{array} { r } { | A _ { 1 2 } | \le \frac 1 2 ( 2 \lambda ) ^ { n } + O ( \lambda ^ { n + 1 } ) } \end{array}$ .

From there, we can conclude that if an avoided crossing happens at $\lambda = \lambda _ { c }$ the minimal gap will scale as

$$
\Delta = O \left( \left( \frac { \lambda _ { c } } { \lambda _ { a } } \right) ^ { n } \right) ,
$$

for some constant $\begin{array} { r } { \lambda _ { a } > \frac { 1 } { 2 } } \end{array}$ , so that it becomes exponentially small if $\lambda _ { c } < \frac { 1 } { 2 }$ . In Appendix C, we also provide an estimation of the tunneling amplitude and show that the estimation matches the upper bound up to a constant. In particular, we find $\lambda _ { a } \approx 0 . 8 1$ for $\alpha = 0 . 6 2$ .

Proof. For a given permutation $p \in S _ { n }$ , let $\begin{array} { r } { A _ { p } = \prod _ { j = 1 } ^ { n - 1 } ( E _ { \mathbf { y } ^ { ( p , j ) } } ) ^ { - 1 } } \end{array}$ . We need to prove that $\textstyle \sum _ { p \in S _ { n } } A _ { p } \leq 2 ^ { n - 1 }$ . We will actually show that for any tree, $\textstyle \sum _ { p \in S _ { n } } A _ { p } = 2 ^ { n - 1 }$ . Since the energies $E _ { \mathbf { y } ^ { ( p , j ) } }$ can only decrease when removing clauses, the amplitude for a spanning tree of a graph is an upper bound on the amplitude for the graph itself, so this implies the lemma.

We prove that $\begin{array} { r } { \sum _ { p \in S _ { n } } A _ { p } = 2 ^ { n - 1 } } \end{array}$ for all trees by induction on the size of the tree $n$ . For $n = 2$ , the only tree consists in two vertices connected by an edge, corresponding to a unique clause ( $x _ { 1 } = x _ { 2 }$ ). There are only two permutations $p \in S _ { 2 }$ , and since flipping either bit will violate the clause, we have $A _ { p } = 1$ for each $p$ and finally $A _ { 1 2 } = 2$ .

Suppose that $\textstyle \sum _ { p \in S _ { n } } A _ { p } = 2 ^ { n - 1 }$ for all trees of size $n$ . We show that this implies that $\textstyle \sum _ { p \in S _ { n + 1 } } A _ { p } = 2 ^ { n }$ for all trees of size $n + 1$ . The set of trees of size $n + 1$ may be generated by attaching an additional vertex to any possible vertex of any possible tree of size $n$ . Let us now consider a particular tree of size $n$ , and suppose we attach an $( n + 1 )$ -th vertex to the vertex number $k$ . Let us represent a permutation $p \in S _ { n }$ as a vector $p = ( p ( 1 ) , \dots , p ( n ) )$ . Then all permutations $p ^ { \prime } \in S _ { n + 1 }$ may be obtained by considering all permutations $p \in S _ { n }$ , and inserting element $( n + 1 )$ in all possible positions. Let $p _ { l } \in S _ { n + 1 }$ be the permutation obtained from $p \in S _ { n }$ by inserting element $( n + 1 )$ after element $p ( l )$ , that is, $p _ { l } = ( p ( 1 ) , \ldots , p ( l ) , n +$ $1 , p ( l + 1 ) , \dots , p ( n ) )$ , where $0 \leq l \leq n$ (for $l = 0$ , the element is inserted in first position, before $p ( 1 )$ ). We then have $\begin{array} { r } { \sum _ { p ^ { \prime } \in S _ { n + 1 } } A _ { p ^ { \prime } } = \sum _ { p \in S _ { n } } \sum _ { l = 0 } ^ { n } A _ { p _ { l } } } \end{array}$ . We will now show that for any $p \in S _ { n }$ , we have $\textstyle \sum _ { l = 0 } ^ { n } A _ { p _ { l } } = 2 A _ { p }$ , whatever the tree of size $n$ we start with and the vertex $k$ where we attach the additional vertex. This allows to conclude the proof.

Let us fix a permutation $p \in S _ { n }$ , and write $E _ { j } = E _ { \mathbf { y } ^ { ( p , j ) } }$ , so that $\begin{array} { r } { A _ { p } = \prod _ { j = 1 } ^ { n - 1 } ( E _ { j } ) ^ { - 1 } } \end{array}$ . We need to compute $\textstyle \sum _ { l = 0 } ^ { n } A _ { p _ { l } }$ for the new Agree instance, obtained by attaching an $( n + 1 )$ -th vertex to the vertex number $k$ of the associated graph, or equivalently introducing a new clause ( $x _ { k } = x _ { n + 1 }$ ). Let $k ^ { \prime } = p ^ { - 1 } ( k )$ . Starting from the all-0 solution, let us study how the energy changes as we flip bits in the order specified by $p _ { l }$ . For $0 \leq l \leq k ^ { \prime } - 1$ the additional clause will be violated as soon as we flip the new bit $n + 1$ (in position $l$ ), and until we flip bit $k$ (in position $k ^ { \prime }$ ). Therefore, we have

$$
A _ { p _ { l } } = \prod _ { j = 1 } ^ { l } ( E _ { j } ) ^ { - 1 } \prod _ { j ^ { \prime } = l } ^ { k ^ { \prime } - 1 } ( E _ { j ^ { \prime } } + 1 ) ^ { - 1 } \prod _ { j ^ { \prime \prime } = k ^ { \prime } } ^ { n - 1 } ( E _ { j ^ { \prime \prime } } ) ^ { - 1 } ,
$$

and it is straightforward to check that $\begin{array} { r } { \sum _ { l = 0 } ^ { k ^ { \prime } - 1 } A _ { p _ { l } } = \prod _ { j = 1 } ^ { n - 1 } ( E _ { j } ) ^ { - 1 } = A _ { p } } \end{array}$ . Similarly, for $k ^ { \prime } \leq$ $l \leq n$ we also obtain $\textstyle \sum _ { l = k ^ { \prime } } ^ { n } A _ { p _ { l } } = A _ { p }$ , and therefore $\textstyle \sum _ { l = 0 } ^ { n } A _ { p _ { l } } = 2 A _ { p }$ as claimed. □

# VII. ANDERSON LOCALIZATION AND THE APPLICABILITY OF PERTUR-BATION THEORY

As shown in Section V, the spectrum of $H ( \lambda )$ presents avoided crossings for $\lambda$ close to zero, and the position of the first avoided crossing $\lambda _ { c }$ is expected to scale as $O ( N ^ { - 1 / 8 } )$ . The presence of an avoided crossing makes the perturbation expansion divergent for $\lambda > \lambda _ { c }$ . This means that, strictly speaking, the convergence radius of the perturbation theory scales as $\lambda _ { c } = { \cal O } ( N ^ { - 1 / 8 } )$ , which tends to zero as $N$ becomes large.

However, this does not imply that we can not use perturbation theory to estimate the spectrum of $H ( \lambda )$ beyond $\lambda _ { c }$ . For $\lambda > \lambda _ { c }$ , the perturbation expansion will be asymptotic rather than convergent. While asymptotic expansions do not generally converge, they may still provide accurate approximations as long as only a finite number of terms are considered.

In our case, the divergence is due to an avoided crossing between two levels corresponding to assignments at a Hamming distance $n = \Theta ( N )$ from each other. This means that the divergence will only appear at order $n = \Theta ( N )$ in perturbation theory, so that successive orders of the perturbation expansion will provide better and better approximations to the spectrum of $H ( \lambda )$ , as long as we stop at a finite order. On the other hand, for orders higher than $n$ , the expansion will start diverging and the approximation will become less and less accurate. The following lemma may be used to obtain an upper bound on the error of the estimation of an eigenvalue.

Lemma 5. Let $| \tilde { \psi } \rangle$ and $\tilde { E }$ be estimations of an eigenstate and corresponding eigenvalue of a Hamiltonian $H$ . Then $H$ admits an eigenvalue $E$ such that $| E - \tilde { E } | \leq | | ( H - \tilde { E } \mathbf { 1 } ) | \tilde { \psi } \rangle | |$ .

Proof. Let $\epsilon = | | ( H - \tilde { E } { \bf 1 } ) | \tilde { \psi } \rangle | |$ . By definition, we have $\epsilon ^ { 2 } = \langle \tilde { \psi } | ( H - \tilde { E } { \bf 1 } ) ^ { 2 } | \tilde { \psi } \rangle$ . This implies that $( H - \tilde { E } \mathbf { 1 } ) ^ { 2 }$ has an eigenvalue $e ^ { 2 }$ such that $0 \leq e ^ { 2 } \leq \epsilon ^ { 2 }$ . In turn, ${ \cal H } - \tilde { E } { \bf 1 }$ must have an eigenvalue $e$ with $- \epsilon \leq e \leq \epsilon$ or, equivalently, $H$ has an eigenvalue $E = \tilde { E } + e$ . $\sqsubset$

If the estimations are obtained from $q$ -th order perturbation theory, this implies that the error on the eigenvalue may be bounded by computing the $( q + 1 )$ -th order corrections to the eigenvalue and eigenstate. If the $( q + 1 )$ -th order corrections are small compared to the $q$ -th order estimation, we still obtain a perfectly valid estimation, even if we are outside of the convergence radius.

Of course, when $\lambda$ becomes much larger, perturbation theory will eventually fail as the error due to higher orders will not be small compared to the estimation anymore. The success of perturbation theory relies on the fact that the perturbed eigenstate is close enough to the unperturbed one. In our case, an unperturbed eigenstate corresponds to a basis state $| \mathbf { x } \rangle$ , and the perturbed eigenstate will be close when it has a large overlap on $| \mathbf { x } \rangle$ , and a smaller overlap on other basis states $| \mathbf { y } \rangle$ , decreasing exponentially with the Hamming distance $d _ { H } ( \mathbf { x } , \mathbf { y } )$ . Such a state is called a localized state. Therefore, the validity of perturbation theory is intimately related to the phenomenon of Anderson localization.

Note that the Hamiltonian $H ( \lambda ) = H _ { P } + \lambda H _ { 0 }$ may be written as

$$
H ( \lambda ) = \sum _ { \mathbf { x } \in \{ 0 , 1 \} ^ { N } } E _ { \mathbf { x } } | \mathbf { x } \rangle \langle \mathbf { x } | - \lambda \sum _ { \mathbf { x } , \mathbf { y } : d _ { H } ( \mathbf { x } , \mathbf { y } ) = 1 } | \mathbf { x } \rangle \langle \mathbf { y } | ,
$$

where the second term (kinetic energy) describes a particle hopping on the vertices of a hypercube, and the first term (potential) adds random energies to each vertex of the hypercube (here the randomness comes from the distribution of random instances). This expression is therefore very similar to the Hamiltonian used by Anderson to demonstrate his famous localization effect in disordered systems [15], the main difference being that the geometry of the system is the $N$ -dimensional hypercube instead of the $d$ -dimensional lattice. The key feature of Anderson localization is that for large enough disorder, or in our terms for small enough $\lambda$ , the eigenstates of $H ( \lambda )$ are localized (i.e., the particle is bound to a vertex of the hypercube) so that perturbation theory is applicable in this regime. On the other hand, for large $\lambda$ , the first term (corresponding to the disorder) is negligible and the eigenstates of $H ( \lambda )$ are close to the eigenstates of $H _ { 0 }$ , describing waves travelling through the hypercube. Therefore, for large $\lambda$ , the eigenstates of $H ( \lambda )$ will have amplitude over all basis states $\vert \mathbf { x } \rangle$ and be called extended.

The transition from localized to extended states marks the failure of perturbation theory, and the position $\lambda _ { r }$ of this transition may be viewed as a weak notion of convergence radius, as shown by Anderson. To circumvent the divergence of perturbation theory due to avoided crossings close to $\lambda = 0$ , Anderson proposed the following resolution. He added a small imaginary part $i \eta$ to all energies $E _ { \mathbf { x } } ^ { ' }$ of the unperturbed Hamiltonian. After this, perturbation theory provides a convergent series, which Anderson called locator expansion. Then, he took the limit $\eta \longrightarrow 0$ , but only after taking the limit $N  \infty$ . Recall that the original divergence of the perturbation expansion started at order $n = \Theta ( N )$ . By taking $N  \infty$ before $\eta \longrightarrow 0$ , this keeps the series convergent and the radius of convergence $\lambda _ { r }$ then corresponds to the transition from localized to extended states (note that if we take the limits in the other order, we would obtain the original radius of convergence $\lambda _ { c }$ due to avoided crossings, which goes to zero as $O ( N ^ { - 1 / 8 } )$ ).

For conventional Anderson localization, the contribution $i \eta$ to the energies can be due to a weak coupling to a thermal bath, or to a possible escape of the particle through the boundary of the system. In the case of adiabatic quantum optimization, the basic idea is that $i \hbar / T$ (where $T$ is the total computation time) would play the same role as $i \eta$ . Indeed let $\Delta$ be the eigenvalue gap created by an avoided crossing. During an evolution of time $T$ , the system cannot resolve energies smaller than $\hbar / T$ . If $\Delta \ll \hbar / T$ , the system will therefore behave as if the avoided crossing was an actual crossing between two decoupled levels, and the divergence of the perturbation expansion due to this avoided crossing will disappear. We have shown in the previous section that $\Delta$ is exponentially small, which implies that this argument is consistent unless we consider an exponentially long time $T > \hbar / \Delta$ . While a complete analysis of Anderson localization in adiabatic quantum optimization could be the subject of an article on its own, the only property that we need is that the position of the transition $\lambda _ { r }$ decreases slower than the position of the first avoided crossing $\lambda _ { c }$ . For Anderson localization on a $d$ -dimensional lattice with random energies of order $E$ , $\lambda _ { r }$ is believed to scale as $\Theta ( E / ( d \ln d ) )$ [20, 21]. In our case, both the degree of vertices and the random energies scale as $\Theta ( N )$ , so we can expect by analogy that $\lambda _ { r } = \Omega ( 1 / \ln N )$ , which is sufficient for our result since $\lambda _ { c } = { \cal O } ( N ^ { - 1 / 8 } )$ . This is probably pessimistic since the conventional Anderson localization considers the critical $\lambda$ for which all eigenstates are still localized, while we are only interested in low energy eigenstates which remain localized much longer (as the density of eigenvalues is much larger in the middle of the spectrum, this is where the first extended states appear). Moreover, since we have shown in Section IV that all terms in the perturbation expansion scale as $\Theta ( N )$ , meaning that dividing the expansion by $N$ gives an expression which is essentially $N$ -independent, it is actually likely that $\lambda _ { r } = \Theta ( 1 )$ for low energy states.

# VIII. CONCLUSION AND DISCUSSION

Putting everything together, we conclude that the adiabatic quantum optimization algorithm fails for random instances of EC3 because of the presence of an exponentially small gap close to the end of the evolution (at $s = 1$ or $\lambda = 0$ ). This result relies on different elements. In Section IV, we have shown that all corrections in the perturbation expansion of eigenenergies of $H ( \lambda )$ scale as $\Theta ( N )$ . In Section V, we have shown that perturbation theory predicts an avoided crossing to occur for some $\lambda _ { c } = { \cal O } ( N ^ { - 1 / 8 } )$ , and confirmed this scaling by numerical simulations. In Section VII, we have also argued that by analogy to the usual Anderson model, we can expect states to be localized for small enough $\lambda < \lambda _ { r } = \Omega ( 1 / \log N )$ , so that perturbation theory is applicable in this regime. Since, as $N$ increases, $\lambda _ { c }$ decreases faster than $\lambda _ { r }$ , for large enough $N$ the expected avoided crossing occurs for $\lambda _ { c } < \lambda _ { r }$ , where the perturbation expansion is accurate, so that the prediction of perturbation theory becomes valid. Finally, in Section VI, we have shown that the gap induced by an avoided crossing at $\lambda _ { c }$ will scale as $\Delta = O ( \lambda _ { c } / \lambda _ { a } ) ^ { n }$ , where $\lambda _ { a }$ is a constant and $n$ is the Hamming distance between the assignments corresponding to the two levels. For large instances close to the satisfiability threshold $\alpha _ { s }$ , random instances will only have a few isolated solutions which are essentially independent from each other, so that $n = \Theta ( N )$ . Moreover, since $\lambda _ { c } = { \cal O } ( N ^ { - 1 / 8 } )$ , this implies that the gap will scale as $\Delta = 2 ^ { - O ( N \log N ) }$ , and therefore the algorithm will fail unless it takes (super-)exponential time. It is interesting to note that this scaling matches a lower bound proved by van Dam and Vazirani (see [12], the proof is given in Appendix D for completeness), so that the typical gap for random instances is really as small as it can get. The fact that the gap is actually super-exponentially small also implies that the complexity of the AQO algorithm will be even worse than classical solvers (including the naive algorithm that exhaustively checks all possible assignments).

While our results predict an exponentially small gap to occur closer and closer to the end of the evolution (at $s = 1$ ), an obvious question is why this was not observed in previous numerical simulations of the gap, where it seemed to scale polynomially and occur close to a fixed $s$ , at least for small $N$ (up to $N \lesssim 2 0$ in [7, 22], 60 in [23] and 128 in [24], each using different methods). As for the position of the gap, note that it scales as $\lambda _ { c } = { \cal O } ( N ^ { - 1 / 8 } )$ , so the dependence on $N$ is weak and we need to consider a very broad range of $N$ to observe it. More importantly, $N$ must also be large enough so that the avoided crossing happens in a region where perturbation theory is applicable, i.e., $\lambda _ { c } < \lambda _ { r }$ , and where the tunneling amplitude decreases exponentially, i.e., $\lambda _ { c } < \lambda _ { a }$ . Since we have found the condition $\lambda _ { c } > \sqrt { 2 } ~ ( C ^ { ( 4 ) } N ) ^ { - 1 / 8 }$ for an avoided crossing to occur at $\lambda _ { c }$ , and obtained the estimations $\lambda _ { r } \approx 0 . 5 2$ and $\lambda _ { a } \approx 0 . 8 1$ , this implies the bound $N > \frac { 1 6 } { C ^ { ( 4 ) } \lambda _ { r } ^ { 8 } } \approx 8 6 0 0 0$ bits to observe the exponentially small gap predicted by our approach. While this number is very high, practically the exponentially small gap could appear much faster. A first reason is that in many cases, an additional clause will only increase the energy by $1$ , and not the maximum 4, due to the form of the cost function in Eq. (1). If we only impose that $E _ { 1 2 } ( \lambda ) > 1$ , we see that small gaps already occur with high probability for $N > \frac { 1 } { C ^ { ( 4 ) } \lambda _ { r } ^ { 8 } } \approx 5 4 0 0$ . A second reason is that in our numerical simulations, we only considered avoided crossings created by the addition of the last clause, but any of the $M - 1$ other clauses could induce other avoided crossings, so that it could be possible to observe this exponentially small gap as soon as $N$ is of the order of a few hundred bits. In particular, let us note that very recent numerical simulations up to $N = 2 5 6$ by Young et al. have revealed that more and more instances exhibit a first order phase transition and therefore a very small gap [25], which could be due to the mechanism described in the present paper. In Figure 4, we plotted a level crossing predicted by fourth order perturbation theory for an instance with $N = 2 0 0$ obtained during our numerical simulations. The crossing occurs at $\lambda \approx 0 . 5 1$ (possibly inside the region where perturbation theory is valid), and the corresponding assignments are at distance $n = 6 0$ from each other.

![](images/28fd6ee0ae9d202b3e22b8524b40371c72584065f960670dbb758abe7800606e.jpg)  
FIG. 4: Simulation of a level crossing for a random instance with $N = 2 0 0$ bits and $\alpha \approx 0 . 6 2$ , obtained by fourth order perturbation theory. Inset: To make the crossing more apparent, we plotted the energy differences $E _ { 1 } - E _ { 2 }$ and $E _ { 2 } - E _ { 1 }$ .

While our argument immediately implies that a particular quantum adiabatic algorithm for EC3 will fail, it is important to note that it also applies to more general cases. In particular, it does not rely on the specific form of the problem Hamiltonian $H _ { P }$ , but rather on its general statistical properties, so that it should extend to other NP-complete problems such as 3-SAT. Moreover, our argument does not rely on the precise form of the initial Hamiltonian $H _ { 0 }$ either, or even on the possible path between the initial and the final Hamiltonian, but only on the behavior of the perturbation in the vicinity of the final Hamiltonian $H _ { P }$ , and we would actually obtain similar conclusions for any perturbation acting locally on the qubits. Therefore, any adiabatic quantum algorithm aimed at solving a similar NP-complete optimization problem by mapping its cost function to a final Hamiltonian would eventually fail for the same reason. Actually, for other problems the situation could be even worse, in that the small gap could occur for smaller instances than for EC3. Indeed, while for EC3 the first non-zero correction to the splitting $E _ { 1 2 } ( \lambda )$ between two solutions only appears at order 4 of perturbation theory, for many other problems, such as 3-SAT, a similar Hamiltonian would already exhibit a splitting at order 2, so that the position of the avoided crossing would scale as $\lambda _ { c } = O ( N ^ { - 1 / 4 } )$ , and therefore this avoided crossing would happen inside the region where perturbation theory is valid for even smaller instances.

# Acknowledgments

We thank A. Childs, E. Farhi, J. Goldstone, S. Gutmann, M. R¨otteler and A. P. Young for interesting discussions. We thank the High Availability Grid Storage department of NEC Laboratories America for giving us access to their cloud to run our numerical simulations. This research was supported in part by US DOE contract No. AC0206CH11357.

[1] E. Farhi, J. Goldstone, S. Gutmann, and M. Sipser (2000), e-print quant-ph/0001106.   
[2] A. Messiah, M´ecanique Quantique (Dunod, Paris, 1959).   
[3] A. M. Childs, E. Farhi, and J. Preskill, Physical Review A 65, 012322 (2002), e-print quantph/0108048.   
[4] J. Roland and N. J. Cerf, Physical Review A 71, 032330 (2005), e-print quant-ph/0409127.   
[5] D. Lidar, Physical Review Letters 100, 160506 (2008).   
[6] D. Aharonov, W. van Dam, J. Kempe, Z. Landau, and S. Lloyd, in Proceedings of the 45th Annual Symposium on the Foundations of Computer Science (IEEE Computer Society Press, New York, 2004), pp. 42–51, e-print quant-ph/0405098.   
[7] E. Farhi, J. Goldstone, S. Gutmann, J. Lapan, A. Lundgren, and D. Preda, Science 292, 472 (2001), e-print quant-ph/0104129.   
[8] E. Farhi, J. Goldstone, S. Gutmann, and D. Nagaj, International Journal of Quantum Information 6, 503 (2008).   
[9] E. Farhi, J. Goldstone, and S. Gutmann (2002), e-print quant-ph/0201031.   
[10] B. Reichardt, in Proceedings of the 36th Annual Symposium on the Theory of Computing (IEEE Computer Society Press, New York, 2004), pp. 279–287.   
[11] W. van Dam, M. Mosca, and U. Vazirani, in Proceedings of the 42nd Annual Symposium on the Foundations of Computer Science (IEEE Computer Society Press, New York, 2001), pp. 279–287. [12] W. van Dam and U. Vazirani, unpublished note (2003).   
[13] M. H. S. Amin and V. Choi (2009), e-print arXiv:0904.1387.   
[14] E. Farhi, J. Goldstone, D. Gosset, S. Gutmann, H. B. Meyer, and P. Shor (2009), e-print arXiv:0909.4766.   
[15] P. W. Anderson, Physical Review 109, 1492 (1958).   
[16] J. P. Keating, N. Linden, J. C. F. Matthews, and A. Winter, Physical Review A 76, 012315 (2007).   
[17] G. Biroli, R. Monasson, and M. Weigt, European Physical Journal B 14, 551 (2000).   
[18] L. Zdeborov´a and M. M´ezard, Physical Review Letters 101, 078702 (2008).   
[19] J. Raymond, A. Sportiello, and L. Zdeborov´a, Physical Review E 76, 011101 (2007).   
[20] K. Efetov, Soviet Physics - Journal of Experimental and Theoretical Physics 67, 199 (1988).   
[21] R. Abou-Chacra, D. J. Thouless, and P. W. Anderson, Journal of Physics C 6, 1734 (1972).   
[22] T. Hogg, Physical Review A 67, 022314 (2003).   
[23] M. C. Ba˜nuls, R. Or´us, J. I. Latorre, A. P´erez, and P. Ruiz-Femen´ıa, Physical Review A 73, 022344 (2006).   
[24] A. P. Young, S. Knysh, and V. N. Smelyanskiy, Physical Review Letters 101, 170503 (2008).   
[25] A. P. Young, S. Knysh, and V. N. Smelyanskiy (2009), e-print arXiv/0910.1378.   
[26] M. Davis and H. Putnam, Journal of the ACM 7, 201 (1960).   
[27] M. Davis, G. Logemann, and D. Loveland, Communications of the ACM 5, 394 (1962).   
[28] We have $E _ { i j } ^ { \mathbf { x } } \neq 0$ unless there is another solution at Hamming distance 2, which would typically not happen for an instance that has been properly cleaned as described in Appendix B.

# APPENDIX A: PROOF OF LEMMA 1

The proof of the lemma relies on the following claim.

Claim 2. For any $u ~ \in ~ \mathbb { N }$ , there exists $g _ { u } ^ { L } , g _ { u } ^ { U } \ \in \ \mathbb { R }$ and $N _ { u } ~ \in ~ \mathbb { N }$ such that $\begin{array} { r } { \frac { g _ { u } ^ { L } N } { \binom { N } { u } } \ \leq \ } \end{array}$ $\begin{array} { r } { \mathrm { P r } [ \mathit { \ddot { \iota } } ^ { \mathrm { q } } \mathit { u } ] \ i s \ c o n n e c t e d ^ { \prime \prime } ] \leq \frac { g _ { \mathit { u } } ^ { U } N } { \binom { N } { \mathit { u } } } } \end{array}$ for any $N \geq N _ { u }$ .

We first show that this implies Lemma 1, and then prove Claim 2.

Proof of Lemma 1. By definition, we have $\begin{array} { r } { G _ { u } = \sum _ { S \subseteq [ N ] : | S | = u } I [ { ^ { \ast } S } } \end{array}$ is connected”], where $I | \mathcal { E } |$ is the indicator variable of event $\mathcal { E }$ . Since all subsets of size $u$ are equivalent up to some

permutation of the bits, we have

$$
\langle G _ { u } \rangle = \sum _ { S \subseteq [ N ] \colon | S | = u } { \mathrm { P r } } [ ^ { \propto } S { \mathrm { ~ i s ~ c o n n e c t e d } } ^ { \ y } ] = { \binom { N } { u } } \operatorname* { P r } [ ^ { \infty } [ u ] { \mathrm { ~ i s ~ c o n n e c t e d } } ^ { \ y } ] ,
$$

which, together with Claim 2, implies that $\left. G _ { u } \right. = \Theta ( N )$ .

Proof of Claim $\boldsymbol { \mathcal { Z } }$ . Let us start with the lower bound. For subsets $S _ { 1 } , S _ { 2 } , S _ { 3 } \subseteq \lfloor N \rfloor$ , we say that a clause $( x _ { i _ { 1 } } , x _ { i _ { 2 } } , x _ { i _ { 3 } } )$ is of type $( S _ { 1 } , S _ { 2 } , S _ { 3 } )$ if $i _ { k } \in S _ { k }$ , for $k = 1 , 2 , 3$ . Let

$$
p _ { u } = \frac { u } { N ( N - 1 ) }
$$

be the probability that a given random clause is of type $( [ u ] , \{ u + 1 \} , [ N ] )$ , and let us denote by $C o n n ( S )$ the event “ $S$ is connected”. A sufficient condition for $[ u + 1 ]$ to be connected is that for each $q \in [ u ]$ , there is exactly one clause of type $( [ q ] , \{ q + 1 \} , [ N ] )$ . Therefore, we have

$$
\begin{array} { l } { \displaystyle \operatorname* { P r } [ C o n n ( [ u + 1 ] ) ] \ge \frac { M ! } { ( M - u ) ! } ( \displaystyle \prod _ { q = 1 } ^ { u } p _ { q } ) ( 1 - \displaystyle \sum _ { q = 1 } ^ { u } p _ { q } ) ^ { M - u } } \\ { \ge \frac { M ! u ! } { ( M - u ) ! N ^ { u } ( N - 1 ) ^ { u } } \left( 1 - \frac { ( M - u ) u ( u + 1 ) } { 2 ( N - 1 ) } \right) } \\ { \ge \frac { C _ { u + 1 } N } { \binom { N } { u + 1 } } , } \end{array}
$$

where we have assumed that $N \geq \alpha u ( u + 1 ) + 1$ so that the second factor is larger than $1 / 2$ , and defined $C _ { u + 1 }$ as

$$
C _ { u + 1 } = { \binom { N } { u + 1 } } { \frac { M ! u ! } { 2 ( M - u ) ! N ^ { u + 1 } ( N - 1 ) ^ { u } } } .
$$

Note that $C _ { 2 } = \alpha / 4$ and

$$
C _ { u + 1 } = \frac { C _ { u } u ( N - u ) ( M - u + 1 ) } { ( u + 1 ) N ( N - 1 ) } \geq \frac { C _ { u } \alpha } { 8 } ,
$$

for $N \geq 2 u - 1$ and $M \geq 2 u - 2$ . Therefore, the lower bound holds with $g _ { 2 } ^ { L } ~ = ~ \alpha / 4$ , $g _ { u + 1 } ^ { L } = g _ { u } ^ { L } \alpha / 8$ and $N$ sufficiently large.

As for the upper bound, we prove it by induction on $u$ . For $u ~ = ~ 1$ , we have Pr[“[1] is connected”] $\leq 1$ so the claim holds with $g _ { 1 } ^ { U } = 1$ . Let us denote by $\cdot C l ( S _ { 1 } , S _ { 2 } , S _ { 3 } ) ^ { \rangle \rangle }$ the event that there exists at least one clause of type $( S _ { 1 } , S _ { 2 } , S _ { 3 } )$ within the $M$ clauses. Now assume that $\begin{array} { r } { \operatorname* { P r } [ C o n n ( [ u ] ) ] \leq \frac { g _ { u } ^ { U } N } { \binom { N } { u } } } \end{array}$ for some constant $g _ { u } ^ { U }$ . We need to bound the probability that $[ u + 1 ]$ is connected. If $[ u + 1 ]$ is connected, there exists some vertex $i \in [ u + 1 ]$ such that the graph obtained from $[ u + 1 ]$ by removing vertex $i$ , i.e., $[ u + 1 ] \backslash \{ i \}$ , is connected as well. Therefore

$$
\begin{array} { l } {  { \operatorname* { P r } [ C o n n ( [ u + 1 ] ) ] } } \\ & { \le 6 \sum _ { i \in [ u + 1 ] } \operatorname* { P r } [ C o n n ( [ u + 1 ] \setminus \{ i \} ) \wedge C l ( \{ i \} , [ u + 1 ] \setminus \{ i \} , [ N ] ) ] } \\ & { = 6 ( u + 1 ) \operatorname* { P r } [ C o n n ( [ u ] ) \wedge C l ( \{ u + 1 \} , [ u ] , [ N ] ) ] } \\ & { \le 6 ( u + 1 ) \operatorname* { P r } [ C o n n ( [ u ] ) \wedge C l ( \{ u + 1 \} , [ u ] , [ N ] \setminus [ u ] ) ] } \\ & { + 6 ( u + 1 ) \operatorname* { P r } [ C o n n ( [ u ] ) \wedge C l ( \{ u + 1 \} , [ u ] , [ u ] ) ] . } \end{array}
$$

For the first term, we have

$$
\begin{array} { r l } & { \operatorname* { P r } [ C o n n ( [ u ] ) \wedge C l ( \{ u + 1 \} , [ u ] , [ N ] \setminus [ u ] ) ] } \\ & { = \operatorname* { P r } [ C l ( \{ u + 1 \} , [ u ] , [ N ] \setminus [ u ] ) ] \cdot \operatorname* { P r } [ C o n n ( [ u ] ) \mid C l ( \{ u + 1 \} , [ u ] , [ N ] \setminus [ u ] ) ] } \\ & { \leq \operatorname* { P r } [ C l ( \{ u + 1 \} , [ u ] , [ N ] \setminus [ u ] ) ] \cdot \operatorname* { P r } [ C o n n ( [ u ] ) ] } \\ & { \leq M \frac { u ( N - u - 1 ) } { N ( N - 1 ) ( N - 2 ) } \cdot \operatorname* { P r } [ C o n n ( [ u ] ) ] } \\ & { \leq \frac { \alpha u } { N - 1 } \cdot \operatorname* { P r } [ C o n n ( [ u ] ) ] . } \end{array}
$$

Similarly, for the second term of Eq. (A4), we have

$$
\begin{array} { l } { \mathrm { P r } [ \mathit { C o n } ( [ u ] ) \wedge \mathit { C l } ( \{ u + 1 \} , [ u ] , [ u ] ) ] } \\ { = \mathrm { P r } [ \mathit { C l } ( \{ u + 1 \} , [ u ] , [ u ] ) ] \cdot \mathrm { P r } [ \mathit { C o n n } ( [ u ] ) \mid \mathit { C l } ( \{ u + 1 \} , [ u ] , [ u ] ) ] } \\ { \leq \mathit { M } \frac { u ( u - 1 ) } { N ( N - 1 ) ( N - 2 ) } \mathrm { P r } [ \mathit { C o n n } ( [ u ] ) \mid \mathit { C l } ( [ N ] , [ u ] , [ u ] ) ] } \\ { \leq \frac { \alpha u ( u - 1 ) } { ( N - 1 ) ( N - 2 ) } \frac { \mathrm { P r } [ \mathit { C l } ( [ N ] , [ u ] , [ u ] ) \mid \mathit { C o n n } ( [ u ] ) ] \cdot \mathrm { P r } [ \mathit { C o n n } ( [ u ] ) ] } { \mathrm { P r } [ \mathit { C l } ( [ N ] , [ u ] , [ u ] ) ] } } \\ { = \frac { \alpha u ( u - 1 ) } { ( N - 1 ) ( N - 2 ) } \frac { \mathrm { P r } [ \mathit { C o n n } ( [ u ] ) ] } { \mathrm { P r } [ \mathit { C l } ( [ N ] , [ u ] , [ u ] ) ] } . } \end{array}
$$

We need to upper bound $\operatorname* { P r } [ C l ( [ N ] , [ u ] , [ u ] ) ]$ . Let

$$
q _ { u } = \frac { u ( u - 1 ) } { N ( N - 1 ) }
$$

be the probability that a given random clause is of type $( [ N ] , [ u ] , [ u ] )$ . For $N \geq 2 \alpha u ( u - 1 ) + 1$ , we obtain

$$
\operatorname* { P r } [ C l ( [ N ] , [ u ] , [ u ] ) ] \ge M q _ { u } ( 1 - M q _ { u } ) \ge \frac { \alpha u ( u - 1 ) } { 2 ( N - 1 ) } \ge \frac { \alpha u ( u - 1 ) } { 4 ( N - 2 ) } .
$$

Therefore, the second term in Eq. (A4) satisfies

$$
\operatorname* { P r } [ C o n n ( [ u ] ) \land C l ( \{ u + 1 \} , [ u ] , [ u ] ) ] \leq \frac { 4 } { N - 1 } \cdot \operatorname* { P r } [ C o n n ( [ u ] ) ] .
$$

Putting everything together, Eq. (A4) implies

$$
\begin{array} { l } { \displaystyle \operatorname* { P r } [ C o n n ( [ u + 1 ] ) ] \le \frac { 6 ( u + 1 ) } { N - 1 } ( \alpha u + 4 ) \operatorname* { P r } [ C o n n ( [ u ] ) ] } \\ { \displaystyle \le \frac { 6 ( u + 1 ) } { N - 1 } ( \alpha u + 4 ) \frac { g _ { u } ^ { U } N } { \binom { N } { u } } } \\ { \displaystyle \le 6 g _ { u } ^ { U } ( \alpha u + 4 ) \frac { N } { \binom { N } { u + 1 } } , } \end{array}
$$

so that the upper bound holds with $g _ { 1 } ^ { U } = 1$ , $g _ { u + 1 } ^ { U } = 6 g _ { u } ^ { U } ( \alpha u + 4 )$ , and $N$ sufficiently large.

# APPENDIX B: DETAILS OF THE NUMERICAL SIMULATIONS

For each number of bits $N$ from 15 to 200 by steps of 5, we generated 5000 random instances with $M = \lfloor \alpha N \rfloor$ clauses using the following procedure.

We first picked $M - 1$ triplets of bits (the clauses) uniformly at random and with replacement, and cleaned the corresponding EC3 instance by removing absent bits, and clauses involving two bits appearing in no other clause, which introduce trivial degeneracies in the space of solutions. We then solved the cleaned EC3 instance $P$ using the Davis-Putnam-Logemann-Loveland algorithm [26, 27], to find all of its satisfying assignments (note that this step takes exponential time and therefore prevents us from considering too large instances). We added a final random clause to create a new instance $P ^ { \prime }$ , and checked which one of the solutions of $P$ satisfied the new clause, therefore being also solutions of $P ^ { \prime }$ . For each of the solutions of $P ^ { \prime }$ , we computed the fourth order correction to the energy $E _ { \mathbf { x } } ^ { ( 4 ) }$ (under Hamiltonian $H ^ { \prime } ( \lambda )$ ), and identified the solution $\mathbf { x } ^ { 1 }$ having the minimum correction, which corresponds to the ground state of $H ^ { \prime } ( \lambda )$ for $\lambda > 0$ . We then computed the correction $E _ { \mathbf { x } } ^ { ( 4 ) }$ under $H ( \lambda )$ , not only for $\mathbf { x } ^ { 1 }$ but also for all solutions of $P$ not being solutions of $P ^ { \prime }$ , in order to identify the solution $\mathbf { x } ^ { 2 }$ having the minimum correction. Finally, we calculated the 4-th order correction $E _ { 1 2 } ^ { ( 4 ) }$ of the splitting between energies of assignments $\mathbf { x } ^ { 1 }$ and $\mathbf { x } ^ { 2 }$ for the instance without the added clause $P$ . Indeed, if this splitting is large enough, this creates an avoided crossing between the ground state $| \mathbf { x } ^ { 1 } , \lambda \rangle$ and the excited state $| \mathbf { x } ^ { 2 } , \lambda \rangle$ of the Hamiltonian $H ^ { \prime } ( \lambda )$ for the instance with the added clause.

Note that if any of the previous steps failed for some reason (e.g. $P$ has no solution, or all solutions of $P$ are also solutions of $P ^ { \prime }$ ), we rejected the instance and started over with $M - 1$ new random clauses. Nevertheless, after having generated 5000 valid instances, we checked that the number of rejected instances stayed approximately constant as $N$ increases, so that our conclusions are verified with constant probability over the random instances.

The numerical simulations were run using a parallel algorithm on 2 nodes of the NECLA cloud, where each node has access to two dual-core Intel Xeon 5160 (3GHz) CPUs and 3.5GB of RAM. The full set of simulations took between 3 and 4 days to complete.

# APPENDIX C: ESTIMATION OF THE TUNNELING AMPLITUDE

The case of a tree provides an upper bound on the tunneling amplitude between two solutions of an Agree instance over $n$ bits, and as a consequence an upper bound on the tunneling amplitude between two solutions of an EC3 instance with Hamming distance $n$ . In this appendix, we will derive an estimation (rather than an upper bound) of this tunneling amplitude. Let us consider an arbitrary Agree instance over $n$ bits with $m$ clauses. Let ${ \tilde { B } } _ { i }$ be the number of clauses where bit $i$ appears, and $\tilde { J } _ { i j }$ be the number of clauses where bit $i$ and $j$ appear together (there is actually only one such clause for the Agree problem, ( $x _ { i } = x _ { j }$ ), but in general this clause could be repeated). Following the notations of Section VI C, let $E _ { j } = E _ { \mathbf { y } ^ { ( p , j ) } }$ be the energy of the bit string $\mathbf { y } ^ { ( p , j ) }$ , obtained from $\mathbf { x } ^ { 1 }$ by flipping bits $p ( 1 ) , p ( 2 ) , . . . , p ( j )$ for a given permutation $p \in S _ { n }$ , and let $\begin{array} { r } { A _ { p } = \prod _ { j = 1 } ^ { n - 1 } ( E _ { j } ) ^ { - 1 } } \end{array}$ . We need to estimate

$$
\begin{array} { l } { { \displaystyle \left| A _ { 1 2 } \right| ~ = ~ \lambda ^ { n } \sum _ { p \in S _ { n } } A _ { p } + { \cal O } ( \lambda ^ { n + 1 } ) } } \\ { { ~ = ~ \lambda ^ { n } n ! \left. A _ { p } \right. _ { p } + { \cal O } ( \lambda ^ { n + 1 } ) , } } \end{array}
$$

where the average is taken over permutations $p \in S _ { n }$ . Let us consider the approximation

$$
\begin{array} { l } { \displaystyle \big \langle A _ { p } \big \rangle _ { p } = \left. \prod _ { j = 1 } ^ { n - 1 } ( E _ { j } ) ^ { - 1 } \right. _ { p } } \\ { \approx \displaystyle \prod _ { j = 1 } ^ { n - 1 } \big \langle E _ { j } \big \rangle _ { p } ^ { - 1 } . } \end{array}
$$

We need to compute the average energy $E _ { j } ^ { ' }$ of a bit string obtained by flipping $j$ bits from a solution. When a particular bit is flipped, each clause where the bit appears will become

violated, but it will be satisfied again when the second bit in the clause is flipped, so that

$$
E _ { j } = \sum _ { k = 1 } ^ { j } \left( \tilde { B } _ { p ( k ) } - \sum _ { l = 1 } ^ { j } \tilde { J } _ { p ( k ) p ( l ) } \right) .
$$

Since, by definition, $\textstyle \sum _ { i = 1 } ^ { n } { \tilde { B } } _ { i } \ = \ 2 m$ and $\textstyle \sum _ { j = 1 } ^ { n } { \tilde { J } } _ { i j } ~ = ~ { \tilde { B } } _ { i }$ , we have $\begin{array} { r } { \left. \tilde { B } _ { p ( k ) } \right. _ { p } = \frac { 2 m } { n } } \end{array}$ and $\begin{array} { r } { \bigg \langle \tilde { J } _ { p ( k ) p ( l ) } \bigg \rangle _ { p } = \frac { 2 m } { n ( n - 1 ) } } \end{array}$ (for any $k , l \in \lfloor n \rfloor$ ), and inserting in Eq. (C3) yields

$$
\langle E _ { j } \rangle _ { p } = { \frac { 2 m j ( n - j ) } { n ( n - 1 ) } } .
$$

This shows that the average energy barrier that has to be broken to tunnel from one solution of Agree (and by reduction of EC3) to another is shaped as a parabola, see Fig. 5. We may now estimate the tunneling amplitude

$$
\begin{array} { l } { { \displaystyle | A _ { 1 2 } | ~ \approx ~ \lambda ^ { n } n ! \prod _ { j = 1 } ^ { n - 1 } \langle E _ { j } \rangle _ { p } ^ { - 1 } } } \\ { { \displaystyle ~ \approx ~ \frac { \lambda ^ { n } n } { ( n - 1 ) ! } \left( \frac { n - 1 } { 2 \beta } \right) ^ { n - 1 } , } } \end{array}
$$

where we have defined the clauses-to-variables ratio $\beta = { \frac { m } { n } }$ for the Agree instance. Using the Stirling formula $n ! \approx n ^ { n } e ^ { - n }$ , we obtain for large $n$

$$
| A _ { 1 2 } | \approx \frac { 2 \beta n } { e } \left( \frac { e \lambda } { 2 \beta } \right) ^ { n } ,
$$

which is therefore exponentially small in $n$ as soon as $\begin{array} { r } { \lambda < \lambda _ { a } \approx \frac { 2 \beta } { e } } \end{array}$ e .

Since we are more interested in EC3 than Agree, we need to estimate the typical value of $\beta$ for the Agree instances obtained by reduction from EC3 instances. Let us consider random instances of EC3 with $N$ bits and $M = \alpha N$ clauses. We have seen in Section III that the clauses forming such a random instance will typically only involve about $N _ { \mathrm { t y p } } ^ { \prime } = N ( 1 - e ^ { - 3 \alpha } )$ of the $N$ bits. Let us discard the absent bits and focus on assignments of the remaining bits satisfying all clauses, that is, the solutions of the instance. Since, for each clause of 3 bits, one of the bits has to be set to $_ 1$ and the other two to $0$ , we expect that solutions will typically involve about $\frac { N _ { \mathrm { t y p } } ^ { \prime } } { 3 }$ 1’s and 2N0typ3 0’s. Therefore, if we look at a random bit xi in a solution, we would expect that $\begin{array} { r } { \operatorname* { P r } _ { i } [ x _ { i } = 1 ] = \frac { 1 } { 3 } } \end{array}$ . Let us now consider the joint distribution $p _ { b ^ { 1 } b ^ { 2 } } = \mathrm { P r } _ { i } [ ( x _ { i } ^ { 1 } , x _ { i } ^ { 2 } ) = ( b ^ { 1 } , b ^ { 2 } ) ]$ for two solutions $\mathbf { x } ^ { 1 } , \mathbf { x } ^ { 2 }$ . For instances with large $N$ and $\alpha$ close to the satisfiablity threshold, the solutions will be essentially independent, so we can expect $p _ { b ^ { 1 } b ^ { 2 } } = \mathrm { P r } _ { i } [ x _ { i } ^ { 1 } = b ^ { 1 } ] \cdot \mathrm { P r } _ { i } [ x _ { i } ^ { 2 } = b ^ { 2 } ]$ , that is, $\begin{array} { r } { p _ { 0 0 } = \frac { 4 } { 9 } } \end{array}$ , $\begin{array} { r } { p _ { 0 1 } = p _ { 1 0 } = \frac { 2 } { 9 } } \end{array}$ and $\textstyle p _ { 1 1 } = { \frac { 1 } { 9 } }$ . From there, we can estimate the typical Hamming distance between two solutions of a random EC3 instance, $\begin{array} { r } { n _ { \mathrm { t y p } } = N _ { \mathrm { t y p } } ^ { \prime } ( p _ { 0 1 } + p _ { 1 0 } ) = \frac { 4 N _ { \mathrm { t y p } } ^ { \prime } } { 9 } } \end{array}$

![](images/11fd03f315648e6446d7a243413cb9d2fa2b863bf39d197bb01e2f8afe24a4de.jpg)  
FIG. 5: Average energy barrier for random paths between the two solutions of an instance of Agree with $n = 2 0$ bits and $m = 2 0$ clauses. $\langle E _ { j } \rangle _ { p }$ gives the average energy after flipping $j$ bits from one of the solutions.

Out of the $M$ clauses, we now need to estimate the number of relevant clauses, that is those involving bits that differ in the two solutions, since these are the clauses corresponding to agree clauses in the Agree instance obtained by reduction. Let us consider the set of all clauses satisfied by the two solutions, and assume that we sample $M$ clauses uniformly at random from this set. We say that a bit $x _ { i }$ is of type $b ^ { 1 } b ^ { 2 }$ when $( x _ { i } ^ { 1 } , x _ { i } ^ { 2 } ) \ = \ ( b ^ { 1 } , b ^ { 2 } )$ . A relevant clause involves one 00-type bit, one 01-type bit and one 10-type bit. Therefore, there are typically about $M _ { \mathrm { r e l } } = 6 p _ { 0 0 } p _ { 0 1 } p _ { 1 0 } ( N _ { \mathrm { t y p } } ^ { \prime } ) ^ { 3 }$ possible relevant clauses. Similarly, an irrelevant clause involves one 11-type bit and two 00-type bits, so there are typically about $M _ { \mathrm { i r r } } = 3 p _ { 1 1 } p _ { 0 0 } ^ { 2 } ( N _ { \mathrm { t y p } } ^ { \prime } ) ^ { 3 }$ irrelevant clauses. A random clause satisfied by the two solutions will therefore be relevant with probability MrelMrel+Mirr . As a consequence, when picking $M$ random clauses, there will typically be around $\begin{array} { r } { m _ { \mathrm { t y p } } = { \frac { 2 M } { 3 } } } \end{array}$ relevant clauses. Finally, the typical clauses-to-variables ratio for the Agree instance obtained by reduction may be estimated as $\begin{array} { r } { \beta _ { \mathrm { t y p } } = \frac { m _ { \mathrm { t y p } } } { n _ { \mathrm { t y p } } } = \frac { 3 } { 2 } \alpha \frac { e ^ { 3 \alpha } } { e ^ { 3 \alpha } - 1 } } \end{array}$ . Back to our original concern about the tunneling amplitude, we see that it will be exponentially small for $\lambda < \lambda _ { a }$ , where

$$
\lambda _ { a } \approx \frac { 2 \beta _ { \mathrm { t y p } } } { e } = \frac { 3 \alpha e ^ { 3 \alpha - 1 } } { e ^ { 3 \alpha } - 1 } .
$$

For $\alpha = 0 . 6 2$ (the value we used in our numerical simulations), we obtain $\lambda _ { a } \approx 0 . 8 1$ .

# APPENDIX D: LOWER BOUND ON THE MINIMUM GAP

Lemma 6 ([12]). Let $H ( s ) = ( 1 - s ) H _ { 0 } + s H _ { P }$ be a Hamiltonian on $N$ qubits where $H _ { 0 } =$ $- \textstyle \sum _ { i = 1 } ^ { N } \sigma _ { x } ^ { ( i ) }$ , and $\begin{array} { r } { H _ { P } = \sum _ { \mathbf { x } \in \{ 0 , 1 \} ^ { N } } E _ { \mathbf { x } } | \mathbf { x } \rangle \langle \mathbf { x } | } \end{array}$ with $E _ { \mathbf { x } ^ { 0 } } = 0$ for some $\mathbf { x } ^ { 0 } \in \{ 0 , 1 \} ^ { N }$ and $1 \leq$ $E _ { \mathbf { x } } \leq M = O ( N )$ for all $\mathbf { x } \neq \mathbf { x } ^ { 0 }$ . Then, the eigenvalue gap of $H ( s )$ satisfies $\Delta ( s ) \geq$ $2 ^ { - O ( N \log N ) }$ for all $0 \leq s \leq 1$ .

Proof. Let us first consider the case s ≥ 2N+12N+2 . Note that the diagonal elements of $H ( s )$ are given by $H _ { \mathbf { x } \mathbf { x } } = s E _ { \mathbf { x } }$ , and the non-diagonal elements satisfy $\begin{array} { r } { \sum _ { \mathbf { y } \neq \mathbf { x } } H _ { \mathbf { x } \mathbf { y } } = - ( 1 - s ) N } \end{array}$ . Therefore, all Gershgorin circles have radius $( 1 - s ) N$ and the circle around $H _ { \mathbf { x } ^ { 0 } \mathbf { x } ^ { 0 } } = 0$ is disjoint from the circles around $H _ { \mathbf { x x } } \geq s$ (for $\mathbf { x } \neq \mathbf { x } ^ { 0 }$ ) as soon as $( 1 - s ) N < s - ( 1 - s ) N$ , that is, $\begin{array} { r } { s > \frac { 2 N } { 2 N + 2 } } \end{array}$ . In that case, the smallest eigenvalue lies in the circle around $H _ { \mathbf { x } ^ { 0 } \mathbf { x } ^ { 0 } } = 0$ , and all others in the union of the other circles, so that we have for the eigenvalue gap $\begin{array} { r } { \Delta ( s ) = E _ { 1 } ( s ) - E _ { 0 } ( s ) \geq s - 2 ( 1 - s ) N \geq \frac { 1 } { 2 N + 2 } \geq \Omega \big ( \frac { 1 } { N } \big ) } \end{array}$ for $\begin{array} { r } { s \ge \frac { 2 N + 1 } { 2 N + 2 } } \end{array}$ .

Let us now consider the case $\begin{array} { r } { s \le \frac { 2 N + 1 } { 2 N + 2 } } \end{array}$ . Let $\begin{array} { r } { Q = \frac { - H ( s ) + s M \mathbf { 1 } } { 1 - s } = A + \lambda ( M \mathbf { 1 } - H _ { P } ) } \end{array}$ , where $A = - H _ { 0 }$ is the adjacency matrix of the hypercube and $\textstyle \lambda = { \frac { s } { 1 - s } }$ . Note that since $E _ { \mathbf { x } } \leq M$ , all elements of this matrix are non-negative. By the mixing properties of the hypercube, all elements of $A ^ { N }$ are at least 1, and therefore this is also true for $Q ^ { N }$ . This implies that the gap between the largest and second largest eigenvalue of $Q ^ { N }$ is at least 1, that is, $\mu _ { 0 } ^ { N } - \mu _ { 1 } ^ { N } \geq 1$ , where $\mu _ { 0 }$ and $\mu _ { 1 }$ are the largest and second largest eigenvalue of $Q$ . The eigenvalues $\mu _ { i }$ of $Q$ are upper-bounded by the spectral radius $\rho ( Q )$ , which in term is upper bounded by the norm $\begin{array} { r } { | | Q | | _ { 1 } = \operatorname* { m a x } _ { \mathbf { x } } \sum _ { \mathbf { y } } | Q _ { \mathbf { x } \mathbf { y } } | } \end{array}$ , so that $\mu _ { i } \leq \lambda M + N$ for all $i$ . Moreover, we have $\mu _ { 0 } ^ { N } - \mu _ { 1 } ^ { N } \leq ( \mu _ { 0 } - \mu _ { 1 } ) ( \mu _ { 0 } + \mu _ { 1 } ) ^ { N - 1 }$ , so that

$$
\mu _ { 0 } - \mu _ { 1 } \geq \frac 1 { ( \mu _ { 0 } + \mu _ { 1 } ) ^ { N - 1 } } \geq \frac 1 { ( 2 \lambda M + 2 N ) ^ { N - 1 } } \geq \frac 1 { ( 4 M N + 2 M + 2 N ) ^ { N - 1 } } ,
$$

where we used the fact that $\lambda \le 2 N + 1$ when $\begin{array} { r } { s \le \frac { 2 N + 1 } { 2 N + 2 } } \end{array}$ 2N+1 . Finally, we have

$$
\Delta ( s ) = ( 1 - s ) ( \mu _ { 0 } - \mu _ { 1 } ) \geq { \frac { 1 } { ( 2 N + 2 ) ( 4 M N + 2 M + 2 N ) ^ { N - 1 } } } \geq 2 ^ { - O ( N \log N ) } .
$$