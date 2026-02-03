# On the adiabatic condition and the quantum hitting time of Markov chains

Hari Krovi,1, ∗ Maris Ozols, $1 , 2 , \dag$ and J´er´emie Roland $^ { 1 }$ , $^ \ddag$ $\mathit { 1 }$ NEC Laboratories America, Inc.

$\boldsymbol { \mathcal { Z } }$ University of Waterloo and Institute for Quantum Computing

Abstract

We present an adiabatic quantum algorithm for the abstract problem of searching marked vertices in a graph, or spatial search. Given a random walk (or Markov chain) $P$ on a graph with a set of unknown marked vertices, one can define a related absorbing walk $P ^ { \prime }$ where outgoing transitions from marked vertices are replaced by self-loops. We build a Hamiltonian $H ( s )$ from the interpolated Markov chain $P ( s ) = ( 1 - s ) P + s P ^ { \prime }$ and use it in an adiabatic quantum algorithm to drive an initial superposition over all vertices to a superposition over marked vertices. The adiabatic condition implies that for any reversible Markov chain and any set of marked vertices, the running time of the adiabatic algorithm is given by the square root of the classical hitting time. This algorithm therefore demonstrates a novel connection between the adiabatic condition and the classical notion of hitting time of a random walk. It also significantly extends the scope of previous quantum algorithms for this problem, which could only obtain a full quadratic speed-up for state-transitive reversible Markov chains with a unique marked vertex.

# Introduction

Adiabatic quantum computation was introduced by Farhi et al. in [1]. It proceeds as follows. Suppose that the solution of a computational problem can be encoded in the ground state of a problem Hamiltonian $H _ { P }$ . We start in the ground state of an initial Hamiltonian $H _ { 0 }$ which is easy to construct. Then we slowly change the Hamiltonian from $H _ { 0 }$ to $H _ { P }$ , so that the instantaneous Hamiltonian at any point in the evolution is $H ( s ) = ( 1 - s ) H _ { 0 } + s H _ { P }$ , where $0 \leq s \leq 1$ . If this is done slowly enough, then the Adiabatic Theorem of Quantum Mechanics [2] guarantees that the state at all points in the evolution stays close to the ground state of $H ( s )$ . Note that the validity of the folk version of the Adiabatic Theorem, as stated in many books of Quantum Mechanics such as [2], has recently been the subject of much debate [3–6], and there is no rigorous proof of it that holds under full generality. It is nevertheless possible to state a more rigorous version of the theorem, so that the folk adiabatic condition can be proved to be sufficient in many interesting cases [7], such as the adiabatic version of Grover’s algorithm [8–10].

Many classical randomized algorithms rely heavily on random walks or Markov chains. The notion of hitting time is a useful characterization of Markov chains used when searching for a marked vertex. Quantum walks are natural generalizations of classical random walks. The notion of hitting time has been carried over to the quantum case in [11–17], by generalizing the classical notion in different ways. It is intimately related to the problem of spatial search. Suppose that we are given a graph where some vertices are marked. Classically, a simple algorithm to find a marked vertex is to repeatedly apply some random walk $P$ on the graph until one of the marked vertices is reached. The hitting time of $P$ is precisely the expected number of repetitions necessary to reach a marked vertex, starting from the stationary distribution of $P$ . The notions of quantum hitting time are based on different quantum analogues of this algorithm. They usually show some quadratic improvement of the quantum hitting time over the classical hitting time. However, until the present paper, they could only show such a relation under restricted conditions: either the quantum algorithm could only detect marked elements [13], or it could only be applied to state-transitive reversible Markov chains with a unique marked element [16]. Whether this quadratic speed-up for finding a marked element also holds for any reversible Markov chain and for multiple marked elements was an open question. In this paper, we answer this question by the positive, by providing an adiabatic quantum algorithm for this problem. In addition to being more general, the algorithm is also conceptually very clean, it implements a simple rotation in a two dimensional subspace based on a quantum walk on the edges of the graph. Moreover, it reveals a close connection between the adiabatic condition and the notion of hitting time.

The paper is structured as follows. In Section I we describe related work and in Section II we state our main result. In Section III we introduce the necessary concepts such as Markov chains, the discriminant matrix, and the quantization of Markov chains. In Section IV we evaluate the spectrum of the interpolating Hamiltonian and in Section V we impose the adiabatic condition to calculate the running time of the adiabatic quantum algorithm. In Section VI we relate this to the hitting time of the Markov chain we started from, and show that the running time of the adiabatic evolution is at most the square root of the classical hitting time.

# I. RELATED WORK

Inspired by Ambainis’ quantum walk algorithm for Element Distinctness [18], Szegedy [13] introduced a powerful way of quantizing Markov chains which led to new quantum walkbased algorithms. He showed that for any symmetric Markov chain a quantum walk could detect the presence of marked vertices in at most the square root of the classical hitting time. However, showing that a marked vertex could also be found in the same time (as is the case for the classical algorithm) proved to be a very difficult task. Magniez et al. [15] extended Szegedy’s approach to the larger class of ergodic Markov chains, and proposed a quantum walk-based algorithm to find a marked vertex, but its complexity may be larger than the square root of the classical hitting time. A typical example where their approach fails to provide a quadratic speed-up is the 2D grid, where their algorithm has complexity $\Theta ( n )$ , whereas the classical hitting time is $\Theta ( n \log n )$ . Ambainis et al. [11] and Szegedy’s [13] approaches yield a complexity of $\Theta ( { \sqrt { n } } \cdot \log n )$ in this special case, for a unique marked vertex. Childs and Goldstone [19, 20] also obtained a similar result using a continuous-time quantum walk. However, whether a full quadratic speed-up was possible remained an open question, until Tulsi [21] proposed a solution involving a new technique. Magniez et al. [16] extended Tulsi’s technique to any reversible state-transitive Markov chain, showing that for such chains, it is possible to find a unique marked vertex with a full quadratic speed-up over the classical hitting time. However, the state-transitivity is a strong symmetry condition, and furthermore their technique cannot deal with multiple marked vertices. It would be strange if one had to rely on involved techniques to solve the finding problem under such restricted conditions, while the classical analogue algorithm is conceptually very simple and works under very general conditions.

In this paper we show that these issues can be resolved by combining the idea of the quantization of Markov chains with adiabatic quantum computation (note that Childs and Goldstone [19, 20] showed that their algorithm for spatial search on the grid could also be translated into an adiabatic algorithm, but this failed to give a quadratic speed-up for low dimensions).

# II. MAIN RESULT

Before describing our quantum algorithm, let us first recall the classical algorithm on which it will provide a quadratic speed-up. This very simple algorithm just consists in walking randomly on the graph until a marked vertex is reached. More precisely, it relies on a Markov chain $P$ with stationary distribution $\pi$ , and works as follows.

# Random Walk Algorithm

1. Sample a vertex $x \in X$ according to distribution $\pi$ .   
2. Check if $x$ is marked.   
3. If so, output $x$ .   
4. Otherwise, update $x$ according to $P$ , and go back to step 2.

Let $P$ be an ergodic Markov chain, and $M$ be a set of marked vertices. The hitting time of $P$ with respect to $M$ , denoted by H $\Gamma ( P , M )$ , is the expected number of executions of step 4 during the course of the Random Walk Algorithm (where the expectation is calculated conditionally on the initial vertex being unmarked). Note that since the algorithm stops as soon as a marked element is reached, this is equivalent to using an absorbing Markov chain $P ^ { \prime }$ , which acts as $P$ on all but marked vertices, where all outgoing transitions are replaced by self-loops.

Previous attempts at providing a quantum speed-up over this classical algorithm have followed one of these two approaches:

• Combining a quantum version of $P$ with a reflection through marked vertices to mimic a Grover operation [11, 15, 18].   
• Directly applying a quantum version of $P ^ { \prime }$ [13, 16].

The problem with these approaches is that they would only be able to find marked vertices in very restricted cases. We explain this by the different nature of random and quantum walks: while both accept a stable state, i.e., the stationary distribution for the random walk and the eigenstate with eigenvalue 1 for the quantum walk, the way both walks act on other states is dramatically different. Indeed, an ergodic random walk will converge to its stationary distribution from any initial distribution. This apparent robustness may be attributed to the inherent randomness of the walk, which will smooth out any initial perturbation. After many iterations of the walk, non-stationary contributions of the initial distribution will be damped and only the stationary distribution will survive (this can be attributed to the thermodynamical irreversibility [26] of ergodic random walks). On the other hand, this is not true for quantum walks, because in the absence of measurements a unitary evolution is deterministic (and in particular thermodynamically reversible): the contributions of the other eigenstates will not be damped but just oscillate with different frequencies, so that the overall evolution is quasi-periodic. As a consequence, while iterations of $P ^ { \prime }$ always lead to a marked vertex, it may happen that iterations of the quantization of $P ^ { \prime }$ will never lead to a state with a large overlap over marked vertices, unless the walk exhibits a strong symmetry (as is the case for a state-transitive walk with only one marked element, which could be addressed by previous approaches).

The main new idea of our approach is that, instead of using a quantization of $P$ or $P ^ { \prime }$ , we first modify the classical random walk, and then use a quantization of the modified walk. The original classical algorithm consists in applying $P ^ { \prime }$ on the stationary distribution $\pi$ of $P$ . While doing so, the system is brought far from equilibrium since $\pi$ is far (in statistical distance) from any stationary distribution of $P ^ { \prime }$ , which only have support on marked elements. The random walk will damp any non-stationary contribution of the initial distribution, but a quantum walk based on $P$ or $P ^ { \prime }$ , which is deterministic until a measurement, seems to have trouble with it. There is however a situation in Quantum Mechanics where contributions from other eigenstates will also cancel out, similarly to what happens for a random walk: if the system starts in a state close to the ground state of its instantaneous Hamiltonian $H ( s )$ (i.e., close to equilibrium), and this Hamiltonian varies slowly, the Adiabatic Theorem ensures that the contributions from excited states will cancel out so that the system will remain close to its ground state. Therefore, our strategy is to first modify the classical algorithm so that the system stays close to equilibrium throughout the evolution, and then to translate it into an adiabatic quantum algorithm.

Consider the interpolated Markov chain $P ( s ) = ( 1 - s ) P + s P ^ { \prime }$ (see Section III A). Our goal is to drive the stationary distribution $\pi$ of $P$ towards a stationary distribution of $P ^ { \prime }$ . Instead of immediately applying $P ^ { \prime }$ on $\pi$ , we could rather apply $P ( s )$ while slowly switching $s$ from $0$ to $1$ , so that the system remains at all time close to the stationary distribution $\pi ( s )$ of $P ( s )$ . It can be shown that this leads to an algorithm with only a constant overhead with respect to Random Walk Algorithm. Therefore, this new classical algorithm still runs in time $O ( \mathrm { H T } ( P , M ) )$ , but the difference is that at all time the system is close to equilibrium, so that we are in a better shape for designing a quantum analogue based on the Adiabatic Theorem.

Using a Hamiltonian version of Szegedy’s quantization technique, proposed by Somma and Ortiz [22], we map $P ( s )$ to a Hamiltonian $H ( s )$ on the edge space $\mathcal { H } \otimes \mathcal { H }$ , where $\mathcal { H }$ is the Hilbert space whose basis states are labeled by the vertices of the graph (see Section III D). The eigenstate of $H ( s )$ with eigenvalue 0 then corresponds to the stationary distribution of $P$ for $s = 0$ , and to a distribution over marked vertices for $s = 1$ , so that this Hamiltonian may be used to solve the search problem by adiabatic evolution. The algorithm consists in preparing the first register in the state $| \pi \rangle$ corresponding to the stationary distribution $\pi$ of $P$ and applying the Hamiltonian $H ( s )$ using a schedule $s ( t )$ (we will specify $s ( t )$ explicitly later). The resulting adiabatic evolution effectively implements a rotation on the first register at constant angular velocity from $| \pi \rangle$ to a superposition over marked vertices.

# Adiabatic Search Algorithm

1. Prepare the state $| \pi \rangle | 0 \rangle$ . 2. Apply the time-dependent Hamiltonian $H ( s )$ with schedule $s ( t )$ from $t = 0$ to $t = x$ , where $\begin{array} { r } { T = \frac { \pi } { 2 \varepsilon } \sqrt { \mathrm { H T } ( P , M ) } } \end{array}$ . 3. Measure the first register in the vertex basis.

Under the assumption that the folk adiabatic condition holds in our setup, we prove the following:

Theorem 1. For any ergodic and reversible Markov chain $P$ with a set of marked vertices $M$ , the Adiabatic Search Algorithm finds a marked vertex with probability at least $1 - \varepsilon ^ { 2 }$ in a time $\begin{array} { r } { T = \frac { \pi } { 2 \varepsilon } \sqrt { \mathrm { H T } ( P , M ) } } \end{array}$ , where HT $( P , M )$ is the hitting time of the classical Markov chain $P$ with respect to the set of marked vertices $M$ .

This theorem constitutes our main result and the body of this paper will be devoted to its proof. While it relies on the folk adiabatic condition, a similar statement can be made for a related quantum circuit algorithm, where no such condition is necessary, as shown in [23]. Nevertheless, as explained in [23], the intuition behind the quantum circuit algorithm originates from the present adiabatic quantum algorithm.

# III. PRELIMINARIES

# A. Classical interpolation

Let us consider a Markov chain on a discrete state space $X$ of size $n$ , and let $P$ be the $n \times n$ (row) stochastic matrix [27] describing the transition probabilities of the Markov chain. From now on, we will assume that the Markov chain is ergodic, meaning that it is both irreducible (any state can be reached from any other state by a finite number of steps) and aperiodic (there is no integer $k > 1$ that divides the length of every cycle of the underlying directed graph of the stochastic matrix $P$ ). Assume that a subset $M \subset X$ of elements are marked and let $m$ be the size of $M$ . Let $P ^ { \prime }$ be the Markov chain obtained from $P$ by turning all outgoing transitions from marked elements into self-loops. We call $P ^ { \prime }$ the absorbing version of $P$ . Note that $P ^ { \prime }$ differs from $P$ only in the rows corresponding to the marked elements (where it contains all zeros on non-diagonal elements, and ones on the diagonal). If we arrange the elements of $X$ so that the marked elements are the last ones, matrices $P$ and $P ^ { \prime }$ have the following block structure:

$$
P : = \left( { \begin{array} { l l l l } { P _ { U U } } & { P _ { U M } } \\ { P _ { M U } } & { P _ { M M } } \end{array} } \right) , \qquad P ^ { \prime } : = \left( { \begin{array} { l l l l } { P _ { U U } } & { P _ { U M } } \\ { 0 } & { I } \end{array} } \right) ,
$$

where $P _ { U U }$ and $P _ { M M }$ are square matrices of size $( n - m ) \times ( n - m )$ and $m \times m$ , respectively, while $P _ { U M }$ and $P _ { M U }$ are matrices of size $( n - m ) \times m$ and $m \times ( n - m )$ , respectively. We call

$$
P ( s ) : = ( 1 - s ) P + s P ^ { \prime } , \quad 0 \leq s \leq 1 ,
$$

the classical interpolation of $P$ and $P ^ { \prime }$ . Note that $P ( 0 ) = P$ , $P ( 1 ) = P ^ { \prime }$ , and $P ( s )$ has block structure

$$
P ( s ) = \left( \begin{array} { c c } { { P _ { U U } } } & { { P _ { U M } } } \\ { { ( 1 - s ) P _ { M U } } } & { { ( 1 - s ) P _ { M M } + s I } } \end{array} \right) .
$$

Moreover, note that the ergodicity of $P$ implies that $P ( s )$ is also ergodic, except for $s = 1$

# B. Stationary distribution and reversibility

By definition, since $P$ is ergodic, it has a unique and non-vanishing stationary distribution, i.e., a probability distribution $\pi$ such that $\pi P = \pi$ . An ergodic Markov chain $P$ is called reversible if it satisfies the so-called detailed balance condition

$$
\forall x , y \in X : \pi _ { x } P _ { x y } = \pi _ { y } P _ { y x } .
$$

This implies that for reversible Markov chains, the net flow of probability in the stationary distribution between every pair of states is zero.

From now on we will assume that $P$ is reversible. Let us argue that $P ( s )$ is also reversible. Let $\pi : = \left( \pi _ { U } \ \pi _ { M } \right)$ be the stationary distribution of $P$ , where $\pi _ { U }$ and $\pi _ { M }$ are row vectors of length $n - m$ and $m$ , respectively. Let $\begin{array} { r } { p _ { M } = \sum _ { x \in M } \pi _ { x } } \end{array}$ be the probability to pick a marked element from the stationary distribution and $\pi ( s )$ be the following distribution:

$$
\pi ( s ) : = \frac { 1 } { 1 - s ( 1 - p _ { M } ) } \left( ( 1 - s ) \pi _ { U } \pi _ { M } \right) .
$$

One can check that $\pi ( s )$ is a stationary distribution for $P ( s )$ for any $s \in \lbrack 0 , 1 \rbrack$ . Moreover, for $s \in [ 0 , 1 ) ~ P ( s )$ is ergodic and this is therefore the unique stationary distribution, while for $s = 1$ any distribution which only has support on marked vertices is stationary. Equation (4) can be used to show that

$$
\forall s \in [ 0 , 1 ] , \forall x , y \in X : \pi _ { x } ( s ) P _ { x y } ( s ) = \pi _ { y } ( s ) P _ { y x } ( s ) ,
$$

which means that $P ( s )$ is reversible for $s \in [ 0 , 1 )$ . Condition (6) is also satisfied at $s = 1$ , but $P ( 1 ) = P ^ { \prime }$ is not ergodic, therefore stricto sensu $P ( 1 )$ is not reversible.

# C. Discriminant matrix

The discriminant matrix of a Markov chain $P ( s )$ is

$$
D ( s ) : = { \sqrt { P ( s ) } } \circ P ( s ) ^ { \intercal } ,
$$

where the Hadamard product “ $\circ ^ { \mathfrak { N } }$ and the square root is computed entry-wise. We prefer to work with $D ( s )$ rather than $P ( s )$ since a Markov chain is not necessarily symmetric while its discriminant matrix is.

For a reversible Markov chain, the extended detailed balance condition (6) implies that $D _ { x y } ( s ) = \sqrt { P _ { x y } ( s ) P _ { y x } ( s ) } = P _ { x y } ( s ) \sqrt { \pi _ { x } ( s ) / \pi _ { y } ( s ) }$ or equivalently

$$
D ( s ) = \mathrm { d i a g } \big ( \sqrt { \pi ( s ) } \big ) { \cal P } ( s ) \mathrm { d i a g } \big ( \sqrt { \pi ( s ) } \big ) ^ { - 1 } .
$$

For $s \in [ 0 , 1 )$ the right-hand side is well-defined so that $D ( s )$ and $P ( s )$ are similar and therefore have the same eigenvalues. Moreover, the entry-wise square root of the stationary distribution $\sqrt { \pi ( s ) ^ { \intercal } }$ is the eigenvector of $D ( s )$ with eigenvalue 1.

At $s = 1$ the right-hand side of equation (8) is not well-defined, but it can be shown that both claims still hold by expanding $P ( s )$ according to equation (3) and considering the limit $s \to 1$ . Then equation (8) becomes

$$
D ( 1 ) = \left( \begin{array} { c c } { { \mathrm { d i a g } \left( \sqrt { \pi _ { U } } \right) P _ { U U } \mathrm { \ d i a g } \left( \sqrt { \pi _ { U } } \right) ^ { - 1 } 0 } } \\ { { 0 } } & { { I } } \end{array} \right) .
$$

This implies that $D ( 1 )$ is similar to $\tilde { P } : = \left( \begin{array} { c c } { P _ { U U } } & { 0 } \\ { 0 } & { I } \end{array} \right)$ , and in turn to $P ( 1 ) = \left( \begin{array} { c c } { { P _ { U U } \ P _ { U M } } } \\ { { 0 } } \end{array} \right)$ as well. To see that $\sqrt { \pi ( 1 ) ^ { \top } }$ is an eigenvector of $D ( 1 )$ with eigenvalue 1, note that $\pi ( 1 ) = ( 0 { \mathrm { \ } } \pi _ { M } ) / p _ { M }$ , and $D ( 1 )$ acts as the identity on marked elements (this follows from equations (5) and (9), respectively).

# D. The quantum Hamiltonian

Szegedy [13] proposed a general method to map a random walk to a unitary operator that defines a quantum walk. Recently Somma and Ortiz [22] showed how Szegedy’s method may be adapted to build a Hamiltonian. We apply this method to the random walk $P ( s )$ .

The first step is to map the rows of $P ( s )$ to quantum states. Let $\mathcal { H }$ be a Hilbert space of dimension $n = | X |$ . For every $x \in X$ we define the following state in $\mathcal { H }$ :

$$
| p _ { x } ( s ) \rangle : = \sum _ { y \in X } { \sqrt { P _ { x y } ( s ) } } | y \rangle .
$$

Following Szegedy [13], we then define a unitary operator $V ( s )$ acting on $\mathcal { H } \otimes \mathcal { H }$ a s

$$
V ( s ) | x , 0 \rangle : = | x \rangle | p _ { x } ( s ) \rangle = \sum _ { y \in X } { \sqrt { P _ { x y } ( s ) } } | x , y \rangle ,
$$

when the second register is in some reference state $| 0 \rangle \in { \mathcal { H } }$ , and arbitrarily otherwise.

Let $S$ be the gate that swaps both registers. When restricted to $| 0 \rangle$ in the second register, the operator $V ^ { \dagger } ( s ) S V ( s )$ acts as $D ( s )$ :

$$
\langle x , 0 | V ^ { \dagger } ( s ) S V ( s ) | y , 0 \rangle = \langle x | p _ { y } ( s ) \rangle \langle p _ { x } ( s ) | y \rangle = \sqrt { P _ { x y } ( s ) P _ { y x } ( s ) } = D _ { x y } ( s ) .
$$

Following [22], we now define the Hamiltonian $H ( s )$ on $\mathcal { H } \otimes \mathcal { H }$ a s

$$
H ( s ) : = i \big [ V ^ { \dagger } ( s ) { S V } ( s ) , \Pi _ { 0 } \big ] ,
$$

where $\Pi _ { 0 } : = I \otimes | 0 \rangle \langle 0 |$ is the projector that keeps only the component containing the reference state $| 0 \rangle$ in the second register and $[ A , B ] : = A B - B A$ is the commutator.

# IV. SPECTRAL DECOMPOSITION OF $H ( s )$

To understand the properties of the Hamiltonian $H ( s )$ , let us find its spectral decomposition. We will relate its spectrum to that of $D ( s )$ .

# A. Diagonalization of $D ( s )$

Recall from equation (7) that $D ( s )$ is real and symmetric. Therefore, its eigenvalues are real and its eigenvectors form an orthonormal basis of $\mathcal { H }$ with real amplitudes. Let

$$
D ( s ) = \sum _ { i = 1 } ^ { n } \lambda _ { i } ( s ) | v _ { i } ( s ) \rangle \langle v _ { i } ( s ) |
$$

be the spectral decomposition of $D ( s )$ . We can make the eigenvalues of $P ( s )$ and hence also of $D ( s )$ to be non-negative by replacing $P$ with $( P + I ) / 2$ . Note that this will only modify

the hitting time of the Markov chain by a factor of 2. Hence, from now on without loss of generality we assume that all eigenvalues of $D ( s )$ are non-negative. In addition, we can arrange them so that

$$
0 \leq \lambda _ { 1 } ( s ) \leq \lambda _ { 2 } ( s ) \leq \cdot \cdot \cdot \leq \lambda _ { n } ( s ) .
$$

From the Perron–Frobenius theorem we have that $\forall i ~ : ~ \lambda _ { i } ( s ) \ \leq ~ 1$ and $\lambda _ { n } ( s ) = 1$ . In addition, for any $s \in [ 0 , 1 )$ the Markov chain $P ( s )$ is ergodic and $\forall i \neq n : \lambda _ { i } ( s ) < 1$ . On the other hand, at $s = 1$ the Markov chain is not ergodic and has eigenvalue 1 with multiplicity $m$ . We may summarize this as follows:

$$
\begin{array} { c c } { { \lambda _ { n - 1 } ( s ) < \lambda _ { n } ( s ) = 1 , } } & { { \forall s \in [ 0 , 1 ) , } } \\ { { } } & { { } } \\ { { \lambda _ { n - m } ( 1 ) < \lambda _ { n - m + 1 } ( 1 ) = \cdot \cdot \cdot = \lambda _ { n } ( 1 ) = 1 . } } & { { } } \end{array}
$$

Recall from Section III C that $\sqrt { \pi ( s ) ^ { \top } }$ is an eigenvector of $D ( s )$ with eigenvalue 1 for any $s \in [ 0 , 1 ]$ , so let us choose $| v _ { n } ( s ) \rangle$ in equation (14) as

$$
| v _ { n } ( s ) \rangle : = { \sqrt { \pi ( s ) ^ { \mathsf { T } } } } .
$$

# B. Diagonalization of $H ( s )$

Now, let us express the eigenvalues and eigenvectors of $H ( s )$ in terms of those of $D ( s )$ . First, let us break up the Hilbert space $\mathcal { H } \otimes \mathcal { H }$ into mutually orthogonal subspaces that are invariant under $H ( s )$ . Let

$$
\begin{array} { r } { \mathcal { B } _ { k } ( s ) : = \mathrm { s p a n } \left\{ | v _ { k } ( s ) , 0 \rangle , V ^ { \dagger } ( s ) S V ( s ) | v _ { k } ( s ) , 0 \rangle \right\} , \forall k \ne n , } \end{array}
$$

Note that $\langle v _ { k } ( s ) , 0 | V ^ { \dagger } ( s ) S V ( s ) | v _ { k } ( s ) , 0 \rangle = \langle v _ { k } ( s ) | D ( s ) | v _ { k } ( s ) \rangle = \lambda _ { k } ( s )$ by equations (12) and (14). Recall that for $s < 1$ , we have $\lambda _ { k } ( s ) \neq 1$ for any $k \neq n$ and thus

$$
V ^ { \dagger } ( s ) S V ( s ) | v _ { k } ( s ) , 0 \rangle = \lambda _ { k } ( s ) | v _ { k } ( s ) , 0 \rangle + \sqrt { 1 - \lambda _ { k } ( s ) ^ { 2 } } | v _ { k } ( s ) , 0 \rangle ^ { \bot }
$$

for some [28] unit vector $| v _ { k } ( s ) , 0 \rangle ^ { \perp }$ orthogonal to $| v _ { k } ( s ) , 0 \rangle$ and lying in the subspace $\boldsymbol { B } _ { k } ( \boldsymbol { s } )$ .   
We also define by continuity $\begin{array} { r } { | v _ { k } ( 1 ) , 0 \rangle ^ { \perp } : = \operatorname* { l i m } _ { s \to 1 } | v _ { k } ( s ) , 0 \rangle ^ { \perp } } \end{array}$ .

Following Somma and Ortiz, who were in turn relying on Szegedy’s work, we may now characterize the spectrum of $H ( s )$ .

Lemma 1 ([13, 22]). $H ( s )$ accepts the following eigenvalues and eigenstates.

• On $\boldsymbol { B } _ { k } ( \boldsymbol { s } )$ , $\forall k \neq n$ :

$$
E _ { k } ^ { \pm } ( s ) : = \pm \sqrt { 1 - \lambda _ { k } ( s ) ^ { 2 } } , \quad | \Psi _ { k } ^ { \pm } ( s ) \rangle : = \frac { | v _ { k } ( s ) , 0 \rangle \pm | v _ { k } ( s ) , 0 \rangle ^ { \perp } } { \sqrt { 2 } } ,
$$

• On $B _ { n } ( s )$ :

$$
E _ { n } ( s ) : = 0 , \quad | \Psi _ { n } ( s ) \rangle : = | v _ { n } ( s ) , 0 \rangle .
$$

• On $B ^ { \bot } ( s )$ :

$$
F _ { j } ( s ) : = 0 , \quad | \Phi _ { j } ( s ) \rangle , \quad j \in \left\{ 1 , \ldots , ( n - 1 ) ^ { 2 } \right\} ,
$$

where $\{ | \Phi _ { j } ( s ) \rangle \}$ defines an arbitrary basis of $B ^ { \bot } ( s )$ .

Proof. We consider the case $s \in \ [ 0 , 1 )$ , the case $s ~ = ~ 1$ follows by continuity. Since $V ^ { \dagger } ( s ) S V ( s ) | v _ { n } ( s ) , 0 \rangle = D ( s ) | v _ { n } ( s ) \rangle | 0 \rangle = | v _ { n } ( s ) , 0 \rangle$ , we immediately have that $| v _ { n } ( s ) , 0 \rangle$ is an eigenstate of $H ( s )$ with eigenvalue $0$ . For $k \neq n$ , note that

$$
\begin{array} { r l } & { V ^ { \dagger } ( s ) S V ( s ) \Pi _ { 0 } | v _ { k } ( s ) , 0 \rangle = \lambda _ { k } ( s ) | v _ { k } ( s ) , 0 \rangle + \sqrt { 1 - \lambda _ { k } ( s ) ^ { 2 } } | v _ { k } ( s ) , 0 \rangle ^ { \perp } , } \\ & { \Pi _ { 0 } V ^ { \dagger } ( s ) S V ( s ) | v _ { k } ( s ) , 0 \rangle = \lambda _ { k } ( s ) | v _ { k } ( s ) , 0 \rangle . } \end{array}
$$

By combining these expressions we get

$$
\begin{array} { r l } & { H ( s ) | v _ { k } ( s ) , 0 \rangle = i \sqrt { 1 - \lambda _ { k } ( s ) ^ { 2 } } | v _ { k } ( s ) , 0 \rangle ^ { \perp } , } \\ & { } \\ & { H ( s ) | v _ { k } ( s ) , 0 \rangle ^ { \perp } = - i \sqrt { 1 - \lambda _ { k } ( s ) ^ { 2 } } | v _ { k } ( s ) , 0 \rangle , } \end{array}
$$

where the second line follows from the fact that $H ( s )$ is Hermitian and traceless. In other words, $H ( s )$ acts on subspace $\boldsymbol { B } _ { k } ( \boldsymbol { s } )$ as $\sqrt { 1 - \lambda _ { k } ( s ) ^ { 2 } } \sigma _ { y }$ , where $\sigma _ { y } : = \left( \begin{array} { c c } { { 0 } } & { { - i } } \\ { { i } } & { { 0 } } \end{array} \right)$ is the Pauli $y$ matrix, which yields equation (20).

Since $B ^ { \bot } ( s )$ is the orthogonal complement of the union of invariant subspaces, it is also an invariant subspace for $H ( s )$ . Note that $H ( s )$ restricted to this subspace is equal to zero, hence the remaining $n ^ { 2 } - ( 2 n - 1 ) = ( n - 1 ) ^ { 2 }$ eigenvalues of $H ( s )$ are zero. □

# V. THE QUANTUM ADIABATIC THEOREM

In adiabatic quantum computing it is a common practice to associate the intermediate state of the computation with the ground state (i.e., the lowest energy eigenstate) of the

Hamiltonian. However, in our case the spectrum of $H ( s )$ is symmetric about zero and the state that we are interested in lies in the middle of the spectrum. Hence, we will not use the ground state of $H ( s )$ , which has negative energy, but instead we will use the zero-eigenvector $\vert \Psi _ { n } ( s ) \rangle$ given in equation (21). Indeed, equation (18) shows that this state is closely related to the stationary distribution $\pi ( s )$ of $P ( s )$ . In particular, the problem would be solved if we can reach the state $\vert \Psi _ { n } ( 1 ) \rangle$ , as measuring the first register of this state yields a vertex distributed according to $\pi ( 1 )$ , which only has support on marked vertices.

# A. The adiabatic condition

We initially prepare the system in the zero-eigenvector $\vert \Psi _ { n } ( 0 ) \rangle$ of $H ( 0 )$ and then start to change the Hamiltonian $H ( s )$ by slowly increasing the parameter $s$ from 0 to $1$ according to some schedule $s ( t )$ . If the schedule $s ( t )$ is chosen so that it satisfies certain conditions, the system is guaranteed to stay close to the intermediate zero-eigenstate $\vert \Psi _ { n } ( s ) \rangle$ . Then, at $s = 1$ , the state will be close to $| \Psi _ { n } ( 1 ) \rangle = | v _ { n } ( 1 ) , 0 \rangle$ , where the first register only has overlap over marked vertices, so that a measurement yields a marked vertex with high probability. Note that in our case the zero-eigenspace $B _ { n } ( s ) \cup B ^ { \bot } ( s )$ of the Hamiltonian $H ( s )$ has a huge dimension, so we have to make sure that the non-relevant part $B ^ { \bot } ( s )$ is totally decoupled from $\vert \Psi _ { n } ( s ) \rangle$ (the only zero-eigenvector that is relevant for our algorithm) before we apply the adiabatic condition. In particular, we want to show that

$$
\langle \Phi _ { j } ( s ) | \cdot { \frac { d } { d t } } | \Psi _ { n } ( s ) \rangle = 0
$$

for any $j \in \{ 1 , \ldots , ( n - 1 ) ^ { 2 } \}$ , since this would imply that during the evolution $\vert \Psi _ { n } ( s ) \rangle$ is not leaked into the subspace $B ^ { \bot } ( s )$ spanned by states $| \Phi _ { j } ( s ) \rangle$ . To see that this is indeed the case, note that

$$
| \Phi _ { j } ( s ) \rangle \perp \mathrm { s p a n } \left\{ | \Psi _ { 1 } ^ { \pm } ( s ) \rangle , \ldots , | \Psi _ { n - 1 } ^ { \pm } ( s ) \rangle , | \Psi _ { n } ( s ) \rangle \right\}
$$

for any $j \in \{ 1 , \ldots , ( n - 1 ) ^ { 2 } \}$ , since the eigenvectors of $H ( s )$ form an orthonormal basis. In particular,

$$
\begin{array} { r l } & { | \Phi _ { j } ( s ) \rangle \perp \mathrm { s p a n } \left\{ | \Psi _ { 1 } ^ { + } ( s ) \rangle + | \Psi _ { 1 } ^ { - } ( s ) \rangle , \ldots , | \Psi _ { n - 1 } ^ { + } ( s ) \rangle + | \Psi _ { n - 1 } ^ { - } ( s ) \rangle , | \Psi _ { n } ( s ) \rangle \right\} } \\ & { \phantom { = } \mathrm { s p a n } \{ | v _ { 1 } ( s ) , 0 \rangle , \ldots , | v _ { n - 1 } ( s ) , 0 \rangle , | v _ { n } ( s ) , 0 \rangle \} . } \end{array}
$$

Recall from equation (21) that $\begin{array} { r } { \frac { d } { d t } | \Psi _ { n } ( s ) \rangle = \frac { d } { d t } | v _ { n } ( s ) \rangle | 0 \rangle } \end{array}$ . Hence, the inner product in equation (27) indeed vanishes. Thus, we can safely apply the adiabatic condition only for the relevant subspace in which the zero-eigenstate is not degenerate.

The folk version of the Adiabatic Theorem [2] states that during the evolution the state of the system $| \psi ( t ) \rangle$ is guaranteed to stay close to the intermediate zero-eigenstate $\vert \Psi _ { n } ( s ) \rangle$ , more precisely,

$$
\forall t : \left| \left. \Psi _ { n } ( s ( t ) ) \middle | \psi ( t ) \right. \right| ^ { 2 } \geq 1 - \varepsilon ^ { 2 } ,
$$

as long as the adiabatic condition

$$
\forall t : \sum _ { \sigma = \pm 1 } \sum _ { k = 1 } ^ { n - 1 } \frac { \big | \langle \Psi _ { k } ^ { \sigma } ( s ) | \cdot \frac { d } { d t } | \Psi _ { n } ( s ) \rangle \big | ^ { 2 } } { \big ( E _ { k } ^ { \sigma } ( s ) - E _ { n } ( s ) \big ) ^ { 2 } } \leq \varepsilon ^ { 2 }
$$

is satisfied. While this condition is known not to be sufficient in full generality (see e.g. the discussion in [7]), we will assume that it can be applied in our setup. We will discuss about how this assumption may be suppressed in Section VII.

If we insert all eigenvalues and eigenvectors from equations (20) and (21), the adiabatic condition (31) can be written purely in terms of the eigenvalues and eigenvectors of the discriminant matrix $D ( s )$ :

$$
\forall t : \sum _ { k : \lambda _ { k } ( s ) \neq 1 } \frac { \big | \langle v _ { k } ( s ) | \cdot \frac { d } { d t } | v _ { n } ( s ) \rangle \big | ^ { 2 } } { 1 - \lambda _ { k } ^ { 2 } ( s ) } \leq \varepsilon ^ { 2 } .
$$

# B. Rotation in a two-dimensional subspace

In this section we will provide a simple interpretation of the evolution of the eigenvector $| v _ { n } ( s ) \rangle$ . First, let us define the following superpositions over all elements, marked elements, and unmarked elements, respectively:

$$
{ \mathrm {  ~ { \widetilde { \tau } } ~ } } : = \sum _ { x \in X } \sqrt { \pi _ { x } } | x \rangle , \quad | M \rangle : = \frac { 1 } { \sqrt { p _ { M } } } \sum _ { x \in M } \sqrt { \pi _ { x } } | x \rangle , \quad | U \rangle : = \frac { 1 } { \sqrt { 1 - p _ { M } } } \sum _ { x \notin M } \sqrt { \pi _ { x } } | x \rangle .
$$

Now, we show that $| v _ { n } ( s ) \rangle$ is subject to a rotation in the two-dimensional subspace $\mathcal { R } : =$ span $\{ | U \rangle , | M \rangle \}$ . From equations (5) and (18), we obtain

$$
{ \mathrm { \Omega } } _ { n } ( s ) \rangle = \sum _ { x \in X } { \sqrt { \pi _ { x } ( s ) } } | x \rangle = { \frac { 1 } { \sqrt { 1 - s ( 1 - p _ { M } ) } } } { \Bigg ( } { \sqrt { 1 - s } } \sum _ { x \notin M } { \sqrt { \pi _ { x } } } | x \rangle + \sum _ { x \in M } { \sqrt { \pi _ { x } } } | x \rangle { \Bigg ) } .
$$

Using the definition of $| U \rangle$ and $| M \rangle$ we can rewrite this simply as

$$
| v _ { n } ( s ) \rangle = \cos \theta ( s ) | U \rangle + \sin \theta ( s ) | M \rangle ,
$$

where

$$
\theta ( s ) : = \arcsin \sqrt { \frac { p _ { M } } { 1 - s ( 1 - p _ { M } ) } } .
$$

Let us choose the schedule $s ( t )$ so that the evolution of $| v _ { n } ( s ) \rangle$ as defined by equation (35) corresponds to a rotation with constant angular velocity in the subspace $_ { \mathcal { R } }$ . If $T$ is the length of the evolution and $s : [ 0 , T ]  [ 0 , 1 ]$ is defined as

$$
t ) : = \frac { 1 } { 1 - p _ { M } } \left( 1 - \frac { p _ { M } } { \sin ^ { 2 } ( \omega t + \theta _ { 0 } ) } \right) , \quad \theta _ { 0 } : = \arcsin \sqrt { p _ { M } } , \quad \omega : = \frac { 1 } { T } \operatorname { a r c c o s } \sqrt { p _ { M } } ,
$$

then

$$
\begin{array} { r } { \theta ( s ( t ) ) = \omega t + \theta _ { 0 } . } \end{array}
$$

Let us choose a vector $| v _ { n } ^ { \perp } ( s ) \rangle$ such that $\{ | v ( s ) \rangle , | v _ { n } ^ { \perp } ( s ) \rangle \}$ is an orthonormal basis of $\mathcal { R }$ for every $s$ :

$$
| v _ { n } ^ { \perp } ( s ) \rangle : = - \sin \theta ( s ) | U \rangle + \cos \theta ( s ) | M \rangle .
$$

Then from equations (35) and (38) we easily find that

$$
\frac { d } { d t } | v _ { n } ( s ( t ) ) \rangle = \omega | v _ { n } ^ { \perp } ( s ( t ) ) \rangle = \frac { 1 } { T } \operatorname { a r c c o s } \sqrt { p _ { M } } | v _ { n } ^ { \perp } ( s ( t ) ) \rangle .
$$

Note that arccos $\begin{array} { r } { \sqrt { p _ { M } } \le \frac { \pi } { 2 } } \end{array}$ . Therefore, we can rewrite the adiabatic condition (32) as follows:

$$
\forall s : \frac { \pi ^ { 2 } } { 4 \varepsilon ^ { 2 } } \sum _ { k : \lambda _ { k } ( s ) \neq 1 } \frac { \left. \langle v _ { k } ( s ) \vert v _ { n } ^ { \perp } ( s ) \rangle \right. ^ { 2 } } { 1 - \lambda _ { k } ^ { 2 } ( s ) } \leq T ^ { 2 } .
$$

If this condition is satisfied, equation (30) implies that we obtain at time $t = T$ a state $| \psi ( T ) \rangle$ close to $| \Psi _ { n } ( 1 ) \rangle = | v _ { n } ( 1 ) \rangle | 0 \rangle = | M \rangle | 0 \rangle$ , so that measuring the first register yields a marked vertex with probability at least $1 - \epsilon ^ { 2 }$ .

# VI. RUNNING TIME OF THE QUANTUM ALGORITHM

# A. Choice of running time $T$

We have to change the parameter $s$ slowly for the evolution to be adiabatic, thus we want to choose $T$ big enough so that condition (41) holds. Recall from Section IV A that we can assume that $\lambda _ { k } ( s ) \geq 0$ . Thus, $1 - \lambda _ { k } ^ { 2 } ( s ) = \left( 1 + \lambda _ { k } ( s ) \right) \left( 1 - \lambda _ { k } ( s ) \right) \geq 1 - \lambda _ { k } ( s )$ . Let us impose a slightly stronger condition on $T$ in equation (41) by replacing $1 - \lambda _ { k } ^ { 2 } ( s )$ with $1 - \lambda _ { k } ( s )$ . In addition, let us choose the smallest $T$ that still satisfies the inequality and use it as the running time of our adiabatic algorithm:

$$
T : = \frac { \pi } { 2 \varepsilon } \operatorname* { m a x } _ { 0 \leq s \leq 1 } \sqrt { \sum _ { k : \lambda _ { k } ( s ) \neq 1 } \frac { | \langle v _ { k } ( s ) | v _ { n } ^ { \perp } ( s ) \rangle | ^ { 2 } } { 1 - \lambda _ { k } ( s ) } } .
$$

It turns out that there is an interesting relationship between this quantity and the hitting time of the Markov chain $P$ .

# B. Hitting time of a Markov chain

Let us first give an explicit expression for the hitting time H $\mathrm { T } ( P , M )$ as defined in Section II. Let $0 _ { M }$ and $1 _ { M }$ (resp., $0 _ { U }$ and $1 _ { U }$ ) be the all-zero and all-one row vectors of dimension $m$ (resp., $n - m$ ). Furthermore, let $\tilde { \pi } _ { M } : = \pi _ { M } / p _ { M }$ and $\tilde { \pi } _ { U } : = \pi _ { U } / ( 1 - p _ { M } )$ be the row vectors describing distributions over marked and unmarked vertices. Then, the distribution of vertices at the the first execution of step 4 of Random Walk Algorithm is $\left( \tilde { \pi } _ { U } \ 0 _ { M } \right)$ , and from the definition of the discriminant $D ( 1 )$ , we have

$$
\begin{array} { l } { { \displaystyle { \mathrm { H T } ( P , M ) } : = \sum _ { t = 0 } ^ { \infty } \mathrm { P r } [ \mathrm { N o ~ m a r k e d ~ v e r t e x ~ f o u n d ~ a f t e r ~ } t \mathrm { ~ s t e p s ~ f r o m ~ } ( \tilde { \pi } _ { U } ~ 0 _ { M } ) ] } } \\ { ~ = \sum _ { t = 0 } ^ { \infty } ( \tilde { \pi } _ { U } ~ 0 _ { M } ) P ^ { t } ( 1 ) \left( { 1 _ { U } ~ 0 _ { M } } \right) ^ { \top } } \\ { ~ = \sum _ { t = 0 } ^ { \infty } \langle U | D ^ { t } ( 1 ) | U \rangle , } \end{array}
$$

where the last equality follows from equation (9). We will show that the running time of our adiabatic quantum algorithm is directly related to the square root of the hitting time HT $( P , M )$ . In order to do this, we define the following extension of the hitting time. Let

$$
\mathrm { H T } ( s ) : = \sum _ { t = 0 } ^ { \infty } \langle U | \big ( D ^ { t } ( s ) - | v _ { n } ( s ) \rangle \langle v _ { n } ( s ) | \big ) | U \rangle .
$$

Note that $\mathrm { H T } ( 1 ) = \mathrm { H T } ( P , M )$ since $\langle U | v _ { n } ( 1 ) \rangle = 0$ . This justifies to consider $\operatorname { H T } ( s )$ as an extension of the hitting time. Intuitively, $\operatorname { H T } ( s )$ may be understood as the time it takes for $P ( s )$ to converge to its stationary distribution, starting from $\left( \tilde { \pi } _ { U } \ 0 _ { M } \right)$ . For $s = 1$ , the walk

$P ( 1 ) = P ^ { \prime }$ converges to the (non-unique) stationary distribution $\left( 0 _ { U } \mathrm { \Delta } \tilde { \pi } _ { M } \right)$ , which only has support over marked elements.

Using the expansion $\textstyle ( 1 - x ) ^ { - 1 } = \sum _ { t = 0 } ^ { \infty } x ^ { t }$ and the spectral decomposition (14) of the discriminant $D ( s )$ , we have

$$
\begin{array} { l } { \displaystyle \mathrm { H T } ( s ) = \sum _ { k \neq n } \sum _ { t = 0 } ^ { \infty } \lambda _ { k } ^ { t } ( s ) \langle U | v _ { k } ( s ) \rangle \langle v _ { k } ( s ) | U \rangle } \\ { = \displaystyle \sum _ { k : \lambda _ { k } ( s ) \neq 1 } \frac { | \langle v _ { k } ( s ) | U \rangle | ^ { 2 } } { 1 - \lambda _ { k } ( s ) } . } \end{array}
$$

C. Relation between the running time and the extended hitting times

Let us express the running time $T$ from equation (42) in terms of $\operatorname { H T } ( s )$ . Define

$$
A ( s ) : = \sum _ { k : \lambda _ { k } ( s ) \neq 1 } { \frac { | v _ { k } ( s ) \rangle \langle v _ { k } ( s ) | } { 1 - \lambda _ { k } ( s ) } } .
$$

Note that both $T$ and $\operatorname { H T } ( s )$ can be expressed in terms of $A ( s )$ as follows:

$$
T = \frac { \pi } { 2 \varepsilon } \operatorname* { m a x } _ { 0 \leq s \leq 1 } \sqrt { \langle v _ { n } ^ { \perp } ( s ) | A ( s ) | v _ { n } ^ { \perp } ( s ) \rangle } , \mathrm { H T } ( s ) = \langle U | A ( s ) | U \rangle .
$$

By definition, we have $A ( s ) | v _ { n } ( s ) \rangle = 0$ , which together with equation (35) implies that

$$
A ( s ) \vert M \rangle = - { \frac { \cos \theta ( s ) } { \sin \theta ( s ) } } A ( s ) \vert U \rangle .
$$

Using this and the definition of $| v _ { n } ^ { \perp } ( s ) \rangle$ in equation (39), we see that $\langle v _ { n } ^ { \perp } ( s ) | A ( s ) | v _ { n } ^ { \perp } ( s ) \rangle =$ $\langle U | A ( s ) | U \rangle / \sin ^ { 2 } \theta ( s )$ . Thus we get the following relationship between $T$ and HT $( s )$ :

$$
T = \frac { \pi } { 2 \varepsilon } \operatorname* { m a x } _ { 0 \leq s \leq 1 } \frac { \sqrt { \mathrm { H T } ( s ) } } { \sin \theta ( s ) } .
$$

To relate $T$ and the usual hitting time HT $( P , M )$ of $P$ , we first provide an explicit expression for $\operatorname { H T } ( s )$ in terms of $\mathrm { H T } ( P , M )$ (the proof is given in the appendix).

Lemma 2. $\mathrm { H T } ( s ) = \mathrm { H T } ( P , M ) \sin ^ { 4 } \theta ( s )$ .

Now, recalling the definition of $\theta ( s )$ in equation (36), it is easy to see that the maximum in equation (52) is attained at $s = 1$ . This immediately implies that the running time of the adiabatic quantum algorithm is given by

$$
T = \frac { \pi } { 2 \varepsilon } \sqrt { \mathrm { H T } ( P , M ) } ,
$$

therefore providing a quadratic improvement over the classical hitting time. This also concludes the proof of Theorem 1.

# VII. CONCLUSION AND DISCUSSION

Our quantum algorithm defines a new notion of quantum hitting time, which is quadratically smaller than the classical hitting time for any reversible Markov chain and any set of marked elements. While previous approaches were subject to various restrictions, e.g., the quantum algorithm could only detect the presence of marked elements [13], did not always provide full quadratic speed-up [15], or could only be applied for state-transitive Markov chains with a unique marked element [16], our adiabatic approach only requires minimal assumptions. Indeed, it can be shown that the only remaining condition, reversibility, is necessary. Let us consider the Markov chain on a cycle $\textstyle P = { \frac { I + C } { 2 } } $ , where $C$ implements a clockwise shift, i.e., $C | x \rangle = | ( x + 1 )$ mod $n \rangle$ . This Markov chain is ergodic but not reversible. While its classical hitting time is of order $\Theta ( n )$ , a simple locality argument implies that any quantum operator acting locally on the cycle requires a time $\Omega ( n )$ to find a marked vertex, so that a quadratic speed-up cannot be achieved. Magniez et al. [16] have also shown that under reasonable conditions the quadratic speed-up is optimal. This provides evidence that our result is both as strong and as general as possible.

While our result relies on the assumption that the folk adiabatic condition is sufficient, this assumption could be suppressed in different ways. One option would be to actually prove that the folk Adiabatic Theorem holds in our setup, as was previously done for the adiabatic version of Grover’s algorithm [7]. Another option would be to circumvent adiabatic evolution altogether, by using the phase randomization technique of Boixo et al. [24]. Their technique provides a quantum circuit realizing the same evolution as the adiabatic approach with a similar running time, but without relying on the adiabatic condition. This leads to the quantum circuit algorithm described in [23].

Finally, note that in order to design the schedule $s ( t )$ , our algorithm requires to know $p _ { M }$ and the order of magnitude of HT $( P , M )$ . These assumptions are standard in other quantum algorithms for this problem. In particular, a similar issue arises in Grover’s algorithm when the number of marked elements is unknown. In Grover’s case, there are techniques to deal with this issue [25], and similar techniques could be applied in our case. While we do not provide a full answer to these questions in the present paper, they do not present any new technical difficulty and we refer the reader to [23] where a full study of these implementation issues is provided for a related quantum circuit algorithm.

# Acknowledgments

J. Roland would like to thank F. Magniez, A. Nayak, M. Santha and R. Somma for useful discussions. H. Krovi would like to thank F. Magniez for useful discussions. This research has been supported in part by ARO/NSA under grant W911NF-09-1-0569. M. Ozols acknowledges support from QuantumWorks.

[1] E. Farhi, J. Goldstone, S. Gutmann, and M. Sipser (2000), arXiv:quant-ph/0001106.   
[2] A. Messiah, M´ecanique Quantique (Dunod, Paris, 1959).   
[3] K.-P. Marzlin and B. C. Sanders, Phys. Rev. Lett. 93, 160408 (2004).   
[4] M. S. Sarandy, L.-A. Wu, and D. A. Lidar, Quantum Information Processing 3, 331 (2004).   
[5] Z. Wu, L. Zheng, and H. Yang (2004), arXiv:quant-ph/0411212.   
[6] D. M. Tong, K. Singh, L. C. Kwek, and C. H. Oh, Phys. Rev. Lett. 95, 110407 (2005).   
[7] S. Jansen, M.-B. Ruskai, and R. Seiler, J. Math. Phys. 48, 102111 (2007).   
[8] L. K. Grover, in Proceedings of the 28th ACM Symposium on Theory of Computing (ACM Press, 1996), pp. 212–219.   
[9] W. van Dam, M. Mosca, and U. Vazirani, in Proceedings of the 42nd IEEE Symposium on Foundations of Computer Science (IEEE Computer Society Press, 2001), pp. 279–287.   
[10] J. Roland and N. J. Cerf, Phys. Rev. A 65, 042308 (2002).   
[11] A. Ambainis, J. Kempe, and A. Rivosh, in Proceedings of the 16th ACM-SIAM Symposium on Discrete Algorithms (SIAM, 2005), pp. 1099–1108.   
[12] J. Kempe, Prob. Th. Rel. Fields 133, 215 (2005).   
[13] M. Szegedy, in Proceedings of the 45th IEEE Symposium on Foundations of Computer Science (IEEE Computer Society Press, 2004), pp. 32–41.   
[14] H. Krovi and T. A. Brun, Phys. Rev. A 73, 032341 (2006).   
[15] F. Magniez, A. Nayak, J. Roland, and M. Santha, in Proceedings of the 39th ACM Symposium on Theory of Computing (ACM Press, 2007), pp. 575–584, ISBN 978-1-59593-631-8.   
[16] F. Magniez, A. Nayak, P. C. Richter, and M. Santha, in Proceedings of the 19th ACM-SIAM Symposium on Discrete Algorithms (SIAM, 2009), pp. 86–95.   
[17] M. Varbanov, H. Krovi, and T. A. Brun, Phys. Rev. A 78, 022324 (2008).   
[18] A. Ambainis, in Proceedings of the 45th IEEE Symposium on Foundations of Computer Science (IEEE Computer Society Press, 2004), pp. 22–31.   
[19] A. M. Childs and J. Goldstone, Phys. Rev. A 70, 022314 (2004).   
[20] A. M. Childs and J. Goldstone, Phys. Rev. A 70, 042312 (2004).   
[21] A. Tulsi, Phys. Rev. A 78, 012310 (2008).   
[22] R. D. Somma and G. Ortiz, in Quantum Quenching, Annealing and Computation (Springer, Heidelberg, 2010), Lecture Notes in Physics, in Press.   
[23] H. Krovi, F. Magniez, M. Ozols, and J. Roland (2010), arXiv:1002.2419 [quant-ph].   
[24] S. Boixo, E. Knill, and R. D. Somma, Quant. Inf. Comp. 9, 0833 (2009).   
[25] M. Boyer, G. Brassard, P. Høyer, and A. Tapp, Fortschritte Der Physik 46, 493 (1998).   
[26] Note that when we consider reversible Markov chains as defined in Section III B, this corresponds to a different notion of reversibility than in the usual thermodynamical sense. Actually, even a “reversible” Markov chain is thermodynamically irreversible.   
[27] Throughout the paper we use the convention that each row of a stochastic matrix $P$ sums to one $\begin{array} { r } { \forall x \in X : \sum _ { y \in X } P _ { x y } = 1 , } \end{array}$ ) and probability distributions are row vectors and hence are multiplied to the transition matrix from the left hand side $( e . g . , \pi P )$ .   
[28] Note that $| v _ { k } ( s ) , 0 \rangle ^ { \perp }$ depends on how the operator $V ( s )$ defined in equation in (11) is extended to the whole Hilbert space.

# Appendix: Proof of Lemma 2

In this section, we will often use $\dot { f } ( s )$ as a shorthand form of $\textstyle { \frac { d } { d s } } f ( s )$ . We will show that the derivative of HT $( s )$ satisfies the following lemma.

Lemma 3. The derivative of $\operatorname { H T } ( s )$ is related to HT $( s )$ as:

$$
{ \frac { d } { d s } } \operatorname { H T } ( s ) = 4 { \dot { \theta } } ( s ) { \frac { \cos \theta ( s ) } { \sin \theta ( s ) } } \operatorname { H T } ( s ) .
$$

Note that Lemma 2 follows directly from there, since $\mathrm { H T } ( s ) = \mathrm { H T } ( P , M ) \sin ^ { 4 } \theta ( s )$ satisfies the differential equation for HT $( s )$ with the boundary condition $\mathrm { H T } ( 1 ) = \mathrm { H T } ( P , M )$ . Therefore, it remains to prove Lemma 3.

Before proving Lemma 3, let us consider the derivative of the discriminant $D ( s )$ . Let $\textstyle \prod _ { M } = \sum _ { x \in M } | x \rangle \langle x |$ be the projector onto the $m$ -dimensional subspace spanned by marked vertices, and let $\{ X , Y \} : = X Y + Y X$ be the anticommutator of $X$ and $Y$ .

Lemma 4. $\begin{array} { r } { \dot { D } ( s ) = \frac { 1 } { 2 ( 1 - s ) } \big \{ \Pi _ { M } , I - D ( s ) \big \} } \end{array}$

Proof. Note from equation (3) that $D ( s )$ has the following block structure:

Hence,

$$
D ( s ) = \left( \begin{array} { c c } { { \sqrt { P _ { U U } \circ P _ { U U } ^ { \sf T } } } } & { { \sqrt { ( 1 - s ) ( P _ { U M } \circ P _ { M U } ^ { \sf T } ) } } } \\ { { \sqrt { ( 1 - s ) ( P _ { M U } \circ P _ { U M } ^ { \sf T } ) } } } & { { ( 1 - s ) \sqrt { P _ { M M } \circ P _ { M M } ^ { \sf T } } + s I } } \end{array} \right) .
$$

$$
\begin{array} { r } { \dot { D } ( s ) = \left( \begin{array} { c c } { 0 } & { - \frac { 1 } { 2 \sqrt { 1 - s } } \sqrt { P _ { U M } \circ P _ { M U } ^ { \mathsf { T } } } } \\ { - \frac { 1 } { 2 \sqrt { 1 - s } } \sqrt { P _ { M U } \circ P _ { U M } ^ { \mathsf { T } } } } & { I - \sqrt { P _ { M M } \circ P _ { M M } ^ { \mathsf { T } } } } \end{array} \right) . } \end{array}
$$

Observe that $\begin{array} { r } { \dot { D } ( s ) + \frac { 1 } { 2 ( 1 - s ) } \{ \Pi _ { M } , D ( s ) \} = \frac { 1 } { 1 - s } \Pi _ { M } } \end{array}$ , which implies the lemma.

We are now ready to prove Lemma 3.

Proof of Lemma 3. In this proof we will often omit to write the dependence on $s$ explicitly. From equation (50) we have

$$
{ \frac { d } { d s } } \operatorname { H T } = \langle U | { \dot { A } } | U \rangle .
$$

Note that $A = B ^ { - 1 } - \Pi _ { n }$ , where

$$
B : = I - D + \Pi _ { n } , \qquad \Pi _ { n } : = | v _ { n } \rangle \langle v _ { n } | .
$$

For any invertible matrix $M$ we have $\begin{array} { r } { \frac { d } { d s } ( M ^ { - 1 } ) = - M ^ { - 1 } \dot { M } M ^ { - 1 } } \end{array}$ . Therefore,

$$
\dot { A } = - B ^ { - 1 } \big ( - \dot { D } + \dot { \Pi } _ { n } \big ) B ^ { - 1 } - \dot { \Pi } _ { n } .
$$

Hence, we have $\begin{array} { r } { \frac { d } { d s } \mathrm { H T } = h _ { 1 } + h _ { 2 } + h _ { 3 } } \end{array}$ , where

$$
\begin{array} { r l } & { h _ { 1 } : = \langle U | B ^ { - 1 } \dot { D } B ^ { - 1 } | U \rangle , } \\ & { } \\ & { h _ { 2 } : = - \langle U | B ^ { - 1 } \dot { \Pi } _ { n } B ^ { - 1 } | U \rangle , } \\ & { } \\ & { h _ { 3 } : = - \langle U | \dot { \Pi } _ { n } | U \rangle . } \end{array}
$$

Let us evaluate each of these terms separately. We can use Lemma 4 and the definition of $B$ to express the first term $h _ { 1 }$ as follows:

$$
\begin{array} { r l } & { 2 ( 1 - s ) h _ { 1 } = \langle U \vert B ^ { - 1 } \{ \Pi _ { M } , I - D \} B ^ { - 1 } \vert U \rangle } \\ & { \qquad = \langle U \vert B ^ { - 1 } \big ( \{ \Pi _ { M } , B \} - \{ \Pi _ { M } , \Pi _ { n } \} \big ) B ^ { - 1 } \vert U \rangle } \\ & { \qquad = \langle U \vert \{ B ^ { - 1 } , \Pi _ { M } \} \vert U \rangle - \langle U \vert B ^ { - 1 } \{ \Pi _ { M } , \Pi _ { n } \} B ^ { - 1 } \vert U \rangle . } \end{array}
$$

Note that $\Pi _ { M } | U \rangle = 0$ , thus the first term vanishes. Also note that $B ^ { - 1 } | v _ { n } \rangle = | v _ { n } \rangle$ and $B ^ { - 1 }$ is Hermitian, thus

$$
2 ( 1 - s ) h _ { 1 } = - 2 \langle U | B ^ { - 1 } \Pi _ { M } \Pi _ { n } | U \rangle .
$$

Note from equation (35) that $\Pi _ { M } | v _ { n } \rangle = \sin \theta | M \rangle$ . Moreover, using equation (51) we can simplify equation (A.13) even further:

$$
\begin{array} { r l } & { 2 ( 1 - s ) h _ { 1 } = - 2 \cos { \theta } \sin { \theta } \langle U \vert B ^ { - 1 } \vert M \rangle } \\ & { \qquad = - 2 \cos { \theta } \sin { \theta } \langle U \vert ( A + \Pi _ { n } ) \vert M \rangle } \\ & { \qquad = - 2 \cos { \theta } \sin { \theta } \langle U \vert A \vert M \rangle - 2 \cos ^ { 2 } { \theta } \sin ^ { 2 } { \theta } } \\ & { \qquad = 2 \cos ^ { 2 } { \theta } \big ( \langle U \vert A \vert U \rangle - \sin ^ { 2 } { \theta } \big ) . } \end{array}
$$

Let us now consider the second term $h _ { 2 }$ :

$$
\begin{array} { r l } { h _ { 2 } = - \langle U | B ^ { - 1 } \dot { \Pi } _ { n } B ^ { - 1 } | U \rangle } & { } \\ & { \ = - \cos \theta \big ( \langle \dot { v } _ { n } | B ^ { - 1 } | U \rangle + \langle U | B ^ { - 1 } | \dot { v } _ { n } \rangle \big ) } \\ & { \ = - 2 \cos \theta \langle U | \big ( A + \Pi _ { n } \big ) | \dot { v } _ { n } \rangle } \\ & { \ = - 2 \dot { \theta } \cos \theta \big ( - \sin \theta \langle U | A | U \rangle + \cos \theta \langle U | A | M \rangle \big ) } \\ & { \ = - 2 \dot { \theta } \cos \theta \left( - \sin \theta \langle U | A | U \rangle - \frac { \cos ^ { 2 } \theta } { \sin \theta } \langle U | A | U \rangle \right) } \\ & { \ = 2 \dot { \theta } \frac { \cos \theta } { \sin \theta } \langle U | A | U \rangle , } \end{array}
$$

where we have used the fact that

$$
| \dot { v } _ { n } \rangle = \dot { \theta } \bigl ( - \sin \theta | U \rangle + \cos \theta | M \rangle \bigr ) ,
$$

and $\Pi _ { n } | \dot { v } _ { n } \rangle = 0$ . Similarly, for the last term $h _ { 3 }$ we have

$$
h _ { 3 } = - \langle U | \dot { \Pi } _ { n } | U \rangle = 2 \dot { \theta } \cos \theta \sin \theta .
$$

Putting all the terms back together, we have

$$
\begin{array} { l } { { \langle U | \dot { A } | U \rangle = \displaystyle \frac { \cos ^ { 2 } \theta } { 1 - s } \big ( \langle U | A | U \rangle - \sin ^ { 2 } \theta \big ) + 2 \dot { \theta } \frac { \cos \theta } { \sin \theta } \langle U | A | U \rangle + 2 \dot { \theta } \cos \theta \sin \theta } } \\ { { = \displaystyle \frac { \cos \theta } { \sin \theta } \left( 2 \dot { \theta } + \frac { \cos \theta \sin \theta } { 1 - s } \right) \langle U | A | U \rangle + \cos \theta \sin \theta \left( 2 \dot { \theta } - \frac { \cos \theta \sin \theta } { 1 - s } \right) . } } \end{array}
$$

From the definition of $\theta$ in equation (36) it is straightforward to check that

$$
2 { \dot { \theta } } = { \frac { \cos \theta \sin \theta } { 1 - s } }
$$

which together with equations (A.4) and (A.26) implies the lemma.