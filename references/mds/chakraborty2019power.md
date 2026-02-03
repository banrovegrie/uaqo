# The power of block-encoded matrix powers: improved regression techniques via faster Hamiltonian simulation

Shantanav Chakraborty∗ András Gilyén† Stacey Jeffery‡

September 5, 2018

# Abstract

We apply the framework of block-encodings, introduced by Low and Chuang (under the name standard-form), to the study of quantum machine learning algorithms and derive general results that are applicable to a variety of input models, including sparse matrix oracles and matrices stored in a data structure. We develop several tools within the block-encoding framework, such as singular value estimation of a block-encoded matrix, and quantum linear system solvers using block-encodings. The presented results give new techniques for Hamiltonian simulation of non-sparse matrices, which could be relevant for certain quantum chemistry applications, and which in turn imply an exponential improvement in the dependence on precision in quantum linear systems solvers for non-sparse matrices.

In addition, we develop a technique of variable-time amplitude estimation, based on Ambainis’ variable-time amplitude amplification technique, which we are also able to apply within the framework.

As applications, we design the following algorithms: (1) a quantum algorithm for the quantum weighted least squares problem, exhibiting a 6-th power improvement in the dependence on the condition number and an exponential improvement in the dependence on the precision over the previous best algorithm of Kerenidis and Prakash; (2) the first quantum algorithm for the quantum generalized least squares problem; and (3) quantum algorithms for estimating electrical-network quantities, including effective resistance and dissipated power, improving upon previous work.

# Contents

# 1 Introduction 3

1.1 Techniques for block-encodings 6   
1.2 Application to least squares 7   
1.3 Application to estimating electrical network quantities 9

# 2 Preliminaries

#

2.1 Notation .   
2.2 Quantum-accessible data structure   
2.3 Unitary block-encoding of matrices   
2.4 Sparse-access input model . . 16

# 3 Variable-time amplitude amplification and estimation 17

3.1 Variable-stopping-time algorithms and variable-time amplification 3.2 Efficient variable-time amplitude amplification and estimation 1721

# 4 Linear system solving using blocks of unitaries 25

4.1 Hamiltonian simulation with quantum data structure . 2828   
4.2 Quantum singular value estimation   
4.3 Quantum linear system solvers

# 5 Applications 39

5.1 Least squares . 5.1.1 Weighted least squares 5.1.2 Generalized least squares .   
5.2 Estimating electrical network quantities

# A Technical results about block-encodings 52

A.1 Error propagation of block-encodings under various operations 53 A.2 Implementing smooth functions of Block-Hamiltonians 54 A.3 Variable time quantum algorithm for implementing negative powers of Hermitian matrices 57

# 1 Introduction

A rapidly growing and important class of quantum algorithms are those that use Hamiltonian simulation subroutines to solve linear algebraic problems, many with potential applications to machine learning. This subfield began with the HHL algorithm, due to Harrow, Hassidim and Lloyd [HHL09], which solves the quantum linear system problem (QLS problem). In this problem, the input consists of a matrix $A \in \mathbb { R } ^ { N \times N }$ and a vector $\vec { b } \in \mathrm { \mathbb { R } } ^ { N }$ , in some specified format, and the algorithm should output a quantum state proportional to $\sum _ { i = 1 } ^ { { N } } x _ { i } | i \rangle$ , where $\Vec { x } = A ^ { - 1 } \Vec { b }$ .

The format in which the input is presented is of crucial importance. For a sparse $A _ { i }$ , given an efficient algorithm to query the $i .$ -th non-zero entry of the $j .$ -th row of $A$ , the HHL algorithm and its subsequent improvements [Amb12, CKS17] can solve the QLS problem in complexity that depends poly-logarithmically on $N .$ Here, if $A$ were given naively as a list of all its entries, it would generally take time proportionally to $N ^ { 2 }$ just to read the input. We will refer to this model of accessing $A ,$ in which we can query the $i .$ -th non-zero entry of the $j .$ -th row, as the sparse-access input model.1

In [KP16] and [KP17], Kerenidis and Prakash consider several linear algebraic problems in a different input model. They assume that data has been collected and stored in some carefully chosen data structure in advance. If the data is described by an arbitrary $N \times N$ matrix, then of course, this collection will take time at least $N ^ { 2 }$ (or, if the matrix is sparse, at least the number of non-zero entries). However, processing the data, given such a data structure, is significantly cheaper, depending only poly-logarithmically on $N$ . Kerenidis and Prakash describe a data structure that, when stored in quantum-random-access read-only memory $( \mathsf { Q R O M } ) ^ { 2 }$ , allows for the preparation of a superposition over $N$ data points in complexity poly-logarithmic in $N$ . We call this the quantum data structure input model and discuss it more in Section 2.2. Although in some applications it might be too much to ask for the data to be presented in such a structure, one advantage of this input model is that it is not restricted to sparse matrices. This result can potentially also be useful for some quantum chemistry applications, since a recent proposal of Babbush et al. $[ { \mathsf { B B K } } ^ { + } 1 6 ]$ uses a database of all Hamiltonian terms in order to simulate the electronic structure.

The HHL algorithm and its variants and several other applications are based on techniques from Hamiltonian simulation. Given a Hermitian matrix $H$ and an input state $| \psi \rangle ,$ the Hamiltonian simulation problem is to simulate the unitary $e ^ { i H }$ on $| \psi \rangle$ for some time t. Most work in this area has considered the sparse-access input model [Llo96, ATS03, BACS07, BC12, $\mathsf { B C C } ^ { + } 1 4$ , $\mathsf { B C C } ^ { + } 1 5$ , Chi04, Chi10, CW12, PQSV11, WBHS11, BCK15, NB16, BN16], but recent work of Low and Chuang [LC16] has considered a different model, which we call the block-encoding framework 3.

The block-encoding framework. A block-encoding of a matrix $A \in \mathbb { C } ^ { N \times N }$ is a unitary $U$ such that the top left block of $U$ is equal to $A / \alpha$ for some normalizing constant $\alpha \geq \left. A \right.$ :

$$
U = \left( \begin{array} { c c } { { A / \alpha } } & { { . } } \\ { { . } } & { { . } } \end{array} \right) .
$$

In other words, for some $a$ , for any state $| \psi \rangle$ of appropriate dimension, $\alpha ( \langle 0 | ^ { \otimes a } \otimes I ) U ( | 0 \rangle ^ { \otimes a } \otimes$ $| \psi \rangle ) = A | \psi \rangle$ .

Such an encoding is useful if $U$ can be implemented efficiently. In that case, $U ,$ combined with amplitude amplification, can be used to generate the state $A | \psi \rangle / \big | \big | A | \psi \rangle \big | \big |$ given a circuit for generating $| \psi \rangle$ . The main motivation for using block-encodings is that Low and Chuang showed [LC16] how to perform optimal Hamiltonian simulation given a block-encoded Hamiltonian $A$ .

In Ref. [KP16], Kerenidis and Prakash implicitly prove that if an $N \times N$ matrix $A$ is given as a quantum data structure, then there is an $\varepsilon$ -approximate block-encoding of $A$ that can be implemented in complexity polylog $( N / \varepsilon )$ . This implies that all results about block-encodings — including Low and Chuang’s Hamiltonian simulation when the input is given as a blockencoding [LC16], and other techniques we develop in this paper — also apply to input presented in the quantum data structure model. This observation is the essential idea behind our applications. Implicit in work by Childs [Chi10] is the fact that, given $A$ in the sparse-access input model, there is an $\varepsilon$ -approximate block-encoding of $A$ that can be implemented in complexity $\mathsf { p o l y l o g } ( N / \varepsilon )$ , so our results also apply to the sparse-access input model. In fact, the block-encoding framework unifies a number of possible input models, and also enables one to work with hybrid input models, where some matrices may come from purifications of density operators, whereas other input matrices may be accessed through sparse oracles or a quantum data structure. For a very recent overview of these general techniques see e.g. [GSLW18].

We demonstrate the elegance of the block-encoding framework by showing how to combine and modify block-encodings to build up new block-encodings, similar to building new algorithms from existing subroutines. For example, given block-encodings of $A$ and $B ,$ their product yields a block-encoding of $A B$ . Given a block-encoding of a Hermitian $A$ , it is possible to construct a block-encoding of $e ^ { i A }$ , using which one can implement a block-encoding of $A ^ { - 1 }$ . We summarize these techniques in Section 1.1, and present them formally in Section 4.

To illustrate the elegance of the block-encoding framework, consider one of our applications: generalized least squares. This problem, defined in Section 1.2, requires that given inputs $\bar { \boldsymbol { X } } \in \mathbb { R } ^ { M \times N }$ , $\Omega \in \mathbb { R } ^ { M \times M }$ and $\vec { y } \in \mathbb R ^ { M }$ , we output a quantum state proportional to

$$
\vec { \beta } = ( X ^ { T } \Omega ^ { - 1 } X ) ^ { - 1 } X ^ { T } \Omega ^ { - 1 } \vec { y } .
$$

Given block-encodings of $\boldsymbol { X }$ and $\Omega$ , it is simple to combine them to get a block-encoding of $( X ^ { T } \Omega ^ { - 1 } X ) ^ { - 1 } X ^ { T } \Omega ^ { - 1 }$ , which can then be applied to a quantum state proportional to $\vec { y }$ .

Variable-time amplitude estimation. A variable-stopping-time quantum algorithm is a quantum algorithm $\mathcal { A }$ consisting of $m$ stages $\mathcal { A } = \mathcal { A } _ { m } \ldots \mathcal { A } _ { 1 }$ , where $A _ { j } A _ { j - 1 } \ldots A _ { 1 }$ has complexity $t _ { j } ,$ for $t _ { m } > \cdots > t _ { 1 } > 0$ . At each stage, a certain flag register, which we can think of as being initialized to a neutral symbol, may be marked as “good” in some branches of the superposition, or “bad” in some branches of the superposition, or left neutral. Each subsequent stage only acts non-trivially on those branches of the superposition in which the flag is not yet set to “good” or “bad”.

At the end of the algorithm, we would like to project onto that part of the final state in which the flag register is set to “good”. This is straightforward using amplitude amplification, however this approach may be vastly sub-optimal. If the algorithm terminates with amplitude $\sqrt { p _ { s u c c } }$ on the “good” part of the state, then standard amplitude amplification requires that we run $1 / \sqrt { p _ { s u c c } }$ rounds, each of which requires us to run the full algorithm $\mathcal { A }$ to generate its final state, costing $t _ { m } / \sqrt { p _ { s u c c } }$ .

To see why this might be sub-optimal, suppose that after $\boldsymbol { A } _ { 1 }$ , the amplitude on the part of the state in which the flag register is set to “bad” is already very high. Using amplitude amplification at this stage is very cheap, because we only have to incur the cost $t _ { 1 }$ of $\mathcal { A } _ { 1 }$ at each round, rather than running all of $\mathcal { A }$ . In [Amb12], Ambainis showed that given a variablestopping-time quantum algorithm, there exists an algorithm that approximates the “good” part of the algorithm’s final state in cost $\begin{array} { r } { \widetilde { \mathcal { O } } \left( t _ { m } + \sqrt { \sum _ { j = 1 } ^ { m } { \frac { p _ { j } } { p _ { s u c c } } } t _ { j } ^ { 2 } } \right) 4 } \end{array}$ , where $p _ { j }$ is the amplitude on the part of the state that is moved from neutral to “good” or “bad” during application of $A _ { j }$ (intuitively, the probability that the algorithm stops at stage $j )$ .

While amplitude amplification can easily be modified to not only project a state onto its “good” part, but also return an estimate of $p _ { s u c c }$ (i.e. the probability of measuring “good” given the output of $\mathcal { A }$ ), this is not immediate in variable-time amplitude amplification. The main difficulty is that a variable-time amplification algorithm applies a lot of subsequent amplification phases, where in each amplification phase the precise amount of amplification is a priori unknown. We overcome this difficulty by separately estimating the amount of amplification in each phase with some additional precision and finally combining the separate estimates in order to get a multiplicative estimate of $p _ { s u c c }$ .

In Section 3, we show in detail how to estimate the success probability of a variablestopping-time quantum algorithm to within a multiplicative error of $\varepsilon$ in complexity

$$
\widetilde { \mathcal { O } } \left( \frac { 1 } { \varepsilon } \left( t _ { m } + \sqrt { \sum _ { j = 1 } ^ { m } \frac { p _ { j } } { p _ { s u c c } } t _ { j } ^ { 2 } } \right) \right) .
$$

Meanwhile we also derive some logarithmic improvements to the complexity of variable-time amplitude amplification.

Applications. We give several applications of the block-encoding framework and variabletime amplitude estimation.

We first present a quantum weighted least squares solver (WLS solver), which outputs a quantum state proportional to the optimal solution to a weighted least squares problem, when the input is given either in the quantum data structure model of Kerenidis and Prakash, or the sparse-access input model. We remark that the sparse-access input model is perhaps less appropriate to the setting of data analysis, where we cannot usually assume any special structure on the input data, however, since our algorithm is designed in the block-encoding framework, it works for either input model. Our quantum WLS solver improves the dependence on the condition number from $\kappa ^ { 6 }$ in [KP17]5 to $\kappa _ { \iota }$ and the dependence on $\varepsilon$ from $1 / \varepsilon$ to polylog $( 1 / \varepsilon )$ .

We next present the first quantum generalized least squares solver (GLS solver), which outputs a quantum state proportional to the optimal solution to a generalized least squares problem. We again assume that the input is given in either the quantum data structure model or the sparse-access model. The complexity is again polynomial in $\log ( 1 / \varepsilon )$ and in the condition numbers of the input matrices.

Finally, we also build on the algorithms of Wang [Wan17a] to estimate effective resistance between two nodes of an electrical network and the power dissipated across a network when the input is given as a quantum data structure or in the sparse-access model. We estimate the norm of the output state of a certain linear system by applying the variable-time amplitude estimation algorithm. In the sparse-access model, we find that our algorithm outperforms Wang’s linear-system-based algorithm. In the quantum data structure model, our algorithms offer a speedup whenever the maximum degree of an electrical network of $n$ nodes is $\Omega ( n ^ { 1 / 3 } )$ .

Our algorithms also have a speedup over the quantum walk based algorithm by Wang in certain regimes.

We describe these applications in more detail in Section 1.2, and formally in Section 5.

Related Work. Independently of this work, recently, Wang and Wossnig [WW18] have also considered Hamiltonian simulation of a Hamiltonian given in the quantum data structure model, using quantum-walk based techniques from earlier work on Hamiltonian simulation [BCK15]. Their algorithm’s complexity scales as $\left. A \right. _ { 1 }$ (which they upper bound by $\sqrt { N }$ ; whereas our Hamiltonian simulation results (Theorem 26), which follow from Low and Chuang’s block-Hamiltonian simulation result, have a complexity that depends poly-logarithmically on the dimension, $N$ . Instead, our complexity depends on the parameter $\mu ,$ described below, which is also at most $\sqrt { N }$ . In principle, the Hamiltonian simulation result of [WW18] can also be used to implement a quantum linear systems solver, however the details are not worked out in [WW18].

# 1.1 Techniques for block-encodings

We develop several tools within the block-encoding framework that are crucial to our applications, but also likely of independent interest. Since an input given either in the sparse-access model or as a quantum data structure can be made into a block-encoding, our block-encoding results imply analogous results in each of the sparse-access and quantum data structure models.

In the following, let $\mu ( A )$ be one of: (1) $\mu ( A ) = \left\| A \right\| _ { F ^ { \prime } }$ , the Frobenius norm of $A$ , in which case the quantum data structures should encode $A$ ; or (2) for some $p \in [ 0 , 1 ] , \mu ( A ) = \sqrt { s _ { 2 p } ( A ) s _ { 2 ( 1 - p ) } ( A ) } ,$ where $s _ { p } ( A ) = \mathsf { m a x } _ { j } \| A _ { j , \cdot } \| _ { p ^ { \prime } } ^ { p }$ in which case the quantum data structures should encode both $A ^ { ( p ) }$ and $( A ^ { ( 1 - p ) } ) ^ { T }$ , defined by $\dot { A } _ { i , j } ^ { ( q ) } : = ( A _ { i , j } ) ^ { q }$ .

Hamiltonian simulation from quantum data structure. In Theorem 26, we prove the following. Given a quantum data structure for a Hermitian $A \in \mathbb { C } ^ { N \times N }$ such that $\left\| A \right\| \leq 1$ , we can implement $e ^ { i t A }$ in complexity $\widetilde { \mathcal { O } } ( t \mu ( A ) \mathsf { p o l y l o g } ( N / \varepsilon ) )$ . This follows from the quantum Hamiltonian simulation algorithm of Low and Chuang that expects the input as a block-encoding.  √ Independently, Wang and Wossnig have proven a similar result, with $\left\| A \right\| _ { 1 } \le \sqrt { N }$ in place of $\mu ( A )$ [WW18].

Quantum singular value estimation. In Ref. [KP16], Kerenidis and Prakash give a quantum algorithm for estimating the singular values of a matrix stored in a quantum data structure. In Theorem 27, we present an algorithm for singular value estimation of a matrix given as a block-encoding. In the special case when the block-encoding is implemented by a quantum data structure, we recover the result of [KP16].

Quantum linear system solver. Given a block-encoding of $A _ { i }$ , which is a unitary $U$ with $A / \alpha$ in the top left corner, for some $\alpha$ , we can implement a block-encoding of $A ^ { - 1 }$ (Lemma 9), which is a unitary $V$ with $A ^ { - 1 } / ( 2 \kappa )$ in the top left corner, where $\kappa$ is an upper bound $0 \mathsf { n } ^ { 6 } \parallel A ^ { - 1 } \parallel$ . Such a block-encoding can be applied to a state $| b \rangle$ to get $\begin{array} { r } { \frac { 1 } { 2 \kappa } | 0 \rangle ^ { \otimes a } ( A ^ { - 1 } | b \rangle ) + | 0 ^ { \perp } \rangle } \end{array}$ for some unnormalized state $| 0 ^ { \perp } \rangle$ orthogonal to every state with $| 0 \rangle$ in the first $a$ registers. Performing amplitude amplification on this procedure, we can approximate the state $A ^ { - 1 } | b \rangle / \big | \big | A ^ { - 1 } | b \rangle \big | \big |$ .

However, this gives quadratic dependence on the condition number of $A ,$ whereas only linear dependence is needed for quantum linear systems solvers in the sparse-access input model, thanks to the technique of variable-time amplitude amplification. Using this technique, we are able to show, in Theorem 30, that given a block-encoding of $A$ , we can approximate the state $A ^ { - 1 } | b \rangle / \big \| A ^ { - 1 } | b \rangle \big \|$ in time

$$
\widetilde { \mathcal { O } } \left( \alpha \kappa T _ { U } \log ^ { 3 } ( 1 / \varepsilon ) + \kappa T _ { b } \log ( 1 / \varepsilon ) \right) ,
$$

where $T _ { U }$ is the complexity of implementing the block-encoding of $A _ { i }$ , and $T _ { b }$ is the cost of a subroutine that generates $| b \rangle$ . From this, it follows that, given $A$ in a quantum data structure, we can implement a QLS solver in complexity

$$
\widetilde { \mathcal { O } } ( \kappa \mu ( A ) \mathsf { p o l y l o g } ( N / \varepsilon ) ) ,
$$

which we prove in Theorem 34.

Using our new technique of variable-time amplitude estimation, in Corollary 32, we also show how to compute a $( 1 \pm \varepsilon )$ -multiplicative estimate of $\left\| A ^ { - 1 } | b \rangle \right\|$ in complexity

$$
\widetilde { \mathcal { O } } \Bigl ( \frac { \kappa } { \varepsilon } ( \alpha T _ { U } + T _ { b } ) \Bigr ) .
$$

Negative powers of Hamiltonians. Finally, we generalize our QLS solver to apply $A ^ { - c }$ for any $c \in ( 0 , \infty )$ . Using variable-time amplification techniques we show in Theorem 33 that, if we have access to a unitary $U$ that block-encodes of $A ,$ , such that $A / \alpha$ is the top left block of $U ,$ and $U$ can be implemented in cost $T _ { U }$ , then we can generate $A ^ { - c } | b \rangle / \big | \big | A ^ { - c } | b \rangle \big | \big |$ in complexity

$$
\mathcal { O } \Big ( \alpha q \kappa ^ { q } T _ { U } \log ^ { 3 } ( 1 / \varepsilon ) + \kappa ^ { q } T _ { b } \log ( 1 / \varepsilon ) \Big )
$$

where $q = \mathsf { m a x } \{ 1 , c \}$ and $T _ { b }$ is the complexity of prepare $| b \rangle$ .

# 1.2 Application to least squares

Problem statements. The problem of ordinary least squares $( O L S )$ is the following. Given data points $\{ ( \vec { x } ^ { ( i ) } , y ^ { ( i ) } ) \} _ { i = 1 } ^ { M }$ for $\vec { x } ^ { ( 1 ) } , \dotsc , \vec { x } ^ { ( M ) } \in \bar { \mathbb { R } } ^ { N }$ and $\begin{array} { r } { \boldsymbol { y } ^ { ( 1 ) } , \ldots , \boldsymbol { y } ^ { ( M ) } \in \mathbb { R } , } \end{array}$ find $\vec { \beta } \in \mathbf { \mathbb { R } } ^ { N }$ that minimizes:

$$
\sum _ { i = 1 } ^ { M } ( \boldsymbol { y } ^ { ( i ) } - \vec { \beta } ^ { T } \vec { x } ^ { ( i ) } ) ^ { 2 } .
$$

The motivation for this task is the assumption that the samples are obtained from some process such that at every sample i, $\boldsymbol y ^ { ( i ) }$ depends linearly on $\vec { x } ^ { ( i ) }$ , up to some random noise, so $\boldsymbol { y } ^ { ( i ) }$ is drawn from a random variable $\vec { \beta } ^ { T } \dot { \vec { x } } ^ { ( i ) } + E _ { i } ,$ where $E _ { i }$ is a random variable with mean 0, for example, a Gaussian. The vector $\vec { \beta }$ that minimizes (1) represents a good estimate of the underlying linear function. We assume $M \geq N$ so that it is feasible to recover this linear function.

We can generalize this task to settings in which certain samples are thought to be of higher quality than others, for example, because the random variables $E _ { i }$ are not identical. We express this belief by assigning a positive weight $w _ { i }$ to each sample, and minimizing

$$
\sum _ { i = 1 } ^ { M } w _ { i } ( y ^ { ( i ) } - \vec { \beta } ^ { T } \vec { x } ^ { ( i ) } ) ^ { 2 } .
$$

Finding $\vec { \beta }$ given $X , ~ \vec { w }$ and $\vec { y }$ is the problem of weighted least squares (WLS).

We can further generalize to settings in which the random variables $E _ { i }$ for sample $i$ are correlated. In the problem of generalized least squares (GLS), the presumed correlations in error between pairs of samples are given in a symmetric non-singular covariance matrix $\Omega$ . We then want to find the vector $\vec { \beta }$ that minimizes

$$
\sum _ { i , j = 1 } ^ { M } \Omega _ { i , j } ^ { - 1 } ( y ^ { ( i ) } - \vec { \beta } ^ { T } \vec { x } ^ { ( i ) } ) ( y ^ { ( j ) } - \vec { \beta } ^ { T } \vec { x } ^ { ( j ) } ) .
$$

We will consider solving quantum versions of these problems. Specifically, a quantum WLS solver (resp. quantum GLS solver) is given access to $\vec { y } \in \mathbb R ^ { M }$ , $\boldsymbol { X } \in \dot { \mathbb { R } } ^ { M \times N }$ , and positive weights $w _ { 1 } , \ldots , w _ { M }$ (resp. $\Omega$ ), in some specified manner, and outputs an $\varepsilon$ -approximation of a quantum state $\begin{array} { r } { \sum _ { i } \beta _ { i } | i \rangle / \left\| \vec { \beta } \right\| , } \end{array}$ , where $\vec { \beta }$ minimizes the expression in (2) (resp. (3)).

Prior work. Quantum algorithms for least squares fitting were first considered in [WBL12]. They considered query access to $\boldsymbol { X }$ , and a procedure for outputting $\begin{array} { r } { | y \rangle = \sum _ { i } y _ { i } | i \rangle / \big | \big | \vec { y } \big | \big | } \end{array}$ , which we refer to as the sparse-access input model. They present a quantum OLS solver, outputting a state proportional to a solution $\dot { \boldsymbol { { \beta } } } _ { \iota }$ that runs in time $\widetilde { \mathcal { O } } \big ( \operatorname* { m i n } \big \{ \log ( M ) s ^ { 3 } \kappa ^ { 6 } / \varepsilon , \log ( M ) s \dot { \kappa ^ { 6 } } / \varepsilon ^ { 2 } \big \} \big \vert$ , where $s$ is the sparsity of $X$ , and $\kappa$ the condition number. To compute a state proportional to ${ \vec { \beta } } ,$ , they first apply $\hat { X } ^ { T }$ to $| y \rangle$ to get a state proportional to $X ^ { T } \vec { y }$ , using techniques similar to [HHL09]. They then apply $( X ^ { T } X ) ^ { - 1 }$ using the quantum linear system solving algorithm of [HHL09], giving a final state proportional to $( X ^ { T } X ) ^ { - 1 } X ^ { T } { \vec { y } } = X ^ { + } { \vec { y } }$ .

The approach of [WBL12] was later improved upon by [LZ17], who also give a quantum OLS solver in the sparse-access input model. Unlike [WBL12], they apply $X ^ { + }$ directly, by using Hamiltonian simulation of $\boldsymbol { X }$ and phase estimation to estimate the singular values of $\boldsymbol { X }$ , and then apply a rotation depending on the inverse singular value if it’s larger than 0, and using amplitude amplification to de-amplify the singular-value-zero parts of the state. This results in an algorithm with complexity $\tilde { \mathcal { O } } \big ( s \llcorner ^ { 3 } \log ( M + N ) / \varepsilon ^ { 2 } \big )$ .

Several works have also considered quantum algorithms for least squares problems with a classical output. The first, due to Wang [Wan17b], outputs the vector $\dot { \boldsymbol { { \beta } } }$ in a classical form. The input model should be compared with the sparse-access model — although $\vec { y }$ is given in classical random access memory, an assumption about the regularity of $\vec { y }$ means the quantum state $| y \rangle$ can be efficiently prepared. The algorithm also requires a regularity condition on the matrix $\boldsymbol { X }$ . The algorithm’s complexity is $\mathsf { o o l y } ( \mathsf { l o g } M , N , \kappa , \frac { 1 } { \varepsilon } )$ . Like [LZ17], Wang’s algorithm uses techniques from quantum linear system solving to apply $X ^ { + }$ directly to $\vert y \rangle$ . To do this, Hamiltonian simulation of $\boldsymbol { X }$ is accomplished via what we would call a block-encoding of $\boldsymbol { X }$ . This outputs a state proportional to $X ^ { + } \vec { y } ,$ , whose amplitudes can be estimated one-by-one to recover $\dot { \vec { \beta } }$ .

A second algorithm to consider least squares with a classical output is [SSP16], which does not output ${ \vec { \beta } } ,$ , but rather, given an input ${ \vec { x } } ,$ outputs $\vec { x } ^ { T } \vec { \beta }$ , thus predicting a new data point. This algorithm requires that $\vec { x } , \vec { y } _ { i }$ , and even $\boldsymbol { X }$ be given as quantum states, and assumes that $\boldsymbol { X }$ has low approximate rank. The algorithm uses techniques from quantum principal component analysis [LMR14], and runs in time $\mathcal { O } \big ( \mathsf { l o g } ( N ) \kappa ^ { 2 } / \varepsilon ^ { 3 } \big )$ .

Recently, Kerenidis and Prakash introduced the quantum data structure input model [KP16]. This input model fits data analysis tasks, because unlike in more abstract problems such as Hamiltonian simulation, where the input matrix may be assumed to be sparse and wellstructured so that we can hope to have implemented efficient subroutines to find the non-zero entries of the rows and columns, the input to least squares is generally noisy data for which we may not assume any such structure. In Ref. [KP17], utilizing this data structure, they solve the quantum version of the weighted least squares problem. Their algorithm assumes access to quantum data structures storing $\boldsymbol { X }$ , or some closely related matrix (see Section 2.2),  $W = \mathsf { d i a g } ( \vec { w } )$ , and ${ \vec { y } } ,$ and have running time $\widetilde { \mathcal { O } } \left( \frac { \kappa ^ { 6 } \mu } { \varepsilon } \mathsf { p o l y l o g } ( M N ) \right)$ , where $\kappa$ is the condition number of $\chi ^ { T } \sqrt { W }$ , and $\mu$ is some prior choice of $\left\| X ^ { T } \sqrt { W } \right\| _ { F }$ or $\sqrt { s _ { 2 p } ( X ^ { T } \sqrt { W } ) s _ { 2 ( 1 - p ) } ( X ^ { T } \sqrt { W } ) }$ for some $p \in [ 0 , 1 ] ^ { 7 }$ . Note that the choice of $\mu$ impacts the way $\boldsymbol { X }$ must be encoded, leading to a family of algorithms requiring slightly different encodings of the input.

Our results. We give quantum WLS and GLS solvers in the model where the input is given as a block-encoding. As a special case, we get quantum WLS and GLS solvers in the quantum data structure input model of Kerenidis and Prakash. Our quantum WLS solver has complexity

$$
\widetilde { \mathcal { O } } ( \mu \kappa \mathsf { p o l y l o g } ( M N / \varepsilon ) ) . ^ { 8 }
$$

This is a 6-th power improvement in the dependence on $\kappa$ , and an exponential improvement in the dependent on $1 / \varepsilon$ as compared with the quantum WLS solver of [KP17]. Our quantum WLS solver is presented in Section 5.1.1, Theorem 35. Since our algorithm is designed via the block-encoding framework, we also get an algorithm in the sparse-access input model with the same complexity, where $\mu$ is replaced by $S _ { \nu }$ , the sparsity. As a special case we get a quantum OLS solver, which compares favourably to previous quantum OLS solvers in the sparse-access model [WBL12, LZ17] in having a linear dependence on $\kappa ,$ and a polylog $( 1 / \varepsilon )$ dependence on the precision. However, these previous results rely on QLS solver subroutines which have since been improved, so their complexity can also likely be improved.

In addition, we give the first quantum GLS solver. We first show how to implement a GLS solver when the inputs are given as block-encodings (Theorem 36). As a special case, we get a quantum GLS solver in the quantum data structure input model (Corollary 39), with complexity

$$
\widetilde { \mathcal { O } } ( \kappa _ { X } \kappa _ { \Omega } ( \mu _ { X } + \mu _ { \Omega } \kappa _ { \Omega } ) \mathrm { p o l y l o g } ( M N / \varepsilon ) ) , ^ { \mathrm { ~ 9 ~ } }
$$

where $\kappa _ { \Omega }$ and $\kappa \chi$ are the condition numbers of $\Omega$ and $\boldsymbol { X }$ , and $\mu _ { \Omega }$ and $\mu _ { X }$ are quantities that depend on how the input is given, as in the case of WLS. As before, since our algorithm is designed via the block-encoding framework, we also get an algorithm in the sparse-access input model with the same complexity, replacing $\mu \chi$ and $\mu _ { \Omega }$ with the respective sparsities of $\boldsymbol { X }$ and $\Omega$ . For details, see Section 5.1.2.

# 1.3 Application to estimating electrical network quantities

Problem statements. An electrical network is a weighted graph $G ( V , E , w )$ of $| V | = N$ vertices and $| E | = M$ edges, with the weight of each edge $W _ { e }$ being the inverse of the resistance (conductance) between the two underlying nodes. Given an external current input to the network, represented by a vector spanned by the vertices of the network, we consider the problem of estimating the power dissipated in the network, up to a multiplicative error $\varepsilon$ . A special case of this, where the external current just has a unit entering at vertex $S$ and leaving at vertex $t$ is the effective resistance between $S$ and $t$ .

The electrical networks we consider here can be dense, i.e. the maximum degree of the network, $d$ , can scale with $N$ . In addition to considering the sparse-access input model, we consider the quantum data structure input model, i.e. we assume that certain matrices representing the network are stored in a quantum-accessible data structure.

Prior work. Electrical networks have previously been studied in several quantum algorithmic contexts. Belovs [Bel13] established a relationship between the problem of finding a marked node in a graph by a quantum walk and the effective resistance of the graph. Building on this work, several other quantum algorithms have been developed $[ { \mathsf { B C } } ] ^ { + } 1 3 ,$ Mon15, MLM17].

Ref. [IJ16] gave a quantum algorithm for estimating the effective resistance between two nodes in a network when the input is given in the adjacency query model. This allows one to query the $i j$ -th entry of the adjacency matrix, in contrast to what we are referring to as the sparse-access model, in which one can query the $i .$ -th nonzero entry of the $j .$ -th row. They considered the unweighted case, where all conductances are in $\{ 0 , 1 \}$ , and showed how to estimate the effective resistance between two nodes, $R _ { s , t } ,$ to multiplicative accuracy $\varepsilon$ in complexity:

$$
\mathcal { \widetilde O } \left( \operatorname* { m i n } \left\{ \frac { N \sqrt { R _ { s , t } } } { \epsilon ^ { 3 / 2 } } , \frac { N \sqrt { R _ { s , t } } } { \epsilon \sqrt { d \lambda } } \right\} \right) ,
$$

where $\lambda$ is the spectral gap of the normalized Laplacian.

Wang [Wan17a] presented two quantum algorithms for estimating certain quantities in large sparse electrical networks: one based on the quantum linear system solver for sparse matrices by [CKS17], the other based on quantum walks. Using both of these algorithms, Wang estimates the power dissipated, the effective resistance between two nodes, the current across an edge and the voltage between two nodes. Wang’s algorithms work in the sparse-access input model, in which the algorithm accesses the input by querying the $i .$ -th neighbour of the $j .$ -th vertex, for $i \in [ d ]$ and $j \in [ N ] ,$ where $d$ is the maximum degree.

In particular, we focus on the problems of approximating the power dissipated in a network and the effective resistance between two nodes. If the maximum edge weight of the network is $W _ { \mathrm { { I n a x } } }$ and $\lambda$ is the spectral gap of the normalized Laplacian of the network, then Wang’s first algorithm for solving these tasks is based on solving a certain quantum linear system and then estimating the norm of the output state by using amplitude estimation. The resulting complexity is

$$
\widetilde { \mathcal { O } } \left( \frac { w _ { \mathrm { m a x } } d ^ { 2 } } { \lambda \epsilon } \mathfrak { p o l y l o g } ( N ) \right) .
$$

On the other hand, the quantum walk based algorithm by Wang solves these problems in complexity

$$
\widetilde { \mathcal { O } } \left( \operatorname* { m i n } \left\{ \frac { \sqrt { w _ { \mathrm { m a x } } } d ^ { 3 / 2 } } { \lambda \epsilon } , \ : \frac { w _ { \mathrm { m a x } } \sqrt { d } } { \lambda ^ { 3 / 2 } \epsilon } \right\} \mathrm { p o l y l o g } ( N ) \right) .
$$

Our results. Using the block-encoding framework, we give algorithms that improve on Wang’s sparse-access input model algorithms for certain parameters, and in addition, we give the first quantum algorithms for estimating the effective resistance between two nodes and the power dissipated by the network in the quantum data structure input model, where the weighted vertex-edge incidence matrix of the electrical network, as well as the input current vector, are given as a quantum data structure.

Our algorithms are based on the quantum-linear-system-solver-based algorithms of Wang. As described in Section 5.2, we replace the quantum linear systems algorithm used by Wang, which assumes sparse access to the input [CKS17], with the QLS solver that we develop here, which assumes the input is given as a block-encoding. We also replace standard amplitude estimation with variable time amplitude estimation. As such, we are not only able to improve upon Wang’s algorithms in the sparse-access model, but also provide new algorithms for the same problem in the quantum data structure model.

In Corollary 44, we prove that in the sparse-access input model, there is a quantum algorithm for estimating the dissipated power (or as a special case, the effective resistance) to an $\varepsilon$ -multiplicative error in complexity

$$
\widetilde { \mathcal { O } } \left( \frac { d ^ { 3 / 2 } } { \epsilon } \sqrt { \frac { w _ { \mathrm { m a x } } } { \lambda } } \mathrm { p o l y l o g } ( N ) \right) .
$$

Thus our algorithm always outperforms the linear-systems based algorithm by Wang. As compared to the quantum-walk based-algorithm:

(i) When $d < \sqrt { w _ { \sf m a x } / \lambda } ,$ we have a speedup of $\widetilde { \mathcal { O } } \left( 1 / { \sqrt { \lambda } } \right)$ .

(ii) When $d > \sqrt { w _ { \sf m a x } / \lambda } ,$ we have a speedup as long as $\sqrt { w _ { \mathrm { m a x } } / \lambda } < d < \sqrt { w _ { \mathrm { m a x } } } / \lambda .$

In comparison to the algorithm of Ref. [IJ16], our algorithm (in the sparse-access input model) has a speedup as long as $R _ { s , t } \gg d ^ { 4 } / N ^ { 2 }$ , although we note that these results are not directly comparable, as they assume very different input models.

In Corollary 45, we give the first quantum algorithm for estimating the dissipated power (or as a special case, the effective resistance) in the quantum data structure model, with complexity:

$$
\widetilde { \mathcal { O } } \left( \frac { 1 } { \varepsilon } \sqrt { \frac { d w _ { \mathrm { m a x } } N } { \lambda } } \right) .
$$

This algorithm outperforms the quantum-linear-system-based algorithms by Wang for both these tasks when the maximum degree of the electrical network is $\mathsf { \bar { O } } ( N ^ { 1 / 3 } )$ . On the other hand, as compared to the quantum walk based algorithm:

(i) When $d < \sqrt { w _ { \sf m a x } / \lambda } ,$ we have a speedup as long as $\lambda < d ^ { 2 } / N$ .   
(ii) When $d > \sqrt { w _ { \sf m a x } / \lambda } ,$ we have a speedup as long as $\lambda < \sqrt { w _ { \sf m a x } / N }$ .

In comparison to the algorithm for estimating effective resistance in the adjacency query model from Ref. [IJ16], we get an improvement whenever $\lambda = \Omega ( 1 )$ and $R _ { s , t } \gg d ^ { 2 } / N$ .

We emphasize that our algorithm in Corollary 45 is not directly comparable to any of these previous results, since the input models are different.

# 2 Preliminaries

# 2.1 Notation

We begin by introducing some notation. For $A \in \mathbb { C } ^ { M \times N }$ , define $\overline { { A } } \in \mathbb { C } ^ { ( M + N ) \times ( M + N ) }$ by

$$
\overline { { A } } = \biggl [ \begin{array} { c c } { { 0 } } & { { A } } \\ { { A ^ { \dagger } } } & { { 0 } } \end{array} \biggr ] .
$$

For many applications where we want to simulate $A$ , or a function of $A$ , it suffices to simulate $\overline { { A } }$

For $A \in \mathbb { C } ^ { N \times N }$ , we define the following norms:

• Spectral norm: $\left\| A \right\| = \mathsf { m a x } \{ \left\| A | u \rangle \right\| : \left\| | u \rangle \right\| = 1 \}$ • Frobenius norm: $\left\| A \right\| _ { F } = \sqrt { \sum _ { i , j } A _ { i , j } ^ { 2 } }$

For $A \in \mathbb { C } ^ { M \times N }$ , let $A _ { i , }$ · denote the $i .$ -th row of $A$ $, \mathsf { r o w } ( A )$ the span of the rows of $A$ , and $\mathsf { c o l } ( A ) = \mathsf { r o w } ( A ^ { T } )$ . Define the following:

• For $q \in [ 0 , 1 ] , s _ { q } ( A ) = \mathsf { m a x } _ { i \in M } \bigl \| A _ { i , \cdot } \bigr \| _ { q } ^ { q }$   
• For $p \in [ 0 , 1 ] , \mu _ { p } ( A ) = \sqrt { s _ { 2 p } ( A ) s _ { 2 ( 1 - p ) } ( A ^ { T } ) }$   
• $\sigma _ { \operatorname* { m i n } } ( A ) = \operatorname* { m i n } \{ | | A | u  | | : | u  \in \operatorname { r o w } ( A ) , | | { u }  | | = 1 \}$ (the smallest non-zero singular value)   
• $\sigma _ { \operatorname* { m a x } } ( A ) = \operatorname* { m a x } \{ | | A | u  | \colon | | | u  | | = 1 \}$ (the larges singular value)   
• $\left\| A \right\| = \left\| { \overline { { A } } } \right\| = \sigma _ { \operatorname* { m a x } } ( A )$

For $A \in \mathbb { C } ^ { M \times N }$ with singular value decomposition $\begin{array} { r } { A = \sum _ { i } \sigma _ { i } | u _ { i } \rangle \langle v _ { i } | } \end{array}$ , we define the Moore-Penrose pseudoinverse of $A$ b $\textstyle { \mathfrak { y } } \ A ^ { + } = \sum _ { i } \sigma _ { i } ^ { - 1 } | v _ { i } \rangle \langle u _ { i } |$ . For a matrix $A _ { i }$ , we let $A ^ { ( p ) }$ be defined $A _ { i , j } ^ { ( p ) } = ( A _ { i , j } ) ^ { p }$ .

# 2.2 Quantum-accessible data structure

We will consider the following data structure, studied in [KP16]. We will refer to this data structure as a quantum-accessible data structure, because it is a classical data structure, which, if stored in QROM, is addressable in superposition, but needn’t be able to store a quantum state, facilitates the implementation of certain useful quantum operations. In our complexity analysis, we consider the cost of accessing a QROM of size $N$ to be $\mathsf { p o l y l o g } ( N )$ . Although this operation requires order $N$ gates [GLM08, $\mathsf { A C l O ^ { + } } 1 5 ]$ , but the gates can be arranged in parallel such that the depth of the circuit indeed remains polylog $( N )$ .

The following is proven in [KP16]. We include the proof for completeness.

Theorem 1 (Implementing quantum operators using an efficient data structure [KP16]). Let $A \in \mathbb { R } ^ { M \times N }$ be a matrix with $A _ { i j } \in \mathbb { R }$ being the entry of the i-th row and the $j$ -th column. If w is  the number of non-zero entries of $A$ , then there exists a data structure of $s i z e ^ { 1 0 } \mathcal { O } \left( w \log ^ { 2 } ( M N ) \right)$ that, given the entries $( i , j , A _ { i j } )$ in an arbitrary order, stores them such that time10 taken to store each entry of $A$ is $\mathcal { O } ( \log ( M N ) )$ . Once this data structure has been initiated with all non-zero entries of $A ,$ there exists a quantum algorithm that can perform the following maps with $\varepsilon$ -precision in $\mathcal { O } ( p o l y l o g ( M N / \varepsilon ) )$ time:

$$
\widetilde { U } : | i \rangle | 0 \rangle \mapsto | i \rangle \frac { 1 } { \left\| \boldsymbol { A } _ { i , \cdot } \right\| } \sum _ { j = 1 } ^ { N } \boldsymbol { A } _ { i , j } | j \rangle = | i , \boldsymbol { A } _ { i } \rangle ,
$$

$$
\widetilde { V } : | 0 \rangle | j \rangle \mapsto \frac { 1 } { \left. A \right. _ { F } } \sum _ { i = 1 } ^ { M } \bigl \Vert A _ { i , \cdot } \bigr \Vert | i \rangle | j \rangle = \bigl | \widetilde { A } , j \bigr \rangle ,
$$

where $\left| A _ { i , \cdot } \right.$ is the normalized quantum state corresponding to the i-th row of $A$ and $| \widetilde { A } \rangle$ is $a$ normalized quantum state such that $\langle i | \widetilde { A } \rangle = \left. A _ { i , \cdot } \right.$ , i.e. the norm of the $i$ -th row of $A$ .

In particular, given a vector $\vec { v } \in \mathbb R ^ { M \times 1 }$ stored in this data structure, we can generate an $\varepsilon$ -approximation of the superposition $\textstyle \sum _ { i = 1 } ^ { M } v _ { i } | i \rangle / \left| \left| \vec { v } \right| \right|$ in complexity polylog $( M / \varepsilon )$ .

Proof. The idea is to have a classical data structure to which the quantum algorithm has access. The data structure includes an array of $M$ full binary trees, each having $N$ leaves. For the incoming entry $( A _ { i j } , i , j )$ , the tuple $\left( A _ { i , j } ^ { 2 } , \mathsf { s i g n } ( A _ { i j } ) \right)$ is stored in leaf $j$ of binary tree $B _ { i }$ . An internal node way, the root $l$ stores the s binary tree of the entries of tcontains the entry in the subtree rooted at . Let the value of any inte $l .$ . In thisal node $B _ { i }$ $\textstyle \sum _ { j = 1 } ^ { N } A _ { i , j } ^ { 2 } .$ of at depth be denoted by $B _ { i , l }$ . Then if $j _ { b }$ represents the -th bit of $j ,$ then

$$
B _ { i , l } = \sum _ { j _ { 1 } \ldots j _ { d } = l ; \atop j _ { d + 1 } \ldots j _ { \mathsf { l o g } ( N ) } \in \{ 0 , 1 \} } A _ { i , j } ^ { 2 } .
$$

This implies that the first $d$ bits of $j$ written in binary is fixed to $l ,$ indicating that we are at depth $d$ . So whenever a new entry comes in, all nodes of the binary tree corresponding to the entry gets updated. In the end the root stores $\left\| A _ { i , \cdot } \right\| ^ { 2 }$ . As there are at most $\mathcal { O } ( \log N )$ nodes from the leaf to the root of any binary tree and to find the address of each entry takes $\mathcal { O } ( \log ( M N ) )$ , inserting each entry into this data structure takes $\mathcal { O } ( \log ^ { 2 } ( M N ) )$ time. If there are $w$ non-zero entries in $A _ { i }$ , then the memory requirement of this data structure is $\mathcal { O } ( w \log ^ { 2 } ( M N ) )$ , because each entry can cause $\lceil \log ( N ) \rceil$ new nodes to be added, each of which require $\mathcal { O } ( \log ( M N ) )$ registers.

To construct the unitary $\widetilde { U }$ in $\mathcal { O } ( \vert \boldsymbol { \mathsf { p o l y l o g } } ( M N / \varepsilon ) )$ time, quantum access to this data structure is required. A sequence of controlled-rotations is performed, similarly to the ideas of [GR02]. For any internal node $B _ { i , l }$ at depth $d$ , conditioned on the first register being $| i \rangle$ and the first $d$ qubits of the second register being equal to $l ,$ the following rotation is made to the $( d + 1 )$ -th qubit

$$
| i \rangle | l \rangle | 0 . . . . 0 \rangle \mapsto | i \rangle | l \rangle \frac { 1 } { \sqrt { B _ { i , l } } } \left( \sqrt { B _ { i , 2 l } } | 0 \rangle + \sqrt { B _ { i , 2 l + 1 } } | 1 \rangle \right) | 0 . . . . 0 \rangle .
$$

For the last qubit, i.e. the $\lceil \log ( n ) \rceil$ -th qubit, the sign of the entry is also included

$$
| i \rangle | l \rangle | 0 \rangle \mapsto | i \rangle | l \rangle \frac { 1 } { \sqrt { B _ { i , l } } } \left( \mathsf { s i g n } ( a _ { 2 l } ) \sqrt { B _ { i , 2 l } } | 0 \rangle + \mathsf { s i g n } ( a _ { 2 l + 1 } ) \sqrt { B _ { i , 2 l + 1 } } | 1 \rangle \right) .
$$

So performing $\widetilde { U }$ requires $\lceil \log ( N ) \rceil$ controlled rotations and for each of which two queries to the classical database is made to query the children of the node under consideration. Discretization errors can be nicely bounded and one can see that an $\varepsilon$ -approximation of $\widetilde { U }$ can be implemented in $\mathcal { O } ( \vert \boldsymbol { \mathsf { p o l y l o g } } ( M N / \varepsilon ) )$ time.

To implement $\widetilde { V }$ , we require an additional binary tree $\boldsymbol { B }$ having $M$ leaf nodes. Leaf $j$ stores the entry of the root of binary tree $B _ { j }$ . As before, all internal nodes $l$ store the sum of the entries of the subtree rooted at $l .$ So just as before, by applying $\lceil \log ( M ) \rceil$ controlled rotations, each of which queries the database twice, we can implement an $\varepsilon$ -approximation of $\widetilde { V }$ in $\mathcal { O } ( \vert \boldsymbol { \mathsf { p o l y l o g } } ( M N / \varepsilon ) )$ time.

Preparation of quantum states: Note that this data structure is also useful for preparing a quantum state when the entries of a classical vector arrive in an online manner. Formally speaking, if $\vec { v } \in \mathbb R ^ { M }$ is a vector with $i .$ -th entry $V _ { i }$ , then using the quantum-accessible data structure described above, one can prepare the quantum state $\begin{array} { r } { | \vec { \nu } \rangle = \overset { \cdot } { \underset { \left\| \vec { v } \right\| } { \sum } } \sum _ { i } { \nu _ { i } | i \rangle } } \end{array}$ . The idea is similar to the case of a matrix. One can store the tuple $\big ( \boldsymbol { v } _ { i } ^ { 2 } , \mathsf { s i g n } ( \boldsymbol { v } _ { i } ) \big )$ in the $i .$ -th leaf of a binary tree. As before, any internal node $l$ stores the sum of squares of the entries of the subtree rooted at l. So, we can use the same unitary $\widetilde { U }$ as before to obtain $| \vec { \nu } \rangle$ .

As a corollary, we have the following, which allows us to generate alternative quantum state representations of the rows of $A$ , as long as we have stored $A$ appropriately beforehand:

Corollary 2. $I f A ^ { ( p ) }$ is stored in a quantum data structure, then there exists a quantum algorithm that can perform the following map with $\varepsilon$ -precision in polylog $( M N / \varepsilon )$ time:

$$
| i \rangle | 0 \rangle \mapsto | i \rangle \frac { 1 } { s _ { 2 p } ( A ) } \sum _ { j = 1 } ^ { N } A _ { i , j } ^ { p } | j \rangle .
$$

In Section 4 we show that using these techniques one can efficiently implement a blockencoding of the matrix $A _ { i }$ , as defined below.

# 2.3 Unitary block-encoding of matrices

We will take advantage of recent techniques in Hamiltonian simulation [LC16, LC17], which enable us to present our results in a nice unified framework. The presented techniques give rise to exponential improvements in the dependence on precision in several applications. In this framework we will represents a subnormalised matrix as the top-left block of a unitary.

$$
U = \left( \begin{array} { c c } { { A / \alpha } } & { { . } } \\ { { . } } & { { . } } \end{array} \right)
$$

Following the exposition of Gilyén et al. [GSLW18] we use the following definition:

Definition 3 (Block-encoding). Suppose that $A$ is an $s$ -qubit operator, $\alpha , \varepsilon \in \mathbb { R } _ { + }$ and $a \in \mathbb { N }$ . Then we say that the $( s + a )$ -qubit unitary $U$ is an $( \alpha , a , \varepsilon )$ -block-encoding $\uparrow \uparrow$ of $A ,$ if

$$
\left\| A - \alpha ( \langle 0 | ^ { \otimes a } \otimes I ) U ( | 0 \rangle ^ { \otimes a } \otimes I ) \right\| \leq \varepsilon .
$$

Block-encodings are really intuitive to work with. For example, one can easily take the product of two block-encoded matrices by keeping their ancilla qubits separately. The following lemma shows that the errors during such a multiplication simply add up as one would expect, and the block-encoding does not introduce any additional errors.

Lemma 4 (Product of block-encoded matrices). If $U$ is an $( \alpha , a , \delta )$ -block-encoding of an $s$ -qubit operator $A ,$ and $V$ is a $( \beta , b , \varepsilon )$ -block-encoding of an $s$ -qubit operator B then12 $( I _ { b } \otimes U ) ( I _ { a } \otimes V )$ is an $( \alpha \beta , a + b , \alpha \varepsilon + \beta \delta )$ -block-encoding of $A B$ .

Proof.

$$
\begin{array} { r l } & { \quad \left\| A B - \alpha \beta ( \langle 0 | ^ { \otimes \alpha + b } \otimes I \rangle ( I _ { b } \otimes U ) ( I _ { a } \otimes V ) ( | 0 \rangle ^ { \otimes \alpha + b } \otimes I ) \right\| } \\ & { = \left\| A B - \underbrace { \alpha ( \langle 0 | ^ { \otimes \alpha } \otimes I \rangle U ( | 0 \rangle ^ { \otimes \alpha } \otimes I ) } _ { \bar { A } } \beta \langle \langle 0 | ^ { \otimes b } \otimes I \rangle V ( | 0 \rangle ^ { \otimes b } \otimes I ) \right\| } \\ & { = \left\| A B - \bar { A } B + \bar { A } B - \bar { A } \bar { B } \right\| } \\ & { = \left\| ( A - \bar { A } ) B + \bar { A } ( B - \bar { B } ) \right\| } \\ & { = \left\| A - \bar { A } \right\| \beta + \alpha \left\| B - \bar { B } \right\| } \\ & { \leq \alpha \varepsilon + \beta \delta . } \end{array}
$$

The above lemma assumes that both matrices are of size $2 ^ { s } \times 2 ^ { s }$ . This is in fact without loss of generality, if the two matrices have size say $M \times N$ and $N \times K$ where $M , N , K \leq 2 ^ { s }$ we can simply “pad” the matrices with zero entries, which does not affect the result of the matrix product.

Also the above lemma can be made more efficient in some cases when both $A$ and $B$ are significantly subnormalized. In such a situation we can first amplify the block-encodings and then only after that take their product. This improvement is based on the fact a subnormalized block-encoding can be efficiently amplified, as shown by Low and Chuang [LC17] and Gilyén et al. [GSLW18]. The precise argument can be found in Appendix A.

Lemma 5. (Poduct of preamplified block-matrices [LC16]) Let $A ~ \in ~ \mathbb { R } ^ { M \times N }$ and $B \in \mathbb { R } ^ { N \times K }$ such that $\left\| A \right\| \leq 1 , \left\| B \right\| \leq 1$ . $I f \ \alpha \ \geq \ 1$ and $U$ is a $( \alpha , a , \delta )$ -block-encoding of $A$ that can be implemented in time $T _ { U }$ ; $\beta \geq 1$ and $V$ is a $( \beta , b , \varepsilon )$ -block-encoding of $B$ that can be implemented in time $T _ { V } ,$ , then there is a $( 2 , a + b + 2 , \sqrt { 2 } ( \delta + \varepsilon + \gamma ) )$ -block-encoding of AB that can be implemented in time $\mathcal { O } ( ( \alpha ( T _ { U } + a ) + \beta ( T _ { V } + b ) ) \log ( 1 / \gamma ) )$ .

Also note that if we have a block-encoding for $A$ , it can be easily converted to a blockencoding of $\overline { { A } }$ , as shown by the following lemma.

Lemma 6 (Complementing block-encoded matrices). Let $U$ is be an $( \alpha , a , \delta )$ -block-encoding of an $S$ -qubit operator $A ,$ , and let cU denote the $( a + 1 + s )$ -qubit controlled- $U$ operator, that acts on the first a and last s qubits controlled on the $( a + 1 ) s t$ qubit. Then ${ \mathrm { c } } U ^ { \dagger } ( I _ { a } \otimes X \otimes I _ { s } ) { \mathrm { c } } U$ is an $( \alpha , a + 1 , \delta )$ -block-encoding of $\overline { { A } }$ .

The following theorem about block-Hamiltonian simulation is a corollary of the results of [LC16, Theorem 1], which also includes bounds on the propagation of errors. For more details see Appendix A.1.

Theorem 7. (Block-Hamiltonian simulation [LC16]) Suppose that $U$ is an $\left( \alpha , a , \varepsilon / | 2 t | \right)$ -blockencoding of the Hamiltonian $H$ . Then we can implement an $\varepsilon$ -precise Hamiltonian simulation unitary $V$ which is an $( 1 , a + 2 , \varepsilon )$ -block-encoding of $e ^ { i t H } .$ , with $\mathcal { O } ( | \alpha t | + \log ( 1 / \varepsilon ) )$ uses of controlled- $U$ or its inverse and with $\mathcal { O } ( a | \alpha t | + a \log ( 1 / \varepsilon ) )$ two-qubit gates.

From this, we can prove the following useful statement (proven in Appendix A.2 as Lemma 52).

Lemma 8 (Implementing controlled Hamiltonian simulation operators). Let $T = 2 ^ { J }$ for some $J \in \mathbb { N }$ and $\epsilon \geq 0$ . Suppose that $U$ is an $( \alpha , a , \varepsilon / | 8 ( J + 1 ) ^ { 2 } T | )$ -block-encoding of the Hamiltonian $H$ . Then we can implement a $( 1 , a + 2 , \varepsilon )$ -block-encoding of $\sum _ { t = 1 } ^ { T - 1 } | t \rangle \langle t | \otimes e ^ { i t H }$ , with $\mathcal { O } ( \alpha T + J \log ( J / \varepsilon ) )$ uses of controlled- $U$ or its inverse and with $\mathcal { O } ( a ( \alpha T + J \log ( J / \varepsilon ) ) )$ two-qubit gates.

Apeldoorn et al. developed some general techniques [AGGW17, Appendix B] that make it possible to implement smooth-functions of a Hamiltonian $H$ , accessing $H$ only via controlled-Hamiltonian simulation. Using their techniques, we show in Appendix A.2 the following results about implementing negative and positive powers of Hermitian matrices.

Lemma 9. (Implementing negative powers of Hermitian matrices) Let  $H$ Herm atrix such that $I / \kappa \preceq H \preceq I .$ Suppose that $\begin{array} { r } { \delta = o \left( \varepsilon / \left( \kappa ^ { 1 + c } ( 1 + c ) \log ^ { 3 } \frac { \kappa ^ { 1 + c } } { \varepsilon } \right) \right) } \end{array}$ $c \in ( 0 , \infty ) , \kappa \geq 2 ,$ , and let , $U$ $( \alpha , a , \delta )$ $H _ { \ast }$ $T _ { U }$ Then for any $\varepsilon ,$ we can implement $a$ unitary $\widetilde { U }$ that is a $( 2 \kappa ^ { c } , a + \mathcal { O } \big ( \log ( \kappa ^ { 1 + c } \log \frac { 1 } { \varepsilon } \big ) , \varepsilon \big ) -$ blockencoding of $H ^ { - c }$ in cost

$$
\mathcal { O } ( \alpha \kappa ( a + T _ { U } ) ( 1 + c ) \log ^ { 2 } ( \frac { \kappa ^ { 1 + c } } { \varepsilon } ) ) .
$$

Lemma 10. (Implementing positive powers of Hermitian matrices) Let $c \in ( 0 , 1 ] , \kappa \geq 2 ,$ and $H$ a Hermitian matrix such that $I / \kappa \preceq H \preceq I .$ Suppose that for $\delta = o \left( \varepsilon / ( \kappa \log ^ { 3 } \frac { \kappa } { \varepsilon } ) \right) .$ , and we are given a unitary $U$ that is an $( \alpha , a , \delta )$ -block-encoding of $H$ , that can be implemented using $T _ { U }$ elementary gates. Then for any $\varepsilon ,$ , we can implement $a$ unitary $\widetilde { U }$ that is $a$ $( 2 , a +$ $\mathcal { O } ( \log \log ( 1 / \varepsilon ) ) , \varepsilon )$ -block-encoding of $H ^ { c }$ in cost

$$
\mathcal { O } \left( \alpha \kappa ( a + T _ { U } ) \log ^ { 2 } ( \kappa / \varepsilon ) \right) .
$$

Finally, we note that subsequent work of Gilyén et al. [GSLW18] improved the log factor of the above two lemmas quadratically, and reduced the ancilla space overhead to a constant. This also directly implies an improvement in the log factors of the results presented in Section 4.

# 2.4 Sparse-access input model

In the sparse-access model we assume that the input matrix $A \in \mathbb { C } ^ { M \times N }$ has $S _ { r }$ -sparse rows and $S _ { C }$ -sparse columns, such that the matrix elements can be queried via an oracle

$$
\mathrm { O } _ { { \cal A } } \colon | i \rangle | j \rangle | 0 \rangle ^ { \otimes b } \mapsto | i \rangle | j \rangle | a _ { i j } \rangle \qquad \forall i \in [ M ] , j \in [ N ] .
$$

Moreover, the indices of non-zero elements of each row can be queried via an oracle

$$
0 _ { r } \colon | i \rangle | k \rangle \mapsto | i \rangle | r _ { i k } \rangle \qquad \forall i \in [ N ] , k \in [ s _ { r } ] , \mathrm { ~ w h e r e }
$$

$r _ { i j }$ is the index for the $j .$ -th non-zero entry of the $i .$ -th row of $A$ , or if there are less than i non-zero entries, then it is $j + N _ { \astrosun }$ . If $A$ is not symmetric (or Hermitian) then we also assume the analogous oracle for columns. It is not difficult to prove [Chi10] that a block-encoding of $A$ can be efficiently implemented in the sparse-access input model, see [GSLW18, Lemma 48] for a direct proof.

Lemma 11 (Constructing block-encodings for sparse-access matrices [GSLW18, Lemma 48]). Let $A \in \mathbb { C } ^ { M \times N }$ be an $s ^ { r } , s ^ { c }$ row and column-sparse matrix given in the sparse-access input√ model. Then for any $\varepsilon \in ( 0 , 1 )$ , we can implement $a$ $( \sqrt { s ^ { r } s ^ { c } }$ , $\mathsf { p o l y l o g } ( M N / \varepsilon ) , \varepsilon )$ -block-encoding of $A$ with $\mathcal { O } ( 1 )$ queries and polylog $( M N / \varepsilon )$ elementary gates.

# 3 Variable-time amplitude amplification and estimation

Following the work of Ambainis [Amb12] we define variable-stopping-time quantum algorithms. In our presentation we use the formulation of Childs et al. [CKS17] which makes the statements easier to read, while one does not lose much of the generality.

In the problem of variable-time amplitude amplification the goal is to amplify the success probability of a variable-stopping-time algorithm by exploiting that the computation may end after time $t _ { j }$ marking a significant portion of the quantum state as “bad”. Here we define the problem of variable-time amplitude estimation which asks for an $\varepsilon$ -multiplicative estimate of the initial unamplified amplitude/probability of success.

Our approach to variable-time amplitude estimation is that we first solve the mindfulamplification problem, where we amplify the amplitude to $\Theta ( 1 )$ , while also determining the amplification gain up to $\varepsilon / 3$ -multiplicative precision. Then we estimate to $\varepsilon / 3 .$ -multiplicative precision the amplitude after the mindful-amplification using amplitude estimation, incurring an overhead of $\approx 1 / \varepsilon$ . This then results in an $\varepsilon$ -multiplicative approximation of the initial amplitude.

Definition 12 (Mindful-amplification problem). For a given $\varepsilon > 0$ , a quantum algorithm $\mathcal { A }$ and an orthogonal projector $\Pi _ { \iota }$ , the $\varepsilon$ -mindful-amplification problem is the following: Construct an algorithm $\mathcal { A } ^ { \prime }$ such that $\Pi { \cal A } ^ { \prime } | 0 \rangle \propto \Pi { \cal A } | 0 \rangle$ and $\left\| \Pi { \cal A } ^ { \prime } | 0 \rangle \right\| = \Theta ( 1 ) .$ , moreover output a number Γ such that $\frac { \| \Pi \mathcal { A } ^ { \prime } | \pmb { 0 }  \| } { \Gamma \| \Pi \mathcal { A } | \pmb { 0 }  \| } \in [ 1 - \varepsilon , 1 + \varepsilon ] .$ .

# 3.1 Variable-stopping-time algorithms and variable-time amplification

Now we turn to discussing variable-stopping-time quantum algorithms. The main idea of such an algorithm is that there are $m$ possible stopping times, and for each stopping time $t _ { j } ,$ there is a control register that can be set to 1 at time $t _ { j } ,$ indicating that the computation has stopped on that branch. More precisely it means that after time $t _ { j }$ the algorithm does not alter the part of the quantum state for which the control flag has been set to 1 by time $t _ { j }$ .

Definition 13 (Variable-stopping-time quantum algorithm). We say that $\mathcal { A } = \mathcal { A } _ { m } \cdot \ldots \cdot \mathcal { A } _ { 1 }$ is $a$ variable-stopping-time quantum algorithm if $\mathcal { A }$ acts on $\mathcal { H } = \mathcal { H } _ { C } \otimes \mathcal { H } _ { A } ,$ where $\mathcal { H } _ { C } = \otimes _ { i = 1 } ^ { m } \mathcal { H } _ { C _ { i } }$ with $\mathcal { H } _ { C _ { i } } = \mathsf { S p a n } ( | 0 \rangle , | 1 \rangle ) ,$ , and each unitary $A _ { j }$ acts on $\mathcal { H } _ { C _ { j } } \otimes \mathcal { H } _ { A }$ controlled on the first $j - 1$ qubits $| 0 \rangle ^ { \otimes j - 1 } \in \otimes _ { i = 1 } ^ { j - 1 } \mathcal { H } _ { C _ { i } }$ being in the all-0 state.

In the case of variable-time amplitude amplification the space $\mathcal { H } _ { A }$ on which the algorithm acts has a flag which indicates success, i.e., $\mathcal { H } _ { A } = \mathcal { H } _ { F } \otimes \mathcal { H } _ { W }$ , where the flag space ${ \mathcal H } _ { F } = \mathsf { S p a n } ( | g \rangle , | b \rangle )$ indicates “good” and “bad” outcomes. Also we define stopping times $0 = t _ { 0 } < t _ { 1 } < t _ { 2 } < . . . < t _ { m } = T _ { \mathrm { m a x } }$ such that for all $j \in [ m ]$ the algorithm $A _ { j } \cdots A _ { 1 }$ has (query/gate) complexity $t _ { j }$ . In order to analyse such an algorithm we define the probability of the different stopping times. We use $\vert { \boldsymbol { 0 } } \rangle \in { \mathcal { H } }$ to denote the all-0 initial state on which we run the algorithm $\mathcal { A }$ .

Definition 14 (Probability of stopping by time $t$ ). We define the orthogonal projector

$$
\Pi _ { \mathsf { s t o p } \leq t } : = \sum _ { j : \ t _ { j } \leq t } | 1 \rangle \langle 1 | c _ { j } \otimes I _ { \mathcal { H } _ { A } } ,
$$

where by $| 1 \rangle \langle 1 | _ { C _ { j } }$ we denote the orthogonal projector on $\mathcal { H } _ { C }$ which projects onto the state

$$
| 0 \rangle _ { \mathcal { H } _ { C _ { 1 } } } \otimes \cdot \cdot \cdot \otimes | 0 \rangle _ { \mathcal { H } _ { C _ { j - 1 } } } \otimes | 1 \rangle _ { \mathcal { H } _ { C _ { j } } } \otimes | 0 \rangle _ { \mathcal { H } _ { C _ { j + 1 } } } \otimes \cdot \cdot \cdot \otimes | 0 \rangle _ { \mathcal { H } _ { C _ { m } } } .
$$

We define $p _ { \mathsf { s t o p } \leq t } : = \| \Pi _ { \mathsf { s t o p } \leq t } A \vert \pmb { 0 } \rangle \| ^ { 2 } .$ , and similarly $p _ { \mathsf { s t o p } \geq t }$ . Finally we define the projector

$$
\Pi _ { \mathrm { m g } } ^ { ( j ) } : = I - \Pi _ { \mathrm { s t o p } \leq t _ { j } } \cdot \left( I _ { \mathcal { H } _ { C } } \otimes | b \rangle \langle b | _ { \mathcal { H } _ { F } } \otimes I _ { \mathcal { H } _ { W } } \right) ,
$$

and $p _ { \mathrm { m g } } ^ { ( j ) } : = \left\| \Pi _ { \mathrm { m g } } ^ { ( j ) } \pmb { A } | \pmb { 0 } \rangle \right\| ^ { 2 } = \left\| \Pi _ { \mathrm { m g } } ^ { ( j ) } \pmb { A } _ { j } \cdot \hdots \cdot \mathcal { A } _ { 1 } | \pmb { 0 } \rangle \right\| ^ { 2 }$ expressing the probability that the state “maybe good” after the $j$ -th segment of the algorithm has been used. This is 1 minus the probability that the state was found to be “bad” by the end of the $j$ -th segment of the algorithm.

For simplicity from now on we assume that $p _ { \mathrm { s t o p } \leq t _ { m } } = 1$ . Using the above notation we can say that in the problem of variable-time amplitude amplification the goal is to prepare a state $\propto \Pi _ { \mathrm { m g } } ^ { ( m ) } A | \mathbf { 0 } \rangle$ ; in variable-time amplitude estimation the goal is to estimate $p _ { \mathsf { s u c c } } : = \left\| \Pi _ { \mathsf { m g } } ^ { ( m ) } \mathcal { A } | \pmb { 0 } \rangle \right\| ^ { 2 }$ . Now we define what we precisely mean by variable-time amplification.

Definition 15 (Variable-time amplification). We say that $\mathcal { A } ^ { \prime } = ( \mathcal { A } _ { 1 } ^ { \prime } , \mathcal { A } _ { 2 } ^ { \prime } , \ldots , \mathcal { A } _ { m } ^ { \prime } )$ is $a$ variabletime amplification of $\mathcal { A }$ if $A _ { 0 } ^ { \prime } = I$ and $\forall j \in [ m ]$ : $\Pi _ { \mathrm { m g } } ^ { ( j ) } \mathcal { A } _ { j } ^ { \prime } | \mathbf { 0 } \rangle \propto \Pi _ { \mathrm { m g } } ^ { ( j ) } \mathcal { \bar { A } } _ { j } \mathcal { A } _ { j - 1 } ^ { \bar { \prime } } | \mathbf { 0 } \rangle ,$ moreover $\mathcal { A } _ { j } ^ { \prime }$ uses the circuit $\mathbf { \Phi } \_ { A _ { j } , A _ { j - 1 } ^ { \prime } }$ and its inverse $a$ total of $q _ { j }$ times and on top of that it uses at most $g _ { j }$ elementary gates. We define aj := $\begin{array} { r } { a _ { j } : = \frac { \left\| \Pi _ { \mathfrak { m g } } ^ { ( j ) } \mathcal { A } _ { j } ^ { \prime } | \mathbf { 0 } \rangle \right\| } { \left\| \Pi _ { \mathfrak { m g } } ^ { ( j ) } \mathcal { A } _ { j } \mathcal { A } _ { j - 1 } ^ { \prime } | \mathbf { 0 } \rangle \right\| } } \end{array}$ as the amplification of the $j$ -th phase, and $\begin{array} { r } { o _ { j } : = \frac { q _ { j } } { a _ { j } } } \end{array}$ as the (query) overhead of the $j$ -th amplification phase.

Note that the above definition implies that for a variable-time amplification $\mathcal { A } ^ { \prime }$ we have that $\forall j \in [ m ]$ : $\Pi _ { \mathrm { m g } } ^ { ( j ) } \mathcal { A } _ { j } ^ { \prime } | \mathbf { 0 } \rangle \propto \Pi _ { \mathrm { m g } } ^ { ( j ) } \mathcal { A } _ { j } \mathcal { A } _ { j - 1 } \cdot \cdot \cdot \mathcal { A } _ { 1 } | \mathbf { 0 } \rangle ,$ in particular $\Pi _ { \mathrm { m g } } ^ { ( j ) } \mathcal { A } _ { m } ^ { \prime } | \pmb { 0 } \rangle \propto \Pi _ { \mathrm { m g } } ^ { ( j ) } \mathcal { A } | \pmb { 0 } \rangle$ .

The following lemma analyses the efficiency of a variable-time amplification $\mathcal { A } ^ { \prime }$ .

Lemma 16. For all $j < k \in [ m ]$ we have that $\mathcal { A } _ { k } ^ { \prime }$ uses $\mathcal { A } _ { j } ^ { \prime }$ a total of

$$
\frac { \left\| \Pi _ { \mathfrak { m g } } ^ { ( k ) } \mathcal { A } _ { k } ^ { \prime } | \mathbf { 0 } \rangle \right\| } { \left\| \Pi _ { \mathfrak { m g } } ^ { ( j ) } \mathcal { A } _ { j } ^ { \prime } | \mathbf { 0 } \rangle \right\| } \sqrt { \frac { p _ { \mathfrak { m g } } ^ { ( j ) } } { p _ { \mathfrak { m g } } ^ { ( k ) } } } \cdot \prod _ { i = j + 1 } ^ { k } o _ { i }
$$

times.

Proof. We prove the claim by induction on $k - j$ . For $j = k$ the statement is trivial. For $j = k - 1$ we have that $\mathcal { A } _ { k } ^ { \prime }$ uses $\mathcal { A } _ { k - 1 } ^ { \prime }$ a total of $q _ { k } = \boldsymbol { a } _ { k } \cdot \boldsymbol { o } _ { k }$ times by definition. Now observe that

$$
\begin{array} { r l } { \alpha _ { k } = } & { \frac { | | \Gamma ( \frac { \| \hat { \mathbf { r } } \| _ { \infty } ^ { k } } { \| \mathbf { r } \| _ { k - 1 } ^ { k } \mathcal { A } _ { k } ^ { \prime } \| \boldsymbol { \mathbb { D } } _ { k } ^ { \prime } } ) | } { | \Gamma ( \frac { \| \hat { \mathbf { r } } \| _ { \infty } ^ { k } \mathcal { A } _ { k } ^ { \prime } \| \boldsymbol { \mathcal { A } } _ { k - 1 } ^ { \prime } \mathcal { B } _ { k } ^ { \prime } ) | } } | } \\ & { = \frac { | | | \Gamma ( \frac { \| \hat { \mathbf { r } } \| _ { \infty } ^ { k } \mathcal { A } _ { k } ^ { \prime } } { 1 + \sqrt { \pi } } ) | } { | | \Gamma ( \frac { \| \hat { \mathbf { r } } \| _ { \infty } ^ { k } \mathcal { A } _ { k } ^ { \prime } } { 1 + \sqrt { \pi } } ) | | } \frac { | | \Gamma ( \frac { \| \hat { \mathbf { r } } - \| ^ { 1 } } { \sqrt { \pi } } ) \mathcal { A } _ { k } ^ { \prime } - 1 | \boldsymbol { \mathbb { D } } _ { k } ^ { \prime } | } { | \Gamma | \frac { \| \hat { \mathbf { r } } \| _ { \infty } ^ { k } \mathcal { A } _ { k } ^ { \prime } \| } { 1 + \sqrt { \pi } } | | } } \\ &  = \frac { | | \Gamma ( \frac { \| \hat { \mathbf { r } } \| _ { \infty } ^ { k } \mathcal { A } _ { k } ^ { \prime } } { 1 + \sqrt { \pi } } ) | } { | | \Gamma | \frac { \| \hat { \mathbf { r } } \| _ { \infty } ^ { k } \mathcal { A } _ { k } ^ { \prime } } { 1 + \sqrt { \pi } } | | } \frac  | | \Gamma | \frac  \| \hat { \mathbf { r } } \| _  \ \end{array}
$$

Finally we show the induction step when $j < k - 1$ . As we observed above $\mathcal { A } _ { k } ^ { \prime }$ uses $\mathcal { A } _ { k - 1 } ^ { \prime }$ a total of

$$
{ \frac { \left\| \Pi _ { \mathfrak { m g } } ^ { ( k ) } \mathcal { A } _ { k } ^ { \prime } | \mathbf { 0 } \rangle \right\| } { \left\| \Pi _ { \mathfrak { m g } } ^ { ( k - 1 ) } \mathcal { A } _ { k - 1 } ^ { \prime } | \mathbf { 0 } \rangle \right\| } } \sqrt { \frac { p _ { \mathfrak { m g } } ^ { ( k - 1 ) } } { p _ { \mathfrak { m g } } ^ { ( k ) } } } \cdot o _ { k }
$$

times. Note that $\mathcal { A } _ { k } ^ { \prime }$ only uses $\mathcal { A } _ { j } ^ { \prime }$ via $\mathcal { A } _ { k - 1 } ^ { \prime }$ . ${ \mathsf { B y } }$ the induction hypothesis we know that $\mathcal { A } _ { k - 1 } ^ { \prime }$ uses $\mathcal { A } _ { j } ^ { \prime }$ a total of

$$
\frac { \left\| \Pi _ { \mathrm { m g } } ^ { ( k - 1 ) } \mathcal { A } _ { k } ^ { \prime } | \mathbf { 0 } \rangle \right\| } { \left\| \Pi _ { \mathrm { m g } } ^ { ( j ) } \mathcal { A } _ { j } ^ { \prime } | \mathbf { 0 } \rangle \right\| } \sqrt { \frac { p _ { \mathrm { m g } } ^ { ( j ) } } { p _ { \mathrm { m g } } ^ { ( k - 1 ) } } } \cdot \prod _ { i = j + 1 } ^ { k - 1 } o _ { i }
$$

times, which then implies the statement.

Corollary 17. $\Pi _ { \mathrm { m g } } ^ { ( m ) } \mathcal { A } _ { m } ^ { \prime } | \pmb { 0 } \rangle \propto \Pi _ { \mathrm { m g } } ^ { ( m ) } \mathcal { A } | \pmb { 0 } \rangle$ and for all $j \in [ m ] , \mathcal { A } _ { m } ^ { \prime }$ uses $A _ { j }$ a total of at most

$$
\frac { \left\| \Pi _ { \mathfrak { m g } } ^ { ( m ) } \mathcal { A } _ { m } ^ { \prime } | \mathbf { 0 } \rangle \right\| } { \left\| \Pi _ { \mathfrak { m g } } ^ { ( j - 1 ) } \mathcal { A } _ { j - 1 } ^ { \prime } | \mathbf { 0 } \rangle \right\| } \left( 1 + \sqrt { \frac { p _ { \mathrm { s t o p } \ge t _ { j } } } { p _ { \mathrm { s u c c } } } } \right) \cdot \prod _ { i = j } ^ { m } o _ { i }
$$

times.

Proof. By Definition 15 we have that $\mathcal { A } _ { m } ^ { \prime }$ uses $A _ { j }$ and $\boldsymbol { \mathcal { A } } _ { j - 1 } ^ { \prime }$ the same number of times. ${ \mathsf { B y } }$ Lemma 16 we know the latter is used a total of $\begin{array} { r } { \frac { \left\| \prod _ { \mathfrak { m g } } ^ { ( m ) } \mathcal { A } _ { m } ^ { \prime } | \mathbf { 0 } \rangle \right\| } { \left\| \prod _ { \mathfrak { m g } } ^ { ( j - 1 ) } \mathcal { A } _ { j - 1 } ^ { \prime } | \mathbf { 0 } \rangle \right\| } \sqrt { \frac { p _ { \mathfrak { m g } } ^ { ( j - 1 ) } } { p _ { \mathfrak { m g } } ^ { ( m ) } } } \cdot \prod _ { i = j + 1 } ^ { m } o _ { i } } \end{array}$ times. ${ \mathsf { B y } }$ Definition 14 we have that $p _ { \mathsf { s u c c } } = p _ { \mathrm { m g } } ^ { ( m ) }$ and $p _ { \mathrm { m g } } ^ { ( j - 1 ) } \leq p _ { \mathrm { s u c c } } + p _ { \mathrm { s t o p } \geq t _ { j } }$ from which the statement√ follows using the simple observation that $\forall a , b \in \mathbb { R } _ { 0 } ^ { + } : \sqrt { a + b } \leq \sqrt { a } + \sqrt { b } .$ . □

Now we define some uniform bound quantities, which make it easier to analyze the performance of variable-time amplification.

Definition 18 (Uniformly bounded variable-time amplification). If the variable-time amplification algorithm $\mathcal { A } ^ { \prime }$ is such that for some $E , G , O \in \mathbb { R } _ { + }$ we have that $\forall j \in [ m ]$ :

$$
\begin{array} { r } { \frac { \left\| \prod _ { m \in \mathcal { A } } ^ { ( m ) } \mathcal { A } _ { m } ^ { \prime } | \mathbf { 0 } \rangle \right\| } { \left\| \prod _ { m \in \mathcal { I } } ^ { ( j - 1 ) } \mathcal { A } _ { j - 1 } ^ { \prime } | \mathbf { 0 } \rangle \right\| } \leq E , \qquad g _ { j } \leq G ( t _ { j } - t _ { j - 1 } ) , a n d \qquad \displaystyle \prod _ { i = 1 } ^ { m } o _ { i } \leq O , } \end{array}
$$

then we say that $\mathcal { A } ^ { \prime }$ is $( E , G , O )$ -bounded.

Using the above definition we can derive some intuitive complexity bounds on variable-time amplifications, essentially recovering13 a bound used by Ambainis [Amb12].

Corollary 19. If  $\mathcal { A } ^ { \prime }$ is an $( E , G , O )$ -bounded variable-time amplification, then $\mathcal { A } _ { m } ^ { \prime }$ has complexity at most EO Tmax + √ Ipsucc coming from the use of the variable-time algorithm $\mathcal { A }$ , and it uses at most EGO Tmax + √ Ipsucc additional elementary gates, where $I \leq t _ { 1 } + \left. T \right. _ { 2 } \sqrt { \mathsf { l n } ( T _ { \operatorname* { m a x } } / t _ { 1 } ) }$ and $\begin{array} { r } { \left. \boldsymbol { T } \right. _ { 2 } : = \sqrt { \sum _ { j = 1 } ^ { m } t _ { j } ^ { 2 } \cdot { p _ { \mathrm { s t o p } = t _ { j } } } } . } \end{array}$ .

Proof. The complexity of the algorithm segment $A _ { j }$ is $t _ { j } - t _ { j - 1 }$ , and due to Corollary 17 $\mathcal { A } _ { m } ^ { \prime }$ uses $A _ { j }$ at most $\begin{array} { r } { E O \left( 1 + \sqrt { \frac { p _ { \mathrm { s t o p } \geq t _ { j } } } { p _ { \mathrm { s u c c } } } } \right) } \end{array}$ times. So we can bound the complexity coming from the use of $\begin{array} { r } { A _ { j } \mathrm { \ b y \ } ( t _ { j } - t _ { j - 1 } ) E O \left( 1 + \sqrt { \frac { p _ { \mathrm { s t o p } \ge t _ { j } } } { p _ { \mathrm { s u c c } } } } \right) } \end{array}$ and we can bound the number of additional elementary gates coming from the implementation of $\mathcal { A } _ { j } ^ { \prime }$ $\begin{array} { r } { \mathrm { \Lambda } _ { j } ^ { \prime } \mathrm { b y } ( t _ { j } - t _ { j - 1 } ) E O O \left( 1 + \sqrt { \frac { p _ { \mathrm { s t o p } \ge t _ { j } } } { p _ { \mathrm { s u c c } } } } \right) . } \end{array}$

We get the total complexities by summing up these contributions for all $j \in [ m ]$

$$
E ( G ) O \sum _ { i = 1 } ^ { m } ( t _ { j } - t _ { j - 1 } ) \left( 1 + \sqrt { \frac { p _ { \mathrm { s t o p } \ge t _ { j } } } { p _ { \mathrm { s t o c } } } } \right) = E ( G ) O \left( T _ { \mathrm { m a x } } + \frac { 1 } { \sqrt { p _ { \mathrm { s t a c } } } } \sum _ { j = 1 } ^ { m } ( t _ { j } - t _ { j - 1 } ) \sqrt { p _ { \mathrm { s t o p } \ge t _ { j } } } \right) .
$$

Before bounding the above expression let us introduce some notation. Let $T$ be a random variable corresponding to the stopping times such that $\mathbb { P } ( T = t _ { j } ) = p _ { \mathsf { s t o p } = t }$ . Let $F$ be the distribution function of $T$ , i.e., $F ( t ) : = p _ { \mathsf { s t o p } \leq t }$ . Also let $F ^ { - 1 } ( p ) : = \operatorname* { i n f } \{ t \in \mathbb { R } \colon F ( t ) \geq p \}$ be the generalized inverse distribution function. The intuitive meaning of $F ^ { - 1 }$ is the following: $F ^ { - 1 }$ is a monotone increasing function with the property that picking a number $p \in [ 0 , 1 ]$ uniformly at random, and then outputting the value $F ^ { - 1 } ( p )$ results in a random variable with the same distribution as $T$ .

Now using the above definitions we rewrite the summation of (8) in the following way:

(by definition)

$$
\begin{array} { r l } { \frac { \sqrt { 3 } } { 2 \pi } } & { \sin ( 2 \pi \Theta \pi ) = - \frac { \pi ^ { 2 } \pi ^ { 3 } } { 2 \pi ^ { 3 } } \quad \Theta \sinh ^ { 2 } \operatorname { f o r o s s u p } _ { \theta \to \pi ^ { - 1 } } \frac { \sqrt { 3 } } { \sqrt { 3 } } ( \theta \Theta \Theta \pi ) , } \\ & { \qquad - \frac { \sqrt { 3 } } { 2 \pi ^ { 3 } } \bigl ( \theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta ^ { \prime } \bigr ) , } \\ & { \qquad - \frac { \sqrt { 3 } } { 2 \pi ^ { 3 } } \bigl ( \theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta ^ { \prime } \bigr ) , } \\ & { \qquad - \frac { \sqrt { 3 } } { 2 \pi ^ { 3 } } \bigl ( 4 \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta ^ { \prime } \bigr ) , } \\ & { \qquad - \frac { \sqrt { 3 } } { 2 \pi ^ { 3 } } \bigl ( \theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \bigr ) , } \\ & { \qquad - \frac { \sqrt { 3 } } { 2 \pi ^ { 3 } } \bigl ( \theta \Theta \Theta \Theta ^ { \prime } \bigr \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \bigr ) , } \\ & { \qquad \le \frac { \sqrt { 3 } } { 2 \pi ^ { 3 } } \bigl ( \Theta \Theta \Theta ^ { \prime } \bigr \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \bigr ) , } \\ & { \qquad - \frac { \sqrt { 3 } } { 2 \pi ^ { 3 } } \int _ { \Omega _ { \omega } \to \pi ^ { - 1 } } ^ { \infty } \phi \bigl ( \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \bigr ) , } \\ &  \qquad - \frac { \sqrt { 3 } } { 2 \pi ^ { 3 } } \int _ { \Omega _ { \omega } \to \pi ^ { - 1 } } ^ { \infty } \phi \bigl ( \Theta \Theta \Theta \Theta \Theta \Theta \Theta \Theta \bigr ) , \end{array}
$$

(by definition)

Thus we get that the total query and gate complexity are bounded by:

$$
E ( G ) O \left( { \cal T } _ { \mathrm { m a x } } + \frac { \cal I } { \sqrt { p _ { \mathrm { s u c c } } } } \right) .
$$

Now we finish the proof by bounding $I .$ Let $c = t _ { 1 } ^ { 2 } / T _ { \mathrm { m a x } } ^ { 2 } \in ( 0 , 1 )$ , then we can bound $I$ as follows14:

$$
\begin{array} { r l } { \varepsilon ^ { - } } & { = \int _ { 0 } ^ { \infty } - \frac { \gamma ( \varepsilon ) - \rho _ { 0 } } { 2 \sqrt { \varepsilon ^ { 2 } - \rho _ { 0 } } } d \rho + \int _ { - \frac { \gamma ( \varepsilon ) } { 2 } - \rho _ { 0 } } ^ { \infty } d \rho } \\ & { = \int _ { 0 } ^ { \infty } - \frac { \gamma ( \varepsilon ) - \rho _ { 0 } } { 2 \sqrt { \varepsilon ^ { 2 } - \rho _ { 0 } } } d \rho + \int _ { - \frac { \gamma ( \varepsilon ) } { 2 } - \rho _ { 0 } } ^ { \infty } d \rho } \\ & { = \int _ { 0 } ^ { \infty } - \frac { \gamma ( \varepsilon ) - \rho _ { 0 } } { 2 \sqrt { \varepsilon ^ { 2 } - \rho _ { 0 } } } d \rho + \sqrt { \varepsilon ^ { 2 } - \rho _ { 0 } } } \\ & { = \int _ { \frac { \gamma ( \varepsilon ) } { 2 } - \rho _ { 0 } } ^ { \infty } \frac { \gamma ( \varepsilon ) - \rho _ { 0 } } { 2 \sqrt { \varepsilon ^ { 2 } - \rho _ { 0 } } } d \rho + \sqrt { \varepsilon ^ { 2 } - \rho _ { 0 } } } \\ & { \leq \frac { \gamma } { 2 } \left. \int _ { 0 } ^ { \infty } \left( - \nu ( \varepsilon ) ^ { 2 } \rho _ { 0 } \right) \rho \right. \int _ { \rho } ^ { \infty } \frac { 1 } { 1 - \frac { \rho _ { 0 } } { 2 } \rho ^ { \rho _ { 0 } } } d \rho - \sqrt { \varepsilon ^ { 2 } - \rho _ { 0 } } } \\ & { = \frac { 1 } { 2 } \sqrt { \varepsilon ^ { 2 } - \rho _ { 0 } } \frac { \gamma ( \varepsilon ) - \rho _ { 0 } } { 2 \sqrt { \varepsilon ^ { 2 } - \rho _ { 0 } } } \left. \int _ { 0 } ^ { \infty } - \frac { 1 } { 2 } \rho ^ { \rho _ { 0 } } + \sqrt { \varepsilon ^ { 2 } - \rho _ { 0 } } \right. } \\ &  = \sqrt { \varepsilon ^ { 2 } - \rho _ { 0 } } \frac  \gamma  \end{array}
$$

Note that the above upper bound depends on the distribution of stopping times only via $\left. T \right. _ { 2 }$ . Also we can reduce the number of distinct stopping times to $\leq 1 + \log ( T _ { \mathrm { m a x } } / t _ { 1 } )$ while increasing the value of $\left\| T \right\| _ { 2 }$ by at most a constant factor. Therefore one may assume that $m \leq 1 + \log ( T _ { \mathrm { m a x } } / t _ { 1 } )$ .

# 3.2 Efficient variable-time amplitude amplification and estimation

Now that we have carefully analyzed the complexity of uniformly bounded variable-time amplifications, we finally apply the results in order to obtain efficient algorithms.

The basic method is to use ordinary amplitude amplification in each amplification phase, which was the original approach that Ambainis used [Amb12]. In order to understand the efficiency of this approach we invoke a result of Aaronson and Ambainis [AA03, Lemma 9], which carefully analyses the efficiency of amplitude amplification. We present their result in a slightly reformulated way, fitting the framework of the presented work better.

Lemma 20 (Efficiency of ordinary amplitude amplification). Suppose that $\mathcal { A }$ is a quantum algorithm, $\sqcap$ is an orthogonal projector, and $\alpha = \| \Pi { \mathcal { A } } | 0  \|$ . Let $\mathcal { A } ^ { ( k ) }$ denote the quantum algorithm that applies $k$ amplitude amplification steps on the outcome of $\mathcal { A }$ . If

$$
k \leq \frac { \pi } { 4 \arcsin ( \alpha ) } - \frac { 1 } { 2 } ,
$$

then

$$
\Big \| \Pi \boldsymbol { A } ^ { ( k ) } | \mathbf { 0 } \rangle \Big \| \geq \sqrt { 1 - \frac { ( 2 k + 1 ) ^ { 2 } \alpha ^ { 2 } } { 3 } } ( 2 k + 1 ) \alpha .
$$

The above result essentially states that if the amplification does not start to wrap around, then the inefficiency of the amplification step is bounded by the final amplitude squared. We make this claim precise in the following corollary.

Corollary 21 (A bound on amplification ratio). Suppose that $A , \Pi , \alpha$ and $\mathcal { A } ^ { ( k ) }$ are as in Lemma 20. If we do not overamplify, i.e., $( 2 k + 1 )$ arcsin $( \alpha ) \leq \pi / 2 ,$ then

$$
\frac { 2 k + 1 } { \Big ( \frac { \big \| \Pi \mathcal { A } ^ { ( k ) } ( \pmb { 0 } ) \big \| } { \alpha } \Big ) } \leq 1 + \frac { 3 } { 2 } \Big \| \Pi \mathcal { A } ^ { ( k ) } ( \pmb { 0 } ) \Big \| ^ { 2 } .
$$

Proof.

$$
\begin{array} { r l r } { \frac { ( 2 k + 1 ) \alpha } { \| \Gamma { \cal A } ^ { ( k + 1 ) } \| 0 } \bigg | \leq \frac { 1 } { \sqrt { 1 - \frac { ( 2 k + 1 ) ^ { 2 } \alpha } { 3 } } } } & { \quad } & { \mathrm { ( b y ~ l \leq m m a ~ 2 0 ) } } \\ { \leq \frac { 1 } { \sqrt { 1 - \frac { ( 2 k + 1 ) ^ { 2 } \alpha \epsilon \sin ^ { 2 } ( \alpha ) } { 3 } } } } & { \quad } & { \mathrm { ( \it \mathcal { N } \pi \pi \pi \pi \rho \| \rho \| \rho \| \rho \| \exp { \Lambda \pi \pi \rho } ) \ c \pi ) } } \\ { \leq 1 + \frac { 5 \alpha ^ { 2 } \sin ^ { 2 } ( \alpha \sin ^ { 2 } ( \alpha ) } { 9 } } & { \quad } & { \mathrm { ( \it \Xi \pi \pi \pi \rho \| \rho \| \rho \| \rho \| \rho \| \alpha ) \| } } \\ { \leq 1 + \frac { 5 \pi ^ { 2 } \sin ^ { 2 } ( \alpha + 1 ) \arctan ( \alpha ) } { 9 - 4 } } & { \quad } & { \mathrm { ( \it \Xi \pi \pi \rho \rho \| \rho \| \rho \| \rho \| \rho \| \phi \| \rho ) \| } } \\ { \leq 1 + \frac { 3 \sin ^ { 2 } ( ( 2 ( k + 1 ) ) \arctan ( \alpha ) ) } { 3 } } & { \quad } & { \mathrm { ( \it \Xi \pi \rho \rho \| \rho \| \rho \| \rho \| \rho \| \rho \| \phi ) \| } } \\ { \leq 1 + \frac { 3 \sin ^ { 2 } ( ( 2 k + 1 ) \arctan ( \alpha ) ) } { 2 } } & { \quad } & { \mathrm { ( \it \Xi \pi \rho \rho \| \rho \| \rho \| \rho \| \rho \| \rho \| \rho \| ) \| } } \\ { = 1 + \frac { 3 } { 2 } \| \Gamma { \cal A } ^ { ( k + 1 ) } ( 0 ) \| ^ { 2 } . } \end{array}
$$

The last equality comes from the usual geometric analysis of amplitude amplification.

Now we turn to proving our result about the efficiency of variable-time amplitude amplification and estimation. A trick we employ is to carefully select the amount of amplification in each phase so that the inefficiencies remain bounded.

Lemma 22 (Analysis of variable-time amplitude amplification). Suppose $\mathcal { A } ^ { \prime }$ is a variable-time amplification such that for all $j \in [ m ]$ the $j$ -th amplification phase $\mathcal { A } _ { j } ^ { \prime }$ uses $k _ { j } \geq 0$ ordinary amplitude amplification steps such that

$$
k _ { j } \leq \frac { \pi } { 4 \arcsin ( \alpha ) } - \frac { 1 } { 2 } ,
$$

and for all $j \in [ m ]$

$$
\left\| \Pi _ { \mathrm { m g } } ^ { ( j ) } \mathcal { A } _ { j } ^ { \prime } | 0 \rangle \right\| = \Theta \left( \mathsf { m a x } \Bigg [ \frac { 1 } { \sqrt { m } } , \frac { 1 } { \sqrt { m - j + 1 } ( 1 + \mathsf { l n } ( m - j + 1 ) ) } \Bigg ] \right) .
$$

Using $\mathcal { A } ^ { \prime }$ the variable-time amplification problem can be solved with query complexity15

$$
\mathcal { O } \left( T _ { \mathrm { m a x } } \sqrt { m } + \frac { \left. T \right. _ { 2 } \sqrt { \log ( 2 T _ { \mathrm { m a x } } / t _ { 1 } ) } \sqrt { m } } { \sqrt { p _ { \mathrm { s u c c } } } } \right) .
$$

Proof. We get that $E = \mathcal { O } \big ( \sqrt { m } \big )$ from (10) immediately. We need to work a bit more for bounding $O$ :

$$
\begin{array} { r l r l } & { \displaystyle \mathcal { D } = \displaystyle \sum _ { j = 1 } ^ { m } \sigma _ { j } = \sum _ { j = 1 } ^ { m } \frac { q _ { j } } { j } = \sum _ { j = 1 } ^ { m } \frac { 2 k _ { j } + 1 } { \left( \frac { \| \Gamma _ { j } \| _ { \infty } ^ { D } \epsilon _ { j } \epsilon _ { j } \epsilon _ { 0 } ^ { ( 0 ) } \| \epsilon _ { j } \| } { \| \Gamma _ { j } \| _ { \infty } ^ { D } \epsilon _ { j } \epsilon _ { j } \epsilon _ { 0 } ^ { ( 0 ) } \| \epsilon _ { j } \| } \right) } } & \\ & { \leq \displaystyle \sum _ { j = 1 } ^ { m } \bigg ( 1 + \frac { 3 } { 2 } \left\| \Gamma _ { j = 1 } ^ { ( j ) } A _ { j } ^ { \dagger } ( 0 ) \cdot A _ { j } ^ { \dagger } ( 0 ) \cdot \right\| ^ { 2 } \bigg ) } & & { \mathrm { ( b y ~ C o r o l l e r y ~ ) } } \\ & { \leq \exp \left( \displaystyle \sum _ { j = 1 } ^ { m } \mathrm { t n } \left( 1 + \frac { 3 } { 2 } \left\| \Gamma _ { m + 4 } ^ { ( j ) } A _ { j } ^ { \dagger } ( 0 ) \right\| ^ { 2 } \right) \right) \leq \exp \left( \displaystyle \sum _ { j = 1 } ^ { m } \frac { 3 } { 2 } \left\| \Gamma _ { m + 4 } ^ { ( j ) } A _ { j } ^ { \dagger } ( 0 ) \right\| ^ { 2 } \right) } & \\ & { \leq \exp \left( C \displaystyle \sum _ { j = 1 } ^ { m } \operatorname* { m a x } \left[ \frac { 1 } { m } , \frac { 1 } { ( m - j + 1 ) ( 1 + \operatorname* { I n } ( m - j + 1 ) ) ^ { 2 } } \right] \right) } & & { \mathrm { ( f o r ~ s o m e ~ } C \in \mathbb { R } _ { + } \mathrm { ~ b y ~ ( } 1 } \end{array}
$$

Now we show that $O \le \exp ( 3 C ) = { \mathcal { O } } ( 1 )$ by bounding the expression inside the exponent:

$$
\begin{array} { l } { { \displaystyle \sum _ { j = 1 } ^ { m } \operatorname* { m a x } \biggl [ \displaystyle \frac 1 m , \displaystyle \frac 1 { ( m - j + 1 ) ( 1 + \ln ( m - j + 1 ) ) ^ { 2 } } \biggr ] \leq \sum _ { j = 1 } ^ { m } \displaystyle \frac 1 m + \sum _ { j = 1 } ^ { m } \displaystyle \frac 1 { ( m - j + 1 ) ( 1 + \ln ( m - j + 1 ) ) } } } \\ { { \displaystyle \ = \ 1 + \sum _ { j = 1 } ^ { m } \displaystyle \frac 1 { j ( 1 + \ln ( j ) ) ^ { 2 } } = 2 + \sum _ { j = 2 } ^ { m } \displaystyle \frac 1 { j ( 1 + \ln ( j ) ) } } } \\ { { \displaystyle \ \leq 2 + \int _ { 1 } ^ { m } \displaystyle \frac 1 { x ( 1 + \ln ( x ) ) ^ { 2 } } d x } } \\ { { \displaystyle \ = 2 + \left[ \displaystyle \frac 1 { 1 + \ln ( x ) } \right] _ { 1 } ^ { m } \leq 3 . } } \end{array}
$$

Using Corollary 19 we get the final complexity claim of variable-time amplification.

Now we describe how to efficiently construct a variable-time amplitude amplification algorithm satisfying the above requirements, and derive an efficient algorithm for variable-time amplitude estimation.

Theorem 23 (Efficient variable-time amplitude amplification and estimation). Let $U$ be a statepreparation unitary that prepares the sate $U | 0 \rangle ^ { \otimes k } = \sqrt { p _ { \mathrm { p r e p } } } | 0 \rangle | \psi _ { 0 } \rangle + \sqrt { 1 - p _ { p r e p } } | 1 \rangle | \psi _ { 1 } \rangle$ and has query complexity $T _ { U }$ . Suppose that $\mathcal { A }$ is a variable-stopping-time algorithm such that we know lower bounds $p _ { \mathrm { p r e p } } \geq p _ { \mathrm { p r e p } } ^ { \prime }$ and $p _ { \mathsf { s u c c } } \geq p _ { \mathsf { s u c c } } ^ { \prime }$ . Let $T _ { \mathrm { m a x } } ^ { \prime } : = 2 T _ { \mathrm { m a x } } / t _ { 1 }$ and

$$
Q = \left( T _ { \mathrm { m a x } } + \frac { T _ { U } + k } { \sqrt { p _ { \mathrm { p r e p } } } } \right) \sqrt { \mathsf { l o g } ( T _ { \mathrm { m a x } } ^ { \prime } ) } + \frac { \left( \left. T \right. _ { 2 } + \frac { T _ { U } + k } { \sqrt { p _ { \mathrm { p r e p } } } } \right) \mathsf { l o g } ( T _ { \mathrm { m a x } } ^ { \prime } ) } { \sqrt { p _ { \mathrm { s u c c } } } } .
$$

We can construct with success probability at least √ $1 - \delta$ a variable-stopping time algorithm $\mathcal { A } ^ { \prime }$ that prepares a state $a | 0 \rangle \bar { \mathcal { A } ^ { \prime } } | \psi _ { 0 } \rangle + \bar { \sqrt { 1 - a ^ { 2 } } } | 1 \rangle | \psi _ { \mathrm { g a r b a g e } } \rangle$ , such that $a = \Theta ( 1 )$ and $\mathcal { A } ^ { \prime }$ has complexity $\mathcal { O } ( Q )$ , moreover the quantum procedure constructing the classical description of the circuit of $\mathcal { A } ^ { \prime }$ has query complexity

$$
\mathcal { O } \left( Q \log \left( T _ { \mathrm { m a x } } ^ { \prime } \right) \log \left( \frac { 1 } { \delta } \log \left( \frac { T _ { \mathrm { m a x } } ^ { \prime } } { p _ { \mathrm { p r e p } } ^ { \prime } p _ { \mathrm { s u c c } } ^ { \prime } } \right) \right) \right) .
$$

Also, for any $\varepsilon \in \mathsf { \Gamma } ( 0 , 1 )$ the $\varepsilon$ -mindful-amplification problem can be solved using $\mathcal { A } ^ { \prime }$ with complexity

$$
\mathcal { O } \left( \frac { Q } { \varepsilon } \log ^ { 2 } \left( T _ { \operatorname* { m a x } } ^ { \prime } \right) \log \left( \frac { \log \left( T _ { \operatorname* { m a x } } ^ { \prime } \right) } { \delta } \right) \right) .
$$

Proof. We describe how to construct a variable-time amplification algorithm as described in Lemma 22.

We will use the following fact throughout the proof. If √ $\boldsymbol { B }$ is a quantum algorithm such that $\mathcal { B } | 0 \rangle ^ { \otimes k } = b | 0 \rangle | \phi _ { 0 } \rangle + \sqrt { 1 - b ^ { 2 } } | 1 \rangle | \phi _ { 1 } \rangle ,$ , then for arbitrary $j \in \mathbb N$ we can boost the success probability of amplitude estimation in a way that it outputs either $b < 2 ^ { j }$ or $b \geq 2 ^ { - j }$ such that the output is correct with probability at least $1 - \delta ^ { \prime }$ . Moreover, if the implementation cost of $\boldsymbol { B }$ is $T _ { B }$ , then the cost of the procedure is $\mathcal { O } \big ( 2 ^ { j } ( T _ { B } + k ) \log ( 1 / \delta ) \big )$ .

Using the above version of amplitude estimation we can estimate $p _ { \mathsf { p r e p } }$ with constant multiplicative precision and success probability at least $1 - \delta / 4$ with complexity $\begin{array} { r } { \mathcal { O } \left( \frac { T _ { U } + k } { \sqrt { p _ { \mathrm { p r e p } } } } \log \left( \frac { \log \left( 1 / p _ { \mathrm { p r e p } } ^ { \prime } \right) } { \delta } \right) \right) } \end{array}$ Then we amplify $T _ { U }$ using $\Theta ( 1 / \sqrt { p _ { \mathrm { p r e p } } } )$ amplification steps, to get amplitude $\Theta ( 1 )$ on the state $| 0 \rangle | \psi _ { 0 } \rangle$ , and define a new variable-time algorithm $\tilde { \mathcal { A } }$ by appending the amplified version of $T _ { U }$ to the beginning of the algorithm. This adds $\begin{array} { r } { C : = \Theta \left( \frac { T _ { U } + k } { \sqrt { p _ { \mathrm { p r e p } } } } \right) } \end{array}$ to the complexity of the first step of the algorithm.

In order to get the claimed bounds we “sparsify” the stopping times yielding $\widetilde { m } = \mathcal { O } \big ( \lfloor \log ( T _ { \mathfrak { m a x } } ^ { \prime } ) \big ) .$ without changing $\left\| \widetilde { T } \right\| _ { 2 }$ too much. Let us define $\widetilde { m } : = \lceil \log _ { 2 } ( T _ { \mathfrak { m a x } } ^ { \prime } ) \rceil$ , and also for all $j \in [ \widetilde m ]$ $t _ { j } ^ { \prime } : = \mathsf { m a x } \big ( t _ { j } : t _ { j }$ is a stopping time of $\mathcal { A }$ which is less than or equal $2 ^ { j } t _ { 1 }$ . Then we define the stopping times of $\tilde { \lambda }$ for all $j ~ \in ~ [ \widetilde { m } ]$ such that $\tilde { t } _ { j } ~ = ~ C + t _ { j } ^ { \prime }$ . Then clearly we have that $\widetilde { m } = \mathcal { O } \big ( \lfloor \log ( T _ { \operatorname* { m a x } } ^ { \prime } ) \big )$ , and $\begin{array} { r } { \widetilde { T } _ { \mathrm { m a x } } = T _ { \mathrm { m a x } } + \Theta \Big ( \frac { T _ { U } + k } { \sqrt { p _ { \mathrm { p r e p } } } } \Big ) } \end{array}$ , and $\begin{array} { r } { \left\| \widetilde { T } \right\| _ { 2 } \leq \dot { 2 } \Big ( \left\| T \right\| _ { 2 } + \Theta \Big ( \frac { T _ { U } + k } { \sqrt { p _ { \mathrm { p r e p } } } } \Big ) \Big ) } \end{array}$ .

Following Definition 15 we construct the variable-time amplification ${ \widetilde { \mathcal { A } } } ^ { \prime }$ inductively. For each $j \in [ \widetilde m ]$ after running the algorithm $\widetilde { \mathcal { A } } _ { j } \widetilde { \mathcal { A } } _ { j - 1 } ^ { \prime }$ we estimate the maybe-good amplitude with constant multiplicative precision and success probability at least $1 - \delta / 4 / ( \log ( \widetilde { m } ) + \log ( 1 / \underline { { p } } _ { \operatorname { s u c c } } ^ { \prime } ) )$ . Then we get the algorithm segment $\mathcal { \tilde { A } } _ { j } ^ { \prime }$ by applying amplitude amplification $k _ { j }$ times on $\bar { \mathcal { A } } _ { j } \bar { \mathcal { A } } _ { j - 1 } ^ { \prime }$ , such that requirements (9)-(10) are satisfied. Observe that upon success the the cost of the amplitude estimation procedure is at most $\mathcal { O } \left( \log \left( \frac { \widetilde { m } + \log _ { 2 } \left( 1 / \widetilde { p _ { \mathrm { s u c c } } ^ { \prime } } \right) } { \delta } \right) \right)$ times the cost of running $\mathcal { \tilde { A } ^ { \prime } } _ { j } .$ . Moreover the overall success probability is at least $1 - \delta / 2 ,$ since upon success there can be at most $\widetilde { m } + \log _ { 2 } \left( 1 / p _ { \mathrm { s u c c } } ^ { \prime } \right)$ amplification steps.

Note that the above procedure needs to be completed only once in order to construct a variable-time amplification ${ \widetilde { \mathcal { A } } } ^ { \prime }$ , that satisfies the requirements of Lemma 22. The complexity bound on ${ \widetilde { \mathcal { A } } } ^ { \prime }$ follows from Lemma 22. There is no need to use the full procedure constructing $\tilde { \mathcal { A } } ^ { \prime }$ when we use the variable-time amplification itself. The query and gate complexity of the above procedure matches the query and gate complexity of the resulting variable-time amplification   up to a factor $\begin{array} { r } { \mathcal { O } \left( \widetilde { m } \log \left( \frac { \widetilde { m } + \log \left( 1 / \boldsymbol { p } _ { \mathrm { s u c c } } ^ { \prime } \right) } { \delta } \right) \right) } \end{array}$ , since the sum of the cost of the algorithms $\mathcal { \tilde { A } } _ { j }$ is upper bounded by $\widetilde { m }$ times the cost of the variable-time amplified algorithm ${ \widetilde { \mathcal { A } } } ^ { \prime }$ .

Finally observe that in order to get an estimate $\Gamma$ such that $\begin{array} { r } { \frac { \| \Pi _ { \mathrm { m g } } ^ { ( \tilde { m } ) } \tilde { \mathcal { A } } ^ { \prime } | \mathbf { 0 }  \| } { \Gamma \| \Pi _ { \mathrm { m g } } ^ { ( \tilde { m } ) } \tilde { \mathcal { A } } | \mathbf { 0 } \rangle \| } \in [ 1 - \varepsilon , 1 + \varepsilon ] , } \end{array}$ suffices to obtain estimates $\gamma _ { j }$ such that $\begin{array} { r } { \frac { \left\| \Pi _ { \mathfrak { m g } } ^ { ( j ) } \widetilde { \mathcal { A } } _ { j } ^ { \prime } | \mathbf { 0 } \rangle \right\| } { \gamma _ { j } \left\| \Pi _ { \mathfrak { m g } } ^ { ( j ) } \widetilde { \mathcal { A } } _ { j } \widetilde { \mathcal { A } } _ { j - 1 } ^ { \prime } | \mathbf { 0 } \rangle \right\| } \in \left[ 1 - \frac { \varepsilon } { 2 \widetilde { m } } , 1 + \frac { \varepsilon } { 2 \widetilde { m } } \right] } \end{array}$ . Then $\begin{array} { r } { \Gamma : = \prod _ { j = 1 } ^ { \widetilde { m } } \gamma _ { j } } \end{array}$ is a good enough estimate since

$$
\prod _ { j = 1 } ^ { \tilde { m } } \frac { \left\| \prod _ { \mathfrak { m } _ { 9 } } ^ { ( j ) } \widetilde { \mathcal { A } } _ { j } ^ { \prime } | \mathbf { 0 } \rangle \right\| } { \left\| \prod _ { \mathfrak { m } _ { 9 } } ^ { ( j ) } \widetilde { \mathcal { A } } _ { j } \widetilde { \mathcal { A } } _ { j - 1 } ^ { \prime } | \mathbf { 0 } \rangle \right\| } = \prod _ { j = 1 } ^ { \tilde { m } } \frac { \left\| \prod _ { \mathfrak { m } _ { 9 } } ^ { ( \tilde { m } ) } \widetilde { \mathcal { A } } _ { \tilde { m } } \cdot \dots \cdot \widetilde { \mathcal { A } } _ { j + 1 } \widetilde { \mathcal { A } } _ { j } ^ { \prime } | \mathbf { 0 } \rangle \right\| } { \left\| \prod _ { \mathfrak { m } _ { 9 } } ^ { ( \tilde { m } ) } \widetilde { \mathcal { A } } _ { \tilde { m } } \cdot \dots \cdot \widetilde { \mathcal { A } } _ { j + 1 } \widetilde { \mathcal { A } } _ { j } \widetilde { \mathcal { A } } _ { j - 1 } ^ { \prime } | \mathbf { 0 } \rangle \right\| } = \frac { \left\| \prod _ { \mathfrak { m } _ { 9 } } ^ { ( \tilde { m } ) } \widetilde { \mathcal { A } } ^ { \prime } | \mathbf { 0 } \rangle \right| } { \left\| \prod _ { \mathfrak { m } _ { 9 } } ^ { ( \tilde { m } ) } \widetilde { \mathcal { A } } | \mathbf { 0 } \rangle \right\| } .
$$

In order to get an estimate of $\gamma _ { j }$ it suffices to estimate both $\left\| \Pi _ { \mathrm { m g } } ^ { ( j ) } \tilde { \mathcal { A } } _ { j } ^ { \prime } | \pmb { 0 } \rangle \right\|$ and $\left\| \Pi _ { \mathrm { m g } } ^ { ( j ) } \tilde { \mathcal { A } } _ { j } \tilde { \mathcal { A } } _ { j - 1 } ^ { \prime } | \mathbf { 0 } \rangle \right\|$ with multiplicative precision $\begin{array} { r } { 1 \pm \frac { \varepsilon } { 5 \widetilde { m } } } \end{array}$ . Note that such an estimate can be computed with success   probability at least $1 - \delta / ( 2 \widetilde { m } )$ with complexity that is at most $\mathcal { O } \left( \begin{array} { c } { \widetilde { m } } \end{array} \lfloor 0 9 \left( \frac { \widetilde { m } } { \delta } \right) \ \right)$ times bigger than the complexity of the algorithm ${ \widetilde { \mathcal { A } } } ^ { \prime }$ . Since we need to compute only $\widetilde { m } = \mathcal { O } \big ( \mathrm { l o g } ( T _ { \mathrm { m a x } } ^ { \prime } ) \big )$ such estimates, the complexity bound follows from the complexity bound on ${ \widetilde { \mathcal { A } } } ^ { \prime }$ . □

# 4 Linear system solving using blocks of unitaries

Given a way to implement a block-encoding for some matrix $A _ { i }$ , there are a number of useful basic operations one can do. We have already seen how the product of two block-encodings for $A$ and $B$ respectively gives a block-encoding for $A B$ (Lemma 4), and how, given a block-encoding for $A _ { i }$ , we can implement a block-encoding for $A ^ { - c }$ , for some $c \in ( 0 , \infty )$ (Lemma 9).

Given a block-encoding $U$ of $A$ , and a state $| b \rangle$ , it is straightforward to approximate the state $A | b \rangle / \big | \big | A | b \rangle \big | \big |$ , by applying $U$ to $| b \rangle$ , and then using amplitude amplification on the $| 0 \rangle A | b \rangle$ part of the resulting state. For convenience, we make this precise in the following lemma.

Lemma 24 (Applying a block-encoded matrix to a quantum state). Fix any $\varepsilon \in ( 0 , 1 / 2 )$ . Let $A \in \mathbb { C } ^ { N \times N }$ such that $\left\| A \right\| \leq 1$ , and $| b \rangle$ a normalized vector in $\mathbb { C } ^ { N }$ such that $\left\| A | b \rangle \right\| \geq \gamma$ . Suppose $| b \rangle$ can be generated in complexity $T _ { b . }$ , and there is an $( \alpha , a , \epsilon )$ -block-encoding of $A$ for some $\alpha \geq 1$ , with $\epsilon \leq \varepsilon \gamma / 2 ,$ , that can be implemented in cost $T _ { A }$ . Then there is a quantum algorithm with complexity

$$
\mathcal { O } \left( \operatorname* { m i n } \left( \frac { \alpha ( T _ { A } + T _ { b } ) } { \gamma } , \frac { \alpha T _ { A } \log \left( \frac { 1 } { \epsilon } \right) + T _ { b } } { \gamma } \right) \right) ,
$$

that terminates with success with probability at least ${ \frac { 2 } { 3 } } ,$ and upon success generates the state $A | b \rangle / \big | \big | A | b \rangle \big | \big |$ to precision $\varepsilon$ .

Proof. First we prove the first complexity upper bound. Let $U$ be the block-encoding of $A$ referred to in the statement of the lemma, so

$$
\begin{array} { r l } & { \qquad \left\| \boldsymbol { A } - \alpha ( \langle 0 | ^ { \otimes a } \otimes \boldsymbol { I } ) \boldsymbol { U } ( | 0 \rangle ^ { \otimes a } \otimes \boldsymbol { I } ) \right\| \le \epsilon } \\ & { \qquad \left\| \frac { 1 } { \alpha } \boldsymbol { A } | \boldsymbol { b } \rangle - ( \langle 0 | ^ { \otimes a } \otimes \boldsymbol { I } ) \boldsymbol { U } ( | 0 \rangle ^ { \otimes a } \otimes | \boldsymbol { b } \rangle ) \right\| \le \epsilon / \alpha . } \end{array}
$$

$\mathsf { B y }$ generating $| b \rangle$ and then applying $U$ , in cost $T _ { b } + T _ { A } ,$ we get a state that is $\epsilon / \alpha$ -close to a state of the form

$$
\vert 0 \rangle ^ { \otimes a } \left( \frac { 1 } { \alpha } A \vert b \rangle \right) + \vert 0 ^ { \perp } \rangle ,
$$

for some unnormalized state $| 0 ^ { \perp } \rangle$ that is orthogonal to every state with $| 0 \rangle ^ { \otimes a }$ in the first register. We have $\textstyle | { | { \frac { 1 } { \alpha } } A | b  } | | \geq { \dot { \gamma } } / \alpha$ , so using $\alpha / \gamma$ rounds of amplitude amplification on $| 0 \rangle ^ { \otimes a }$ in the first register, we can get within a constant of a state that is $\begin{array} { r } { \frac { \epsilon } { \alpha } \frac { \alpha } { \gamma } = \frac { \epsilon } { \gamma } } \end{array}$ -close to $| 0 \rangle ^ { \otimes a } \frac { A | b \rangle } { \left\| A | b \rangle \right\| }$ (because the error is also amplified by the amplitude amplification). Since $\epsilon \leq \varepsilon \gamma / 2$ , the error on the $| 0 \rangle ^ { \otimes a }$ part of the state is at most $\varepsilon / 2$ . Thus, if we measure a $| 0 \rangle ^ { \otimes a }$ in the first register at this stage, we will be within $\varepsilon / 2$ of the desired state.

To get the second complexity bound we first amplify the block-encoding resulting in a unitary $U ^ { \prime }$ that is a $( { \sqrt { 2 } } , a , 2 \epsilon )$ -block-encoding of $A ,$ that can by implemented in complexity $\begin{array} { r } { T _ { A } ^ { \prime } : = \mathcal { O } \big ( \alpha T _ { A } \log \big ( \frac { 1 } { \epsilon } \big ) \big ) } \end{array}$ due to Lemma 47. Then we use $U ^ { \prime }$ in the previous argument, replacing $T _ { A }$ with $T _ { A } ^ { \prime }$ and $\alpha$ with $\sqrt { 2 }$ . □

Given a block-encoding of $A _ { i }$ , we can implement a block-encoding of $A ^ { - c }$ , from which we can approximately generate the state $A ^ { - c } | b \rangle / \big | \big | A ^ { - c } | b \rangle \big | \big |$ given a circuit for generating $| b \rangle$ . When $c =$ 1, this is simply a quantum linear system solver, and more generally, we call this implementing negative powers of a Hamiltonian. However, we can get a better algorithm for this problem using the technique of variable-time amplitude amplification, which we do in Section 4.3.

Although block-encodings are quite a general way of representing a matrix, we motivate them by connecting them to quantum data structures, showing that if a matrix is stored in a quantum data structure, in one of a number of possible ways, then there is an efficiently implementable block-encoding of the matrix.

Specifically, for $p \in [ 0 , 1 ] ,$ define $\mu _ { p } ( A ) = \sqrt { s _ { 2 p } ( A ) s _ { 2 ( 1 - p ) } ( A ^ { T } ) }$ where $s _ { q } ( A ) = \mathsf { m a x } _ { j } \| A _ { j , \cdot } \| _ { q } ^ { q }$ is the $q$ -th power of the maximum $q$ -norm of any row of $A$ . We let $A ^ { ( p ) }$ denote the matrix of the same dimensions as $A _ { i }$ , with $A _ { j , k } ^ { ( p ) } = ( A _ { j , k } ) ^ { p }$ . The following was proven in [KP17], although not in the language of block-encodings. We include the proof of [KP17] for completeness.

Lemma 25 (Implementing block-encodings from quantum data structures). Let $A \in \mathbb { C } ^ { M \times N }$ .

1. $F i x p \in [ 0 , 1 ] .$ . If $\operatorname { T } A \in \mathbb { C } ^ { M \times N }$ , and $A ^ { ( p ) }$ and $( A ^ { ( 1 - p ) } ) ^ { \dag }$ are both stored in quantum-accessible data structures16, then there exist unitaries $U _ { R }$ and $U _ { L }$ that can be implemented in time $\mathcal { O } ( \mathsf { p o l y l o g } ( M N / \varepsilon ) )$ such that $U _ { R } ^ { \dot { \imath } } U _ { L }$ is a $( \mu _ { p } ( A ) , \lceil \log ( N + M + 1 ) \rceil , \varepsilon )$ -block-encoding of $\overline { { A } }$ . 2. On the other hand, if $A$ is stored in a quantum-accessible data structure16, then there exist unitaries $U _ { R }$ and $U _ { L }$ that can be implemented in time $\mathcal { O } ( \mathsf { p o l y l o g } ( M N ) / \varepsilon )$ such that $U _ { R } ^ { \bar { \prime } } U _ { L }$ is $a$ $( \left. A \right. _ { F }$ , $\lceil \log ( M + N ) \rceil , \varepsilon )$ -block-encoding of $\overline { { A } }$ .

(Note that in the above lemma one could replace ${ \overline { { A } } } \ \mathsf { b y } \ A ,$ the proof remains almost the same.)

This allows us to apply our block-encoding results in the quantum data structure setting, including Hamiltonian simulation (Section 4.1), quantum linear system solvers (Section 4.3) and implementing negative powers of a Hamiltonian (Section 4.3).

We now proceed with the proof of Lemma 25.

Proof. Similarly to [KP17, Theorem 4.4], for $j \in [ M ] ,$ we define

$$
| \psi _ { j } \rangle = \frac { \sum _ { k \in [ N ] } A _ { j , k } ^ { p } | j , M + k \rangle } { \sqrt { s _ { 2 p } ( A ) } } + \sqrt { 1 - \frac { \sum _ { k \in [ N ] } A _ { j , k } ^ { 2 p } } { s _ { 2 p } ( A ) } } | j , N + M + 1 \rangle
$$

and for $k \in [ N ] ,$ define

$$
| \psi _ { M + k } \rangle = \frac { \sum _ { j \in [ M ] } A _ { j , k } ^ { 1 - p } | M + k , j \rangle } { \sqrt { s _ { 2 ( 1 - p ) } ( A ^ { T } ) } } + \sqrt { 1 - \frac { \sum _ { j \in [ M ] } A _ { j , k } ^ { 2 ( 1 - p ) } } { s _ { 2 ( 1 - p ) } ( A ^ { T } ) } | M + k , M + N + 1 \rangle } .
$$

For $j \in [ M ] ,$ define

$$
| \phi _ { j } \rangle = \frac { \sum _ { k \in [ N ] } A _ { j , k } ^ { p } | M + k , j \rangle } { \sqrt { s _ { 2 p } ( A ) } } + \sqrt { 1 - \frac { \sum _ { k \in [ N ] } A _ { j , k } ^ { 2 p } } { s _ { 2 p } ( A ) } } | M + N + 1 , j \rangle ,
$$

and for $k \in [ N ] ,$ define

$$
| \phi _ { M + k } \rangle = \frac { \sum _ { j \in [ M ] } A _ { j , k } ^ { 1 - p } | j , M + k \rangle } { \sqrt { s _ { 2 ( 1 - p ) } ( A ^ { T } ) } } + \sqrt { 1 - \frac { \sum _ { j \in [ M ] } A _ { j , k } ^ { 2 ( 1 - p ) } } { s _ { 2 ( 1 - p ) } ( A ^ { T } ) } } | M + N + 1 , M + k \rangle .
$$

Then for $j , j ^ { \prime } \in [ M ] ,$ and $k , k ^ { \prime } \in [ N ] ,$ we have

$$
\langle \psi _ { j } | \phi _ { j ^ { \prime } } \rangle = \langle \psi _ { M + k } | \phi _ { M + k ^ { \prime } } \rangle = 0 ,
$$

but for $( j , k ) \in [ M ] \times [ N ] ,$ we have:

$$
\langle \psi _ { j } | \phi _ { M + k } \rangle = \frac { A _ { j , k } } { \mu _ { p } ( A ) } \mathrm { ~ a n d ~ } \langle \psi _ { M + k } | \phi _ { j } \rangle = \frac { A _ { j , k } } { \mu _ { p } ( A ) } = \frac { A _ { k , j } ^ { T } } { \mu _ { p } ( A ) } .
$$

Thus, for any $i , i ^ { \prime } \in [ M + N ] , \langle \psi _ { i } | \phi _ { i ^ { \prime } } \rangle = \overline { { A } } _ { i , i ^ { \prime } } / \mu _ { p } ( A ) .$

Letting $\ell = \lceil \log ( M + N + 1 ) \rceil$ , we define a unitary $U _ { R }$ on $\mathbb { C } ^ { ( M + N ) \times 2 ^ { \ell } }$ by

$$
U _ { R } : | i \rangle | 0 ^ { \ell } \rangle \mapsto | \psi _ { i } \rangle
$$

for all $i \in [ M + N ]$ . Similarly, we define a unitary $U _ { L }$ on $\mathbb { C } ^ { ( M + N ) \times 2 ^ { \ell } }$ by

$$
U _ { L } : | i \rangle | 0 ^ { \ell } \rangle \mapsto | \phi _ { i } \rangle
$$

for all $i \in [ M + N ] .$ . Then the first result follows.

For the second result, we define, for each $j \in [ M ] ,$

$$
| \psi _ { j } \rangle = \sum _ { k \in [ N ] } \frac { A _ { j , k } } { \left\| \boldsymbol A _ { j , \cdot } \right\| } | j , M + k \rangle \mathrm { ~ a n d ~ } | \phi _ { j } \rangle = \sum _ { k \in [ N ] } \frac { A _ { j , k } } { \left\| A _ { j , \cdot } \right\| } | M + k , j \rangle ,
$$

and for each $k \in [ N ] ,$

$$
| \psi _ { M + k } \rangle = \sum _ { j \in [ M ] } \frac  \big \| A _ { j , \cdot } \big \| _ { | M + k , j \rangle \mathrm { ~ a n d ~ } } | \phi _ { M + k } \rangle = \sum _ { j \in [ M ] } \frac { \| A _ { j , \cdot } \| } { \| A \| _ { F } } | j , M + k \rangle .
$$

These vectors can be constructed from the quantum-accessible data structure described in Theorem 1, and we have, for any $j , j ^ { \prime } \in [ M ]$ and $k , k ^ { \prime } \in [ N ]$ :

$$
\langle \psi _ { j } | \phi _ { j ^ { \prime } } \rangle = \langle \psi _ { M + k } | \phi _ { M + k ^ { \prime } } \rangle = 0 , \ : \langle \psi _ { j } | \phi _ { M + k } \rangle = \frac { A _ { j , k } } { \big \| A \big \| _ { F } } \mathrm { a n d } \langle \psi _ { M + k } | \phi _ { j } \rangle = \frac { A _ { k , j } ^ { T } } { \big \| A \big \| _ { F } } .
$$

The second result follows, similarly to the first.

# 4.1 Hamiltonian simulation with quantum data structure

Low and Chuang [LC16] showed how to implement an optimal Hamiltonian simulation algorithm given a block-encoding of the Hamiltonian (Theorem 7). Their result combined with Lemma 25 gives the following:

Theorem 26 (Hamiltonian simulation using quantum data structure). For any $t \in \mathbb { R }$ and $\varepsilon \in ( 0 , 1 / 2 )$ , we have the following:

1. Fix $p \in [ 0 , 1 ]$ . Let $H \in \mathbb { C } ^ { N \times N }$ be a Hermitian matrix, and suppose $H ^ { ( p ) }$ and $( H ^ { ( 1 - p ) } ) ^ { \dag }$ are stored in quantum-accessible data structures16. Then we can implement a unitary $\widetilde { U }$ that is a $( 1 , n + 3 , \varepsilon )$ -block-encoding of $e ^ { i t H }$ in time $\widetilde { \mathcal { O } } \big ( t \mu _ { p } ( A ) \mathrm { p o l y l o g } ( N / \varepsilon ) \big )$ . 2. If $H$ is stored in a quantum-accessible data structure16, then we can implement a unitary     $\widetilde { U }$ that is a $( 1 , n + 3 , \varepsilon )$ -block-encoding of $e ^ { i t H }$ in time $\mathcal { \tilde { O } } ( t \| A \| _ { F } \mathsf { p o l y l o g } ( N / \varepsilon ) )$ .

# 4.2 Quantum singular value estimation

The quantum singular value estimation (QSVE) problem is the following17: Given access to a matrix P $A \in \mathbb { R } ^ { \bar { M } \times N }$ with singular value decomposition P $\begin{array} { r } { A = \sum _ { j } \sigma _ { j } | u _ { j } \rangle \langle v _ { j } | } \end{array}$ , and given input $\textstyle | \psi \rangle = \sum _ { j } c _ { j } | u _ { j } \rangle$ , output $\textstyle \sum _ { j } c _ { j } | \phi ( \sigma _ { j } ) \rangle | u _ { j } \rangle ,$ , where $| \phi ( \sigma _ { j } ) \rangle$ is a unit vector on a space with a phase register and an auxiliary register, such that, when the phase register is measured, it outputs an estimate of $\sigma _ { j } , \tilde { \sigma } _ { j }$ such that with probability $1 - \varepsilon , | \sigma _ { j } - \tilde { \sigma } _ { j } | \leq \Delta .$

Kerenidis and Prakash [KP16] gave a quantum algorithm for estimating singular values wherein they showed that if a matrix $A$ is stored in a quantum-accessible data structure, the singular values of $A$ can be estimated to a precision $\delta$ in time $\mathcal { \widetilde { O } } ( ( \mu / \delta ) \mathsf { p o l y l o g } ( M N ) )$ , where $\mu = \left\| A \right\| _ { F }$ , or if $A ^ { ( p ) }$ and $A ^ { ( 1 - p ) }$ are stored in quantum-accessible data structures for some p, $\mu = \mu _ { p } ( A )$ . We provide an alternative quantum algorithm for singular value estimation when the matrix $A$ is given as a block-encoding — the quantum-accessible data structure case considered by Kerenidis and Prakash is a special case of this. In the scenario where $A$ is stored in a quantum-accessible data structure, we recover the same running time as Kerenidis and Prakash.

A subsequent improved version of this algorithm, without the need for an auxiliary register in addition to the phase register, can be found in [GSLW18].

Theorem 27 (Quantum singular value estimation). Let $\varepsilon , \Delta \in ( 0 , 1 )$ , and $\begin{array} { r } { \varepsilon ^ { \prime } = \frac { \varepsilon \Delta } { 4 \log ^ { 2 } ( 1 / \Delta ) } } \end{array}$ Let $U$ . be an $( \alpha , a , \varepsilon ^ { \prime } )$ -block-encoding of a matrix $A$ that can be implemented in cost $T _ { U }$ . Then we can implement a quantum algorithm that solves $Q S V E$ of $A$ in complexity

$$
\mathcal { O } \Big ( \frac { \alpha } { \Delta } ( a + T _ { U } ) \mathsf { p o l y l o g } ( 1 / \varepsilon ) \Big ) .
$$

Proof. At a high-level, the algorithm works by using phase estimation of Hamiltonian simulation of $A _ { i }$ , however, $A$ is not necessarily Hermitian, so we instead use $\overline { { A } }$ .

Hamiltonian simulation of $\overline { { A } }$ : Let $\textstyle A = \sum _ { j = 1 } ^ { r } \sigma _ { j } | u _ { j } \rangle \langle v _ { j } |$ , where $r = \mathsf { m i n } \{ M , N \} , \{ \sigma _ { j } \} _ { j }$ are the singular values of $A _ { i }$ , while $\left| u _ { j } \right. \left( \left| \nu _ { j } \right. \right)$ are the left (right) singular vectors of $A$ . Then the matrix

$$
\begin{array} { r } { \overline { { A } } = \left[ \begin{array} { l l } { 0 } & { A } \\ { A ^ { \dagger } } & { 0 } \end{array} \right] , } \end{array}
$$

has non-zero eigenvalues $\{ \pm \sigma _ { 1 } , . . . . , \pm \sigma _ { r } \}$ and corresponding eigenvectors

$$
| \lambda _ { j } ^ { \pm } \rangle = \frac { 1 } { \sqrt { 2 } } \big ( | 0 \rangle | u _ { j } \rangle \pm | 1 \rangle | v _ { j } \rangle \big ) .
$$

Observe that for all $j \in [ r ] , | 0 \rangle | u _ { j } \rangle = \left( | \lambda _ { j } ^ { + } \rangle + | \lambda _ { j } ^ { - } \rangle \right) / \sqrt { 2 }$ . The remaining zero eigenvalues of $\overline { { A } }$ belong to span $\{ | v _ { 1 } \rangle , . . . , | v _ { r } \rangle \} ^ { \perp }$ . So any quantum state $| \psi \rangle$ that is spanned by the right singular vectors will have no support on the zero eigenspace of $\overline { { A } }$ .

If $U$ is an $( \alpha , a , \varepsilon ^ { \prime } )$ -block-encoding of $A _ { i }$ , then the unitary

$$
\begin{array} { r } { \overline { { U } } = \left[ \begin{array} { l l } { 0 } & { U } \\ { U ^ { \dagger } } & { 0 } \end{array} \right] , } \end{array}
$$

composed with appropriate SWAP gates is an $( \alpha , 2 \boldsymbol { a } , \varepsilon ^ { \prime } )$ -block encoding of $\overline { { A } }$ . So if $T _ { U }$ is the cost of implementing the unitary $U$ , then the cost of implementing $\overline { { U } }$ is $2 T _ { U } + \mathcal { O } ( 1 )$ .

From Lemma 8, there exists a unitary $V$ that is an $( 1 , 2 a + 2 , \varepsilon / 2 )$ -block encoding of $\sum _ { t = - \frac { T - 1 } { 2 } } ^ { \frac { T - 1 } { 2 } } | t \rangle \langle t | \otimes e ^ { i t \overline { { A } } }$ that can be implemented in complexity

$$
\mathcal { O } \left( \left( \frac { \alpha } { \Delta } + \log \left( \frac { 1 } { \varepsilon } \log \frac { 1 } { \Delta } \right) \right) ( a + T _ { U } ) \right) .
$$

This will be our main subroutine.

Dirichlet kernels: We will use the fact that for all $x , \vert \sin x \vert \leq \vert x \vert ,$ , and for all $x \in [ - \pi / 2 , \pi / 2 ] ,$ $| \sin x | \geq | 2 x / \pi |$ .

Let $D _ { n } ( x )$ be the Dirichlet kernel, defined:

$$
D _ { n } ( x ) = { \frac { \sin ( ( n + 1 / 2 ) x ) } { \sin ( x / 2 ) } } = \sum _ { t = - n } ^ { n } \cos ( 2 t x )
$$

This function is peaked around 0, with the peak becoming more extreme as $n$ increases. We will make use of a few easily verified facts about $D _ { n } ( x )$ :

• $\begin{array} { r } { D _ { n } ( x ) = D _ { n } ( - x ) } \end{array}$ • $\begin{array} { r } { D _ { n } ( x ) \leq \frac { 1 } { \sin ( x / 2 ) } \leq \frac { \pi } { | x | } } \end{array}$ for $x \in [ - \pi , \pi ]$ $\begin{array} { r } { D _ { n } ( x ) = \frac { \sin ( ( n + 1 / 2 ) x ) } { \sin ( x / 2 ) } \geq \frac { ( 2 n + 1 ) \delta } { \pi \delta / 2 } = \frac { 2 ( 2 n + 1 ) } { \pi } \mathrm { ~ f o r ~ } x \in [ 0 , \frac { \pi } { 2 n + 1 } ] . } \end{array}$

Algorithm: We now describe the sve algorithm. Let $T$ be an odd number such that $T \ge 2 \pi / \Delta$ Begin by generating the state:

$$
\begin{array} { r c l } { \displaystyle \sum _ { t = - \frac { T - 1 } { 2 } } ^ { \frac { T - 1 } { 2 } } \frac { 1 } { \sqrt { T } } \vert t \rangle \vert + \rangle \vert 0 \rangle \vert \psi \rangle } & { = } & { \displaystyle \sum _ { j } c _ { j } \displaystyle \sum _ { t = - \frac { T - 1 } { 2 } } ^ { \frac { T - 1 } { 2 } } \frac { 1 } { \sqrt { 2 T } } \vert t \rangle \big ( \vert 0 \rangle \vert 0 \rangle \vert u _ { j } \rangle + \vert 1 \rangle \vert 0 \rangle \vert u _ { j } \rangle \big ) } \\ & { = } & { \displaystyle \sum _ { j } c _ { j } \displaystyle \sum _ { t = - \frac { T - 1 } { 2 } } ^ { \frac { T - 1 } { 2 } } \frac { 1 } { 2 \sqrt { T } } \vert t \rangle \Big ( \vert 0 \rangle \vert \lambda _ { j } ^ { + } \rangle + \vert \lambda _ { j } ^ { - } \rangle \vert + \vert 1 \rangle \langle \vert \lambda _ { j } ^ { + } \rangle + \vert \lambda _ { j } ^ { - } \rangle \vert } \end{array}
$$

Next, we apply $e ^ { ( - 1 ) ^ { b } t { \overline { { A } } } }$ conditioned on $| t \rangle | b \rangle$ in the first registers, to get:

$$
\sum _ { j } c _ { j } \sum _ { t = - \frac { \tau _ { - 1 } } { 2 } } ^ { \frac { T - 1 } { 2 } } \frac { 1 } { 2 \sqrt { T } } | t \rangle \Big ( | 0 \rangle ( e ^ { i t \sigma _ { j } } | \lambda _ { j } ^ { + } \rangle + e ^ { - i t \sigma _ { j } } | \lambda _ { j } ^ { - } \rangle ) + | 1 \rangle ( e ^ { - i t \sigma _ { j } } | \lambda _ { j } ^ { + } \rangle + e ^ { i t \sigma _ { j } } | \lambda _ { j } ^ { - } \rangle ) .
$$

We perform a Hadamard gate on the second register, to get:

$$
\begin{array} { r l } { { } } & { { \displaystyle \sum _ { j } c _ { j } \sum _ { t = - \frac { T - 1 } { 2 } } ^ { \frac { T - 1 } { 2 } } \frac { 1 } { \sqrt { 2 T } } | t \rangle \Big ( \cos ( t \sigma ) | 0 \rangle ( | \lambda _ { j } ^ { + } \rangle + | \lambda _ { j } ^ { - } \rangle ) + i \sin ( t \sigma ) | 1 \rangle ( | \lambda _ { j } ^ { + } \rangle - | \lambda _ { j } ^ { - } \rangle ) \Big ) } } \\ { { = } } & { { \displaystyle \sum _ { j } c _ { j } \sum _ { t = - \frac { T - 1 } { 2 } } ^ { \frac { T - 1 } { 2 } } \frac { 1 } { \sqrt { T } } | t \rangle \big ( \cos ( t \sigma ) | 0 \rangle | 0 \rangle | u _ { j } \rangle + i \sin ( t \sigma ) | 1 \rangle | 1 \rangle | v _ { j } \rangle \big ) . } } \end{array}
$$

We are interested in the part of the state with $| 0 \rangle$ in the second register. This part of the state has squared amplitude:

$$
\begin{array} { r c l } { \displaystyle \beta ^ { 2 } : = \sum _ { t = - \frac { T - 1 } { 2 } } ^ { \frac { T - 1 } { 2 } } \frac { 1 } { T } \cos ^ { 2 } ( t \sigma _ { j } ) } & { = } & { \displaystyle \frac { 1 } { 2 T } \sum _ { t = - \frac { T - 1 } { 2 } } ^ { \frac { T - 1 } { 2 } } \big ( 1 + \cos ( 2 t \sigma _ { j } ) \big ) } \\ & { = } & { \displaystyle \frac { 1 } { 2 } + \frac { 1 } { 2 T } D _ { \frac { - 1 } { 2 } } ( 2 \sigma _ { j } ) \geq \frac { 1 } { 2 } - \frac { 1 } { 2 T } \frac { T - 1 } { 4 } = \frac { 3 } { 8 } , } \end{array}
$$

where in the last line, we have used a lower bound on the Dirichlet kernel, $D _ { \frac { T - 1 } { 2 } } ( 2 \sigma _ { j } ) \geq - C ^ { \frac { T - 1 } { 2 } } .$ , where $C < 1 / 2$ is the absolute minimum of $2 \sin ( x ) / x$ (See, for example, [Mer]). We will consider the $| 1 \rangle$ part of the state the “bad” part of the state, and the $| 0 \rangle$ part of the state the “good” part of the state. We analyze the remainder of the algorithm’s action on the “good” part of the state, which is:

$$
\beta ^ { - 1 } \sum _ { j } c _ { j } \sum _ { t = - \frac { \tau _ { - 1 } } { 2 } } ^ { \frac { T - 1 } { 2 } } \frac { 1 } { \sqrt { 2 T } } | t \rangle \cos ( t \sigma _ { j } ) | 0 \rangle ( | \lambda _ { j } ^ { + } \rangle + | \lambda _ { j } ^ { - } \rangle ) = \beta ^ { - 1 } \sum _ { j } c _ { j } \sum _ { t = - \frac { \tau _ { - 1 } } { 2 } } ^ { \frac { T - 1 } { 2 } } \frac { 1 } { \sqrt { T } } | t \rangle \cos ( t \sigma _ { j } ) | 0 \rangle | u _ { j } \rangle ,
$$

Discarding the second register, and performing a Fourier transform on the first, we get:

$$
\begin{array} { r l } & { \beta ^ { - 1 } \displaystyle \sum _ { j } c _ { j } \sum _ { z = - \frac { I - 1 } { 2 } } ^ { \frac { I - 1 } { 2 } } \left( \frac { 1 } { T } \sum _ { t = - \frac { I - 1 } { 2 } } ^ { \frac { I - 1 } { 2 } } \cos ( t \sigma _ { j } ) e ^ { i 2 \pi t / T } \right) | z \rangle | u _ { j } \rangle } \\ { = } & { \beta ^ { - 1 } \displaystyle \sum _ { j } c _ { j } \sum _ { z = - \frac { I - 1 } { 2 } } ^ { \frac { I - 1 } { 2 } } \left( \frac { 1 } { 2 T } \sum _ { t = - \frac { I - 1 } { 2 } } ^ { \frac { I - 1 } { 2 } } e ^ { i t ( 2 \pi z / T + \sigma _ { j } ) } + \frac { 1 } { 2 T } \sum _ { t = - \frac { I - 1 } { 2 } } ^ { \frac { I - 1 } { 2 } } e ^ { i t ( 2 \pi z / T - \sigma _ { j } ) } \right) | z \rangle | u _ { j } \rangle } \\ { = } & { \beta ^ { - 1 } \displaystyle \sum _ { j } c _ { j } \sum _ { z = - \frac { I - 1 } { 2 } } ^ { \frac { I - 1 } { 2 } } \frac { 1 } { 2 T } \left( D _ { \frac { I - 1 } { 2 } } \left( \frac { 2 \pi z } { T } + \sigma _ { j } \right) + D _ { \frac { I - 1 } { 2 } } \left( \frac { 2 \pi z } { T } - \sigma _ { j } \right) \right) | z \rangle | u _ { j } \rangle . } \end{array}
$$

Thus, we are adding two functions of $| z \rangle$ : one peaking around $z \approx - \frac { T \sigma _ { j } } { 2 \pi }$ , and the other around $\begin{array} { r } { z \approx \frac { T \sigma _ { j } } { 2 \pi } } \end{array}$ Finally, we can reversibly map $| z \rangle$ to $\left| { \sf s g n } ( z ) \right. \left| \left| z \right| \right.$ , where $\left| { \sf s g n } ( z ) \right.$ is 0 if $z = 0 , + \mathrm { i f }$ $z > 0$ and $-$ if $z < 0$ . Then we have:

$$
| \phi ( \sigma _ { j } ) \rangle = \beta ^ { - 1 } \sum _ { z = - \frac { \tau - 1 } { 2 } } ^ { \frac { \tau - 1 } { 2 } } \frac { 1 } { 2 T } \bigg ( D _ { \frac { \tau - 1 } { 2 } } \bigg ( \frac { 2 \pi z } { T } + \sigma _ { j } \bigg ) + D _ { \frac { \tau - 1 } { 2 } } \bigg ( \frac { 2 \pi z } { T } - \sigma _ { j } \bigg ) \bigg ) | \mathrm { s g n } ( z ) \rangle | | z | \rangle .
$$

We will interpret $| z |$ as an estimate $\pi | z | / T$ of $\sigma _ { j }$

Correctness: Fix some $j ,$ and let $Z ^ { * }$ be the closest integer to $\frac { T \sigma _ { j } } { 2 \pi }$ Define $\begin{array} { r } { \delta = \sigma _ { j } - \frac { 2 \pi z ^ { * } } { T } } \end{array}$ , so $\begin{array} { r } { | \delta | \le { \frac { \pi } { T } } } \end{array}$ . We will first argue that if we measure the last register of $| \phi ( \sigma _ { j } ) \rangle$ , we will get $Z ^ { * }$ with probability at least ${ \frac { 1 } { 4 } } ( 2 / \pi - 1 / 4 ) ^ { 2 } >$ .037. Suppose $z ^ { * } \neq 0$ . In that case, we can measure either $| - , z ^ { * } \rangle$ or $| + , z ^ { * } \rangle$ , with respective probabilities at least:

$$
\beta ^ { - 2 } \biggl | \frac { 1 } { 2 T } \left( D _ { \frac { T - 1 } { 2 } } \left( \frac { 2 \pi z ^ { * } } { T } + \sigma _ { j } \right) + D _ { \frac { T - 1 } { 2 } } \left( \frac { 2 \pi z ^ { * } } { T } - \sigma _ { j } \right) \right) \biggr | ^ { 2 }
$$

and

$$
\beta ^ { - 2 } \frac { 1 } { 2 T } \Bigg | \Bigg ( D _ { \frac { T - 1 } { 2 } } \left( - \frac { 2 \pi z ^ { * } } { T } + \sigma _ { j } \right) + D _ { \frac { T - 1 } { 2 } } \left( - \frac { 2 \pi z ^ { * } } { T } - \sigma _ { j } \right) \Bigg ) \Bigg | ^ { 2 } .
$$

These are equal, by the symmetry of $D _ { \frac { T - 1 } { 2 } }$ , so the total probability of measuring $Z ^ { * }$ is:

$$
\begin{array} { r l r } & { } & { 2 \beta ^ { - 2 } \bigg | \displaystyle \frac { 1 } { 2 T } \bigg ( D _ { \frac { T - 1 } { 2 } } \left( \frac { 2 \pi z ^ { * } } { T } + \sigma _ { j } \right) + D _ { \frac { T - 1 } { 2 } } \left( \frac { 2 \pi z ^ { * } } { T } - \sigma _ { j } \right) \bigg ) \bigg | ^ { 2 } } \\ & { \geq } & { \displaystyle \frac { 1 } { 2 T ^ { 2 } } \bigg | D _ { \frac { T - 1 } { 2 } } ( | \delta | ) + D _ { \frac { T - 1 } { 2 } } \left( \frac { 2 \pi z ^ { * } } { T } + \sigma _ { j } \right) \bigg | ^ { 2 } \qquad \mathrm { s i n c e } \ \beta \leq 1 } \\ & { \geq } & { \displaystyle \frac { 1 } { 2 T ^ { 2 } } \bigg | \displaystyle \frac { 2 T } { \pi } - \frac { T - 1 } { 4 } \bigg | ^ { 2 } \geq \frac { 1 } { 2 } ( 2 / \pi - 1 / 4 ) ^ { 2 } \qquad \mathrm { s i n c e } \ | \delta | \leq \pi / T . } \end{array}
$$

The case for $z ^ { * } = 0$ is similar, but the probability is only half as much, since there is only one contribution.

Next, for an integer $d$ , let $p _ { d }$ be the probability we measure $z ^ { * } + d$ . We can upper bound this as

$$
\begin{array} { r c l } { \displaystyle p _ { d } } & { = } & { \displaystyle 2 \beta ^ { - 2 } \bigg | \frac { 1 } { 2 T } \bigg ( D _ { \frac { T - 1 } { 2 } } \bigg ( \frac { 2 \pi ( z ^ { * } + d ) } { T } + \sigma _ { j } \bigg ) + D _ { \frac { T - 1 } { 2 } } \bigg ( \frac { 2 \pi ( z ^ { * } + d ) } { T } - \sigma _ { j } \bigg ) \bigg ) \bigg | ^ { 2 } } \\ & { = } & { \displaystyle 2 \beta ^ { - 2 } \bigg | \frac { 1 } { 2 T } \bigg ( D _ { \frac { T - 1 } { 2 } } \bigg ( \frac { 2 \pi ( z ^ { * } + d ) } { T } + \sigma _ { j } \bigg ) + D _ { \frac { T - 1 } { 2 } } \bigg ( \frac { 2 \pi d } { T } + \delta \bigg ) \bigg ) \bigg | ^ { 2 } } \\ & { \leq } & { \displaystyle \frac { 1 } { 2 T ^ { 2 } } \frac { 8 } { 3 } \bigg | \frac { T } { | 2 ( z ^ { * } + d ) + T \sigma _ { j } / \pi | } + \frac { T } { | 2 d + T \delta / \pi | } \bigg | ^ { 2 } } \\ & { \leq } & { \displaystyle \frac { 4 } { 3 } \bigg | \frac { 2 } { | 2 | d | - T | \delta | / \pi } \bigg | ^ { 2 } \leq \frac { 1 6 } { 3 ( 2 | d | - 1 ) ^ { 2 } } \leq \frac { 1 6 } { 3 d ^ { 2 } } . } \end{array}
$$

Then the probability of measuring a $Z$ such that $| z ^ { * } - z | \geq k$ for some $k < T$ is at most

$$
2 \sum _ { d = k } ^ { \frac { T - 1 } { 2 } - z ^ { * } } \frac { 1 6 } { 3 d ^ { 2 } } = O ( 1 / k ) .
$$

Thus, as in [CEMM98], we can boost the success probability to $\varepsilon$ of measuring $Z$ such that $\left| z - z ^ { * } \right| < 2$ at a cost of $\log ( 1 / \varepsilon )$ parallel repetitions. Note that in each repetition, only $\geq 3 / 8$ of the state will be “good”. In any branch of the superposition, we will only compute the final estimate off of those repetitions where we’re in the good state. The probability that we measure $Z$ such that $\tilde { \sigma } = \pi z / T$ satisfies $| \tilde { \sigma } - \sigma _ { j } | \le \Delta$ is at least the probability that we measure $Z$ such that $\left| \pi z ^ { * } / T - \pi z / T \right| < 2 \pi / T$ , or equivalently, $| z ^ { * } - z | < 2$ . □

In the case where $| \psi \rangle$ and $A$ are stored in a quantum-accessible data structure, we have that $\alpha = \mu$ , where $\mu = \left\| A \right\| _ { F }$ or if $A ^ { ( p ) }$ and $A ^ { ( 1 - p ) }$ are stored in quantum-accessible data structures for some $p$ , $\mu = \mu _ { p } ( A )$ . In each such case, we have $T _ { U } = \mathcal { O } ( \mathrm { p o l y l o g } ( M N / \varepsilon ) )$ and $T _ { \psi } = \mathcal { O } ( \mathsf { p o l y l o g } ( M N / \varepsilon ) )$ , which gives us a running time of

$$
\widetilde { \mathcal { O } } \left( \frac { \mu } { \Delta } \mathsf { p o l y l o g } ( M N / \varepsilon ) \right) ,
$$

and thus we recover the running time of the QSVE algorithm by Kerenidis and Prakash [KP16].

# 4.3 Quantum linear system solvers

The quantum linear system problem (QLS problem) is the following. Given access to an $N \times N$ matrix $A _ { i }$ , and a procedure for computing a quantum state $| b \rangle$ in the image of $A$ , prepare a state that is within $\varepsilon$ of $A ^ { + } | b \rangle / \big | \big | A ^ { + } | b \rangle \big |$ . As with Hamiltonian simulation, several methods of encoding the part of the input $A$ have been considered. We consider the case where $A$ is given as a block-encoding. In that case, as a special case of Lemma 9 when $c = 1$ , given a $( \alpha , a , \delta )$ -blockencoding $U$ of $A$ with implementation cost $T _ { U }$ , we can implement a $( 2 \kappa , a + \mathcal { O } ( \log ( \kappa \log ( 1 / \varepsilon ) ) ) , \varepsilon ) \mathrel { \mathop : }$ - block-encoding of $A ^ { - 1 }$ , assuming $\delta = o ( \varepsilon / ( \kappa ^ { 2 } \log ^ { 3 } \frac { \kappa } { \varepsilon } ) )$ , in complexity $\mathcal { O } ( \alpha \kappa ( a + T _ { U } ) \mathrm { p o l y l o g } ( \kappa / \varepsilon ) )$ . 18

From this block-encoding of $A ^ { - 1 }$ , we can solve the QLS problem by applying the unitary $U$ to the state $| b \rangle$ , and then doing amplitude amplification. However, since $U$ is a $( 2 \kappa , a + \mathcal { O } ( \log ( \kappa \log ( 1 / \varepsilon ) ) ) , \varepsilon ) .$ -block-encoding, we will require a number of amplitude amplification rounds that is linear in $\kappa ,$ , giving an overall quadratic dependence on $\kappa$ . Quantum linear system solvers in the sparse-access input model have only a linear dependence on $\kappa ,$ , thanks to techniques of Ambainis [Amb12], which were also successfully applied in a setting more similar to ours by Childs, Kothari and Somma [CKS17]. Using these techniques, we can also reduce our dependence on $\kappa$ to linear.

Reducing the dependence on condition number. To reduce the dependence on $\kappa ,$ we use the technique of variable time amplitude amplification (VTAA) instead of standard amplitude amplification. For this, we need to adapt the quantum linear systems algorithm to be a variable-stopping-time algorithm, to which VTAA can be applied (see Section 3.1). Our setting is similar to that of Childs, Kothari and Somma [CKS17], so we will follow their notation and proof.

First we formally state a version of quantum phase estimation that determines whether an eigenphase $\lambda \in [ - 1 , 1 ]$ of a given unitary $U$ satisfies $0 \leq | \lambda | \leq \phi$ or $2 \phi \le | \lambda | \le 1$ . This is known as gapped quantum phase estimation (GPE) and was introduced in [CKS17]. We restate it here.

Lemma 28 (Gapped phase estimation [CKS17]). Let $U$ be a unitary such that $U | \lambda \rangle = e ^ { i \lambda } | \lambda \rangle$ and $\lambda \in [ - 1 , 1 ]$ . Let $\phi \in \left( 0 , 1 / 4 \right]$ and $\epsilon > 0$ . Then there exists $a$ quantum algorithm that performs the transformation

$$
| 0 \rangle _ { C } | 0 \rangle _ { P } | \lambda \rangle _ { I } \mapsto \alpha _ { 0 } | 0 \rangle _ { C } | g _ { 0 } \rangle _ { P } | \lambda \rangle _ { I } + \alpha _ { 1 } | 1 \rangle _ { C } | g _ { 1 } \rangle _ { P } | \lambda \rangle _ { I } ,
$$

for some unit vectors $\left| g _ { 0 } \right.$ and $\left| g _ { 1 } \right.$ , where $C$ and $P$ are registers of 1 and $\begin{array} { r } { \mathcal { O } \left( \frac { 1 } { \phi } \log \frac { 1 } { \epsilon } \right) } \end{array}$ qubits, respectively, $| \alpha _ { 0 } | ^ { 2 } + | \alpha _ { 1 } | ^ { 2 } = 1$ and

• if $0 \leq | \lambda | \leq \phi$ then $| \alpha _ { 1 } | \le \epsilon$ and • i $m / 2 \phi \leq | \lambda | \leq 1$ then $| \alpha _ { 0 } | \le \epsilon$ .

If $T _ { U }$ is the cost of implementing $U _ { ☉ }$ , then the cost of this quantum algorithm is $\mathcal { O } \left( \frac { T _ { U } } { \phi } \log \frac { 1 } { \epsilon } \right)$ .

As a corollary to Lemma 9, which, in the special case when $c = 1$ , says we can get a block-encoding of $H ^ { - 1 }$ from a block-encoding of $H _ { \ l }$ , we have the following, which allows us to invert $H$ on a certain range of its eigenspaces:

Corollary 29 (Efficient inversion of a block-encoded matrix). Let   $\varepsilon , \lambda > 0$ and $H$ an $N \times N$ Hermitian matrix. Suppose that for $\begin{array} { r } { \delta = o \left( \varepsilon \lambda ^ { 2 } / \log ^ { 3 } { \frac { 1 } { \lambda \varepsilon } } \right) } \end{array}$ the unitary $U$ is an $( \alpha , a , \delta )$ -blockencoding of $H$ that can be implemented using $T _ { U }$ elementary gates. Then for any state $| \psi \rangle$ that is spanned by eigenvectors of $H$ with eigenvalues in the range $[ - 1 , - \lambda ] \cup [ \lambda , 1 ] ,$ there exists a unitary $W ( \lambda , \varepsilon )$ that implements

$$
W ( \lambda , \varepsilon ) | 0 \rangle _ { F } | 0 \rangle _ { Q } | \psi \rangle _ { I } = \frac { 1 } { \alpha _ { \mathrm { m a x } } } | 1 \rangle _ { F } | 0 \rangle _ { Q } f ( H ) | \psi \rangle _ { I } + | 0 \rangle _ { F } | \widetilde { \psi } ^ { \bot } \rangle _ { Q I }
$$

where $\alpha _ { \mathrm { m a x } } \leq \lambda$ is a constant, $| \widetilde { \psi } ^ { \perp } \rangle _ { Q I }$ is an unnormalized quantum state, orthogonal to $| 0 \rangle _ { Q }$ and $\left\| f ( H ) | \psi \rangle - H ^ { - 1 } | \psi \rangle \right\| \leq \varepsilon$ . Here $F , Q$ and $I$ are registers of 1 qubit, $\alpha$ qubits and $\mathsf { l o g } ( N )$ qubits respectively. The cost of implementing $W ( \lambda , \varepsilon )$ is

$$
\mathcal { O } \left( \alpha \lambda ^ { - 1 } \log ^ { 2 } \left( \frac { 1 } { \lambda \varepsilon } \right) ( a + T _ { U } ) \right) .
$$

Proof. Let $H _ { \lambda }$ be the restriction of $H$ to its eigenspaces with corresponding eigenvalues in $[ - 1 , - \lambda ] \cup [ \lambda , 1 ]$ . An application of Lemma 9 with $c = 1$ and $\kappa = \lambda ^ { - 1 }$ yields a $( 2 \lambda ^ { - 1 } , a +$ $\mathcal { O } \big ( \log ( \lambda ^ { - 1 } \log \frac { 1 } { \lambda \varepsilon } ) \big ) , \varepsilon \big )$ block encoding of $H _ { \lambda } ^ { - 1 }$ . That is, there exists a unitary $\widetilde { U }$ such that

$$
{ \widetilde { U } | 0 \rangle } _ { Q } | \psi \rangle _ { I } = \frac { \lambda } { 2 } | 0 \rangle _ { Q } f ( H ) | \psi \rangle _ { I } + | { \widetilde { \psi } ^ { \perp } \rangle } _ { Q I } ,
$$

where $\left| { \big | } f ( H ) | \psi \rangle - H ^ { - 1 } | \psi \rangle \right| \leq \varepsilon$ whenever $| \psi \rangle$ is a unit vector in the span of eigenvectors of $H$ with eigenvalues in $[ - 1 , - \lambda ] \cup [ \lambda , 1 ]$ . $\mathsf { B y }$ Lemma 9, such a $\widetilde { U }$ can be implemented in complexity given by the expression in (12).

If we add a single qubit flag register, initialized to $| 0 \rangle _ { F }$ to the aforementioned procedure, and flip this register controlled on the register $Q$ being in the state $| 0 \rangle$ , then the resulting unitary $\widetilde { U ^ { \prime } }$ acts as

$$
| 0 \rangle _ { F } | 0 \rangle _ { Q } | \psi \rangle _ { I } \mapsto \frac { \lambda } { 2 } | 1 \rangle _ { F } | 0 \rangle _ { Q } f ( H ) | \psi \rangle _ { I } + | 0 \rangle _ { F } | \widetilde { \psi } ^ { \bot } \rangle _ { Q I } .
$$

Finally, we implement the following rotation controlled on register $Q$ being in $| 0 \rangle$ that replaces $\lambda / 2$ with some constant $\alpha _ { \mathrm { m a x } } ^ { - 1 }$ , independent of $\lambda$ , such that19 $\alpha _ { \mathrm { m a x } } = \mathcal { O } ( \kappa )$ . That is we implement

$$
| 1 \rangle _ { F } \mapsto \frac { 2 } { \lambda \alpha _ { \mathrm { m a x } } } | 1 \rangle _ { F } + \sqrt { 1 - \frac { 4 \lambda ^ { 2 } } { \alpha _ { \mathrm { m a x } } ^ { 2 } } } | 0 \rangle _ { F } .
$$

These two operations together give us $W ( \lambda , \varepsilon )$ and the cost of implementing this is of the same order as that of implementing $\widetilde { U }$ .

Variable-time algorithm. Now we will describe a variable time algorithm $\mathcal { A }$ that, given a block-encoding of an $N \times N$ matrix $A$ , can be applied to an input state $| \psi \rangle$ to produce a state close to $A ^ { - 1 } | \psi \rangle$ . The algorithm $\mathcal { A }$ can be thought of as a sequence of steps $\mathcal { A } _ { 1 } , \ldots , \mathcal { A } _ { m }$ , where $m = \lceil \log _ { 2 } \kappa \rceil + 1$ . The goal is that the whole algorithm retains a block-encoded form so that it enables us to use this easily in applications in subsequent sections. $\mathcal { A }$ will work on the following registers:

• $m$ single-qubit clock registers $C _ { 1 } , \ldots , C _ { m }$ , collectively referred to as $C$ .   
• An input register $I _ { \iota }$ initialized to $| \psi \rangle$ .   
• A single qubit flag register $F$ , used to indicate success.   
• $m$ registers $P _ { 1 } , \ldots , P _ { m }$ used as ancilla for GPE.   
• An ancilla register $Q$ required for the block-encoding, initialized to $| 0 \rangle ^ { \otimes a }$ .

Let $\epsilon ^ { \prime } = \varepsilon / ( m \alpha _ { \mathrm { m a x } } )$ . We define algorithm ${ \mathcal { A } } _ { j } ,$ as follows:

1. If $C _ { 1 } , \dotsc , C _ { j - 1 }$ is in the state $| 0 \rangle ^ { \otimes ( j - 1 ) }$ , apply GPE to $e ^ { i A }$ , defined in Lemma 28, with precision $2 ^ { - j }$ and accuracy $\epsilon ^ { \prime }$ to input $| \psi \rangle$ , using $P _ { j }$ as workspace, and writing the output qubit in $C _ { j }$ .   
2. If $C _ { j }$ is now in the state $| 1 \rangle$ , apply the unitary $W ( 2 ^ { - j } , \epsilon ^ { \prime } )$ , as defined in Corollary 29, on $I \otimes F \otimes Q$ .

We shall also require algorithms $\mathcal { A } ^ { \prime } = \mathcal { A } _ { m } ^ { \prime } \ldots \mathcal { A } _ { 1 } ^ { \prime }$ that are similar to $\mathcal { A }$ except that in step 2, $\mathcal { A } _ { j } ^ { \prime }$ implements the following:

$$
W ^ { \prime } | \psi \rangle _ { I } | 0 \rangle _ { F } | 0 \rangle _ { Q } = | \psi \rangle _ { I } | 1 \rangle _ { F } | 0 \rangle _ { Q } .
$$

Then we can define the final variable time algorithm formally using the following lemma.20

Theorem 30 (Variable-time quantum linear systems algorithm). Let $\kappa \geq 2 ,$ , and $H$ be an $N \times N$ Hermitian matri $\kappa ^ { 2 1 }$ such that the non-zero eigenvalues of $H$ lie in the range $[ - 1 , - 1 / \kappa ] \bigcup [ 1 / \kappa , 1 ] .$ . Suppose that for $\delta = o \left( \varepsilon / ( \kappa ^ { 2 } \log ^ { 3 } { \frac { \kappa } { \varepsilon } } ) \right)$ we have a unitary $U$ that is a $( \alpha , a , \delta )$ -block-encoding of $H$ that can be implemented using $T _ { U }$ elementary gates. Also suppose that we can prepare an input state $| \psi \rangle$ which spans the eigenvectors of $H$ in time $T _ { \psi }$ . Then there exists a variable time quantum algorithm that outputs a state that is $\varepsilon$ -close to $\left| H ^ { - 1 } | \psi \rangle / \right| \left| H ^ { - 1 } | \psi \rangle \right|$ at a cost

$$
\mathcal { O } \Big ( \kappa \Big ( \alpha \big ( T _ { U } + a \big ) \log ^ { 2 } \Big ( \frac { \kappa } { \varepsilon } \Big ) + T _ { \psi } \Big ) \log ( \kappa ) \Big ) .
$$

Proof. Given an $( \alpha , a , \delta )$ -block encoding of $H$ , we append some ancilla qubits in order to be in the framework for applying VTAA to algorithm $\mathcal { A }$ . At the end of the algorithm we will discard these additional registers. We append a single qubit flag register $F$ , and registers $C , P$ and $Q$ (defined previously) all initialized in $| 0 \rangle$ . So now we are in a framework where the VTAA can be applied to algorithm $\mathcal { A }$ to the state $| \psi \rangle _ { I } | 0 \rangle _ { C P F Q }$ . The final algorithm $\nu$ involves using VTAA from Theorem 23 to $\mathcal { A }$ . The resulting output is a state that has performed $r ( H ) | \psi \rangle$ conditioned on the flag register being in $| 1 \rangle _ { F }$ . Subsequently, we apply the unitary $( A ^ { \prime } ) ^ { \dag }$ that erases the ancillary states. The final algorithm results in the following transformation

$$
\mathcal { V } | \psi \rangle _ { I } | 0 \rangle _ { C F P Q } \mapsto \frac { f ( H ) | \psi \rangle _ { I } } { \left| \left| f ( H ) | \psi \rangle _ { I } \right| \right| } | 0 \rangle _ { C F P Q } ,
$$

such that $\left\| { \frac { f ( H ) } { \left\| f ( H ) \vert \psi \rangle \right\| } } - { \frac { H ^ { - 1 } } { \left\| H ^ { - 1 } \vert \psi \rangle \right\| } } \right\| \leq { \mathcal { O } } ( \varepsilon )$ . We can then discard ancilla registers $C , F$ , and $P$ . So the transformation in the space ${ \big / } \otimes Q$ is

$$
| \psi \rangle _ { I } | 0 \rangle _ { Q } \mapsto \frac { f ( H ) | \psi \rangle _ { I } } { \left| \left| f ( H ) | \psi \rangle _ { I } \right| \right| } | 0 \rangle _ { Q } .
$$

The correctness of this algorithm is similar to that of Childs, Kothari and Somma [CKS17]. Let the input quantum state $\begin{array} { r } { | \psi \rangle = \sum _ { k } c _ { k } | \lambda _ { k } \rangle } \end{array}$ , where $| \lambda _ { k } \rangle ^ { \prime } s$ are the eigenstates of $H _ { \cdot }$ . Let us consider an eigenstate of $H$ , say $| \lambda \rangle$ with eigenvalue $\lambda \in [ - 1 , 1 ]$ such that $2 ^ { - j } < | \lambda | < 2 ^ { 1 - j }$ for $1 \leq j \leq m$ . Such a $j$ exists because $1 / \kappa \leq | \lambda | \leq 1$ . For such a $\lambda ,$ applying $\mathcal { A } _ { j - 1 } \ldots \mathcal { A } _ { 1 }$ to the state $| \lambda \rangle _ { I } | 0 \rangle _ { C F P Q }$ , does nothing but modify the ancilla registers $P _ { j - 1 } , \ldots , P _ { 1 }$ due to the output of GPE. This is because the precision of GPE for any of $\boldsymbol { \mathcal { A } } _ { k }$ such that $1 \leq k \leq j - 1$ is greater than $2 ^ { - j }$ and the register $C _ { k }$ for $1 \leq k \leq j - 1$ is always in $| 0 \rangle$ .

When $A _ { j }$ is applied, however, the output of GPE is in a superposition of $| 0 \rangle$ and $| 1 \rangle$ on $C _ { j } ,$ as $2 ^ { - j } < | \lambda | < 2 ^ { 1 - j }$ . So in the part of the resulting state where register $C$ is not in $| 0 \rangle ^ { \otimes m }$ , step 2 of $A _ { j }$ is implemented and $W ( 2 ^ { - j } , \epsilon ^ { \prime } )$ is applied to $I \otimes F \otimes Q$ . The computation stops on this part of the resulting state as register $C$ is non-zero. On the other hand, on the part where register $C$ is in $| 0 \rangle ^ { \tilde { \otimes } m }$ , the computation continues. Applying $\boldsymbol { A } _ { j + 1 }$ to this part, first results in $| 1 \rangle$ in $C _ { j + 1 }$ with a very high probability as $| \lambda | > 2 ^ { - j }$ . Applying step 2 of $\boldsymbol { A } _ { j + 1 }$ again implements $W ( 2 ^ { - j - 1 } , \epsilon ^ { \prime } )$ on $I \otimes F \otimes Q$ . Since the resulting state has no overlap with $| 0 \rangle _ { C } , \mathcal { A } _ { j + 2 } \dots \mathcal { A } _ { m }$ has no effect.

We observe that actually for any $2 ^ { - j } < | \lambda | < 2 ^ { 1 - j }$ , only $A _ { j }$ and $\boldsymbol { A } _ { j + 1 }$ implements $H ^ { - 1 }$ through the unitary $W$ defined in Corollary 29. The requirements of Corollary 29 are satisfied as $\lambda$ lies between $[ - 1 , 2 ^ { - j } ] \cup [ 2 ^ { - j } , 1 ^ { - }$ ] and also between $[ - 1 , 2 ^ { - j - 1 } ] \cup [ 2 ^ { - j - 1 } ,$ 1].

$\mathsf { B y }$ linearity on $\begin{array} { r } { | \psi \rangle ~ = ~ \sum _ { k } c _ { k } | \lambda _ { k } \rangle } \end{array}$ , the algorithm $\mathcal { A }$ implements $H ^ { - 1 } / \alpha _ { \mathrm { m a x } }$ on register $I$ conditioned on the flag register being in $| 1 \rangle _ { F }$ . Next VTAA is applied to the resulting state and following that $( A ^ { \prime } ) ^ { \dag }$ is used to erase the ancilla registers and output the state in (13). For more details, readers can refer to [CKS17].

Next, we analyse the complexity of this algorithm. Note that the complexity of $\nu$ is the same order as the cost of applying VTAA to algorithm $\mathcal { A }$ as the cost of running algorithm $( A ^ { \prime } ) ^ { \dag }$ is at most twice that of $\mathcal { A }$ . So the contribution of $( A ^ { \prime } ) ^ { \dag }$ to the overall complexity can be ignored.

To estimate the cost of implementing each algorithm $A _ { j }$ we first observe that the cost of implementing GPE with precision $2 ^ { - j }$ and error probability $\epsilon ^ { \prime } = \varepsilon / ( m \alpha _ { \mathrm { m a x } } )$ is

$$
\mathcal { O } \big ( \alpha 2 ^ { j } \log \big ( 1 / \epsilon ^ { \prime } \big ) ( a + T _ { U } ) \big ) ,
$$

up to additive log factors. The cost of implementing $W ( 2 ^ { - j } , \epsilon ^ { \prime } )$ is given by Corollary 29 as

$$
\mathcal { O } \left( \alpha 2 ^ { j } \log ^ { 2 } \frac { 2 ^ { j } } { \epsilon ^ { \prime } } ( a + T _ { U } ) \right) .
$$

So the time required to implement $A _ { j }$ is

$$
\mathcal { O } \left( \alpha 2 ^ { j } \log ^ { 2 } \frac { 2 ^ { j } } { \epsilon ^ { \prime } } ( a + T _ { U } ) \right) .
$$

This implies that the time $t _ { j }$ required to implement $\mathcal { A } _ { j } \ldots \mathcal { A } _ { 1 }$ is also

$$
\mathcal { O } \left( \alpha 2 ^ { j } \log ^ { 2 } \frac { \kappa } { \epsilon ^ { \prime } } ( a + T _ { U } ) \right) .
$$

Also, $T _ { \mathrm { m a x } }$ , the time required to execute $\mathcal { A } _ { m } \ldots \mathcal { A } _ { 1 }$ is

$$
T _ { \mathrm { m a x } } = \mathcal { O } \left( \alpha \kappa \log ^ { 2 } \frac { \kappa } { \epsilon ^ { \prime } } ( a + T _ { U } ) \right) = \mathcal { O } \left( \alpha \kappa ( a + T _ { U } ) \log ^ { 2 } \left( \frac { \kappa \log \kappa } { \varepsilon } \right) \right) .
$$

Now in order to upper bound the cost of applying VTAA to the algorithm $\mathcal { A }$ , we need to now upper bound the probability that $\mathcal { A }$ stops at the $j { \cdot }$ -th step. This is given by $p _ { j } ~ =$ $\left\| \Pi _ { C _ { j } } \pmb { A } _ { j } \ldots \pmb { A } _ { 1 } | \psi \rangle _ { I } | 0 \rangle _ { C F P Q } \right\| ^ { 2 } , 2 2$ where $\Pi _ { C _ { j } }$ denotes the projector on to $| 1 \rangle _ { C _ { j } }$ . Then we can calculate the $l _ { 2 }$ -averaged stopping time of ${ \mathcal { A } } , \left. { \boldsymbol { T } } \right. _ { 2 }$ as

$$
\begin{array} { r l } & { \| T \| _ { 2 } ^ { 2 } = \displaystyle \sum _ { j } p _ { j } t _ { j } ^ { 2 } } \\ & { \qquad = \displaystyle \sum _ { \lambda } \left\| \Pi _ { C , d } { \boldsymbol { \lambda } } _ { j } \cdots A _ { 1 } | { \boldsymbol { \hat { \mu } } } \rangle _ { j } | 0 \rangle _ { C E P \downarrow } \right\| ^ { 2 } t _ { j } ^ { 2 } } \\ & { \qquad = \displaystyle \sum _ { k } | c _ { k } | ^ { 2 } \sum _ { j } \left( \left\| \Pi _ { C , d } { \boldsymbol { \lambda } } _ { j } \cdots A _ { 1 } | { \boldsymbol { \lambda } } _ { k } \rangle | 0 \rangle _ { C E P \theta } \right\| ^ { 2 } t _ { j } ^ { 2 } \right) } \\ & { \qquad = \displaystyle \mathcal { O } \left( \alpha ^ { 2 } ( \alpha + T \omega ) ^ { 2 } \frac { | c _ { k } | ^ { 2 } } { k } \log ^ { 4 } \frac { 1 } { \lambda _ { k } ^ { 2 } } \right) } \\ & { \qquad \implies \| T \| _ { 2 } \le \alpha ( \alpha + T \omega ) \log ^ { 2 } \left( \frac { k [ \log \alpha ] } { \varepsilon } \right) \sqrt { \displaystyle \sum _ { k } \left| \frac { c _ { k } | ^ { 2 } } { \lambda _ { k } ^ { 2 } } \right| } . } \end{array}
$$

The final thing that we need for calculating the final complexity of VTAA applied to $\mathcal { A }$ is the success probability, $p _ { \mathsf { s u c c } }$ which can be written as

$$
\begin{array} { l } { \sqrt { p _ { \mathrm { s u c c } } } = \left\| \Pi _ { \cal F } \frac { H ^ { - 1 } } { \alpha _ { \mathrm { m a x } } } | \psi \rangle _ { I } | \Phi \rangle _ { C F P Q } \right\| + { \mathcal O } \bigl ( m \epsilon ^ { \prime } \bigr ) } \\ { = \displaystyle \frac { 1 } { \alpha _ { \mathrm { m a x } } } \left( \displaystyle \sum _ { k } \frac { | c _ { k } | ^ { 2 } } { \lambda _ { k } ^ { 2 } } \right) ^ { 1 / 2 } + { \mathcal O } \left( \frac { \varepsilon } { \alpha _ { \mathrm { m a x } } } \right) } \\ { = \Omega \left( \displaystyle \frac { 1 } { \kappa } \sqrt { \displaystyle \sum _ { k } \frac { | c _ { k } | ^ { 2 } } { \lambda _ { k } ^ { 2 } } } \right) . } \end{array}
$$

So the final complexity of applying VTAA to algorithm $\mathcal { A }$ is given by Theorem 23. Thus the

overall cost is given by (neglecting constants):

$$
\begin{array} { r l } & { T _ { \mathrm { m a x } } + T _ { \psi } + \frac { \left( \left. T \right. _ { 2 } + T _ { \psi } \right) \log \left( T _ { \mathrm { m a x } } ^ { \prime } \right) } { \sqrt { p _ { \mathrm { s u c c } } } } } \\ & { = \mathcal { O } \left( \alpha \kappa \log ^ { 2 } \left( \frac { \kappa \log \kappa } { \varepsilon } \right) \left( a + T _ { U } \right) + \kappa \left( \alpha ( a + T _ { U } ) \log ^ { 2 } \left( \frac { \kappa \log \kappa } { \varepsilon } \right) + T _ { \psi } \right) \log ( \kappa ) \right) } \\ & { = \mathcal { O } \left( \kappa \left( \alpha \left( T _ { U } + a \right) \log ^ { 2 } \left( \frac { \kappa } { \varepsilon } \right) + T _ { \psi } \right) \log ( \kappa ) \right) . } \end{array}
$$

Next we show that in the scenario where the state $| \psi \rangle$ does not belong entirely to the range of $H _ { \ l }$ , i.e. $\left| \left| \cap \mathsf { c o l } ( H ) | \psi \rangle \right| \right| < 1$ , we can prepare the state $ H ^ { + } | \psi \rangle / | | H ^ { + } | \psi \rangle | |$ . We only assume that a lower bound for $| | \Gamma \mathrm { c o i } ( H ) | \psi  |$ is known.

Corollary 31 (Complexity of pseudoinverse state preparation). Let $\kappa \geq 2 .$ , and $H$ be an $N \times N$ Hermitian matrix such that the non-zero eigenvalues of $H$ lie in the range $[ - 1 , - 1 / \kappa ] \bigcup [ 1 / \kappa , 1 ] .$ . Suppose that for $\delta = o \left( \varepsilon / ( \kappa ^ { 2 } \log ^ { 3 } \frac { \kappa } { \varepsilon } ) \right) w \epsilon$ have a unitary $U$ that is a $\mid ( \alpha , a , \delta )$ -block-encoding of $H$ that can be implemented using $T _ { U }$ elementary gates. Also suppose that we can prepare $a$ state $| \psi \rangle$ in time $T _ { \psi }$ such that $\left\| \Pi _ { \mathrm { c o l } ( H ) } | \psi \rangle \right\| \geq \sqrt { \gamma }$ . Then there exists $a$ variable time quantum algorithm that outputs $a$ state that is $\varepsilon$ -close to $\left. H ^ { + } | \psi \rangle / \right| \left| H ^ { + } | \psi \rangle \right|$ at a cost

$$
\mathcal { O } ( \kappa \Big ( \alpha \big ( T _ { U } + a \big ) \log ^ { 2 } \Big ( \frac { \kappa } { \varepsilon } \Big ) + T _ { \psi } ) \frac { \log ( \kappa ) } { \sqrt { \gamma } } ) .
$$

Proof. The result follows similarly to Theorem 30 after decreasing $p _ { \mathsf { s u c c } }$ by a factor of $\gamma$

Often, in several applications the norm of the output of the QLS problem needs to be estimated. In such cases, one needs to replace amplitude amplification with amplitude estimation. We shall use the variable time amplitude estimation algorithm (VTAE) defined in Theorem 23 in order to estimate the norm of the output of QLS which gives us an improved dependence on $\kappa$ as compared to ordinary amplitude estimation. In order to implement this, we convert the QLS algorithm to a variable-time algorithm in the same way as the case of applying VTAA. Then we have the following corollary.

Corollary 32 (Complexity of pseudoinverse state preparation and its amplitude estimation). Let $\varepsilon > 0$ . Then under the same assumptions as in Corollary 31, there exists a variable time quantum algorithm that outputs a number Γ such that

$$
1 - \varepsilon \le \frac { \Gamma } { \left\| H ^ { + } | \psi \rangle \right\| } \le 1 + \varepsilon ,
$$

at a cost

$$
\mathcal { O } ( \frac { \kappa } { \varepsilon } \Big ( \alpha \big ( T _ { U } + a \big ) \log ^ { 2 } \Big ( \frac { \kappa } { \varepsilon } \Big ) + T _ { \psi } ) \frac { \log ^ { 3 } ( \kappa ) } { \sqrt { \gamma } } \log ( \frac { \log ( \kappa ) } { \delta } ) ) ,
$$

with success probability at least $1 - \delta$ .

Proof. The framework is the same as that in Theorem 30, except instead of VTAA we use VTAE algorithm defined in Theorem 23 to obtain $\Gamma$ . Thus, the quantities $T _ { \mathrm { m a x } } , \ T _ { \mathrm { m a x } } ^ { \prime } , \ \left\| \tau \right\| _ { 2 }$ and $\sqrt { p _ { \mathsf { s u c c } } }$ are the same as in (14), (15) and (16), except $p _ { \mathsf { s u c c } }$ is decreased by a factor of $\gamma$ . Thus the overall complexity is given by Theorem 23 which is

$$
= \mathcal { O } \left( \frac { \kappa } { \varepsilon } \Big ( \alpha \big ( T _ { U } + a \big ) \log ^ { 2 } \Big ( \frac { \kappa } { \varepsilon } \Big ) + T _ { \psi } \Big ) \frac { \log ^ { 3 } ( \kappa ) } { \sqrt { \gamma } } \log \left( \frac { \log ( \kappa ) } { \delta } \right) \right) .
$$

Observe that VTAA or VTAE algorithms can be applied to a variable-time version of the algorithm that implements a block encoding of $H ^ { - c }$ , for any $c > 0$ . Consider the quantum algorithm to implement a block encoding of $H ^ { - c }$ as in Lemma 9.

In order to amplify the amplitude of the output state, we use VTAA by converting this to a variable-stopping-time algorithm. As seen before, we need to apply this procedure in certain patches of the overall domain of   $H$ . For this we use Corollary 29 and simply replace the value of $\delta$ there with $\begin{array} { r } { \delta = o \left( \varepsilon / \left( \kappa ^ { 1 + c } ( 1 + c ) \log ^ { 3 } \frac { \kappa ^ { 1 + c } } { \varepsilon } \right) \right) } \end{array}$ and $\alpha _ { \mathrm { m a x } } = \mathcal { O } ( \kappa ^ { c } )$ . So now $W ( \lambda , \varepsilon )$ implements the following transformation

$$
W ( \lambda , \varepsilon ) | 0 \rangle _ { F } | 0 \rangle _ { Q } | \psi \rangle _ { I } = \frac { 1 } { \alpha _ { \mathrm { m a x } } } | 1 \rangle _ { F } | 0 \rangle _ { Q } f ( H ) | \psi \rangle _ { I } + | 0 \rangle _ { F } | \psi ^ { \bot } \rangle _ { Q I } ,
$$

where $\alpha _ { \mathrm { m a x } } = \mathcal { O } ( \kappa ^ { c } )$ and $\left\| f ( H ) - H ^ { - c } \right\| \leq \varepsilon$ while the rest of the parameters are the same as Corollary 29. ${ \mathsf { B y } }$ using Lemma 9 we get the cost of implementing $W ( \lambda , \varepsilon )$ is

$$
\mathcal { O } \left( \frac { \alpha } { \lambda } \big ( T _ { U } + a \big ) ( 1 + c ) \log ^ { 2 } \left( \frac { \kappa ^ { 1 + c } } { \varepsilon } \right) \right) .
$$

The variable-stopping-time algorithm can be defined $\mathcal { A } = \mathcal { A } _ { m } . . . \mathcal { A } _ { 1 }$ for $m = \lceil \log _ { 2 } \kappa \rceil + 1$ . Each $A _ { j }$ can be defined in the same way as for $H ^ { - 1 }$ . So we can define a variable-time quantum algorithm, similar to Theorem 30, to implement $H ^ { - c }$ .

Theorem 33. (Variable-time quantum algorithm for implementing negative powers) Let $\kappa \geq 2 ,$ , $c \in ( 0 , \infty )$ , $q = \mathsf { m a x } ( 1 , c ) .$ , and $H$ be an $N \times N$ Hermitian matrix such that the eigenvalues   of $H$ lie in the range $[ - 1 , - 1 / \kappa ] \bigcup [ 1 / \kappa , 1 ]$ . Suppose that for $\delta = o \left( \varepsilon / \left( \kappa ^ { q } q \log ^ { 3 } { \frac { \kappa ^ { q } } { \varepsilon } } \right) \right) $ we have a unitary $U$ that is a $( \alpha , a , \delta )$ -block-encoding of $H$ which can be implemented using $T _ { U }$ elementary gates. Also suppose that we can prepare an input state $| \psi \rangle$ that is spanned by the eigenvectors of $H$ in time $T _ { \psi }$ . Then there exists $a$ variable time quantum algorithm that outputs $a$ state that is $\varepsilon$ -close to $\left. H ^ { - c } | \psi \rangle / \right| \left| H ^ { - c } | \psi \rangle \right|$ with a cost of

$$
\mathcal { O } \bigg ( \bigg ( \alpha \kappa ^ { q } \big ( T _ { U } + a \big ) q \log ^ { 2 } \bigg ( \frac { \kappa ^ { q } } { \varepsilon } \bigg ) + \kappa ^ { c } T _ { \psi } \bigg ) \log ( \kappa ) \bigg ) .
$$

Also, there exists $a$ variable time quantum algorithm that outputs a number $\Gamma$ such that

$$
1 - \varepsilon \leq \frac { \Gamma } { \left\| H ^ { - c } | \psi \rangle \right\| } \leq 1 + \varepsilon ,
$$

at a cost

$$
\mathcal { O } \left( \frac { 1 } { \varepsilon } \left( \alpha \kappa ^ { q } \big ( T _ { U } + a \big ) q \log ^ { 2 } \left( \frac { \kappa ^ { q } } { \varepsilon } \right) + \kappa ^ { c } T _ { \psi } \right) \log ^ { 3 } ( \kappa ) \log \left( \frac { \log ( \kappa ) } { \delta } \right) \right) ,
$$

with success probability at least $1 - \delta$ .

Proof. Refer to Sec. A.3 of the Appendix.

Wossnig, Zhao and Prakash [WZP18] introduced a new quantum linear system solver based on decomposing $A$ into a product of isometries and using a Szegedy walk to perform singular value estimation. In the setting where $H$ is given by a data structure as in Theorem 1, this decomposition is generic, and both isometries can be implemented efficiently given the data structure storing $H$ . The complexity of this algorithm has a better dependence on the sparsity of $H$ as compared to previous algorithms for solving quantum linear systems. Thus the algorithm of [WZP18] provides a polynomial advantage in the scenario where $H$ is non-sparse. However this algorithm has a quadratic dependence on the condition number of $H$ and a polynomial dependence on the precision of the output state. As an application of Theorem 30, we give a new quantum linear system solver in this setting, with an exponentially better dependence on precision and a linear dependence on the condition number.

We have a $N \times N$ Hermitian matrix $A$ . In this setting either (i) $A$ is stored in the quantumaccessible data structure defined in Theorem 1 or (ii) given some $p \in [ 0 , 1 ] ,$ , $A ^ { ( p ) }$ and $A ^ { ( 1 - p ) }$ are stored in quantum-accessible data structures, as was considered in [KP17]. For the QLS problem and its subsequent applications, it may be the case that $A$ is not Hermitian. In such a case either we store (i) $A$ and $A ^ { \dagger }$ in the quantum-accessible data structure or (ii) $A ^ { ( p ) }$ and $( A ^ { ( 1 - p ) } ) ^ { \dag }$ are stored in quantum-accessible data structures so that Lemma 25 is applicable. So henceforth it suffices to consider that $A$ is Hermitian.

Theorem 34 (Quantum Linear System solver with data structure). Let $\varepsilon \in ( 0 , 1 / 2 ) .$ , suppose that $\left\| A \right\| \leq 1$ , $\left\| A ^ { - 1 } \right\| \leq \kappa ,$ and either $( 1 ) { \cal A }$ is stored in a quantum-accessible data structure, in which case, let $\mu { \dot { = } } \left\| A \right\| _ { F }$ ; or $( 2 )$ for some $p \in [ 0 , 1 ] , A ^ { ( p ) }$ and $A ^ { ( 1 - p ) }$ are stored in quantumaccessible data structures, in which case, let $\mu = \mu _ { p } ( A )$ . Also assume that there is a unitary $U$ which acts on polylog $( M N / \varepsilon )$ qubits and prepares the state $| b \rangle$ with complexity $T _ { b }$ . Then (i) The QLS problem can be solved in time $\widetilde { \mathcal { O } } ( \kappa ( \mu + T _ { b } ) \mathsf { p o l y l o g } ( M N / \varepsilon ) ) .$

(ii) $I f \varepsilon \in ( 0 , 1 )$ , then an $\varepsilon$ -multiplicative approximation of $\| A ^ { + } | b  \|$ can be obtained in time $\widetilde { \mathcal { O } } \left( \frac { \kappa } { \varepsilon } ( \mu + T _ { b } ) \mathsf { p o l y l o g } ( M N ) \right)$

Proof. For (i), by Lemma 25 and Theorem 30 we can solve QLS with complexity

$$
\mathcal { O } \Big ( \left( \mu \kappa \log ^ { 2 } \Big ( \frac { \kappa } { \varepsilon } \Big ) \mathsf { p o l y l o g } ( M N / \varepsilon ) + \kappa T _ { b } \right) \mathsf { l o g } ( \kappa ) \Big ) .
$$

As shown by Corollary 32 using VTAE we can estimate $\| A ^ { + } | b  \|$ with the stated complexity.

Note that in the scenario where the vector $\overrightarrow { b } = ( b _ { 1 } , \ldots , b _ { N } ) ^ { T }$ , is also stored in a quantumaccessible data structure, then from Theorem 1 we can prepare the state $\begin{array} { r } { \left| b \right. = \sum _ { i } { b _ { i } \vert i \rangle } / \left\| \overrightarrow { b } \right\| } \end{array}$ in time $T _ { b } = \mathcal { O } ( \mathsf { p o l y l o g } ( N / \varepsilon ) )$ . Thus the complexity of solving (i) in Theorem 34 in that case, is

$$
\widetilde { \mathcal { O } } ( \kappa \mu \boldsymbol { \ p o l } \boldsymbol { \updownarrow } \boldsymbol { \updownarrow } \boldsymbol { \mathrm { l o g } } ( M N / \varepsilon ) ) ,
$$

while that of (ii) is $\widetilde { \mathcal { O } } \left( \frac { \kappa \mu } { \varepsilon } \mathsf { p o l y l o g } ( M N ) \right)$

# 5 Applications

In this section, we apply the QLS algorithm of Section 4.3 to solve the least squares problem, which is used in several machine learning applications. We present improved quantum algorithms for the weighted least squares problem (Section 5.1.1) and new quantum algorithms for the generalized least squares problem (Section 5.1.2). Finally, we apply the QLS solver to design new quantum algorithms for estimating electrical network quantities (Section 5.2).

# 5.1 Least squares

The problem of ordinary least squares is the following. Given data points $\{ ( \vec { x } ^ { ( i ) } , y ^ { ( i ) } ) \} _ { i = 1 } ^ { M }$ for $\vec { x } ^ { ( 1 ) } , \dotsc , \vec { x } ^ { ( M ) } \in \mathbb { R } ^ { N }$ and $\begin{array} { r } { { \boldsymbol { y } } ^ { ( 1 ) } , \ldots , { \boldsymbol { y } } ^ { ( M ) } \in \mathbb { R } , } \end{array}$ find $\vec { \beta } \in \mathbb { R } ^ { N }$ that minimizes:

$$
\sum _ { i = 1 } ^ { M } ( \boldsymbol { y } ^ { ( i ) } - \vec { \beta } ^ { T } \vec { x } ^ { ( i ) } ) ^ { 2 } .
$$

The motivation for this task is the assumption that the samples $( \vec { x } ^ { ( i ) } , y ^ { ( i ) } )$ are obtained from some process such that for every i, $\boldsymbol y ^ { ( i ) }$ depends linearly on $\vec { x } ^ { ( i ) }$ , up to some random noise, so $\boldsymbol y ^ { ( i ) }$ is drawn from a random variable $\vec { \beta } ^ { T } \vec { x } ^ { ( i ) } + E _ { i } ,$ where $E _ { i }$ is a random variable with mean 0, for example, a Gaussian. The vector $\vec { \beta }$ that minimizes (19) represents the underlying linear function. We assume $M \geq N$ so that it is feasible to recover this linear function.

In particular, if $\boldsymbol { X } \in \mathbb { R } ^ { M \times N }$ is the matrix with $\vec { x } ^ { ( i ) }$ as its $i .$ -th row, for each $i ,$ and $\vec { y } \in \mathbb R ^ { M }$ has $\boldsymbol { y } ^ { ( i ) }$ as its $i .$ -th entry, assuming $X ^ { T } X$ is invertible, the optimal $\vec { \beta }$ satisfies:

$$
{ \vec { \beta } } = ( X ^ { T } X ) ^ { - 1 } X ^ { T } { \vec { y } } .
$$

The assumption that $X ^ { T } X$ is invertible, or equivalently, that $\boldsymbol { X }$ has rank $N _ { \iota }$ , is very reasonable, and is generally used in least squares algorithms. This is because $X ^ { T } X \in \mathbb { R } ^ { N \times \bar { N } }$ is a sum of $M \geq N$ terms, and so it is unlikely to have rank less than $N$ .

We can generalize this task to settings in which certain samples are thought to be of higher quality than others, for example, because the random variables $E _ { i }$ are not identical. We express such a belief by assigning a positive weight $W _ { i }$ to each sample, and minimizing

$$
\sum _ { i = 1 } ^ { M } w _ { i } ( y ^ { ( i ) } - \vec { \beta } ^ { T } \vec { x } ^ { ( i ) } ) ^ { 2 } .
$$

If $W \in \mathbb { R } ^ { M \times M }$ denotes the diagonal matrix in which $w _ { i }$ appears in the $i .$ -th diagonal entry, the vector $\vec { \beta }$ that minimizes (20) is given by:

$$
\vec { \beta } = ( X ^ { T } W X ) ^ { - 1 } X ^ { T } W \vec { y } ,
$$

under the justified assumption that $X ^ { T } W X$ is invertible. Finding $\vec { \beta }$ given $X , W$ and $\vec { y }$ is the problem of weighted least squares.

We can further generalize to settings in which the random variables $E _ { i }$ for sample $i$ are correlated. In the problem of generalized least squares, the presumed correlations in error between pairs of samples are given in a non-singular covariance matrix $\Omega$ . We then want to find the vector $\vec { \beta }$ that minimizes

$$
\sum _ { i , j = 1 } ^ { M } \Omega _ { i , j } ^ { - 1 } ( y ^ { ( i ) } - \vec { \beta } ^ { T } \vec { x } ^ { ( i ) } ) ( y ^ { ( j ) } - \vec { \beta } ^ { T } \vec { x } ^ { ( j ) } ) .
$$

As long as $X ^ { T } \Omega ^ { - 1 } X$ is invertible, this minimizing vector is given by

$$
{ \vec { \beta } } = ( X ^ { T } \Omega ^ { - 1 } X ) ^ { - 1 } X ^ { T } \Omega ^ { - 1 } { \vec { y } } .
$$

In this section, we will consider solving quantum versions of these problems. Specifically, a quantum WLS solver is given access to $\vec { y } \in \mathbb R ^ { M }$ , $\boldsymbol { X } \in \mathbb { R } ^ { M \times N }$ , and positive weights $W 1 , \ldots , W M$ in some specified manner, and outputs a quantum state

$$
 ( X ^ { T } W X ) ^ { - 1 } X ^ { T } W | y \rangle / | | ( X ^ { T } W X ) ^ { - 1 } X ^ { T } W | y \rangle | | ,
$$

up to some specified error $\varepsilon$ .

Similarly, a quantum $G L S$ solver is given access to $\vec { y } \in \mathbb R ^ { M } , X \in \mathbb R ^ { M \times N } ,$ , and a positive definite $\Omega \in \mathbb { R } ^ { M \times M }$ , in some specified manner, and outputs a quantum state

$$
\begin{array} { r } { ( X ^ { T } \Omega ^ { - 1 } X ) ^ { - 1 } X ^ { T } \Omega ^ { - 1 } | y \rangle / \left. ( X ^ { T } \Omega ^ { - 1 } X ) ^ { - 1 } X ^ { T } \Omega ^ { - 1 } | y \rangle \right. , } \end{array}
$$

up to some specified error $\varepsilon$ .

# 5.1.1 Weighted least squares

In this section we describe a quantum algorithm for the weighted least squares problem using our new quantum linear system solver, before considering generalized least squares in the next section. In particular, letting $\overline { { S S } } _ { \ r { \ r { r e s } } } ^ { W }$ be the normalized weighted sum of squares residual (defined shortly), we prove the following:

Theorem 35 (Quantum WLS solver using data structure input). Let   √ $A = { \sqrt { W } } X$ such that $\left\| A ^ { + } \right\| \le \kappa _ { A }$ . Suppose $\sqrt { W } \vec { y }$ is stored in a quantum-accessible data structure, and either $( 1 )$ $A$ is stored in a quantum-accessible data structure, in which case, let $\mu ( A ) = \left\| A \right\| _ { F } ;$ or $( 2 )$ for some $p \in [ 0 , 1 ] , A ^ { ( p ) }$ and $A ^ { ( 1 - p ) }$ are stored in quantum-accessible data structures, in which case, let $\mu ( A ) = \mu _ { p } ( A )$ . Finally, suppose the data points satisfy $\overline { { S S } } _ { r e s } ^ { W } \leq \eta$ . Then we can implement a quantum WLS solver with error $\varepsilon$ in complexity:

$$
\widetilde { \mathcal { O } } \left( \frac { \kappa _ { A } \mu ( A ) } { \sqrt { 1 - \eta } } \mathsf { p o l y l o g } ( M N / \varepsilon ) \right) .
$$

Our weighted least squares algorithm improves over the previous best quantum algorithm  for this problem, due to [KP17], which has complexity $\begin{array} { r } { \mathcal { O } \left( \frac { 1 } { \varepsilon } \kappa _ { A } ^ { 6 } \mu ( A ) \log ^ { 3 } \frac { \kappa _ { A } } { \varepsilon } \mathsf { p o l y l o g } ( M N ) \right) } \end{array}$ (assuming $\left\| A \right\| = 1$ and $\eta$ is bounded by a constant $< 1$ ). Compared to this previous result, our algorithm has an exponential improvement in the dependence on $\varepsilon$ , and a 6th power improvement in the dependence on $\kappa _ { A }$ . Before proving Theorem 35, we first give a high-level overview of the algorithm.

Let $\textstyle | y \rangle = \sum _ { i = 1 } ^ { M } y _ { i } | i \rangle / \big | \big | \vec { y } \big | \big |$ . As in [KP17], our algorithm works by first constructing the state $| b \rangle = \sqrt { W } | y \rangle / \Big \| \sqrt { W } | y \rangle \Big \|$ , and then applying $A ^ { + } = ( \sqrt { W } X ) ^ { + }$ . Given a block-encoding of $A$ , we can use Corollary 31 to obtain the state $A ^ { + } | b \rangle / \big | \big | A ^ { + } | b \rangle \big |$ . However, in general, $| b \rangle$ will not be in the rowspace of $A ^ { + }$ , so $A ^ { + } | b \rangle$ might be much smaller than $\sigma _ { \operatorname* { m i n } } ( A ^ { + } ) = \left. A \right. ^ { - 1 }$ . However, as long as the data is not too far from linear — that is, the fit is not too bad — the overlap of $| b \rangle$ with $\mathsf { r o w } ( A ^ { + } ) = \mathsf { c o l } ( A )$ will be high, and so $\| A ^ { + } | b  \|$ won’t be much smaller than $\left\| A \right\| ^ { - 1 }$ . Before proving the main theorem of this section, we relate the size of $\Pi _ { \mathrm { c o l } ( A ) } | b \rangle$ to the quality of the fit.

Define the weighted sum of squared residuals with respect to weights $W$ by

$$
S S _ { \mathrm { r e s } } ^ { W } = \Big \| ( I - \Pi _ { \mathrm { c o l } ( A ) } ) \sqrt { W } \vec { y } \Big \| ^ { 2 } .
$$

This measures the sum of squared errors — i.e. discrepancies between the observed and predicted data points — weighted by $W$ . To make sense of this value, we can define the normalized weighted sum of squared residuals:

$$
\overline { { S S } } _ { \mathrm { r e s } } ^ { W } = \frac { \left\| ( I - \Pi _ { \mathrm { c o l } ( A ) } ) \sqrt { W } \vec { y } \right\| ^ { 2 } } { \left\| \sqrt { W } \vec { y } \right\| ^ { 2 } } = \frac { \left\| ( I - \Pi _ { \mathrm { c o l } ( A ) } ) | b \rangle \right\| ^ { 2 } } { \left\| | b \rangle \right\| ^ { 2 } } = 1 - \left\| \Pi _ { \mathrm { c o l } ( A ) } | b \rangle \right\| ^ { 2 } .
$$

It’s reasonable to assume that ${ \overline { { S S } } } _ { \mathrm { r e s } } ^ { W }$ is not too small, because otherwise, the data is very poorly fit by a linear function. In particular, if ${ \overline { { S S } } } _ { \ r e s } ^ { W } \geq \eta ,$ then $R ^ { 2 } \leq 1 - \eta ,$ where $R ^ { 2 }$ is the coefficient of determination, commonly used to measure the goodness of the fit.

Proof of Thereom 35: We now prove our main theorem of the section. Let $\delta = o ( \varepsilon / ( { \kappa _ { A } ^ { 2 } \log ^ { 3 } { \frac { \kappa _ { A } } { \varepsilon } } } ) )$ . $\mathsf { B y }$ Lemma 25 we know how to implement a $( \mathcal { O } ( \mu ( A ) ) , \lceil \log ( N + M + 1 ) \rceil , \delta )$ -block-encoding of $\overline { { A } }$ with complexity $\mathcal { O } ( \vert \boldsymbol { \mathrm { p o l y l o g } } ( M N / \delta ) )$ . Since $\sqrt { W } \vec { y }$ is stored in a quantum-accessible data structure, the state $| b \rangle$ can be generated in cost $\mathsf { p o l y l o g } ( M N / \delta )$ . Using these ingredients Corollary 31 implies that we can prepare am $\varepsilon$ -approximation of the quantum state $A ^ { + } | b \rangle / \big | \big | A ^ { + } | b \rangle \big | \big |$ in complexity:

$$
\widetilde { \mathcal { O } } \left( \frac { \kappa _ { A } \mu ( A ) } { \sqrt { 1 - \eta } } \mathsf { p o l y l o g } ( M N / \varepsilon ) \right) .
$$

In applying Corollary 31, we used the fact that

$$
\begin{array} { r } { \left\| \Pi _ { \mathrm { c o l } ( A ) } \big | b \big \rangle \right\| ^ { 2 } = 1 - \overline { { S S } } _ { \mathrm { r e s } } ^ { W } \geq 1 - \eta . } \end{array}
$$

In some applications it might not be natural to assume that we store $A$ in quantum memory. Therefore we also prove a version where $\boldsymbol { X }$ and $W$ are accessed separately, as a special case of the GLS solver we prove in the next subsection.

# 5.1.2 Generalized least squares

In this section, we give a quantum GLS solver when the input is given in the block-encoding framework. Given block-encodings of $\boldsymbol { X }$ and $\Omega$ , it is straightforward to implement a blockencoding of $( X ^ { T } \Omega ^ { - 1 } X ) ^ { - 1 } X ^ { T } \Omega ^ { - 1 }$ using the following: 1) Given a block-encoding of $A _ { i }$ , we can implement a block-encoding of $A ^ { - 1 }$ ; and 2) Given block-encodings of $A$ and $B$ , we can implement a block-encoding of $A B$ . The resulting block-encoding can then be applied to $| y \rangle$ to get a state proportional to $\bar { \vec { \beta } }$ , the desired output. (For a detailed analysis of this approach, see [CGJ18]). While this approach is conceptually quite simple, we can get a simpler algorithm with better complexity by observing that if A = Ω−1/2X , then (X T Ω−1X )−1X T Ω−1 = A+Ω−1/2.

Theorem 36. (Quantum GLS solver using block-encodings) Suppose that we have a unitary $U _ { u }$ preparing a quantum state proportional to y\~ in complexity Ty. Suppose X ∈ RM×N, Ω ∈ RM×M are such that $\left\| X \right\| \leq 1 , \left\| \Omega \right\| \leq 1$ and $\Omega \succ 0$ is positive definite. Suppose that we have access to $U _ { X }$ that is an $( \alpha _ { X } , a _ { X } , 0 )$ -block-encoding of $\boldsymbol { X }$ which has complexity $T _ { X } \geq a _ { X }$ , and similarly we have access $U _ { \Omega }$ that is an $( \alpha _ { \Omega } , a _ { \Omega } , 0 )$ -block-encoding of $\Omega ^ { - \frac { 1 } { 2 } }$ which has complexity $T _ { \Omega } \geq a _ { \Omega }$ . Let $A : = \Omega ^ { - \frac { 1 } { 2 } } X ,$ , and suppose we have the following upper bounds: $\left\| A ^ { + } \right\| \le \kappa _ { A } , \left\| \Omega ^ { - 1 } \right\| \le \kappa _ { \Omega } ,$ and $\overline { { S S } } _ { r e s } ^ { \Omega } \leq \eta$ . Then we can implement a quantum GLS-solver with error $\varepsilon$ in complexity

$$
{ \mathcal O } ( \frac { \kappa _ { A } \log ( \kappa _ { A } ) } { \sqrt { 1 - \eta } } \Big ( \big ( \sqrt { \kappa _ { \Omega } } \alpha _ { X } T _ { X } + \alpha _ { \Omega } T _ { \Omega } \big ) \log ^ { 3 } \Big ( \frac { \kappa _ { A } } { \varepsilon } \Big ) + \sqrt { \kappa _ { \Omega } } T _ { y } ) ) .
$$

Proof. The goal is to implement a unitary preparing a state proportional to

$$
( X ^ { T } \Omega ^ { - 1 } X ) ^ { - 1 } X ^ { T } \Omega ^ { - 1 } | y \rangle = { \Big ( } \Omega ^ { - { \frac { 1 } { 2 } } } X { \Big ) } ^ { + } \Omega ^ { - { \frac { 1 } { 2 } } } | y \rangle .
$$

$\mathsf { B y }$ Lemma 24 we can implement a unitary $U _ { \psi }$ , that prepares a $\delta$ -approximation of

$$
| \psi \rangle : = \frac { \Omega ^ { - \frac { 1 } { 2 } } | \vec { y } \rangle } { \left\| \Omega ^ { - \frac { 1 } { 2 } } \vec { y } \right\| } \mathrm { ~ w i t h ~ } \mathrm { c o m p l e x i t y ~ } T _ { \psi } : = \mathcal { O } \left( \alpha _ { \Omega } T _ { \Omega } \log \left( \frac { 1 } { \delta } \right) + \sqrt { \kappa _ { \Omega } } T _ { y } \right) .
$$

Let $: = a x + a _ { \Omega } + 2 \ /$ , by Lemma 5 we can combine the block-encodings of $\Omega ^ { - \frac { 1 } { 2 } }$ and $\boldsymbol { X }$ to implement a unitary $U _ { A } ,$ that is a $( 2 \sqrt { \kappa _ { \Omega } } , a _ { A } , \delta )$ block-encoding of $A$ in complexity

$$
T _ { A } : = { \mathcal O } \left( \left( \alpha _ { X } ( T _ { X } + a _ { X } ) + \frac { \alpha _ { \Omega } } { \sqrt { \kappa _ { \Omega } } } ( T _ { \Omega } + a _ { \Omega } ) \right) \mathsf { l o g } \left( \frac { \kappa _ { \Omega } } { \delta } \right) \right) .
$$

Finally by choosing $\begin{array} { r } { \delta = o \left( \varepsilon \kappa _ { A } ^ { - 2 } \log ^ { - 3 } ( \frac { \kappa _ { A } } { \varepsilon } ) \right) } \end{array}$ and defining $\alpha _ { A } : = \sqrt { \kappa _ { \Omega } } ,$ using Corollary 31 we get that a quantum state proportional to $A ^ { + } | \psi \rangle$ can be prepared with $\varepsilon$ -precision in complexity

$$
\begin{array} { r l } & { \quad \mathcal { O } \left( \Big ( \alpha _ { A } \kappa _ { A } ( a _ { A } + T _ { A } ) \log ^ { 2 } \left( \frac { \kappa _ { A } } { \varepsilon } \right) + \kappa _ { A } T _ { \psi } \Big ) \frac { \log ( \kappa _ { A } ) } { \sqrt { \gamma } } \right) } \\ & { = \mathcal { O } \left( \frac { \kappa _ { A } \log \left( \kappa _ { A } \right) } { \sqrt { 1 - \eta } } \left( \sqrt { \kappa _ { \Omega } } T _ { A } \log ^ { 2 } \left( \frac { \kappa _ { A } } { \varepsilon } \right) + T _ { \psi } \right) \right) } \\ & { = \mathcal { O } \left( \frac { \kappa _ { A } \log \left( \kappa _ { A } \right) } { \sqrt { 1 - \eta } } \left( \left( \sqrt { \kappa _ { \Omega } } \alpha _ { X } T _ { X } + \alpha _ { \Omega } T _ { \Omega } \right) \log ^ { 3 } \left( \frac { \kappa _ { A } } { \varepsilon } \right) + \sqrt { \kappa _ { \Omega } } T _ { y } \right) \right) . } \end{array}
$$

Note that the above theorem requests 0-error block-encoding inputs, however if the algorithm uses $T$ queries to the block-encodings, the error blows up only linearly in $T$ , so if we allow a $\delta = c \varepsilon ^ { 2 } / T$ initial error (for some small enough $c \in \mathbb { R } _ { + }$ constant) in the block-encodings, then we do not make more than $\varepsilon / 2$ overall error.23

Corollary 37 (Quantum WLS solver using data structure or sparse oracles – alternate input). Let W be a diagonal matrix such that $1 ~ \le ~ w _ { i } ~ \le ~ w _ { \mathfrak { m a x } }$ for each $i ,$ moreover $\| X \| \leq 1$ . Let $A = { \sqrt { W } } X$ and suppose that $\left\| A ^ { + } \right\| \le \kappa _ { A }$ . Suppose $\vec { y }$ is stored in $a$ quantum data structure, and the diagonal entries of $W$ are stored in QROM so that we can compute $| i \rangle \mapsto | i \rangle | w _ { i } \rangle$ in polylog $( M N / \varepsilon )$ , as well as $W _ { \mathrm { { I n a x } } }$ . Further, suppose either (1) $\boldsymbol { X }$ is stored in a quantumaccessible data structure, in which case, let $\mu ( X ) \ : = \ : \| X \| _ { F } ;$ or $( 2 )$ for some $p \in [ 0 , 1 ] .$ , $\chi ( p )$ and $\chi ( 1 - p )$ are stored in quantum-accessible data structures, in which case, let $\mu ( X ) = \mu _ { p } ( X )$ . Finally, suppose the data points satisfy $\overline { { S S } } _ { \ r { r e s } } ^ { W } \leq \eta$ . Then we can implement a quantum WLS solver with error $\varepsilon$ in complexity:

$$
\widetilde { \mathcal { O } } \left( \frac { \kappa _ { A } \sqrt { w _ { \mathrm { m a x } } } } { \sqrt { 1 - \eta } } \mu ( X ) \mathrm { p o l y l o g } ( M N / \varepsilon ) \right) .
$$

Similarly, if we are given sparse access to $\boldsymbol { X }$ which has row and column sparsity at most $s _ { X } ^ { r }$ and $s _ { X } ^ { c }$ respectively, and a unitary $U _ { y }$ preparing $| y \rangle$ in complexity $T _ { y } ,$ then we can implement a quantum WLS solver with error $\varepsilon$ in complexity:

$$
\widetilde { \mathcal { O } } \left( \frac { \kappa _ { A } \sqrt { w _ { \mathrm { m a x } } } } { \sqrt { 1 - \eta } } \left( \sqrt { s _ { X } ^ { r } s _ { X } ^ { c } } + T _ { y } \right) \mathrm { p o l y l o g } ( M N / \varepsilon ) \right) .
$$

Corollary 38 (Quantum GLS solver using block-encodings – alternate input). Suppose that $X , \ \Omega ,$ and $\vec { y }$ are as in Theorem ${ 3 6 } ,$ except we have access to $U _ { \Omega }$ that is an $( \alpha _ { \Omega } , a _ { \Omega } , 0 )$ -blockencoding of $\Omega$ which has complexity $T _ { \Omega } \geq a _ { \Omega }$ . Then we can implement a quantum GLS-solver with error $\varepsilon$ in complexity

$$
\widetilde { \mathcal { O } } \left( \frac { \kappa _ { A } \sqrt { \kappa _ { \Omega } } } { \sqrt { 1 - \eta } } \big ( \alpha _ { X } T _ { X } + \alpha _ { \Omega } \kappa _ { \Omega } T _ { \Omega } + T _ { y } \big ) \mathrm { p o l y l o g } \left( \frac { 1 } { \varepsilon } \right) \right) .
$$

Proof. ${ \mathsf { B y } }$ Lemma 9 we can implement a unitary $U _ { \Omega } ^ { \prime }$ that is a $\begin{array} { r } { ( 2 \sqrt { \kappa _ { \Omega } } , a _ { \Omega } + \mathcal { O } \left( \log \left( \kappa _ { \Omega } \log \frac { 1 } { \delta } \right) , \delta / 4 \right) } \end{array}$ block-encoding of $\Omega ^ { - \frac { 1 } { 2 } }$ in complexity $\begin{array} { r } { \mathcal { O } \Big ( \alpha _ { \Omega } \kappa _ { \Omega } ( a _ { \Omega } + T _ { \Omega } ) \log ^ { 2 } \left( \frac { \kappa _ { \Omega } } { \delta } \right) \Big ) } \end{array}$ . Choosing $\begin{array} { r } { \delta = o \big ( \mathrm { p o l y } \big ( \frac { \kappa _ { A } } { \varepsilon } \big ) \big ) } \end{array}$ the result follows from Theorem 36. □

Corollary 39 (Quantum GLS using quantum data structure or sparse oracles). Suppose X, Ω, and $\vec { y }$ are as in Corollary 38, and we are given access to $\boldsymbol { X }$ as in Corollary 37, and similarly to $\Omega$ . Then in case of the database input model we can implement a quantum GLS-solver with error $\varepsilon$ in complexity

$$
\widetilde { \mathcal { O } } \left( \frac { \kappa _ { A } \sqrt { \kappa _ { \Omega } } } { \sqrt { 1 - \eta } } ( \mu \chi + \mu _ { \Omega } \kappa _ { \Omega } ) \mathrm { p o l y l o g } ( M N / \varepsilon ) \right) .
$$

Similarly, in case of the sparse-access input model we can implement a quantum GLS-solver with error $\varepsilon$ in complexity

$$
\widetilde { \mathcal { O } } \left( \frac { \kappa _ { A } \sqrt { \kappa _ { \Omega } } } { \sqrt { 1 - \eta } } \left( \sqrt { s _ { X } ^ { r } s _ { X } ^ { c } } + s _ { \Omega } \kappa _ { \Omega } \right) \mathsf { p o l y l o g } ( M N / \varepsilon ) \right) .
$$

# 5.2 Estimating electrical network quantities

Analysis of electrical networks finds widespread applications in a plethora of graph-based algorithms. For algorithms such as graph sparsification [SS11], computing maximum-flows $[ \mathrm { C K M ^ { + } } 1 1 ]$ , LRS13] and for analyzing several classical random walk-based problems [DS84], it turns out to be useful to treat the underlying graph as an electrical network.

In Ref. [Wan17a], Wang presents two quantum algorithms for estimating certain quantities in large sparse electrical networks in the sparse-access input model: one is based on using a quantum linear systems algorithm for sparse matrices [CKS17] to invert the weighted signed incidence matrix, defined shortly, while the other is based on quantum walks. The estimated quantities include, among others, the power dissipated across a network, of which the effective resistance between two nodes is a special case. Wang uses the fact that these quantities can be obtained by estimating the norm of the output of a certain QLS problem.

In this section, we give a quantum algorithm for estimating the dissipated power similar to Wang’s linear-system-based algorithm, but in the block-encoding input model, replacing the QLS solver of [CKS17], which Wang uses, by our QLS solver for block-encodings. In particular, rather than standard amplitude estimation, we make use of our new variable-time amplitude estimation (Corollary 32). An immediate corollary of this is an algorithm in the sparse-access input model, which outperforms Wang’s linear-system-based algorithm for all electrical networks, and in some parameter regimes, also improves on his quantum-walkbased algorithm for this problem. Additionally, our block-encoding algorithm implies the first algorithm for this problem in the quantum data structure input model. Our algorithms also apply to estimating the effective resistance, as a special case.

It is worth noting that we can also obtain a speedup over the remaining algorithms introduced by Wang in [Wan17a] that are based on only solving linear systems such as calculating the current across an edge and approximating voltage across two nodes. However, we do not include this analysis here.

We begin by defining an electrical network and related quantities that shall be used subsequently.

Problem setting and definitions. An electrical network is a weighted connected graph with the weight of each edge being the inverse of the resistance — i.e., the conductance — of the edge. Let $G ( V , E , w )$ denote a connected graph with vertices $V$ , edges $E$ , and edge weights $w$ . Let $N = | V |$ and $M = | E |$ . We assume that the weight of each edge $W _ { e }$ is such that $1 \leq w _ { e } \leq w _ { \mathrm { m a x } }$ . The degree of $V$ is the number of vertices adjacent to $V _ { \ast }$ , and is denoted by $d ( v )$ . The maximum degree of $G$ is denoted $d = \mathfrak { m a x } _ { v \in V } d ( v )$ . As the network may be non-sparse, $d$ can scale with the size of the network. The complexity of our quantum algorithms depend on the size of the network $N$ , the maximum degree $d$ , the spectral gap of the normalized Laplacian representing the network $\lambda$ (defined shortly), the precision parameter $\epsilon$ , and the maximum edge weight $W _ { \mathrm { { m a x } } }$ .

Let $B _ { G } ~ \in \ \mathbb { R } ^ { N \times M }$ be the signed vertex-edge incidence matrix, defined so that for each $e \in [ M ] ,$ , the $e$ -th column has a single 1 and a single $- 1$ , in the rows corresponding to the two vertices incident to edge $e$ , and 0s elsewhere; and let $W _ { G } \in \mathbb { R } ^ { M \times M }$ be a diagonal matrix where the $e$ -th diagonal entry represents the weight $w _ { e }$ of edge $e$ . The weighted signed vertex-edge incidence matrix is then $C _ { G } = B _ { G } \sqrt { W _ { G } }$ and the graph Laplacian is $L _ { G } = C _ { G } C _ { G } ^ { T } = B _ { G } W _ { G } B _ { G } ^ { T }$ .

$L _ { G }$ is a positive semidefinite matrix with its minimum eigenvalue being 0 and the corresponding eigenvector being the uniform vector [Bol13]. We denote the eigenvalues of $L _ { G }$ as

$$
\lambda _ { 1 } ( L _ { G } ) = 0 < \lambda _ { 2 } ( L _ { G } ) \leq . . . . \lambda _ { N } ( L _ { G } ) \leq 2 w _ { \sf m a x } d .
$$

The weighted degree of a vertex is the sum of the weights of the edges incident to it, i.e. $\begin{array} { r } { \overline { { d } } _ { v } = \sum _ { e : v \in e } w _ { e } } \end{array}$ . Define the diagonal weighted degree matrix $\begin{array} { r } { D _ { G } = \sum _ { v \in V } \overline { d } _ { v } | v \rangle \langle v | } \end{array}$ . Then one can also define the normalized Laplacian of $G$ as $\mathcal { L } _ { G } = D _ { G } ^ { - 1 / 2 } L _ { G } D _ { G } ^ { - 1 / 2 }$ . The spectrum of the normalized Laplacian is denoted

$$
\lambda _ { 1 } ( \mathcal { L } _ { G } ) = 0 < \lambda _ { 2 } ( \mathcal { L } _ { G } ) \le . . . . \lambda _ { N } ( \mathcal { L } _ { G } ) \le 2 .
$$

It is easy to show that since $\overline { { d } } _ { v } \geq 1 , \forall v \in V , \lambda _ { 2 } ( \mathcal { L } _ { G } ) \leq \lambda _ { 2 } ( L _ { G } ) .$

We now give a mathematical definition of the dissipated power of an external current applied to a network.

Definition 40 (Dissipated power). Given a weighted graph $G ( V , E , w )$ , and $a$ current $\vec { i } \in \mathbb R ^ { M }$ the dissipated power of $\vec { i }$ is given by $\begin{array} { r } { \mathcal E ( \vec { i } ) = \sum _ { e \in E } \frac { \vec { i } ( e ) ^ { 2 } } { w _ { e } } = \left. W _ { G } ^ { - 1 / 2 } \vec { i } \right. ^ { 2 } } \end{array}$ .

An external current $\vec { i } _ { e x t } \in \mathbb { R } ^ { N }$ is a real-valued function on $V$ that sums to $\it { 0 . }$ . A positive value $\vec { i } _ { e x t } ( \nu )$ represents current entering the network at $V ,$ , and a negative value $\vec { i } _ { e x t } ( \nu )$ represents current leaving the network at $V$ . An external current $\vec { i } _ { e x t }$ on $G$ induces $a$ potential (voltage) $\vec { v } \in \mathbb R ^ { N }$ on the vertices of $G _ { \ * }$ , given by $\vec { v } = L _ { G } ^ { + } \vec { i } _ { e x t }$ . This voltage has a corresponding induced current defined via Ohm’s Law as ${ \vec { i } } = W _ { G } B _ { G } ^ { T } { \vec { v } }$ . The dissipated power of $\vec { i } _ { e x t }$ is defined as $\mathcal { E } ( \vec { i } )$ .

A well-known special case of the dissipated power is the effective resistance between $s$ and $t$ for $s , t \in V$ , which is the power dissipated by the current induced by injecting a unit of current into $s$ , and removing it at $t$ .

Definition 41 (Effective resistance). Given a weighted graph $G ( V , E , w )$ and a pair of vertices $s , t \in V ,$ , the effective resistance between $S$ and $t$ is just the dissipated power of the external current $\vec { i } _ { e x t } = | s \rangle - | t \rangle$ .

Since the effective resistance is a special case of the dissipated power, algorithms for estimating the dissipated power can be applied to estimate the effective resistance between two nodes.

Algorithms for estimating dissipated power. From [Wan17a, Lemma 6], we have:

Lemma 42. Let $C _ { G } \in \mathbb { R } ^ { N \times M }$ be the weighted signed vertex-edge incidence matrix of an electrical network $G ( V , E , w )$ . Then given an external current $\vec { i } _ { e x t } \in \mathbb { R } ^ { N }$ on $G _ { \ * }$ , if $\vec { i }$ denotes the induced current, we have

$$
\left[ \begin{array} { c c c } { { 0 } } & { { } } & { { C _ { G } } } \\ { { C _ { G } ^ { T } } } & { { } } & { { 0 } } \end{array} \right] ^ { + } \left( \begin{array} { c c c } { { \vec { i } _ { e x t } } } \\ { { 0 } } \end{array} \right) = \left( \begin{array} { c c c } { { 0 } } \\ { { W _ { G } ^ { - 1 / 2 } \vec { i } } } \end{array} \right) .
$$

Thus, to estimate the dissipated power of an external current $\vec { i } _ { e x t }$ , it suffices to estimate $\left\| \overline { { C } } _ { G } ^ { + } | 0 \rangle \vec { i } _ { e x t } \right\| ^ { 2 } = \left\| W _ { G } ^ { - 1 / 2 } \vec { i } \right\| ^ { 2 }$ . This gives the following:

Theorem 43 (Estimating dissipated power). Fix $\epsilon \in ( 0 , 1 )$ , $w _ { \sf m a x } \geq 1 , \lambda > 0$ , and $d \geq 1$ . Fix any $\delta$ in $O \left( \frac { \epsilon \lambda } { d w _ { \mathrm { { m a x } } } \log ^ { 2 } \frac { d w _ { \mathrm { { m a x } } } } { \epsilon \lambda } } \right)$ For $a$ weighted network $G ( V , E , w )$ , with $| V | = N ,$ , $| E | = M ,$ maximum degree $d$ , $1 \leq w _ { e } \leq w _ { \sf m a x }$ for all $e \in E .$ , and $\lambda _ { 2 } ( { \mathcal { L } } _ { G } ) \geq \lambda ,$ and an external current $\vec { i } _ { e x t } \in \mathbb { R } ^ { N } ,$ , suppose we are given the value $\left\| \vec { i } _ { e x t } \right\| = \mathsf { p o l y } ( N ) ,$ a unitary $U _ { \vec { i } _ { e x t } }$ preparing $a$ quantum state proportional to $\vec { i } _ { e x t }$ in complexity $T _ { \vec { i } _ { e x t } } ,$ and an $( \alpha , a , \delta )$ -block-encoding of $C _ { G }$ that can be implemented in complexity $T _ { C _ { G } }$ . Then the dissipated power of $\vec { i } _ { e x t }$ can be estimated to multiplicative accuracy $\epsilon$ with success probability at least $\frac { 2 } { 3 }$ in complexity

$$
\mathcal { O } \left( \frac { 1 } { \epsilon } \sqrt { \frac { d w _ { \mathrm { m a x } } } { \lambda } } \left( \alpha \big ( T _ { C _ { G } } + a \big ) \log ^ { 2 } \frac { d w _ { \mathrm { m a x } } } { \lambda \epsilon } + T _ { \vec { i } _ { e x t } } \right) \log ^ { 4 } \frac { d w _ { \mathrm { m a x } } } { \lambda } \right) .
$$

In particular, if $\hat { \dot { \iota } } _ { e x t } = \vert s \rangle - \vert t \rangle ,$ then we can estimate the effective resistance between s and t in the given complexity, even without assuming an input oracle for state preparation.

Proof. By Lemma 42 it suffices to compute $\left\| C _ { G } ^ { + } \vec { i } _ { e x t } \right\| ^ { 2 }$ . We will actually estimate $\left\| C _ { G } ^ { + } \vec { i } _ { e x t } \right\|$ to $\epsilon / 3$ -multiplicative accuracy, yielding an $\epsilon$ -multiplicative estimate of $\left\| C _ { G } ^ { + } \vec { i } _ { e x t } \right\| ^ { 2 }$ .

We first note that for any external current ${ \vec { i } } _ { e x t } , { \vec { i } } _ { e x t } \in { \mathrm { c o l } } ( C _ { G } )$ . This is because the entries of $\vec { i } _ { e x t }$ must sum to 0, meaning it is orthogonal to the uniform vector. Since $\lambda _ { 2 } ( L _ { G } ) \geq \lambda _ { 2 } ( \mathcal { L } _ { G } ) > 0$ , the uniform vector is the unique 0-eigenvector of $L _ { G }$ , so $\vec { i } _ { e x t } \in \mathsf { c o l } ( L _ { G } ) = \mathsf { c o l } ( C _ { G } ) ,$ since $L _ { G } =$ $C _ { G } C _ { G } ^ { T }$ .

$\mathsf { B y }$ (24), the condition number of $L _ { G }$ is at most $2 d w _ { \mathrm { m a x } } / \lambda _ { 2 } ( L _ { G } ) \leq 2 d w _ { \mathrm { m a x } } / \lambda _ { 2 } ( \mathcal { L } _ { G } ) \leq 2 d w _ { \mathrm { m a x } } / \lambda _ { \iota }$ , and since $L _ { G } = C _ { G } C _ { G } ^ { T }$ , the condition number of $C _ { G }$ is at most $\kappa = \sqrt { 2 d w _ { \sf m a x } / \lambda }$ . Thus, the eigenvalues of $C _ { G } / \| C _ { G } \|$ lie in $[ 1 / \kappa , 1 ]$ , and we have an $\lfloor \alpha / \left. C _ { G } \right. , a , 0 )$ -block-encoding of $C _ { G } / \| C _ { G } \|$ , so by Corollary 32, we can estimate $\left\| C _ { G } ^ { + } \vec { i } _ { e x t } \right\| / \left\| \vec { i } _ { e x t } \right\|$ to multiplicative accuracy $\epsilon / 3$ in complexity

$$
\mathcal { O } \left( \frac { \kappa } { \epsilon } \left( \frac { \alpha } { \left. C _ { G } \right. } \big ( T _ { C _ { G } } + a \big ) \log ^ { 2 } \frac { \kappa } { \epsilon } + T _ { \vec { i } _ { e x t } } \right) \log ^ { 4 } \kappa \right) .
$$

Observe that for any $e \in E , \sqrt { 2 } \leq \left. C _ { G } | e \rangle \right. \leq \left. C _ { G } \right.$ ; also $\kappa \leq \sqrt { \frac { d w _ { \mathrm { m a x } } } { \lambda } }$ concluding the proof.

In Ref. [Wan17a], Wang considers estimating the dissipated power in an input model that assumes a constant-complexity procedure for generating a state proportional to ${ \dot { \vec { i } } _ { e x t } } ,$ and allows sparse access to $C _ { G }$ , whose sparsity is $d$ , in constant complexity. Since sparse access can be used to implement a $( d , \mathsf { p o l y l o g } ( M N / \delta ) , \delta )$ -block-encoding of $C _ { G }$ in complexity polylog $( M N / \delta )$ , we have the following corollary.

Corollary 44 (Estimating dissipated power in the sparse-access model). Fix parameters as in Theorem 43, and assume sparse access to $C _ { G } ,$ , access to the value $\left\| \vec { i } _ { e x t } \right\| ,$ and query access to a subroutine that generates a state proportional to $\vec { i } _ { e x t }$ . Then there is a quantum algorithm that estimates the dissipated power of $\vec { i } _ { e x t }$ to multiplicative accuracy $\epsilon$ with bounded error in query and gate complexity

$$
\widetilde { \mathcal { O } } \left( \frac { d ^ { 3 / 2 } } { \epsilon } \sqrt { \frac { w _ { \mathrm { m a x } } } { \lambda } } \mathrm { p o l y l o g } ( N ) \right) .
$$

In particular, if ${ \vec { i } } _ { e x t } = | s \rangle - | t \rangle ,$ then we can estimate the effective resistance between s and t in the given complexity, even without assuming an input oracle for state preparation.

Our algorithm in the sparse-access input model compares favourably with Wang’s algorithm that is also based on inverting $C _ { G } ,$ which has complexity $\widetilde { \mathcal { O } } \left( \frac { w _ { \mathrm { m a x } } d ^ { 2 } } { \lambda \epsilon } \mathrm { p o l y l o g } ( N ) \right)$ . However, Wang presents a second algorithm for estimating the dissipated power that uses quantumwalk-based techniques. Our result also improves on this second algorithm in some parameter regimes. We discuss this further at the end of this section.

Our block-encoding result can also be applied to the case when the input is given as a quantum data structure, in which case, the value $\left\| \vec { i } _ { e x t } \right\|$ can be easily read off the root of the tree that stores the entries of $\vec { i } _ { e x t }$ in a quantum data structure:

Corollary 45 (Estimating dissipated power in quantum data structure model). $F i x$ parameters as in Theorem 43, and assume $\vec { i } _ { e x t }$ is stored in a quantum data structure and either (1) $C _ { G }$ is stored in a quantum data structure, in which case, let are stored in quantum data structures, in which case, $\mu ( C _ { G } ) = \left. C _ { G } \right. _ { F } ,$ (2) . $C _ { G } ^ { ( { p } ) }$ and  ther $C _ { G } ^ { ( 1 - p ) }$ $\mu ( C _ { G } ) = \mu _ { p } ( C _ { G } )$ $a$ quantum algorithm that estimates the dissipated power of $\vec { i } _ { e x t }$ to multiplicative accuracy $\epsilon$ with bounded error in complexity

$$
\widetilde { \mathcal { O } } \left( \frac { \mu ( C _ { G } ) } { \epsilon } \sqrt { \frac { d w _ { \mathrm { m a x } } } { \lambda } } \mathrm { p o l y l o g } ( N ) \right) .
$$

In particular, if $\begin{array} { r } { \boldsymbol { \mathscr { r } } \vec { i } _ { e x t } = | s \rangle - | t \rangle , } \end{array}$ then we can estimate the effective resistance between s and t in the given complexity, even without assuming an input oracle for state preparation.

In the quantum data structure model, it may be more natural to assume that the weights $W _ { G }$ and the incidence matrix $B _ { G }$ are stored separately. In that case, we get the following.

Corollary 46 (Estimating dissipated power in quantum data structure model, alternative input). Fix parameters as in Theorem 43, and assume $\vec { i } _ { e x t }$ is stored in a quantum data structure, w is stored in QROM so that we can compute $| e \rangle \mapsto | e \rangle | w _ { e } \rangle$ in polylog $( M )$ complexity, and either (1) $B _ { G }$ is stored in a quantum data structure, in which case, let $\mu ( B _ { G } ) = \left\| B _ { G } \right\| _ { F } ,$ ; or (2) $B _ { G } ^ { ( p ) }$ and $B _ { G } ^ { ( 1 - p ) }$ are stored in quantum data structures, in which case, let $\mu ( B _ { G } ) = \mu _ { p } ( B _ { G } )$ . Then there is a quantum algorithm that estimates the dissipated power of $\vec { i } _ { e x t }$ to multiplicative accuracy $\epsilon$ with bounded error in complexity

$$
\widetilde { \mathcal { O } } \left( \frac { \mu ( B _ { G } ) w _ { \mathrm { m a x } } } { \epsilon } \sqrt { \frac { d } { \lambda } } \mathrm { p o l y l o g } ( N ) \right) .
$$

In particular, $i f { \vec { i } } _ { e x t } = | s \rangle - | t \rangle ,$ then we can estimate the effective resistance between s and t in the given complexity, even without assuming an input oracle for state preparation.

Proof. Similar to the proof of Lemma 25, we can implement a $( \sqrt { w _ { \mathrm { m a x } } } \mu ( B _ { G } ) , \mathsf { p o l y l o g } ( N ) , \delta ) \ –$ block-encoding of $C _ { G } = B _ { G } \sqrt { W _ { G } }$ in complexity polylog $( N / \delta )$ . Then the result follows from Theorem 43. □

We note that due to the specific structure of $B _ { G } , ~ \mu ( B _ { G } )$ can likely be bounded in some cases, but we leave this for future work.

Comparison with previous work. In the sparse-access model (Corollary 44) our complexity is

$$
\widetilde { \mathcal { O } } \left( \frac { d ^ { 3 / 2 } } { \epsilon } \sqrt { \frac { w _ { \mathrm { m a x } } } { \lambda } } \mathrm { p o l y l o g } ( N ) \right) .
$$

This improves upon Wang’s QLS based algorithm for estimating the dissipated power, which has complexity

$$
\widetilde { \mathcal { O } } \left( \frac { w _ { \mathrm { m a x } } d ^ { 2 } } { \lambda \epsilon } \mathsf { p o l y l o g } ( N ) \right) .
$$

Wang also gives an alternative algorithm for estimating the dissipated power based on quantum walks, which has complexity:

$$
\widetilde { \mathcal { O } } \left( \frac { \sqrt { d w _ { \mathrm { m a x } } } } { \lambda \epsilon } \operatorname* { m i n } \left\{ d , \sqrt { \frac { w _ { \mathrm { m a x } } } { \lambda } } \right\} \mathrm { p o l y l o g } ( N ) \right) .
$$

We also compare this complexity with our algorithm’s complexity (25) by case separation:

(i) When $d < \sqrt { w _ { \mathrm { m a x } } / \lambda }$ , the complexity of Wang’s algorithm (27) is $\mathcal { \tilde { O } } \big ( \sqrt { w _ { \mathrm { m a x } } } d ^ { 3 / 2 } \epsilon ^ { - 1 } \lambda ^ { - 1 } \big )$ . Our complexity (25) is better by a factor of $\widetilde { \mathcal { O } } \left( 1 / { \sqrt { \lambda } } \right)$ .

(ii) When $d > \sqrt { w _ { \sf m a x } / \lambda } ,$ the complexity of Wang’s algorithm (27) is $\widetilde { \mathcal { O } } \left( w _ { \mathrm { m a x } } \sqrt { d } \lambda ^ { - 3 / 2 } \epsilon ^ { - 1 } \right)$ . Our complexity (25) has a worse dependence on $d$ , but a better dependence on $W _ { \mathrm { { m a x } } }$ and λ. We get a speedup as long as $\sqrt { w _ { \mathrm { m a x } } / \lambda } < d \ll \sqrt { w _ { \mathrm { m a x } } } / \lambda ,$ e.g., if $d = \mathcal { O } ( \mathsf { p o l y l o g } ( N ) )$ , we get a speedup of $\mathcal { \tilde { O } } ( \sqrt { w _ { \mathrm { m a x } } } / \lambda )$ .

We now consider our algorithm in the quantum data structure access model (Corollary 45) and compare it to Wang’s algorithms. Note that as Wang’s algorithms are in the sparse-access input model, these are not directly comparable. Assume that we are in Case (1), in which case   √ $\mu ( C _ { G } ) = \left\| C _ { G } \right\| _ { F } \leq \left\| C _ { G } \right\| \sqrt { N }$ . The complexity of our algorithm in this model is

$$
\mathcal { \widetilde { O } } \left( \frac { 1 } { \epsilon } \sqrt { \frac { d N w _ { \mathrm { m a x } } } { \lambda } } \mathrm { p o l y l o g } ( N ) \right) .
$$

As compared to Wang’s algorithm based on linear systems (26), our complexity (28) is better for graphs with maximum degree $d \gg \sqrt [ 3 ] { N \lambda / W _ { \operatorname* { m a x } } }$ . With respect to Wang’s quantum walk-based algorithm (27) our complexity (28) is better only in certain regimes.

(i) When $d < \sqrt { w _ { \mathrm { m a x } } / \lambda } ,$ the complexity of Wang’s algorithm (27) is $\mathcal { \tilde { O } } \big ( \sqrt { w _ { \mathrm { m a x } } } d ^ { 3 / 2 } \epsilon ^ { - 1 } \lambda ^ { - 1 } \big )$ . Our complexity (28) is better as long as $\lambda \ll d ^ { 2 } / N$ .   
(ii) When $d > \sqrt { w _ { \sf m a x } / \lambda }$ , the complexity of Wang’s algorithm (27) is $\widetilde { \mathcal { O } } \left( w _ { \mathrm { m a x } } \sqrt { d } \lambda ^ { - 3 / 2 } \epsilon ^ { - 1 } \right)$ . Our complexity (28) is better as long as $\lambda \ll \sqrt { w _ { \mathrm { m a x } } / N }$ .

In Ref. [IJ16], the authors developed a quantum algorithm for estimating effective resistance between $S$ and t, $R _ { s , t }$ , in the adjacency query model. Moreover, the weights of each edge are assumed to be in $\{ 0 , 1 \}$ . The algorithm estimates $R _ { s , t }$ up to a multiplicative error $\epsilon$ in complexity

$$
\widetilde { \mathcal { O } } \left( \frac { N \sqrt { R _ { s , t } } } { \epsilon } \operatorname* { m i n } \left\{ \frac { 1 } { \sqrt { \epsilon } } , \frac { 1 } { \sqrt { d \lambda } } \right\} \right) .
$$

Although our models are not directly comparable to that of [IJ16], the complexity (28) in the quantum data structure input model is better whenever $\lambda = \Omega ( 1 )$ and $R _ { s , t } \gg d ^ { 2 } w _ { \mathrm { m a x } } / N$ .

# Acknowledgments

The authors are grateful for Iordanis Kerendis, Anupam Prakash and Michael Walter for useful discussions. This work was initiated when SC was a member of the Physics of Information and Quantum Technologies group at IT Lisbon and was visiting QuSoft, CWI Amsterdam. SC was then supported by DP-PMI and FCT (Portugal) through scholarship SFRH/BD/52246/2013 and by FCT (Portugal) through programmes PTDC/POPH/POCH and projects UID/EEA/50008/2013, IT/QuNet, ProQuNet, partially funded by EU FEDER, and from the JTF project NQuN (ID 60478). SC is supported by the Belgian Fonds de la Recherche Scientifique - FNRS under grants no F.4515.16 (QUICTIME) and R.50.05.18.F (QuantAlgo). AG is supported by ERC Consolidator Grant QPROGRESS. SJ is supported by an NWO WISE Grant and NWO Veni Innovational Research Grant under project number 639.021.752.

# References

[AA03] Scott Aaronson and Andris Ambainis. Quantum search of spatial regions. In FOCS, pages 200–209, 2003, arXiv: quant-ph/0303041.   
[AGGW17] Joran van Apeldoorn, András Gilyén, Sander Gribling, and Ronald de Wolf. Quantum SDP-solvers: Better upper and lower bounds. In FOCS, pages 403–414, 2017, arXiv: 1705.01843.   
$[ \mathsf { A C } | \mathsf { O } ^ { + } 1 5 ]$ Srinivasan Arunachalam, Vlad Gheorghiu, Tomas Jochym-O’Connor, Michele Mosca, and Priyaa Varshinee Srinivasan. On the robustness of bucket brigade quantum ram. New Journal of Physics, 17(12):123010, 2015, arXiv: 1502.03450.   
[Amb12] Andris Ambainis. Variable time amplitude amplification and quantum algorithms for linear algebra problems. In Symposium on Theoretical Aspects of Computer Science STACS, pages 636–647, 2012, arXiv: 1010.4458.   
[ATS03] Dorit Aharonov and Amnon Ta-Schma. Adiabatic quantum state generation and statistical zero-knowledge. In Proceedings of the 35th Annual ACM Symposium on Theory of Computing (STOC 2003), pages 20–29, 2003, arXiv: quant-ph/0301023.   
[BACS07] Dominic W. Berry, Graeme Ahokas, Richard Cleve, and Barry C. Sanders. Efficient quantum algorithms for simulating sparse hamiltonians. Communications in Mathematical Physics, 270(2):359–371, 2007, arXiv: quant-ph/0508139.   
$[ { \mathsf { B B K } } ^ { + } 1 6 ]$ Ryan Babbush, Dominic W Berry, Ian D Kivlichan, Annie Y Wei, Peter J Love, and Alán Aspuru-Guzik. Exponentially more precise quantum simulation of fermions in second quantization. New Journal of Physics, 18(3):033032, 2016, arXiv: 1506.01020.   
[BC12] Dominic W. Berry and Andrew M. Childs. Black-box hamiltonian simulation and unitary implementation. Quantum Information and Computation, 12(1–2):29–62, 2012, arXiv: 0910.4157.   
$[ 1 3 { \mathrm { C C } } ^ { + } 1 4 ]$ D. W. Berry, A. M. Childs, R. Cleve, R. Kothari, and R. D. Somma. Exponential improvement in precision for simulating sparse hamiltonians. In Symposium on Theory of Computing, STOC 2014, pages 283–292, 2014, arXiv: 1312.1414.

$[ 1 3 \mathrm { C C ^ { + } } 1 5 ]$ Dominic W. Berry, Andrew M. Childs, Richard Cleve, Robin Kothari, and Rolando D. Somma. Simulating hamiltonian dynamics with a truncated taylor series. Phys. Rev. Lett., 114:090502, 2015, arXiv: 1412.4687.

$[ | 3 \mathrm { C } | ^ { + } 1 3 ]$ Aleksandrs Belovs, Andrew M Childs, Stacey Jeffery, Robin Kothari, and Frédéric Magniez. Time-efficient quantum walks for 3-distinctness. In International Colloquium on Automata, Languages, and Programming, pages 105–122. Springer, 2013, arXiv: 1302.7316.

[BCK15] Dominic W. Berry, Andrew M. Childs, and Robin Kothari. Hamiltonian simulation with nearly optimal dependence on all parameters. In FOCS, pages 792–809, 2015, arXiv: 1501.01715.

el97] R. Bellman. Introduction to Matrix Analysis. Society for Industrial and Applied Mathematics, second edition, 1997.

13] Aleksandrs Belovs. Quantum walks and electric networks. 2013, arXiv: 1302.3143.

Dominic W. Berry and Leonardo Novo. Corrected quantum walk for optimal hamiltonian simulation. Quantum Information and Computation, 16(15–16):1295–1317, 2016, arXiv: 1606.03443.

[Bol13] Béla Bollobás. Modern graph theory. Springer Science & Business Media, 2013.

[CEMM98] Richard Cleve, Artur Ekert, Chiara Macchiavello, and Michele Mosca. Quantum algorithms revisited. Proceedings of the Royal Society A: Mathematical, Physical and Engineering Sciences, 454(1969):339–354, 1998, arXiv: quant-ph/9708016.

[CGJ18] Shantanav Chakraborty, András Gilyén, and Stacey Jeffery. The power of blockencoded matrix powers: improved regression techniques via faster hamiltonian simulation, 2018. arXiv:1804.01973v1.

Chi04] Andrew M. Childs. Quantum information processing in continuous time. PhD thesis, Massachusetts Institute of Technology, 2004.

Andrew M. Childs. On the relationship between continuous- and discrete-time quantum walk. Communications in Mathematical Physics, 294(2):581–603, 2010, arXiv: 0810.0312.

$\left[ \mathsf { C K M } ^ { + } \thinspace 1 \thinspace 1 \right]$ Paul Christiano, Jonathan A Kelner, Aleksander Madry, Daniel A Spielman, and Shang-Hua Teng. Electrical flows, laplacian systems, and faster approximation of maximum flow in undirected graphs. In Proceedings of the forty-third annual ACM symposium on Theory of computing, pages 273–282. ACM, 2011, arXiv: 1010.2921.

[CKS17] Andrew M. Childs, Robin Kothari, and Rolando D. Somma. Quantum algorithm for systems of linear equations with exponentially improved dependence on precision. 2017, arXiv: 1511.02306.

[CW12]

Andrew M. Childs and Nathan Wiebe. Hamiltonian simulation using linear combinations of unitaries. Quantum Information and Computation, 12(11–12):901–924, 2012, arXiv: 1202.5822.

Peter G Doyle and J Laurie Snell. Random walks and electric networks. Mathematical Association of America, 1984.

Richard P. Feynman. An operator calculus having applications in quantum electrodynamics. Phys. Rev., 84:108–128, 1951.

[GLM08]

Vittorio Giovannetti, Seth Lloyd, and Lorenzo Maccone. Quantum random access memory. Phys. Rev. Lett., 100:160501, Apr 2008, arXiv: 0708.1879.

[GR02]

Lov Grover and Terry Rudolph. Creating superpositions that correspond to efficiently integrable probability distributions. 2002, arXiv: quant-ph/0208112.

[GSLW18] András Gilyén, Yuan Su, Guang Hao Low, and Nathan Wiebe. Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics. 2018, arXiv: 1806.01838.

[HHL09] Aram W. Harrow, Avinatan Hassidim, and Seth Lloyd. Quantum algorithm for linear systems of equations. Physical review letters, 103(15):150502, 2009, arXiv: 0811.3171.

Tsuyoshi Ito and Stacey Jeffery. Approximate span programs. In Proceedings of the 43rd International Colloquium on Automata, Languages and Programming (ICALP 2016), 2016, arXiv: 1507.00432.

[KP16]

Iordanis Kerenidis and Anupam Prakash. Quantum recommendation systems. 2016, arXiv: 1603.08675.

[KP17]

Iordanis Kerenidis and Anupam Prakash. Quantum gradient descent for linear systems and least squares. 2017, arXiv: 1704.04992.

[KS48]

Robert Karplus and Julian Schwinger. A note on saturation in microwave spectroscopy. Phys. Rev., 73:1020–1026, 1948.

Guang Hao Low and Isaac L. Chuang. Hamiltonian simulation by qubitization. 2016, arXiv: 1610.06546.

Guang Hao Low and Isaac L. Chuang. Hamiltonian simulation by uniform spectral amplification. 2017, arXiv: 1707.05391.

Seth Lloyd. Universal quantum simulators. Science, 273(5278):1073–1078, 1996.

Seth Lloyd, Masoud Mohseni, and Patrick Rebentrost. Quantum principal component analysis. Nature Physics, 10(631), 2014, arXiv: 1307.0401.

Yin Tat Lee, Satish Rao, and Nikhil Srivastava. A new approach to computing maximum flows using electrical flows. In Proceedings of the forty-fifth annual ACM symposium on Theory of computing, pages 755–764. ACM, 2013.

[LZ17]

Yang Liu and Shengyu Zhang. Fast quantum algorithms for least squares regression and statistic leverage scores. Theor. Comput. Sci., 657(PA):38–47, 2017.

Idris D. Mercer. The minimum value and the l1-norm of the dirichlet kernel. Available at http://www.idmercer.com/dirichletkernel.pdf.

[MLM17] Dominic J Moylett, Noah Linden, and Ashley Montanaro. Quantum speedup of the traveling-salesman problem for bounded-degree graphs. Physical Review A, 95(3):032323, 2017, arXiv: 1612.06203.

[Mon15] Ashley Montanaro. Quantum walk speedup of backtracking algorithms. 2015, arXiv: 1509.02374.   
[NB16] Leonardo Novo and Dominic W. Berry. Improved hamiltonian simulation via a truncated Taylor series and corrections. Quantum Information and Computation, 17(7– 8):0623–0635, 2016, arXiv: 1611.10033.   
[PQSV11] David Poulin, Angie Qarry, Rolando Somma, and Frank Verstraete. Quantum simulation of time-dependent hamiltonians and the convenient illusion of hilbert space. Phys. Rev. Lett., 106:170501, Apr 2011, arXiv: 1102.1360.   
[SS11] Daniel A Spielman and Nikhil Srivastava. Graph sparsification by effective resistances. SIAM Journal on Computing, 40(6):1913–1926, 2011, arXiv: 0803.0929.   
[SSP16] Maria Schuld, Ilya Sinayskiy, and Francesco Petruccione. Prediction by linear regression on a quantum computer. Physical Review A, 94:022342, 2016, arXiv: 1601.07823.   
[TS13] Amnon Ta-Shma. Inverting well conditioned matrices in quantum logspace. In Proceedings of the Forty-fifth Annual ACM Symposium on Theory of Computing, pages 881–890, 2013.   
[Wan17a] Guoming Wang. Efficient quantum algorithms for analyzing large sparse electrical networks. Quantum Information and Computation, 11 and 12:987–1026, 2017, arXiv: 1311.1851.   
[Wan17b] Guoming Wang. Quantum algorithm for linear regression. Physical Review A, 96:012335, 2017, arXiv: 1402.0660.   
[WBHS11] Nathan Wiebe, Dominic W. Berry, Peter Høyer, and Barry C. Sanders. Simulating hamiltonian dynamics on a quantum computer. Journal of Physics A, 44(44):445308, 2011, arXiv: 1011.3489.   
[WBL12] Nathan Wiebe, Daniel Braun, and Seth Lloyd. Quantum algorithm for data fitting. Physical review letters, 109(5):050505, 2012, arXiv: 1204.5242.   
[WW18] Chunhao Wang and Leonard Wossnig. A quantum algorithm for simulating nonsparse hamiltonian, 2018, arXiv: 1803.08273.   
[WZP18] Leonard Wossnig, Zhikuan Zhao, and Anupam Prakash. Quantum linear system algorithm for dense matrices. Physical review letters, 120(5):050502, 2018, arXiv: 1704.06174.

# A Technical results about block-encodings

In this appendix we first prove some results about products of block-encodings, then we turn to smooth-functions of Hermitian matrices.

In order to improve the complexity of multiplication of block-encoded matrices, we invoke a result about efficiently amplifying a subnormalized block-encoding, as proposed by Low and Chuang [LC17]. The following result is proven in [GSLW18].

Lemma 47 (Uniform block-amplification). Let $A \in \mathbb { R } ^ { M \times N }$ such that $\left\| A \right\| \leq 1$ . If $\alpha \geq 1$ and $U$ is a $( \alpha , a , \delta )$ -block-encoding of $A$ that can be implemented in time $T _ { U } ,$ then there is $a$ $( \sqrt { 2 } , a + 1 , \delta + \gamma )$ -block-encoding of $A$ that can be implemented in time $\mathcal { O } ( \alpha ( T _ { U } + a ) \log ( 1 / \gamma ) )$ .

Lemma 5. (Poduct of preamplified block-matrices [LC16]) Let $A ~ \in ~ \mathbb { R } ^ { M \times N }$ and $B \in \mathbb { R } ^ { N \times K }$ such that $\left\| A \right\| \leq 1 , \left\| B \right\| \leq 1$ . $I f \ \alpha \ \geq \ 1$ and $U$ is a $( \alpha , a , \delta )$ -block-encoding of $A$ that can be implemented in time $T _ { U }$ ; $\beta \geq 1$ and $V$ is a $( \beta , b , \varepsilon )$ -block-encoding of $B$ that can be implemented in time $T _ { V } ,$ , then there is $a$ $( 2 , a + b + 2 , \sqrt { 2 } ( \delta + \varepsilon + \gamma ) )$ -block-encoding of $A B$ that can be implemented in time $\mathcal { O } ( ( \alpha ( T _ { U } + a ) + \beta ( T _ { V } + b ) ) \log ( 1 / \gamma ) )$ .

Proof. Using Lemma 47 we can implement a unitary $\widetilde { U }$ that is a $( \sqrt { 2 } , a + 1 , \delta + \gamma / 2 )$ blockencoding of $A$ in time $\mathcal { O } ( \alpha \log ( 1 / \gamma ) ( T _ { U } + a ) )$ . Similarly we can implement a unitary $\widetilde { V }$ that is a $( \sqrt { 2 } , b + 1 , \varepsilon + \gamma / 2 )$ block-encoding of $B$ in time $\mathcal { O } ( \beta \log ( 1 / \gamma ) ( T _ { V } + b ) )$ . Using Lemma 4 we get a unitary $W$ that is a $( 2 , a + b + 2 , { \sqrt { 2 } } ( \delta + \varepsilon + \gamma ) )$ block-encoding of $A B$ , that can be implemented in time $\mathcal { O } ( ( \alpha ( T _ { U } + a ) + \beta ( T _ { V } + b ) ) \log ( 1 / \gamma ) )$ . □

# A.1 Error propagation of block-encodings under various operations

In this subsection we present bounds on how the error propagates in block-encoded matrices when we perform multiplication or Hamiltonian simulation.

First we present some results about the error propagation when multiplying block-encodings in the special case when the encoded matrices are unitaries and their block-encoding does not use any extra scaling factor. In this case one might reuse the ancilla qubits, however it introduces an extra error term, which can be bounded by the geometrical mean of the two input error bounds. The following two lemmas can be found in the work of Gilyén et al. [GSLW18].

Lemma 48. If $U$ is an $( 1 , a , \delta )$ -block-encoding of an $s$ -qubit unitary operator $A ,$ and $V$ is an $( 1 , a , \varepsilon )$ -block-encoding of an $s$ -qubit unitary operator $B$ then $U V$ is a $( 1 , a , \delta + \varepsilon + 2 \sqrt { \delta \varepsilon } )$ - block-encoding of the unitary operator $A B$ .

The above lemma suggests that if we multiply together multiple block-encoded unitaries, the error may grow super-linearly. $\mathsf { B y }$ analysing the spreading of errors following a binary tree structure, one can show [GSLW18] that the error increases at most quadratically with the number of factors in the product, as stated in the following corollary.

Corollary 49. Suppose that $U _ { j }$ is an $( 1 , a , \varepsilon )$ -block-encoding of an $s$ -qubit unitary operator $W _ { j }$ for all $j \in [ K ] .$ . Then $\textstyle \prod _ { j = 1 } ^ { K } U _ { j }$ is an $( 1 , a , 4 K ^ { 2 } \varepsilon )$ -block-encoding of $\textstyle \prod _ { j = 1 } ^ { K } W _ { j }$ .

The following lemma helps us to understand error accumulation in Hamiltonian simulation, which enables us to present a more generic claim in Theorem 7.

Lemma 50. Suppose that $H , H ^ { \prime } \in \mathbb { C } ^ { s }$ are Hermitian operators, then

$$
\left\| e ^ { i t H } - e ^ { i t H ^ { \prime } } \right\| \leq | t | \| H - H ^ { \prime } \| .
$$

Proof. We recall a formula introduced by [KS48, Fey51], see also [Bel97, Page 181]:

$$
{ \frac { d } { d x } } e ^ { A ( x ) } = \int _ { 0 } ^ { 1 } e ^ { y A ( x ) } { \frac { d A ( x ) } { d x } } e ^ { ( 1 - y ) A ( x ) } d y .
$$

Now observe that

$$
\begin{array} { l } { { \displaystyle e ^ { i t H ^ { \prime } } - e ^ { i t H } = \int _ { x = 0 } ^ { 1 } \frac { d } { d x } \Big ( e ^ { i t ( H + x ( H ^ { \prime } - H ) ) } \Big ) d x } } \\ { { \displaystyle \qquad = \int _ { 0 } ^ { 1 } \int _ { 0 } ^ { 1 } e ^ { y i t ( H + x ( H ^ { \prime } - H ) ) } i t ( H ^ { \prime } - H ) e ^ { ( 1 - y ) i t ( H + x ( H ^ { \prime } - H ) ) } d y d x . } } \end{array}
$$

Finally using the triangle inequality we get that

$$
\begin{array} { l } { \displaystyle \Big \| e ^ { i t H ^ { \prime } } - e ^ { i t H } \Big \| \leq \int _ { 0 } ^ { 1 } \int _ { 0 } ^ { 1 } \Big \| e ^ { y i t ( H + x ( H ^ { \prime } - H ) ) } i t ( H ^ { \prime } - H ) e ^ { ( 1 - y ) i t ( H + x ( H ^ { \prime } - H ) ) } \Big \| d y d x } \\ { \displaystyle = \int _ { 0 } ^ { 1 } \int _ { 0 } ^ { 1 } | t | \| H ^ { \prime } - H \| d y d x } \\ { \displaystyle = | t | \| H ^ { \prime } - H \| . } \end{array}
$$

Now we restate the following result in order to better place its proof in context.

Theorem 7. (Block-Hamiltonian simulation [LC16]) Suppose that $U$ is an $\left( \alpha , a , \varepsilon / | 2 t | \right)$ -blockencoding of the Hamiltonian $H$ . Then we can implement an $\varepsilon$ -precise Hamiltonian simulation unitary $V$ which is an $( 1 , a + 2 , \varepsilon )$ -block-encoding of $e ^ { i t H }$ , with $\mathcal { O } ( | \alpha t | + \log ( 1 / \varepsilon ) )$ uses of controlled- $U$ or its inverse and with $\mathcal { O } ( a | \alpha t | + a \log ( 1 / \varepsilon ) )$ two-qubit gates.

Proof. Let $H ^ { \prime } = \alpha ( I \otimes \langle 0 | ^ { \otimes a } ) U ( I \otimes \langle 0 | ^ { \otimes a } )$ , then $\left\| H ^ { \prime } - H \right\| \leq \varepsilon / | 2 t |$ . By [LC16, Theorem 1] we can implement $V$ an $( 1 , a + 2 , \varepsilon / 2 )$ -block-encoding of $e ^ { i t H ^ { \prime } }$ , with $\mathcal { O } ( | \alpha t | + \log ( 1 / \varepsilon ) )$ uses of controlled- $U$ or its inverse and with $\mathcal { O } ( a | \alpha t | + a \log ( 1 / \varepsilon ) )$ two-qubit gates. ${ \mathsf { B y } }$ Lemma 50 we get that $V$ is an $( 1 , a + 2 , \varepsilon )$ -block-encoding of $e ^ { i t H }$ . □

Note that in order to get the optimal block-Hamiltonian simulation result, one can replace the $\log ( 1 / \varepsilon )$ term with the term $\frac { \log ( 1 / \varepsilon ) } { \log ( e + \log ( 1 / \varepsilon ) / | \alpha t | ) }$ in the above result and its proof. For more details see [GSLW18].

# A.2 Implementing smooth functions of Block-Hamiltonians

Apeldoorn et al. developed some general techniques [AGGW17, Appendix B] that make it possible to implement smooth-functions of a Hamiltonian $H _ { \ l }$ , based on Fourier series decompositions and using the Linear Combinations of Unitaries (LCU) Lemma [BCK15]. The techniques developed in [AGGW17, Appendix B] access $H$ only through controlled-Hamiltonian simulation, which we define in the following:

Definition 51. Let $M = 2 ^ { J }$ for some $J \in \mathbb { N } , \gamma \in \mathbb { R }$ and $\epsilon \geq 0$ . We say that the unitary

$$
W : = \sum _ { m = - M } ^ { M - 1 } | m \rangle \langle m | \otimes e ^ { i m \gamma H }
$$

implements controlled $( M , \gamma )$ -simulation of the Hamiltonian $H ,$ , where $| m \rangle$ denotes a (signed) bitstring $| b _ { J } b _ { J - 1 } \dots b _ { 0 } \rangle$ such that $\begin{array} { r } { m = - b _ { J } 2 ^ { J } + \sum _ { j = 0 } ^ { J - 1 } b _ { j } 2 ^ { j } } \end{array}$ .

The following lemma shows what is the cost of implementing controlled Hamiltonian simulation, provided a block-encoding of $H$ .

Lemma 52. Let $M = 2 ^ { J }$ for some $J \in \mathbb { N } ,$ , $\gamma \in \mathbb { R }$ and $\epsilon \geq 0$ . Suppose that $U$ is an $( \alpha , a , \varepsilon / | 8 ( J +$ $1 ) ^ { 2 } M \gamma | )$ -block-encoding of the Hamiltonian $H$ . Then we can implement $a$ $( 1 , a + 2 , \varepsilon )$ -blockencoding of a controlled $( M , \gamma )$ -simulation of the Hamiltonian $H _ { \ast }$ , with $\mathcal { O } ( \vert \alpha M \gamma \vert + J \log ( J / \varepsilon ) )$ uses of controlled- $. U$ or its inverse and with $\mathcal { O } ( a | \alpha M \gamma | + a J \log ( J / \varepsilon ) )$ two-qubit gates.

Proof. We use the result of Theorem 7, which tells us that we can implement Hamiltonian simulation of $H$ for time $t \leq M \gamma$ with $\varepsilon / ( J + 1 ) ^ { 2 }$ precision using

$$
\mathcal { O } ( | \alpha M \gamma | + \log ( J / \varepsilon ) )
$$

uses of controlled- $U$ or its inverse and with

$$
\mathcal { O } ( a | \alpha M \gamma | + a \log ( J / \varepsilon ) )
$$

two-qubit gates.

Now we write the sought unitary $W$ as the product of controlled Hamiltonian simulation unitaries. For $b \in \{ 0 , 1 \}$ let us introduce the projector $| b \rangle \langle b | _ { j } : = I _ { 2 ^ { j } } \otimes | b \rangle \langle b | \otimes I _ { 2 ^ { J - j } } ,$ where $J = \log ( M )$ . Observe that

$$
W = \left( | 1 \rangle \langle 1 | _ { J } \otimes e ^ { - i 2 ^ { J } \gamma H } + | 0 \rangle \langle 0 | _ { J } \otimes I \right) \prod _ { j = 0 } ^ { J - 1 } \left( | 1 \rangle \langle 1 | _ { j } \otimes e ^ { i 2 ^ { j } \gamma H } + | 0 \rangle \langle 0 | _ { j } \otimes I \right) .
$$

We can implement an $( 1 , a + 2 , \varepsilon / ( 4 ( J + 1 ) ^ { 2 } ) )$ -block-encoding of the $j .$ -th operator $e ^ { \pm i 2 ^ { j } \gamma H }$ in the product (32) with using $\begin{array} { r } { \mathcal { O } \big ( \alpha 2 ^ { j } \gamma + \log \big ( \frac { j } { \varepsilon } \big ) \big ) } \end{array}$ queries (30) and using $\mathcal { O } \big ( a | \alpha 2 ^ { j } \gamma | + a \log ( J / \varepsilon ) \big )$ two-qubit gates by (31). ${ \mathsf { B y } }$ Corollary 49 we get the sought error bound. The complexity statement easily follows by adding up the complexities.

Now we invoke [AGGW17, Theorem 40] about implementing smooth functions of Hamiltonians. The theorem is stated slightly differently in order to adapt it to the terminology used here, but the the same proof applies as for [AGGW17, Theorem 40].

Theorem 53 (Implementing a smooth function of a Hamiltonian). Let $x _ { 0 } \in \mathbb { R }$ and $r > 0$ be such that P $\begin{array} { r } { f ( x _ { 0 } + x ) = \sum _ { \ell = 0 } ^ { \infty } a _ { \ell } x ^ { \ell } } \end{array}$ for all $x \in [ - r , r ] .$ . Suppose    $B > 0$ and $\delta \in ( 0 , r ]$ are such that ${ \textstyle \sum _ { \ell = 0 } ^ { \infty } ( r + \delta ) ^ { \ell } | a _ { \ell } | \le B }$ . $I f \left\| H - x _ { 0 } I \right\| \leq r$ and $\begin{array} { r } { \varepsilon ^ { \prime } \in \left( 0 , \frac { 1 } { 2 } \right] , } \end{array}$ then we can implement a unitary $\tilde { U }$ that is $\tau \left( B , a + \mathcal { O } \big ( \log ( r \log ( 1 / \varepsilon ^ { \prime } ) / \delta ) \big ) , B \varepsilon ^ { \prime } \right)$ -block-encoding of $f ( H )$ , with a single use of a circuit $V$ which is a $( 1 , a , \varepsilon ^ { \prime } / 2 )$ -block-encoding of controlled       $\left( \mathcal { O } \left( r \log ( 1 / \varepsilon ^ { \prime } ) / \delta \right) , \mathcal { O } ( 1 / r ) \right)$ -simulation of $H _ { \ast }$ , and with using $\mathcal { O } \big ( r / \delta \log \big ( r / ( \delta \varepsilon ^ { \prime } ) \big ) \log \big ( 1 / \varepsilon ^ { \prime } \big ) \big )$ two-qubit gates.

Now we are ready to prove our result about implementing power functions of both negative and positive exponents.

Corollary 54. Let $\kappa \geq 2$ , $c \in ( 0 , \infty )$ and $H$ be an $s$ -qubit Hamiltonian such that $I / \kappa \preceq H \preceq I .$ Then we can implement a unitary $\tilde { U }$ that is $a$ $( 2 \kappa ^ { c } , a + \mathcal { O } ( \log ( \kappa ^ { c } \operatorname* { m a x } ( 1 , c ) \log ( \kappa ^ { c } / \varepsilon ) ) ) , \varepsilon )$ -blockencoding of $H ^ { - c }$ , with $a$ single use of a circuit $V$ which is $a \left( 1 , a , \varepsilon / ( 4 \kappa ^ { c } ) \right)$ -block-encoding of con- trolled $( \mathcal { O } ( \kappa \operatorname* { m a x } ( 1 , c ) \log ( \kappa ^ { c } / \varepsilon ) ) , \mathcal { O } ( 1 ) )$ -simulation of H, and with using $\mathcal { O } \left( \kappa \operatorname* { m a x } ( 1 , c ) \log ^ { 2 } \left( \kappa ^ { 1 + c } / \varepsilon \right) \right)$ two-qubit gates.

Proof. Let $f ( y ) : = y ^ { - c }$ and observe that $\begin{array} { r } { f ( 1 + x ) = ( 1 + x ) ^ { - c } = \sum _ { k = 0 } ^ { \infty } \binom { - c } { k } x ^ { k } } \end{array}$ for all $x \in ( - 1 , 1 )$ . We choose $\mathrm { ~ : = ~ } 1 \mathrm { , ~ } r : = 1 - 1 / \kappa \mathrm { , ~ } \delta : = 1 / ( 2 \kappa \operatorname* { m a x } ( 1 \mathrm { , ~ } c ) )$ , and observe that

$$
\begin{array} { r l } & { \displaystyle \sum _ { k = 0 } ^ { \infty } | ( \begin{array} { l } { - c } \\ { k } \end{array} ) | ( r + \delta ) ^ { k } = \sum _ { k = 0 } ^ { \infty } | ( \begin{array} { l } { - c } \\ { k } \end{array} ) | ( 1 - \frac { 1 } { \kappa } + \frac { 1 } { 2 \kappa \mathsf { m a x } ( 1 , c ) } ) ^ { k } } \\ & { \qquad = \displaystyle \sum _ { k = 0 } ^ { \infty } ( \begin{array} { l } { - c } \\ { k } \end{array} ) ( \frac { 1 } { \kappa } ( 1 - \frac { 1 } { 2 \mathsf { m a x } ( 1 , c ) } ) - 1 ) ^ { k } } \\ & { \qquad = \kappa ^ { c } ( 1 - \frac { 1 } { 2 \mathsf { m a x } ( 1 , c ) } ) ^ { - c } } \\ & { \qquad \le \displaystyle \sum _ { k = 0 } ^ { \infty } ( \frac { c ^ { 2 } \kappa ^ { c } } { 2 \kappa } . } \end{array}
$$

$\mathsf { B y }$ choosing $\varepsilon ^ { \prime } : = \varepsilon / ( 2 \kappa ^ { c } )$ we get the results by invoking Theorem 53.

Lemma 9. (Implementing negative powers of Hermitian matrices) Let $c \in ( 0 , \infty ) , \kappa \geq 2 ,$ and let $H$ be a Hermitian matrix such that $I / \kappa \preceq H \preceq I .$ . Suppose that $\begin{array} { r } { \delta = o \left( \varepsilon / \left( \kappa ^ { 1 + c } ( 1 + c ) \log ^ { 3 } \frac { \kappa ^ { 1 + c } } { \varepsilon } \right) \right) } \end{array}$ and $U$ is an $( \alpha , a , \delta )$ -block-encoding of $H$ , that can be implemented using $T _ { U }$ elementary gates. Then for any $\varepsilon _ { \varepsilon }$ , we can implement a unitary $\widetilde { U }$ that is a $\begin{array} { r } { ( 2 \kappa ^ { c } , a + \mathcal { O } \big ( \log ( \kappa ^ { 1 + c } \log \frac { 1 } { \varepsilon } \big ) , \varepsilon \big ) } \end{array}$ -blockencoding of $H ^ { - c }$ in cost

$$
\mathcal { O } ( \alpha \kappa ( a + T _ { U } ) ( 1 + c ) \log ^ { 2 } ( \frac { \kappa ^ { 1 + c } } { \varepsilon } ) ) .
$$

Proof. By Lemma 52, we can implement a   $\textstyle \left( { 1 , a + 2 , { \frac { \varepsilon } { 4 \kappa ^ { c } } } } \right)$ -block-encoding $V$ of $( t , \gamma )$ -controlled simulation of $H ,$ , for $\begin{array} { r } { t = \mathcal { O } \big ( \kappa \mathsf { m a x } ( 1 , c ) \mathsf { l o g } { \frac { \kappa ^ { c } } { \varepsilon } } \big ) } \end{array}$ and $\gamma = \mathcal { O } ( 1 ) .$ , in cost

$$
T _ { V } = { \cal O } \left( \left( \alpha t + \log t \log \frac { \kappa ^ { c } \log t } { \varepsilon } \right) \left( a + T _ { U } \right) \right) = { \cal O } \left( \left( \alpha \kappa ( 1 + c ) \log ^ { 2 } \frac { \kappa ^ { 1 + c } } { \varepsilon } \right) \left( a + T _ { U } \right) \right) .
$$

Then by Corollary 54, we can implement a $\begin{array} { r } { ( 2 \kappa ^ { c } , a + \mathcal { O } \big ( \mathsf { l o g } ( \kappa ^ { c } \mathsf { m a x } ( 1 , c ) \mathsf { l o g } \frac { \kappa ^ { c } } { \varepsilon } \big ) , \varepsilon \big ) . } \end{array}$ -blockencoding of $H ^ { - c }$ in gate complexity $\begin{array} { r } { T _ { V } + \mathcal { O } \left( \kappa \mathrm { m a x } ( 1 , c ) \log ^ { 2 } \frac { \kappa ^ { 1 + c } \mathrm { m a x } ( 1 , c ) } { \varepsilon } \right) } \end{array}$ , which gives total cost:

$$
\mathcal { O } \left( \left( \alpha \kappa ( 1 + c ) \log ^ { 2 } \frac { \kappa ^ { 1 + c } } { \varepsilon } \right) ( a + T _ { U } ) \right) .
$$

Similarly we prove a result about implementing power functions of positive exponents.

Corollary 55. Let $\kappa \geq 2 .$ , $c \in ( 0 , 1 ]$ and $H$ be an $s$ -qubit Hamiltonian such that $I / \kappa \preceq H \preceq I .$ Then we can implement a unitary $\tilde { U }$ that is a $( 2 , a + \mathcal { O } ( \log \log ( 1 / \varepsilon ) ) , \varepsilon )$ -block-encoding of $H ^ { c }$ , with a single use of a circuit $V$ which is $a \left( 1 , a , \varepsilon / 4 \right)$ -block-encoding of controlled $( \mathcal { O } ( \kappa \log ( 1 / \varepsilon ) ) , \mathcal { O } ( 1 ) ) .$ - simulation of $H ,$ and with using $\mathcal { O } ( \kappa \log ( \kappa / \varepsilon ) \log ( 1 / \varepsilon ) )$ two-qubit gates.

Proof. Let $f ( y ) : = y ^ { c }$ and observe that $\begin{array} { r } { f ( 1 + x ) = ( 1 + x ) ^ { c } = \sum _ { k = 0 } ^ { \infty } \binom { c } { k } x ^ { k } } \end{array}$ for all $x \in [ - 1 , 1 ]$ . We choose $x _ { 0 } : = 1$ , $r : = 1 - 1 / \kappa , \delta : = 1 / \kappa ,$ and observe that

$$
\begin{array} { l } { { \displaystyle \sum _ { k = 0 } ^ { \infty } \left| \left( { { { \bf \Lambda } ^ { c } } } \right) \left| \left( { r + \delta } \right) ^ { k } - \mathrm { s } _ { k = 0 } ^ { \infty } \right| \left( { { { \bf \Lambda } ^ { c } } } \right) \right| } } \\ { { \displaystyle \qquad = 1 - \sum _ { k = 1 } ^ { \infty } \left( { { { \bf \Lambda } ^ { c } } } \right) \left( - 1 \right) ^ { k } \left( - 1 \right) ^ { k } } } \\ { { \displaystyle \qquad = 2 - \sum _ { k = 0 } ^ { \infty } \left( { { { \bf \Lambda } ^ { c } } } \right) \left( - 1 \right) ^ { k } \left( - 1 \right) ^ { k } } } \\ { { \displaystyle \qquad = 2 - f \{ 1 - 1 } \} } \\ { { \displaystyle \qquad = \sum _ { k = 0 } ^ { \infty } \sum _ { k = 1 } ^ { \infty } \left( { { { \bf \Lambda } ^ { c } } } \right) \left( - 1 \right) ^ { k } } } \end{array}
$$

$\mathsf { B y }$ choosing $\varepsilon ^ { \prime } : = \varepsilon / 2$ we get the results $\mathsf { b y }$ invoking Theorem 53.

Lemma 10. (Implementing positive powers of Hermitian matrices) Let $c \in ( 0 , 1 ]$ , $\kappa \geq 2 ,$ , and $H$ a Hermitian matrix such that $I / \kappa \preceq H \preceq I .$ Suppose that for $\delta = o \left( \varepsilon / ( \kappa \log ^ { 3 } \frac { \kappa } { \varepsilon } ) \right) .$ , and we are given a unitary $U$ that is an $( \alpha , a , \delta )$ -block-encoding of $H _ { \ast }$ , that can be implemented using $T _ { U }$ elementary gates. Then for any $\varepsilon ,$ , we can implement $a$ unitary $\widetilde { U }$ that is $a$ $( 2 , a +$ $\mathcal { O } ( \log \log ( 1 / \varepsilon ) ) , \varepsilon )$ -block-encoding of $H ^ { c }$ in cost

$$
\mathcal { O } \left( \alpha \kappa ( a + T _ { U } ) \log ^ { 2 } ( \kappa / \varepsilon ) \right) .
$$

Proof. ${ \mathsf { B y } }$ Lemma 52, we can implement a $( 1 , a + 2 , \frac { \varepsilon } { 4 } )$ -block-encoding $V$ of $( t , \gamma )$ -controlled simulation of $H$ , for $t = \mathcal { O } ( \kappa \log ( 1 / \varepsilon ) )$ and $\gamma = \mathcal { O } ( 1 )$ , in cost

$$
T _ { V } = { \cal O } \left( \left( \alpha t + \log t \log \frac { \log t } { \varepsilon } \right) \left( a + T _ { U } \right) \right) .
$$

Then by Corollary 55, we can implement a $( 2 , a + \mathcal { O } ( \log \log ( 1 / \varepsilon ) ) , \varepsilon ) .$ -block-encoding of $H ^ { c }$ in gate complexity $T _ { V } + \mathcal { O } ( \kappa \log ( \kappa / \varepsilon ) \log ( 1 / \varepsilon ) )$ . The result follows. □

# A.3 Variable time quantum algorithm for implementing negative powers of Hermitian matrices

Theorem 33. (Variable-time quantum algorithm for implementing negative powers) Let $\kappa \geq 2 ,$ , $c \in ( 0 , \infty )$ , $q = \mathsf { m a x } ( 1 , c ) .$ , and $H$ be an $N \times N$ Hermitian matrix such that the eigenvalues   of $H$ lie in the range $[ - 1 , - 1 / \kappa ] \bigcup [ 1 / \kappa , 1 ]$ . Suppose that for $\delta = o \left( \varepsilon / \left( \kappa ^ { q } q \log ^ { 3 } { \frac { \kappa ^ { q } } { \varepsilon } } \right) \right) $ we have a unitary $U$ that is a $( \alpha , a , \delta )$ -block-encoding of $H$ which can be implemented using $T _ { U }$ elementary gates. Also suppose that we can prepare an input state $| \psi \rangle$ that is spanned by the eigenvectors of $H$ in time $T _ { \psi }$ . Then there exists a variable time quantum algorithm that outputs a state that is $\varepsilon$ -close to $\left. H ^ { - c } | \psi \rangle / \right| \left| H ^ { - c } | \psi \rangle \right|$ with a cost of

$$
\mathcal { O } \left( \left( \alpha \kappa ^ { q } \big ( T _ { U } + a \big ) q \log ^ { 2 } \left( \frac { \kappa ^ { q } } { \varepsilon } \right) + \kappa ^ { c } T _ { \psi } \right) \log ( \kappa ) \right) .
$$

Also, there exists $a$ variable time quantum algorithm that outputs a number $\Gamma$ such that

$$
1 - \varepsilon \leq \frac { \Gamma } { \left\| H ^ { - c } | \psi \rangle \right\| } \leq 1 + \varepsilon ,
$$

at a cost

$$
\mathcal { O } \left( \frac { 1 } { \varepsilon } \left( \alpha \kappa ^ { q } \big ( T _ { U } + a \big ) q \log ^ { 2 } \left( \frac { \kappa ^ { q } } { \varepsilon } \right) + \kappa ^ { c } T _ { \psi } \right) \log ^ { 3 } ( \kappa ) \log \left( \frac { \log ( \kappa ) } { \delta } \right) \right) ,
$$

with success probability at least $1 - \delta$ .

Proof. We follow the same argument as Theorem 30, except that $\epsilon ^ { \prime } = \varepsilon / ( m \alpha _ { \mathrm { m a x } } )$ where $\alpha _ { m a x } =$ $\mathcal { O } ( \kappa ^ { c } )$ . This gives us that

$$
T _ { \mathrm { m a x } } = \mathcal { O } \left( \alpha \kappa q \log ^ { 2 } \left( \frac { q \kappa ^ { q } } { \epsilon ^ { \prime } } \right) \left( a + T _ { U } \right) \right) = \mathcal { O } \left( \alpha q \kappa \log ^ { 2 } \left( \frac { q \kappa ^ { q } } { \varepsilon } \right) \left( a + T _ { U } \right) \right) ,
$$

and $T _ { \mathrm { m a x } } ^ { \prime } = \mathcal { O } ( \kappa )$ . We can calculate the $l _ { 2 }$ -averaged stopping time of $\mathcal { A } , \left. \tau \right. _ { 2 }$ as

$$
\begin{array} { r l } & { \| T \| _ { 2 } ^ { 2 } = \displaystyle \sum _ { j } p _ { j } t _ { j } ^ { 2 } } \\ & { \qquad = \displaystyle \sum _ { k } | c _ { k } | ^ { 2 } \sum _ { j } ( \| \Pi _ { C _ { j } } A _ { j } \dots A _ { 1 } | \lambda _ { k }  _ { l } | 0 \rangle _ { C F P Q } \| ^ { 2 } t _ { j } ^ { 2 } ) } \\ & { \qquad = \displaystyle \mathcal { O } ( \alpha ^ { 2 } q ^ { 2 } ( a + T _ { U } ) ^ { 2 } \sum _ { k } \frac { | c _ { k } | ^ { 2 } } { \lambda _ { k } ^ { 2 } } \log ^ { 4 } \frac { q \kappa ^ { c } \log \kappa } { \varepsilon \lambda _ { k } ^ { q } } ) } \\ & { \qquad \implies \| T \| _ { 2 } \le \alpha q ( a + T _ { U } ) \log ^ { 2 } ( \frac { q \kappa ^ { q } } { \varepsilon } ) \sqrt { \sum _ { k } \frac { | c _ { k } | ^ { 2 } } { \lambda _ { k } ^ { 2 } } } . } \end{array}
$$

Also the success probability, $p _ { \mathsf { s u c c } }$ can be written as

$$
\begin{array} { l } { \displaystyle { \sqrt { p _ { \mathrm { s u c c } } } = \left\| \Pi _ { F } \frac { H ^ { - c } } { \alpha _ { \mathrm { m a x } } } | \psi \rangle _ { I } | \Phi \rangle _ { C F P Q } \right\| + \mathcal { O } \big ( m \epsilon ^ { \prime } \big ) } } \\ { \displaystyle { = \frac { 1 } { \alpha _ { \mathrm { m a x } } } \left( \sum _ { k } \frac { \left. c _ { k } \right. ^ { 2 } } { \lambda _ { k } ^ { 2 c } } \right) ^ { 1 / 2 } + \mathcal { O } \left( \frac { \varepsilon } { \alpha _ { \mathrm { m a x } } } \right) } } \\ { \displaystyle { \geq \Omega \left( \frac { 1 } { \kappa ^ { c } } \right) \left( \sum _ { k } \frac { \left. c _ { k } \right. ^ { 2 } } { \lambda _ { k } ^ { 2 c } } \right) ^ { 1 / 2 } } . } \end{array}
$$

When $c \geq 1$ we have:

$$
\sqrt { \frac { \sum _ { k } | c _ { k } | ^ { 2 } } { \lambda _ { k } ^ { 2 c } } } \geq \sqrt { \frac { \sum _ { k } | c _ { k } | ^ { 2 } } { \lambda _ { k } ^ { 2 } } } .
$$

Thus, the success probability satisfies:

$$
\sqrt { p _ { \mathrm { s u c c } } } \geq \Omega \left( \frac { 1 } { \kappa ^ { c } } \right) \sqrt { \sum _ { k } \frac { | c _ { k } | ^ { 2 } } { \lambda _ { k } ^ { 2 } } } .
$$

On the other hand, using that $| \kappa \lambda _ { k } | \geq 1$ , term-by-term comparison reveals that for all $c \in [ 0 , 1 ]$

$$
\begin{array} { l } { \displaystyle \sum _ { k } \frac { | c _ { k } | ^ { 2 } } { ( \kappa \lambda _ { k } ) ^ { 2 c } } \geq \sum _ { k } \frac { | c _ { k } | ^ { 2 } } { ( \kappa \lambda _ { k } ) ^ { 2 } } } \\ { \displaystyle \sqrt { \frac { \sum _ { k } | c _ { k } | ^ { 2 } } { \lambda _ { k } ^ { 2 c } } } \geq \kappa ^ { - 1 + c } \sqrt { \frac { \sum _ { k } | c _ { k } | ^ { 2 } } { \lambda _ { k } ^ { 2 } } } . } \end{array}
$$

So for this case, the success probability is bounded as

$$
\sqrt { p _ { \mathrm { s u c c } } } \geq \Omega \left( \frac { 1 } { \kappa } \right) \sqrt { \sum _ { k } { \frac { | c _ { k } | ^ { 2 } } { \lambda _ { k } ^ { 2 } } } } .
$$

$\mathsf { B y }$ combining (33) and (34), we have that for $c \in ( 0 , \infty )$

$$
\sqrt { p _ { \mathrm { s u c c } } } \geq \Omega \left( \frac { 1 } { \kappa ^ { q } } \right) \sqrt { \sum _ { k } \frac { | c _ { k } | ^ { 2 } } { \lambda _ { k } ^ { 2 } } } .
$$

The final complexity of applying VTAA is given by Theorem 23 as (neglecting constants):

$$
\begin{array} { r l } & { T _ { \mathrm { m a x } } + T _ { \psi } + \frac { \left( \left. T \right. _ { 2 } + T _ { \psi } \right) \log ( T _ { \mathrm { m a x } } ^ { \prime } ) } { \sqrt { p _ { \mathrm { s u c c } } } } } \\ & { = \alpha q \kappa \log ^ { 2 } \left( \frac { q \kappa ^ { q } } { \varepsilon } \right) ( a + T _ { U } ) + \left( \alpha q \kappa ^ { q } ( a + T _ { U } ) \log ^ { 2 } \left( \frac { q \kappa ^ { q } } { \varepsilon } \right) + \kappa ^ { c } T _ { \psi } \right) \log ( \kappa ) } \\ & { = { \cal O } \left( \left( \alpha q \kappa ^ { q } ( a + T _ { U } ) \log ^ { 2 } \left( \frac { q \kappa ^ { q } } { \varepsilon } \right) + \kappa ^ { c } T _ { \psi } \right) \log ( \kappa ) \right) . } \end{array}
$$

The second part follows from Corollary 32.