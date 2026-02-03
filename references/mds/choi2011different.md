# Adiabatic Quantum Algorithms for the NP-Complete Maximum-Weight Independent Set, Exact Cover and 3SAT Problems

Vicky Choi   
vchoi@cs.vt.edu   
Department of Computer Science   
Virginia Tech   
Falls Church, VA

November 26, 2024

# Abstract

The problem Hamiltonian of the adiabatic quantum algorithm for the maximum-weight independent set problem (MIS) that is based on the reduction to the Ising problem (as described in [6]) has flexible parameters. We show that by choosing the parameters appropriately in the problem Hamiltonian (without changing the problem to be solved) for MIS on CK graphs [7], we can prevent the first order quantum phase transition [4] and significantly change the minimum spectral gap. We raise the basic question about what the appropriate formulation of adiabatic running time should be. We also describe adiabatic quantum algorithms for Exact Cover and 3SAT in which the problem Hamiltonians are based on the reduction to MIS. We point out that the argument in Altshuler et al. [2] that their adiabatic quantum algorithm failed with high probability for randomly generated instances of Exact Cover does not carry over to this new algorithm.

# 1 Introduction

Adiabatic quantum computation (AQC) was proposed by Farhi et al. [12] in 2000 as an alternative quantum paradigm to solve NP-hard optimization problems, which are believed to be classically intractable. Later, it was shown by Aharonov et al. [1] that AQC is not just limited to optimization problems, and is polynomially equivalent to conventional quantum computation (quantum circuit model). A quantum computer promises extraordinary power over a classical computer, as demonstrated by Shor [22] in 1994 with the polynomial quantum algorithm for solving the factoring problem, for which the best known classical algorithms are exponential. Just how much more powerful are quantum computers? In particular, we are interested in whether an adiabatic quantum computer can solve NP-complete problems more efficiently than a classical computer.

Unlike classical computation or conventional quantum model in which an algorithm is specified by a finite sequence of discrete operations via classical/quantum gates, the adiabatic quantum algorithm is continuous. It has been assumed (see Section 2 for more discussion) that, according to the adiabatic theorem, the dominant factor of the adiabatic running time (ART) of the algorithm scales polynomially with the inverse of the minimum spectral $g a p \ g _ { \mathsf { m i n } }$ of the system Hamiltonian (that describes the algorithm). Therefore, in order to analyze the running time of an adiabatic algorithm, it is necessary to be able to bound $g _ { \mathrm { m i n } }$ analytically. However, $g _ { \mathrm { m i n } }$ is in general difficult to compute (it is as hard as solving the original problem if computed directly). Rigorous analytical analysis of adiabatic algorithms remains challenging. Most of studies have to resort to numerical calculations. These include numerical integration of Schrodinger equation [12, 5], eigenvalue computation (or exact diagonization)[28, 21], ¨ and quantum Monte Carlo (QMC) technique [25, 26]. However, not only are these methods limited to small sizes (as the simulations of quantum systems grow exponentially with the system size), but also little insight can be gained from these numbers to design and analyze the time complexity of the algorithm.

Perhaps, from the algorithmic design point of view, it is more important to unveil the quantum evolution black-box and thus enable us to obtain insight for designing efficient adiabatic quantum algorithms. For this purpose, we devise a visualization tool, called Decomposed State Evolution Visualization (DESEV). Through the aid of this tool, we constructed a family of instances of MIS, called CK graphs [7]. The numerical results of an adiabatic algorithm for MIS on these graphs suggested that $g _ { \mathsf { m i n } }$ is exponentially small and thus the algorithm requires exponential time. These results were then explained by the first order quantum phase transition (FQPT) in [4]. Since then, there have been some other papers (Altshuler et al., [2] ; Farhi et al., [14]; Young et al., [26]; Jorg et al., [18, 19]) investigating the same phenomenon, i.e., first order quantum phase transition. In particular, Farhi et al. in [14] suggested that the exponential small gap caused by the FQPT could be overcome (for the set of instances they consider) by randomizing the choice of initial Hamiltonian. In this paper, we show that by changing the parameters in the problem Hamiltonian (without changing the problem to be solved) of the adiabatic algorithm for MIS on CK graphs, we prevent the FQPT from occurring and significantly increase $g _ { \mathrm { m i n } }$ . We do so by scaling the vertex-weight of the graph, namely, multiplying the weights of vertices by a scaling factor. In order to determine the best scaling factor, we raise the basic question about what the appropriate formulation of adiabatic running time should be.

We also describe adiabatic quantum algorithms for Exact Cover and 3SAT in which the problem Hamiltonians are based on the reduction to MIS. In [2], Altshuler et al. claimed that a particular adiabatic quantum algorithm failed with high probability for randomly generated instances of Exact Cover. They claimed that the correctness of their argument did not rely on the specific form of the problem Hamiltonian for Exact Cover. We demonstrate an adiabatic algorithm for Exact Cover in which the problem Hamiltonian is based on the reduction to MIS that questions the generality of this claim.

This paper is organized as follows. In Section 2, we review the adiabatic quantum algorithm, and adiabatic running time. In Section 3, we recall the adiabatic quantum algorithm for MIS based on the reduction to the Ising problem. In Section 4, we describe the visualization tool DESEV and the CK graphs. We show examples of DESEV on the MIS adiabatic algorithm for CK graphs. In Section 5, we describe how changing the parameters affects $g _ { \mathrm { m i n } }$ , and raise the question about ART. In Section 6, we describe adiabatic algorithms for Exact Cover and 3SAT that are based on MIS reduction. We conclude with the discussion in Section 7.

# 2 Adiabatic Quantum Algorithm

An adiabatic quantum algorithm is described by a time-dependent system Hamiltonian

$$
\mathcal { H } ( t ) = ( 1 - s ( t ) ) \mathcal { H } _ { \mathrm { i n i t } } + s ( t ) \mathcal { H } _ { \mathrm { p r o b l e m } }
$$

for $t \in [ 0 , T ] , s ( 0 ) = 0 , s ( T ) = 1$ . There are three components of $\mathcal { H } ( . )$ : (1) initial Hamiltonian: $\mathcal { H } ( 0 ) = \mathcal { H } _ { \mathrm { i n i t } }$ ; (2) problem Hamiltonian: $\mathcal { H } ( T ) = \mathcal { H } _ { \sf p r o b l e m }$ ; and (3) evolution path: $s : [ 0 , T ] \longrightarrow [ 0 , 1 ]$ , e.g., $\begin{array} { r } { s ( t ) = \frac { t } { T } } \end{array}$ . $\mathcal { H } ( t )$ is an adiabatic algorithm for an optimization problem if we encode the problem into the problem Hamiltonian $\mathcal { H } _ { \mathrm { p r o b l e m } }$ such that the ground state of $\mathcal { H } _ { \mathrm { p r o b l e m } }$ corresponds to the answer to the problem. The initial Hamiltonian $\mathcal { H } _ { \mathrm { i n i t } }$ is chosen to be non-commutative with $\mathcal { H } _ { \mathrm { p r o b l e m } }$ and its ground state must be known and experimentally constructable, e.g., $\begin{array} { r } { \mathcal { H } _ { \sf i n i t a l } = - \sum _ { i \in \mathsf { V } ( G ) } \Delta _ { i } \sigma _ { i } ^ { x } } \end{array}$ . Here $T$ is the running time of the algorithm. According to the adiabatic theorem, if $\mathcal { H } ( t )$ evolves “slowly” enough, or equivalently, if $T$ is “large” enough (see Adiabatic

Running Time below) the system remains in the ground state of $\mathcal { H } ( t )$ , and consequently, ground state of $\mathcal { H } ( T ) =$ $\mathcal { H } _ { \mathrm { p r o b l e m } }$ gives the solution to the problem.

Notice that given a problem, there are three components (initial Hamiltonian, problem Hamiltonian, and evolution path) that specify an adiabatic algorithm for the problem. A change in an component (e.g. initial Hamiltonian) will result in a different adiabatic algorithm for the same problem.

In this paper, we fix the evolution path by the linear interpolation function $\begin{array} { r } { s ( t ) = \frac { t } { T } } \end{array}$ . Hereafter, we describe an adiabatic algorithm by the re-parametrized Hamiltonian

$$
\mathcal { H } ( s ) = ( 1 - s ) \mathcal { H } _ { \mathrm { i n i t } } + s \mathcal { H } _ { \mathrm { p r o b l e m } }
$$

where $s \in [ 0 , 1 ]$ , with understanding that $s ( t ) = t / T$ . Furthermore, throughout this paper, we fix the initial Hamiltonian to be $\begin{array} { r } { \mathcal { H } _ { \mathrm { i n i t } } = - \sum _ { i \in \mathsf { V } ( G ) } \sigma _ { i } ^ { x } } \end{array}$ . When it is clear from context, we also refer to the problem Hamiltonian as the adiabatic algorithm for the problem.

Adiabatic Running Time. In their original work [11], the running time of the adiabatic algorithm is defined to be the same as the adiabatic evolution time $T$ , which is given by the adiabatic condition of the adiabatic theorem. However, this definition is under the assumption of some physical limit of the maximum energy of the system (see e.g., [17]), and is not well-defined from the computational point of view, as observed by Aharonov et al. [1]. They re-define ART $( { \mathcal { H } } )$ as $T \cdot \operatorname* { m a x } _ { s } \vert \vert \mathcal { H } ( s ) \vert \vert$ , taking into the account of the time-energy trade-off in the Schrodinger’s ¨ equation1.

On the other hand, given the extensive work on the rigorous proofs of the adiabatic theorem, it is interesting (if not confusing) that many different versions of the adiabatic conditions have been recently proposed. These include [29, 30, 31, 32, 34, 33, 37, 39, 35, 36, 38] in the quantum physics community, and [20, 1, 3] in the computer science community. Most of these studies suggest that ART scales polynomially with the inverse of the spectral gap of the system Hamiltonian, which is sufficient when one is interested in the coarse computational complexity of algorithms, namely, the distinction between polynomial and exponential running time.

However, from both the practical and algorithmic point of view, it is important to have a more precise formulation of ART. First, this is because the specification of the adiabatic evolution time $T$ is required in an adiabatic algorithm, and therefore a tight and simple upper bound is desired. Second, we are interested in the actual time complexity of the algorithm, and not just the polynomial vs. exponential distinction. It is necessary to have a more precise formulation of ART such that basic algorithmic analysis can be carried out. Third, at this stage of research, it is particularly important to have such a formulation because the spectral gap, which plays the dominating role in the formulation of ART, is difficult to analyze. All current efforts on the spectral gap analysis resort to numerical studies, and that means the studies are restricted to small problem sizes only. Therefore, to gain insight into the time complexity of algorithms from these small instances, it is important that the formulation of ART applies to small sizes. So what is the appropriate formulation of ART? What should the adiabatic condition(s) be? In Section 5.2, we compare three closely related versions and raise the question about what the appropriate adiabatic running time should be.

# 3 An Adiabatic Algorithm for MIS

In this section, we recall the adiabatic algorithm for MIS that is based on the reduction to the Ising problem, as described in [6]. First, we formally define the Maximum-Weight Independent Set (MIS) problem (optimization version):

Input: An undirected graph $G ( = ( \mathsf { V } ( G ) , \mathsf { E } ( G ) ) )$ ), where each vertex $i \in \mathsf { V } ( G ) = \{ 1 , \dots , n \}$ is weighted by a positive rational number $c _ { i }$

Output: A subset $S \subseteq \mathsf { V } ( G )$ such that $S$ is independent (i.e., for each $i , j \in \mathsf { V } ( G ) , i \neq j , i j \notin \mathsf { E } ( G ) )$ and the total weight of $\textstyle S ( = \sum _ { i \in S } c _ { i } )$ is maximized. Denote the optimal set by $\mathsf { m i s } ( G )$ .

There is a one-one correspondence between the MIS problem and the Ising problem, which is the problem directly solved by the quantum processor that implements $1 / 2$ -spin Ising Hamiltonian. We recall the quadratic binary optimization formulation of the problem. More details can be found in [6].

Theorem 3.1 (Theorem 5.1 in [6]). If $J _ { i j } \geq \operatorname* { m i n } \{ c _ { i } , c _ { j } \}$ for all $i j \in { \mathsf { E } } ( G )$ , then the maximum value of

$$
\mathcal { V } ( x _ { 1 } , \ldots , x _ { n } ) = \sum _ { i \in \mathsf { V } ( G ) } c _ { i } x _ { i } - \sum _ { i j \in \mathsf { E } ( G ) } J _ { i j } x _ { i } x _ { j }
$$

is the total weight of the MIS. In particular if $J _ { i j } > \operatorname* { m i n } \{ c _ { i } , c _ { j } \}$ for all $i j \in { \mathsf { E } } ( G )$ , then ${ \mathfrak { m i s } } ( G ) = \{ i \in \mathsf { V } ( G )$ : $x _ { i } ^ { * } = 1 \}$ , where $( x _ { 1 } ^ { * } , \ldots , x _ { n } ^ { * } ) = { \arg \operatorname* { m a x } } _ { ( x _ { 1 } , \ldots , x _ { n } ) \in \{ 0 , 1 \} ^ { n } } { \mathcal { V } } ( x _ { 1 } , \ldots , x _ { n } ) .$ .

Here the function $\mathcal { V }$ is called the pseudo-boolean function for MIS. Notice that in this formulation, we only require $J _ { i j } > \operatorname* { m i n } \{ c _ { i } , c _ { j } \}$ , and thus there is freedom in choosing this parameter. In this paper we will show how to take advantage of this.

By changing the variables $\begin{array} { r } { ( x _ { i } = \frac { 1 + s _ { i } } { 2 } , } \end{array}$ ), it is easy to show that MIS is equivalent to minimizing the following function, known as the Ising energy function:

$$
\begin{array} { r c l } { \mathscr { E } ( s _ { 1 } , \ldots , s _ { n } ) } & { = } & { \displaystyle \sum _ { i \in \mathsf { V } ( G ) } h _ { i } s _ { i } + \sum _ { i j \in \mathsf { E } ( G ) } J _ { i j } s _ { i } s _ { j } , } \end{array}
$$

which is the eigenfunction of the following Ising Hamiltonian:

$$
\mathcal { H } _ { { | \mathrm { s i n g } } } = \sum _ { i \in \mathsf { V } ( G ) } h _ { i } \sigma _ { i } ^ { z } + \sum _ { i j \in \mathsf { E } ( G ) } J _ { i j } \sigma _ { i } ^ { z } \sigma _ { j } ^ { z }
$$

where $\begin{array} { r } { h _ { i } = \sum _ { j \in \mathsf { n b r } ( i ) } J _ { i j } - 2 c _ { i } , \mathsf { n b r } ( i ) = \{ j : i j \in \mathsf E ( G ) \} } \end{array}$ , for $i \in \mathsf { V } ( G )$ .

That is, an adiabatic algorithm for MIS in which the problem Hamiltonian is ${ \mathcal { H } } _ { \mathrm { l s i n g } }$ is described by the following system Hamiltonian:

$$
\mathcal { H } ( s ) = ( 1 - s ) \mathcal { H } _ { \mathrm { i n i t } } + s \mathcal { H } _ { \mathrm { l s i n g } }
$$

where $s \in [ 0 , 1 ]$ with the assumption that $s ( t ) = t / T$ . If $T$ is sufficiently large according to the adiabatic theorem, then the ground state of $\mathcal { H } ( 1 )$ , say $\vert x _ { 1 } ^ { * } x _ { 2 } ^ { * } \dots x _ { n } ^ { * } \rangle$ , corresponds to the maximum-weight independent set, namely $\mathsf { m i s } ( G ) = \{ i : x _ { i } ^ { * } = 0 \} ^ { 2 }$ .

# 4 DESEV and CK Graphs

In this section, we describe a visualization tool, called Decomposed State Evolution Visualization (DESEV), which aims to “open up” the quantum evolution black-box from a computational point of view. Consider the above adiabatic algorithm for MIS. Recall that according to the adiabatic theorem, if the evolution is slow enough,

the system remains in the instantaneous ground state. Let $| \psi ( s ) \rangle$ be the ground state of $\mathcal { H } ( s )$ , for $s \in [ 0 , 1 ]$ . For a system of $n$ -qubits, $| \psi ( s ) \rangle$ is a superposition of $2 ^ { n }$ possible computational states, namely,

$$
| \psi ( s ) \rangle = \sum _ { x \in \{ 0 , 1 \} ^ { n } } \alpha _ { x } ( s ) | x \rangle , \qquad { \mathrm { w h e r e } } \quad \sum _ { x \in \{ 0 , 1 \} ^ { n } } | \alpha _ { x } ( s ) | ^ { 2 } = 1 .
$$

For example, we have the initial ground state $\begin{array} { r } { | \psi ( 0 ) \rangle = \frac { 1 } { \sqrt { 2 ^ { n } } } \sum _ { x \in \{ 0 , 1 \} ^ { n } } | x \rangle } \end{array}$ , which is uniform superposition of all $2 ^ { n }$ states, while the final ground state $| \psi ( 1 ) \rangle = | x _ { 1 } ^ { * } x _ { 2 } ^ { * } \ldots x _ { n } ^ { * } \rangle$ , corresponding to the solution state. A natural question is: what are the instantaneous ground states $| \psi ( s ) \rangle$ , for $0 < s < 1$ , like? In particular, we would like to “see” how the instantaneous ground state evolves? A naive solution would be to trace the $2 ^ { n }$ amplitudes $\alpha _ { x }$ . The task becomes unmanageable even for $n = 1 0$ , which has 1024 amplitudes, even thouhg many may be negligible (close to zero).

To make the “visualization” feasible, we introduce a new measure $\Gamma _ { k }$ . Suppose that $\mathcal { H } ( 1 )$ , has $( m + 1 ) \leq 2 ^ { n }$ distinct energy levels: $E _ { 0 } < E _ { 1 } < . . . < E _ { m }$ . For $0 \leq k \leq m$ , let $D _ { k } = \{ x \in \{ 0 , 1 \} ^ { n } : \mathcal { H } ( 1 ) | x \rangle = E _ { k } | x \rangle \}$ be the set of (degenerate) computational states that have the same energy level $E _ { k }$ (with respect to the problem Hamiltonian $\mathcal { H } ( 1 ) )$ , and define

$$
\Gamma _ { k } ( s ) = \sum _ { x \in D _ { k } } | \alpha _ { x } ( s ) | ^ { 2 } .
$$

In other words, $\Gamma _ { k } ( s )$ is the total percentage of (computational) states of the same energy level $E _ { k }$ participating in $| \psi ( s ) \rangle$ . The idea is now to trace $\Gamma _ { k }$ instead of $\alpha _ { x }$ . Here we remark that $\Gamma _ { k }$ are defined for any eigenstate $| \psi \rangle$ and not just for the ground state.

For our purpose, we constructed a special family of vertex-weighted graphs for the MIS problem, called CK graphs [7]. We designed the problem instances such that the global minimum is “hidden” in the sense that there are many local minima to mislead local search based algorithms. Note that the size of th smallest instances needs to be necessarily smaller than 20 as we are relying on the eigenvalue computation (or exact diagonization) to compute $\Gamma _ { k }$ .

CK Graph Construction. Let $r , g$ be integers, and $w _ { A }$ , $w _ { B }$ be positive rational numbers. Our graphs are specified by these four parameters. There are two types of vertices in the graph: vertices of a $2 g$ -independent set, denoted by $V _ { A }$ , and vertices of $\textit { g r }$ -cliques (which form $r ^ { g }$ maximal independent sets), denoted by $V _ { B }$ . The weight of vertex in $V _ { A }$ $\displaystyle { V _ { B } }$ resp.) is $w _ { A }$ ( $w _ { B }$ resp.). The connections between $V _ { A }$ and $V _ { B }$ : partition the $2 g$ vertices in $V _ { A }$ into $g$ groups of 2. Label the $g \ r .$ -cliques such that each group is adjacent to all but one (the same label) $r$ -cliques. Note if $w _ { B } < 2 w _ { A }$ , then we have $V _ { A }$ forming the (global) maximum independent sets of weight $2 g w _ { A }$ , while there are $r ^ { g }$ (local) maximal independent set of weight $g w _ { B }$ . See Figure 1 for an example of a graph for $r = 3$ and $g = 3$ .

# 4.1 DESEV for the MIS Adiabatic Algorithm on a 15-vertex CK Graph

In the section, we fix the CK graph with $r = 3$ , $g = 3$ as illustrated in Figure 1. We set $w _ { A } = 1$ , and consider $1 \le w _ { B } < 2$ . The graph $G$ consists of 15 vertices: $V _ { A } = \{ 1 , \ldots , 6 \}$ forms the maximum-weight independent set of weight 6; while $V _ { B }$ , consisting of 3 groups of 3 triangles: $\{ 7 , 8 , 9 \}$ , $\{ 1 0 , 1 1 , 1 2 \}$ , and $\{ 1 3 , 1 4 , 1 5 \}$ , forms $3 ^ { 3 }$ maximal independent sets of weight $3 w _ { B } < 6$ .

According to Eq.(3), the problem Hamiltonian (and thus the adiabatic algorithm) for MIS on $G$ is

$$
\mathcal { H } _ { 1 } = \sum _ { i \in V _ { A } } ( 6 J - 2 ) \sigma _ { i } ^ { z } + \sum _ { i \in V _ { B } } ( 6 J - 2 w _ { B } ) \sigma _ { i } ^ { z } + J \sum _ { i j \in \mathsf { E } ( G ) } \sigma _ { i } ^ { z } \sigma _ { j } ^ { z }
$$

Here we fix $J _ { i j } = J = 2 > w _ { B }$ for all $i j \in { \mathsf { E } } ( G )$ .

![](images/2452cb8433734d9ab183ab0cf9acdc2459203d562a3f565db5a7ad6ab48d102f.jpg)  
Figure 1: (a) A CK graph for $r = 3$ and $g = 3$ . The graph consists of 15 vertices: $V _ { A } = \{ 1 , \ldots , 6 \}$ forms an independent set of size 6, while $V _ { B }$ , consisting of $g ( = 3 )$ groups of $r ( = 3 )$ triangles: $\{ 7 , 8 , 9 \}$ , $\{ 1 0 , 1 1 , 1 2 \}$ , and $\{ 1 3 , 1 4 , 1 5 \}$ , forms $3 ^ { 3 }$ independent sets of size 3. The graph is connected as follows. The 6 vertices in $V _ { A }$ are divided into 3 groups: $\{ 1 , 2 \} , \{ 3 , 4 \}$ , and $\{ 5 , 6 \}$ . The vertices in each group are adjacent to vertices in two groups of three triangles in $V _ { B }$ (as illustrated by different colors). (b) The drawing of the graph with explicit connections. The weight of a vertex in $V _ { A }$ ( $\displaystyle V _ { B }$ resp.) is $w _ { A }$ ( $w _ { B }$ resp.). We set $w _ { A } = 1$ , and consider $1 \le w _ { B } < 2$ . For explanation purpose, we represent a vertex in $V _ { A }$ by a $\bullet$ , and a vertex in $V _ { B }$ by a $\triangle$ . Therefore, $V _ { A } = \{ \bullet , \bullet , \bullet , \bullet , \bullet , \bullet , \}$ , forms the MIS of weight 6; while $\{ \triangle , \triangle , \triangle \}$ is a maximal independent set of weight $3 w _ { B } ( < 6 )$ .

Notation on represent the computational states. For a computational state $\left| x _ { 1 } x _ { 2 } \ldots x _ { n } \right.$ where $x _ { i } \in \{ 0 , 1 \}$ , we adopt the zero position representation, namely, represent it by $| i _ { 1 } i _ { 2 } \dots i _ { k } \rangle$ where $x _ { j } = 0$ if and only if $j = i _ { t }$ for some $t$ . That is, we represent $\left| 0 0 0 0 0 0 1 1 1 1 1 1 1 1 \right.$ (the solution state) by |123456i. Further, we use a $\bullet$ to denote a vertex in $V _ { A }$ , a $\triangle$ for a vertex in $V _ { B }$ . That is, the solution state is now represented by $| \bullet \bullet \bullet \bullet \bullet \rangle$ , while $| \triangle \triangle \triangle \rangle$ , corresponding to a local maximal independent set of weight $3 w _ { B }$ with one vertex from each triangle.

Maximum vs Minimum. The maximum of MIS corresponds to the minimum of the Ising energy. For explanation purpose, instead of referring to the energy values of the Ising Hamiltonian, we will refer to the values of MIS given by the pseudo-boolean function $\mathcal { V }$ in Eq.(1) by “(-)energy”, where “ $- ( - ) ^ { , }$ is to indicate the reverse ordering.

Example. The (-)energy of $| \bullet \bullet \bullet \bullet \bullet \rangle$ is 6; while $| \triangle \triangle \triangle \triangle \rangle$ is $4 w _ { B } - J$ , where $\Delta t \Delta$ represents two connected vertices from $V _ { B }$ , e.g. vertex 7 and 8 in Figure 1.

See Figure 2 for the DESEV of the the ground state of the adiabatic algorithm with $\mathcal { H } _ { 1 }$ in Eq.(4) as the problem Hamiltonian for $w _ { B } = 1 . 5$ and 1.8.

# 4.2 FQPT and Perturbation Estimation

To gain better understanding, we vary the weights of vertices: fix $w _ { A } = 1$ , while varying $w _ { B }$ from 1 to 1.9 with a step size of 0.1. That is, we fix the global maximum independent set, while increasing the weight of the local maximum. As the weight of $w _ { B }$ increases, the minimum spectral gaps get smaller and smaller (indeed, from $1 0 ^ { - 1 }$ to $1 0 ^ { - 8 }$ as $w _ { B }$ changes from 1 to 1.9). See Table 2 in Appendix A.

This was consequently explained by the FQPT in [4]. By FQPT, here we mean that there is a level anticrossing between two states as illustrated in Figure 3. The minimum spectral gap $( g _ { \mathrm { m i n } } )$ and the position $( s ^ { * } )$ were then estimated based on the assumption of the level anti-crossing between the global minimum and the local minima using perturbation method. In particular, $g _ { \mathsf { m i n } }$ was estimated by the tunneling amplitude between the global minimum and the local minima. The formula so derived involves combinatorial enumeration of the all possible paths between local minima and the global minimum, and suggested $g _ { \mathrm { m i n } }$ is exponentially (in terms of the problem size) small. See also [2, 4, 14, 26] for more explanation on the FQPT and the level anti-crossing.

# 5 Varying Parameters in the Problem Hamiltonian for MIS

In this section, we show that by changing the parameters in the problem Hamiltonian for MIS on CK graphs, the FQPT no longer occurs and we can significantly increase $g _ { \mathsf { m i n } }$ .

Recall that in the pseudo-boolean formulation of MIS as in Theorem 3.1, the requirement for $J _ { i j }$ is at least $\operatorname* { m i n } \{ c _ { i } , c _ { j } \}$ , for each $i j ~ \in ~ { \mathsf { E } } ( G )$ . For simplicity, we consider the simplest case in which $J _ { i j } ~ = ~ J$ for all $i j \in { \mathsf { E } } ( G )$ . In other words, we have the corresponding problem Hamiltonian:

$$
\mathcal { H } _ { 1 } = \sum _ { i \in \mathsf { V } ( G ) } ( d _ { i } J - 2 c _ { i } ) \sigma _ { i } ^ { z } + \sum _ { i j \in \mathsf { E } ( G ) } J \sigma _ { i } ^ { z } \sigma _ { j } ^ { z }
$$

where $d _ { i }$ is the degree of vertex $i \in \mathsf { V } ( G )$ .

The natural question is how does the ART change when we vary $J ?$ Note that it is not sufficient to consider only the minimum spectral gap change (as almost all the other works on adiabatic quantum computation did) because by increasing $J$ , the maximum energy of the system Hamiltonian also increases. Instead, in order to keep the maximum energy of the system Hamiltonian comparable, we keep $J$ fixed and vary $c _ { i }$ instead, namely multiplying all weights $c _ { i }$ by a scaling factor, say $1 / k$ , for $k \geq 1$ , which does not change the original problem to be solved. We remark that this is equivalent to multiplying $J$ by $k$ , and then multiply the problem Hamiltonian by $( 1 / k )$ . The details and more general case can be found in [8].

That is, we consider the following (scaled) problem Hamiltonian

$$
\mathcal { H } _ { k } = \sum _ { i \in \mathsf { V } ( G ) } ( J d _ { i } - 2 c _ { i } / k ) \sigma _ { i } ^ { z } + \sum _ { i j \in \mathsf { E } ( G ) } J \sigma _ { i } ^ { z } \sigma _ { j } ^ { z }
$$

where $k \geq 1$ is the scaling factor.

# 5.1 Minimum Spectral Gap $g _ { \mathrm { m i n } }$ Without FQPT

The DESEV of $\mathcal { H } _ { 1 }$ and $\mathcal { H } _ { 1 0 }$ $k = 1 0 \AA$ ) is shown in Figure 4 and Figure 5. The anti-crossing between the global minimum and the local minima (for $k = 1 \AA$ ) no longer occurs for $k = 1 0$ , and $g _ { \mathsf { m i n } }$ increases from $1 . 0 4 \times 1 0 ^ { - 5 }$ to 0.145. Notice that the change in the lowest few excited energy levels: for $k = 1$ , the lowest few excited states (beyond the first excited state) of the problem Hamiltonian is mainly the superposition of states from $V _ { B }$ $( \triangle )$ (which constitutes the local minima); while these states of the scaled $k = 1 0 )$ ) problem Hamiltonian is mainly the superposition of states from $V _ { A } ( \bullet )$ (which constitutes the global minimum). The DESEV of $\mathcal { H } _ { k }$ for $k = 1 , 2 , 3 , 5 , 1 0 , 5 0$ is shown in Figure 6.

In [4], based on the FQPT assumption, we estimate $g _ { \mathrm { m i n } }$ (for $\mathcal { H } _ { 1 }$ ) by the tunneling amplitude between the local minima and the global minimum, which suggests that $g _ { \mathrm { m i n } }$ is exponentially small. However, for $k = 1 0$ , from our numerical data and DESEV in Figure 4, we see that the FQPT (that causes $g _ { \mathsf { m i n } }$ to be exponentially small) no longer occurs, and $g _ { \mathrm { m i n } }$ increases significantly (from $1 0 ^ { - 5 }$ to 0.145). This seems to suggest that $g _ { \mathrm { m i n } }$ to be polynomially small instead. We are currently investigating how to analytically bound or estimate $g _ { \mathrm { m i n } }$ of $\mathcal { H } _ { k }$ for a general CK graph of size $n$ . We remark here that the perturbation method is still valid (in fact, as we increase $k$ , we also increase the minimum spectral gap position $s ^ { * } \nsim 1$ (see [8] for the proof)), however we can no longer assume that $g _ { \mathrm { m i n } }$ can be approximated by the tunneling amplitude between the two (localized) states.

# 5.2 Scaling Factor and ART

In this section, we discuss what the good scaling factor should be, and how it affects the ART. To address this question, we need an appropriate formulation for ART. We point out that it is not sufficient to just consider $g _ { \mathrm { m i n } }$ , but the matrix element of the time derivative of the Hamiltonian also matters. In particular, we adopt the following three formulations, which are related to the widely used traditional condition:

$$
( * ) \left\{ \begin{array} { l l } { \mathsf { A R T } _ { 1 } ( \mathcal { H } ) = \frac { \operatorname* { m a x } _ { 0 \leq s \leq 1 } \mathcal { M } ( s ) } { g _ { \operatorname* { m i n } } ^ { 2 } } \operatorname* { m a x } _ { 0 \leq s \leq 1 } | | \mathcal { H } | | } \\ { \mathsf { A R T } _ { 2 } ( \mathcal { H } ) = \frac { \mathcal { M } ( s ^ { * } ) } { g _ { \operatorname* { m i n } } ^ { 2 } } \operatorname* { m a x } _ { 0 \leq s \leq 1 } | | \mathcal { H } | | , \mathrm { ~ w h e r e ~ } g _ { \operatorname* { m i n } } = E _ { 1 } ( s ^ { * } ) - E _ { 0 } ( s ^ { * } ) } \\ { \mathsf { A R T } _ { 3 } ( \mathcal { H } ) = \operatorname* { m a x } _ { 0 \leq s \leq 1 } \frac { \mathcal { M } ( s ) } { ( E _ { 1 } ( s ) - E _ { 0 } ( s ) ) ^ { 2 } } \operatorname* { m a x } _ { 0 \leq s \leq 1 } | | \mathcal { H } | | } \end{array} \right.
$$

where $\begin{array} { r } { \mathcal { M } ( s ) = | \langle E _ { 1 } ( s ) | \frac { d \mathcal { H } } { d s } | E _ { 0 } ( s ) \rangle | } \end{array}$ is the matrix element of the time derivative Hamiltonian at time $s$ , and $\begin{array} { r } { \mathcal { H } ( s ) \vert E _ { i } ( s ) \rangle = E _ { i } ( s ) \vert E _ { i } ( s ) \rangle } \end{array}$ . See Table 1 for the numerical comparisons.

From Table1, we see that $g _ { \mathrm { m i n } }$ increases as $k$ increases from 1 to 10, however, decreases from 10 to 50 (even though it is still much larger than $k = 1$ ). The latter, perhaps, can be explained by the following: as $k$ increases, the difference between the low energy levels decreases, and becomes dominate for $k > 1 0$ . We remark that the optimal value for $k$ seems to depend only on the vertex weights (for which $J$ depends on), and independ of the problem size. By increasing the scaling factor, we also increase the precision (or dynamic range) requirement for representing the parameters $h _ { i }$ & $J _ { i j }$ ) in the problem Hamiltonian, which is one of the important physical resources.

The three versions of ART look similar, and indeed they coincide for some Hamiltonians (e.g. for $k = 1 \AA$ ). However, they can be very different for the large $k$ . The main reason is that the matrix element $\mathcal M ( s )$ can be extremely small at the minimum spectral gap position $s ^ { * }$ . For example, for $k = 5 0 , s ^ { * }  1 , \mathcal { M } ( s ^ { * } )$ is extremely small. Note one can show that $\mathcal { M } ( s ) = \vert \langle E _ { 1 } ( s ) \vert \mathcal { H } _ { \mathrm { i n i t } } \vert E _ { 0 } ( s ) \vert / s$ for $s \in ( 0 , 1 ] ^ { 3 }$ . Thus, for our initial Hamiltonian, $\mathcal M ( s )$ measures the overlap of the states with one single bit flip, and in this case it is extremely small. Observe that the position of the minimum spectral gap $s ^ { * }$ is not the same as the position $s ^ { \prime }$ where $\frac { \mathcal { M } ( s ) } { g ( s ) ^ { 2 } }$ is maximized. What should be the appropriate formulation of ART? Should it be $\mathsf { A R T } _ { 3 } ?$ If so, under what condition, can $\mathsf { A R T } _ { 1 }$ be a good approximation to $\mathsf { A R T } _ { 3 } ?$ and under what condition, can we assume that $g _ { \mathrm { m i n } }$ is the dominating factor (as have been assumed by all other works)?

<table><tr><td rowspan=1 colspan=1>k</td><td rowspan=1 colspan=1>s</td><td rowspan=1 colspan=1>gmin</td><td rowspan=1 colspan=1>M(s*)</td><td rowspan=1 colspan=1>max0≤s≤1M(s)</td><td rowspan=1 colspan=1>max0≤s≤1|H||</td><td rowspan=1 colspan=1>ART2</td><td rowspan=1 colspan=1>ART1</td></tr><tr><td rowspan=1 colspan=1>1</td><td rowspan=1 colspan=1>0.62763727</td><td rowspan=1 colspan=1>1.04e-05</td><td rowspan=1 colspan=1>4.02e+00</td><td rowspan=1 colspan=1>4.02e+00</td><td rowspan=1 colspan=1>2.26e+02</td><td rowspan=1 colspan=1>8.34e+12</td><td rowspan=1 colspan=1>8.34e+12</td></tr><tr><td rowspan=1 colspan=1>2</td><td rowspan=1 colspan=1>0.54578285</td><td rowspan=1 colspan=1>6.37e-03</td><td rowspan=1 colspan=1>2.04e+00</td><td rowspan=1 colspan=1>1.69e+00</td><td rowspan=1 colspan=1>2.48e+02</td><td rowspan=1 colspan=1>1.24e+07</td><td rowspan=1 colspan=1>1.03e+07</td></tr><tr><td rowspan=1 colspan=1>3</td><td rowspan=1 colspan=1>0.54467568</td><td rowspan=1 colspan=1>3.30e-02</td><td rowspan=1 colspan=1>1.41e+00</td><td rowspan=1 colspan=1>1.01e+00</td><td rowspan=1 colspan=1>2.55e+02</td><td rowspan=1 colspan=1>3.32e+05</td><td rowspan=1 colspan=1>2.37e+05</td></tr><tr><td rowspan=1 colspan=1>4</td><td rowspan=1 colspan=1>0.55610853</td><td rowspan=1 colspan=1>6.83e-02</td><td rowspan=1 colspan=1>1.18e+00</td><td rowspan=1 colspan=1>1.18e+00</td><td rowspan=1 colspan=1>2.59e+02</td><td rowspan=1 colspan=1>6.57e+04</td><td rowspan=1 colspan=1>6.58e+04</td></tr><tr><td rowspan=1 colspan=1>5</td><td rowspan=1 colspan=1>0.57419149</td><td rowspan=1 colspan=1>9.67e-02</td><td rowspan=1 colspan=1>1.06e+00</td><td rowspan=1 colspan=1>1.07e+00</td><td rowspan=1 colspan=1>2.61e+02</td><td rowspan=1 colspan=1>2.96e+04</td><td rowspan=1 colspan=1>2.99e+04</td></tr><tr><td rowspan=1 colspan=1>10</td><td rowspan=1 colspan=1>0.66773072</td><td rowspan=1 colspan=1>1.45e-01</td><td rowspan=1 colspan=1>7.48e-01</td><td rowspan=1 colspan=1>7.92e-01</td><td rowspan=1 colspan=1>2.66e+02</td><td rowspan=1 colspan=1>9.45e+03</td><td rowspan=1 colspan=1>1.00e+04</td></tr><tr><td rowspan=1 colspan=1>20</td><td rowspan=1 colspan=1>0.80170240</td><td rowspan=1 colspan=1>1.30e-01</td><td rowspan=1 colspan=1>4.72e-01</td><td rowspan=1 colspan=1>5.68e-01</td><td rowspan=1 colspan=1>2.68e+02</td><td rowspan=1 colspan=1>7.48e+03</td><td rowspan=1 colspan=1>9.01e+03</td></tr><tr><td rowspan=1 colspan=1>30</td><td rowspan=1 colspan=1>0.99318624</td><td rowspan=1 colspan=1>7.97e-02</td><td rowspan=1 colspan=1>8.95e-09</td><td rowspan=1 colspan=1>4.26e-01</td><td rowspan=1 colspan=1>2.69e+02</td><td rowspan=1 colspan=1>3.78e-04</td><td rowspan=1 colspan=1>1.80e+04</td></tr><tr><td rowspan=1 colspan=1>40</td><td rowspan=1 colspan=1>0.99642154</td><td rowspan=1 colspan=1>5.99e-02</td><td rowspan=1 colspan=1>4.90e-10</td><td rowspan=1 colspan=1>4.35e-01</td><td rowspan=1 colspan=1>2.69e+02</td><td rowspan=1 colspan=1>3.67e-05</td><td rowspan=1 colspan=1>3.26e+04</td></tr><tr><td rowspan=1 colspan=1>50</td><td rowspan=1 colspan=1>0.99779592</td><td rowspan=1 colspan=1>4.79e-02</td><td rowspan=1 colspan=1>5.30e-11</td><td rowspan=1 colspan=1>4.41e-01</td><td rowspan=1 colspan=1>2.69e+02</td><td rowspan=1 colspan=1>6.20e-06</td><td rowspan=1 colspan=1>5.16e+04</td></tr></table>

<table><tr><td rowspan=1 colspan=1>k</td><td rowspan=1 colspan=1>s&#x27;′</td><td rowspan=1 colspan=1>g(s′)</td><td rowspan=1 colspan=1>M(s′)</td><td rowspan=1 colspan=1>M(s)g(s^)2}$</td><td rowspan=1 colspan=1>max0≤s≤1 ||||</td><td rowspan=1 colspan=1>ART3</td></tr><tr><td rowspan=1 colspan=1>1</td><td rowspan=1 colspan=1>0.62763727</td><td rowspan=1 colspan=1>1.04e-05</td><td rowspan=1 colspan=1>4.02e+00</td><td rowspan=1 colspan=1>3.70e+10</td><td rowspan=1 colspan=1>2.26e+02</td><td rowspan=1 colspan=1>8.34e+12</td></tr><tr><td rowspan=1 colspan=1>2</td><td rowspan=1 colspan=1>0.54578226</td><td rowspan=1 colspan=1>6.37e-03</td><td rowspan=1 colspan=1>2.04e+00</td><td rowspan=1 colspan=1>5.02e+04</td><td rowspan=1 colspan=1>2.48e+02</td><td rowspan=1 colspan=1>1.24e+07</td></tr><tr><td rowspan=1 colspan=1>3</td><td rowspan=1 colspan=1>0.54461081</td><td rowspan=1 colspan=1>3.30e-02</td><td rowspan=1 colspan=1>1.41e+00</td><td rowspan=1 colspan=1>1.30e+03</td><td rowspan=1 colspan=1>2.55e+02</td><td rowspan=1 colspan=1>3.32e+05</td></tr><tr><td rowspan=1 colspan=1>4</td><td rowspan=1 colspan=1>0.55545411</td><td rowspan=1 colspan=1>6.83e-02</td><td rowspan=1 colspan=1>1.18e+00</td><td rowspan=1 colspan=1>2.54e+02</td><td rowspan=1 colspan=1>2.59e+02</td><td rowspan=1 colspan=1>6.57e+04</td></tr><tr><td rowspan=1 colspan=1>5</td><td rowspan=1 colspan=1>0.57223394</td><td rowspan=1 colspan=1>9.68e-02</td><td rowspan=1 colspan=1>1.07e+00</td><td rowspan=1 colspan=1>1.14e+02</td><td rowspan=1 colspan=1>2.61e+02</td><td rowspan=1 colspan=1>2.97e+04</td></tr><tr><td rowspan=1 colspan=1>10</td><td rowspan=1 colspan=1>0.65682886</td><td rowspan=1 colspan=1>1.46e-01</td><td rowspan=1 colspan=1>7.75e-01</td><td rowspan=1 colspan=1>3.64e+01</td><td rowspan=1 colspan=1>2.66e+02</td><td rowspan=1 colspan=1>9.66e+03</td></tr><tr><td rowspan=1 colspan=1>20</td><td rowspan=1 colspan=1>0.77115481</td><td rowspan=1 colspan=1>1.33e-01</td><td rowspan=1 colspan=1>5.41e-01</td><td rowspan=1 colspan=1>3.08e+01</td><td rowspan=1 colspan=1>2.68e+02</td><td rowspan=1 colspan=1>8.24e+03</td></tr><tr><td rowspan=1 colspan=1>30</td><td rowspan=1 colspan=1>0.83962780</td><td rowspan=1 colspan=1>1.08e-01</td><td rowspan=1 colspan=1>4.43e-01</td><td rowspan=1 colspan=1>3.82e+01</td><td rowspan=1 colspan=1>2.69e+02</td><td rowspan=1 colspan=1>1.02e+04</td></tr><tr><td rowspan=1 colspan=1>40</td><td rowspan=1 colspan=1>0.88050519</td><td rowspan=1 colspan=1>8.82e-02</td><td rowspan=1 colspan=1>3.93e-01</td><td rowspan=1 colspan=1>5.05e+01</td><td rowspan=1 colspan=1>2.69e+02</td><td rowspan=1 colspan=1>1.36e+04</td></tr><tr><td rowspan=1 colspan=1>50</td><td rowspan=1 colspan=1>0.90581875</td><td rowspan=1 colspan=1>7.39e-02</td><td rowspan=1 colspan=1>3.63e-01</td><td rowspan=1 colspan=1>6.64e+01</td><td rowspan=1 colspan=1>2.69e+02</td><td rowspan=1 colspan=1>1.79e+04</td></tr></table>

where g(s) = E1(s) − E0(s), and s0 = arg max0≤s≤1 M(s)g(s)2 .

Table 1: $\mathsf { A R T } _ { 1 }$ , $\mathsf { A R T } _ { 2 }$ , $\mathsf { A R T } _ { 3 }$ for $\mathcal { H } _ { k }$ in Eq.(5). Observations: (1) $g _ { \mathrm { m i n } }$ increases as $k$ increases from 1 to 10, but decreases from 10 to 50. (2) $\mathsf { A R T } _ { 1 }$ , $\mathsf { A R T } _ { 2 }$ , and $\mathsf { A R T } _ { 3 }$ are close for $k < 5$ . (3) The matrix element $\boldsymbol { \mathcal { M } } ( \boldsymbol { s } ^ { * } )$ at the position of minimum spectral gap is extremely small for $k \geq 3 0$ . (4) For $k > 1 0$ , $s ^ { * }$ (the position of the minimum spectral gap) is different from s0, where s0 = arg max0≤s≤1 g(s)2 . Note that $\mathsf { A R T } _ { 1 }$ , and $\mathsf { A R T } _ { 3 }$ are close, in particular, they coincide for small $k < 5$ .

# 6 Adiabatic Algorithms for Exact Cover and 3SAT Based on the Reduction to MIS

In this section, we first recall the Exact Cover problem, and then explain the special case of Exact Cover as the positive-1-in-3SAT, also called EC3, for which the adiabatic algorithm was first proposed for. The problem Hamiltonian of the proposed adiabatic algorithm for EC3 or the general 3SAT (see, e.g., [14, 24]) is based on the cost function which computes the number of clauses violated. This form (i.e. clause-violation cost function) of problem Hamiltonian has been adopted (there are two slightly different forms) by all the existing work. In the following, we describe different problem Hamiltonians for Exact Cover and 3SAT that are based on the reduction to MIS. We then point out that the argument that the clause-violation cost function based problem Hamiltonian (and thus the adiabatic algorithm) for Exact Cover [2] has exponential small $g _ { \mathrm { m i n } }$ (and thus require exponential time) does not apply to the MIS reduction based problem Hamiltonian.

# 6.1 Exact Cover

Formally, the Exact Cover is as follows:

Input: A set of $m$ elements, $X = \{ c _ { 1 } , c _ { 2 } , \ldots , c _ { m } \}$ ; a family of $n$ subsets of $X$ $\mathbf { \bar { \Psi } } , S = \{ S _ { 1 } , S _ { 2 } , \ldots , S _ { n } \}$ where $S _ { i } \subset X$

Question: Is there a subset $I \subseteq \{ 1 , \ldots , n \}$ such that $\cup _ { i \in I } S _ { i } = X$ , where $S _ { i } \cap S _ { j } = \emptyset$ for $i \neq j \in I ?$ Here $\{ S _ { i } : i \in I \}$ is called an exact cover of $X$ .

Example. $X ~ = ~ \{ c _ { 1 } , c _ { 2 } , c _ { 3 } , c _ { 4 } , c _ { 5 } \}$ , and $\boldsymbol { \mathcal { S } } = \{ S _ { 1 } , S _ { 2 } , \ldots , S _ { 7 } \}$ , with $S _ { 1 } = \{ c _ { 1 } , c _ { 2 } , c _ { 4 } \}$ , $S _ { 2 } = \{ c _ { 1 } , c _ { 2 } , c _ { 5 } \}$ , ${ { S } _ { 3 } } = \{ { { c } _ { 1 } } , { { c } _ { 3 } } , { { c } _ { 4 } } \} , { { S } _ { 4 } } = \{ { { c } _ { 2 } } , { { c } _ { 3 } } \}$ , $S _ { 5 } = \{ c _ { 3 } \}$ , $S _ { 6 } = \{ c _ { 4 } , c _ { 5 } \}$ , $S _ { 7 } = \{ c _ { 5 } \}$ . Here $\{ S _ { 1 } , S _ { 5 } , S _ { 7 } \}$ is the exact cover of $X$ .

In particular, if we further restrict that each element $c _ { i } \in X$ appears exactly in three subsets. The problem is referred as EC3, which can then be polynomially reducible to the positive 1-in-3SAT problem:

$\mathrm { E C } 3 ~ \leq _ { P }$ positive 1-in-3SAT. Given an instance of EC3 with an $m$ -element set $X$ and $n$ subsets $S _ { 1 } , \ldots , S _ { n }$ , we construct a 3CNF boolean formula $\Psi ( x _ { 1 } , . ~ . ~ . , x _ { n } ) = C _ { 1 } \wedge . ~ . ~ . \wedge C _ { m }$ with $n$ variables and $m$ clauses. Associate each set $S _ { i }$ with a binary variable $x _ { i }$ . For each element $c _ { i } \in X$ , let $S _ { i _ { 1 } }$ , $S _ { i _ { 2 } }$ , $S _ { i _ { 3 } }$ be the three sets that consist of $c _ { i }$ . Define the corresponding clause $C _ { i } = x _ { i _ { 1 } } \vee x _ { i _ { 2 } } \vee x _ { i _ { 3 } }$ . Then if is clear that there is an exact cover to the original problem if and only if the formula $\Psi ( x _ { 1 } , \dots , x _ { n } ) = C _ { 1 } \wedge \dots \wedge C _ { m }$ is satisfiable in that there is exactly one variable in each clause is satisfied.

The cost function

$$
\mathcal { E } _ { \Psi } ( x _ { 1 } , \dots , x _ { n } ) = \sum _ { i = 1 } ^ { m } ( x _ { i _ { 1 } } + x _ { i _ { 2 } } + x _ { i _ { 3 } } - 1 ) ^ { 2 } .
$$

penalizes each violating clause. $\Psi$ is satisfiable if and only if the minimum of ${ \mathcal { E } } _ { \Psi }$ is zero (i.e. no violation). The corresponding problem Hamiltonian based on this penalty function as used by Altshuler et al.[2] (and Young et al. [26]) 4

$$
\mathcal { H } _ { A Y } = \sum _ { i \in \mathsf { V } ( G _ { \mathsf { E C } } ) } B _ { i } \sigma _ { i } ^ { z } + \sum _ { i j \in \mathsf { E } ( G _ { \mathsf { E C } } ) } I _ { i j } \sigma _ { i } ^ { z } \sigma _ { j } ^ { z }
$$

where $B _ { i }$ is the number of clauses that contains variable $x _ { i }$ , and $I _ { i j }$ is the number of clauses that contains both $x _ { i }$ and $x _ { j }$ , and ${ \mathsf { V } } ( G _ { \mathsf { E C } } ) = \{ 1 , \dots , n \}$ , and $\mathsf E ( G _ { \mathsf E \mathsf C } ) = \{ i j : x _ { i }$ and $x _ { j }$ appear in a clause. $\}$ .

Next, we show the polynomial reduction from Exact Cover to MIS:

Exact Cover $\le _ { P }$ MIS. Given an instance of Exact Cover with an $m$ -element set $X$ and $n$ subsets $S _ { 1 } , \ldots , S _ { n }$ , we construct a graph $G _ { M }$ with $n$ vertices, where vertex $i$ corresponds to the set $S _ { i }$ . The weight of vertex $i$ is the number of elements in $S _ { i }$ . There is an edge between two vertices if and only if $S _ { i }$ and $S _ { j }$ share a common element. Thus, there is an exact cover to the original problem if only if the weight of $\mathsf { m i s } ( G _ { M } )$ is $m$ .

For EC3, it is easy to see that $G _ { \mathsf { E C } }$ and $G _ { M }$ are exactly the same because there is one-one corresponding between the variable $x _ { i }$ and the set $S _ { i }$ $( \mathsf { V } ( G _ { \mathsf { E C } } ) = \mathsf { V } ( G _ { M } ) )$ , and $\cdot _ { x _ { i } }$ and $x _ { j }$ appear in a clause” is equivalent to “ $S _ { i }$ and $S _ { j }$ share a common element” $( \mathsf E ( G _ { \mathsf E \mathsf C } ) = \mathsf E ( G _ { M } ) )$ . Based on this reduction, we therefore have the

following problem Hamiltonian for the same problem:

$$
\mathcal { H } _ { C } = \sum _ { i \in \mathsf { V } ( G _ { \mathsf { E C } } ) } \left( \sum _ { j \in \mathsf { n b r } ( i ) } J _ { i j } - 2 B _ { i } / k \right) \sigma _ { i } ^ { z } + \sum _ { i j \in \mathsf { E } ( G _ { \mathsf { E C } } ) } J _ { i j } \sigma _ { i } ^ { z } \sigma _ { j } ^ { z }
$$

where $J _ { i j } > \operatorname* { m i n } \{ B _ { i } , B _ { j } \}$ , and $k \geq 1$

See Appendix A for an example on how to reduce EC3 (given as a 3SAT problem) to a MIS problem. As pointed out by Young [27], $\mathcal { H } _ { A Y }$ and $\mathcal { H } _ { C }$ are the same for the special case $J _ { i j } = 2 I _ { i j }$ . However, our model is much more general since the $J _ { i j }$ can take any values provided only that $J _ { i j } > \operatorname* { m i n } \{ B _ { i } , B _ { j } \}$ . Recall that $\begin{array} { r } { 2 B _ { i } = \sum _ { j \in \mathsf { n b r } ( i ) } I _ { i j } } \end{array}$ . In particular, for some $i j \in { \mathsf { E } } ( G )$ , $J _ { i j } > 2 I _ { i j }$ (e.g. $I _ { 2 3 } = 1$ but $J _ { 2 3 } > 3$ in the example of the Appendix).

In [2], Altshuler et al. claimed that the adiabatic quantum algorithm with problem Hamiltonian $\mathcal { H } _ { A Y }$ failed with high probability for randomly generated instances of EC3. They claimed that the correctness of their argument did not rely on the specific form of the problem Hamiltonian for Exact Cover, but only depended on the properties of the problem instance $B _ { i }$ and $I _ { i j }$ . However, our problem Hamiltonian $\mathcal { H } _ { C }$ challenges the generality of their claim. Their argument requires computing the energy difference $E _ { 1 2 } ( s )$ which depends on the energy function of the problem Hamiltonian. While the energy function for $\mathcal { H } _ { A Y }$ only depends on $B _ { i }$ and $I _ { i j }$ , the energy function for $\mathcal { H } _ { C }$ also depends on $J _ { i j }$ (and/or $k$ ) whose values have a range to choose 5.

We would like to emphasize here we point out that the argument in [2] does not carry over to this new adiabatic algorithm for the same problem (EC3). That means that we can not use their argument to claim that our new algorithm requires exponential time. Whether this algorithm requires polynomial or exponential time will require rigorous analytical analysis of the algorithm. In [26], Young et al. used QMC to show that $g _ { \mathrm { m i n } }$ of adiabatic algorithm based on the same problem Hamiltonian $\mathcal { H } _ { A Y }$ is exponentially small. It will be interesting to see the $g _ { \mathsf { m i n } }$ result (for the same set of instances) using this new problem Hamiltonian $\mathcal { H } _ { C }$ .

# 6.2 3SAT

Similarly, for 3SAT , there is a well-known reduction to MIS (which is one of the first NP-complete reductions, to show the NP-hardness of MIS) [15]. For completeness, here we recall the reduction:

3SAT $\le _ { P }$ MIS. Given a 3SAT instance $\Psi ( x _ { 1 } , \dots , x _ { n } ) = C _ { 1 } \wedge \dots \wedge C _ { m }$ with $n$ variables and $m$ clauses, we construct a (unweighted) graph $G _ { \mathsf { S A T } }$ as follows:

• For each clause $C _ { i } = y _ { i _ { 1 } } \vee y _ { i _ { 2 } } \vee y _ { i _ { 3 } }$ , we construct a triangle with three vertices labeled accordingly, i.e., with $y _ { i _ { 1 } } , y _ { i _ { 2 } } , y _ { i _ { 3 } }$ , where $y _ { j } \in \{ x _ { j } , \overline { { x _ { j } } } \}$ . Therefore, $G _ { \mathsf { S A T } }$ consists of $3 m$ vertices. • There is an edge between two vertices in different triangles if there labels are in conflict. That is, for $i \neq j$ , $i _ { s } j _ { t } \in \mathsf E ( G _ { \mathsf { S A T } } )$ if and only if $y _ { i _ { s } } = \overline { { y _ { j _ { t } } } }$ .

One can then show that $\Psi$ is satisfiable if and only if $G _ { \mathsf { S A T } }$ has a MIS of size $m$ . See e.g. [10] for an example.

# 7 Discussion

In this paper, we have shown that by changing the parameters in the problem Hamiltonian (without changing the problem to be solved) of the adiabatic algorithm for MIS on CK graphs, we prevent the FQPT, that causes the exponential small $g _ { \mathsf { m i n } }$ , from occurring and significantly increase $g _ { \mathsf { m i n } }$ . We do so by scaling the vertex-weight of the graph, namely, multiplying the weights of vertices by a scaling factor. In order to determine the best scaling factor, we raise the basic question about what the appropriate formulation of adiabatic running time should be.

We also describe adiabatic quantum algorithms for Exact Cover and 3SAT in which the problem Hamiltonians are based on the reduction to MIS. Notice that the reduction requires only the solution to be preserved, i.e. there is a polynomial time algorithm that maps the solution to the reduced problem to the solution to the original problem and vice versa (see e.g. [10]). In other words, the reduction might only preserves the solution (i.e. the ground state) and alter the energy levels of the problem Hamiltonian. As we demonstrate in our small examples, the minimum spectral gap can be increased drastically when the excited energy levels are changed. By definition, NP-complete problems can be polynomial reducible to each other. Different reduction gives rise to different problem Hamiltonians, and thus different adiabatic algorithms, for the same problem. At the risk of stating the obvious, it is not sufficient to conclude that a problem is hard for adiabatic quantum computation/optimization by showing that there exists an adiabatic quantum algorithm for the problem (e.g. for a particular problem Hamiltonian) that requires exponential time. There are three variable components, namely, initial Hamiltonian, problem Hamiltonian and evolution path, in order to specify an adiabatic algorithm. To prove that adiabatic quantum computation (optimization) fail to solve a particular problem in polynomial time, one requires to prove that no polynomial-time adiabatic (optimization) algorithms for the problem is possible, which is in general hard.

In [23, 24], van Dam et al. argued that adiabatic quantum optimization might be thought of as a kind of “quantum local search”, and in [24], they constructed a special family of 3SAT instances for which the (clauseviolation cost function based) adiabatic algorithm required exponential time6. Our CK graphs were designed to trap local search algorithms in the sense that there are many local minima to mislead the local search process. From DESEV on a 15-vertex CK graph, we see that indeed this is the case for $\mathcal { H } _ { 1 }$ and the adiabatic algorithm would require exponential time due to the exponential small $g _ { \mathsf { m i n } }$ caused by the FQPT or the level anti-crossing between the global minimum and the local minima. However, for $\mathcal { H } _ { k }$ (say $k = 1 0$ ), the FQPT no longer occurs and $g _ { \mathrm { m i n } }$ increases significantly, which might suggest the possibility of exponential speed-up over $\mathcal { H } _ { 1 }$ . It remains challenging on how to analytically bound $g _ { \mathsf { m i n } }$ and/or ART of the adiabatic algorithm for $\mathcal { H } _ { k }$ on general CK graphs.

# 8 Acknowledgments

I would like to thank my very enthusiastic students in my adiabatic quantum computing class: Ryan Blace, Russell Brasser, Mark Everline, Eric Franklin, Nabil Al Ramli, and Aiman Shabsigh, who also helped to name DESEV. I would like to thank Siyuan Han and Peter Young for their comments. Thanks also go to David Sankoff and David Kirkpatrick for the encouragment.

![](images/82e14ef35832075f1e3cf7650883838bc402dc4a3789725c914245f82df0fb6b.jpg)

Figure 2: DESEV (only the 7 lowest energy levels shown) of the ground state of the MIS adiabatic algorithm with $\mathcal { H } _ { 1 }$ in Eq.(4) as the problem Hamiltonian for $w _ { B } = 1 . 5$ (left) and $w _ { B } = 1 . 8$ (right). The $\mathbf { X }$ -axis is the time $s$ . The y-axis is the (-)energy level. Each color corresponds to an energy level. The correspondence between (-)energy levels and the states are shown. The z-axis is $\Gamma$ . As time $s$ increases, one can see how $\Gamma$ of each energy level evolves to get some sense of the evolution. For example, for $w _ { B } = 1 . 5$ (left), for the (-)energy level 6 (which corresponds to the solution state), shown in brown, $\Gamma$ changes from almost 0 at $s = 0 . 2$ , to more than 0.4 at $s = 0 . 4$ , to almost 1.0 at $s = 0 . 8$ . For $w _ { B } = 1 . 8$ (right), $\Gamma$ of (-) energy level 6 changes from almost 0 before $s = 0 . 6$ to more than 0.9 at $s = 0 . 7$ ; while $\Gamma$ of (-) energy level 5.4, which corresponds to the local minima, gradually increases from $s = 0$ to 0.6, but almost 0 after $s = 0 . 6$ .

![](images/c09b1ee56770f32445f90b7063e9c147f3b1e1457eef8201dc74b8936ac6cc47.jpg)  
Figure 3: DESEV of the ground state and the first excited state of the MIS adiabatic algorithm with $\mathcal { H } _ { 1 }$ in (4) as the problem Hamiltonian for $w _ { B } = 1 . 8$ (a) $s = 0 \dots 1$ ; (b) Zoom in $s = 0 . 6 2 7 \ldots 0 . 6 2 8$ ; (c) The lowest two energy levels of $\mathcal { H } ( s )$ , $s = 0 \dots 1$ . The inset illustrates a level anti-crossing between two states $| B \rangle$ and $| A \rangle$ , or the system has a FQPT from $| B \rangle$ to $| A \rangle$ at the anti-crossing $s ^ { * }$ . In this example, $| A \rangle = | \bullet \bullet \bullet \bullet \bullet \rangle + | \bullet \bullet \bullet \bullet \rangle$ and $| B \rangle = | \triangle \triangle \triangle \triangle \rangle + | \triangle \triangle \triangle \rangle + | \triangle \triangle \triangle \rangle$ .

![](images/0695df1ef7d0c11c6f703507c87a3436c7589ece7bb7a7af81d4f3f02dd0ed3c.jpg)  
Figure 4: DESEV of the ground state and the first excited state of the MIS adiabatic algorithm with problem Hamiltonian $\mathcal { H } _ { 1 }$ (left) and $\mathcal { H } _ { 1 0 }$ (right) where $w _ { B } = 1 . 8$ . Notice the differences in the lowest few excited states. For $k = 1$ , the $2 n d$ and $3 r d$ excited states are superpositions of $\triangle \mathsf { s }$ (vertex in $V _ { B }$ which constitutes the local optima); while for $k = 1 0$ , the $2 n d$ and $3 r d$ excited states are superpositions of $\bullet \mathbf { S }$ (vertex in $V _ { A }$ which constitutes the global optimum). As a result, the first order phase transition from local minima to global minimum occurs for $k = 1$ , which results in the $g _ { \mathsf { m i n } } = 1 . 0 4 \times 1 0 ^ { - 5 }$ at $s ^ { * } = 0 . 6 2 7$ . For $k = 1 0$ , such crossing no longer occurs, and $g _ { \mathrm { m i n } } = 0 . 1 4 5$ at $s ^ { * } = 0 . 6 6 7$ . See Figure 5 for the zoom-in.

$$
k = 1 ( s : 0 . 6 2 7 \dots 0 . 6 2 8 )
$$

![](images/09c2eeae5476252e45b23337ab24b483673945393cdce1e246debf79ce7b1c73.jpg)  
Figure 5: Zoom around $s ^ { * }$ .

![](images/7c2f2b141b4c31938a0951c50e3f30965aa6a1e8962f98ba2fd0c756f8348e2d.jpg)

$$
\begin{array} { r l r l r l r l r l r l } { k = 1 } & { } & { 3 . 8 } & & { } & { 4 } & { \bullet \bullet \bullet \bullet } & { } & { \{ 3 . 8 }  & { } & { \cdots \bullet \bullet \bullet \bullet } & { } & { \{ 2 . 8 \triangle \triangle \triangle \triangle \rangle }  & & { \times 2 } & { } & { 5 4 } \\ & { } & { 1 . 6 \bullet \triangle \rangle } & & { } & { | \triangle \bullet \bullet \bullet \bullet \quad } & & { } & { | \triangle \bullet \bullet \bullet \bullet \circ \triangle \rangle } & & { } & { | \triangle \triangle \triangle \rangle } & & { | \triangle \triangle \rangle } & { } & { | \bullet \bullet \bullet \bullet \bullet \bullet \bullet } \\ { k = 2 } & { } & { } & { 1 . 8 } & & { } & { 1 . 9 } & & { } & { 2 } & { . 5 } & { } & { 2 . 7 } & { } & { 3 } & { } & { 3 } \\ & { } & { | \triangle \triangle \rangle } & & { } & { | \triangle \triangle \rangle } & & { } & { | \bullet \bullet \bullet \bullet \bullet } & & { } & { | \triangle \bullet \bullet \bullet \bullet \bullet \bullet } & { } & { | \triangle \triangle \triangle \rangle } & { } & { | \bullet \bullet \bullet \bullet \bullet \bullet \bullet } \\ { k \geq 3 } & { } & { } & { 3 . 6 / k } & & { } & { 3 . 8 / k } & & { } & { 4 / k } & { } & { 1 7 } & { } & { 5 . 7 k } & { } & { } & { 5 . 4 / k } & { } & { 6 / k } \\ & { } & { | \bullet \bullet \bullet \rangle } & & { } & { | \triangle \triangle \rangle } & & { } & { | \bullet \bullet \triangle \rangle } & & { } & { | \bullet \bullet \bullet \bullet \bullet \bullet \quad } & { | \triangle \bullet \bullet \bullet \bullet \bullet \rangle } \end{array}
$$

Figure 6: DESEV of the ground state and the first excited state of the adiabatic algorithm with problem Hamiltonian $\mathcal { H } _ { k }$ for $w _ { B } = 1 . 8$ , where $k = 1 , 2 , 3 , 5 , 1 0 , 5 0$ .

# References

[1] D. Aharonov, W. van Dam, J. Kempe, Z. Landau, S. Lloyd, and O. Regev. Adiabatic quantum computation is equivalent to standard quantum computation. SIAM Journal of Computing, Vol. 37, Issue 1, p. 166–194 (2007), conference version in Proc. 45th FOCS, p. 42–51 (2004).   
[2] B. Altshuler, H. Krovi and J. Roland. Adiabatic quantum optimization fails for random instances of NPcomplete problems. arXiv:quant-ph/0908.2782, 2009. Anderson localization casts clouds over adiabatic quantum optimization. arXiv:quant-ph/0912.0746, 2009.   
[3] A. Ambainis and O. Regev. An elementary proof of the quantum adiabatic theorem. arXiv:quantph/0411152.   
[4] M.H.S. Amin, V. Choi. First order phase transition in adiabatic quantum computation. arXiv:quantph/0904.1387, 2009. Phys. Rev. A., 80(6), 2009.   
[5] A.M. Childs, E. Farhi, J. Goldstone and S. Gutmann. Finding cliques by quantum adiabatic evolution. Quantum Information and Computation, 2, 181, 2002.   
[6] V. Choi. Minor-embedding in adiabatic quantum computation: I. The parameter setting problem. Quantum Inf. Processing., 7, 193–209, 2008. Available at arXiv:quant-ph/0804.4884.   
[7] V. Choi, D. Kirkpatrick. On the Construction of Hard Instances for the Maximum-Weight Independent Set Problem. . Manuscipt. 2008.   
[8] V. Choi. Scaling, Precision and Adiabatic Running Time. In preparation.   
[9] V. Choi. An Adiabatic Quantum Computation Primer. In preparation.   
[10] S. Dasgupta, C. Papadimitriou, U. Vazirani. Algorihtms. McGraw Hill, 2008.   
[11] E. Farhi, J. Goldstone, S. Gutmann, and M. Sipser. Quantum computation by adiabatic evolution. arXiv:quant-ph/0001106, 2000.   
[12] E. Farhi, J. Goldstone, S. Gutmann, J. Lapan, A. Lundgren, and D. Preda. A quantum adiabatic evolution algorithm applied to random instances of an NP-complete problem. Science, 292(5516):472–476, 2001.   
[13] E. Farhi, J. Goldstone and S. Gutmann. Quantum adiabatic evolution algorithms with different paths. arXiv.org:quant-ph/0208135, 2002.   
[14] E. Farhi, J. Goldstone, D. Gosset, S. Gutmann, H. B. Meyer and P. Shor. Quantum adiabatic algorithms, small gaps, and different paths. arXiv.org:quant-ph/0909.4766, 2009.   
[15] M. R. Garey and D. S. Johnson. Computers and Intractability: A Guide to the Theory of NP-Completeness. W. H. Freeman, 1979.   
[16] T. Hogg. Adiabatic quantum computing for random satisfiability problems. Phys. Rev. A 67, 022314, 2003.   
[17] S.P. Jordan, E. Farhi, P.W. Shor. Error-correcting codes for adiabatic quantum computation. Phys. Rev. A., 74, 052322, 2006.   
[18] T. Jorg, F. Krzakala, G. Semerjian, and F. Zamponi. First-order transitions for random optimization problems in a transverse field. arXiv.org:quant-ph/0911.3438, 2009.   
[19] T. Jorg, F. Krzakala, J. Kurchan, A.C. Maggs and J. Pujos. Energy gaps in quantum first-order mean-fieldlike transitions:The problems that quantum annealing cannot solve. arXiv.org:quant-ph/0912.4865, 2009.   
[20] B.W. Reichardt. The quantum adiabatic optimization algorithm and local minima. Proc. 35th STOC, 502– 510, 2004.   
[21] G. Schaller and R. Schutzhold. The role of symmetries in adiabatic quantum algorithms. arXiv:quant- ¨ ph/0708.1882, 2007.   
[22] P.W. Shor. Algorithms for quantum computation: discrete logs and factoring. Proc. 35th FOCS, (1994); SIAM J. Comp., 26, 1484–1509, 1997.   
[23] W. van Dam, M. Mosca, and U. Vazirani. How powerful is adiabatic quantum computation? Proc. 42nd FOCS, 279–287, 2001.   
[24] W. van Dam and U. Vazirani. Limits on quantum adiabatic optimization. Unpublished, 2001.   
[25] A.P. Young, S. Knysh, and V.N. Smelyanskiy. Size dependence of the minimum excitation gap in the quantum adiabatic algorithm. Phys. Rev. Lett., 101, 170503, 2008.   
[26] A. P. Young and S. Knysh and V. N. Smelyanskiy. First order phase transition in the Quantum Adiabatic Algorithm. arXiv:quant-ph/0910.1378, 2009. Phys. Rev. Lett., 2009.   
[27] A. P. Young. Private Communication.   
[28] M. Znidaric. Scaling of running time of quantum adiabatic algorithm for propositional satisfiability. Phys. Rev. A, 71, 062305, 2005.

SOME RECENT REFERENCES ON ADIABATIC THEOREM

[29] M.H.S. Amin. On the inconsistency of the adiabatic theorem. arXiv:quant-ph/0810.4335, 2008. Phys. Rev. Lett. 102, 220401, 2009.   
[30] D. Comparat. General conditions for quantum adiabatic evolution. Phys. Rev. A, 80, 012106, 2009.   
[31] V.I. Yukalov. Adiabatic theorems for linear and nonlinear Hamiltonians. Phys. Rev. A, 79, 052117, 2009.   
[32] J. Du and L. Hu and Y. Wang and J. Wu and M. Zhao and D. Suter. Is the quantum adiabatic theorem consistent? arXiv:quant-ph/0810.0361, 2008.   
[33] J. Goldstone. Adiabatic Theorem. Appendix F. S. Jordan’s PhD Thesis. arXiv:quant-ph/0809.2307, 2008.   
[34] D.A. Lidar and A.T. Rezakhani and A. Hamma. Adiabatic approximation with exponential accuracy for many-body systems and quantum computation. arXiv:quant-ph/0808.2697, 2008.   
[35] D.M. Tong, K. Singh, L.C. Kwek, and C.H. Oh. Sufficiency Criterion for the Validity of the Adiabatic Approximation. Phys. Rev. Lett. 98, 150402, 2007.   
[36] Z. Wei and M. Ying. Quantum adiabatic computation and adiabatic conditions. Phys. Rev. A, 76, 024304, 2007.   
[37] Y. Zhao. Reexamination of the quantum adiabatic theorem. Phys. Rev. A, 76, 032109, 2008.   
[38] R. MacKenzie, A. Morin-Duchesne, H. Paquette, and J. Pinel. Validity of the adiabatic approximation in quantum mechanics. Phys. Rev. A, 76, 044102, 2007.   
[39] S. Jansen, R. Seiler and M.B. Ruskai. Bounds for the adiabatic approximation with applications to quantum computation. Journal of Mathematical Physics, 48, 102111, 2007. Available at arXiv:quant-ph/0603175.

# Appendix A.

Example: $\operatorname { E C } 3 \ \leq _ { P }$ MIS. Let $\Psi ( x _ { 1 } , \dots , x _ { 7 } ) = C _ { 1 } \wedge C _ { 2 } \wedge C _ { 3 } \wedge C _ { 4 } \wedge C _ { 5 }$ be an instance of EC3 with 7 variables and 5 clauses:

$$
C _ { 1 } = x _ { 1 } \vee x _ { 2 } \vee x _ { 3 } , C _ { 2 } = x _ { 1 } \vee x _ { 2 } \vee x _ { 4 } , C _ { 3 } = x _ { 3 } \vee x _ { 4 } \vee x _ { 5 } , C _ { 4 } = x _ { 1 } \vee x _ { 3 } \vee x _ { 6 } , C _ { 5 } = x _ { 2 } \vee x _ { 3 } .
$$

For each variable $x _ { i }$ , let $S _ { i }$ be the set consisting of all clauses in which $x _ { i }$ appears. That is, we have

$$
\begin{array} { l } { { S _ { 1 } = \{ C _ { 1 } , C _ { 2 } , C _ { 4 } \} , S _ { 2 } = \{ C _ { 1 } , C _ { 2 } , C _ { 5 } \} , S _ { 3 } = \{ C _ { 1 } , C _ { 3 } , C _ { 4 } \} } } \\ { { \ } } \\ { { S _ { 4 } = \{ C _ { 2 } , C _ { 3 } \} , S _ { 5 } = \{ C _ { 3 } \} , S _ { 6 } = \{ C _ { 4 } , C _ { 5 } \} , S _ { 7 } = \{ C _ { 5 } \} } } \end{array}
$$

Construct the graph $G _ { \mathsf { E C } }$ as follows:

• $\mathsf { V } ( G _ { \mathsf { E C } } ) = \{ 1 , 2 , \dots , 7 \}$ , where vertex $i$ corresponds to the set $S _ { i }$ , and the weight of vertex $i$ is the number of elements in $S _ { i } \ ( = B _ { i } )$ ;   
• $\mathsf E ( G _ { \mathsf E \mathsf C } ) = \{ i j : S _ { i }$ and $S _ { j }$ share a common clause $\}$ .

See Figure 7. It is easy to see that $G _ { \mathsf { E C } }$ has a MIS of weight 5 if only if $\Psi$ is satisfiable (in positive 1-in-3SAT sense).

![](images/f866b04b4a2f97a249b455c77828e509b5d8549bfce2c0e2a63f1ee86999e3d8.jpg)

Figure 7: The number next to the vertex is the weight of the vertex. $\mathsf { m i s } ( G _ { \mathsf { E C } } ) = \{ 1 , 5 , 7 \}$ , with weight 5.

<table><tr><td rowspan=1 colspan=1>wB</td><td rowspan=1 colspan=1>$</td><td rowspan=1 colspan=1>gmin</td></tr><tr><td rowspan=1 colspan=1>1.0</td><td rowspan=1 colspan=1>0.2368</td><td rowspan=1 colspan=1>5.23e-01</td></tr><tr><td rowspan=1 colspan=1>1.1</td><td rowspan=1 colspan=1>0.2517</td><td rowspan=1 colspan=1>4.12e-01</td></tr><tr><td rowspan=1 colspan=1>1.2</td><td rowspan=1 colspan=1>0.2708</td><td rowspan=1 colspan=1>2.90e-01</td></tr><tr><td rowspan=1 colspan=1>1.3</td><td rowspan=1 colspan=1>0.2964</td><td rowspan=1 colspan=1>1.68e-01</td></tr><tr><td rowspan=1 colspan=1>1.4</td><td rowspan=1 colspan=1>0.3323</td><td rowspan=1 colspan=1>7.14e-02</td></tr><tr><td rowspan=1 colspan=1>1.5</td><td rowspan=1 colspan=1>0.3805</td><td rowspan=1 colspan=1>2.04e-02</td></tr><tr><td rowspan=1 colspan=1>1.6</td><td rowspan=1 colspan=1>0.4422</td><td rowspan=1 colspan=1>3.63e-03</td></tr><tr><td rowspan=1 colspan=1>1.7</td><td rowspan=1 colspan=1>0.5217</td><td rowspan=1 colspan=1>3.39e-04</td></tr><tr><td rowspan=1 colspan=1>1.8</td><td rowspan=1 colspan=1>0.6276</td><td rowspan=1 colspan=1>1.04e-05</td></tr><tr><td rowspan=1 colspan=1>1.9</td><td rowspan=1 colspan=1>0.7758</td><td rowspan=1 colspan=1>4.14e-08</td></tr></table>

Table 2: The minimum spectral gap $g _ { \mathrm { m i n } }$ (and position $s ^ { * }$ ) changes as $w _ { B }$ changes from 1 to 1.9, for the (unscaled) problem Hamiltonian $\mathcal { H } _ { 1 }$ in Eq.(4).