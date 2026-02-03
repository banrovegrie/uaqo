# Ising formulations of many NP problems

Andrew Lucas Department of Physics, Harvard University, Cambridge, MA, USA 02138

We provide Ising formulations for many NP-complete and NP-hard problems, including all of Karp’s 21 NP-complete problems. This collects and extends mappings to the Ising model from partitioning, covering and satisfiability. In each case, the required number of spins is at most cubic in the size of the problem. This work may be useful in designing adiabatic quantum optimization algorithms.

lucas@fas.harvard.edu

# Contents

# 1 Introduction 2

1.1 Quantum Adiabatic Optimization .   
1.2 Ising Spin Glasses   
1.3 The Goal of This Paper   
1.4 What Problems Are Easy (to Embed) on Experimental AQO Devices? 4

# 2 Partitioning Problems 5

# 2.1 Number Partitioning . 5

2.22.3 Graph Partitioning Cliques . . . . . . 67   
2.4 Reducing $N$ to $\log N$ Spins in Some Constraints 8

# 3 Binary Integer Linear Programming 9

# 4 Covering and Packing Problems 10

4.1 Exact Cover . 10   
4.2 Set Packing 11   
4.3 Vertex Cover 11   
4.4 Satisfiability . 1212   
4.5 Minimal Maximal Matching . .

# 5 Problems with Inequalities 13

5.1 Set Cover 14   
5.2 Knapsack with Integer Weights . . . 14

# 6 Coloring Problems 15

6.1 Graph Coloring . . 15   
6.2 Clique Cover 16   
6.3 Job Sequencing with Integer Lengths 16

# 7 Hamiltonian Cycles 17

7.1 Hamiltonian Cycles and Paths 17   
7.2 Traveling Salesman . 17

# 8 Tree Problems 18

8.1 Minimal Spanning Tree with a Maximal Degree Constraint 18   
8.2 Steiner Trees 19   
8.3 Directed Feedback Vertex Set . 20   
8.4 Undirected Feedback Vertex Set . 20   
8.5 Feedback Edge Set 21

# 9 Graph Isomorphisms 22

# 10 Conclusions 22

References 24

# 1. Introduction

# 1.1. Quantum Adiabatic Optimization

Recently, there has been much interest in the possibility of using adiabatic quantum optimization (AQO) to solve NP-complete and NP-hard problems [1, 2].1 This is due to the following trick: suppose we have a quantum Hamiltonian $H _ { \mathrm { P } }$ whose ground state encodes the solution to a problem of interest, and another Hamiltonian $H _ { 0 }$ , whose ground state is “easy” (both to find and to prepare in an experimental setup). Then, if we prepare a quantum system to be in the ground state of $H _ { 0 }$ , and then adiabatically change the Hamiltonian for a time $T$ according to

$$
H ( t ) = \left( 1 - \frac { t } { T } \right) H _ { 0 } + \frac { t } { T } H _ { \mathrm { P } } ,
$$

then if $T$ is large enough, and $H _ { 0 }$ and $H _ { \mathrm { P } }$ do not commute, the quantum system will remain in the ground state for all times, by the adiabatic theorem of quantum mechanics. At time $T$ , measuring the quantum state will return a solution of our problem.

There has been debate about whether or not these algorithms would actually be useful: i.e., whether an adiabatic quantum optimizer would run any faster than classical algorithms [3, 4, 5, 6, 7, 8, 9], due to the fact that if the problem has size $N$ , one typically finds

$$
T = 0 \left[ \exp \left( \alpha N ^ { \beta } \right) \right] ,
$$

in order for the system to remain in the ground state, for positive coefficients $\alpha$ and $\beta$ , as $N \to \infty$ . This is a consequence of the requirement that exponentially small energy gaps between the ground state of $H ( t )$ and the first excited state, at some intermediate time, not lead to Landau-Zener transitions into excited states [5].2 While it is unlikely that NP-complete problems can be solved in polynomial time by AQO, the coefficients $\alpha , \beta$ may be smaller than known classical algorithms, so there is still a possibility that an AQO algorithm may be more efficient than classical algorithms, on some classes of problems.

There has been substantial experimental progress towards building a device capable of running such algorithms [11, 12, 13], when the Hamiltonian $H _ { \mathrm { P } }$ may be written as the quantum version of an Ising spin glass. A classical Ising model can be written as a quadratic function of a set of $N$ spins $s _ { i } = \pm 1$ :

$$
H \left( s _ { 1 } , \ldots , s _ { N } \right) = - \sum _ { i < j } J _ { i j } s _ { i } s _ { j } - \sum _ { i = 1 } ^ { N } h _ { i } s _ { i } .
$$

The quantum version of this Hamiltonian is simply

$$
H _ { \mathrm { P } } = H \left( \sigma _ { 1 } ^ { z } , \dots , \sigma _ { N } ^ { z } \right)
$$

where $\boldsymbol { \sigma } _ { i } ^ { z }$ is a Pauli matrix (a $2 \times 2$ matrix, whose cousin $( 1 + \sigma _ { i } ^ { z } ) / 2$ has eigenvectors $| 0 , 1 \rangle$ with eigenvalues $0 , 1 )$ acting on the $i ^ { \mathrm { t h } }$ qubit in a Hilbert space of $N$ qubits $\{ | + \rangle , | - \rangle \} ^ { \otimes N }$ , and $J _ { i j }$ and $h _ { i }$ are real numbers. We then choose $H _ { 0 }$ to consist of transverse magnetic fields [11]:

$$
H _ { 0 } = - h _ { 0 } \sum _ { i = 1 } ^ { N } \sigma _ { i } ^ { x } ,
$$

so that the ground state of $H _ { 0 }$ is an equal superposition of all possible states in the eigenbasis of $H _ { \mathrm { P } }$ (equivalent to the eigenbasis of the set of operators $\sigma _ { i } ^ { z }$ ( $i = 1 , \ldots , N )$ ). This means that one does not expect any level crossings.3 For more work discussing the choice of $H$ , see [14]. Also, note that this class of Hamiltonians is not believed to be sufficient to build a universal adiabatic quantum computer [15] – at all times, $H ( t )$ belongs to a special class of Hamiltonians called stoquastic Hamiltonians [16].

# 1.2. Ising Spin Glasses

Ising spin glasses4 are known to be NP-hard problems for classical computers [17], so it is natural to suspect intimate connections with all other NP problems. For the purposes of this paper, an NP-complete problem is always a decision problem with a yes or no answer (does the ground state of $H$ have energy $\leq 0 !$ ), whereas an NP-hard problem is an optimization problem (what is the ground state energy of $H ?$ ). The class of NP-complete problems includes a variety of notoriously hard problems, and has thus attracted much interest over the last 40 years [18, 19]. Mathematically, because the decision form of the Ising model is NP-complete, there exists a polynomial time mapping to any other NP-complete problem.

Analogies between the statistical physics of Ising spin glasses and NP problems have been frequently studied in the past [20, 21, 22], and have been used to construct simulated annealing algorithms [23 which have been quite fruitful in approximate algorithms for problems on classical computers. These connections have suggested a physical understanding of the emergence of hardness in these problems via a complex energy landscape with many local minima [24]. Conversely, computational hardness of solving glassy problems has implications for the difficulty of the solutions to important scientific problems ranging from polymer folding [25, 26] to memory [27] to collective decision making in economics and social sciences [28, 29]. Problems of practical scientific interest have already been encoded and solved (in simple instances) on experimental devices using Ising Hamiltonians [30, 31, 32, 33, 34, 35].

Finally, we note that Ising glasses often go by the name QUBO (quadratic unconstrained binary optimization), in the more mathematical literature [36, 37]. Useful tricks have been developed to fix the values of some spins immediately [38] and to decompose large QUBO problems into smaller ones [39].

# 1.3. The Goal of This Paper

Mathematically, the fact that a problem is NP-complete means we can find a mapping to the decision form of the Ising model with a polynomial number of steps. This mapping can be re-interpreted as a pseudo-Boolean optimization problem [37]. As the constructions of these pseudo-Boolean optimization problems (or $^ { 6 6 } p$ -spin glasses”) often lead to three-body or higher interactions in $H$ (e.g., terms of the form $s _ { 1 } s _ { 2 } s _ { 3 }$ ), we then conclude by using “gadgets” to reduce the problem to an Ising spin glass, by introducing a polynomial number of auxiliary spins which help to enforce the three-body interaction by multiple two-body interactions $\left( s _ { 1 } s _ { 2 } \right)$ [40, 41]. As such, we can get from any NP-complete problem to the Hamiltonian of an Ising spin glass, whose decision problem (does the ground state have energy $\leq 0 !$ ) solves the NP-complete problem of interest. Classical gadgets are useful for many problems in physics as the physical energy (Hamiltonian) contains three-body interactions, but they are also useful for writing down many algorithms in other fields (e.g. integer factorization [42]).

However, for generic problems, this is a very inefficient procedure, as the power of the polynomial can grow quite rapidly. As such, the typical NP-complete problem (of size $N$ ) studied in the context of Ising glasses is very straightforward to write as a glass with $N$ spins (such as number partitioning, or satisfiability). The primary purpose of this paper is to present constructions of Ising Hamiltonians for problems where finding a choice of Hamiltonian is a bit subtle; for pedagogical purposes, we will also provide a review of some of the simple maps from partitioning and satisfiability to an Ising spin glass. In particular, we will describe how “all of the famous NP problems”5 [18, 19] can be written down as Ising models with a polynomial number of spins which scales no faster than $N ^ { 3 }$ . For most of this paper, we will find it no more difficult to solve the NP-hard optimization problem vs. the NP-complete decision problem, and as such we will usually focus on the optimization problems. The techniques employed in this paper, which are rare elsewhere in the quantum computation literature, are primarily of a few flavors, which roughly correspond to the tackling the following issues: minimax optimization problems, problems with inequalities as constraints (for example, $n \geq 1$ , as opposed to $n = 1$ ), and problems which ask global questions about graphs. The methods we use to phrase these problems as Ising glasses generalize very naturally.

# 1.4. What Problems Are Easy (to Embed) on Experimental AQO Devices?

We hope that the reader may be inspired, after reading this paper, to think about solving some of these classical computing problems, or others like them, on experimental devices implementing AQO. Towards this end, the reader should look for three things in the implementations in this paper. The first is the number of spins required to encode the problem. In some instances, the “logical spins/bits” (the spins which are required to encode a solution of the problem) are the only spins required; but in general, we may require auxiliary “ancilla spins/bits”, which are required to enforce constraints in the problem. Sometimes, the number of ancilla bits required can be quite large, and can be the dominant fraction of the spins in the Hamiltonian. Another thing to watch out for is the possibility that large separations of energy scales are required: e.g., the ratio of couplings $J _ { 1 2 } / J _ { 2 3 }$ in some Ising glass is proportional to $N$ , the size of the problem being studied. A final thing to note is whether or not the graph must be highly connected: does the typical degree of vertices on the Ising embedding graph (not the graph associated with the NP problem) scale linearly with $N$ ?

It is probably evident why we do not want too many ancilla bits – this simply means we can only encode smaller problems on the same size piece of hardware. It is a bit more subtle to understand why complete graphs, or separations of energy scales, are problematic. It is probable that the successful experimental implementations of AQO with the most qubits are on devices generated by DWave Systems [11, 12, 13].6 As such, we now discuss the ease with which these Hamiltonians can be encoded onto such a device. These devices may only encode problems via a “chimera” graph. The primary problem with Hamiltonians on a complete graph is that it is inefficient [43, 44] to embed complete graphs onto the chimera graph. A primary difficulty is demonstrated by the following simple case: a node $v$ in the complete graph must be mapped two a pair of nodes $u$ and $w$ on the chimera graph, with the coupling $J _ { u w }$ large compared to other scales in the problem, to ensure that $s _ { u } = s _ { w }$ (so these nodes effectively act as one spin). A second problem is that some of the Hamiltonians require separations of energy scales. However, in practice, these devices may only encode couplings constants of $1 , \ldots , 1 6$ , due to experimental uncertainties [11, 12, 13]. This means that it is unlikely that, for very connected graphs, one may successfully encode any $H$ with a separation of energy scales. A final challenge is that sometimes couplings or qubits are broken – at this early stage in the hardware development, optimal algorithms have embeddings which are insensitive to this possibility [45].

# 2. Partitioning Problems

The first class of problems we will study are partitioning problems, which (as the name suggests) are problems about dividing a set into two subsets. These maps are celebrated in the spin glass community [24], as they helped physicists realize the possibility of using spin glass technology to understand computational hardness in random ensembles of computing problems. For completeness, we review these mappings here, and present a new one based on similar ideas (the clique problem).

# 2.1. Number Partitioning

Number partitioning asks the following: given a set of $N$ positive numbers ${ \cal S } = \{ n _ { 1 } , \ldots , n _ { N } \}$ , is there a partition of this set of numbers into two disjoint subsets $R$ and $S - R$ , such that the sum of the elements in both sets is the same? For example, can one divide a set of assets with values $\pi _ { 1 } , \ldots , \pi _ { N }$ , fairly between two people? This problem is known to be NP-complete [18]. This can be phrased trivially as an Ising model as follows. Let $n _ { i }$ ( $i = 1 , \ldots , N = | S | ,$ describe the numbers in set $S$ , and let

$$
H = A \left( \sum _ { i = 1 } ^ { N } n _ { i } s _ { i } \right) ^ { 2 }
$$

be an energy function, where $s _ { i } = \pm 1$ is an Ising spin variable. Here $A > 0$ is some positive constant. Typically, such constants are scaled to $^ 1$ in the literature, but for simplicity we will retain them, since in many formulations a separation of energy scales will prove useful, and retaining each scale can make it easier to follow conceptually. Classical studies of this problem are slightly easier if the square above is replaced with absolute value [24].

It is clear that if there is a solution to the Ising model with $H = 0$ , then there is a configuration of spins where the sum of the $n _ { i }$ for the $+ 1$ spins is the same for the sum of the $n _ { i }$ for the $- 1$ spins. Thus, if the ground state energy is $H = 0$ , there is a solution to the number partitioning problem.

This Ising glass has degeneracies – i.e., there are always at least two different solutions to the problem. This can be seen by noting that if $s _ { i } ^ { * }$ denotes a solution to the problem, then $- \boldsymbol { s } _ { i } ^ { * }$ is also a solution. Physically, this corresponds to the fact that we do not care which set is labeled as $\pm$ . In the spin glass literature, the change $s _ { i } \to - s _ { i }$ , which does not change the form of $H$ , is often (rather loosely) called a gauge transformation. The existence of a gauge transformation which leaves the couplings unchanged (as there are no linear terms) implies that all energy levels of $H$ are degenerate. It is possible that there are $2 m$ ground states (with $m > 1$ ). This means that there are $m$ physically distinct solutions to the computational problem. We only need to find one of them to be happy with our adiabatic quantum algorithm. We can remove this double degeneracy by fixing $s _ { 1 } = 1$ . This also allows us to remove one spin: now only $s _ { 2 } , \ldots , s _ { N }$ are included on the graph, and $s _ { 1 }$ serves as an effective magnetic field. So in general, we require $N - 1$ spins, which live on a complete graph, to encode this problem.

If the ground state has $H > 0$ , we know that there are no solutions to the partitioning problem, but the ground state we do find is (one of) the best possible solutions, in the sense that it minimizes the mismatch. Minimizing this mismatch is an NP-hard problem, and we see that we do not require any more fancy footwork to solve the optimization problem – the same Hamiltonian does the trick.

# 2.2. Graph Partitioning

Graph partitioning is the original [20] example of a map between the physics of Ising spin glasses and NP-complete problems. Let us consider an undirected graph $G = ( V , E )$ . with an even number $N = | V |$ of vertices. We ask: what is a partition of the set $V$ into two subsets of equal size $N / 2$ such that the number of edges connecting the two subsets is minimized? This problem has many applications: finding these partitions can allow us to run some graph algorithms in parallel on the two partitions, and then make some modifications due to the few connecting edges at the end [39]. Graph partitioning is known to be an NP-hard problem; the corresponding decision problem (are there less than $k$ edges conecting the two sets?) is NP-complete [18]. We will place an Ising spin $s _ { v } = \pm 1$ on each vertex $v \in V$ on the graph, and we will let $+ 1$ and $^ { - 1 }$ denote the vertex being in either the $^ +$ set or the $-$ set. We solve this with an energy functional consisting of two components:

$$
H = H _ { A } + H _ { B }
$$

where

$$
H _ { A } = A \left( \sum _ { n = 1 } ^ { N } s _ { i } \right) ^ { 2 }
$$

is an energy which provides a penalty if the number of elements in the $^ +$ set is not equal to the number in the $-$ set, and

$$
H _ { B } = B \sum _ { ( u v ) \in E } \frac { 1 - s _ { u } s _ { v } } { 2 }
$$

is a term which provides an energy penalty $B$ for each time that an edge connects vertices from different subsets. If $B > 0$ , then we wish to minimize the number of edges between the two subsets; if $B < 0$ , we will choose to maximize this number. Should we choose $B < 0$ , we must ensure that $B$ is small enough so that it is never favorable to violate the constraint of $H _ { A }$ in order to minimize energy. To determine a rather simple lower bound on $A$ , we ask the question: what is the minimum value of $\Delta H _ { B }$ – the change in the energy contributed by the $B$ -term – if we violate the $A$ constraint once. It is easy to see that the penalty for violating the $A$ -constraint is $\Delta H _ { A } \geq 4 A$ . The best gain we can get by flipping a spin is to gain an energy of $B \operatorname* { m i n } ( \Delta , N / 2 )$ , where $\Delta$ is the maximal degree of $G$ .7 We conclude

$$
{ \frac { A } { B } } \geq { \frac { \operatorname* { m i n } ( 2 \Delta , N ) } { 8 } } .
$$

$N$ spins on a complete graph are required to encode this problem.

This Hamiltonian is invariant under the same gauge transformation $s _ { i } \to - s _ { i }$ . We conclude that we can always remove one spin by fixing a single vertex to be in the $^ +$ set.

We have written $H$ in a slightly different form than the original [20], which employed a constraint on the space of solutions to the problem, that

$$
\sum _ { i = 1 } ^ { N } s _ { i } = 0 .
$$

We will want none of our formulations to do this (i.e., we wish to solve the unconstrained optimization problem), as the experimental hardware that is being built for quantum optimization can only solve unconstrained problems. Instead, we encode constraint equations by making penalty Hamiltonians which raise the energy of a state which violates them.

# 2.3. Cliques

A clique of size $K$ in an undirected graph $G = ( V , E )$ is a subset $W \subseteq V$ of the vertices, of size $| W | = K$ , such that the subgraph $( W , E _ { W } )$ (where $E _ { W }$ is the edge set $E$ restricted to edges between nodes in $W$ ) is a complete graph – i.e., all possible $K ( K - 1 ) / 2$ edges in the graph are present, because every vertex in the clique has an edge to every other vertex in the clique. Cliques in social networks can be useful as they are “communities of friends”; finding anomalously large cliques is also a key sign that there is structure in a graph which may appear to otherwise be random [46]. The NP-complete decision problem of whether or not a clique of size $K$ exists [18] can be written as an Ising-like model, as follows. We place a spin variable $s _ { v } = \pm 1$ on each vertex $v \in V$ of the graph. In general, in this paper, for a spin variable $s _ { \alpha }$ , we will define the binary bit variable

$$
x _ { \alpha } \equiv \frac { s _ { \alpha } + 1 } { 2 } .
$$

It will typically be more convenient to phrase the energies in terms of this variable $x _ { \alpha }$ , as it will be for this problem. Note that any energy functional which was quadratic in $s _ { v }$ will remain quadratic in $x _ { v }$ , and vice versa, so we are free to use either variable. We then choose

$$
H = A \left( K - \sum _ { v } x _ { v } \right) ^ { 2 } + B \left[ { \frac { K ( K - 1 ) } { 2 } } - \sum _ { ( u v ) \in E } x _ { u } x _ { v } \right]
$$

where $A , B > 0$ are positive constants. We want the ground state of this Hamiltonian is $H = 0$ if and only if a clique of size $K$ exists. It is easy to see that $H = 0$ if there is a clique of size $K$ . However, we

wish to now show that $H \neq 0$ for any other solution. It is easy to see that if there are $n$ $x _ { v }$ s which are 1, that the minimum possible value of $H$ is

$$
\sin ( n ) = A ( n - K ) ^ { 2 } + B { \frac { K ( K - 1 ) - n ( n - 1 ) } { 2 } } = ( n - K ) \left[ A ( n - K ) - B { \frac { n + K - 1 } { 2 } } \right]
$$

The most “dangerous” possible value of $n = 1 + K$ . We can easily see that so long as $A > K B$ , $H _ { \operatorname* { m i n } } ( K + 1 ) > 0$ . We finally note that, given a ground state solution, it is of course easy to read off from the $x _ { v }$ which $K$ nodes form a clique. $N$ spins on a complete graph are required to solve this problem.

A quantum algorithm for this NP-complete problem can be made slightly more efficient so long as the initial state can be carefully prepared [47].

The NP-hard version of the clique problem asks us to find (one of) the largest cliques in a graph. We can modify the above Hamiltonian to account for this, by adding an extra variable $y _ { i }$ $\mathit { i } = 2 , \ldots , \Delta _ { \cdot }$ ), which is 1 if the largest clique has size $i$ , and $0$ otherwise. Let $H = H _ { A } + H _ { B } + H _ { C }$ where

$$
H _ { A } = A \left( 1 - \sum _ { i = 2 } ^ { N } y _ { i } \right) ^ { 2 } + A \left( \sum _ { i = 2 } ^ { n } n y _ { n } - \sum _ { v } x _ { v } \right) ^ { 2 }
$$

and

$$
H _ { B } = B \left[ { \frac { 1 } { 2 } } \left( \sum _ { i = 2 } ^ { N } n y _ { n } \right) \left( - 1 + \sum _ { i = 2 } ^ { N } n y _ { n } \right) - \sum _ { ( u v ) \in E } x _ { u } x _ { v } \right] .
$$

We want cliques to satisfy $H _ { A } = H _ { B } = 0$ , and to be the only ground states. The Hamiltonian above satisfies this if $A / B$ is large enough so the constraints of $H _ { A } = 0$ are always satisfied – we can see this by noting that the first term of $H _ { A }$ forces us to pick only one value of $y _ { i } = n$ , and the second term fixes us to choose $n$ vertices. Then $H _ { B } = 0$ ensures that we have a clique. Similarly to the discussion above, we see that the absence of negative energy states requires $A > N B$ . If the maximal degree of the graph is $\Delta$ , this can be simplified to $A > \Delta B$ . Now that we know that all ground states are cliques,8 we have to find the state with the smallest value of $y _ { n }$ . This can be obtained by choosing

$$
H = - C \sum _ { v } x _ { v } ,
$$

where $C > 0$ is some constant. If $C$ is small enough, then the ground state energy is $H = - C K$ , where $K$ is the size of the largest clique in the graph. To determine an upper bound on $C$ , so that we solve the cliques problem (as opposed to some other problem), we need to make sure that it is never favorable to color an extra vertex, at the expense of mildly violating the $H _ { A }$ constraint. The penalty for coloring one extra vertex, given $y _ { i } = n$ , is at minimum $A - n B - C$ . We conclude that we must choose

$$
C < A - n B .
$$

So, for example, we could take $A = ( \Delta + 2 ) B$ , and $B = C$ .

# 2.4. Reducing $N$ to $\log N$ Spins in Some Constraints

There is a trick which can be used to dramatically reduce the number of extra $y _ { i }$ spins which must be added, in the NP-hard version of the clique problem above [48]. In general, this trick is usable throughout this paper, as we will see similar constructions of auxiliary $y$ bits appearing repeatedly.

We know that we want to encode a variable which can take the values $2 , \ldots , N$ (or $\Delta$ , if we know the maximal degree of the graph – the argument is identical either way). For simplicity, suppose we wish to encode the values $1 , \ldots , N$ (this is a negligible difference, in the large $N$ limit). Define an integer $M$ so that

$$
2 ^ { M } \leq N < 2 ^ { M + 1 } .
$$

Alternatively, $M = \lfloor \log N \rfloor$ – in this paper, the base 2 is implied in the logarithm. In this case, we only need $M + 1$ binary variables: $y _ { 0 } , \ldots , y _ { M }$ , instead of $N$ binary variables, $y _ { 1 } , \ldots , y _ { N }$ , to encode a variable which can take $N$ values. It is easy to check that replacing

$$
\sum _ { n = 1 } ^ { N } n y _ { n }  \sum _ { n = 0 } ^ { M - 1 } 2 ^ { n } y _ { n } + ( N + 1 - 2 ^ { M } ) y _ { M }
$$

solves the same clique problem, without loss of generality. (This is true in general for all of our NP problems.) If $N \neq 2 ^ { M + 1 } - 1$ , the ground state may be degenerate, as the summation of $y$ s to a given integer is not always unique. When actually encoding these problems for computational purposes, of course, this trick should be used, but for pedagogy and simplicity we will not write it out explicitly for the remainder of the paper.

Using this trick, we note that solving the NP-hard version of the cliques problem requires $N { + } 1 { + } \lfloor \log \Delta \rfloor$ spins.

# 3. Binary Integer Linear Programming

Let $x _ { 1 } , \ldots , x _ { N }$ be $N$ binary variables, which we arrange into a vector $\mathbf { x }$ . The binary integer linear programming (ILP) problem asks: what is the largest value of $\mathbf { c } \cdot \mathbf { x }$ , for some vector $\mathbf { c }$ , given a constraint

$$
\mathsf { S } \mathbf { x } = \mathbf { b }
$$

with S an $m \times N$ matrix and $\mathbf { b }$ a vector with $m$ components. This is NP-hard [18], with a corresponding NP-complete decision problem. Many problems can be posed as ILP: e.g., a supplier who wants to maximize profit, given regulatory constraints [48].

The Ising Hamiltonian corresponding to this problem can be constructed as follows. Let $H = H _ { A } + H _ { B }$ where

$$
H _ { A } = A \sum _ { j = 1 } ^ { m } \left[ b _ { j } - \sum _ { i = 1 } ^ { N } S _ { j i } x _ { i } \right] ^ { 2 }
$$

and $A > 0$ is a constant. The ground states of $H _ { A } = 0$ enforce (if such a ground state exists, of course!) the constraint that $\mathsf { S } \mathbf { x } = \mathbf { b }$ . Then we set

$$
H _ { B } = - B \sum _ { i = 1 } ^ { N } c _ { i } x _ { i } .
$$

with $B \ll A$ another positive constant.

To find constraints on the required ratio $A / B$ , we proceed similarly to before. For simplicity, let us assume that the constraint Eq. (21) can be satisfied for some choice of $\mathbf { x }$ . For such a choice, the largest possible value of $- \Delta H _ { B }$ is, in principle, $B \mathcal { C }$ , where

$$
\mathcal { C } = \sum _ { i = 1 } ^ { N } \operatorname* { m a x } ( c _ { i } , 0 ) .
$$

The smallest possible value of $\Delta H _ { A }$ is related to the properties of the matrix S, and would occur if we only violate a single constraint, and violate that constraint by the smallest possible amount, given by

$$
{ \cal S } \equiv \operatorname* { m i n } _ { \sigma _ { i } \in \{ 0 , 1 \} , j } \left( \operatorname* { m a x } \left[ 1 , \frac { 1 } { 2 } \sum _ { i } ( - 1 ) ^ { \sigma _ { i } } S _ { j i } \right] \right) .
$$

This bound could be made better if we know more specific properties of S and/or $\mathbf { b }$ . We conclude

$$
{ \frac { A } { B } } \geq { \frac { \mathcal { C } } { S } } .
$$

If the coefficients $c _ { i }$ and $S _ { i j }$ are ${ \mathrm { O } } ( 1 )$ integers, we have ${ \mathcal { C } } \leq N \operatorname* { m a x } ( c _ { i } )$ , and $s \geq 1$ , so we conclude $A / B \gtrsim N$ .

# 4. Covering and Packing Problems

In this section, we discuss another simple class of mappings from NP problems to Ising models: “covering” and “packing” problems. These problems can often be thought of as asking: how can I pick elements out of a set (such as vertices out of a graph’s vertex set) so that they “cover” the graph in some simple way (e.g., removing them makes the edge set empty). In this class of problems, there are constraints which must be exactly satisfied. Many of the problems described below are often discussed in the literature, but again we review them here for completeness. We conclude the section with the minimal maximal matching problem, which is a slightly more involved problem that has not been discussed in the AQO literature before.

These are, by far, the most popular class of problems discussed in the AQO literature. As we mentioned in the introduction, this is because this is the only class of NP problems (discussed in this paper) for which it is easy to embed the problem via a graph which is not complete (or close to complete).

# 4.1. Exact Cover

The exact cover problem goes as follows: consider a set $U = \{ 1 , \ldots , n \}$ , and subsets $V _ { i } \subseteq U$ ( $\mathbf { \zeta } _ { i } = 1 , \ldots , N )$ such that

$$
U = \bigcup _ { i } V _ { i } .
$$

The question is: is there a subset of the set of sets $\{ V _ { i } \}$ , called $R$ , such that the elements of $R$ are disjoint sets, and the union of the elements of $R$ is $U$ ? This problem was described in [49] but for simplicity, we repeat it here. This decision problem is NP-complete [18]. The Hamiltonian we use is

$$
H _ { A } = A \sum _ { \alpha = 1 } ^ { n } \left( 1 - \sum _ { i : \alpha \in V _ { i } } x _ { i } \right) ^ { 2 } .
$$

In the above Hamiltonian $\alpha$ denotes the elements of $U$ , while $i$ denotes the subsets $V _ { i }$ . $H _ { A } = 0$ precisely when every element is included exactly one time, which implies that the unions are disjoint. The existence of a ground state of energy $H = 0$ corresponds to the existence of a solution to the exact cover problem. If this ground state is degenerate, there are multiple solutions. $N$ spins are required.

It is also straightforward to extend this, and find the smallest exact cover (this makes the problem NP-hard). This is done by simply adding a second energy scale: $H = H _ { A } + H _ { B }$ , with $H _ { A }$ given above, and

$$
H _ { B } = B \sum _ { i } x _ { i } .
$$

The ground state of this model will be $m B$ , where $m$ is the smallest number of subsets required. To find the ratio $A / B$ required to encode the correct problem, we note that the worst case scenario is that there are a very small number of subsets with a single common element, whose union is $U$ . To ensure this does not happen, one can set $A > n B$ .9

# 4.2. Set Packing

Let us consider the same setup as the previous problem, but now ask a different question: what is the largest number of subsets $V _ { i }$ which are all disjoint? This is called the set packing problem; this optimization problem is NP-hard [18]. To do this, we use $H = H _ { A } + H _ { B }$ :

$$
H _ { A } = A \sum _ { i , j : V _ { i } \cap V _ { j } \neq \emptyset } x _ { i } x _ { j } ,
$$

which is minimized only when all subsets are disjoint. Then, we use

$$
H _ { B } = - B \sum _ { i } x _ { i }
$$

which simply counts the number of sets we included. Choosing $B < A$ ensures that it is never favorable to violate the constraint $H _ { A }$ (since there will always be a penalty of at least $A$ per extra set included) [4].

Note that an isomorphic formulation of this problem, in the context of graph theory is as follows: let us consider the sets to be encoded in an undirected graph $G = ( V , E )$ , where each set $V _ { i }$ maps to to a vertex $i \in V$ . An edge $i j \in E$ exists when $V _ { i } \cap V _ { j }$ is nonempty. It is straightforward to see that if we replace

$$
H _ { A } = A \sum _ { i j \in E } x _ { i } x _ { j }
$$

that the question of what is the maximal number of vertices which may be “colored” ( $x _ { i } = 1$ ) such that no two colored vertices are connected by an edge, is exactly equivalent to the set packing problem described above. This version is called the maximal independent set (MIS) problem.

# 4.3. Vertex Cover

Given an undirected graph $G = ( V , E )$ , what is the smallest number of vertices that can be “colored” such that every edge is incident to a colored vertex? This is NP-hard; the decision form is NP-complete [18]. Let $x _ { v }$ be a binary variable on each vertex, which is 1 if it is colored, and 0 if it is not colored. Our Hamiltonian will be $H = H _ { A } + H _ { B }$ . The constraint that every edge has at least colored vertex is encoded in $H _ { A }$ :

$$
H _ { A } = A \sum _ { u v \in E } ( 1 - x _ { u } ) ( 1 - x _ { v } ) .
$$

Then, we want to minimize the number of colored vertices with $H _ { B }$ :

$$
H _ { B } = B \sum _ { v } x _ { v }
$$

Choose $B < A$ , as if we uncolor any vertex that ruins the solution, at least one edge will no longer connect to a colored vertex. The number of spins required is $| V |$ , the size of the vertex set.

# 4.4. Satisfiability

Satisfiability is one of the most famous NP-complete problems [18]. Every satisfiability problem can be written as a so-called 3SAT problem in conjunctive normal form (and this algorithm takes only polynomial steps/time) and so we will focus for simplicity on this case. In this case, we ask whether

$$
\Psi = C _ { 1 } \wedge C _ { 2 } \cdot \cdot \cdot \wedge C _ { m }
$$

can take on the value of true – i.e., every $C _ { i }$ for $1 \leq i \leq m$ is true, where the form of each $C _ { i }$ is:

$$
C _ { i } = y _ { i _ { 1 } } \vee y _ { i _ { 2 } } \vee y _ { i _ { 3 } }
$$

Here $y _ { i _ { 1 } }$ , $y _ { i _ { 2 } }$ and $y _ { i _ { 3 } }$ are selected from another set of Boolean variables: $x _ { 1 } , \ldots , x _ { N } , { \overline { { x } } } _ { 1 } , \ldots , { \overline { { x } } } _ { N }$ . This is a very brief description of satisfiability; physicists who are unfamiliar with this problem should read appropriate chapters of [24].

There is a well-known reduction of 3SAT to MIS [49] which we reproduce here, for completeness. Consider solving the set packing problem on a graph $G$ with $3 m$ nodes, which we construct as follows. For each clause $C _ { i }$ , we add 3 nodes to the graph, and connect each node to the other 3. After this step, if there is a $y _ { 1 }$ and $y _ { 2 }$ such that $y _ { 1 } = \overline { { y } } _ { 2 }$ , then we also add an edge between these two nodes. Solving MIS on this graph, and asking whether the solution has exactly $m$ nodes, is equivalent to solving the 3SAT problem. This can be seen as follows: if a solution to the 3SAT problem exists, only one element of each clause needs to be true – if more are true, that is also acceptable, but we must have that one is true, so let us choose to color the vertex corresponding to the variable which is true. However, we may also not choose to have both $x _ { 1 }$ be true and $\overline { { x } } _ { 1 }$ be true, so we are required to connect all such points with an edge. Since the graph is made up of $m$ connected triangles, the only way to color $m$ vertices if each vertex is in a distinct triangle, so there must be an element of each clause $C _ { i }$ which is true.

Note that we can solve an NP-hard version of this problem (if we have to violate some clauses, wha is the fewest number?), by solving the optimization version of the MIS problem.

# 4.5. Minimal Maximal Matching

The minimal maximal (minimax) matching problem on a graph is defined as follows: let $G = ( V , E )$ denote an undirected graph, and let $C \subseteq E$ be a proposed “coloring”. The constraints on $C$ are as follows: for each edge in $C$ , let us color the two vertices it connects: i.e. let $D = \cup _ { e \in C } \partial e$ . We will then demand that: no two edges in $C$ share a vertex (if $e _ { 1 } , e _ { 2 } \in C$ , $\partial e _ { 1 } \cap \partial e _ { 2 } = \emptyset$ ) and that if $u , v \in D$ , that $( u v ) \notin E$ . This is NP-hard; the decision problem is NP-complete [19]. This is minimal in that we cannot add any more edges to $C$ (coloring any appropriate vertices) without violating the first constraint, and maximal in the sense that the trivial empty set solution is not allowed – we must include all edges between uncolored vertices.

Note that, from this point on in this paper, we have not found any of the Ising formulations of this paper in the literature.

We will use the spins on the graph to model whether or not an edge is colored. Let us use the binary variable $x _ { e }$ to denote whether or not an edge is colored; thus, the number of spins is $| E | = \mathrm { O } ( \Delta N )$ , the size of the edge set; as before, $\Delta$ represents the maximal degree. To encode this problem, we use a series of three Hamiltonians:

$$
H = H _ { A } + H _ { B } + H _ { C } .
$$

The first and largest term, $H _ { A }$ , will impose the constraint that no vertex has two colored edges. This can be done by setting

$$
H _ { A } = A \sum _ { v } \sum _ { \{ e _ { 1 } , e _ { 2 } \} \subset \partial v } x _ { e _ { 1 } } x _ { e _ { 2 } } .
$$

Here $A > 0$ is a positive energy, and $\partial v$ corresponds to the subset of $E$ of edges which connect to $v$ . Thus the ground states consist of $H _ { A } = 0$ ; if $H _ { A } > 0$ , it is because there is a vertex where two of its edges are colored.

We also can define, for states with $H _ { A } = 0$ , the variable

$$
y _ { v } \equiv { \left\{ \begin{array} { l l } { 1 ~ } & { v { \mathrm { ~ h a s ~ a ~ c o l o r e d ~ e d g e } } } \\ { 0 ~ } & { v { \mathrm { ~ h a s ~ n o ~ c o l o r e d ~ e d g e s } } } \end{array} \right. } = \sum _ { e \in \partial v } x _ { e } .
$$

We stress that this definition is only valid for states with $H _ { A } = 0$ , since in these states each vertex has either $0$ or 1 colored edges. We then define the energy $H _ { B }$ , such that solutions to the minimax coloring problem also have $H _ { B } = 0$ . Since we have already constrained the number of colored edges per vertex, we choose $H _ { B }$ to raise the energy of all solutions where there exists a possible edge which can be colored, yet still not violate the coloring condition, out of the ground state. To do this, we can sum over all edges in the graph, and check whether or not the edge connects two vertices, neither of which are colored:

$$
H _ { B } = B \sum _ { e = ( u v ) } ( 1 - y _ { u } ) ( 1 - y _ { v } ) .
$$

Note that since, $1 - y _ { v }$ can be negative, we must choose $B > 0$ to be small enough. To bound $B$ , we note that the only problem (a negative term in $H _ { B }$ ) comes when $y _ { u } = 0$ , $y _ { v } > 1$ , and $( u v ) \in E$ . Suppose that $m$ of $\boldsymbol { v }$ ’s neighbors have $y _ { u } = 0$ . Then, the contributions to $H _ { A }$ and $H _ { B }$ associated to node $v$ are given by

$$
H _ { v } = A \frac { y _ { v } ( y _ { v } - 1 ) } { 2 } - B ( y _ { u } - 1 ) m .
$$

Note that $m + y _ { u } \le k$ , if $k$ is the degree of node $v$ . Putting all of this together, we conclude that if $\Delta$ is the maximal degree in the graph, because the worst case scenario is $y _ { v } = 2$ , $m = \Delta - 2$ , if we pick

$$
A > ( \Delta - 2 ) B ,
$$

then it is never favorable to have any $y _ { v } > 1$ . This will ensure that a ground state of $H _ { A } + H _ { B }$ will have $H _ { A } = H _ { B } = 0$ : i.e., states which do not violate the minimax constraints.

Now, given the states where $H _ { A } = H _ { B } = 0$ , we now want the ground state of $H _ { A } + H _ { B } + H _ { C }$ to be the state where the fewest number of edges are colored. To do this, we simply let

$$
H _ { C } = C \sum _ { e } x _ { e }
$$

count the number of colored edges. Here $C$ is an energy scale chosen to be small enough such that it is never energetically favorable to violate the constraints imposed by either the $H _ { A }$ or $H _ { B }$ terms: one requires $C < B$ , since there is an energy penalty of $B$ associated to each edge which could be colored, but isn’t. The term with the smallest $H _ { C }$ has the smallest number of edges, and is clearly the solution to the minimax problem. Each ground state of this spin model is equivalent to a solution of the minimax problem.

# 5. Problems with Inequalities

We now turn to NP problems whose formulations as Ising models are more subtle, due to the fact that constraints involve inequalities as opposed to equalities. These constraints can be re-written as constraints only involving equalities by an expansion of the number of spins.

As with partitioning problems, we will find that these Hamiltonians require embedding highly con nected graphs onto a quantum device. This may limit their usability on current hardware.

# 5.1. Set Cover

Consider a set $U = \{ 1 , \ldots , n \}$ , with sets $V _ { i } \subseteq U$ $i = 1 , \ldots , N )$ such that

$$
U = \bigcup _ { i = 1 } ^ { N } V _ { \alpha } .
$$

The set covering problem is to find the smallest possible number of $V _ { i }$ s, such that the union of them is equal to $U$ . This is a generalization of the exact covering problem, where we do not care if some $\alpha \in U$ shows up in multiple sets $V _ { i }$ ; finding the smallest number of sets which “cover” $U$ is NP-hard [18].

Let us denote $x _ { i }$ to be a binary variable which is 1 if set $i$ is included, and $0$ if set $i$ is not included. Let us then denote $x _ { \alpha , m }$ to be a binary variable which is 1 if the number of $V _ { i }$ s which include element $\alpha$ is $m \geq 1$ , and 0 otherwise. Set $H = H _ { A } + H _ { B }$ . Our first energy imposes the constraints that exactly one $x _ { \alpha , m }$ must be 1, since each element of $U$ must be included a fixed number of times, and that the number of times that we claimed $\alpha$ was included is in fact equal to the number of $V _ { i }$ we have included, with $\alpha$ as an element:

$$
H _ { A } = A \sum _ { \alpha = 1 } ^ { n } \left( 1 - \sum _ { m = 1 } ^ { N } x _ { \alpha , m } \right) ^ { 2 } + A \sum _ { \alpha = 1 } ^ { n } \left( \sum _ { m = 1 } ^ { N } m x _ { \alpha , m } - \sum _ { i : \alpha \in V _ { i } } x _ { i } \right) ^ { 2 } .
$$

Finally, we minimize over the number of $V _ { \alpha }$ s included:

$$
H _ { B } = B \sum _ { i = 1 } ^ { N } x _ { i } ,
$$

with $0 < B < A$ required to never violate the constraints of $H _ { A }$ (the worst case is that one set must be included to obtain one element of $U$ ; the change in $H$ if we include this last element is $B - A$ , which must be negative).

Let $M \leq N$ be the maximal number of sets which contain any given element of $U$ ; then $N$ $x _ { i }$ s are required, and $n \lfloor 1 + \log M \rfloor$ spins are required (using the trick described earlier) for the $x _ { \alpha , m }$ spins; the total number is therefore $N + n \lfloor 1 + \log M \rfloor$ spins.

# 5.2. Knapsack with Integer Weights

The knapsack problem is the following problem: we have a list of $N$ objects, labeled by indices $\alpha$ , with the weight of each object given by $w _ { \alpha }$ , and its value given by $c _ { \alpha }$ , and we have a knapsack which can only carry weight $W$ . If $x _ { \alpha }$ is a binary variable denoting whether (1) or not (0) object $\alpha$ is contained in the knapsack, the total weight in the knapsack is

$$
\mathcal { W } = \sum _ { \alpha = 1 } ^ { N } w _ { \alpha } x _ { \alpha }
$$

and the total cost is

$$
\mathcal { C } = \sum _ { \alpha = 1 } ^ { N } c _ { \alpha } x _ { \alpha } .
$$

The NP-hard [18] knapsack problem asks us to maximize $\mathcal { C }$ subject to the constraint that $\mathcal { W } \leq W$ . It has a huge variety of applications, particularly in economics and finance [50].

Let $y _ { n }$ for $1 \leq n \leq W$ denote a binary variable which is $^ 1$ if the final weight of the knapsack is $n$ , and 0 otherwise. Our solution consists of letting $H = H _ { A } + H _ { B }$ , with

$$
H _ { A } = A \left( 1 - \sum _ { n = 1 } ^ { W } y _ { n } \right) ^ { 2 } + A \left( \sum _ { n = 1 } ^ { W } n y _ { n } - \sum _ { \alpha } w _ { \alpha } x _ { \alpha } \right) ^ { 2 }
$$

which enforces that the weight can only take on one value and that the weight of the objects in the knapsack equals the value we claimed it did, and finally

$$
H _ { B } = - B \sum _ { \alpha } c _ { \alpha } x _ { \alpha } .
$$

As we require that it is not possible to find a solution where $H _ { A }$ is weakly violated at the expense of $H _ { B }$ becoming more negative, we require $0 < B \operatorname* { m a x } ( c _ { \alpha } ) < A$ (adding one item to the knapsack, which makes it too heavy, is not allowed). The number of spins required is (using the log trick) $N + \lfloor 1 + \log W \rfloor$ .

# 6. Coloring Problems

We now turn to coloring problems. Naively, coloring problems are often best phrased as Potts models [51], where the spins can take on more than two values, but these classical Potts models can be converted to classical Ising models with an expansion of the number of spins. This simple trick forms the basis for our solutions to this class of problems.

# 6.1. Graph Coloring

Given an undirected graph $G = ( V , E )$ , and a set of $n$ colors, is it possible to color each vertex in the graph with a specific color, such that no edge connects two vertices of the same color? This is one of the more famous NP-complete [18] problems, as one can think of it as the generalization of the problem of how many colors are needed to color a map, such that no two countries which share a border have the same color. Of course, in this special case,10 one can prove that there is always a coloring for $n \geq 4$ [52, 53]. This problem is called the graph coloring problem.

Our solution consists of the following: we denote $x _ { v , i }$ to be a binary variable which is $1$ if vertex $v$ is colored with color $i$ , and $0$ otherwise. The energy is

$$
H = A \sum _ { v } \left( 1 - \sum _ { i = 1 } ^ { n } x _ { v , i } \right) ^ { 2 } + A \sum _ { ( u v ) \in E } \sum _ { i = 1 } ^ { n } x _ { u , i } x _ { v , i } .
$$

The first term enforces the constraint that each vertex has exactly one color, and provides an energy penalty each time this is violated, and the second term gives an energy penalty each time an edge connects two vertices of the same color. If there is a ground state of this model with $H = 0$ , then there is a solution to the coloring problem on this graph with $n$ colors. We can also read off the color of each node (in one such coloring scheme) by looking at which $x \mathrm { s }$ are 1. Note that the number of spins can be slightly reduced, since there is a permutation symmetry among colorings, by choosing a specific node in the graph to have the color 1, and one of its neighbors to have the color 2, for example. The total number of spins required is thus $n N$ .

# 6.2. Clique Cover

The clique cover problem, for an undirected graph $G = ( V , E )$ , is the following: given $n$ colors, we assign a distinct color to each vertex of the graph. Let $W _ { 1 } , \ldots , W _ { n }$ be the subsets of $V$ corresponding to each color, and $E _ { W _ { 1 } } , \ldots , E _ { W _ { n } }$ the edge set restricted to edges between vertices in the $W _ { i }$ sets. The clique cover problem asks whether or not $( W _ { i } , E _ { W _ { i } } )$ is a complete graph for each $W _ { i }$ (i.e., does each set of colored vertices form a clique?). This problem is known to be NP-complete [18].

Our solution is very similar to the graph coloring problem. Again, we employ the same binary variables as for graph coloring, and use a Hamiltonian very similar to the cliques problem:

$$
H = A \sum _ { v } \left( 1 - \sum _ { i = 1 } ^ { n } x _ { v , i } \right) ^ { 2 } + B \sum _ { i = 1 } ^ { n } \left[ \frac { 1 } { 2 } \left( - 1 + \sum _ { v } x _ { v , i } \right) \sum _ { v } x _ { v , i } - \sum _ { ( u v ) \in E } x _ { u , i } x _ { v , i } \right] .
$$

The first term enforces the constraint that each vertex has exactly one color by giving an energy penalty each time this constraint is violated. In the second term, since the sum over $v$ of $x _ { v , i }$ counts the number of nodes with color $i$ , the first sum counts highest possible number of edges that could exist with color $i$ . The second term then checks if, in fact, this number of edges does in fact exist. Thus $H = 0$ if and only if the clique cover problem is solved by the given coloring. If a ground state exists with $H = 0$ , there is a solution to the clique covering problem. The discussion on the required ratio $A / B$ to encode the correct solution is analogous to the discussion for the cliques problem. The total number of spins required is $n N$ .

# 6.3. Job Sequencing with Integer Lengths

The job sequencing problem is as follows: we are given a list of $N$ jobs for $m$ computer clusters. Each job $i$ has length $L _ { i }$ . How can each job be assigned to a computer in the cluster such that, if the set of jobs on cluster $\alpha$ is $V _ { \alpha }$ , then the length of that cluster, defined as

$$
M _ { \alpha } \equiv \sum _ { i \in V _ { \alpha } } L _ { i } ,
$$

are chosen such that $\operatorname* { m a x } ( M _ { \alpha } )$ is minimized? Essentially, this means that if we run all of the jobs simultaneously, all jobs will have finished running in the shortest amount of time. This is NP-hard [18], and there is a decision version (is $\operatorname* { m a x } ( M _ { \alpha } ) \leq M _ { 0 } !$ ?) which is NP-complete. We assume that $L _ { i } \in \mathbb { N }$ .

To do this, we will begin by demanding that without loss of generality, $M _ { 1 } \ge M _ { \alpha }$ for any $\alpha$ . Introduce the variables $x _ { i , \alpha }$ which are 1 if job $i$ is added to computer $\alpha$ , and 0 otherwise, and the variables $y _ { n , \alpha }$ for $\alpha \neq 1$ and $n \geq 0$ , which is $^ 1$ if the difference $M _ { 1 } - M _ { \alpha } = n$ . Then the Hamiltonian

$$
H _ { A } = A \sum _ { i = 1 } ^ { N } \left( 1 - \sum _ { \alpha } x _ { i , \alpha } \right) ^ { 2 } + A \sum _ { \alpha = 1 } ^ { m } \left( \sum _ { n = 1 } ^ { M } n y _ { n , \alpha } + \sum _ { i } L _ { i } ( x _ { i , \alpha } - x _ { i , 1 } ) \right) ^ { 2 }
$$

encodes that each job can be given to exactly one computer, and that no computer can have a longer total length than computer 1. The number $\mathcal { M }$ must be chosen by the user, and is related to the number of auxiliary spins required to adequately impose the length constraints that $M _ { 1 } \ge M _ { \alpha }$ : in the worst case, it is given by $N \operatorname* { m a x } ( L _ { i } )$ . To find the minimal maximal length $M _ { 1 }$ , we just use

$$
H _ { B } = B \sum _ { i } L _ { i } x _ { i , 1 } .
$$

Similarly to finding bounds on $A / B$ for the knapsack problem, for this Hamiltonian to encode the solution to the problem, we require (in the worst case) $0 < B \operatorname* { m a x } ( L _ { i } ) < A$ . Using the log trick, the number of spins required here is $m N + ( m - 1 ) \lfloor 1 + \log { \mathcal { M } } \rfloor$ .

In this section, we describe the solution to the (undirected or directed) Hamiltonian cycles problem, and subsequently the traveling salesman problem, which for the Ising spin glass formulation, is a trivial extension.

# 7.1. Hamiltonian Cycles and Paths

Let $G = ( V , E )$ , and $N = | V |$ . The graph can either be directed or undirected; our method of solution will not change. The Hamiltonian path problem is as follows: starting at some node in the graph, can one travel along an edge, visiting other nodes in the graph, such that one can reach every single node in the graph without ever returning to the same node twice? The Hamiltonian cycles problem asks that, in addition, the traveler can return to the starting point from the last node he visits. Hamiltonian cycles is a generalization of the famous K¨onigsberg bridge problem [24], and is NP-complete [18].

Without loss of generality, let us label the vertices $1 , \ldots , N$ , and take the edge set $( u v )$ to be directed – i.e., the order $u v$ matters. It is trivial to extend to undirected graphs, by just considering a directed graph with $( v u )$ added to the edge set whenever $( u v )$ is added to the edge set. Our solution will use $N ^ { 2 }$ bits $x _ { v , i }$ , where $v$ represents the vertex and $i$ represents its order in a prospective cycle. Our energy will have three components. The first two things we require are that every vertex can only appear once in a cycle, and that there must be a $j ^ { \mathrm { t h } }$ node in the cycle for each $j$ . Finally, for the nodes in our prospective ordering, if $x _ { u , j }$ and $x _ { v , j + 1 }$ are both 1, then there should be an energy penalty if $( u v ) \notin E$ . Note that $N + 1$ should be read as $^ 1$ , in the expressions below, if we are solving the cycles problem. These are encoded in the Hamiltonian:

$$
H = A \sum _ { v = 1 } ^ { n } \left( 1 - \sum _ { j = 1 } ^ { N } x _ { v , j } \right) ^ { 2 } + A \sum _ { j = 1 } ^ { n } \left( 1 - \sum _ { v = 1 } ^ { N } x _ { v , j } \right) ^ { 2 } + A \sum _ { ( u v ) \notin E } \sum _ { j = 1 } ^ { N } x _ { u , j } x _ { v , j + 1 } .
$$

$A > 0$ is a constant. It is clear that a ground state of this system has $H = 0$ only if we have an ordering of vertices where each vertex is only included once, and adjacent vertices in the cycle have edges on the graph – i.e., we have a Hamiltonian cycle.

To solve the Hamiltonian path problem instead, restrict the last sum over $j$ above from $_ 1$ to $N - 1$ ; we do not care about whether or not the first and last nodes are also connected. $N ^ { 2 }$ spins are requied to solve this problem.

It is straightforward to slightly reduce the size of the state space for the Hamiltonian cycles problem as follows: it is clear that node 1 must always be included in a Hamiltonian cycle, and without loss of generality we can set $x _ { 1 , i } = \delta _ { 1 , i }$ : this just means that the overall ordering of the cycle is chosen so that node 1 comes first. This reduces the number of spins to $( N - 1 ) ^ { 2 }$ .

# 7.2. Traveling Salesman

The traveling salesman problem for a graph $G = ( V , E )$ , where each edge $u v$ in the graph has a weight $W _ { u v }$ associated to it, is to find the Hamiltonian cycle such that the sum of the weights of each edge in the cycle is minimized. Typically, the traveling salesman problem assumes a complete graph, but we have the technology developed to solve it on a more arbitrary graph. The decision problem (does a path of total weight $\leq W$ exist?) is NP-complete [18].

To solve this problem, we use $H = H _ { A } + H _ { B }$ , with $H _ { A }$ the Hamiltonian given for the directed (or undirected) Hamiltonian cycles problem. We then simply add

$$
H _ { B } = B \sum _ { ( u v ) \in E } W _ { u v } \sum _ { j = 1 } ^ { N } x _ { u , j } x _ { v , j + 1 } .
$$

with $B$ small enough that it is never favorable to violate the constraints of $H _ { A }$ ; one such constraint is $0 < B \operatorname* { m a x } ( W _ { u v } ) < A$ (we assume in complete generality $W _ { u v } \ge 0$ for each $( u v ) \in E$ ).11 If the traveling salesman does not have to return to his starting position, we can restrict the sum over $j$ from $_ 1$ to $N - 1$ , as before. As with Hamiltonian cycles, $( N - 1 ) ^ { 2 }$ spins are required, as we may fix node 1 to appear first in the cycle.

# 8. Tree Problems

The most subtle NP problems to solve with Ising models are problems which require finding connected tree subgraphs of larger graphs.12 Because determining whether a subgraph is a tree requires global information about the connectivity of a graph, we will rely on similar tricks to what we used to write down Hamiltonian cycles as an Ising model.

# 8.1. Minimal Spanning Tree with a Maximal Degree Constraint

The minimal spanning tree problem is the following: given an undirected graph $G = ( V , E )$ , where each edge $( u v ) \in E$ is associated with a cost $c _ { u v }$ , what is the tree $T \subseteq G$ , which contains all vertices, such that the cost of $T$ , defined as

$$
c ( T ) \equiv \sum _ { ( u v ) \in E _ { T } } c _ { u v } ,
$$

is minimized (if such a tree exists)? Without loss of generality, we take $c _ { u v } \ > \ 0$ in this subsection (a positive constant can always be added to each $c _ { u v }$ ensure that the smallest value of $c _ { u v }$ is strictly positive, without changing the trees $T$ which solve the problem). We will also add a degree constraint, that each degree in $T$ be $\leq \Delta$ . This makes the problem NP-hard, with a corresponding NP-complete decision problem [18].

To solve this problem, we place a binary variable $y _ { e }$ on each edge to determine whether or not that edge is included in $T$ :

$$
y _ { e } \equiv \left\{ \begin{array} { l l } { { 1 } } & { { e \in E _ { T } } } \\ { { 0 } } & { { \mathrm { o t h e r w i s e } } } \end{array} \right. .
$$

We also place a large number of binary variables $x _ { v , i }$ on each vertex, and $x _ { u v , i } , x _ { v u , i }$ on edge $( u v )$ (these are distinct spins): the number $i = 0 , 1 , \ldots , N / 2$ will be used to keep track of the depth a node in the tree, and if $x _ { u v } = 1$ , it means that $u$ is closer to the root than $v$ , and if $x _ { v u } = 1$ it means that $v$ is closer to the root. Finally, we use another variable $z _ { v , i }$ ( $i = 1 , \dots \Delta$ ) to count the number of degrees of each node. We now use energy $H = H _ { A } + H _ { B }$ , where the terms in $H _ { A }$ are used to impose the constraints that: there is exactly one root to the tree, each vertex has a depth, each bond has a depth, and its two vertices must be at different heights, the tree is connected (i.e., exactly one edge to a non-root vertex comes from a vertex at lower depth), each node can have at most $\Delta$ edges, and each edge at depth $i$ points between a node at depth $i - 1$ and $i$ , respectively:

$$
\begin{array} { l } { \displaystyle { _ A = A \left( 1 - \sum _ { v } x _ { v , 0 } \right) ^ { 2 } + A \sum _ { v } \left( 1 - \sum _ { i } x _ { v , i } \right) ^ { 2 } + A \sum _ { u v \in E } \left( y _ { u v } - \sum _ { i } ( x _ { u v , i } + x _ { v u , i } ) \right) ^ { 2 } } } \\ { \displaystyle { + A \sum _ { v } \sum _ { i = 1 } ^ { N / 2 } \left( x _ { v , i } - \sum _ { u : ( u v ) \in E } x _ { u v , i } \right) ^ { 2 } + A \sum _ { v } \left( \sum _ { j = 1 } ^ { \Delta } j z _ { v , j } - \sum _ { u : ( u v ) \in E } \sum _ { i } ( x _ { u v , i } + x _ { v u , i } ) \right. } } \\ { \displaystyle { + A \left. \sum _ { ( u v ) , ( v u ) \in E } \sum _ { i = 1 } ^ { N / 2 } x _ { u v , i } ( 2 - x _ { u , i - 1 } - x _ { v , i } ) \right. } } \end{array}
$$

The ground states with $H _ { A } = 0$ are trees which include every vertex. In the last term in the sum, remember that $x _ { u v , i }$ and $x _ { v u , i }$ are both spins that are included for each edge; the notation in the summation is meant to remind us of this. We then add

$$
H _ { B } = B \sum _ { u v , v u \in E } \sum _ { i = 1 } ^ { N / 2 } c _ { u v } x _ { u v , i } .
$$

In order to solve the correct problem, we need to make sure that we never remove any $x _ { u v , i }$ from $H _ { B }$ in order to have a more negative total $H$ . As each constraint in $H _ { A }$ contributes an energy $\geq A$ if it is violated, we conclude that setting $0 < B \operatorname* { m a x } ( c _ { u v } ) < A$ is sufficient. The minimum of $E$ will find the minimal spanning tree, subject to the degree constraint.

The number of spins required is $| V | ( \lfloor | V | + 1 \rfloor + 2 ) / 2 + | E | ( | V | + 1 ) + | V | \lfloor 1 + \log \Delta \rfloor$ . The maximal possible number of edges on any graph is $| E | = \mathrm { O } ( | V | ^ { 2 } )$ , so this Ising formulation may require a cubic number of spins in the size of the vertex set.

# 8.2. Steiner Trees

The NP-hard [18] Steiner tree problem is somewhat similar to the problem above: given our costs $c _ { u v }$ , we want to find a minimal spanning tree for a subset $U \subset V$ of the vertices (i.e., a tree such that the sum of $c _ { u v }$ s along all included edges is minimal). We no longer impose degree constraints; the problem turns out to be “hard” already, as we now allow for the possibility of not including nodes which are not in $U$ .

To solve this by finding the ground state of an Ising model, we use the same Hamiltonian as for the minimal spanning tree, except we add binary variables $y _ { v }$ for $v \not \in U$ which determine whether or not a node $\boldsymbol { v }$ is included in the tree. We use the Hamiltonian $H = H _ { A } + H _ { B }$ , where $H _ { A }$ enforces constraints similarly to in the previous case:

$$
\begin{array} { l } { \displaystyle { H _ { A } = A \left( 1 - \sum _ { v } x _ { v , 0 } \right) ^ { 2 } + A \sum _ { v \in U } \left( 1 - \sum _ { i } x _ { v , i } \right) ^ { 2 } + A \sum _ { v \notin U } \left( y _ { v } - \sum _ { i } x _ { v , i } \right) ^ { 2 } } } \\ { \displaystyle { \qquad + A \sum _ { v } \sum _ { i = 1 } ^ { N / 2 } \left( x _ { v , i } - \sum _ { ( u v ) \in E } x _ { u v , i } \right) ^ { 2 } + A \sum _ { u v , v u \in E } \sum _ { i = 1 } ^ { N / 2 } x _ { u v , i } ( 2 - x _ { u , i - 1 } - x _ { v , i } ) } } \\ { \displaystyle { \qquad + A \sum _ { u v \in E } \left( y _ { u v } - \sum _ { i } ( x _ { u v , i } + x _ { v u , i } ) \right) ^ { 2 } } } \end{array}
$$

We then use $H _ { B }$ from the previous model to determine the minimum weight tree; the same constraints on $A / B$ apply. The number of spins is $| V | ( \lfloor | V | + 1 \rfloor + 4 + 2 | E | ) / 2 + | E |$ .

# 8.3. Directed Feedback Vertex Set

A feedback vertex set for a directed graph $G = ( V , E )$ is a subset $F ~ \subset ~ V$ such that the subgraph $( V - F , \partial ( V - F ) )$ is acyclic (has no cycles). We will refer to $F$ as the feedback set. Solving a decision problem for whether or not a feedback set exists for $| F | \le k$ is NP-complete [18]. We solve the optimization problem of finding the smallest size of the feedback set first for a directed graph – the extension to an undirected graph will be a bit more involved.

Before solving this problem, it will help to prove two lemmas. The first lemma is quite simple: there exists a node in a directed acyclic graph which is not the end point of any edges. Suppose that for each vertex, there was an edge that ends on that vertex. Then pick an arbitrary vertex, pick any edge ending on that vertex, and follow that edge in reverse to the starting vertex. Repeat this process more than $N$ times, and a simple counting argument implies that we must have visited the same node more than once, at least once. Thus, we have traversed a cycle in reverse, which contradicts our assumption.

The second lemma is as follows: a directed graph $G = ( V , E )$ is acyclic if and only if there is a height function $h : V \to \mathbb { N }$ such that if $u v \in E$ , $h ( u ) < h ( v )$ : i.e., every edge points from a node at lower height to one at higher height. That height function existence implies acyclic is easiest to prove using the contrapositive: suppose that a graph is cyclic. Then on a cycle of edges, we have

$$
0 < \sum [ h ( u _ { i + 1 } ) - h ( u _ { i } ) ] = h ( u _ { 1 } ) - h ( u _ { n } ) + h ( u _ { n } ) - h ( u _ { n - 1 } ) + \cdot \cdot \cdot - h ( u _ { 1 } ) = 0
$$

is a contradiction. To prove that an acyclic graph has a height function, we construct one recursively. Using our first lemma, we know that there exists a vertex $u$ with only outgoing edges, so let us call $h ( u ) = 1$ . For any other vertex, we will call the height of that vertex $h ( v ) = 1 + h ^ { \prime } ( v )$ , where $h ^ { \prime } ( v )$ is found by repeating this process on the graph with node $u$ removed (which must also be acyclic). It is clear this process will terminate and assign exactly one node height $i$ for each integer $1 \leq i \leq | V |$ .

We can now exploit this lemma to write down an Ising spin formulation of this problem. We place a binary variable $y _ { v }$ on each vertex, which is $0$ if $v$ is part of the feedback set, and 1 otherwise. We then place a binary variable $x _ { v , i }$ on each vertex, which is 1 if vertex $\boldsymbol { v }$ is at height $i$ . So far the heights $i$ are arbitrary, and the requirement that a height function be valid will be imposed by the energy. The energy functional we use is $H = H _ { A } + H _ { B }$ where

$$
H _ { A } = A \sum _ { v } \left( y _ { v } - \sum _ { i } x _ { v , i } \right) ^ { 2 } + A \sum _ { u v \in E } \sum _ { i \geq j } x _ { u , i } x _ { v , j } .
$$

The first term ensures that if a vertex is not part of the feedback set, it has a well-defined height; the second term ensures that an edge only connects a node with lower height to a node at higher height. We then find the smallest possible feedback set by adding

$$
H _ { B } = B \sum _ { v } ( 1 - y _ { v } ) .
$$

In order to solve the correct problem, we cannot add too few nodes to the feedback set. If we set $y _ { v } = 1$ for a node which should be part of the feedback set, we find an energy penalty of $A$ from $H _ { A }$ , and a gain of $B$ from $H _ { B }$ . We conclude that $B < A$ is sufficient to ensure we solve the correct problem. We see that $| V | ( | V | + 1 )$ spins are required.

# 8.4. Undirected Feedback Vertex Set

The extension to undirected graphs requires a bit more care. In this case, we have to be careful because there is no a priori distinction on whether the height of one end of an edge is smaller or larger than the other – this makes the problem much more involved, at first sight. Furthermore, it is not true that a directed acyclic graph is acyclic if the orientation of edges is ignored. However, for an undirected graph, we also know that a feedback vertex set must reduce the graph to trees, although there is no longer a requirement that these trees are connected (this is called a forest). With this in mind, we find that the problem is actually extremely similar to minimal spanning tree, but without degree constraints or connectivity constraints. The new subtlety, however, is that we cannot remove edges.

To solve this problem, we do the following: introduce a binary variable $x _ { v , i }$ , which is $_ 1$ if $v$ is a vertex in any tree (anywhere in the forest) at depth $i$ , and 0 otherwise. However, to account for the fact that we may remove vertices, we will allow for $y _ { v } = 1$ if $v$ is part of the feedback vertex set, and 0 otherwise. We do a similar thing for edges: we consider $x _ { u v , i } , x _ { v u , i }$ to be defined as before when $i > 0$ . We also define the variables $y _ { u v } , y _ { v u }$ , which we take to be 1 when the ending node of the “directed” edge is in the feedback vertex set. Now, we can write down a very similar energy to the minimal spanning tree:

$$
\begin{array} { l } { { \displaystyle = { \cal A } \sum _ { v } \Bigg ( 1 - y _ { v } - \sum _ { i } x _ { v , i } \Bigg ) ^ { 2 } + { \cal A } \sum _ { u v \in { \cal E } } \Bigg ( 1 - \sum _ { i } ( x _ { u v , i } + x _ { v u , i } + y _ { u v } + y _ { v u } ) \Bigg ) ^ { 2 } + { \cal A } \sum _ { u v \in \{ i , i \} } \sum _ { i } \sum _ { u \in \{ i , i \} } \sum _ { u \in \{ i , i \} } \left( 1 - \sum _ { i } ( x _ { u v , i } + x _ { v u , i } + x _ { v v , i } - y _ { v u , i } ) \right) ^ { 2 } } } \\ { { \displaystyle ~ + { \cal A } \sum _ { v } \sum _ { i > 0 } \Bigg ( x _ { v , i } - \sum _ { u : u v \in { \cal E } } x _ { u v , i } \Bigg ) ^ { 2 } + { \cal A } \sum _ { u v , v u \in { \cal E } } \sum _ { i > 0 } x _ { u v , i } ( 2 - x _ { u , i - 1 } - x _ { v , i } ) } } \end{array}
$$

The changes are as follows: we no longer constrain only 1 node to be the root, or constrain the degree of a vertex – however, we have to add a new term to ensure that edges are only ignored in the tree constraint if they point to a node in the feedback set. We then add

$$
H _ { B } = B \sum _ { v } y _ { v }
$$

with $B < A$ required so that the $A$ constraints are never violated. This counts the number of nodes in the feedback set, so thus $H$ is minimized when $H _ { B }$ is smallest – i.e., we have to remove the fewest number of nodes. The number of spins required is $( | E | + | V | ) [ ( | V | + 3 ) / 2 ]$ .13

The recent paper [54] has a more efficient implementation of a mapping, for use in understanding random ensembles of this problem by the replica method. Unfortuntaely, this technique is not efficient for AQO; the Hamiltonian contains $N$ -body terms.

# 8.5. Feedback Edge Set

For a directed graph, the feedback edge set problem is to find the smallest set of edges $F \subset E$ such that $( V , E - F )$ is a directed acyclic graph. It is known to be NP-hard [18].14 Our solution will be somewhat similar to the directed feedback vertex set. We place a binary variable $y _ { u v }$ on each edge, which is 1 if $u v \notin F$ , and define $x _ { u v , i }$ to be 1 if both $y _ { u v } = 1$ and the height of node $u$ is $i$ . We also add a binary variable $x _ { v , i }$ , as for the feedback vertex set. Our constraint energy must then enforce that: each vertex and included edge has a well-defined height, and that each edge points from a lower height to a higher height:

$$
\sum _ { v } \left( 1 - \sum _ { i } x _ { v , i } \right) ^ { 2 } + A \sum _ { u v \in E } \left( y _ { u v } - \sum _ { i } x _ { u v , i } \right) ^ { 2 } + A \sum _ { u v } \sum _ { i } x _ { u v , i } \left( 2 - x _ { u , i } - \sum _ { j > i } x _ { v , j } \right) ^ { 2 } ,
$$

We then use

$$
H _ { B } = B \sum _ { u v \in E } ( 1 - y _ { u v } )
$$

to count the number of edges in $F - \mathrm { i t }$ is minimized when this number is smallest. As before, one needs $B < A$ to encode the correct problem. The number of spins required is $| E | + | V | ( | V | + | E | )$ .

# 9. Graph Isomorphisms

Graphs $G _ { 1 }$ and $G _ { 2 }$ , with $N$ vertices each, are isomorphic if there is a labeling of vertices $1 , \ldots , N$ in each graph such that the adjacency matrices for the graphs is identical. More carefully: any graph $G = ( V , E )$ , with vertices labeled as $1 , \ldots , N$ , has an $N \times N$ adjacency matrix $\mathsf { A }$ with

$$
A _ { i j } = \left\{ \begin{array} { l l } { 1 } & { ( i j ) \in E , } \\ { 0 } & { ( i j ) \notin E . } \end{array} \right. ,
$$

which contains all information about the edge set $E$ . Let $\mathsf { A } _ { 1 , 2 }$ be the adjacency matrices of graphs $G _ { 1 , 2 }$ If there is a permutation matrix $\mathsf { P }$ such that $\mathsf { A } _ { 2 } = \mathsf { P } ^ { \mathsf { T } } \mathsf { A } _ { 1 } \mathsf { P }$ , then we say $G _ { 1 , 2 }$ are isomorphic.

The question of whether two graphs $G _ { 1 } = ( V _ { 1 } , E _ { 1 } )$ and $G _ { 2 } = ( V _ { 2 } , E _ { 2 } )$ are isomorphic is believed to be hard, but its classification into a complexity class is still a mystery [55]. Since it is (in practice) a hard problem, let us nonetheless describe an Ising formulation for it. An isomorphism is only possible if $| V _ { 1 } | = | V _ { 2 } | \equiv N$ , so we will restrict ourselves to this case, and without loss of generality, we label the vertices of $G _ { 1 }$ with $1 , \ldots , N$ .

We write this as an Ising model as follows. Let us describe a proposed isomorphism through binary variables $x _ { v , i }$ which is $1$ if vertex $v$ in $G _ { 2 }$ gets mapped to vertex $i$ in $G _ { 1 }$ . The energy

$$
H _ { A } = A \sum _ { v } \left( 1 - \sum _ { i } x _ { v , i } \right) ^ { 2 } + A \sum _ { i } \left( 1 - \sum _ { v } x _ { v , i } \right) ^ { 2 }
$$

ensures that this map is bijective. We then use an energy

$$
H _ { B } = B \sum _ { i j \notin E _ { 1 } } \sum _ { u v \in E _ { 2 } } x _ { u , i } x _ { v , j } + B \sum _ { i j \in E _ { 1 } } \sum _ { u v \notin E _ { 2 } } x _ { u , i } x _ { v , j }
$$

to penalize a bad mapping: i.e. an edge that is not in $G _ { 1 }$ is in $G _ { 2 }$ , or an edge that is in $G _ { 1 }$ is not in $G _ { 2 }$ .   
As usual, assume $A , B > 0$ . If the ground state of this Hamiltonian has $H = 0$ , there is an isomorphism.   
$N ^ { 2 }$ spins are required.

An approximate algorithm that uses quantum annealing to distinguish between non-isomorphic graphs via the spectra of graph-dependent Hamiltonians was presented in [56].

# 10. Conclusions

The focus of research into AQO has essentially been on NP-complete/hard problems, because the Ising model is NP-hard, and because computer scientists have struggled to find efficient ways of solving these problems. In this paper, we have presented strategies for mapping a wide variety of NP problems to Ising spin glasses, exemplified by a demonstration of a glass for each of Karp’s 21 NP-complete problems. It is an open question the extent to which AQO will help provide efficient solutions for these problems, whether these solutions are exact or approximate.

However, physicists are interested in building a universal quantum computer which is capable of solving much more than just Ising models. As an example, a universal quantum computer would also reduce the time for searching an unsorted list of $N$ items from $\mathrm { O } ( N )$ to $\mathrm { O } ( { \sqrt { N } } )$ [57]. This would be incredibly useful for many practical applications, despite the fact that searching is an easy linear time algorithm. Analogously, it may be the case that there exists a family of “easy” problems which AQO can solve in polynomial time, yet more efficiently than a classical polynomial time algorithm. This statement may even be true with Ising-implementing AQO hardware, although if so it is not obvious.

It is certainly the case that an AQO-implementing device can be used to solve easy problems. Consider the simple problem of finding the largest integer in a list $\pi _ { 1 } , \ldots , \pi _ { N }$ (this is the searching algorithm that a universal quantum computer can perform efficiently). Introducing binary variables $x _ { i }$ for $i = 1 , \ldots , N$ , the Ising model

$$
H = A \left( 1 - \sum _ { i } x _ { i } \right) ^ { 2 } - B \sum _ { i } n _ { i } x _ { i }
$$

for $A > B \operatorname* { m a x } ( n _ { i } )$ solves this problem. In fact, this problem looks somewhat like an instance of the random field Ising model on a complete graph, and yet this has a very simple $\mathrm { O } ( N )$ classical algorithm. It would surely take longer to program this algorithm into a quantum device than to solve the problem itself.

The above example demonstrates that sometimes the “hardness” of a problem can be deceptive – one can phrase something that is easy in a way which makes it seem hard. It is worth discussing more closely the hardness of NP problems, because it turns out that sometimes, NP problems can be easier than they first appear. To be NP-complete but not $\mathrm { P }$ (if $\mathrm { P \neq N P }$ ) one only needs a small family of instances of the problem to be unsolvable in polynomial time by a deterministic algorithm. However, typical instances may not be so hard. Many popular NP problems can almost surely be solved exactly in polynomial time on large random instances [58, 59],15 and there exist randomized algorithms for some NP problems which can get arbitrarily close to a solution with arbitrarily low failure probability in polynomial time [60, 61] (though multiplicative coefficients or polynomial exponents must diverge as the failure probability and/or error on determining the ground state tends to zero, if $\mathrm { P \neq N P }$ ). In addition, popular algorithms in P, like matrix decomposition, may serve as the bottlenecks of practical computations, and should not be thought of as “easy”. Typical instances approach the asymptotic bounds on worst-case runtimes, in contrast to the case for some NP problems; many recent developments focus on randomized algorithms [62, 63, 64].

The Hamiltonians of this paper may be deceptively “hard” – this can mean that they involve too many spins. Another possibility is that these Hamiltonians have small spectral gaps, and that alternative choices have much larger spectral gaps – this is a question we have not addressed at all in this paper. Studying how to simplify quantum algorithms, and more importantly increase energy gaps (and thus reduce $T$ ), even by constant factors, is a much needed endeavor.

# Acknowledgements

A.L. is supported by the Smith Family Graduate Science and Engineering Fellowship at Harvard.

He would like to thank Robert Lucas for pointing out that a compendium of ways to map famous NP problems to Ising glasses was lacking, Jacob Biamonte for encouraging publication, and Vicky Choi,

Jacob Sanders, Federico Spedalieri, John Tran, and especially the reviewers, for many helpful comments on AQO and computer science.

# References

[1] E. Farhi, J. Goldstone, S. Gutmann, J. Lapan, A. Lundgren, and D. Preda. “A quantum adiabatic evolution algorithm applied to random instances of an NP-complete problem”, Science 292 472 (2001) [quant-ph/0104129].   
[2] A. Das and B.K. Chakrabarti. “Colloquium: Quantum annealing and analog quantum computation”, Reviews of Modern Physics 80 1061 (2008) [0801.2193].   
[3] B. Altshuler, H. Krovi, and J. Roland. “Anderson localization makes adiabatic quantum optimization fail”, Proceedings of the National Academy of Sciences 107 12446 (2010) [0912.0746].   
[4] N.G. Dickson and M.H.S. Amin. “Does adiabatic quantum optimization fail for NP-complete problems?”, Physical Review Letters 106 050502 (2011) [1010.0669].   
[5] V. Bapst, L. Foini, F. Krzakala, G. Semerjian, and F. Zamponi. “The quantum adiabatic algorithm applied to random optimization problems: the quantum spin glass perspective”, Physics Reports 523 127 (2013) [1210.0811].   
[6] E. Farhi, J. Goldstone, D. Gosset, S. Gutmann, and P. Shor. “Unstructured randomness, small gaps and localization”, Quantum Computation and Information 11 840 (2011) [1010.0009].   
[7] E. Farhi, D. Gosset, I. Hen, A.W. Sandvik, P. Shor, A.P. Young, and F. Zamponi. “The performance of the quantum adiabatic algorithm on random instances of two optimization problems on regular hypergraphs”, Physical Review A86 052334 (2012) [1208.3757].   
[8] I. Hen and A.P. Young. “Exponential complexity of the quantum adiabatic algorithm for certain satisfiability problems”, Physical Review E84 061152 (2011) [1109.6872].   
[9] T. Jorg, F. Krzakala, G. Semerjian, and F. Zamponi. “First-order transitions and the performance of quantum algorithms in random optimization problems”, Physical Review Letters 104 207206 (2010) [0911.3438].   
[10] G.E. Santoro, R. Martonak, E. Tosatti, and R. Car. “Theory of quantum annealing of an Ising spin glass”, Science 295 2427 (2002) [cond-mat/0205280].   
[11] S. Boixo, T. Albash, F.M. Spedalieri, N. Chancellor, and D.A. Lidar. “Experimental signature of programmable quantum annealing”, Nature Communications 4 3067 (2013) [1212.1739].   
[12] S. Boixo, T.F. Rønnow, S.V. Isakov, Z. Wang, D. Wecker, D.A. Lidar, J.M. Martinis, and M. Troyer. “Quantum annealing with more than one hundred qubits” [1304.4595].   
[13] M.W. Johnson et. al. “Quantum annealing with manufactured spins”, Nature 473 194 (2011).   
[14] J.D. Whitfield, M. Faccin, and J.D. Biamonte. “Ground state spin logic”, Europhysics Letters 99 57004 (2012) [1205.1742].   
[15] J.D. Biamonte and P.J. Love. “Realizable Hamiltonians for universal adiabatic quantum computers”, Physical Review A78 012352 (2008) [0704.1287].   
[16] S. Bravyi, D.P. DiVincenzo, R.I. Oliveira, and B.M. Terhal. “The complexity of stoquastic local Hamiltonian problems”, Quantum Information and Computation 8 0361 (2008) [quant-ph/0606140].   
[17] F. Barahona. “On the computational complexity of Ising spin glass models”, Journal of Physics A15 3241 (1982).   
[18] R.M. Karp. “Reducibility among combinatorial problems”, in Complexity of Computer Computations, ed. R.E. Miller, J.W. Thatcher and J.D. Bohlinger, 85 (1972).   
[19] M.R. Garey and D.S. Johnson. Computers and Intractability: a Guide to the Theory of NP-Completeness (1979).   
[20] Y. Fu and P.W. Anderson. “Application of statistical mechanics to NP-complete problems in combinatorial optimisation”, Journal of Physics A19 1605 (1986).   
[21] M. M´ezard, G. Parisi, and M. Virasoro. Spin Glass Theory and Beyond (1987).   
[22] A.K. Hartmann and M. Weigt. Phase Transitions in Combinatorial Optimization Problems: Basics, Algorithms and Statistical Mechanics (2006).   
[23] S. Kirkpatrick, C.D. Gelatt, and M.P. Vecchi. “Optimization by simulated annealing”, Science 220 671 (1983).   
[24] M. M´ezard and A. Montanari. Information, Physics and Computation (2009).   
[25] J.D. Bryngelson and P.G. Wolynes. “Spin glasses and the statistical mechanics of protein folding”, Proceedings of the National Academy of Sciences 84 7524 (1987).   
[26] B. Berger and T. Leighton. “Protein folding in the hydrophobic-hydrophilic (HP) model is NPcomplete”, Journal of Computational Biology 5 27 (1998).   
[27] J.J. Hopfield. “Neural networks and physical systems with emergent collective computational abilities”, Proceedings of the National Academy of Sciences 79 2554 (1982).   
[28] J-P. Bouchaud. “Crises and collective socio-economic phenomena: simple models and challenges”, Journal of Statistical Physics 151 567 (2013) [1209.0453].   
[29] A. Lucas and C.H. Lee. “Multistable binary decision making on networks”, Physical Review E87 032806 (2013) [1210.6044].   
[30] N. Xu, J. Zhu, D. Lu, X. Zhou, X. Peng, and J. Du. “Quantum factorization of 143 on a dipolarcoupling nuclear magnetic resonance system”, Physical Review Letters 108 130501 (2012); Erratum 109 269902E (2012) [1111.3726].   
[31] Z. Bian, F. Chudak, W.G. Macready, L. Clark, and F. Gaitan. “Experimental determination of Ramsey numbers”, Physical Review Letters 111 130505 (2013) [1201.1842].   
[32] A. Perdomo-Ortiz, N. Dickson, M. Drew-Brook, G. Rose, and A. Aspuru-Guzik. “Finding lowenergy conformations of lattice protein models by quantum annealing”, Scientific Reports 2 571 (2012) [1204.5485].   
[33] R. Babbush, A. Perdomo-Ortiz, B. O’Gorman, W. Macready, and A. Aspuru-Guzik. “Construction of energy functions for lattice heteropolymer models: a case study in constraint satisfaction programming and adiabatic quantum optimization”, [1211.3422].   
[34] H. Neven, G. Rose, and W.G. Macready. “Image recognition with an adiabatic quantum computer. I. Mapping to quadratic unconstrained binary optimization” [0804.4457].   
[35] V. Denchev, N. Ding, S.V.N. Vishwanathan, and H. Neven. “Robust classification with adiabatic quantum optimization”, Proceedings of the 29 $^ \mathrm { t h }$ International Conference on Machine Learning 863 (2012) [1205.1148].   
[36] E. Boros and P.L. Hammer. “The max-cut problem and quadratic 0-1 optimization; polyhedral aspects, relaxations and bounds”, Annals of Operations Research 33 151 (1991).   
[37] E. Boros and P.L. Hammer. “Pseudo-Boolean optimization”, Discrete Applied Mathematics 123 155 (2002).   
[38] E. Boros, P.L. Hammer, and G. Tavares. “Preprocessing of unconstrained quadratic binary optimization”, RUTCOR Research Report 10-2006 (2006).   
[39] A. Billionnet and B. Jaumard. “A decomposition method for minimizing quadratic pseudo-Boolean functions”, Operations Research Letters 8 161 (1989).   
[40] J.D. Biamonte. “Non-perturbative $k$ -body to two-body commuting conversion Hamiltonians and embedding problem instances into Ising spins”, Physical Review A77 052331 (2008) [0801.3800].   
[41] R. Babbush, B. O’Gorman, and A. Aspuru-Guzik. “Resource efficient gadgets for compiling adiabatic quantum optimization problems”, Annalen der Physik 525 877 (2013) [1307.8041].   
[42] X. Peng, Z. Liao, N. Xu, G. Qin, X. Zhou, D. Suter, and J. Du. “A quantum adiabatic algorithm for factorization and its experimental implementation”, Physical Review Letters 101 220405 (2008) [0808.1935].   
[43] V. Choi. “Minor-embedding in adiabatic quantum computation: I. the parameter setting problem”, Quantum Information Processing 7 193 (2008) [0804.4884].   
[44] V. Choi. “Minor-embedding in adiabatic quantum computation: II. Minor-universal graph design”, Quantum Information Processing 10 343 (2011) [1001.3116].   
[45] C. Klymko, B.D. Sullivan, and T.S. Humble. “Adiabatic quantum programming: minor embedding with hard faults”, Quantum Information Processing (accepted) [1210.8395].   
[46] N. Alon, M. Krivelevich, and B. Sudakov. “Finding a large hidden clique in a random graph”, Random Structures & Algorithms 13 457 (1998).   
[47] A.M. Childs, E. Farhi, J. Goldstone, and S. Gutmann. “Finding cliques by quantum adiabatic evolution”, Quantum Information and Computation 2 181 (2002) [quant-ph/0012104].   
[48] A. Schrijver. Theory of Integer and Linear Programming (1998).   
[49] V. Choi. “Adiabatic quantum algorithms for the NP-complete maximum-weight independent set, exact cover and 3SAT problems”, [1004.2226].   
[50] H. Kellerer and U. Pferschy. Knapsack Problems (2004).   
[51] F-Y. Wu. “The Potts model”, Reviews of Modern Physics 54 1 (1982).   
[52] K. Appel and W. Haken. “Every planar map is four colorable. I. Discharging”, Illinois Journal of Mathematics 21 429 (1977).   
[53] K. Appel, W. Haken, and J. Koch. “Every planar map is four colorable. II. Reducibility”, Illinois Journal of Mathematics 21 491 (1977).   
[54] H-J. Zhou. “Spin glass approach to the feedback vertex set problem”, European Physical Journal B86 455 (2013) [1307.6948].   
[55] D.S. Johnson. “The NP-completeness column”, ACM Transactions on Algorithms 1 160 (2005).   
[56] I. Hen and A.P. Young. “Solving the graph isomorphism problem with a quantum annealer”, Physical Review A86 042310 (2012) [1207.1712].   
[57] M.A. Nielsen and I.A. Chuang. Quantum Computation and Quantum Information (2000).   
[58] R. Beier and B. V¨ocking. “Random knapsack in expected polynomial time”, Proceedings of the 35 $^ { t h }$ Annual ACM Symposium on the Theory of Computing 232 (2004).   
[59] M. Krivelevich and D. Vilenchik. “Solving random satisfiable 3CNF formulas in expected polynomial time”, Proceedings of the $1 7 ^ { t h }$ Annual ACM-SIAM Symposium on Discrete Algorithms 454 (2006).   
[60] M. Dyer, A. Frieze, and R. Kannan. “A random polynomial-time algorithm for approximating the volume of convex bodies”, Journal of the ACM 38 1 (1991).   
[61] V.V. Vazirani. Approximation Algorithms (2003).   
[62] E. Liberty, F. Woolfe, P.G. Martinsson, V. Rokhlin, and M. Tygert. “Randomized algorithms for the low-rank approximation of matrices”, Proceedings of the National Academy of Sciences 104 20167 (2007).   
[63] N. Halko, P. Martinsson, and J.A. Tropp. “Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions ”, SIAM Review 53 217 (2011) [0909.4061].   
[64] A. Lucas, M. Stalzer, and J. Feo. “Parallel implementation of a fast randomized algorithm for the decomposition of low rank matrices”, Parallel Processing Letters (accepted) [1205.3830].