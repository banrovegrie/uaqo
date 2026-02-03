# Spatial search by quantum walk is optimal for almost all graphs

Shantanav Chakraborty $^ { 1 , 2 , }$ ,∗, Leonardo Novo $^ { 1 , 2 , }$ ∗, Andris Ambainis $^ 3$ , and Yasser Omar $^ { 1 , 2 }$   
$^ { 1 }$ Physics of Information and Quantum Technologies Group, Instituto de Telecomunica¸c˜oes, Portugal $^ 2$ Instituto Superior T´ecnico, Universidade de Lisboa, Portugal and $^ 3$ Faculty of Computing, University of Latvia ( $^ *$ both authors have equal contribution) (Dated: 11th March, 2016)

The problem of finding a marked node in a graph can be solved by the spatial search algorithm based on continuous-time quantum walks (CTQW). However, this algorithm is known to run in optimal time only for a handful of graphs. In this work, we prove that for Erd¨os-Renyi random graphs, i.e. graphs of $n$ vertices where each edge exists with probability $_ p$ , search by CTQW is almost surely optimal as long as $p \geq \log ^ { 3 / 2 } ( n ) / n$ . Consequently, we show that quantum spatial search is in fact optimal for almost all graphs, meaning that the fraction of graphs of $n$ vertices for which this optimality holds tends to one in the asymptotic limit. We obtain this result by proving that search is optimal on graphs where the ratio between the second largest and the largest eigenvalue is bounded by a constant smaller than 1. Finally, we show that we can extend our results on search to establish high fidelity quantum communication between two arbitrary nodes of a random network of interacting qubits, namely to perform quantum state transfer, as well as entanglement generation. Our work shows that quantum information tasks typically designed for structured systems retain performance in very disordered structures.

PACS numbers: 03.67.Ac, 03.67.Lx, 03.67.Hk

Quantum walks provide a natural framework for tackling the spatial search problem of finding a marked node in a graph of $n$ vertices. In the original work of Childs and Goldstone [1], it was shown that continuous-time quantum walks can search on complete graphs, hypercubes and lattices of dimension larger than four in $\mathcal { O } ( \sqrt { n } )$ time, which is optimal. More recently, new instances of graphs have been found where spatial search works optimally. These examples show that global symmetry, regularity and high connectivity are not necessary for the optimality of the algorithm [2–4]. However, it is not known how general is the class of graphs for which spatial search by quantum walk is optimal.

Here we address the following question: If one picks at random a graph from the set of all graphs of $n$ nodes, can one find a marked node in optimal time using quantum walks? We show that the answer is almost surely yes. Moreover, we adapt the spatial search algorithm to protocols, for state transfer and entanglement generation between arbitrary nodes of a network of interacting qubits, that work with high fidelity for almost all graphs, for large $n$ (nodes and vertices are used interchangeably throughout the paper). Thus, besides showing that spatial search by quantum walk is optimal in a very general scenario, we also show that other important quantum information tasks, typically designed for ordered systems, can be accomplished efficiently in very disordered structures.

We obtain our results by studying the spatial search problem in Erd¨os-Renyi random graphs, i.e. graphs of $n$ vertices where an edge between any two vertices exists with probability $p$ independently of all other edges, typically denoted as $G ( n , p )$ [5, 6]. Note that our approach is different from the quantum random networks of non-interacting qubits defined in [7], where two nodes are connected if they share a maximally entangled state, having in view long-distance quantum communication. Also, in Refs. [8, 9], the authors compare the dynamics of classical and quantum walks on Erd¨os-Renyi graphs and other complex networks, although with a different perspective from our work.

In our work, we show that search is optimal on $G ( n , p )$ with probability that tends to one as $n$ tends to infinity, as long as $p \geq \log ^ { 3 / 2 } ( n ) / n$ . It can be demonstrated that when $p = 1 / 2$ , $G ( n , 1 / 2 )$ is a graph picked at random from the set of all graphs of $n$ nodes in an unbiased way, i.e. each graph is picked with equal probability. This allows us to conclude that spatial search by quantum walk is optimal for almost all graphs from this set. To obtain this result, we prove a sufficient condition regarding the adjacency matrix of graphs where search is optimal: the eigenstate corresponding to its largest eigenvalue must be sufficiently delocalized and the ratio between the second largest and the largest eigenvalues must be bounded by a constant smaller than 1.

This general result also allows us to prove that search is optimal for graphs sampled uniformly from the set of all regular graphs, also known as random regular graphs. Thus, this leads us to conclude that spatial search by quantum walk is optimal for almost all regular graphs.

A sufficient condition for optimal quantum search $-$ Let $G$ be a graph with a set of vertices $V = \{ 1 , \ldots , n \}$ . We consider the Hilbert space spanned by the localized quantum states at the vertices of the graph $\mathcal { H } = \operatorname { s p a n } \{ | 1 \rangle , \dotsc , | n \rangle \}$ , and the following search Hamiltonian

$$
{ \cal H } _ { G } = - \left| w \right. \left. w \right| - \gamma A _ { G } ,
$$

where $| w \rangle$ corresponds to the solution of the search problem, $\gamma$ is a real number and $A _ { G }$ is the adjacency matrix of a graph $G$ [1]. We say that quantum search by continuous time quantum walk is optimal on a graph $G$ if there is an initial state $| \psi _ { 0 } \rangle$ , irrespective of $w$ , and a value of $\gamma$ such that after a time $T = \mathcal { O } ( { \sqrt { n } } )$ [10], the probability of finding the solution upon a measurement in the vertex basis is $| \langle w | e ^ { - i H _ { G } t } | \psi _ { 0 } \rangle | ^ { 2 } = \mathcal { O } ( 1 )$ . The initial state $| \psi _ { 0 } \rangle$ is usually chosen to be the equal superposition of all vertices, i.e. the state $\begin{array} { r } { \left| s \right. = \sum _ { i = 1 } ^ { n } \left| i \right. / \sqrt { n } } \end{array}$ , since it is not biased towards any vertex of the graph. We start by proving the following general lemma regarding the spectral properties of $A _ { G }$ and the optimality of search:

Lemma 1 Let $H _ { 1 }$ be a Hamiltonian with eigenvalues $\lambda _ { 1 } \geq \lambda _ { 2 } \geq . . . \geq \lambda _ { k }$ (satisfying $\lambda _ { 1 } = 1$ and $| \lambda _ { i } | \le c < 1$ for all $i > 1$ ) and eigenvectors $| \boldsymbol { v } _ { 1 } \rangle = | \boldsymbol { s } \rangle$ , $\left| v _ { 2 } \right. , \ldots , \left| v _ { k } \right.$ and let $H _ { 2 } ~ = ~ \vert w \rangle \left. w \vert \right.$ with $| \langle w | s \rangle | = \epsilon$ . For an appropriate choice of $r = O ( 1 )$ , applying the Hamiltonian $( 1 + r ) H _ { 1 } + H _ { 2 }$ to tn a s ing st with $| \boldsymbol { v } _ { 1 } \rangle = | s \rangle$ $\Theta ( 1 / \epsilon )$ $| f \rangle$ $\begin{array} { r } { | \langle w | f \rangle | ^ { 2 } \geq \frac { 1 - c } { 1 + c } - o ( 1 ) } \end{array}$ $I$

Thus, if $\lambda _ { 1 } ^ { A } \ \ge \ \lambda _ { 2 } ^ { A } \ \ge \ . . . \ge \ \lambda _ { n } ^ { A }$ are the eigenvalues of the adjacency matrix $A _ { G }$ , we choose $\gamma = 1 / \lambda _ { 1 } ^ { A }$ and consequently, $H _ { 1 } ~ = ~ \gamma A _ { G }$ . If $| s \rangle$ is an eigenstate of $A _ { G }$ corresponding to its largest eigenvalue $\lambda _ { 1 } ^ { A }$ , and since $\left| \langle w | s \rangle \right| = 1 / { \sqrt { n } }$ , we have that search is optimal as long as $\lambda _ { 2 } ^ { A } / \lambda _ { 1 } ^ { A } \ \le \ c \ < \ 1$ , following Lemma 1. We will see that Erd¨os-Renyi graphs and random regular graphs fulfil this property, leading to the conclusion that search is optimal for almost all graphs and also for almost all regular graphs (the latter is discussed in Section $\mathrm { I I }$ of Supplemental Material).

In fact, Lemma 1 implies that for any regular graph having a constant normalized algebraic connectivity, quantum search is optimal [11]. This is in contrast to Ref. [4] where two examples of regular graphs [12] with low normalized algebraic connectivity are given, such that quantum search is optimal on one and non-optimal on the other. This result showed that normalized algebraic connectivity is not a necessary condition for fast quantum search: when connectivity is low, search can be fast or slow depending on the graph. On the other hand, Lemma 1 proves that high connectivity is indeed a sufficient condition.

Quantum search on Erd¨os-Renyi random graphs – Let us consider a graph $G ( n )$ with a set of vertices $V = \{ 1 , \ldots , n \}$ . We restrict ourselves to simple graphs, i.e. graphs which do not contain self-loops or multiple edges connecting the same pair of vertices. The maximum number of edges that a simple graph $G ( n )$ can have is $\begin{array} { r } { N \ = \ \binom { n } { 2 } } \end{array}$ . Thus, there are $\textstyle { \binom { N } { M } }$ graphs of $M$ edges and the total number of (labelled) graphs is $\begin{array} { r } { \sum _ { M = 0 } ^ { N } { \binom { N } { M } } = 2 ^ { N } } \end{array}$ [13]. Now let us consider the random graph model $G ( n , p )$ , a graph with $n$ vertices where we have an edge between any two vertices with probability $p$ , independently of all the other edges [5, 6, 14]. In this model, a graph $G _ { 0 }$ with $M$ edges appears with probability $P \{ G ( n , p ) = G _ { 0 } \} = p ^ { M } ( 1 - p ) ^ { N - M }$ . In particular, if we consider the case $p = 1 / 2$ , each of the $2 ^ { N }$ graphs appears with equal probability $P ~ = ~ 2 ^ { - N }$ . In their seminal papers, Erd¨os and Renyi introduced this model of random graphs and studied the probability of a random graph to possess a certain property $Q$ [5, 6]. They studied properties like connectedness of the graph, the probability that a certain subgraph is present, etc. They introduced the terminology stating that almost all graphs have a property $Q$ if the probability that a random graph $G ( n , p )$ has $Q$ goes to $1$ as $n \to \infty$ . Equivalently, it can be stated that $G ( n , p )$ almost surely has property $Q$ . Interestingly, certain properties of random graphs arise suddenly for a certain critical probability $p = p _ { c }$ , where this probability depends typically on $n$ . More precisely, if $p ( n )$ grows faster than $p _ { c } ( n )$ , the probability that the random graph has property $Q$ goes to $1$ in the asymptotic limit, whereas if it grows slower than $p _ { c } ( n )$ it goes to $0$ . For example above the percolation threshold, i.e. when $p > \log ( n ) / n$ the graph is almost surely connected, whereas if $p < \log ( n ) / n$ the graph has almost surely isolated nodes.

In this work, we are interested in the threshold value of $p$ for which quantum search becomes optimal, i.e. a marked vertex from the graph can be found in $\mathcal { O } ( \sqrt { n } )$ time. We consider the search Hamiltonian in Eq. (1) for Erd¨os-Renyi random graphs ${ \cal H } _ { G ( n , p ) } = - | w \rangle \langle w | -$ $\gamma A _ { G ( n , p ) }$ . In order to apply Lemma $^ { 1 }$ we need to know the largest eigenvalue of $A _ { G ( n , p ) }$ , which we denote as $\lambda _ { 1 } ^ { A }$ , its corresponding eigenstate $\left| v _ { 1 } \right.$ and the second largest eigenvalue of $A _ { G ( n , p ) }$ denoted as $\lambda _ { 2 } ^ { A }$ . It was shown in Ref. [15] that the highest eigenvalue, $\lambda _ { 1 } ^ { A }$ is a random variable whose probability distribution converges to a Gaussian distribution with mean $n p$ and standard deviation $\sqrt { p ( 1 - p ) }$ , as $n  \infty$ . The corresponding eigenstate, $\left| v _ { 1 } \right.$ tends almost surely to $\begin{array} { r } { | s \rangle = 1 / \sqrt { n } \sum _ { i = 1 _ { . } } ^ { n } | i \rangle } \end{array}$ . For a more detailed analysis of the convergence of $\left| v _ { 1 } \right.$ to $| s \rangle$ , refer to Lemma 2 in Section III of Supplemental Material. It is also possible to obtain an upper bound on the second highest eigenvalue, $\lambda _ { 2 } ^ { A }$ from the results of Ref. [15] which applies to random symmetric matrices. In fact in Ref. [16], a tighter bound on $\lambda _ { 2 } ^ { A }$ is provided as $n \to \infty$ , given by

$$
\lambda _ { 2 } ^ { A } = 2 \sqrt { n p } + \mathcal { O } ( ( n p ) ^ { 1 / 4 } \log ( n ) )
$$

We see that as long as $p \geq \log ^ { 4 / 3 } ( n ) / n$ , the ratio $\lambda _ { 2 } ^ { A } / \lambda _ { 1 } ^ { A }$ is bounded by a constant. However, as can be seen in Section III of Supplemental Material, in order to ensure that $\left| v _ { 1 } \right.$ converges to $| s \rangle$ , almost surely, we choose the critical value of probability for search to be optimal as $p \ge \log ^ { 3 / 2 } ( n ) / n$ . In fact, in the asymptotic limit, $\lambda _ { 2 } ^ { A } / \lambda _ { 1 } ^ { A } \to 0$ , and the eigenstates corresponding to the two lowest eigenvalues of $H _ { G ( n , p ) }$ are

$$
| \lambda _ { \pm } \rangle \approx \frac { | w \rangle \pm | s _ { \bar { w } } \rangle } { \sqrt { 2 } } ,
$$

where $\left| { s _ { \bar { w } } } \right.$ is the equal superposition of all the vertices other than the solution state $| w \rangle$ . The probability of

success is

$$
P _ { w } ( t ) = | \left. w \right| \exp ( - i H _ { G ( n , p ) } t ) | s \rangle | ^ { 2 } = \sin ^ { 2 } \left( \frac { t } { \sqrt { n } } \right) .
$$

To confirm these theoretical predictions we plot, on the left side of Fig. 1 a)-c), the approximate probability $P _ { w } ( t )$ from Eq. (4) (in red) and the exact solution calculated numerically (in blue) for $n = 1 0 0 0$ and $p = 0 . 1 , 0 . 0 1 , 0 . 0 0 2$ . On the right side, we plot the spectrum of the respective Hamiltonians. We observe, as expected, that the larger the gap between the two lowest eigenvalues and the bulk of the spectrum, the better is the approximation given by Eq. (4) for the probability of success of search. As this gap disappears, close to the percolation threshold, the eigenstates corresponding to the two lowest eigenvalues do not follow Eq. (3) and will mix randomly with the subspace orthogonal to $| w \rangle$ and $\left| s _ { \bar { w } } \right.$ . At this point, since we are close to the percolation threshold, the graph is expected to have some isolated components and the algorithm breaks (see Fig. 1 c)).

So far we have made the choice $\gamma = 1 / \lambda _ { 1 } ^ { A }$ , and assumed that we know the value of the random variable $\lambda _ { 1 } ^ { A }$ . In fact, its standard deviation is small enough so that it is sufficient to know its mean, which is equal to $n p$ , i.e we can choose $\gamma = 1 / ( n p )$ , in order to prove that search is optimal almost surely. We prove this in Section IV of Supplemental Material, using tools of degenerate perturbation theory. These tools are also useful to design protocols for performing optimal state transfer and entanglement generation in Erd¨os-Renyi graphs, as will be explained subsequently.

State transfer with high fidelity – Quantum state transfer in spin chains [17] and spin networks [18] has been proposed as a way to establish short-range quantum channels. The problem of what structures lead to high fidelity state transfer has been of wide interest [18– 20]. Here we show that it is possible to transfer, with low control and high fidelity, a quantum state between two arbitrary non-adjacent nodes of a random network (namely, an Erd¨os-Renyi random graph). The Hamiltonian of a network of coupled spins, with an XX type interaction, conserves the number of excitations and so, in the single excitation subspace, the Hamiltonian is that of a single particle quantum walk on the same network. The graph $G ( n , p )$ can be perceived as a communication network where each node represents a party that transfers information to any of the other nodes. We assume that each party has access to a qubit and can control the local energy of the corresponding node. In order to transfer a state from node $i$ to $j$ , with fidelity that tends to $^ { 1 }$ in the asymptotic limit, the strategy is the following: all qubits are initially in state $| 0 \rangle$ , which is an eigenstate of the network; the sender (corresponding to node $i$ ) and the receiver (corresponding to node $j$ ) can tune the respective site energies of $| i \rangle$ and $| j \rangle$ to $^ { - 1 }$ , thereby making $| i \rangle$ , $| j \rangle$ and $| s \rangle$ approximately degenerate. Finally, in order to transfer a qubit from $_ i$ , the sender performs a local operation on her qubit to prepare $\left| \psi \right. = \alpha \left| 0 \right. + \beta \left| 1 \right.$ . As long as $p \geq \log ^ { 3 / 2 } ( n ) / n$ , the approximate dynamics of a quantum walk starting at $| i \rangle$ is obtained by diagonalizing the Hamiltonian

![](images/cb95c1911d5c25a910414a627c5f4fa14774dc942eeda1a276351b8b5e5b14f3.jpg)  
FIG. 1: Left side: probability of observing the solution calculated numerically (blue curve) compared to the prediction from Eq. (4) (red curve), obtained in the limit $n \to \infty$ , using degenerate perturbation theory. We fix the number of vertices $n = 1 0 0 0$ and $p = 0 . 1 , 0 . 0 1$ and 0.002 in a), b) and $\mathrm { \bf c }$ ), respectively. Right side: Spectrum of the search Hamiltonian for instances of random graphs that provide the dynamics represented on the left side. In red, the two lowest eigenvalues are shown in a) and b), which are clearly isolated from the rest of the spectrum shown in blue. In c) this does not happen since $p$ is close to $1 / n$ , which is the percolation threshold and thus the semicircle law is not valid. We see that, the larger the gap between the two lowest eigenvalues $\lambda \pm$ and the rest of the spectrum, the better is the prediction from Eq. (4) for the probability of success. When the two lowest eigenvalues are not isolated, the probability of observing the solution is low and the algorithm does not provide speed-up with respect to classical search.

$$
H _ { G ( n , p ) } ^ { \prime } = - \left| i \right. \left. i \right| - \left| j \right. \left. j \right| - \left| s _ { i \bar { j } } \right. \left. s _ { i \bar { j } } \right| - \gamma A _ { G ( n , p ) } ^ { \prime }
$$

projected onto the approximately degenerate subspace spanned by $\left\{ \left| i \right. , \left| s _ { i \bar { j } } \right. , \left| j \right. \right\}$ which is given by

$$
H _ { G ( n , p ) } ^ { \prime } = \left[ { - 1 / \sqrt { n } \begin{array} { c c c } { - 1 } & { - 1 / \sqrt { n } } & { 0 } \\ { - 1 / \sqrt { n } } & { - 1 } & { - 1 / \sqrt { n } } \\ { 0 } & { - 1 / \sqrt { n } } & { - 1 } \end{array} } \right] ,
$$

![](images/9d30619d345089adee86b9e5cdb49ded21bc7b15f57b84d906d9500c1afada9e.jpg)  
FIG. 2: Quantum state transfer in Erd¨os-Renyi random graph $G ( 1 0 0 , 0 . 2 )$ : using our protocol, the fidelity achieved for this network is $8 0 \%$ .

with $\begin{array} { r } { \left| s _ { i j } \right. = \sum _ { k \neq i , j } \left| k \right. / \sqrt { n - 2 } } \end{array}$ and $| s _ { i j } \rangle \approx | s _ { \bar { i } } \rangle \approx | s \rangle$ , where we assume that $_ i$ and $j$ are non-adjacent vertices. Thus, the dynamics is approximately the same as that of end-to-end state transfer in a chain with three spins, where perfect state transfer is possible [20] and the component of the wave function at the receiver is approxi-√ mately $| \left. j | U ( t ) | i \right. | ^ { 2 } = \sin ^ { 2 } ( t / \sqrt { 2 n } )$ . Hence, after time $T = \pi { \sqrt { n / 2 } }$ , the receiver gets $| \psi \rangle$ with fidelity 1, in the limit $n  \infty$ (see Fig. 2 for an example with finite $n$ ). The receiver can preserve this state for future use by tuning the energy of node $j$ , locally, to a value that is off-resonant with the rest of the network [21]. We conclude that high fidelity quantum state transfer can be achieved in almost all networks.

Creating Bell pairs in a random network – In quantum communication networks, entanglement is an useful resource that can be used for various tasks such as teleportation, superdense coding, cryptographic protocols, etc [22]. Here, we present a protocol to entangle arbitrary nodes in a random network based on the search Hamiltonian. Imagine that Charlie at node $| w \rangle$ wants to entangle the qubits of Alice at node $| a \rangle$ and of Bob at node $| b \rangle$ . We assume that none of the nodes $\left| w \right. , \left| a \right.$ and $| b \rangle$ are adjacent to each other. As before, $\gamma$ is chosen to be $1 / ( n p )$ . In this case, the protocol is as follows: i) Alice, Bob and Charlie tune their respective site energies to $^ { - 1 }$ , ii) Charlie tunes his nearest neighbour couplings to $\sqrt { 2 } / d _ { C }$ , where $d _ { C }$ is the degree of the node corresponding to Charlie, while the other couplings in the graph are $\gamma = 1 / n p$ . This ensures that the Hamiltonian, projected onto the approximately degenerate sub-√ space spanned by $| w \rangle$ , $\begin{array} { r } { \left| s _ { \overline { { w a b } } } \right. = \sum _ { k \neq a , b , w } \left| k \right. / \sqrt { n - 2 } } \end{array}$ and $| s _ { a b } \rangle = ( | a \rangle + | b \rangle ) / \sqrt { 2 }$ , is equal to

$$
H _ { G ( n , p ) } ^ { \prime } = \left[ { - \sqrt { 2 / n } \begin{array} { c c c } { - 1 } & { - \sqrt { 2 / n } } & { 0 } \\ { - \sqrt { 2 / n } } & { - 1 } & { - \sqrt { 2 / n } } \\ { 0 } & { - \sqrt { 2 / n } } & { - 1 } \end{array} } \right] ,
$$

in the asymptotic limit [23]. Thus, after time $T =$ $\pi \sqrt { n } / 2$ , Alice and Bob share the state $\left| s _ { a b } \right. \ : = \ : ( | a \rangle \ : +$ $\left| b \right. ) / { \sqrt { 2 } }$ , which is a Bell state. Subsequently, other Bell states may be obtained by local operations. Furthermore, Alice and Bob can preserve their Bell state by tuning the local energies of their qubits to a value that is off-resonant with the other eigenvalues of the network.

Discussion – We have shown that searching for a marked node in a graph using continuous-time quantum walks works optimally for almost all graphs. This means that, in terms of the structures on which it performs optimally, this approach to quantum spatial search is much more general than what has been shown before. Our result was obtained by proving that the algorithm is almost surely optimal for Erd¨os-Renyi random graphs $G ( n , p )$ , as long as $p \geq \log ^ { 3 / 2 } ( n ) / n$ .

As pointed out in Ref. [1], the analog version of Grover’s algorithm of Ref. [10] can be seen as a quantum walk on the complete graph. Furthermore, Erd¨os-Renyi random graph $G ( n , p )$ can be obtained from the complete graph by randomly deleting edges with probability $1 - p$ . Thus, our result can also be interpreted as showing an inherent robustness of the analog version of Grover’s algorithm to edge loss. This implies that there is a large family of random Hamiltonians that can be employed to achieve optimal quantum search. Hence, our work paves the way to understanding how this randomness would translate to the circuit model of quantum search and whether this implies an inherent robustness of the (standard) Grover’s algorithm.

Finally, we have shown that one can adapt the spatial search algorithm to design protocols for quantum state transfer and for entanglement generation between arbitrary nodes of a random network of interacting qubits. Our results show that quantum information tasks typically designed for structured systems retain performance in very disordered structures. These results could lead to further investigation on what kind of random structures appear naturally in physical systems (for example those appearing in Refs. [24, 25]) and whether they would offer a sufficient spectral gap to perform efficient and robust quantum information tasks. It would also be interesting to explore whether non-trivial quantum information tasks can be performed on other models of random networks such as scale-free networks [26].

Acknowledgements – LN, SC and YO thank the support from Funda¸c˜ao para a Ciˆencia e a Tecnologia (Portugal), namely through programmes PTDC/POPH/POCH and projects UID/EEA/50008/2013, IT/QuSim, Pro-QuNet, partially funded by EU FEDER, and from the EU FP7 projects LANDAUER (GA 318287) and PAPETS (GA 323901). Furthermore, LN and SC acknowledge the support from the DP-PMI and FCT (Portugal) through SFRH/BD/52241/2013 and SFRH/BD/52246/2013, respectively. AA thanks the support from ERC Advanced Grant MQC (320731), EU FP7 projects QALGO (600700) and RAQUEL (323970), and the Latvian State Research Programme NexIT Project No. 1.

# I. SUFFICIENT CONDITION FOR OPTIMAL QUANTUM SEARCH: PROOF OF LEMMA 1

Proof: Let us express $| w \rangle$ in the basis $\left| v _ { 1 } \right. , \left| v _ { 2 } \right. , \ldots , \left| v _ { k } \right.$ :

$$
\left| w \right. = a _ { 1 } \left| v _ { 1 } \right. + a _ { 2 } \left| v _ { 2 } \right. + \ldots + a _ { k } \left| v _ { k } \right. .
$$

We rescale $H _ { 1 }$ by $( 1 + r ) H _ { 1 } - r I$ , where $I$ is the identity matrix. With this replacement, $\left| v _ { 1 } \right.$ remains an eigenvector of $H _ { 1 }$ with an eigenvalue 1. The other eigenvalues change to $\lambda _ { i } ^ { \prime } = ( 1 + r ) \lambda _ { i } - r$ . Now, the expression

$$
\sum _ { i = 2 } ^ { k } { \frac { a _ { i } ^ { 2 } } { 1 - \lambda _ { i } } } ,
$$

after rescaling $H _ { 1 }$ as mentioned before becomes

$$
\sum _ { i = 2 } ^ { k } { \frac { a _ { i } ^ { 2 } } { 1 - \lambda _ { i } ^ { \prime } } } = \sum _ { i = 2 } ^ { k } { \frac { a _ { i } ^ { 2 } } { ( 1 + r ) ( 1 - \lambda _ { i } ) } } .
$$

As $| \lambda _ { i } | \le c$ , we have

$$
\begin{array} { l } { { \displaystyle \sum _ { i = 2 } ^ { k } \frac { a _ { i } ^ { 2 } } { ( 1 + r ) ( 1 + c ) } \le \sum _ { i = 2 } ^ { k } \frac { a _ { i } ^ { 2 } } { ( 1 + r ) ( 1 - \lambda _ { i } ) } , \mathrm { a n d } , } } \\ { { \displaystyle \sum _ { i = 2 } ^ { k } \frac { a _ { i } ^ { 2 } } { ( 1 + r ) ( 1 - \lambda _ { i } ) } \le \sum _ { i = 2 } ^ { k } \frac { a _ { i } ^ { 2 } } { ( 1 + r ) ( 1 - c ) } } } \end{array}
$$

So we choose an appropriate $r ~ \in ~ [ - \frac { c } { 1 + c } , \frac { c } { 1 - c } ]$ , such that

$$
\sum _ { i = 2 } ^ { k } { \frac { a _ { i } ^ { 2 } } { 1 - \lambda _ { i } } } = \sum _ { i = 2 } ^ { k } a _ { i } ^ { 2 } .
$$

If $| \lambda _ { i } | \le c$ , then $\lambda _ { i } ^ { \prime } \geq 0$ for $\textstyle r = - { \frac { c } { 1 + c } }$ and $\lambda _ { i } ^ { \prime } \leq 0$ for $\begin{array} { l } { r \ = \ \frac { c } { 1 - c } } \end{array}$ . In the first case, the left hand side of (13) is at least the right hand side. In the second case, the left hand side is at most the right hand side. After the nt of are i $H _ { 1 }$ byhe $( 1 + r ) H _ { 1 } - r I$ new eigenvalues. $\lambda _ { 2 } ^ { \prime } , \ldots , \lambda _ { k } ^ { \prime }$ $[ - \frac { 2 c } { 1 - c } , \frac { 2 c } { 1 + c } ]$

After we replace $H _ { 1 } + H _ { 2 }$ by $( 1 + r ) H _ { 1 } + H _ { 2 } - r I$ , we can omit the $- r I$ term (since it only affects the phase of the state). To simplify the notation, we now refer to the Hamiltonian $( 1 + r ) H _ { 1 }$ as $H _ { 1 }$ and to new eigenvalues $\lambda _ { i } ^ { \prime }$ as $\lambda _ { i }$ .

$$
\left| v \right. = b _ { 1 } \left| v _ { 1 } \right. + b _ { 2 } \left| v _ { 2 } \right. + . . . + b _ { k } \left| v _ { k } \right. .
$$

We write out the conditions for $| v \rangle$ to be an eigenvector of $H _ { 1 } + H _ { 2 }$ with an eigenvalue $\lambda$ . We have

$$
H \left| v \right. = H _ { 1 } \left| v \right. + H _ { 2 } \left| v \right. = \sum _ { i } ( b _ { i } \lambda _ { i } + a _ { i } \gamma ) \left| v _ { i } \right.
$$

where $\gamma =  w | v $ . Since we also have

$$
H \left| v \right. = \lambda \left| v \right. = \sum _ { i } \lambda b _ { i } \left| v _ { i } \right. ,
$$

we get that $\lambda b _ { i } = \lambda _ { i } b _ { i } + \gamma a _ { i }$ which is equivalent to $b _ { i } =$ ${ \frac { \gamma } { \lambda - \lambda _ { i } } } a _ { i }$ . Substituting this into $\begin{array} { r } { \gamma =  w | v  = \sum _ { i } { a _ { i } b _ { i } } } \end{array}$ gives that

$$
\sum _ { i } { \frac { a _ { i } ^ { 2 } } { \lambda - \lambda _ { i } } } = 1 .
$$

This is the condition for the eigenvalues $\lambda$ . In each of intervals $[ \lambda _ { i } , \lambda _ { i - 1 } ]$ for $i = 2 , \ldots , k$ , the left hand side is strictly decreasing from $+ \infty$ to $- \infty$ and in the interval $[ \lambda _ { 1 } , + \infty )$ , the left hand side is strictly decreasing from $+ \infty$ to $0$ . Therefore, each of these intervals contains one eigenvalue.

We are interested in the two eigenvalues $\lambda$ that are in $[ \lambda _ { 2 } , \lambda _ { 1 } ]$ and $[ \lambda _ { 1 } , + \infty )$ . (We denote these eigenvalues by $\lambda _ { - }$ and $\lambda _ { + }$ and the corresponding eigenvectors by $| v _ { - } \rangle$ and $| v _ { + } \rangle$ .) We express these eigenvalues as $\lambda = 1 + \delta$ (where $\delta$ is positive for $\lambda _ { + }$ and negative for $\lambda _ { - }$ ). By Taylor expansion, if $\delta$ is small, we have

$$
\sum _ { i = 2 } ^ { k } \frac { a _ { i } ^ { 2 } } { ( 1 + \delta ) - \lambda _ { i } } = \sum _ { i = 2 } ^ { k } \frac { a _ { i } ^ { 2 } } { 1 - \lambda _ { i } } - \sum _ { i = 2 } ^ { k } \frac { a _ { i } ^ { 2 } } { ( 1 - \lambda _ { i } ) ^ { 2 } } \delta + O ( \delta ^ { 2 } ) .
$$

Thus, the condition for eigenvalues becomes

$$
\frac { a _ { 1 } ^ { 2 } } { \delta } + \sum _ { i = 2 } ^ { k } \frac { a _ { i } ^ { 2 } } { 1 - \lambda _ { i } } - \sum _ { i = 2 } ^ { k } \frac { a _ { i } ^ { 2 } } { ( 1 - \lambda _ { i } ) ^ { 2 } } \delta + O ( \delta ^ { 2 } ) = 1 .
$$

Since the second term on the left hand side is $^ { 1 }$ , this is equivalent to

$$
\frac { a _ { 1 } ^ { 2 } } { \delta } = \sum _ { i = 2 } ^ { k } \frac { a _ { i } ^ { 2 } } { ( 1 - \lambda _ { i } ) ^ { 2 } } \delta + O ( \delta ^ { 2 } ) .
$$

which is satisfied for

$$
\delta \approx \pm \frac { a _ { 1 } } { \sqrt { \sum _ { i = 2 } ^ { k } \frac { a _ { i } ^ { 2 } } { ( 1 - \lambda _ { i } ) ^ { 2 } } } } .
$$

Since $a _ { 1 } = \epsilon$ and the denominator is of the order $\Theta ( 1 )$ , the right hand side is $\Theta ( \epsilon )$ .

We now consider the overlap $\langle s \left| v _ { + } \right.$ . We assume that $| v _ { + } \rangle$ is normalized so that $\| v _ { + } \| = 1$ . This is equivalent to $\textstyle \sum _ { i } b _ { i } ^ { 2 } = 1$ which, in turn, is equivalent to

$$
\sum _ { i } \left( \frac { \gamma } { \lambda - \lambda _ { i } } a _ { i } \right) ^ { 2 } = 1 .
$$

We can rewrite this as

$$
\frac { 1 } { \gamma } = \sqrt { \sum _ { i } \frac { a _ { i } ^ { 2 } } { ( \lambda - \lambda _ { i } ) ^ { 2 } } } .
$$

We now estimate the expression under the square root. We have

$$
{ \frac { 1 } { \gamma } } \approx { \sqrt { { \frac { a _ { 1 } ^ { 2 } } { \delta ^ { 2 } } } + \sum _ { i = 2 } ^ { k } { \frac { a _ { i } ^ { 2 } } { ( 1 - \lambda _ { i } ) ^ { 2 } } } } } \approx { \sqrt { 2 } } { \frac { a _ { 1 } } { \delta } }
$$

with the first step following by approximating $\lambda - \lambda _ { i } =$ $( 1 + \delta ) - \lambda _ { i } \approx 1 - \lambda _ { i }$ for $i > 1$ and the second step follows from (21).

This means that $\begin{array} { r } { \gamma \approx \frac { \delta } { \sqrt { 2 } a _ { 1 } } } \end{array}$ . Therefore,

$$
\langle s | v _ { + } \rangle = { \frac { \gamma a _ { 1 } } { \lambda _ { + } - 1 } } = { \frac { \gamma a _ { 1 } } { \delta } } \approx { \frac { 1 } { \sqrt { 2 } } }
$$

and

$$
\langle s | v _ { - } \rangle = \frac { \gamma a _ { 1 } } { \lambda _ { - } - 1 } = - \frac { \gamma a _ { 1 } } { \delta } \approx - \frac { 1 } { \sqrt { 2 } } .
$$

Thus, $| s \rangle$ can be approximated by $\scriptstyle { \frac { 1 } { \sqrt { 2 } } } \left( \left| v _ { + } \right. - \left| v _ { - } \right. \right)$ . Evolving the Hamiltonian $H _ { 1 } + H _ { 2 }$ for time $\begin{array} { r } { \frac { \pi } { 2 \delta } = \Theta ( \frac { 1 } { \epsilon } ) } \end{array}$ transforms $| s \rangle$ to

$$
| f \rangle \approx \frac { 1 } { \sqrt { 2 } } ( | v _ { + } \rangle + | v _ { - } \rangle ) .
$$

We have

$$
\langle w | f \rangle \approx \frac { 1 } { \sqrt { 2 } } \langle w | v _ { + } \rangle + \frac { 1 } { \sqrt { 2 } } \langle w | v _ { - } \rangle .
$$

We now consider $\langle w | v _ { + } \rangle = \gamma$ . By combining the first part of (24) with (21), we obtain that

$$
\frac { 1 } { \gamma } \approx \sqrt { 2 \sum _ { i = 2 } ^ { k } \frac { a _ { i } ^ { 2 } } { ( 1 - \lambda _ { i } ) ^ { 2 } } } .
$$

Because of (13) and $\begin{array} { r } { \lambda _ { i } \le \frac { 2 c } { 1 + c } } \end{array}$ , this is at most

$$
{ \sqrt { 2 { \frac { \sum _ { i = 2 } ^ { k } a _ { i } ^ { 2 } } { 1 - { \frac { 2 c } { 1 + c } } } } } } \leq { \sqrt { 2 { \frac { 1 } { 1 - { \frac { 2 c } { 1 + c } } } } } } = { \sqrt { \frac { 2 ( 1 + c ) } { 1 - c } } } .
$$

Therefore, γ = hw |v+i ≥ q $\gamma = \langle w | v _ { + } \rangle \geq \sqrt { \frac { 1 - c } { 2 ( 1 + c ) } }$ . Similarly, $\langle w | v _ { - } \rangle \geq$ q 1−c2(1+c) . Together with (28), this means that, up to the approximations that we made,

$$
\langle w \left| f \right. \geq { \sqrt { \frac { 1 - c } { 1 + c } } } .
$$

# II. QUANTUM SEARCH ON RANDOM REGULAR GRAPHS

A family of random graphs whose adjacency matrix has an $\mathcal { O } ( 1 )$ gap between the largest and second largest eigenvalues are the $d$ -random regular graphs, a random graph sampled uniformly from the set of all regular graphs of degree $d$ . For these graphs, the largest eigenvalue is $d$ , with the corresponding eigenvector, $| s \rangle$ . Also in Ref. [27] it has been proven that the second largest eigenvalue is $\mathcal { O } ( d ^ { 3 / 4 } )$ for $d \geq 3$ , with high probability. This way, we choose $\gamma = 1 / d$ and since $\lambda _ { 2 } ^ { A } / \lambda _ { 1 } ^ { A } = \mathcal { O } ( d ^ { - 1 / 4 } ) < 1$ , it follows from Lemma 1 that quantum search is optimal. It is interesting to note that for lattices, the lowest dimension for which search is possible in $\mathcal { O } ( \sqrt { n } )$ time is dimension five [1], which is a specific instance of a regular graph of degree ten. However, for random regular graphs search is optimal for degree three and larger.

# III. CONVERGENCE OF THE EIGENSTATECORRESPONDING TO THE MAXIMUMEIGENVALUE OF AN ERDOS-RENYI RANDOM¨GRAPH

Lemma 2 Let $A$ be the adjacency matrix of the Erd¨os-Renyi random graph $G ( n , p )$ with vertices $1 , 2 , . . . , n$ . Let $\gamma A$ represent the adjacency matrix of $G ( n , p )$ with each entry rescaled by $\gamma ~ = ~ 1 / n p$ . Also let $\begin{array} { r l } { | s \rangle } & { { } = } \end{array}$ $\textstyle \left( 1 / { \sqrt { n } } \right) \sum _ { i = 1 } ^ { n } | i \rangle$ be the equal superposition of all nodes such that $\left| s \right. = \alpha \left| v _ { 1 } \right. + \beta \left| v _ { 1 } \right. ^ { \perp }$ , where $\left| v _ { 1 } \right.$ is the eigenvector corresponding to the highest eigenvalue, $\lambda _ { 1 }$ of $\gamma A$ . Then, $\alpha \geq 1 - o ( 1 )$ almost surely for $p \geq { \frac { \log ^ { 3 / 2 } n } { n } }$ .

Proof: First we observe that from Ref. [15] that the largest eigenvalue follows a Gaussian distribution with mean 1 and standard deviation $\scriptstyle { \frac { 1 } { n } } { \sqrt { \frac { 1 - p } { p } } }$ 1−pp , i.e, λ1 ∼ $\begin{array} { r } { \mathcal { N } ( 1 , \frac { 1 } { n } \sqrt { \frac { 1 - p } { p } } ) } \end{array}$ . So if $\delta = 1 / \sqrt { n }$ , for $p \geq \log ^ { 3 / 2 } n / n$ , one can show that

$$
P r [ \lambda _ { 1 } \ge 1 - \delta ] = 1 - \frac { 1 } { 2 } \mathrm { e r f c } \Big [ \frac { \log ^ { 3 / 4 } n } { \sqrt { 2 } } \Big ] ,
$$

where $\begin{array} { r } { \operatorname { e r f c } [ x ] = \left( 2 / \sqrt { \pi } \right) \int _ { x } ^ { \infty } e ^ { - x ^ { 2 } / 2 } d x } \end{array}$ . As $\mathrm { e r f c } [ x ]  0$ as $n \to \infty$ , we have

$$
\lambda _ { 1 } \ge 1 - \delta ,
$$

almost surely. To prove this explicitly, we use the bound, erfc[x] ≤ √2π e−x2(x+√x2+4/π) , for $x \ > \ 0$ . In our case $x = ( \log ^ { 3 / 4 } n ) / \sqrt { 2 }$ and so, by using the inequality $\log ^ { a } n \geq a \log n$ , for $a > 1$ , we can show that

$$
\operatorname { e r f c } [ x ] \leq { \mathcal O } { \Big ( } { \frac { 1 } { n ^ { 3 / 4 } \log ^ { 3 / 4 } n } } { \Big ) } .
$$

Thus,

$$
P r [ \lambda _ { 1 } \ge 1 - \delta ] \ge 1 - \mathcal { O } \Bigl ( \frac { 1 } { n ^ { 3 / 4 } \log ^ { 3 / 4 } n } \Bigr ) .
$$

Similarly, one can also obtain an upper bound $\lambda _ { 1 } \leq 1 + \delta$ , almost surely.

Also, from Ref. [15, 16], we have,

$$
| | \gamma ( A - E ( A ) ) | | \leq ( 2 + ( n p ) ^ { - 1 / 4 } \log n ) { \frac { 1 } { \sqrt { n p } } } ,
$$

where $E ( X )$ denotes the expectation of random variable $X$ and $| | \bigstar | | \bigstar$ denotes the standard Euclidean norm.

Let $\lambda _ { i } , j \geq 2$ be the rest of the spectrum of $\gamma A$ and let $| v _ { i } \rangle$ be the corresponding eigenvectors. From Eq. 36, it follows that

$$
\begin{array} { l } { \displaystyle | | \lambda _ { 1 } | v _ { 1 }   v _ { 1 } | + \displaystyle \sum _ { i \geq 2 } \lambda _ { i } | v _ { i }   v _ { i } | - | s   s | | | } \\ { \displaystyle \qquad \leq ( 2 + ( n p ) ^ { - 1 / 4 } \log n ) \frac { 1 } { \sqrt { n p } } } \end{array}
$$

Now,

$$
\begin{array} { l } { \displaystyle \left( \lambda _ { 1 } \left| v _ { 1 } \right. \left. v _ { 1 } \right| + \sum _ { i \geq 2 } \lambda _ { i } \left| v _ { i } \right. \left. v _ { i } \right| - \left| s \right. \left. s \right| \right) \left| v _ { 1 } \right. } \\ { \displaystyle = \lambda _ { 1 } \left| v _ { 1 } \right. - \alpha \left| s \right. } \\ { = \left( \lambda _ { 1 } - \alpha ^ { 2 } \right) \left| v _ { 1 } \right. - \alpha \beta \left| v _ { 1 } \right. ^ { \perp } . } \end{array}
$$

$$
\begin{array} { l } { \displaystyle | | \left( \lambda _ { 1 } \left| v _ { 1 } \right. \left. v _ { 1 } \right| + \sum _ { i \geq 2 } \lambda _ { i } \left| v _ { i } \right. \left. v _ { i } \right| - \left| s \right. \left. s \right| \right) \left| v _ { 1 } \right. | | ^ { 2 } } \\ { = ( \lambda _ { 1 } - \alpha ^ { 2 } ) ^ { 2 } + \alpha ^ { 2 } \beta ^ { 2 } . } \end{array}
$$

From Eq. 37 and the Cauchy-Schwarz inequality, we obtain

$$
\begin{array} { c } { { ( \lambda _ { 1 } - \alpha ^ { 2 } ) ^ { 2 } \leq \displaystyle \frac { ( 2 + ( n p ) ^ { - 1 / 4 } \log n ) ^ { 2 } } { n p } } } \\ { { \Longrightarrow \alpha ^ { 2 } \geq \lambda _ { 1 } - \displaystyle \frac { ( 2 + ( n p ) ^ { - 1 / 4 } \log n ) } { \sqrt { n p } } } } \\ { { \Longrightarrow \alpha \geq \alpha ^ { 2 } \geq 1 - o ( 1 ) , } } \end{array}
$$

for log3/2 nn , where the final expression for α follows from the fact that $\alpha \in [ 0 , 1 ]$ and that $\lambda _ { 1 } \ge 1 - \delta$ .

# IV. PROOF OF OPTIMALITY OF SEARCH ON ERDOS-RENYI RANDOM GRAPHS USING ¨ DEGENERATE PERTURBATION THEORY

Here, we present an intuitive way to prove the optimality of search for Erd¨os-Renyi graphs, $G ( n , p )$ , by using degenerate perturbation theory. This proof is instrumental in constructing protocols for optimal state transfer and entanglement generation in these random networks.

The spectral density of a graph G is defined as

$$
\rho ( \lambda ) = \frac { 1 } { n } \sum _ { i = 1 } ^ { n } \delta ( \lambda _ { i } - \lambda )
$$

where $\lambda _ { i }$ are eigenvalues of the adjacency matrix $A _ { G }$ [28]. In the limit of $n \to \infty$ this approaches a continuous function. For a random graph $G ( n , p )$ , as long as $n p \to \infty$ , the spectral density is given by

$$
\rho ( \lambda ) = \left\{ \begin{array} { l l } { \sqrt { 4 n p ( 1 - p ) - \lambda ^ { 2 } } } & { \mathrm { i f ~ } | \lambda | < 2 \sqrt { n p ( 1 - p ) } } \\ { 0 } & { \mathrm { o t h e r w i s e } } \end{array} \right. ,
$$

known as the Wigner’s semicircle law. The highest eigenvalue, $\lambda _ { 1 }$ , of $A _ { G ( n , p ) }$ is isolated from the bulk of the spectrum and follows a Gaussian distribution with mean $n p$ and standard deviation $\sqrt { p ( 1 - p ) }$ , as $n  \infty$ . From Section I, the corresponding eigenstate, $\left| v _ { 1 } \right.$ tends almost surely to $\textstyle | s \rangle = 1 / { \sqrt { n } } \sum _ { i = 1 } ^ { n } { \big | } i \rangle$ . From Ref. [16], we obtain that the second highest eigenvalue, as $n  \infty$ , is given by

$$
\lambda _ { 2 } = 2 \sqrt { n p } + \mathcal { O } ( ( n p ) ^ { 1 / 4 } \log ( n ) ) .
$$

There is thus a significant gap in the spectrum between the first and second largest eigenvalues, with high probability. In order to make use of this separation between the largest eigenvalue and the rest of the spectrum, it will be helpful to write

$$
A _ { G ( n , p ) } = E \left| s ^ { \prime } \right. \left. s ^ { \prime } \right| + A _ { G ( n , p ) } ^ { \prime }
$$

where $E  n p$ , and $| s ^ { \prime } \rangle \to | s \rangle$ as $n  \infty$ . The search Hamiltonian then becomes

$$
H _ { G ( n , p ) } = - \left| w \right. \left. w \right| - \gamma _ { p } E \left| s ^ { \prime } \right. \left. s ^ { \prime } \right| - \gamma _ { p } A _ { G ( n , p ) } ^ { \prime } .
$$

We use $| s \rangle$ as the initial state of the quantum algorithm and choose $\gamma _ { p } = 1 / ( n p )$ so that, for large $n$ , $| s \rangle$ and $| w \rangle$ are approximately degenerate. The spectrum of $\gamma _ { p } A _ { G ( n , p ) } ^ { \prime }$ follows the semi-circle law, where the radius of the semicircle is given by

$$
R = \gamma _ { p } 2 \sqrt { n p ( 1 - p ) } = 2 \sqrt { \frac { ( 1 - p ) } { n p } } .
$$

As long as $\pi p \to \infty$ , the radius $R  0$ . This implies, for the whole range in which the semi-circle law is valid, that the radius $R$ shrinks as $n p$ grows. Also from Section III, we know that as long as $p \geq \log ^ { 3 / 2 } ( n ) / n$ ,

$$
1 - \frac { 1 } { \sqrt { n } } \leq \gamma _ { p } \lambda _ { 1 } \leq 1 + \frac { 1 } { \sqrt { n } } ,
$$

almost surely.

One can show that the algorithm retains its optimality as long as this is the case. If

$$
- 1 - \delta \leq \gamma _ { p } \lambda _ { 1 } \leq - 1 + \delta ,
$$

using degenerate perturbation theory, we obtain the ground and first excited states of $H _ { G ( n , p ) }$ from its diagonalization in the 2-dimensional subspace spanned by

$\left\{ \left| w \right. , \left| s _ { \bar { w } } \right. \right\}$ , where $\begin{array} { r } { | s _ { \bar { w } } \rangle ~ = ~ \sum _ { i \neq w } ^ { n } | i \rangle / \sqrt { n - 1 } } \end{array}$ . These eigenstates are

$$
\begin{array} { c } { { \displaystyle \left| \lambda _ { + } \right. \approx \displaystyle \frac 1 \kappa \Big ( \displaystyle \frac 1 { \sqrt n } \left| w \right. - \mu \left| s _ { \bar { w } } \right. \Big ) , } } \\ { { \displaystyle \left| \lambda _ { - } \right. \approx \displaystyle \frac 1 \kappa \Big ( \mu \left| w \right. + \displaystyle \frac 1 { \sqrt n } \left| s _ { \bar { w } } \right. \Big ) } } \end{array}
$$

where $\begin{array} { r } { \left| s _ { \bar { w } } \right. = \sum _ { i \neq w } ^ { n } \left| i \right. / \sqrt { n - 1 } } \end{array}$ , $\mu = \delta / 2 + \sqrt { \delta ^ { 2 } / 4 + 1 / n }$ and $\kappa = \surd \mu ^ { 2 } + 1 / n$ .

Thus, the probability of observing the marked vertex $| w \rangle$ is given by

$$
P _ { w } ( t ) = | \left. w \right| \exp ( - i H _ { G ( n , p ) } t ) | s \rangle | ^ { 2 } = \frac { 1 } { 1 + N \delta ^ { 2 } / 4 } \sin ^ { 2 } \left( \frac { \Omega t } { 2 } \right) .
$$

where $\begin{array} { l l l } { \Omega } & { = } & { \sqrt { \delta ^ { 2 } / 4 + 1 / n } } \end{array}$ . Thus, as long as $\delta \in \mathsf { \Gamma }$ $[ - 1 / \sqrt { n } , 1 / \sqrt { n } ]$ , the running time of the algorithm is $T = \mathcal { O } ( { \sqrt { n } } )$ .

Thus, the gap between the lowest eigenvalue of $- \gamma _ { p } A _ { G ( n , p ) } ^ { \prime }$ and the second lowest eigenvalue of $H _ { G ( n , p ) }$ is $\gamma _ { p } ( \lambda _ { 2 } - \lambda _ { 1 } ) = \mathcal { O } ( 1 )$ as long as $p \geq \log ^ { 3 / 2 } ( n ) / n$ . The error obtained from this approximation is $\mathcal { O } ( \gamma _ { p } ^ { 2 } \lambda _ { 2 } ^ { 2 } )$ , since $\gamma _ { p } \lambda _ { 2 }$ is the largest eigenvalue of $\gamma _ { p } A _ { G ( n , p ) } ^ { \prime }$ which we consider as a perturbation. Note that the error of our approximation decreases as $n p$ increases. Thus, for a fixed $n$ , the higher the value of $p$ , the lower is the error. Again, for a fixed $p$ , the error diminishes with increase in $n$ .

[1] Andrew M. Childs and Jeffrey Goldstone. Spatial search by quantum walk. Physical Review A, 70:022314, 2004.   
[2] Jonatan Janmark, David A. Meyer, and Thomas G. Wong. Global symmetry is unnecessary for fast quantum search. Physical Review Letters, 112:210502, 2014.   
[3] Leonardo Novo, Shantanav Chakraborty, Masoud Mohseni, Hartmut Neven, and Yasser Omar. Systematic dimensionality reduction for quantum walks: Optimal spatial search and transport on non-regular graphs. Scientific Reports, 5:13304, 2014.   
[4] David A. Meyer and Thomas G. Wong. Connectivity is a poor indicator of fast quantum search. Physical Review Letters, 114:110503, 2015.   
[5] Paul Erd˝os and Alfred R´enyi. On random graphs. I. Publ. Math. Debrecen, 6:290–297, 1959.   
[6] Paul Erd˝os and Alfred R´enyi. On the evolution of random graphs. Publications of the Mathematical Institute of the Hungarian Academy of Sciences, 5:17–61, 1960.   
[7] S´ebastien Perseguers, Maciej Lewenstein, Antonio Ac´ın, and J Ignacio Cirac. Quantum random networks. Nature Physics, 6(7):539–543, 2010.   
[8] Mauro Faccin, Tomi Johnson, Jacob Biamonte, Sabre Kais, and Piotr Migda l. Degree distribution in quantum walks on complex networks. Physical Review X, 3:041007, 2013.   
[9] Mauro Faccin, Piotr Migda l, Tomi H. Johnson, Ville Bergholm, and Jacob D. Biamonte. Community detection in quantum complex networks. Physical Review $X$ 4:041012, 2014.   
[10] Edward Farhi and Sam Gutmann. Analog analogue of a digital quantum computation. Physical Review A, 57:2403, 1998.   
[11] Normalized algebraic connectivity is defined as the second largest eigenvalue of the symmetric normalized Laplacian defined as $L ^ { \prime } = D ^ { - 1 / 2 } L D ^ { - 1 / 2 }$ , where $L$ is the Laplacian of the graph, with $D$ being a diagonal matrix where the $i ^ { t h }$ diagonal entry is the degree of vertex $_ i$ . In such a case we can define $H _ { 1 } = I - L ^ { \prime }$ .   
[12] One of them is almost regular with $n - 2$ vertices having degree $n / 2$ , while the other two having degree $n / 2 + 1$ .   
[13] Frank Harary and Edgar M Palmer. Graphical enumeration. Elsevier, 2014.   
[14] B´ela Bollob´as. Random graphs. Springer, 1998.   
[15] Zolt´an F¨uredi and J´anos Koml´os. The eigenvalues of random symmetric matrices. Combinatorica, 1(3):233– 241, 1981.   
[16] Van H. Vu. Spectral norm of random matrices. Combinatorica, 27(6):721–736, 2007.   
[17] Sougato Bose. Quantum communication through an unmodulated spin chain. Physical Review Letters, 91:207901, 2003.   
[18] Matthias Christandl, Nilanjana Datta, Artur Ekert, and Andrew J. Landahl. Perfect state transfer in quantum spin networks. Physical Review Letters, 92:187902, 2004.   
[19] Sougato Bose, Andrea Casaccino, Stefano Mancini, and Simone Severini. Communication in xyz all-to-all quantum networks with a missing link. International Journal of Quantum Information, 7(04):713–723, 2009.   
[20] Vivien M Kendon and Christino Tamon. Perfect state transfer in quantum walks on graphs. Journal of Computational and Theoretical Nanoscience, 8:42, 2011.   
[21] The error in this analysis is in going up to only first order in degenerate perturbation theory.   
[22] Michael A Nielsen and Isaac L Chuang. Quantum computation and quantum information. Cambridge university press, 2010.   
[23] The state $| s _ { a b } ^ { - } \rangle = ( | a \rangle - | b \rangle ) / \sqrt { 2 }$ is also degenerate with these states since $\langle s _ { a b } ^ { - } | H | s _ { a b } ^ { - } \rangle \approx - 1$ . However, this state is decoupled from the dynamics because $\langle s _ { w a b } | H | s _ { a b } ^ { - } \rangle \approx$ $^ { - 1 }$ .   
[24] Masoud Mohseni, Alireza Shabani, Seth Lloyd, Yasser Omar, and Herschel Rabitz. Geometrical effects on energy transfer in disordered open quantum systems. The Journal of Chemical Physics, 138:204309, 2013.   
[25] Torsten Scholak, Fernando de Melo, Thomas Wellens, Florian Mintert, and Andreas Buchleitner. Efficient and coherent excitation transfer across disordered molecular networks. Phys. Rev. E, 83:021912, 2011.   
[26] Mark Newman. Networks: An introduction. Oxford University Press, 2010.   
[27] Andrei Broder and Eli Shamir. On the second eigenvalue of random regular graphs. In Foundations of Computer

chanics of complex networks. Reviews of Modern Physics, 74(1):47, 2002.