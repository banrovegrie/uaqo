# Adiabatic Quantum Computing

Tameem Albash

Information Sciences Institute,   
University of Southern California, Marina del Rey,   
CA 90292   
Department of Physics and Astronomy,   
University of Southern California,   
Los Angeles, California 90089,   
USA   
Center for Quantum Information Science & Technology,   
University of Southern California,   
Los Angeles, California 90089,   
USA

Daniel A. Lidar

Department of Physics and Astronomy,   
University of Southern California,   
Los Angeles, California 90089,   
USA   
Center for Quantum Information Science & Technology,   
University of Southern California,   
Los Angeles, California 90089,   
USA   
Department of Electrical Engineering,   
University of Southern California,   
Los Angeles, California 90089,   
USA   
Department of Chemistry,   
University of Southern California,   
Los Angeles, California 90089,   
USA

Adiabatic quantum computing (AQC) started as an approach to solving optimization problems, and has evolved into an important universal alternative to the standard circuit model of quantum computing, with deep connections to both classical and quantum complexity theory and condensed matter physics. In this review we give an account of most of the major theoretical developments in the field, while focusing on the closedsystem setting. The review is organized around a series of topics that are essential to an understanding of the underlying principles of AQC, its algorithmic accomplishments and limitations, and its scope in the more general setting of computational complexity theory. We present several variants of the adiabatic theorem, the cornerstone of AQC, and we give examples of explicit AQC algorithms that exhibit a quantum speedup. We give an overview of several proofs of the universality of AQC and related Hamiltonian quantum complexity theory. We finally devote considerable space to Stoquastic AQC, the setting of most AQC work to date, where we discuss obstructions to success and their possible resolutions.

# CONTENTS

I. Introduction 2

II. Adiabatic Theorems 5

A. Approximate versions   
B. Rigorous versions 1. Inverse cubic gap dependence with generic $H ( s )$ 2. Rigorous inverse gap squared 3. Arbitrarily small error 4. Lower bound

III. Algorithms 9

A. Adiabatic Grover 1. Setup for the adiabatic quantum Grover

algorithm 10   
2. Quadratic quantum speedup 11   
3. Multiple marked states 11   
B. Adiabatic Deutsch-Jozsa algorithm 12   
1. Unitary interpolation 12   
2. Linear interpolation 13   
3. Interpretation 13   
C. Adiabatic Bernstein-Vazirani algorithm 14   
D. The glued trees problem 15   
E. Adiabatic PageRank algorithm 16   
1. Google matrix and PageRank 16   
2. Hamiltonian and gap 17   
3. Speedup 17

IV. Universality of AQC 18

A. The circuit model can efficiently simulate AQC 19

B. AQC can efficiently simulate the circuit model:   
history state proof 19   
C. Fermionic ground state quantum computation 21   
D. Space-time Circuit-to-Hamiltonian Construction 22   
E. Universal AQC in 1D with 9-state particles 23   
F. Adiabatic gap amplification 24

V. Hamiltonian quantum complexity theory and universal AQC

A. Background 25   
1. Boolean Satisfiability Problem: $k$ -SAT 25   
2. NP, NP-complete, and NP-hard 25   
3. The $k$ -local Hamiltonian Problem 26   
4. Motivation for Adiabatic Quantum Computing 26   
B. MA and QMA 27   
C. The general relation between QMA completeness and   
universal AQC 27   
D. QMA-completeness of the $k$ -local Hamiltonian   
problem and universal AQC 27

VI. Stoquastic Adiabatic Quantum Computation 29

A. Why it might be easy to simulate stoquastic Hamiltonians 30   
B. Why it might be hard to simulate stoquastic Hamiltonians 31 1. Topological obstructions 31 2. Non-topological obstructions 32   
C. QMA-complete problems and universal AQC using stoquastic Hamiltonians with excited states 33   
D. Examples of slowdown by StoqAQC 33 1. Perturbed Hamming Weight Problems with Exponentially Small Overlaps 34 2. 2-SAT on a Ring 35 3. Weighted 2-SAT on a chain with periodicity 36 4. Topological slowdown in a dimer model or local Ising ladder 37 5. Ferromagnetic Mean-field Models 38 6. 3-Regular 3-XORSAT 38 7. Sherrington-Kirkpatrick and Two-Pattern Gaussian Hopfield Models 39   
E. StoqAQC algorithms with a scaling advantage over simulated annealing 40 1. Spike-like Perturbed Hamming Weight Problems 40 2. Large plateaus 40   
F. StoqAQC algorithms with undetermined speedup 41 1. Number partitioning 41 2. Exact Cover and its generalizations 41 3. 3-Regular MAXCUT 42 4. Ramsey numbers 43 5. Finding largest cliques in random graphs 43 6. Graph isomorphism 43 7. Machine learning 44   
G. Speedup mechanisms? 44 1. The role of tunneling 44 2. The role of entanglement 46

VII. Circumventing slowdown mechanisms for AQC

A. Avoiding poor choices for the initial and final   
Hamiltonians 47   
B. Quantum Adiabatic Brachistochrone 48   
C. Modifying the initial Hamiltonian 50   
D. Modifying the final Hamiltonian 50   
E. Adding a catalyst Hamiltonian 51   
F. Addition of non-stoquastic terms 52   
G. Avoiding perturbative crossings 52   
H. Evolving non-adiabatically 54

VIII. Outlook and Challenges 55

Acknowledgments 56

A. Technical calculations 56   
1. Upper bound on the adiabatic path length $L$ 56   
2. Proof of the inequality given in Eq. (25) 56   
B. A lower bound for the adiabatic Grover search problem 57   
C. Technical details for the proof of the universality of AQC   
using the History State construction 57   
1. $| \gamma ( 0 ) \rangle$ is the ground state of $H _ { \mathrm { i n i t } }$ 57   
2. $| \eta \rangle$ is a ground state of $H _ { \mathrm { f i n a l } }$ 58   
3. Gap bound in the space spanned by $\{ | \gamma ( \ell ) \rangle \} _ { \ell = 0 } ^ { L }$ 58   
a. Bound for $s < 1 / 3$ 58   
b. Bound for $s \geq 1 / 3$ 59   
4. Gap bound in the entire Hilbert space 60   
D. Proof of the Amplification Lemma (Claim 1) 61   
E. Perturbative Gadgets 62   
1. Degenerate Perturbation Theory \`a la (Bloch, 1958) 62   
2. Perturbative Gadgets 63

References 65

# I. INTRODUCTION

Quantum computation (QC) originated with Benioff’s proposals for quantum Turing machines (Benioff, 1980, 1982) and Feynman’s ideas for circumventing the difficulty of simulating quantum mechanics by classical computers (Feynman, 1982). This led to Deutsch’s proposal for universal QC in terms of what has become the “standard” model: the circuit, or gate model of QC (Deutsch, 1989). Adiabatic quantum computation (AQC) is based on an idea that is quite distinct from the circuit model. Whereas in the latter a computation may in principle evolve in the entire Hilbert space and is encoded into a series of unitary quantum logic gates, in AQC the computation proceeds from an initial Hamiltonian whose ground state is easy to prepare, to a final Hamiltonian whose ground state encodes the solution to the computational problem. The adiabatic theorem guarantees that the system will track the instantaneous ground state provided the Hamiltonian varies sufficiently slowly. It turns out that this approach to QC has deep connections to condensed matter physics, computational complexity theory, and heuristic algorithms.

In its first incarnation, the idea of encoding the solution to a computational problem in the ground state of a quantum Hamiltonian appeared as early as 1988, in the context of solving classical combinatorial optimization problems, where it was called quantum stochastic optimization (Apolloni et al., 1989).1 It was renamed quantum annealing (QA) in (Apolloni et al., 1988) and reinvented several times (Amara et al., 1993; Finnila et al.,

1994; Kadowaki and Nishimori, 1998; Somorjai, 1991).2 These early papers emphasized that QA was to be understood as an algorithm that exploits simulated quantum (rather than thermal) fluctuations and tunneling, thus providing a quantum-inspired version of simulated annealing (SA) (Kirkpatrick et al., 1983). The first direct comparison between QA and SA (Kadowaki and Nishimori, 1998) suggested that QA can be more powerful.

A very different approach was taken via an experimental implementation of QA in a disordered quantum ferromagnet (Brooke et al., 1999, 2001). This provided the impetus to reconsider QA from the perspective of quantum computing, i.e., to consider a dedicated device that solves optimization problems by exploiting quantum evolution. Thus was born the idea of the quantum adiabatic algorithm (QAA) (Farhi et al., 2001, 2000) [also referred to as adiabatic quantum optimization (AQO) (Reichardt, 2004; Smelyanskiy et al., 2001)], wherein a physical quantum computer solves a combinatorial optimization problem by evolving adiabatically in its ground state. The term adiabatic quantum computation we shall use here was introduced in (van Dam et al., 2001), though the context was still optimization.3

Adiabatic quantum algorithms for optimization problems typically use “stoquastic” Hamiltonians, characterized by having only non-positive off-diagonal elements in the computational basis. Adiabatic quantum computation with non-stoquastic Hamiltonians is as powerful as the circuit model of quantum computation (Aharonov et al., 2007). In other words, non-stoquastic AQC and all other models for universal quantum computation can simulate one another with at most polynomial resource overhead. For this reason the contemporary use of the term AQC typically refers to the general, nonstoquastic setting, thus extending beyond optimization to any computational. When discussing the case of stoquastic Hamiltonians we will use the term “stoquastic AQC” (StoqAQC).4

For most of this review we essentially adopt the definition of AQC from (Aharonov et al., 2007), as this definition allows for the proof of the equivalence with the circuit model, and is thus used to establish the universality of AQC. Interestingly, this proof builds on one of the first QC ideas due to Feynman, which was later shown to allow a general purpose quantum computation to be embedded in the ground state of a quantum system (Feynman, 1985; Kitaev et al., 2000). A related ground state embedding approach was independently pursued in (Mizel et al., 2001, 2002), around the same time as the original development of the QAA. To define AQC, we first need the concept of a $k$ -local Hamiltonian, which is a Hermitian matrix $H$ acting on the space of $p$ -state particles that can be written as $\begin{array} { r } { H = \sum _ { i = 1 } ^ { r } H _ { i } } \end{array}$ where each $H _ { i }$ acts non-trivially on at most $k$ particles, i.e., $H _ { i } = h \otimes \mathbb { 1 }$ where $h$ is a Hamiltonian on at most $k$ particles, and $\mathbb { 1 }$ denotes the identity operator.

Definition 1 (Adiabatic Quantum Computation). A $k$ - local adiabatic quantum computation is specified by two $k$ -local Hamiltonians, $H _ { 0 }$ and $H _ { 1 }$ , acting on n $p$ -state particles, $p \geq 2$ . The ground state of $H _ { 0 }$ is unique and is a product state. The output is a state that is $\varepsilon$ -close in $\ell _ { 2 }$ -norm to the ground state of $H _ { 1 }$ . Let $s ( t ) : [ 0 , t _ { f } ] \mapsto $ $[ 0 , 1 ]$ (the “schedule”) and let $t _ { f }$ be the smallest time such that the final state of an adiabatic evolution generated by $H ( s ) = ( 1 - s ) H _ { 0 } + s H _ { 1 }$ for time $t _ { f }$ is $\varepsilon$ -close in $\ell _ { 2 }$ -norm to the ground state of $H _ { 1 }$ .

Several comments are in order. (1) A uniqueness requirement was imposed on the ground state of $H _ { 1 }$ in (Aharonov et al., 2007), but this is not necessary. E.g., in the setting where $H _ { 1 }$ represents a classical optimization problem, multiple final ground states do not pose a problem as any of the final states represents a solution to the optimization problem. (2) Sometimes it is beneficial to consider adiabatic quantum computation in an excited state (see, e.g., Sec. VI.C). (3) As already noted in (Aharonov et al., 2007), it is useful to allow for more general “paths” between $H _ { 0 }$ and $H _ { 1 }$ , e.g., by introducing an intermediate “catalyst” Hamiltonian that vanishes at $s = 0 , 1$ (see, e.g., Sec. VII.E).

A crucial question that will occupy us throughout this review is the cost of running an algorithm in AQC. In the circuit model the cost is equated with the number of gates, so one cost definition would be to the count the number of gates needed to simulate the equivalent adiabatic process. This cost definition presupposes that the circuit model is fundamental, which may be unsatisfactory. In AQC one might be tempted to just use the run time $t _ { f }$ , but in order for this quantity to be meaningful it is necessary to define an appropriate energy scale for the Hamiltonian. In (Aharonov et al., 2007) the cost of the adiabatic algorithm was defined to be the dimensionless quantity

$$
\mathrm { c o s t } = t _ { f } \operatorname* { m a x } _ { s } \| H ( s ) \| ~ ,
$$

in order to prevent the cost from being made arbitrarily small by changing the time units, or distorting the scaling of the algorithm by multiplying the Hamiltonians by some size-dependent factor.5 From hereon we will focus on the run time $t _ { f }$ , which should be compared to the circuit depth of analogous circuit model algorithms, whereas the full cost in Eq. (1) should be compared to the circuit gate count.

The run time $t _ { f }$ of an adiabatic algorithm scales at worst as $1 / \Delta ^ { 3 }$ , where $\Delta$ is the minimum eigenvalue gap between the ground state and the first excited state of the Hamiltonian of the adiabatic algorithm (Jansen et al., 2007). If the Hamiltonian is varied sufficiently smoothly, one can improve this to $O ( 1 / \Delta ^ { 2 } )$ up to a polylogarithmic factor in $\Delta$ (Elgart and Hagedorn, 2012). While these are useful sufficient conditions, they involve bounding the minimum eigenvalue gap of a complicated manybody Hamiltonian, a notoriously difficult problem. This is one reason that AQC has generated so much interest among physicists: it has a rich connection to well studied problems in condensed matter physics. For example, because of the dependence of the run time on the gap, the performance of quantum adiabatic algorithms is strongly influenced by the type of quantum phase transition the same system would undergo in the thermodynamic limit (Latorre and Orus, 2004).

Nevertheless, a number of examples are known where the gap analysis can be carried out. For example, adiabatic quantum computers can perform a process analogous to Grover search (Grover, 1997), and thus provide a quadratic speedup over the best possible classical algorithm for the Grover search problem (Roland and Cerf, 2002). Other examples are known where the gap analysis can be used to demonstrate that AQC provides a speedup over classical computation, including adiabatic versions of some of the keystone algorithms of the circuit model. However, much more common is the scenario where either the gap analysis reveals no speedup over classical computation, or where a clear answer to the speedup question is unavailable. In fact, the least is known about adiabatic quantum speedups in the original setting of solving classical combinatorial optimization problems. This remains an area of very active research, partly due to the original (still unmaterialized) hope that the QAA would deliver quantum speedups for NP-complete problems (Farhi et al., 2001), and partly due the availability of commercial quantum annealing devices such as those manufactured by D-Wave Systems Inc. (Johnson et al., 2011), designed to solve optimization problems using stoquastic Hamiltonians.

The goal of this article is to review the field of AQC from its inception, with a focus on the closed system case. That is, we omit the fascinating topic of AQC in open systems coupled to an environment. This includes all experimental work on AQC, and all work on quantum error correction and suppression methods for AQC, as these topics deserve a separate review (Albash and Lidar, 2017) and including them here would limit our ability to do justice to the many years of work on AQC in closed systems, an extremely rich topic with many elegant results. For the same reasons we also omit the blossoming and closely related fields of holonomic QC (Zanardi and Rasetti, 1999), topological QC (Nayak et al., 2008), and adiabatic state preparation for quantum simulation (Babbush et al., 2014b). To achieve our goal we organized this review around a series of topics that are essential to an understanding of the underlying principles of AQC, its algorithmic accomplishments and limitations, and its scope in the more general setting of computational complexity theory.

We begin by reviewing the adiabatic theorem in Sec. II. The adiabatic theorem forms the backbone of AQC: it provides a sufficient condition for the success of the computation, and in doing so provides the run time of a computation in terms of the eigenvalue gap $\Delta$ of the Hamiltonian and the Hamiltonian’s time-derivative. In fact there is not one single adiabatic theorem, and we review a number of different variants that provide different run time requirements, under different smoothness and differentiability assumptions about the Hamiltonian.

Next, we review in Sec. III the handful of explicit algorithms for which AQC is known to give a speedup over classical computation. The emphasis is on “explicit”, since Sec. IV provides several proofs for the universality of AQC in terms of its ability to efficiently simulate the circuit model, and vice versa. This means that every quantum algorithm that provides a speedup in the circuit model [many of which are known (Jordan, 2016b)] can in principle be implemented with up to polynomial overhead in AQC. That the number of explicit AQC algorithms is still small is therefore likely to be a reflection of the relatively modest amount of effort that has gone into establishing such results compared to the circuit model. However, there is also a real difficulty, in that performing the gap analysis in order to establish the actual scaling (beyond the polynomial-time equivalence) is, as already mentioned above, in many cases highly non-trivial. A second non-trivial aspect of establishing a speedup by AQC is that when such a speedup is polynomial, relying on universality is insufficient, since the polynomial overhead involved in implementing the transformation from the circuit model to AQC can then swamp the speedup. A good example is the case of Grover’s algorithm, where a direct use of the equivalence to the circuit model would not suffice; instead, what is required is a careful analysis and choice of the adiabatic schedule $s ( t )$ in order to realize the quantum speedup.

In Sec. V we go beyond universality into Hamiltonian quantum complexity theory. This is an active contemporary research area, that started with the introduction of the complexity class QMA (“quantum Merlin-Arthur”) as the natural quantum generalization of the classical complexity classes ”nondeterministic polynomial time” (NP) and MA (Kitaev et al., 2000). The theory of QMAcompleteness deals with decision problems that are efficiently checkable using quantum computers. It turns out that these decision problems can be formulated naturally in terms of $k$ -local Hamiltonians, of the same type that appear in the proofs of the universality of AQC. Thus universality and Hamiltonian quantum complexity studies are often pursued hand-in-hand, and a reduction of $k$ as well as the dimensionality $p$ of the particles appearing in these constructions is one of the main goals. For example, already $k = 2$ and $p = 2$ leads to both universal AQC and QMA-complete Hamiltonians in 2D, while in 1D $p > 2$ is needed for both.6

We turn our attention to StoqAQC in Sec. VI. This is the setting of the vast majority of AQC work to date. The final Hamiltonian $H _ { 1 }$ is assumed to be a classical Ising model Hamiltonian, typically (but not always) representing a hard optimization problem such as a spin glass. The initial Hamiltonian $H _ { 0 }$ is typically assumed to be proportional to a transverse field, i.e., $\textstyle \sum _ { i } \sigma _ { i } ^ { x }$ , whose ground state is the uniform superposition state in the computational basis. AQC with stoquastic Hamiltonians is probably less powerful than universal quantum computation, but examples can be constructed which show that it may nevertheless be more powerful than classical computation. Moreover, if we relax the definition of AQC to allow for computation using excited states, it turns out that stoquastic Hamiltonians can even be QMA-complete and support universal AQC. To do justice to this mixed and complicated picture, we first review examples where it is known that StoqAQC does not outperform classical computation (essentially because the eigenvalue gap $\Delta$ decreases rapidly with problem size but classical algorithms do not suffer a slowdown), then discuss examples where StoqAQC offers a quantum scaling advantage over simulated annealing in the sense that it outperforms classical simulated annealing but not necessarily other classical algorithms, and finally point out examples where it is currently not known whether StoqAQC offers a quantum speedup, but one might hope that it does. We also discuss the role of potential quantum speedup mechanisms, in particular tunneling and entanglement.

The somewhat bleak picture regarding StoqAQC should not necessarily be a cause for pessimism. Some of the obstacles in the way of a quantum speedup can be overcome or circumvented, as we discuss in Sec. VII. In all cases this involves modifying some aspect of the Hamiltonian, either by optimizing the schedule $s ( t )$ , or by adding certain terms to the Hamiltonian such that small gaps are avoided. This can result in a non-stoquastic Hamiltonian whose final ground state is the same as that of the original Hamiltonian, with an exponentially small gap (often corresponding to a first order quantum phase transition) changing into a polynomially small gap (often corresponding to a second order phase transition). Another type of modification is to give up adiabatic evolution itself, and allow for diabatic transitions. While this results in giving up the guarantee of convergence to the ground state provided by the adiabatic theorem, it can be a strategy that results in better run time scaling for the same Hamiltonian than an adiabatic one.

We conclude with an outlook and discussion of future directions in Sec. VIII. Various technical details are provided in the Appendix.

# II. ADIABATIC THEOREMS

The origins of the celebrated quantum adiabatic approximation date back to Einstein’s “Adiabatenhypothese”: “If a system be affected in a reversible adiabatic way, allowed motions are transformed into allowed motions” (Einstein, 1914). Ehrenfest was the first to appreciate the importance of adiabatic invariance, guessing—before the advent of a complete quantum theory— that quantum laws would only allow motions which are invariant under adiabatic perturbations (Ehrenfest, 1916). The more familiar, modern version of the adiabatic approximation was put forth by Born and Fock already in 1928 for the case of discrete spectra (Born and Fock, 1928), after the development of the Born-Oppenheimer approximation for the separation of electronic and nuclear degrees of freedom a year earlier (Born and Oppenheimer, 1927). Kato put the approximation on a firm mathematical foundation in 1950 (Kato, 1950) and arguably proved the first quantum adiabatic theorem.

The adiabatic approximation states, roughly, that for a system initially prepared in an eigenstate (e.g., the ground state) $\vert \varepsilon _ { 0 } ( 0 ) \rangle$ of a time-dependent Hamiltonian $H ( t )$ , the time evolution governed by the Schr¨odinger equation

$$
i \frac { \partial | \psi ( t ) \rangle } { \partial t } = H ( t ) | \psi ( t ) \rangle
$$

(we set $\hbar \equiv 1$ from now on) will approximately keep the actual state $| \psi ( t ) \rangle$ of the system in the corresponding instantaneous ground state (or other eigenstate) $| \varepsilon _ { 0 } ( t ) \rangle$ of $H ( t )$ , provided that $H ( t )$ varies “sufficiently slowly”.

Quantifying the exact nature of this slow variation is the subject of the Adiabatic Theorem (AT), which exists in many variants. In this section we provide an overview of these variants of the AT, emphasizing aspects that are pertinent to AQC. We discuss the “folklore” adiabatic condition, that the total evolution time $t _ { f }$ should be large on the timescale set by the square of the inverse gap, and the question of how to ensure a high fidelity between the actual state and the ground state. We then discuss a variety of rigorous versions of the AT, emphasizing different assumptions and consequently different performance guarantees. Throughout this discussion, it is important to keep in mind that ultimately the AT provides only an upper bound on the evolution time required to achieve a certain fidelity between the actual state and the target eigenstate of $H ( t )$ .

# A. Approximate versions

Let $| \varepsilon _ { j } ( t ) \rangle ~ ( j \in \{ 0 , 1 , 2 , . . . \} )$ denote the instantaneous eigenstate of $H ( t )$ with energy $\varepsilon _ { j } ( t )$ such that $\varepsilon _ { j } ( t ) \ \leq$ $\varepsilon _ { j + 1 } ( t ) \ \forall j , t$ , i.e., $H ( t ) | \varepsilon _ { j } ( t ) \rangle = \varepsilon _ { j } ( t ) | \varepsilon _ { j } ( t ) \rangle$ and $j = 0$ denotes the (possibly degenerate) ground state. Assume that the initial state is prepared in one of the eigenstates $\vert \varepsilon _ { j } ( 0 ) \rangle$ .

The simplest as well as one of the oldest traditional versions of the adiabatic approximation states that a system initialized in an eigenstate $\vert \varepsilon _ { j } ( 0 ) \rangle$ will remain in the same instantaneous eigenstate $| \varepsilon _ { j } ( t ) \rangle$ (up to a global phase) for all $t \in [ 0 , t _ { f } ]$ , where $t _ { f }$ denotes the final time, provided (Messiah, A., 1962):

$$
\operatorname* { m a x } _ { t \in [ 0 , t _ { f } ] } \frac { | \langle \varepsilon _ { i } | \partial _ { t } \varepsilon _ { j } \rangle | } { | \varepsilon _ { i } - \varepsilon _ { j } | } = \operatorname* { m a x } _ { t \in [ 0 , t _ { f } ] } \frac { | \langle \varepsilon _ { i } | \partial _ { t } H | \varepsilon _ { j } \rangle | } { | \varepsilon _ { i } - \varepsilon _ { j } | ^ { 2 } } \ll 1 \ \forall i \neq j \ .
$$

This version has been critiqued (Du et al., 2008; Marzlin and Sanders, 2004; Tong et al., 2005; Wu et al., 2008) on the basis of arguments and examples involving a separate, independent timescale. Indeed, if the Hamiltonian includes an oscillatory driving term then the eigenstate population will oscillate with a timescale determined by this term, that is independent of $t _ { f }$ , even if the adiabatic criterion (3) is satisfied.7

A more careful statement of the adiabatic condition that excludes such additional timescales is thus required. The first step is to assume that the Hamiltonian $H _ { t _ { f } } ( t )$ in the Schr¨odinger equation $\partial | \psi _ { t _ { f } } ( t ) \rangle / \partial t =$ $- i H _ { t _ { f } } ( t ) | \psi _ { t _ { f } } ( t ) \rangle$ can be written as $H _ { t _ { f } } ( s t _ { f } ) ~ = ~ H ( s )$ , where $s \equiv t / t _ { f } \in [ 0 , 1 ]$ is the dimensionless time, and $H ( s )$ is $t _ { f }$ -independent. This includes the “interpolating” Hamiltonians of the type often considered in AQC, i.e., $H ( s ) = A ( s ) H _ { 0 } + B ( s ) H _ { 1 }$ [where $A ( s )$ and $B ( s )$ are monotonically decreasing and increasing, respectively] and excludes cases with multiple timescales.8 The Schr¨odinger equation then becomes

$$
\frac { 1 } { t _ { f } } \frac { \partial | \psi _ { t _ { f } } ( s ) \rangle } { \partial s } = - i H ( s ) | \psi _ { t _ { f } } ( s ) \rangle ~ ,
$$

which is the starting point for all rigorous adiabatic theorems.

A more careful adiabatic condition subject to this formulation is given by (Amin, 2009):

$$
\frac { 1 } { t _ { f } } \operatorname* { m a x } _ { s \in [ 0 , 1 ] } \frac { | \langle \varepsilon _ { i } ( s ) | \partial _ { s } H ( s ) | \varepsilon _ { j } ( s ) \rangle | } { | \varepsilon _ { i } ( s ) - \varepsilon _ { j } ( s ) | ^ { 2 } } \ll 1 \forall j \neq i .
$$

The conditions (3) and (5) give rise to the widely used criterion that the total adiabatic evolution time should be large on the timescale set by the minimum of the square of the inverse spectral gap $\Delta _ { i j } ( s ) = \varepsilon _ { i } ( s ) - \varepsilon _ { j } ( s )$ . In most cases one is interested in the ground state, so that $\Delta _ { i j } ( s )$ is replaced by

$$
\Delta \equiv \operatorname* { m i n } _ { s \in [ 0 , 1 ] } \Delta ( s ) = \operatorname* { m i n } _ { s \in [ 0 , 1 ] } \varepsilon _ { 1 } ( s ) - \varepsilon _ { 0 } ( s ) ~ .
$$

However, arguments such as those leading to Eqs. (3) and (5) are approximate, in the sense that they do not result in strict inequalities and do not result in bounds on the closeness between the actual time-evolved state and the desired eigenstate. We discuss this next.

# B. Rigorous versions

The first rigorous adiabatic condition is due to Kato (Kato, 1950), and was followed by numerous alternative derivations and improvements giving tighter bounds under various assumptions, e.g., (Ambainis and Regev, 2004; Avron and Elgart, 1999; Cheung et al., 2011; Elgart and Hagedorn, 2012; Ge et al., 2015; Hagedorn and Joye, 2002; Jansen et al., 2007; Lidar et al., 2009; Nenciu, 1993; O’Hara and O’Leary, 2008; Reichardt, 2004; Teufel, 2003). All these rigorous results are more severe in the gap condition than the traditional criterion, and they involve a power of the norm of time derivatives of the Hamiltonian, rather than a transition matrix element.

We summarize a few of these results here, and refer the reader to the original literature for their proofs. For simplicity we always assume that the system is initialized in its ground state and that the gap is the ground state gap (6). We also assume that for all $s \in [ 0 , 1 ]$ the Hamiltonian $H ( s )$ has an eigenprojector $P ( s )$ with eigenenergy $\varepsilon _ { 0 } ( s )$ , and that the gap never vanishes, i.e., $\Delta > 0$ .9 The ground state, and hence the projector $P ( s )$ , is allowed to be (even infinitely) degenerate. $P ( s )$ represents the “ideal” adiabatic evolution.

Let $P _ { t _ { f } } ( s ) = | \psi _ { t _ { f } } ( s ) \rangle \langle \psi _ { t _ { f } } ( s ) |$ . This is the projector onto the time-evolved solution of the Schr¨odinger equation, i.e., the “actual” state. Adiabatic theorems are usually statements about the “instantaneous adiabatic distance” $\| P _ { t _ { f } } ( s ) - P ( s ) \|$ between the projectors associated with the actual and ideal evolutions, or the “finaltime adiabatic distance” $\| P _ { t _ { f } } ( 1 ) - P ( 1 ) \|$ . Typically, adiabatic theorems give a bound of the form $O ( 1 / t _ { f } )$ for the instantaneous case, and a bound of the form $O ( 1 / t _ { f } ^ { n } )$ for any $n \in \mathbb N$ for the final-time case. After squaring, these projector-distance bounds immediately become bounds on the transition probability, defined as $\vert \langle \psi _ { t _ { f } } ^ { \bot } ( s ) \vert \psi _ { t _ { f } } ( s ) \rangle \vert ^ { 2 }$ , where $\begin{array} { r } { | \psi _ { t _ { f } } ^ { \bot } ( s ) \rangle = Q _ { t _ { f } } ( s ) | \psi _ { t _ { f } } ( s ) \rangle } \end{array}$ , with $Q = I - P$ .

# 1. Inverse cubic gap dependence with generic $H ( s )$

Kato’s work on the perturbation theory of linear operators (Kato, 1950) introduced techniques based on resolvents and complex analysis that have been widely used in subsequent work. Jansen, Ruskai, and Seiler (JRS) proved several versions of the AT that build upon these techniques (Jansen et al., 2007), and that rigorously establish the gap dependence of $t _ { f }$ , without any strong assumptions on the smoothness of $H ( s )$ . Their essential assumption is that the spectrum of $H ( s )$ has a band associated with the spectral projection $P ( s )$ which is separated by a non-vanishing gap $\Delta ( s )$ from the rest. Here we present one their theorems:

Theorem 1. Suppose that the spectrum of $H ( s )$ restricted to $P ( s )$ consists of $m ( s )$ eigenvalues separated by a gap $\Delta ( s ) = \varepsilon _ { 1 } ( s ) - \varepsilon _ { 0 } ( s ) > 0$ from the rest of the spectrum of $H ( s )$ , and that $H ( s )$ is twice continuously differentiable. Assume that $H$ , $H ^ { ( 1 ) }$ , and $H ^ { ( 2 ) }$ are bounded operators, an assumption that is always fulfilled in finite-dimensional spaces.10 Then for any $s \in [ 0 , 1 ]$

$$
\begin{array} { l } { { \displaystyle \left\| P _ { t _ { f } } ( s ) - P ( s ) \right\| \le \frac { m ( 0 ) \left\| H ^ { ( 1 ) } ( 0 ) \right\| } { t _ { f } \Delta ^ { 2 } ( 0 ) } + \frac { m ( s ) \left\| H ^ { ( 1 ) } ( s ) \right\| } { t _ { f } \Delta ^ { 2 } ( s ) } } } \\ { { \displaystyle ~ + \frac { 1 } { t _ { f } } \int _ { 0 } ^ { s } \left( \frac { m \left\| H ^ { ( 2 ) } \right\| } { \Delta ^ { 2 } } + \frac { 7 m \sqrt { m } \left\| H ^ { ( 1 ) } \right\| ^ { 2 } } { \Delta ^ { 3 } } \right) d x \qquad ( 7 } } \end{array}
$$

The numerator depends on the norm of the first or second time derivative of $H ( s )$ , rather than the matrix element that appears in the traditional versions of the adiabatic condition.

Ignoring the $m$ -dependence for simplicity, this result shows that the adiabatic limit can be approached arbitrarily closely if (but not only if)

$$
\begin{array} { c l l } { \displaystyle \mathit { t } _ { f } \gg \operatorname* { m a x } \{ \underset { s \in [ 0 , 1 ] } { \operatorname* { m a x } } \frac { \| H ^ { ( 2 ) } ( s ) \| } { \Delta ^ { 2 } ( s ) } , \underset { s \in [ 0 , 1 ] } { \operatorname* { m a x } } \frac { \| H ^ { ( 1 ) } ( s ) \| ^ { 2 } } { \Delta ^ { 3 } ( s ) } ,  } \\ { \displaystyle \underset { s \in [ 0 , 1 ] } { \operatorname* { m a x } } \frac { \| H ^ { ( 1 ) } ( s ) \| } { \Delta ^ { 2 } ( s ) } \} . } \end{array}
$$

Similar techniques based on Kato’s approach can be used to prove a rigorous adiabatic theorem for open quantum systems, where the evolution is generated by a non-Hermitian Liouvillian instead of a Hamiltonian (Venuti et al., 2016).

# 2. Rigorous inverse gap squared

A version of the AT that yields a scaling of $t _ { f }$ with the inverse of the gap squared (up to a logarithmic correction) was given in (Elgart and Hagedorn, 2012). All other rigorous AT versions to date have a worse gap dependence (cubic or higher). The proof introduces assumptions on $H ( s )$ that go beyond those of Theorem 1. Namely, it is assumed that $H ( s )$ is bounded and infinitely differentiable, and the higher derivatives cannot have a magnitude that is too large, or more specifically, that $H ( s )$ belongs to the Gevrey class $G ^ { \alpha }$ :

Definition 2 (Gevrey class). $H ( s ) \in G ^ { \alpha }$ if $d H ( s ) / d s \neq$ $0 \forall s \in [ 0 , 1 ]$ and there exist constants $C , R > 0$ , such that for all $k \geq 1$ ,

$$
\operatorname* { m a x } _ { s \in [ 0 , 1 ] } \Big \| H ^ { ( k ) } ( s ) \Big \| \le C R ^ { k } k ^ { \alpha k } \ .
$$

An example is $H ( s ) = [ 1 - A ( s ) ] H _ { 0 } + A ( s ) H _ { 1 }$ , where $\begin{array} { r } { A ( s ) = c \int _ { - \infty } ^ { s } \exp [ - 1 / ( x - x ^ { 2 } ) ] d x } \end{array}$ if $s \in ( 0 , 1 )$ , and $A ( s ) =$ $0$ if $s \notin \left[ 0 , 1 \right]$ ∞ . The constant $c$ is chosen so that $A ( 1 ) = 1$ . For this family $\left\| H ^ { ( k ) } ( s ) \right\| = \left| A ^ { ( k ) } ( s ) \right| \left\| H _ { 1 } - H _ { 0 } \right\| \leq C k ^ { 2 k }$ , so that $H ( s ) \in G ^ { 2 }$ .

The AT due to (Elgart and Hagedorn, 2012) can now be stated as follows:

Theorem 2. Assume that $H ( s )$ is bounded and belongs to the Gevrey class $G ^ { \alpha }$ with $\alpha > 1$ , and that $\Delta \ll h$ , where $h \equiv \| H ( 0 ) \| = \| H ( 1 ) \|$ . If

$$
t _ { f } \geq \frac { K } { \Delta ^ { 2 } } | \ln ( \Delta / h ) | ^ { 6 \alpha }
$$

for some $\Delta$ -independent constant $K > 0$ (with units of energy), then the distance $\| P _ { t _ { f } } ( s ) - P ( s ) \|$ is $o ( 1 ) \ \forall s \in$ $[ 0 , 1 ]$ .

This result is remarkable in that it rigorously gives an inverse gap squared dependence, which is essentially tight due to existence of a lower bound of the form $t _ { f } ~ = ~ O ( \Delta ^ { - 2 } / | \ln \Delta | )$ for Hamiltonians satisfying rank $H ( 1 ) \ll \dim ( \mathcal { H } )$ (Cao and Elgart, 2012). However, the error bound is not tight, and we address this next.

# 3. Arbitrarily small error

Building on work originating with (Nenciu, 1993) [see also (Hagedorn and Joye, 2002)], (Ge et al., 2015) proved a version of the AT that results in an exponentially small error bound in $t _ { f }$ . The inverse gap dependence is cubic.

Assume for simplicity that $\varepsilon _ { 0 } ( s ) = 0$ and choose the phase of $\left. \varepsilon _ { 0 } ( s ) \right.$ so that $\langle \dot { \varepsilon } _ { 0 } ( s ) | \varepsilon _ { 0 } ( s ) \rangle = 0$ , where the dot denotes $\partial _ { s }$ .

Theorem 3. Assume that all derivatives of the Hamiltonian $H ( s )$ vanish at $s = 0 , 1$ , and moreover that it satisfies the following Gevrey condition: there exist constants $C , R , \alpha > 0$ such that for all $k \geq 1$ ,

$$
\operatorname* { m a x } _ { s \in [ 0 , 1 ] } \left\| H ^ { ( k ) } ( s ) \right\| \leq C R ^ { k } \frac { ( k ! ) ^ { 1 + \alpha } } { ( k + 1 ) ^ { 2 } } \ .
$$

Then the adiabatic error is bounded as

$$
\operatorname* { m i n } _ { \theta } \big \| | \psi _ { t _ { f } } ( 1 ) \rangle - e ^ { i \theta } | \varepsilon _ { 0 } ( 1 ) \rangle \big \| \leq c _ { 1 } \frac { C } { \Delta } e ^ { - \big ( c _ { 2 } \frac { \Delta ^ { 3 } } { C ^ { 2 } } t _ { f } \big ) ^ { \frac { 1 } { 1 + \alpha } } }
$$

where $\begin{array} { r } { c _ { 1 } = e R \left( \frac { 8 \pi ^ { 2 } } { 3 } \right) ^ { 3 } } \end{array}$ and $\begin{array} { r } { c _ { 2 } = \frac { 1 } { 4 e R ^ { 2 } } \left( \frac { 3 } { 4 \pi ^ { 2 } } \right) ^ { 5 } . } \end{array}$

Thus, as long as $t _ { f } \gg \frac { C ^ { 2 } } { \Delta ^ { 3 } }$ , the adiabatic error is exponentially small in $t _ { f }$ .

The idea of using vanishing boundary derivatives dates back at least to (Garrido, L. M. and Sancho, F. J., 1962). It was also used in (Lidar et al., 2009) for a different class of functions than the Gevrey class: functions that are analytic in a strip of width $2 \gamma$ in the complex time plane and have a finite number $V$ of vanishing boundary derivatives, i.e., $H ^ { ( v ) } ( 0 ) = H ^ { ( v ) } ( 1 ) = 0 \ \forall v \in [ 1 , V ]$ . The adiabatic error is then upper-bounded by $( V + 1 ) ^ { \gamma + 1 } q ^ { - V }$ as along as $\begin{array} { r } { t _ { f } \geq \frac { q } { \gamma } V \operatorname* { m a x } _ { s } \left\| H _ { V } ^ { ( 1 ) } ( s ) \right\| ^ { 2 } / \Delta ^ { 3 } } \end{array}$ , where $q > 1$ is a parameter that can be optimized given knowledge of $\left\| H _ { V } ^ { ( 1 ) } \right\|$ Thus, the adiabatic error can be made arbitrarily small in the number of vanishing derivatives, while the scaling of $t _ { f }$ with $V$ is encoded into $\left\| H _ { V } ^ { ( 1 ) } \right\|$ An example of a function whose first $V$ derivatives vanish at the boundaries $s = 0 , 1$ is the regularized $\beta$ function $\begin{array} { r } { A ( s ) = \frac { \int _ { 0 } ^ { s } x ^ { V } \left( 1 - x \right) ^ { V } d x } { \int _ { 0 } ^ { 1 } x ^ { V } \left( 1 - x \right) ^ { V } d x } } \end{array}$ (Rezakhani et al., 2010b). It is possible to further reduce the error quadratically in $t _ { f }$ using an interference effect that arises from imposing an additional boundary symmetry condition (Wiebe and Babcock, 2012).

Note that an important difference between Theorems 2 and 3 is that the former applies for all times $s \in [ 0 , 1 ]$ (“instantaneous AT”), while the latter applies only at the final time $s = 1$ (“final-time AT”), which typically gives rise to tighter error bounds.

Also note that Landau and Zener already showed that the transition probability out of the ground state is $O ( e ^ { - C \Delta ^ { 2 } t _ { f } } )$ (C. Zener, 1932; Landau, L. D., 1932) [see (Joye, 1994) for a rigorous proof for analytic Hamiltonians], thus combining an inverse gap square dependence with an exponentially small error bound. However, this result only holds for two-level systems.

# 4. Lower bound

Let $H ( s )$ , with $s \in [ 0 , 1 ]$ , be a given continuous Hamiltonian path and $\vert \varepsilon ( s ) \rangle$ the corresponding non-degenerate eigenstate path (eigenpath). In the so-called black-box model the only assumption is to be able to evolve with $H [ s ( t ) ]$ for some schedule $s ( t )$ (here $s$ is allowed to be a general function of $t$ ), without exploiting the unknown structure of $H ( s )$ . Define the path length $L$ as:

$$
L = \int _ { 0 } ^ { 1 } \| | \dot { \varepsilon } ( s ) \rangle \| d s ,
$$

where dot denotes $\partial _ { s }$ . Assuming, without loss of generality, that the phase of $\vert \varepsilon ( s ) \rangle$ is chosen so that $\langle \varepsilon ( s ) | \dot { \varepsilon } ( s ) \rangle =$ $0$ , then $L$ is the only natural length in projective Hilbert space (up to irrelevant normalization factors).

It was shown in (Boixo and Somma, 2010) that there is a lower bound on the time required to prepare $\vert \varepsilon ( 1 ) \rangle$ from $\left| \varepsilon ( 0 ) \right.$ with bounded precision:

$$
t _ { f } > O ( L / \Delta ) .
$$

Since an upper bound on $L$ is $\operatorname* { m a x } _ { s } \| \dot { H } ( s ) \| / \Delta$ , $_ { 1 2 }$ one obtains the estimate $t _ { f } \sim O ( \operatorname* { m a x } _ { s } \| \dot { H } ( s ) \| / \Delta ^ { 2 } )$ , reminiscent of the approximate versions of the adiabatic condition [e.g., Eq. (5)]. The proof of the lower bound is essentially based on the optimality of the Grover search algorithm.

The lower bound is nearly achievable using a “digital”, non-adiabatic method proposed in (Boixo et al., 2010), that does not require path continuity or differentiability. The time required scales as ${ \cal O } [ ( L / \Delta ) \log ( L / \epsilon ) ]$ , where $\epsilon$ is a specified bound on the error of the output state $\vert \varepsilon ( 1 ) \rangle$ . $L$ is the angular length of the path and is suitably defined to generalize Eq. (13) to the non-differentiable case.

Armed with an arsenal of adiabatic theorems we are now well equipped to start surveying AQC algorithms.

# III. ALGORITHMS

In this section we review the algorithms which are known to provide quantum speedups over classical algorithms. However, to make the idea of a quantum speedup precise we need to draw distinctions among different types of speedups, as several such types will arise in the course of this review. Toward this end we adopt a classification of quantum speedup types proposed in (Rønnow et al., 2014). The classification is the following, in decreasing order of strength.

A “provable” quantum speedup is the case where there exists a proof that no classical algorithm can outperform a given quantum algorithm. The best known example is Grover’s search algorithm (Grover, 1997), which, in the query complexity setting, exhibits a provable quadratic speedup over the best possible classical algorithm (Bennett et al., 1997).

• A “strong” quantum speedup was originally defined in (Papageorgiou and Traub, 2013) by comparing a quantum algorithm against the performance of the best classical algorithm, whether such a classical algorithm is explicitly known or not. This aims to capture computational complexity considerations allowing for the existence of yet-to-be discovered classical algorithms. Unfortunately, the performance of the best possible classical algorithm is unknown for many interesting problems (e.g., for factoring).

A “quantum speedup” (unqualified, without adjectives) is a speedup against the best available classical algorithm [for example Shor’s polynomial time factoring algorithm (Shor, 1994)]. Such a speedup may be tentative, in the sense that a better classical algorithm may eventually be found.

• Finally, a “limited quantum speedup” is a speedup obtained when compared specifically with classical algorithms that ‘correspond” to the quantum algorithm in the sense that they implement the same algorithmic approach, but on classical hardware.

This definition allows for the existence of other classical algorithms that are already better than the quantum algorithm. The notion of a limited quantum speedup will turn out to be particularly useful in the context of StoqAQC.

A refinement of this classification geared at experimental quantum annealing was given in (Mandr\`a et al., 2016).

Using this classification, this section collects most of the adiabatic quantum algorithms known to give a provable quantum speedup (Grover, Deutsch-Jozsa, Bernstein-Vazirani, and glued trees), or just a quantum speedup (PageRank).13

Many other adiabatic algorithms have been proposed, and we review a large subset of these in Sec. VI. In a few of these cases there is a scaling advantage over classical simulated annealing, while in some cases there are definitely faster classical algorithms.

# A. Adiabatic Grover

The adiabatic Grover algorithm (Roland and Cerf, 2002) is perhaps the hallmark example of a provable quantum speedup using AQC, so we review it in detail. As in the circuit model Grover algorithm (Grover, 1997), informally the objective is to find the marked item (or possibly multiple marked items) in an unsorted database of $N$ items by accessing the database as few times as possible. More formally, one is allowed to call a function $f : \{ 0 , 1 \} ^ { n } \mapsto \{ 0 , 1 \}$ (where $N = 2 ^ { \pi }$ is the number of bit strings) with the promise that $f ( m ) = 1$ and $f ( x ) = 0$ $\forall x \neq m$ , and the goal is to find the unknown index $m$ in the smallest number of calls. This is an oracular problem (Nielsen and Chuang, 2000), in that the algorithm can make queries to an oracle that recognizes the marked items. The oracle remains a black box, i.e., the details of its implementation and its complexity are ignored. This allows for an uncontroversial determination of the complexity of the algorithm in terms of the number of queries to the oracle.

For a classical algorithm, the only strategy is to query the oracle until the marked item is found. Whether the classical algorithm uses no memory, i.e., the algorithm does not keep track of items that have already been checked, or uses an exponential amount of memory (in $n$ ) to store all the items that have been checked, the classical algorithm will have an average number of queries that scales linearly in $N$ .

In the AQC algorithm we denote the marked item by the binary representation of $m$ . The oracle is defined in terms of the final Hamiltonian $H _ { 1 } = \mathbb { 1 } - | m \rangle \langle m |$ , where $| m \rangle$ is the marked state associated with the marked item. In this representation, the binary representations give the eigenvalues under $\sigma ^ { z }$ , i.e., $\sigma ^ { z } | 0 \rangle = + | 0 \rangle$ and $\sigma ^ { z } | 1 \rangle = - | 1 \rangle$ . The marked state is the ground state of this Hamiltonian with energy $0$ , and all other computational basis states have energy 1.

# 1. Setup for the adiabatic quantum Grover algorithm

We use the initial Hamiltonian $H _ { 0 } = 1 1 - | \phi \rangle \langle \phi |$ , where $| \phi \rangle$ is the uniform superposition state,

$$
 { \left| \phi \right. } = \frac { 1 } { \sqrt { N } } \sum _ { i = 0 } ^ { N - 1 }  { \left| i \right. } =  { \left| + \right. } ^ { \otimes n } \ ,
$$

where $\begin{array} { r } { | \pm \rangle = \frac { 1 } { \sqrt { 2 } } ( | 0 \rangle \pm | 1 \rangle ) } \end{array}$ . We take the time-dependent Hamiltonian to be an interpolation:

$$
\begin{array} { r l r } {  { H ( s ) = [ 1 - A ( s ) ] H _ { 0 } + A ( s ) H _ { 1 } } } & { { } ( 1 } \\ & { { } } & { = [ 1 - A ( s ) ] ( \mathbb { 1 } - | \phi \rangle \langle \phi | ) + A ( s ) ( \mathbb { 1 } - | m \rangle \langle m | ) , } \end{array}
$$

where $s = t / t _ { f } \in [ 0 , 1 ]$ is the dimensionless time, $t _ { f }$ is the total computation time, and $A ( s )$ is a “schedule” that can be optimized. For simplicity, we first consider a linear schedule: $A ( s ) = s$ . Note that $H _ { 1 }$ is $n$ -local.

If the initial state is initialized in the ground state of $H ( 0 )$ , i.e., $| \psi ( 0 ) \rangle = | \phi \rangle$ , then the evolution of the system is restricted to a two-dimensional subspace, defined by the span of $| m \rangle$ and $\begin{array} { r } { | m ^ { \perp } \rangle \ = \ \frac { 1 } { \sqrt { N - 1 } } \sum _ { i \neq m } ^ { N - 1 } | i \rangle } \end{array}$ 1 PN−1i=m |ii. In this two-dimensional subspace $H ( s )$ can be written as:

$$
[ H ( s ) ] _ { | m \rangle , | m ^ { \bot } \rangle } = { \frac { 1 } { 2 } } \mathbb { 1 } _ { 2 \times 2 } - { \frac { \Delta ( s ) } { 2 } } \left( \begin{array} { c c } { \cos \theta ( s ) } & { \sin \theta ( s ) } \\ { \sin \theta ( s ) } & { - \cos \theta ( s ) } \end{array} \right) ,
$$

where:

$$
\begin{array} { c } { { \displaystyle \Delta ( s ) = \sqrt { ( 1 - 2 s ) ^ { 2 } + \frac { 4 } { N } s ( 1 - s ) } \ , } } \\ { { \displaystyle \cos \theta ( s ) = \frac { 1 } { \Delta ( s ) } \left[ 1 - 2 ( 1 - s ) \left( 1 - \frac { 1 } { N } \right) \right] \ , } } \\ { { \displaystyle \sin \theta ( s ) = \frac { 2 } { \Delta ( s ) } ( 1 - s ) \frac { 1 } { \sqrt { N } } \sqrt { 1 - \frac { 1 } { N } } \ . } } \end{array}
$$

The eigenvalues and eigenvectors in this subspace are then given by:

$$
\begin{array} { c c } { { \varepsilon _ { 0 } ( s ) = \displaystyle \frac { 1 } { 2 } \left( 1 - \Delta ( s ) \right) ~ , } } & { { \varepsilon _ { 1 } ( s ) = \displaystyle \frac { 1 } { 2 } \left( 1 + \Delta ( s ) \right) ~ , } } \\ { { } } & { { } } \\ { { \displaystyle | \varepsilon _ { 0 } ( s ) \rangle = \cos \displaystyle \frac { \theta ( s ) } { 2 } | m \rangle + \sin \displaystyle \frac { \theta ( s ) } { 2 } | m ^ { \perp } \rangle ~ , } } & { { ( 1 } } \\ { { } } & { { } } \\ { { \displaystyle | \varepsilon _ { 1 } ( s ) \rangle = - \sin \displaystyle \frac { \theta ( s ) } { 2 } | m \rangle + \cos \displaystyle \frac { \theta ( s ) } { 2 } | m ^ { \perp } \rangle ~ . } } & { { ( 1 } } \end{array}
$$

The remaining $N - 2$ eigenstates of $H ( s )$ have eigenvalue 1 throughout the evolution. The minimum gap occurs at $s = 1 / 2$ and scales exponentially with $n$ :

$$
\Delta _ { \mathrm { m i n } } = \Delta ( s = 1 / 2 ) = \frac { 1 } { \sqrt { N } } = 2 ^ { - n / 2 } ~ .
$$

(This can be viewed as a special case of Lemma $^ { 1 }$ below.)

In our discussion of the adiabatic theorem we saw that without special assumptions on $s ( t )$ except that it is twice differentiable, the adiabatic condition is inferred from Eq. (7), which requires setting $t _ { f } \gg$ $\begin{array} { r } { 2 \operatorname* { m a x } _ { s } \| \partial _ { s } H ( s ) \| / \Delta ^ { 2 } ( s ) + \int _ { 0 } ^ { 1 } \| \partial _ { s } H ( s ) \| ^ { 2 } / \Delta ^ { 3 } ( s ) d s } \end{array}$ , where we have accounted for the boundary conditions and used the positivity of the integrand to extend the upper limit to 1.14 Differentiating Eq. (17) yields

$$
\partial _ { s } H ( s ) = \left( \begin{array} { c c } { { - \left( 1 - \frac 1 N \right) } } & { { \frac 1 { \sqrt { N } } \sqrt { 1 - \frac 1 N } } } \\ { { \frac 1 { \sqrt { N } } \sqrt { 1 - \frac 1 N } } } & { { 1 - \frac 1 N } } \end{array} \right) \ ,
$$

which has eigenvalues $\pm \sqrt { 1 - \frac { 1 } { N } }$ , so that $\| \partial _ { s } H \| \ \leq$ $1$ . The other integrand in Eq. (7), involving $\left\| \partial _ { s } ^ { 2 } H ( s ) \right\| / \Delta ^ { 2 } ( s )$ , vanishes after differentiating Eq. (21). The ground state degeneracy $m ( s ) ~ = ~ 1$ throughout. Since $\begin{array} { r } { \int _ { 0 } ^ { s } 1 / \Delta ^ { 3 } ( x ) d x = \frac { N } { 2 } - \frac { N ^ { 3 / 2 } ( 1 - 2 s ) } { 2 \sqrt { N ( 1 - 2 s ) ^ { 2 } + 4 ( 1 - s ) s } } } \end{array}$ , which is a monotonically increasing function of $N = { \Delta } _ { \operatorname* { m i n } } ^ { - 2 }$ as $s \to 1$ , the adiabatic con $s$ that approaches ition becomes

$$
t _ { f } \gg 2 \operatorname* { m a x } _ { s } \frac { 1 } { \Delta ^ { 2 } ( s ) } + \int _ { 0 } ^ { 1 } d s \frac { 1 } { \Delta ^ { 3 } ( s ) } = \frac { 3 } { \Delta _ { \mathrm { m i n } } ^ { 2 } } \ .
$$

This suggests the disappointing conclusion that the quantum adiabatic algorithm scales in the same way as the classical algorithm.

However, by imposing the adiabatic condition globally, i.e., to the entire time interval $t _ { f }$ , the evolution rate is constrained throughout the whole computation, while the gap only becomes small around $s = 1 / 2$ . Thus, it makes sense to use a schedule $A ( s )$ that adapts and slows down near the minimum gap, but speeds up away from it (van Dam et al., 2001; Roland and Cerf, 2002) [this is related to the idea of rapid adiabatic passage, which has a long history in nuclear magnetic resonance (Powles, 1958)]. By doing so the quadratic quantum speedup can be recovered, as we address next.

Consider again the adiabatic condition (7), which we can rewrite as:

$$
t _ { f } \gg 2 \operatorname* { m a x } _ { s } \frac { \| \partial _ { s } H ( s ) \| } { \Delta ^ { 2 } ( s ) } + \int _ { 0 } ^ { 1 } \left( \frac { \left\| \partial _ { s } ^ { 2 } H \right\| } { \Delta ^ { 2 } } + \frac { \left\| \partial _ { s } H \right\| ^ { 2 } } { \Delta ^ { 3 } } \right) d s ,
$$

where now $H$ and $\Delta$ depend on a schedule $A ( s )$ . Let us now use the ansatz (Jansen et al., 2007; Roland and Cerf, 2002)

$$
\partial _ { s } A = c \Delta ^ { p } [ A ( s ) ] \ , \quad A ( 0 ) = 0 \ , \quad p , c > 0 \ .
$$

This schedule slows down as the gap becomes smaller, as desired. The normalization constant $c \quad = { }$ $\begin{array} { r } { \int _ { 0 } ^ { 1 } \Delta ^ { - p } [ A ( s ) ] \partial _ { s } A d s = \int _ { A ( 0 ) } ^ { A ( 1 ) } \Delta ^ { - p } ( u ) d u } \end{array}$ [using $u = A ( s ) ]$ is chosen to ensure that $A ( 1 ) = 1$ .

It follows that:

$$
\begin{array} { l l l l } { \displaystyle \int _ { 0 } ^ { 1 } \left( \frac { \left\| \partial _ { s } ^ { 2 } H [ A ( s ) ] \right\| } { \Delta ^ { 2 } [ A ( s ) ] } + \frac { \| \partial _ { s } H [ A ( s ) ] \| ^ { 2 } } { \Delta ^ { 3 } [ A ( s ) ] } \right) d s } \\ { \displaystyle \leq 4 c \int _ { 0 } ^ { 1 } \Delta ^ { p - 3 } ( u ) d u } \end{array}
$$

(the proof is given in Appendix A.2). Finally, the boundary term in Eq. (23) yields $\begin{array} { r } { 2 \operatorname* { m a x } _ { s } \frac { \| \partial _ { s } H ( s ) \| } { \Delta ^ { 2 } ( s ) } \leq 4 c \Delta _ { \operatorname* { m i n } } ^ { p - 2 } } \end{array}$ .

The case $p \ : = \ : 2$ serves to illustrate the main point. In this case the boundary term is $_ { 4 c }$ and evaluating the integrals yields

$$
\begin{array} { l } { { c = \displaystyle \int _ { 0 } ^ { 1 } \Delta ^ { - 2 } ( u ) d u = \frac { N } { \sqrt { N - 1 } } \tan ^ { - 1 } \sqrt { N - 1 } \to \frac { \pi } { 2 } \sqrt { N } } } \\ { { \displaystyle \int _ { 0 } ^ { 1 } \Delta ^ { - 1 } ( u ) d u = \frac { \log \Big [ \frac { \sqrt { N - 1 } \sqrt { N } + N - 1 } { \sqrt { N - 1 } \sqrt { N } - ( N - 1 ) } \Big ] } { 2 \sqrt { \frac { N - 1 } { N } } } \to \log ( 2 N ) / 2 \ , } } \end{array}
$$

where the asymptotic expressions are for $N \gg 1$ . Substituting this into Eq. (25) yields the adiabatic condition

$$
t _ { f } \gg 2 \pi \sqrt { N } [ 1 + \log ( 2 N ) ] ,
$$

which is a sufficient condition for the smallness of the adiabatic error, and nearly recovers the quadratic speedup expected from Grover’s algorithm.

The appearance of the logarithmic factor latter is actually an artifact of using bounds that are not tight.15 The quadratic speedup, i.e., the scaling of $t _ { f }$ with $\sqrt { N }$ , can be fully recovered by solving for the schedule from Eq. (24) in the $p = 2$ case (Roland and Cerf, 2002). We first rewrite Eq. (24) in dimensional time units as $\partial _ { t } A =$ $c ^ { \prime } \Delta ^ { 2 } [ A ( t ) ]$ , with the boundary conditions $A ( 0 ) = 0$ and $A ( t _ { f } ) = 1$ ;. To solve this differential equation we rewrite it as t = R t0 dt = R A(t)A(0) $\begin{array} { r } { t = \int _ { 0 } ^ { t } d t = \int _ { A ( 0 ) } ^ { A ( t ) } d A / [ c ^ { \prime } \Delta ^ { 2 } ( A ) ] } \end{array}$ . After integration we obtain

$$
\begin{array} { l } { { \displaystyle t = \frac { N } { 2 c ^ { \prime } \sqrt { N - 1 } } \left[ \tan ^ { - 1 } \left( \sqrt { N - 1 } \left( 2 A ( t ) - 1 \right) \right) \right. } } \\ { { \displaystyle \left. + \tan ^ { - 1 } \sqrt { N - 1 } \right] \ . } } \end{array}
$$

Evaluating Eq. (27) at $t _ { f }$ gives:

$$
t _ { f } = { \frac { N } { c ^ { \prime } \sqrt { N - 1 } } } \tan ^ { - 1 } \sqrt { N - 1 } \to { \frac { \pi } { 2 c ^ { \prime } } } \sqrt { N } ,
$$

which is the expected quadratic quantum speedup.

One may be tempted to conclude that $t _ { f }$ can be made arbitrarily small since so far $c ^ { \prime }$ is arbitrary and can be chosen to be large. However, the adiabatic error bound (26) shows that this is not the case: while it is not tight, it suggests that if $t _ { f }$ scales as $\sqrt { N }$ then $c ^ { \prime }$ must scale as $1 / \log ( 2 N )$ in order to keep the adiabatic error small. Thus, the general conclusion is that increasing $c ^ { \prime }$ results in a larger adiabatic error.16

Inverting Eq. (27) for $A ( t )$ [or, equivalently, solving Eq. (24) for $p = 2$ ] gives the locally optimized schedule

$$
A ( s ) = \frac { 1 } { 2 } + \frac { 1 } { 2 \sqrt { N - 1 } } \tan \left[ ( 2 s - 1 ) \tan ^ { - 1 } \sqrt { N - 1 } \right] \ ,
$$

where we replaced $t / t _ { f }$ [with $t _ { f }$ given by Eq. (28)] with $s$ . As expected, this schedule rises rapidly near $s = 0 , 1$ and is nearly flat around $s = 1 / 2$ , i.e., it slows down near the minimum gap.

Since the choice in Eq. (24) is not unique, we may wonder if there exists a schedule that gives an even better scaling. Given that Grover’s algorithm is known to be optimal in the circuit model setting (Bennett et al., 1997; Zalka, 1999), this is, unsurprisingly, not the case, and a general argument to that effect which applies to any Hamiltonian quantum computation was given by (Farhi and Gutmann, 1998). We review this argument in the AQC setting, in Appendix B.

# 3. Multiple marked states

The present results generalize easily to the case where we have $M \geq 1$ marked states, for which Grover’s algorithm is known to also give a quadratic speedup in the

circuit model (Biham et al., 1999; Boyer et al., 1998). The final Hamiltonian can be written as:

$$
H _ { 1 } = 1 1 - \sum _ { m \in \mathcal { M } } | m \rangle \langle m | ,
$$

where $\mathcal { M }$ is the index set of the marked states. Let:

$$
| m _ { \perp } \rangle = \frac { 1 } { \sqrt { N - M } } \sum _ { i \notin { \mathcal { M } } } | i \rangle \langle i | ~ .
$$

Instead of evolving in a two-dimensional subspace, the system evolves in an $M + 1$ dimensional subspace spanned by $( \{ | m \rangle \} _ { m \in \mathcal { M } } , | m _ { \bot } \rangle )$ , and instead of Eq. (17), the Hamiltonian can be written in this basis as:

$$
H ( s ) = \left( \begin{array} { c c c c c } { \left( 1 - s \right) \left( 1 - \frac { 1 } { N } \right) } & { - \frac { 1 - s } { N } } & { \cdots } & { } & { - \left( 1 - s \right) \frac { \sqrt { N - M } } { N } } \\ { - \frac { 1 - s } { N } } & { \left( 1 - s \right) \left( 1 - \frac { 1 } { N } \right) } & { - \frac { 1 - s } { N } } & { \cdots } & { } & { - \left( 1 - s \right) \frac { \sqrt { N - M } } { N } } \\ { \vdots } & { \ddots } & { } & { \vdots } \\ { - \left( 1 - s \right) \frac { \sqrt { N - M } } { N } } & { - \left( 1 - s \right) \frac { \sqrt { N - M } } { N } } & { \cdots } & { } & { s + \left( 1 - s \right) \left( 1 - \frac { N - M } { N } \right) } \end{array} \right) .
$$

This Hamiltonian can be easily diagonalized, and one finds that there are $M - 1$ eigenvalues equal to $1 - s$ , and two eigenvalues

$$
\lambda _ { \pm } = \frac { 1 } { 2 } \pm \frac { 1 } { 2 } \sqrt { ( 1 - 2 s ) ^ { 2 } + \frac { 4 M } { N } s ( 1 - s ) } \ ,
$$

that determine the relevant minimum gap: $\begin{array} { r l } { \Delta ( s ) } & { { } = } \end{array}$ $\begin{array} { r } { \sqrt { ( 1 - 2 s ) ^ { 2 } + \frac { 4 M } { N } s ( 1 - s ) } } \end{array}$ . The remaining $N \mathrm { ~ - ~ } M \mathrm { ~ - ~ } 1$ eigenvalues of the unrestricted Hamiltonian are equal to 1, Comparing the $M = 1$ case Eq. (18a) to the present case, the only difference is the change from $1 / N$ to $M / N$ . Therefore our discussion from earlier goes through with only this modification.

In closing, we note that an experimentally realizable version of the adiabatic Grover search algorithm using a single bosonic particle placed in an optical lattice was recently proposed in (Hen, 2017).

# B. Adiabatic Deutsch-Jozsa algorithm

Given a function $f : \{ 0 , 1 \} ^ { n } \mapsto \{ 0 , 1 \}$ which is promised to be either constant or balanced [i.e., $f ( x ) = 0$ on half the inputs and $f ( x ) = 1$ on the other half], the Deutsch-Jozsa problem is to determine which type the function is. There exists a quantum circuit algorithm that solves the problem in a single $f$ -query (Deutsch and Jozsa, 1992). Classically, the problem requires $2 ^ { n - 1 } + 1$ $f$ -queries in the worst case, since it is possible that the first $2 ^ { n - 1 }$ queries return a constant answer, while the function is actually balanced. It is important to note that the quantum advantage requires a deterministic setting, since the classical error probability is exponentially small in the number of queries.

An adiabatic implementation of the Deutsch-Jozsa algorithm using unitary interpolation was given in (Sarandy and Lidar, 2005) and an implementation using a linear interpolation was given in (Wei and Ying, 2006). These algorithms match the speedup obtained in the circuit model [for an earlier example where this is not the case see (Das et al., 2002)], and we proceed to review both. We note that, just like the adiabatic Grover’s algorithm, the adiabatic Deutsch-Jozsa algorithm requires $n$ -local Hamiltonians. We also note that both the unitary interpolation and linear interpolation strategies we describe here are not unique to the Deutsch-Jozsa problem, and apply equally well to any depth-one quantum circuit. Thus they should be viewed in this more general context, and are used here with a specific algorithm for illustrative purposes.

# 1. Unitary interpolation

The initial Hamiltonian is chosen such that its ground state is the uniform superposition state $| \phi \rangle$ [Eq. (15)] and $N \ = \ 2 ^ { n }$ , i.e., $\begin{array} { r } { H ( 0 ) ~ = ~ \omega \sum _ { i = 1 } ^ { n } | - \rangle _ { i } \langle - | } \end{array}$ , where $\omega$ is the energy scale. The Deutsch-Jozsa problem can be solved by a single computation of the function $f$ through the unitary transformation $U | x \rangle = ( - 1 ) ^ { f ( x ) } | x \rangle$ ( $x \in \{ 0 , 1 \} ^ { n } )$ ) (Collins et al., 1998), so that in the $\{ | x \rangle \}$ (computational) basis $U$ is represented by the diagonal matrix $U ~ = ~ \mathrm { d i a g } [ ( - 1 ) ^ { f ( 0 ) } , . . . , ( - 1 ) ^ { f ( 2 ^ { n } - 1 ) } ]$ . An adiabatic implementation requires a final Hamiltonian $H ( 1 )$ such that its ground state is $| \psi ( 1 ) \rangle = U | \psi ( 0 ) \rangle$ . This can be accomplished via a unitary transformation of $H ( 0 )$ , i.e., $H ( 1 ) \ = \ U H ( 0 ) U ^ { \dagger }$ . Then the final Hamiltonian encodes the solution of the Deutsch problem in its ground state, which can be extracted via a measurement of the qubits in the $\{ | + \rangle , | - \rangle \}$ basis (note that this is compatible with the definition of AQC, Def. 1, which does not restrict the measurement basis). A suitable unitary interpolation between $H ( 0 )$ and $H ( 1 )$ can be defined by $H ( s ) = \tilde { U } ( s ) H ( 0 ) \tilde { U } ^ { \dagger } ( s )$ , where ${ \tilde { U } } ( s ) =$ $\exp \left( i \frac { \pi } { 2 } s U \right)$ , for which ${ \tilde { U } } ( 1 ) = i U$ . Since a unitary transformation of $H ( 0 )$ preserves its spectrum, it does not change the ground state gap, which remains $\omega$ . The run time of the algorithm can be determined from the adiabatic condition (8), and what remains is the numerator: $\begin{array} { r } { \left\| H ^ { ( 1 ) } ( s ) \right\| = \left\| i \frac { \pi } { 2 } [ U , H ( s ) ] \right\| \le \pi \| H ( 0 ) \| = \pi } \end{array}$ [and similarly for $\left\| H ^ { \left( 2 \right) } ( s ) \right\| ]$ . This yields $t _ { f } \gg 1 / \omega$ . This result is independent of $n$ so the adiabatic run time is $O ( 1 )$ .

# 2. Linear interpolation

Unitary interpolations, introduced in (Siu, 2005), are somewhat less standard. Therefore we also present the standard linear interpolation method as an alternative. Consider the usual initial Hamiltonian $H _ { 0 } = 1 1 - | \phi \rangle \langle \phi |$ over $n$ qubits, where once again $| \phi \rangle$ is the uniform superposition state. Let the final Hamiltonian be $H _ { 1 } =$ $\mathinner { \mathbb { 1 } } - | \psi \rangle _ { f } \langle \psi |$ , where

$$
| \psi \rangle _ { f } = \frac { \mu _ { f } } { \sqrt { N / 2 } } \sum _ { i = 0 } ^ { N / 2 - 1 } | 2 i \rangle + \frac { 1 - \mu _ { f } } { \sqrt { N / 2 } } \sum _ { i = 0 } ^ { N / 2 - 1 } | 2 i + 1 \rangle \ ,
$$

and where

$$
\mu _ { f } = \left. { \frac { 1 } { N } } \sum _ { x \in \{ 0 , 1 \} ^ { n } } ( - 1 ) ^ { f ( x ) } \right. \ .
$$

Clearly, $\mu _ { f } = 1$ or $0$ if $f$ is constant or balanced, respectively. Therefore $| \psi \rangle _ { f }$ is a uniform superposition over all even (odd) index states if $f$ is constant or balanced, respectively, and a measurement of the ground state of $H _ { 1 }$ in the computational basis reveals whether $f$ is constant or balanced, depending on whether the observed state belongs to the even or odd sector, respectively. However, we note that one may object to the reasonableness of the final Hamiltonian $H _ { 1 }$ . Namely, preparing the state $| \psi \rangle _ { f }$ involves precomputing the quantity $\mu _ { f }$ , which directly encodes whether $f$ is constant or balanced and so may be thought to represent an oracle that is too powerful.17

Indeed, $H _ { 1 }$ in this construction is not of the standard form $\textstyle \sum _ { x } f ( x ) | x \rangle \langle x |$ , wherein each oracle call $f ( x )$ corresponds to a query about a single basis state $| x \rangle$ . Therefore, there is no classical analogue to this oracle in the computational basis.

Setting this concern in the present version of the algorithm due to (Wei and Ying, 2006) aside, it remains to determine the adiabatic run time for the adiabatic Hamiltonian $H ( s ) = ( 1 - s ) H _ { 0 } + s H _ { 1 }$ . The following Lemma (Aharonov and Ta-Shma, 2003) comes in handy:

Lemma 1. Let $| \alpha \rangle$ and $| \beta \rangle$ be two states in some subspace of an $N$ -dimensional Hilbert space $\mathcal { H }$ , and let $H _ { \alpha } =$ $\mathinner { \hat { \pi } - \mathopen { \left| \alpha \right. } } \mathinner { \langle \alpha | }$ , $H _ { \beta } = \mathinner { \pi \mathrm { - } | { \beta } \rangle } \langle \beta |$ . For any convex combination $H _ { \eta } = ( 1 - \eta ) H _ { \alpha } + \eta H _ { \beta }$ , where $\eta \in \left[ 0 , 1 \right]$ , the ground state gap $\Delta ( H _ { \eta } ) \ge | \langle \alpha | \beta \rangle |$ .

Proof. Expand $| \beta \rangle = a | \alpha \rangle + b | \alpha ^ { \bot } \rangle$ where $\langle \alpha | \alpha ^ { \perp } \rangle = 0$ , and complete $\{ | \alpha \rangle , | \alpha ^ { \perp } \rangle \}$ to an orthonormal basis for $\mathcal { H }$ . Writing $H _ { \eta }$ in this basis yields

$$
H _ { \eta } = \left( \begin{array} { c c } { { \eta | b | ^ { 2 } } } & { { \eta a b ^ { * } } } \\ { { \eta a ^ { * } b } } & { { \eta | a | ^ { 2 } + 1 - \eta } } \end{array} \right) \oplus \mathbb { 1 } _ { ( N - 2 ) \times ( N - 2 ) } ~ .
$$

The eigenvalues of this matrix are all $1$ for the identity matrix block and the difference between the eigenvalues in the $2 \times 2$ block is $\Delta ( H _ { \eta } ) = \sqrt { 1 - 4 { \eta } ( 1 - \eta ) } | b | ^ { 2 }$ . This is minimized for $\eta = 1 / 2$ , where it equals $| a |$ . $\sqsubset$

Applying this lemma, we see that $\begin{array} { r l } { \Delta [ H ( s ) ] } & { { } \geq } \end{array}$ $| \langle \phi | \psi _ { f } \rangle | = 1 / \sqrt { 2 }$ . Since $\left\| H ^ { ( 1 ) } ( s ) \right\| \ = \ \| H _ { 1 } - H _ { 0 } \| \ \leq \ 2$ and $\left\| H ^ { ( 2 ) } ( s ) \right\| = 0$ , it follows from the adiabatic condition (8) that $t _ { f }$ is independent of $n$ , i.e., the adiabatic run time is $O ( 1 )$ as in the circuit model depth.

# 3. Interpretation

As mentioned above, a classical probabilistic algorithm that simply submits random queries to the oracle will fail with a probability that is exponentially small in the number of queries. One might thus be concerned that the adiabatic algorithms above are no better (Hen, 2014a), since they are probabilistic, in the sense that there is a non-zero probability of ending in an excited state. However, for the linear interpolation adiabatic algorithm reviewed, measuring the energy of the final state returns $0$ in the ground state or 1 in an excited state. In the latter ”inconclusive” case, the algorithm needs to be repeated until an energy of $0$ is found and only then is a computational basis measurement performed. If an even (or odd) index state is measured, the corresponding constant (or balanced) result is guaranteed to be correct. Moreover, an excited state outcome can (and should) be made exponentially unlikely using a smooth schedule as per Theorem 3. Thus, the adiabatic algorithms above improve upon a classical probabilistic algorithm in the following sense: In the adiabatic case, to know with certainty that the function is constant or balanced (an even or odd index measurement result) happens with probability $p = 1 - q$ where $q \sim e ^ { - t _ { f } }$ , where the run time $t _ { f }$ is independent of $n$ . Therefore, the expected number of runs $r$ to certainty in the adiabatic case is

$$
\langle r \rangle = \sum _ { r = 1 } ^ { \infty } p q ^ { r - 1 } r = \frac { 1 } { 1 - q } \approx 1 + q \sim 1 + e ^ { - t _ { f } } \ .
$$

On the other hand, classically, to know with certainty that the function is constant requires $N = 2 ^ { n } / 2 + 1$ runs or queries (all yielding identical outcomes).

Finally, we note that there exists a non-adiabatic Hamiltonian quantum algorithm that solves the Deutsch-Jozsa problem in constant time with a deterministic guarantee of ending up with the right answer (i.e., in the ground state) (Hen, 2014a). This algorithm is based on finding a fine-tuned schedule $s ( t )$ .

# C. Adiabatic Bernstein-Vazirani algorithm

The Bernstein-Vazirani problem (Bernstein and Vazirani, 1993) is to find an unknown binary string $a \in$ $\{ 0 , 1 \} ^ { n }$ with as few queries as possible of the function (or oracle)

$$
f _ { a } ( w ) = w \odot a \in \{ 0 , 1 \} \ ,
$$

where $\odot$ denotes the bitwise inner product modulo 2, and $w \in \{ 0 , 1 \} ^ { n }$ as well. In the quantum circuit model, it can be shown that $a$ can be determined with $O ( 1 )$ queries (Bernstein and Vazirani, 1993) whereas classical algorithms require $n$ queries (the classical algorithm tries all $n w$ ’s with a single 1 entry to identify each bit of $a$ ). This is a polynomial quantum speedup.

Before presenting the adiabatic algorithm we point out the following useful observation. For an initial state:

$$
| \Psi ( 0 ) \rangle = \sum _ { w \in \{ 0 , 1 \} ^ { n } } c _ { w } | w \rangle _ { A } \otimes | \psi _ { w } ( 0 ) \rangle _ { B } ~ , ~ \sum _ { w \in \{ 0 , 1 \} ^ { n } } | c _ { w } | ^ { 2 } = 1
$$

that undergoes an evolution according to the timedependent Hamiltonian of the form

$$
H ( s ) = \sum _ { w \in \{ 0 , 1 \} ^ { n } } | w \rangle _ { A } \langle w | \otimes H _ { w } ( s ) ~ ,
$$

we have:

$$
| \Psi ( t ) \rangle = \sum _ { w \in \{ 0 , 1 \} ^ { n } } c _ { w } | w \rangle _ { A } \otimes | \psi _ { w } ( t ) \rangle _ { B } ~ ,
$$

where

$$
\begin{array} { r l r } {  { | \psi _ { w } ( t ) \rangle _ { B } = | \psi _ { t _ { f } , w } ( s ) \rangle _ { B } } } \\ & { } & { = \mathrm { T e x p } [ - i t _ { f } \int _ { 0 } ^ { s } d \sigma H _ { w } ( \sigma ) ] | \psi _ { w } ( 0 ) \rangle _ { B } ~ , } \end{array}
$$

where Texp denotes the time-ordered exponential. To see this, simply expand the formal solution:

$$
\begin{array} { r l r } {  { | \Psi ( t ) \rangle = \mathrm { T e x p } [ - i t _ { f } \int _ { 0 } ^ { s } d \sigma H ( \sigma ) ] | \Psi ( 0 ) \rangle = } } & { { } \ ( 4 3 ) } \\ { \sum _ { w \in \{ 0 , 1 \} ^ { n } } c _ { w } | w \rangle _ { A } \otimes \mathrm { T e x p } [ - i t _ { f } \int _ { 0 } ^ { s } d \sigma H _ { w } ( \sigma ) ] | \psi _ { w } ( 0 ) \rangle _ { B } \ . } & { } \end{array}
$$

Thus for each state $| w \rangle$ in subsystem $A$ , there is an independently evolving state in subsystem $B$ . In particular, note that adiabaticity in subsystem $B$ does not depend on the size of system $A$ .

The adiabatic algorithm (Hen, 2014b) encodes the action of $f _ { a } ( w )$ in a Hamiltonian acting on two subsystems $A$ and $B$ comprising $n$ qubits and 1 qubit respectively:

$$
\begin{array} { l } { { \displaystyle H _ { 1 } = \sum _ { w \in \{ 0 , 1 \} ^ { n } } h _ { w } ~ , } } \\ { { } } \\ { { \displaystyle h _ { w } \equiv - \frac 1 2 | w \rangle _ { A } \langle w | \otimes \left( \mathbb { 1 } _ { B } + ( - 1 ) ^ { f _ { a } ( w ) } \sigma _ { B } ^ { z } \right) ~ . } } \end{array}
$$

The initial Hamiltonian is chosen to be

$$
\begin{array} { l } { { \displaystyle H _ { 0 } = \frac { 1 } { 2 } \left( \mathbb { 1 } _ { A } \otimes \left( \mathbb { 1 } _ { B } - \sigma _ { B } ^ { x } \right) \right) } } \\ { { \displaystyle \quad = \frac { 1 } { 2 } \sum _ { w \in \{ 0 , 1 \} ^ { n } } \vert w \rangle _ { A } \langle w \vert \otimes \left( \mathbb { 1 } _ { B } - \sigma _ { B } ^ { x } \right) \ . } } \end{array}
$$

Any state of the form

$$
| \Psi ( 0 ) \rangle = \sum _ { w \in \{ 0 , 1 \} ^ { n } } c _ { w } | w \rangle _ { A } \otimes | + \rangle _ { B }
$$

is a ground state of $H _ { 0 }$ , with eigenvalue $0$ . We assume that the initial state is prepared as the uniform superposition state, i.e., $c _ { w } = 2 ^ { - n / 2 } \ \forall w$ .

The total Hamiltonian is thus given by:

$$
{ \cal H } ( s ) = ( 1 - s ) H _ { 0 } + s H _ { 1 } = \sum _ { w \in \{ 0 , 1 \} ^ { n } } | w \rangle _ { A } \langle w | \otimes H _ { w } ( s ) \ ,
$$

where

$$
H _ { w } ( s ) = { \frac { 1 - s } { 2 } } \left( \mathbb { 1 } _ { B } - \sigma _ { B } ^ { x } \right) - { \frac { s } { 2 } } \left( \mathbb { 1 } _ { B } + ( - 1 ) ^ { f _ { a } ( w ) } \sigma _ { B } ^ { z } \right) ~ .
$$

The adiabatic algorithm proceeds, after preparation of the initial state, by adiabatic evolution to the final state:

$$
\begin{array} { l c l } { { | \Psi ( { t _ { f } } ) \rangle = } } & { { \displaystyle ( 4 9 ) } } \\ { { { \displaystyle { \frac { 1 } { 2 ^ { n / 2 } } } \sum _ { w \in \{ 0 , 1 \} ^ { n } } | w \rangle _ { A } \otimes \exp \left[ - i t _ { f } \int _ { 0 } ^ { 1 } \varepsilon _ { 0 , w } ( s ) d s \right] | f _ { a } ( w ) \rangle _ { B } ~ , } } } \end{array}
$$

where $\varepsilon _ { 0 , w } ( s )$ is the instantaneous ground-state energy of $H _ { w } ( s )$ , and we have used the general argument from Eqs. (39)-(42). Finally an $x$ measurement on subsystem $B$ is performed. Since we can write

$$
| f _ { a } ( w ) \rangle = \frac { 1 } { \sqrt { 2 } } \left( | + \rangle + ( - 1 ) ^ { f _ { a } ( w ) } | - \rangle \right) ,
$$

the state collapses to either of the following states with equal probability:

$$
\begin{array} { l } { { \displaystyle | \Psi _ { + } \rangle = \frac 1 { 2 ^ { n / 2 } } \sum _ { w \in \{ 0 , 1 \} ^ { n } } | w \rangle _ { A } \otimes | + \rangle _ { B } = | \Psi ( 0 ) \rangle ~ , } } \\ { { \displaystyle | \Psi _ { - } \rangle = \frac 1 { 2 ^ { n / 2 } } \sum _ { w \in \{ 0 , 1 \} ^ { n } } | w \rangle _ { A } \otimes ( - 1 ) ^ { f _ { a } ( w ) } | - \rangle _ { B } ~ . } } \end{array}
$$

Note that since $f _ { a } ( w )$ counts the number of 1-agreements between $a$ and $w$ , we can write:

$$
\sum _ { w \in \{ 0 , 1 \} ^ { n } } ( - 1 ) ^ { f _ { a } ( w ) } | w \rangle _ { A } = \bigotimes _ { k = 0 } ^ { n - 1 } ( | 0 \rangle _ { k } + ( - 1 ) ^ { a _ { k } } | 1 \rangle _ { k } ) _ { A } \ ,
$$

so that

$$
\left| \Psi _ { - } \right. = \frac 1 { 2 ^ { n / 2 } } \bigotimes _ { k = 0 } ^ { n - 1 } ( | 0 \rangle _ { k } + ( - 1 ) ^ { a _ { k } } | 1 \rangle _ { k } ) _ { A } \otimes | - \rangle _ { B } ~ .
$$

If the measurement gives $+ 1$ [i.e., Eq. (51a)], then the measured state is the initial state and no information is gained and the process must be repeated. If the measurement gives $^ { - 1 }$ , the resulting state in the $A$ subspace encodes all the bits of $a$ , since if the $k$ -th qubit is in the $| + \rangle _ { k }$ state, then $a _ { k } = 0$ and if it is in the $| - \rangle _ { k }$ state, then $a _ { k } = 1$ . The probability of failure after $m$ tries is $2 ^ { - m }$ so it is exponentially small and $n$ -independent.

The run time of the algorithm is also $n$ -independent, since only a single qubit (system B) is effectively evolving..

In conclusion, the adiabatic Bernstein Vazirani algorithm finds the unknown binary string $a$ in $O ( 1 )$ time, matching the circuit model depth. Using a similar technique, (Hen, 2014b) presented a quantum adiabatic version of Simon’s exponential-speedup period finding algorithm (Simon, 1997) [a precursor to Shor’s factoring algorithm (Shor, 1997)], again matching the circuit model depth scaling. An important aspect of these quantum adiabatic constructions is that they go beyond the general-purpose (and hence suboptimal) polynomialequivalence prescription of universality proofs that map circuit-based algorithms into quantum-adiabatic ones (see Section IV). That equivalence does not necessarily preserve a polynomial quantum speedup, whereas the construction in (Hen, 2014b) discussed here does.

# D. The glued trees problem

Consider two binary trees, each of depth $n$ . Each tree has Pnj=0 $\textstyle \sum _ { j = 0 } ^ { n } 2 ^ { j } \ = \ 2 ^ { n + 1 } \ - \ 1$ vertices, for a total of $N = 2 ^ { n + 2 } - 2$ vertices, each labelled by a randomly chosen $2 n$ -bit string. The two trees are randomly glued as shown in Fig. 1. More specifically, choose a leaf on the left end at random and connect it to a leaf on the right end chosen at random. Then connect the latter to a leaf on the left chosen randomly among the remaining ones, and so on, until every leaf on the left is connected to two leaves on the right (and vice versa). This creates a random cycle that alternates between the leaves of the two trees. The problem is, starting from the left root, to find a path to the right root in the smallest possible number of steps, while traversing the tree as in a maze. I.e., keeping a record of one’s moves is allowed, but at any given vertex one can only see the adjacent vertices. More formally, an oracle outputs the adjacent vertices of a given input vertex (note that the roots of the trees are the only vertices with adjacency two, so it is easy to check if the right root was found). The problem is, given the name of the left root and access to the oracle, to find the name of the right root in the smallest number of queries. Classical algorithms require at least a subexponential in $n$ number of oracle calls, but there exists a polynomial-time quantum algorithm based on quantum walks for solving this problem (Childs et al., 2003). A polynomial-time quantum almost-adiabatic algorithm was given in (Somma et al., 2012). The qualifier “almost” is important: the algorithm is not adiabatic during the entire evolution, since it explicitly requires a transition from the ground state to the first excited state and back. We now review the algorithm, which (so far) provides the only example of a (sub-)exponential almost-adiabatic quantum speedup.

Let us denote the bit-string corresponding to the first root by $a _ { 0 }$ and the second root by $a N - 1$ . Define the diagonal (in the computational basis) Hamiltonians

$$
H _ { 0 } = - | a _ { 0 } \rangle \langle a _ { 0 } | \ , H _ { 1 } = - | a _ { N - 1 } \rangle \langle a _ { N - 1 } | \ ,
$$

and the states

$$
| c _ { j } \rangle = \frac { 1 } { \sqrt { N _ { j } } } \sum _ { i \in j \mathrm { - t h ~ c o l u m n } } | a _ { i } \rangle \ ,
$$

which are a uniform superposition over the vertices in the $j$ -th column with $N _ { j } = 2 ^ { j }$ for $0 \leq j \leq n$ and $N _ { j } =$ $2 ^ { 2 n + 1 - j }$ for $n + 1 \leq j \leq 2 n + 1$ . Note that $\left| c _ { 0 } \right. = \left| a _ { 0 } \right.$ and $| c _ { 2 n + 1 } \rangle = | a _ { N - 1 } \rangle$ . Let us define the Hamiltonian $A$ associated with the oracle as having the following nonzero matrix elements:

$$
\langle c _ { j } | A | c _ { j + 1 } \rangle = \left\{ \begin{array} { l } { { \sqrt { 2 } \quad j = n } } \\ { { 1 \quad \mathrm { o t h e r w i s e } } } \end{array} \right.
$$

We then pick as our interpolating Hamiltonian:

$$
H ( s ) = ( 1 - s ) \alpha H _ { 0 } - s ( 1 - s ) A + s \alpha H _ { 1 }
$$

where $\alpha \in ( 0 , 1 / 2 )$ is a constant (independent of $n$ ) and $s ( t )$ is the schedule. Note that a unitary evolution according to this Hamiltonian will keep a state within the subspace spanned by $\{ | c _ { j } \rangle \}$ if the state is initially within that subspace. Since the instantaneous ground state at $s = 0 \left( \left| a _ { 0 } \right. \right)$ is in this subspace, it suffices to only consider this subspace. Because of the form of the Hamiltonian, the eigenvalue spectrum is symmetric about $s = 1 / 2$ .

In this subspace, at $s _ { \times } = \alpha / \sqrt { 2 }$ (and by symmetry at $1 - s _ { \times } ,$ ), the energy gap between the ground state and the first excited state closes exponentially in $n$ . This is depicted in Fig. 2, where $s _ { 1 } , s _ { 2 }$ represent the region around $s _ { \times }$ and $s _ { 3 } , s _ { 4 }$ represent the region around $1 - s _ { \times }$ . In the regions $s \in [ 0 , s _ { 1 } )$ , $s \in [ s _ { 2 } , s _ { 3 } )$ , and $s \in [ s _ { 4 } , 1 ]$ , the energy gap between the ground state and first excited state is lower-bounded by $c / n ^ { 3 }$ . The gap between the first and second excited states is lower-bounded by $c ^ { \prime } / n ^ { 3 }$ throughout the evolution. Both $c , c ^ { \prime } > 0$ .

![](images/be4118b416fd6480c5d741208a7cd2026e142124d1569bf3745c9d27fefe2a82.jpg)  
FIG. 1 A glued tree with $n = 4$ . The labeling $j$ from Eq. (55) is depicted on top of the tree.

The proposed evolution exploits the symmetry and gap structure of the spectrum as follows. A schedule is chosen that guarantees adiabaticity only if the energy gap scales as $1 / n ^ { 3 }$ . Then, during $s \in [ 0 , s _ { 1 } )$ , the desired evolution is sufficiently adiabatic that it follows the instantaneous ground state. During $s \in [ s _ { 1 } , s _ { 2 } )$ , the evolution is nonadiabatic (since the gap scales as $1 / e ^ { n }$ ) and a transition to the first excited state occurs with high probability. During $s ~ \in ~ [ s _ { 2 } , s _ { 3 } )$ , the evolution is again sufficiently adiabatic that it follows the instantaneous first excited state. During $s \in [ s _ { 3 } , s _ { 4 } )$ , the evolution is again nonadiabatic and a transition from the first excited state back to the ground state occurs with high probability. During $s \in [ s _ { 4 } , 1 ]$ , the evolution is again adiabatic and follows the instantaneous ground state.

Since $\begin{array} { r } { t _ { f } \ = \ \int _ { 0 } ^ { 1 } d s ( d s / d t ) ^ { - 1 } \ \sim \ n ^ { 6 } } \end{array}$ , we conclude that $\left| a _ { N - 1 } \right.$ can be found in polynomial time.

# E. Adiabatic PageRank algorithm

We review the adiabatic quantum algorithm from (Garnerone et al., 2012) that prepares a state containing the same ranking information as the PageRank vector. The latter is a central tool in data mining and information retrieval, at the heart of the success of the Google search engine (Brin and Page, 1998). Using the adiabatic algorithm, the extraction of the full PageRank vector cannot, in general, be done more efficiently than when using the best classical algorithms known. However, there are particular graph-topologies and specific tasks of relevance in the use of search engines (such as finding just the top-ranked entries) for which the quantum algorithm, combined with other known quantum protocols, may provide a polynomial, or even exponential quantum speedup. Note that unlike the previous algorithms we reviewed in this section, which all provided a provable quantum speedup, the current algorithm provides a “regular” quantum speedup, in the sense that it outperforms all currently known classical algorithms, but better future classical algorithms have not been ruled out.

![](images/7cff1488ff6d8ef762cfc7d518b44a7ca2debbe47644c523664bc30108be0047.jpg)  
FIG. 2 The ground state ( $\lambda _ { 0 } ( s )$ , blue solid curve), first excited state $\lambda _ { 1 } ( s )$ , red dashed curve) and second excited state ( $\lambda _ { 2 } ( s )$ yellow dot-dashed curve) of the glued-trees Hamilto-√ nian (57) for $\alpha = 1 / \sqrt { 8 }$ and $n = 6$ . Inside the region $[ s _ { 1 } , s _ { 2 } ]$ and $[ s _ { 3 } , s _ { 4 } ]$ , the gap between the ground state and first excited state $\Delta _ { 1 0 }$ closes exponentially with $n$ . In the region $[ s _ { 2 } , s _ { 3 } ]$ , the gap between the ground state and first excited state $\Delta _ { 1 0 }$ and the gap between the first excited state and second excited state $\Delta _ { 2 1 }$ are bounded by $n ^ { - 3 }$ . Similarly, in the region $[ s _ { 4 } , 1 ]$ , the gap between the ground state and first excited state $\Delta _ { 1 0 }$ is bounded by $n ^ { - 3 }$ .

# 1. Google matrix and PageRank

PageRank can be seen as the stationary distribution of a random walker on the web-graph, which spends its time on each page in proportion to the relative importance of that page (Langville and Meyer, 2006).

To model this define the transition matrix $P _ { 1 }$ associated with the (directed) adjacency matrix $A$ of the graph

$$
P _ { 1 } ( i , j ) = { \left\{ \begin{array} { l l } { 1 / d ( i ) } & { { \mathrm { i f ~ } } ( i , j ) { \mathrm { ~ i s ~ a n ~ e d g e ~ o f ~ } } A ; } \\ { 0 } & { { \mathrm { e l s e } } , } \end{array} \right. }
$$

where $d ( i )$ is the out-degree of the $\imath$ th node.

The rows having zero matrix elements, corresponding to dangling nodes, are replaced by the vector $\vec { e } / n$ whose entries are all $1 / n$ , where $n$ is the number of pages or nodes, i.e., the size of the web-graph. Call the resulting (right) stochastic matrix $P _ { 2 }$ . However, there could still be subgraphs with in-links but no out-links. Thus one

$$
G : = \alpha P _ { 2 } ^ { T } + ( 1 - \alpha ) E ,
$$

where ${ \cal E } \equiv | \vec { v } \rangle \langle \vec { e } |$ . The “personalization vector” $\vec { v }$ is a probability distribution; the typical choice is $\vec { v } = \vec { e } / n$ . The parameter $\alpha ~ \in ~ ( 0 , 1 )$ is the probability that the walker follows the link structure of the web-graph at each step, rather than hop randomly between graph nodes according to $\vec { v }$ (Google reportedly uses $\alpha = 0 . 8 5$ ). By construction, $G$ is irreducible and aperiodic, and hence the Perron-Frobenius theorem (Horn and Johnson, 2012),1 8 ensures the existence of a unique eigenvector with all positive entries associated to the maximal eigenvalue 1. This eigenvector is precisely the PageRank $\bar { p }$ . Moreover, the modulus of the second eigenvalue of $G$ is upper-bounded by $\alpha$ (Nussbaum, 2003). This is important for the convergence of the power method, the standard computational technique employed to evaluate $\bar { p }$ . It uses the fact that for any probability vector $\vec { p _ { 0 } }$

$$
\vec { p } = \operatorname* { l i m } _ { k \to \infty } G ^ { k } \vec { p _ { 0 } } .
$$

The power method computes $\vec { p }$ with accuracy $\nu$ in a time that scales as $O [ s n \log ( 1 / \nu ) / \log ( 1 / \alpha ) ]$ , where $s$ is the sparsity of the graph (maximum number of non-zero entries per row of the adjacency matrix). The rate of convergence is determined by $\alpha$ .

# 2. Hamiltonian and gap

Consider the following non-local final Hamiltonian associated with a generic Google matrix $G$ (in this subsection we use $H$ and $h$ for local and non-local Hamiltonians, respectively):

$$
h _ { 1 } = h ( G ) \equiv \left( \mathbb { 1 } - G \right) ^ { \dagger } \left( \mathbb { 1 } - G \right) .
$$

Since $h ( G )$ is positive semi-definite, and $^ { 1 }$ is the maximal eigenvalue of $G$ associated with $\vec { p }$ , it follows that the ground state of $h ( G )$ is given by $\left| \pi \right. \equiv { \vec { p \prime } } \left\| | { \vec { p } } \right\|$ . The initial Hamiltonian has a similar form, but it is associated with the Google matrix $G _ { c }$ of the complete graph

$$
h _ { 0 } = h ( G _ { c } ) \equiv \left( \mathbb { 1 } - G _ { c } \right) ^ { \dagger } \left( \mathbb { 1 } - G _ { c } \right) .
$$

The ground state of $\textstyle | \psi ( 0 ) \rangle = \sum _ { j = 1 } ^ { n } | j \rangle / { \sqrt { n } }$ $h _ { 0 }$ is the uniform superposition state . The basis vectors $| j \rangle$ span the $n$ -dimensional Hilbert space of $\log _ { 2 } n$ qubits The interpolating adiabatic Hamiltonian is

$$
h ( s ) = ( 1 - s ) h _ { 0 } + s h _ { 1 } .
$$

Equations (61)-(63) completely characterize the adiabatic quantum PageRank algorithm, apart from the schedule $s ( t )$ .

By numerically simulating the dynamics generated by $h ( s )$ , (Garnerone et al., 2012) showed that for typical random graph instances generated using the “preferential attachment model” (Barabasi and Albert, 1999; Bollob´as et al., 2001) and “copying model” (Kleinberg et al., 1999) (both of which yield sparse random graphs with smallworld and scale-free features), the typical run time of the adiabatic quantum PageRank algorithm scales as

$$
t _ { f } \sim ( \log \log n ) ^ { b - 1 } ( \log n ) ^ { b } ,
$$

where $b > 0$ is some small integer that depends on the details of the graph parameters. The numerically computed gap scales as $( \log n ) ^ { - b }$ , which (Garnerone et al., 2012) found to be due to the power law distribution of the out-degree nodes $d ( i )$ .19

# 3. Speedup

We next discuss two tasks for which this adiabatic quantum ranking algorithm offers a speedup.

The best currently known classical Markov Chain Monte Carlo (MCMC) technique used to evaluate the full PageRank vector requires a time (in the bulk synchronous parallel computational model (Valiant, 1990)) which scales as $O [ \log ( n ) ]$ (Das Sarma et al., 2015). The algorithm launches $\log n$ random walks from each node of the graph in parallel (for a total of $n \log ( n )$ walkers), with each node communicating $O [ \log ( n ) ]$ bits of data to each of its connected neighbors after each step. After $O [ \log ( n ) ]$ steps, the total number of walkers that have visited a node is used to estimate the PageRank of that node. In the absence of synchronization costs [synchronization and communication are known to be important issues for networks with a large number of processors (Awerbuch, 1985; Bisseling, 2004; Kumar et al., 2003; Rauber and R¨unger, 2010)], the classical cost can be taken to be $O [ n \log ( n ) ^ { 2 } ]$ , i.e., the number of parallel processes multiplied by the duration of each process.20

At the conclusion of the adiabatic evolution generated by the Hamiltonian in Eq. (63), the PageRank vector $\vec { p } = \left\{ p _ { i } \right\}$ is encoded into the quantum PageRank state $\textstyle | \pi \rangle = \sum _ { i = 1 } ^ { n } { \sqrt { \pi _ { i } } } | i \rangle$ of a $( \log _ { 2 } n )$ -qubit system, where $| i \rangle$ denotes the $i$ -th node in the graph $G$ . The probability of measuring node $i$ is $\pi _ { i } = p _ { i } ^ { 2 } / \left| \left| \vec { p } \right| \right| ^ { 2 }$ . One can estimate $\pi _ { i }$ by repeatedly sampling the expectation value of the operator $\boldsymbol { \sigma } _ { i } ^ { z }$ in the final state. The number of measurements $M$ needed to estimate $\pi _ { i }$ is given by the Chernoff-Hoeffding bound (Hoeffding, 1963), allowing one to approximate $\pi _ { i }$ with an additive error $e _ { i }$ and with $M = \mathrm { p o l y } ( e _ { i } ^ { - 1 } )$ . A nontrivial approximation requires $e _ { i } \leq p _ { i }$ and, these are typically $O ( 1 / n )$ .

The fact that the amplitudes of the quantum PageRank state are $\{ { \sqrt { \pi _ { i } } } \ = \ p _ { i } / \ \lVert { \vec { p } } \rVert \}$ , rather than $\{ { \sqrt { p _ { i } } } \}$ , is a virtue: the number of samples needed to estimate the rank $\pi _ { i }$ with additive error $e _ { i } \sim \pi _ { i }$ scales as $O [ n ^ { 2 \gamma _ { i } - 1 } ]$ , so the total quantum cost is $O [ n ^ { 2 \gamma _ { i } - 1 } \mathrm { p o l y l o g } ( n ) ]$ .21 Thus, for the combined task of state preparation and rank estimation, there is a polynomial quantum speedup whenever $\gamma _ { i } \quad < \quad 1$ , namely $O [ n ^ { 2 \gamma _ { i } - 1 } \mathrm { p o l y l o g } ( n ) ]$ vs. $O [ n \mathrm { \ p o l y l o g } ( n ) ]$ ; simulations reported in (Garnerone et al., 2012) show that this is indeed the case for the topranked $\log ( n )$ entries, and in applications one is most often interested in the top entries. We emphasize that this holds in the average (not worst) case, and is not a provable speedup; the evidence for the scaling is numerical, and it is unknown whether a classical algorithm for the preparation of $\pi$ rather than $\vec { p }$ may give a similar scaling to the quantum scaling, though if that is the case one could consider quantum preparation of $\{ \pi _ { i } ^ { 2 } / \Vert \pi \Vert ^ { 2 } \}$ , etc.

Another context for useful applications is comparing successive PageRanks, or more generally “q-sampling” (Aharonov and Ta-Shma, 2003). Suppose one perturbs the web-graph. The adiabatic quantum algorithm can provide, in time $O [ \mathrm { p o l y l o g } ( n ) ]$ , the pre- and postperturbation states $| \pi \rangle$ and $| \tilde { \pi } \rangle$ as input to a quantum circuit implementing the SWAP-test (Buhrman et al., 2001). To obtain an estimate of the fidelity $| \langle \pi | \tilde { \pi } \rangle | ^ { 2 }$ one needs to measure an ancilla $O ( 1 )$ times, the number depending only on the desired precision. In contrast, deciding whether two probability distributions are close classically requires $O [ n ^ { 2 / 3 } \log n ]$ samples from each (Batu et al., 2000). Whenever some relevant perturbation of the previous quantum PageRank state is observed, one can decide to run the classical algorithm again to update the classical PageRank.

# IV. UNIVERSALITY OF AQC

What is the relation between the computational power of the circuit model and the adiabatic model of quantum computing? It turns out that they are equivalent, up to polynomial overhead. It is well known that the circuit model is universal for quantum computing, i.e., that there exist sets of gates acting on a constant number of qubits each that can efficiently simulate a quantum Turing machine (Deutsch, 1985; Yao, 1993). A set of gates is said to be universal for QC if any unitary operation may be approximated to arbitrary accuracy by a quantum circuit involving only those gates (Nielsen and Chuang, 2000). The analog of such a set of gates in AQC is a Hamiltonian. An operational definition of universal AQC is thus to efficiently map any circuit to an adiabatic computation using a sufficiently powerful Hamiltonian. Formally:

Definition 3 (Universal Adiabatic Quantum Computation). A time-dependent Hamiltonian $H ( t )$ , $t \in [ 0 , t _ { f } ]$ , is universal for AQC if, given an arbitrary quantum circuit $U$ operating on an arbitrary initial state $| \psi \rangle$ of $n$ $p$ -state particles and having depth $L$ , the ground state of $H ( t _ { f } )$ is equal to $U | \psi \rangle$ with probability greater than $\epsilon > 0$ , the number of particles $H ( t )$ operates on is poly $n$ ) t, and $t _ { f } = p o l y ( n , L )$ .

The stipulation that the ground state of $H ( t _ { f } )$ is equal to the final state at the end of the circuit ensures that the circuit and the adiabatic computation have the same output. We note that it is possible and useful to relax the ground state requirement and replace it with another eigenstate of $H ( t )$ (see, e.g., Sec. VI.C). The requirement that the number of particles and time taken by the adiabatic computation are polynomial in $n$ and $L$ ensures that the resources used do not blow up.

We begin, in Sec. IV.A, by showing that the circuit model can efficiently simulate AQC. The real challenge is to show the other direction, i.e., that AQC can efficiently simulate the circuit model, which is what we devote the rest of this section to. Along the way, this establishes the universality of AQC. We present several proofs, starting in Sec. IV.B with a detailed review of the history state construction of (Aharonov et al., 2007), who showed in addition that six-state particles in two dimensions suffice for universal adiabatic quantum computation. This was improved in (Kempe et al., 2006), using perturbation-theory gadgets, who showed that qubits can be used instead of six-state particles, and that adiabatic evolution with 2-local Hamiltonians is quantum universal. A 2-local model of universal AQC in 2D, which we review in Sec. IV.C, was proposed in (Mizel et al., 2007), using fermions. Universal AQC using qubits on a two-dimensional grid was accomplished in (Oliveira and Terhal, 2008). Further simplifications of universal AQC in 2D were presented in (Breuckmann and Terhal, 2014;

Gosset et al., 2015; Lloyd and Terhal, 2016), using the space-time circuit model, which we review in Sec. IV.D. The ultimate reduction in spatial dimensionality was accomplished in (Aharonov et al., 2009), who showed that universal AQC is possible with 1D 9-state particles, as we review in Sec. IV.E. Finally, in Sec. IV.F we review a construction that allows one to quadratically amplify the gap of any Hamiltonian used in AQC (satisfying a frustration-freeness property), though this requires the computation to take place in an excited state.

# A. The circuit model can efficiently simulate AQC

That the circuit model can efficiently simulate the adiabatic model is relatively straightforward and was first shown in (Farhi et al., 2000). Assume for simplicity a linear schedule, i.e., an AQC Hamiltonian of the form $\begin{array} { r } { H ( t ) = ( 1 - \frac { t } { t _ { f } } ) H _ { 0 } + \frac { t } { t _ { f } } H _ { 1 } } \end{array}$ . The evolution of a quantum system generated by the time-dependent Hamiltonian $H ( t )$ is governed by the unitary operator:

$$
U ( t _ { f } , 0 ) = \mathrm { T e x p } \left[ - i \int _ { 0 } ^ { t _ { f } } d t H ( t ) \right] ~ .
$$

If $t _ { f }$ satisfies the condition for adiabaticity, $U ( t _ { f } , 0 )$ will map the ground state at $t = 0$ to the ground state at $t _ { f }$ . Therefore it suffices to show that the circuit model can simulate $U ( t _ { f } , 0 )$ . To do so, we approximate the evolution by a product of unitaries involving time-independent Hamiltonians $H _ { m } ^ { \prime } \equiv H ( m \Delta t )$ :

$$
U ( t _ { f } , 0 ) \mapsto U ^ { \prime } ( t _ { f } , 0 ) = \prod _ { m = 1 } ^ { M } U _ { m } ^ { \prime } = \prod _ { m = 1 } ^ { M } e ^ { - i \Delta t H _ { m } ^ { \prime } } \ ,
$$

where $\Delta t = t _ { f } / M$ . The error incurred by this approximation is (van Dam et al., 2001):

$$
\| U ( t _ { f } , 0 ) - U ^ { \prime } ( t _ { f } , 0 ) \| \in O \left( \sqrt { t _ { f } \mathrm { p o l y } ( n ) / M } \right) \ ,
$$

where we used

$$
\begin{array} { r } { \| H ( t ) - H _ { \lceil m t / t _ { f } \rceil } ^ { \prime } \| \le \displaystyle \frac { 1 } { M } \| H _ { 1 } - H _ { 0 } \| } \\ { \in O ( \mathrm { p o l y } ( n ) / M ) ~ . } \end{array}
$$

We now wish to approximate each individual term in the product in Eq. (66) using the Baker-Campbell-Hausdorff formula (Klarsfeld and Oteo, 1989) by:

$$
U _ { m } ^ { \prime } \mapsto U _ { m } ^ { \prime \prime } = e ^ { - i \Delta t \left( 1 - \frac { m \Delta t } { t _ { f } } \right) H _ { 0 } } e ^ { - i \Delta t \frac { m \Delta t } { t _ { f } } H _ { 1 } } \ ,
$$

which incurs an error $\lVert e ^ { A + B } - e ^ { A } e ^ { B } \rVert \in O \left( \left. A B \right. \right)$ due to the neglected leading order commutator term $[ A , B ] / 2$ , i.e.,

$$
\lVert U _ { m } ^ { \prime } - U _ { m } ^ { \prime \prime } \rVert \in O \left( \frac { t _ { f } ^ { 2 } } { M ^ { 2 } } \lVert H _ { 0 } H _ { 1 } \rVert \right) \ .
$$

Therefore, accounting for the $M$ terms in the product and observing that the error in Eq. (67) is subdominant, the total error is (van Dam et al., 2001):

$$
\| U ( t _ { f } , 0 ) - \prod _ { m = 1 } ^ { M } U _ { m } ^ { \prime \prime } \| \in O \left( \mathrm { p o l y } ( n ) t _ { f } ^ { 2 } / M \right) \ .
$$

This means we can approximate $U ( t _ { f } , 0 )$ with a product of $2 M$ unitaries provided that $M$ scales as $t _ { f } ^ { 2 } \mathrm { p o l y } ( n )$ .

Depending on the form of $H _ { 0 }$ and $H _ { 1 }$ , they may need further decomposition in order to write the terms in Eq. (69) in terms of few-qubit unitaries. E.g., for the standard initial Hamiltonian $\begin{array} { r } { H _ { 0 } = - \sum _ { i } \sigma _ { i } ^ { x } } \end{array}$ , which is a sum of commuting single qubit operators, we can write $e ^ { - i \Delta t ( 1 - t / t _ { f } ) H _ { 0 } / K }$ as a product of $n$ one-qubit unitaries. Likewise, assuming that $H _ { 1 }$ is 2-local, we can write $e ^ { - i \frac { m \Delta t } { t _ { f } } \Delta t H _ { 1 } / M }$ as a product of up to $n ^ { 2 }$ two-qubit unitaries within the same order of approximation as Eq. (69). Thus, $U ( t _ { f } , 0 )$ can be approximated as a product of unitary operators each of which acts on a few qubits. The scaling of $t _ { f }$ required for adiabatic evolution is inherited by the number of few-qubit unitary operators in the associated circuit version of the algorithm.

A more efficient method was proposed in (Boixo et al., 2009b), building upon the ideas explained in Sec. II.B.4. This “eigenpath traversal by phase randomization” method applies the Hamiltonian $H ( t _ { j } )$ in piecewise continuous manner at random times $t _ { j }$ . Each interval $[ t _ { j } , t _ { j + 1 } ]$ corresponds to a unitary $e ^ { - i H ( t _ { j } ) }$ , which then needs to be decomposed into one- and two-qubit gates, as above. The randomization introduces an effective eigenstate decoupling in the Hamiltonian eigenbasis (similarly to the effect achieved by projections in the Zeno effect), so that if the initial state is the ground state, the evolution will follow the ground state throughout as required for AQC. The algorithmic cost of this randomization method is defined as the average number of times the unitaries are applied, and it can be shown that the cost is ${ \cal O } [ L ^ { 2 } / ( \varepsilon \Delta ) ]$ , where $\varepsilon$ is the desired maximum error of the final state compared to the target eigenstate, and $L$ is the path length [Eq. (13)]. Since $L \leq \operatorname* { m a x } _ { s } \| \dot { H } ( s ) \| / \Delta$ as we saw in Sec. II.B.4, the worst-case bound on the cost is $\operatorname* { m a x } _ { s } \| \dot { H } ( s ) \| ^ { 2 } / ( \varepsilon \Delta ^ { 3 } )$ , up to logarithmic factors.

# B. AQC can efficiently simulate the circuit model: history state proof

The goal is, given an arbitrary $n$ -qubit quantum circuit, to design an adiabatic computation whose final ground state is the output of the quantum circuit described by a sequence of $L$ one or two-qubit unitary gates, $U _ { 1 } , U _ { 2 } , \dots U _ { L }$ . This adiabatic simulation of the circuit should be efficient, i.e., it may incur at most polynomial overhead in the circuit depth $L$ . In this subsection we review the proof presented in (Aharonov et al., 2007). This was the first complete proof of the universality of AQC, and many of the ideas and techniques introduced therein inspired subsequent proofs, remaining relevant today.

Let us assume that the $n$ -qubit input to the circuit is the $| 0 \cdots 0 \rangle$ state. After the $\ell$ -th gate, the state of the quantum circuit is given by $| \alpha ( \ell ) \rangle$ . To proceed, we use the “circuit-to-Hamiltonian” construction (Kitaev et al., 2000), where the final Hamiltonian will have as its ground state the entire history of the quantum computation. This “history state” is given by:

$$
\begin{array} { r } { | \eta \rangle = \displaystyle \frac { 1 } { \sqrt { L + 1 } } \sum _ { \ell = 0 } ^ { L } | \gamma ( \ell ) \rangle } \\ { | \gamma ( \ell ) \rangle \equiv | \alpha ( \ell ) \rangle \otimes | 1 ^ { \ell } 0 ^ { L - \ell } \rangle _ { \mathrm { c } } } \end{array}
$$

where $| 1 ^ { \ell } 0 ^ { L - \ell } \rangle _ { \mathrm { c } }$ denotes the “Feynman clock” (Feynman, 1985) register composed of $L + 1$ qubits. The notation means that we have $\ell$ ones followed by $L - \ell$ zeros to denote the time after the $\ell$ -th gate. We wish to construct a Hamiltonian $H _ { \mathrm { i n i t } }$ with ground state $| \gamma ( 0 ) \rangle$ and a Hamiltonian $H _ { \mathrm { f i n a l } }$ with ground state $| \eta \rangle$ . Let:

$$
\begin{array} { r c l } { { } } & { { } } & { { H _ { \mathrm { i n i t } } = H _ { \mathrm { c - i n i t } } + H _ { \mathrm { i n p u t } } + H _ { \mathrm { c } } } } \\ { { } } & { { } } & { { H _ { \mathrm { f i n a l } } = \displaystyle \frac { 1 } { 2 } H _ { \mathrm { c i r c u i t } } + H _ { \mathrm { i n p u t } } + H _ { \mathrm { c } } } } \\ { { } } & { { } } & { { { } } } \\ { { } } & { { \displaystyle H _ { \mathrm { c i r c u i t } } = \displaystyle \sum _ { \ell = 1 } ^ { L } H _ { \ell } ~ . } } \end{array}
$$

The full time independent Hamiltonian $H ( s )$ is given by (Aharonov et al., 2007):

$$
\begin{array} { l } { H ( s ) = ( 1 - s ) H _ { \mathrm { i n i t } } + s H _ { \mathrm { f i n a l } } } \\ { \displaystyle \quad = H _ { \mathrm { i n p u t } } + H _ { \mathrm { c } } + ( 1 - s ) H _ { \mathrm { c - i n i t } } + \frac { s } { 2 } H _ { \mathrm { c i r c u i t } } \ . } \end{array}
$$

The various terms are chosen so that the ground state always has energy 0:

• $H _ { \mathrm { c } }$ : This term should ensure that the clock’s state is always of the form $| 1 ^ { \ell } 0 ^ { L - \ell } \rangle _ { \mathrm { c } }$ . Therefore, we energetically penalize any clock-basis state that has the sequence 01:

$$
H _ { \mathrm { c } } = \sum _ { \ell = 1 } ^ { L - 1 } | 0 _ { \ell } 1 _ { \ell + 1 } \rangle _ { \mathrm { c } } \langle 0 _ { \ell } 1 _ { \ell + 1 } |
$$

where $| 0 \ell 1 \ell { + } 1 \rangle _ { \mathrm { c } }$ denotes a $0$ on the $\ell$ -th clock qubit and 1 on the $( \ell { + } 1 )$ -th clock qubit. Any illegal clock state will have an energy $\geq 1$ . Any legal clock state will have energy $0$ .

• $H _ { \mathrm { c - i n i t } }$ : Ensures that the initial clock state is $| 0 ^ { L } \rangle _ { \mathrm { c } }$ .

$$
H _ { \mathrm { c - i n i t } } = | 1 _ { 1 } \rangle _ { \mathrm { c } } \langle 1 _ { 1 } |
$$

Note that we only need to specify the first clock qubit to be in the zero state. For a legal clock state, Eqs. (75) and (76) imply that the rest are in the zero state as well.

$$
H _ { \mathrm { i n p u t } } = \sum _ { i = 1 } ^ { n } | 1 _ { i }   1 _ { i } | \otimes | 0 _ { 1 }  _ { \mathrm { c } } \langle 0 _ { 1 } |
$$

• $H _ { \mathrm { i n p u t } }$ : Ensures that if the clock state is $| 0 ^ { L } \rangle$ , then the computation qubits are in the $| 0 ^ { n } \rangle$ state.

• $H _ { \ell }$ : Ensures that the propagation from $\ell - 1$ to $\ell$ corresponds to the application of $U _ { \ell }$ .

$$
\begin{array} { r l } { H _ { 1 } = } & { 1 \otimes \left| 0 _ { 1 } 0 _ { 2 } \right. \left. 0 | 0 _ { 2 } \right| - U _ { 1 } \left| 1 _ { 1 } 0 _ { 2 } \right. \left. 0 _ { 1 } 0 _ { 2 } \right. } \\ & { - U _ { 1 } ^ { i } \left| 0 _ { 1 } 0 _ { 2 } \right. \left. \langle 1 _ { 1 } 0 _ { 2 } \right| + 1 \otimes \left| 1 _ { 1 } 0 _ { 2 } \right. \left. \langle 1 _ { 1 } 0 _ { 2 } \right| } \\ & { - U _ { 1 } ^ { i } \left| 1 _ { t - 1 } 0 _ { t } 0 _ { t + 1 } \right. \left. 1 _ { t - 1 } 0 _ { t } 0 _ { t + 1 } \right| } \\ & { - U _ { t } \left| \ell _ { - 1 } 1 _ { t } 0 _ { t + 1 } \right. \left. 1 _ { t } - | 0 _ { t } 0 _ { t + 1 } \right| } \\ & { - U _ { t } ^ { i } \left| 1 _ { t - 1 } \ell _ { t } 0 _ { t + 1 } \right. \left. 1 _ { t - 1 } 0 _ { t } \ell _ { t + 1 } \right| } \\ & { + 1 \otimes \left| 1 _ { t - 1 } 1 _ { t } 0 _ { t + 1 } \right. \left. 1 _ { t - 1 } 1 _ { t } 0 _ { t + 1 } \right| } \\ { H _ { L } = } & { 1 \otimes \left| 1 _ { L - 1 } 0 _ { L } \right. \left. 1 _ { L - 1 } 0 _ { L } \right| } \\ & { - U _ { L } \left| 1 _ { L - 1 } 1 _ { L } \right. \left. 1 _ { L - 1 } 0 _ { L } \right| } \\ & { - U _ { 1 } ^ { i } \left| 1 _ { L - 1 } 0 _ { L } \right. \left. 1 _ { L - 1 } 1 _ { L } \right| } \\ & { + 1 \otimes \left| 1 _ { L - 1 } 1 _ { L } \right. \left. \ell 1 _ { L - 1 } 1 _ { L } \right| } \end{array}
$$

Note that the first and last terms leave the state unchanged. The second term propagates the computational state and clock register forward, while the third term propagates the computational state and clock register backward.

It turns out that the state $\left| \gamma ( 0 ) \right. = \left| \alpha ( 0 ) \right. \otimes \left| 0 ^ { L } \right.$ is the ground state of $H _ { \mathrm { i n i t } }$ with eigenvalue $0$ , and $| \eta \rangle$ is the ground state of $H _ { \mathrm { f i n a l } }$ with eigenvalue $0$ . Let $S _ { 0 }$ be the subspace spanned by $\{ | \gamma ( \ell ) \rangle \} _ { \ell = 0 } ^ { L }$ . The state $| \alpha ( 0 ) \rangle$ is the input to the circuit, so it can be taken to be the $| 0 \cdots 0 \rangle$ state, i.e., the initial ground state is an easily prepared state. Since the initial state $| \gamma ( 0 ) \rangle \in S _ { 0 }$ , the dynamics generated by $H ( s )$ keep the state in $S _ { 0 }$ . It turns out that the ground state is unique for $s \in [ 0 , 1 ]$ . By mapping the Hamiltonian within $S _ { 0 }$ to a stochastic matrix, it is possible to find a polynomial lower bound on the gap from the ground state within $S _ { 0 }$ :

$$
\Delta ( H _ { S _ { 0 } } ) \geq \frac { 1 } { 4 } \left( \frac { 1 } { 6 L } \right) ^ { 2 } \ .
$$

It is also possible to bound the global gap (i.e., not restricted to the $S _ { 0 }$ subspace) as

$$
\Delta ( H ) \geq \Omega ( 1 / L ^ { 3 } ) \ .
$$

A measurement of the final state will find the final outcome of the quantum circuit $| \gamma ( L ) \rangle$ with probability $\frac { 1 } { L + 1 }$ . This can be amplified by inserting identity operators at the end of the circuit, hence causing the history state to include a greater superposition of the final outcome of the circuit. Together, these results show that there is an efficient implementation of any given quantum circuit using the adiabatic algorithm with $H ( s )$ . Here and elsewhere “efficient” means up to polynomial overhead, i.e., where $t _ { f }$ scales as a polynomial in $L$ .

The proof techniques used to obtain these results are instructive and of independent interest, so we review additional technical details in Appendix C.

To conclude this section, we briefly mention additional results supporting the equivalence of the circuit and adiabatic approach, in terms of state preparation. In (Aharonov and Ta-Shma, 2003) it was shown (Theorem 2) that any quantum state that can be efficiently generated in the circuit model can also be efficiently generated by an adiabatic approach, and vice versa, for the same initial state. The proof relies on two important lemmas, the “sparse Hamiltonian lemma” and the “jagged adiabatic path” lemma. The former gives conditions under which a Hamiltonian is efficiently simulatable in the circuit model, and the latter provides conditions under which a sequence of Hamiltonians, defining a path, can have a non-negligible spectral gap.

# C. Fermionic ground state quantum computation

A model of ground state quantum computation (GSQC) using fermions was independently proposed in (Mizel et al., 2001) [see also (Mizel, 2004; Mizel et al., 2002) and (Mao, 2005a,b)] around the same time as AQC. In GSQC, one executes a quantum circuit by producing a ground state that spatially encodes the entire temporal trajectory of the circuit, from input to output. It was shown in (Mizel et al., 2007) how to adiabatically reach the desired ground state, thus providing an alternative to history state type constructions for universal AQC. One of the differences between the GSQC and history states constructions is that instead of relying on Feynman “global clock particle” idea, particles are synchronized locally (via CNOT gates), an idea that traces back to (Margolus, 1990) and was later adopted in some of the space-time circuit-to-Hamiltonian constructions (Breuckmann and Terhal, 2014).

Consider a quantum circuit with $n$ qubits and depth $L$ . We associate $2 ( L + 1 )$ fermionic modes with every qubit $q$ , via creation operators $a _ { q , \ell } ^ { \dagger }$ and $b _ { q , \ell } ^ { \dagger }$ , where $\ell =$ $0 , \ldots , L$ . One can view these $2 \bar { n ( L + 1 ) }$ modes as the state-space of $n$ spin- $1 / 2$ fermions, where each fermion can be localized at sites on a 1D (time)-line of length $L + 1$ . To illustrate this with a concrete physical system, imagine a two-dimensional array of quantum dots with $L + 1$ columns and two rows per qubit, corresponding to the $| 0 \rangle$ and $| 1 \rangle$ basis states of that qubit. A total of $n$ electrons are placed in the array. The state of each qubit determines the spin state of the corresponding electron, which in term determines which of the two rows it is in, while the clock of each qubit is represented by which column the electron is in.

It is convenient to group creation operators into row vectors $C _ { q , \ell } ^ { \dagger } = ( a _ { q , \ell } ^ { \dagger } b _ { q , \ell } ^ { \dagger } )$ . Then for each single-qubit gate (1) $U _ { q , \ell } ^ { ( 1 ) }$ we introduce a term

$$
H _ { q , \ell } ^ { ( 1 ) } ( s ) = \left( C _ { q , \ell } ^ { \dag } - s C _ { q , \ell - 1 } ^ { \dag } ( U _ { q , \ell } ^ { ( 1 ) } ) ^ { \dag } \right) \left( C _ { q , \ell } - s C _ { q , \ell - 1 } U _ { q , \ell } ^ { ( 1 ) } \right)
$$

into the circuit Hamiltonian $H _ { \mathrm { c i r c u i t } }$ . The off-diagonal terms represent hopping or tunneling of the $q$ -th electron from site \` − 1 to \` (and v.v.), while U (1)q,\` acts on the electron’s spin. The diagonal terms Cq, C†q,\`Cq,\` and C†q,\` 1Cq,\`−1 ensure that H(1)q,\` $H _ { q , \ell } ^ { ( 1 ) } ~ \ge ~ 0$ . The parameter $s \in \left[ 0 , 1 \right]$ controls the interpolation from the initial, simple to prepare ground state at $s = 0$ when there is no tunneling and every electron is frozen in place, to the full realization of all the gates $U _ { q , \ell } ^ { ( 1 ) }$ when $s = 1$ .

One can similarly define CNOT Hamiltonian terms between electrons or fermions, whose form can be found in (Mizel et al., 2007) [see also (Breuckmann and Terhal, 2014)]. These 2-local terms can be understood as a sum of an identity and NOT term. For such two-qubit gates, the fermions corresponding to the control and target qubits both tunnel forward or backward and the internal spin-state of the target fermion changes depending on the internal state of the control fermion. An important additional ingredient is the addition of a penalty term that imposes an energy penalty on states in which one qubit has gone through the CNOT gate without the other. Instead of the Feynman clock used in the history state construction, there are many local clocks, one per qubit. The synchronization mechanism takes place via the CNOT Hamiltonian. Moreover, the entire construction naturally involves only 2-local interactions between fermions in 2D.

While the fermionic GSQC model proposed in (Mizel et al., 2007) was shown there to be universal for AQC, its gap analysis was incomplete.22 This was fixed in (Childs et al., 2013), which proved the “Nullspace Projection Lemma” that was implicitly assumed in (Mizel et al., 2007). This lemma is interesting in its own right, so we reproduce it here:

Lemma 2 (Nullspace Projection Lemma (Childs et al., 2013)). Let $\Delta ( A )$ denote the smallest nonzero eigenvalue of the positive semidefinite operator $A$ . Let $H _ { 0 }$ and $H _ { 1 }$ be positive semidefinite and assume the nullspace $S$ of $H _ { 0 }$ is non-empty. Also assume that $\Delta ( H _ { 1 } | _ { S } ) \geq c > 0$ and $\Delta ( H _ { 0 } ) \ge d > 0$ . Then

$$
\Delta ( H _ { 0 } + H _ { 1 } ) \ge { \frac { c d } { c + d + \| H _ { 1 } \| } } \ .
$$

As shown in (Breuckmann and Terhal, 2014), the fermionic GSQC model can be unitarily mapped onto the space-time circuit-to-Hamiltonian model for qubits in 2D, where the gap analysis is more convenient. Using the same mapping, (Breuckmann and Terhal, 2014) also showed that the fermionic model of (Mizel et al., 2007) is in fact QMA-complete. We thus proceed to discuss the space-time model next.

# D. Space-time Circuit-to-Hamiltonian Construction

Here we briefly review another construction that realizes universal adiabatic quantum computation (Gosset et al., 2015; Lloyd and Terhal, 2016). This builds on the so-called space-time circuit-to-Hamiltonian construction (Breuckmann and Terhal, 2014), which in turn is based on the Hamiltonian computation construction of (Janzing, 2007). We consider the $2 n$ -qubit quantum circuit with $n ^ { 2 }$ two-qubit gates, arranged as shown in Fig. 3(a). This form is sufficient for universal quantum computation (Janzing, 2007). An equivalent representation of the circuit is given in Fig. 3(b), where the $n ^ { 2 }$ gates are arranged in a rotated $n \times n$ grid. Each plaquette $p$ is associated with a gate $U _ { p }$ , of which the majority are identity gates. Only a $k \times k$ subgrid of the $n \times n$ grid with $k = \sqrt { n } / 1 6$ has non-identity gates, with the subgrid located as shown in Fig. 3(c). This region is referred to as the interaction region.

The circuit is mapped to a Hamiltonian $H ( \lambda )$ , with $\lambda \in [ 0 , 1 ]$ . The Hamiltonian describes the evolution of particles that live on the edges of the rotated $n \times n$ grid. The positions of the particles are given in terms of the coordinates $( t , w ) \in \{ 1 , \ldots , 2 n \} ^ { 2 }$ as shown in Fig. 3(b). Each particle has two internal degrees of freedom in order to encode the qubits of the circuit. Let $a _ { t , s } [ w ]$ denote the annihilation operator which annihilates a particle with internal state $s \in \{ 0 , 1 \}$ on the edge $( t , w )$ . The number operator is defined as $n _ { t , s } [ w ] = a _ { t , s } ^ { \dagger } [ w ] a _ { t , s } [ w ]$ , which counts the number of particles (which will be either $0$ or 1) at position $( t , w )$ with state $s$ . Let $\mathbf { n } _ { t } [ w ] =$ $n _ { t , 0 } [ w ] + n _ { t , 1 } [ w ]$ .

We focus on configurations of particles that form connected segments starting at the top and ending at the bottom [an example is shown in Fig. $\mathrm { 3 ( b ) }$ ], referred to as consistent connected string configurations. For a fixed $w$ (i.e., a horizontal line on the rotated grid), there is only one occupied edge. We can describe such configurations in terms of $2 n$ bits, denoted by $z$ . Specifically, let the bit value $0$ correspond to an edge going down and left and 1 correspond to an edge going down and right. The Hamming weight of such configurations must be $n$ , since they start and end in the middle of the grid and so must go left and right an equal number of times.

![](images/fc0b4c3e81bf9fa705a8d2f7ca811ec579fc1a05ca1a0f31344f9dd11fb7f876.jpg)  
FIG. 3 (a) A $2 n = 8$ qubit quantum circuit, where each grey square $n ^ { 2 } = 1 6$ in total) corresponds to a 2-qubit gate. (b) An equivalent representation of the quantum circuit in (a) in terms of a rotated grid. The red dashed line corresponds to an allowed string configuration for the particles. (c) The circuit is constrained such that the majority of the gates are identity except in a $k \times k$ subgrid (shown in black), located such that its left vertex is at the center of the rotated grid. A successful computation requires the $t$ position of the $2 k$ particles with $w$ positions that cross the interaction region, to lie to the right of the interaction region. See also Fig. 1 in (Gosset et al., 2015).

We are now ready to describe the Hamiltonian:

$$
H ( \lambda ) = H _ { \mathrm { s t r i n g } } + H _ { \mathrm { c i r c u i t } } ( \lambda ) + H _ { \mathrm { i n p u t } } \ .
$$

$\bullet$ $H _ { \mathrm { i n p u t } }$ : This term ensures that the ground state has the internal state of all particles set to $s = 0$ when the string lies on the left-hand side of the grid by energetically penalizing all states (on the left-hand side) with $s = 1$ . It is given by:

$$
H _ { \mathrm { i n p u t } } = \sum _ { w = 1 } ^ { 2 n } \sum _ { t \leq n } n _ { t , 1 } [ w ] \mathrm { ~ . ~ }
$$

• $H _ { \mathrm { s t r i n g } }$ : This term ensures that the ground state is in the subspace of connected strings. Consider a single vertex $v$ in the grid with incident edges labeled by $( t , w ) , ( t + 1 , w ) , ( t , w + 1 ) , ( t + 1 , w + 1 )$ . We can associate a Hamiltonian Hvstring to each vertex,

$$
\begin{array} { c } { { H _ { \mathrm { s t r i n g } } ^ { v } = { \bf n } _ { t } [ w ] + { \bf n } _ { t + 1 } [ w ] + { \bf n } _ { t } [ w + 1 ] + { \bf n } _ { t + 1 } [ w + 1 ] } } \\ { { - 2 \left( { \bf n } _ { t } [ w ] + { \bf n } _ { t + 1 } [ w ] \right) \left( { \bf n } _ { t } [ w + 1 ] + { \bf n } _ { t + 1 } [ w + 1 ] \right) } } \end{array}
$$

(for vertices at the boundary of the grid with two or three incident edges, the definition of $H _ { \mathrm { s t r i n g } } ^ { v }$ needs to be modified accordingly) such that $\begin{array} { r } { H _ { \mathrm { s t r i n g } } = \sum _ { v } H _ { \mathrm { s t r i n g } } ^ { v } } \end{array}$ . For connected string configurations, the energy due to this Hamiltonian is zero, while disconnected strings with $L$ string segments have a higher energy $2 L - 2$ .

$\bullet$ $\begin{array} { r } { H _ { \mathrm { c i r c u i t } } ( \lambda ) = \sum _ { p } H _ { \mathrm { g a t e } } ^ { p } ( \lambda ) + \sqrt { 1 - \lambda ^ { 2 } } H _ { \mathrm { i n i t } } } \end{array}$ : Define for each plaquette $p$ with borders given by the edges $\{ ( t , w )$ ,

$$
\begin{array} { r l } & { ( t + 1 , w ) , ( t , w + 1 ) , ( t + 1 , w + 1 ) \} } \\ & { H _ { \mathrm { g a t e } } ^ { p } ( \lambda ) = \mathbf { n } _ { t } [ w ] \mathbf { n } _ { t } [ w + 1 ] + \mathbf { n } _ { t + 1 } [ w ] \mathbf { n } _ { t + 1 } [ w + 1 ] + \lambda H _ { \mathrm { p r o p } } ^ { p } } \end{array}
$$

where

$$
\begin{array} { r } { H _ { \mathrm { p r o p } } ^ { p } = - \displaystyle \sum _ { \alpha , \beta , \gamma , \delta } \Big ( \langle \beta , \delta | U _ { p } | \alpha , \gamma \rangle a _ { t + 1 , \beta } ^ { \dagger } a _ { t , \alpha } [ w ] } \\ { \times a _ { t + 1 , \delta } ^ { \dagger } [ w + 1 ] a _ { t , \gamma } [ w + 1 ] \Big ) + \mathrm { h . c . } } \end{array}
$$

The term $H _ { \mathrm { p r o p } } ^ { p }$ allows for a pair of particles located on the left (right) edges of a plaquette to hop together such that they both are located on the right (left) edges of a plaquette, with their internal states changed according to $U _ { p }$ ( $U _ { p } ^ { \dagger }$ ). Note that this move preserves the connectedness of the string. Furthermore, the term $\begin{array} { r } { \sum _ { p } H _ { \mathrm { g a t e } } ^ { p } ( 0 ) } \end{array}$ is minimized by a configuration lying either entirely on the left border (corresponding to the bit string $z = 0 ^ { n } 1 ^ { n }$ ) or entirely on the right border ( $z = 1 ^ { n } 0 ^ { n }$ ), which in conjunction with $H _ { \mathrm { i n i t } }$ , given by

$$
H _ { \mathrm { i n i t } } = { \bf n } _ { n + 1 } [ w = 1 ] + { \bf n } _ { n + 1 } [ w = 2 n ] \ ,
$$

ensures that the ground state of $H ( 0 )$ is such that all particles lie along the left boundary of the grid. Including the effect of $H _ { \mathrm { c i r c u i t } } ( 0 )$ and $H _ { \mathrm { i n p u t } }$ , the ground state of $H ( 0 )$ is given by $| 0 ^ { 2 n } \rangle | 0 ^ { n } 1 ^ { n } \rangle$ with eigenvalue 1. This is an easily prepared ground state.

It can be shown that the ground state of $H ( \lambda )$ [Eq. (83)] along $\lambda \in [ 0 , 1 ]$ is unique and the energy gap above the ground state is lower bounded by $1 / \mathrm { p o l y } ( n )$ for all $\lambda \in \left[ 0 , 1 \right]$ [Theorem 1 in Ref. (Gosset et al., 2015)]. To measure the output of the quantum circuit, we measure the $t$ positions of the $2 k$ particles for the $w$ values that cross the interaction region (recall that there will always be one particle per horizontal $w$ line). If we find that all $2 k$ particles lie to the right of the interaction region, then their internal states must encode the output of the quantum circuit. For the choice $k = \sqrt { n } / 1 6$ , this occurs with a probability lower bounded by a positive constant. Together, these properties allow for an efficient (up to polynomial overhead) simulation of the quantum circuit using the adiabatic algorithm generated by $H ( \lambda )$ .

However, this implementation requires 4-body interactions [see for example the product term in Eq. (85)]. In (Lloyd and Terhal, 2016), improvements to the above construction were presented with only 2-local interactions using a first order perturbation gadget and a quadratic increase in the number of qubits from the original quantum circuit. The use of only first order perturbation theory is particularly significant, since effective interactions obtained in $k$ -th order degenerate perturbation theory with perturbative coupling $g$ and gap $\Delta$ of the unperturbed Hamiltonian scale in strength as $g ( g / \Delta ) ^ { k - 1 }$ , leading to a correspondingly small gap of the effective Hamiltonian. In addition, multiple uses of higher-order perturbation theory can increase qubit overhead and complexity.

# E. Universal AQC in 1D with 9-state particles

The constructions of universal AQC we have reviewed so far are all spatially two-dimensional (2D). It was unclear for some time whether universal AQC is possible in 1D, with some suggestive evidence to the contrary, such as the impressive success of density matrix renormalization group (DMRG) techniques in calculating ground state energies and other properties of a variety of 1D quantum systems (Schollw¨ock, 2005). Moreover, classical 1D systems are generally “easy”; e.g., a 1D restriction of MAX-2-SAT with $p$ -state variables can be solved by dynamic programming and hence is in the complexity class P. In addition, the area law implies that 1D systems with a constant spectral gap can be efficiently simulated classically (Hastings, 2009). All this implies that adiabatic evolution with 1D Hamiltonians is not useful for universal QC unless certain conditions are met, in particular a spectral gap that tends to zero.

This was accomplished in (Aharonov et al., 2009), who proved that it is possible to perform universal AQC using a 1D quantum system of 9-state particles. The striking qualitative difference between the quantum and the classical 1D versions of the same problem seems surprising. However, the $k$ -local Hamiltonian problem allows for the encoding of an extra dimension (time), by making the ground state a superposition of states corresponding to different times. This means that the correct analogue of the quantum 1D local Hamiltonian problem is 2D classical MAX-k-SAT, which is NP-complete.

The proof presented in (Aharonov et al., 2009) builds heavily on the history state construction reviewed in Sec. IV.B. However, there are a couple of important differences. As in the history state construction, the starting point is a quantum circuit $U _ { x }$ acting on $n$ qubits (where $x$ is the classical input to the function implemented by the circuit in the universal AQC case). A 1D $p$ -state Hamiltonian is designed which will verify correct propagation according to this circuit. Then this is used as the final Hamiltonian for the adiabatic evolution. The problem with directly realizing this in the 1D case is that only the particles nearest to the clock would be able to take advantage of it in order to check correct propagation in time. To overcome this, the circuit $U _ { x }$ is first modified into a new circuit $\tilde { U } _ { x }$ with a distributed clock. The history state construction relies on the ability to copy qubits from one column to the next in order to move to the next block of gates in the computation, so a new strategy is needed in 1D. For the modified circuit $\ddot { U } _ { x }$ , the qubits are instead placed in a block of $n$ adjacent particles. One set of gates is performed, and then all of the qubits are moved over $n$ places to advance time in the original circuit $U _ { x }$ . More states per particle are needed to accomplish this than in the 2D case. The second main new idea that is needed is related to ensuring that the state of the system had a valid structure. In the 2D case local constraints were used to check that there are no two qubit states in adjacent columns. However, using only local constraints, there is no way to check that there are exactly $n$ qubit data states in an unknown location in a 1D system, since there are only a constant number of local rules available, which are therefore unable to count to an arbitrarily large $n$ . Instead, it is ensured that, under the transition rules of the system, any invalid configurations will evolve in polynomial time into a configuration which can be detected as illegal by local rules. Thus, for every state which is not a valid history state, either the propagation is wrong, which implies an energy penalty due to the propagation Hamiltonian, or the state evolves to an illegal configuration which is locally detectable, which implies an energy penalty due to the local check of illegal configurations. For additional technical details required to complete the proof see (Aharonov et al., 2009). A 20- state translation-invariant modification of the construction from (Aharonov et al., 2009) for universal AQC in 1D was given in (Nagaj and Wocjan, 2008), improving on a 56-state construction by (Janzing et al., 2008).

# F. Adiabatic gap amplification

In all universality constructions the run time of the adiabatic simulation of a quantum circuit depends on the inverse minimum gap of the simulating Hamiltonian. Therefore it is of interest to develop a general technique for amplifying this gap, as was done in (Somma and Boixo, 2013).

Consider a Hamiltonian $H$ with ground state $| \phi \rangle$ . The goal is to construct a new Hamiltonian $H ^ { \prime }$ that has $| \phi \rangle$ as an eigenstate (not necessarily the ground state) but with a larger spectral gap. A quadratic spectral gap amplification is possible when $H$ is frustration-free [see also (Bravyi and Terhal, 2009)]:

Definition 4. (frustration freeness) A Hamiltonian $H \in$ $\mathbb { C } ^ { N } \times \mathbb { C } ^ { N }$ is frustration free if it can be written as a sum × over positive semi-definite operators: $\begin{array} { r } { H = \sum _ { k = 1 } ^ { L } { a _ { k } \Pi _ { k } } } \end{array}$ with $a _ { k } ~ \in ~ [ 0 , 1 ]$ and $L = \mathrm { p o l y l o g } ( N )$ . Further, if $| \phi \rangle$ is the ground state of $H$ then it is a ground state (i.e., zero eigenvector) of every term in the decomposition of $H$ , i.e., $\Pi _ { k } | \phi \rangle = 0 \ \forall k$ .

(Somma and Boixo, 2013) took $\Pi _ { k }$ as projectors. The quadratic amplification is optimal for frustrationfree Hamiltonians in a suitable black-box model, and no spectral gap amplification is possible, in general, if the frustration-free property is removed. An important caveat is that the construction replaces ground state evolution by evolution of a state that lies in the middle of the spectrum; thus it does not fit the strict definition of AQC (Def. 1). We will have another occasion to relax the definition in the same sense, in Sec. VI.C.

We now review the construction in (Somma and Boixo, 2013) in some detail. To place it in context, note that the universality results we reviewed thus far can be summarized as follows: Any quantum circuit specified by unitary gates $U _ { 1 } , \dots , U _ { Q }$ can be simulated by an adiabatic quanans: $\begin{array} { r } { H ( s ) = \sum _ { k = 1 } ^ { L } a _ { k } ( s ) \Pi _ { k } ( s ) } \end{array}$ rustration-free Hamiltoni-. The ground state of the final Hamiltonian $H ( 1 )$ has large overlap with the output state of the quantum circuit. Moreover, $L$ is polynomial in $Q$ , and $\Pi _ { k }$ denotes nearest-neighbor, two-body interactions between spins of corresponding many-body systems in one- or two-dimensional lattices. The inverse minimum gap of $H ( s )$ is polynomial in $Q$ , and hence so is the duration of the adiabatic simulation.

Now, consider a frustration-free Hamiltonian

$$
H ( s ) = \sum _ { k = 1 } ^ { L } a _ { k } \Pi _ { k } ( s ) \ ,
$$

where each $\Pi _ { k } ( s )$ is a projector for all $s \in [ 0 , 1 ]$ , and is a local operator. Denote the eigenvalues of this Hamiltonian by $\{ \lambda _ { j } \}$ , where $\lambda _ { 1 } = 0$ is the ground state energy. Then, take the Hamiltonian

$$
\bar { H } ( s ) = \sum _ { k = 1 } ^ { L } \sqrt { a _ { k } } \Pi _ { k } ( s ) \otimes ( | k \rangle \langle 0 | + | 0 \rangle \langle k | ) ~ ,
$$

where $| 0 \rangle$ and $| k \rangle$ are ancilla registers defined over one and $\log _ { 2 } ( L )$ qubits, respectively. It can be shown that $H ( s )$ has the desired properties, i.e., if $| \psi ( s ) \rangle$ was the ground state of $H$ , then $| \psi ( s ) \rangle | 1 0 \cdots 0 \rangle$ is a (degenerate) zero-eigenvalue eigenstate of $\bar { H }$ and the eigenvalues of $H ( s )$ are $\{ \pm \sqrt { \lambda _ { j } } \}$ [the proof is given in Appendix B of (Somma and Boixo, 2013)]. Thus, the gap has been quadratically amplified, and one can evolve with $\bar { H }$ to transform eigenstates at $s = 0$ to eigenstates at $s = 1$ and simulate the original quantum circuit with a quadratic speedup over the simulation involving $H$ .

In general $H ( s )$ will be $\log _ { 2 } ( L )$ -local due to the appearance of $| k \rangle$ . To avoid these many-body interactions one can represent $| k \rangle$ using a unary encoding, i.e., $| k \rangle \mapsto | 0 \dots 0 1 0 \dots 0 \rangle$ (with $1$ at the $k$ -th position). In this single-particle subspace the new Hamiltonian becomes

$$
\bar { H } ( s ) = \sum _ { k = 1 } ^ { L } \sqrt { a _ { k } } \Pi _ { k } ( s ) \otimes ( \sigma _ { k } ^ { + } \sigma _ { 0 } ^ { - } + \sigma _ { k } ^ { - } \sigma _ { 0 } ^ { + } ) ~ ,
$$

where $\sigma ^ { \pm } = ( \sigma ^ { x } \pm i \sigma ^ { y } ) / 2$ are Pauli raising and lowering operators. Note that since each $\Pi _ { k } ( s )$ interacts with the same qubit $0$ of the new register, if the original $H$ was geometrically local, then $H$ is not, i.e., it has a central spin geometry.

One more issue that needs to be dealt with is the degeneracy of the zero eigenvalue. To remove this degeneracy from contributions within the single-particle subspace one can add a penalty term $\begin{array} { r } { \frac { 1 } { 4 } \sqrt { \Delta } ( \mathbb { 1 } + \sigma _ { 0 } ^ { z } ) } \end{array}$ to $\bar { H } ( s )$

which penalizes all states with qubit $0$ in $| 0 \rangle$ ; the relevant spectral gap in the single-particle subspace is then still of order $\sqrt { \Delta }$ . To remove additional degeneracy from the many-particle subspaces one can add penalties for states that belong to such subspaces. Adding $\begin{array} { r } { Z = ( L - 2 ) \mathbb { 1 } - \sum _ { k = 0 } ^ { L } \sigma _ { k } ^ { z } } \end{array}$ achieves this since it acts as a penalty that grows with the Hamming weight $a$ of states in the $a$ -particle subspace. Thus

$$
\begin{array} { c } { { H ^ { \prime } ( s ) = \displaystyle \frac { 1 } { L ^ { 1 / d } } \left[ \displaystyle \sum _ { k = 1 } ^ { L } \sqrt { a _ { k } } \Pi _ { k } ( s ) \otimes ( | k \rangle \langle 0 | + | 0 \rangle \langle k | ) \right. } } \\ { { \displaystyle \left. + \frac { 1 } { 4 } \sqrt { \Delta } ( \mathbb { 1 } + \sigma _ { 0 } ^ { z } ) \right] + Z \ : , } } \end{array}
$$

has $| \psi _ { 0 } \rangle | 1 0 \cdots 0 \rangle$ as a unique eigenstate of eigenvalue $0$ , and all other eigenvalues are at distance at least $\sqrt { \Delta } / L ^ { 1 / d }$ if $d \geq 2$ .23 This is the desired quadratic gap amplification result.

How far can gap amplification methods go? It was shown in (Schaller, 2008) that for the one-dimensional transverse-field quantum Ising model, and for the preparation of cluster states (Raussendorf and Briegel, 2001), it is possible to use a series of straight-line interpolations in order to generate a schedule along which the gap is always greater than a constant independent of the system size, thus avoiding the quantum phase transition. However, there exists an efficient method to compute the ground state expectation values of local operators of 2D lattice Hamiltonians undergoing exact adiabatic evolution, and this implies that adiabatic quantum algorithms based on such local Hamiltonians, with unique ground states, can be simulated efficiently if the spectral gap does not scale with the system size (Osborne, 2007).

# V. HAMILTONIAN QUANTUM COMPLEXITY THEORY AND UNIVERSAL AQC

In this section we review Hamiltonian quantum complexity theory from the perspective of QMA completeness. This theory naturally incorporates decision problems of the type that motivate AQC. Essentially, it concerns a problem involving the ground state of a local Hamiltonian, whose ground state energy is promised to either be below a threshold $a$ or above another threshold $b > a$ , and where $b - a$ is polynomially small in the system size. In some cases this problem is easy, and in other cases it turns out to be so hard that we do not hope to solve it efficiently even on a quantum computer. Characterizing which types of local Hamiltonians fall into the latter category is the subject of QMA-completeness.

Hamiltonian quantum complexity theory is an extremely rich subject that is rapidly advancing and has already been reviewed a number of times, so we will only touch upon it and highlight some aspects that are relevant to AQC. Perhaps the most direct connection is the fact that 2-local Hamiltonians of a form that naturally appears in AQC, are QMA-complete. Additionally, some of the technical tools that played an important role in QMA-completeness locality reductions, such as perturbative gadgets, have also found great use in proofs of the universality of AQC with different Hamiltonians.

The reviews (Aharonov and Naveh, 2002; Gharibian, 2013; Gharibian et al., 2015), are excellent resources for additional perspectives and details on Hamiltonian quantum complexity theory.

# A. Background

# 1. Boolean Satisfiability Problem: $k$ -SAT

Consider a Boolean formula $\Phi$ that depends on $n$ literals $x _ { i } \in \{ 0 , 1 \}$ (with 0 and 1 representing False and True, respectively) or their negations. The problem is to decide whether there exists an assignment of values to the literals that satisfies the Boolean formula, i.e., such that $\Phi = 1$ . If there exists such an assignment then the formula is satisfiable, otherwise it is unsatisfiable.

The Boolean formula is typically written in conjunctive normal form: it is written in terms of a conjunction (AND - $\wedge$ ) of $r$ clauses, where each clause contains the disjunction (OR - ) of $k$ literals (variables) or their negation (NOT - $\neg$ ). A literal and its negation are often referred to as positive and negative literals. The Boolean formula is written as:

$$
\Phi = C _ { 1 } \wedge C _ { 2 } \wedge \cdot \cdot \cdot \wedge C _ { r }
$$

where $C _ { i } = x _ { i _ { 1 } } \vee x _ { i _ { 2 } } \cdot \cdot \cdot \vee x _ { i _ { k } }$ and $x _ { i _ { j } }$ is the $j$ -th positive or negative literal in the $i$ -th clause. The question of Boolean satisfiability, or $k$ -SAT, is whether there exists a choice $X = ( x _ { 1 } , \ldots , x _ { n } ) $ such that $\Phi ( X ) = 1$ . Note that it only requires $O ( k r )$ steps to check whether $X$ is a satisfying assignment, yet there are $2 ^ { n }$ possible choices for $X$ .

For $k = 3$ , the Boolean satisfiability problem, called 3-SAT, is NP-complete. Let us explain what this means.

# 2. NP, NP-complete, and NP-hard

Informally, problems in NP are those whose verification can be done efficiently (e.g., checking whether a Boolean formula is satisfied). An important conjecture, called the Exponential Time Hypothesis (Impagliazzo and Paturi, 2001), states that there are problems in NP that take exponentially long to solve.

Formally, a decision problem $Q$ is in NP if and only if there is an efficient algorithm $V$ , called the verifier, such that for all inputs $\eta$ (e.g., in the case of SAT, this would be the clauses) of the problem:

• if $Q ( \eta ) = 1$ , then there exists a witness $X$ such that $V ( \eta , X ) = 1$ .   
• if $Q ( \eta ) ~ = ~ 0$ , then for all witnesses $X$ we have $V ( \eta , X ) = 0$ .

In both cases, we typically take $| X | = \mathrm { p o l y } ( | \eta | )$ , where $| \eta |$ is the number of bits in the binary string associated with the input $\eta$ . The verifier is efficient in the sense that its cost scales as $\mathrm { p o l y } ( | X | )$ . In SAT the witness $X$ would be our test assignment.

A decision problem $Q$ is NP-complete if:

• $Q$ is in NP

• Every problem in NP is reducible to $Q$ in polynomial time.

Here reducibility means that given a problem $A$ in NP and a problem $B$ that is NP-complete, $A$ can be solved using a hypothetical polynomial-time algorithm that solves for $B$ . A commonly used reduction is the polynomial-time many-to-one reduction (Karp, 1972), whereby the inputs of $A$ are mapped into the inputs to $B$ such that the output of $B$ matches the output of $A$ . The hypothetical algorithm then solves $B$ to get the answer to $A$ .

A decision problem $Q$ is NP-hard if every problem in NP is reducible to $Q$ in polynomial time. (Note that unlike the NP-complete case, $Q$ does not need to be in NP). Clearly, NP-complete $\subseteq$ NP-hard.

# 3. The $k$ -local Hamiltonian Problem

The history state construction of Sec. IV.B relies on a 5-local Hamiltonian. Such a Hamiltonian belongs to an important class of decision problems known as the $k$ -local Hamiltonian Problem, of which a complete complexity classification was given in (Cubitt and Montanaro, 2016) subject to restrictions on the set of local terms from which the Hamiltonian can be composed [see also (Bravyi and Hastings, 2014)]. Recall that a $k$ -local Hamiltonian is a Hermitian matrix that acts non-trivially on at most $k$ $p$ -state particles.

The $k$ -local Hamiltonian Problem is defined on $n$ qubits, with the following input:

• A $k$ -local Hamiltonian $\begin{array} { r } { H \ = \ \sum _ { i = 1 } ^ { r } H _ { i } } \end{array}$ with $r =$ $\mathrm { p o l y } ( n )$ . Each $H _ { i }$ is $k$ -local and satisfies $\| H _ { i } \| =$ $\mathrm { p o l y } ( n )$ and its non-zero entries are specified by $\mathrm { p o l y } ( n )$ bits.

• Two real numbers $a$ and $b$ specified with $\mathrm { p o l y } ( n )$ bits of precision, such that

$$
b - a > \frac { 1 } { \mathrm { p o l y } ( n ) } \ .
$$

The output ( $0$ or 1) answers the question: Is the smallest eigenvalue of $H$ smaller than $a$ (output is 1), or are all eigenvalues larger than $b$ (output is $0$ )? We are promised that the ground state eigenvalue cannot be between $a$ and b.24

We may map 3-SAT to the 3-local Hamiltonian Problem as follows. For every clause $C _ { i }$ (which involves three literals), we can define a 3-local projector $H _ { i }$ onto all the unsatisfying assignments of $C _ { i }$ . Because $H _ { i }$ is a projector, it has eigenvalues 0 and 1, where the 0 eigenvalue is associated with satisfying assignments and the 1 eigenvalue with unsatisfying assignments. Therefore:

$$
H | X \rangle = \sum _ { i = 1 } ^ { r } H _ { i } | X \rangle = q | X \rangle
$$

where $q$ is the number of unsatisfied assignments by $X$ . Thus 3-SAT is equivalent to the following 3-local Hamiltonian problem: is the smallest eigenvalue of $H$ zero (the 3-SAT problem is satisfiable) or is it at least 1 (the 3-SAT problem is unsatisfiable)?

# 4. Motivation for Adiabatic Quantum Computing

Adiabatic evolution seems well-suited to tackling the $k$ -local Hamiltonian problem. By initializing an $n$ - qubit system in an easily prepared ground state, we can (in principle) evolve the system with a time-dependent Hamiltonian whose end point is the $k$ -local Hamiltonian. If the evolution is adiabatic, then we are guaranteed to be in the ground state of the $k$ -local Hamiltonian with high probability. By measuring the state of the system, we can determine the energy eigenvalue of the state (which hopefully is the ground state energy) and hence determine the answer to an NP-complete problem such as 3-SAT. This motivated early work on the quantum adiabatic algorithm (Farhi et al., 2001).

Another possibility is to try to use AQC as the verifier. However, the quantum algorithm only gives us the answer probabilistically, so we must first define a probabilistic analog of NP and then a quantum version. These new complexity classes are MA and QMA (Kitaev et al., 2000).

# B. MA and QMA

Informally, MA can be thought of as a probabilistic analog of NP, allowing for two-sided errors. Formally, a decision problem $Q$ is in MA iff there is an efficient probabilistic verifier $V$ such that for all inputs $\eta$ of the problem:

if $Q ( \eta ) = 1$ , then there exists a witness $X$ such that $\operatorname* { P r } ( V ( \eta , X ) = 1 ) \ge \frac { 2 } { 3 }$ (completeness). • if $Q ( \eta ) ~ = ~ 0$ , then for all witnesses $X$ we have $\begin{array} { r } { \operatorname* { P r } ( V ( \eta , X ) = 1 ) \le \frac { 1 } { 3 } } \end{array}$ (soundness).

Again we take $\left| X \right| = \mathrm { p o l y } ( \left| \eta \right| )$ . MA is typically viewed as an interaction between two parties, Merlin and Arthur. Merlin provides Arthur with a witness $X$ , on which Arthur runs $V$ . If $Q ( \eta ) = 0$ , Merlin should never be able to fool Arthur with a witness $X$ into believing that $Q ( \eta ) = 1$ with probability $> 1 / 3$ .

Note that there is nothing special about the probabilities $( 2 / 3 , 1 / 3 )$ . We can generalize our description to $\operatorname { M A } ( c , s )$ :

Claim 1. $M A ( c , c - 1 / | \eta | ^ { g } ) \subseteq M A ( 2 / 3 , 1 / 3 ) = M A ( 1 -$ $e ^ { - | \eta | ^ { g } } , e ^ { - | \eta | ^ { g } } )$ , where $g$ is a constant and $c > 0$ and $c -$ $1 / | \eta | ^ { g } < 1$ .

The proof of this “amplification lemma” [see, e.g., (Goldreich, 2008; Marriott and Watrous, 2005; Nagaj et al., 2009)] is interesting since it invokes the Chernoff bound, a widely used tool. We thus present it in Appendix $\mathrm { \Delta } \mathrm { D }$ for pedagogical interest.

The complexity class QMA can be viewed as the quantum analogue of MA. Thus, QMA is informally the class of problems that can be efficiently checked on a quantum computer given a “witness” quantum state related to the answer to the problem. Formally, define a quantum verifier $V$ (a quantum circuit) that takes $\eta$ and a quantum witness state $| X \rangle \in ( \mathbb { C } ^ { 2 } ) ^ { \otimes \mathrm { p o l y } ( | \eta | ) }$ as inputs and probabilistically outputs a binary number. The decision problem $Q$ is said to be in QMA if and only if there exists an efficient (polynomial time) $V$ for all inputs $\eta$ of the problem that satisfies:

if $Q ( \eta ) = 1$ , then there exists a witness $| X \rangle$ such that $\operatorname* { P r } ( V ( \eta , | X \rangle ) = 1 ) \ge \frac { 2 } { 3 }$ (completeness). • if $Q ( \eta ) = 0$ , then for all witnesses $| X \rangle$ we have $\begin{array} { r } { \operatorname* { P r } ( V ( \eta , | X \rangle ) = 1 ) \le \frac { 1 } { 3 } } \end{array}$ (soundness).

The amplification lemma applies here as well. The definition of QMA also allows $V$ to have $\mathrm { p o l y } ( | \eta | )$ ancilla qubits each initialized in the $| 0 \rangle$ state (Gharibian et al., 2015).

One can also define the class QCMA, which is similar to QMA except that $| X \rangle$ is a classical state (Aharonov and Naveh, 2002). Since the quantum verifier can force Merlin to send him a classical witness by measuring the witness before applying the quantum algorithm, we have: MA $\subseteq$ QCMA $\subseteq$ QMA.

# C. The general relation between QMA completeness and universal AQC

The class of efficiently solvable problems on a quantum computer is bounded error quantum polynomial time (BQP) (Bernstein and Vazirani, 1993), which consists of the class of decision problems solvable by a uniform family of polynomial-size quantum circuits with error probability bounded below $1 / 2$ . Because of the polynomial equivalence between AQC and the circuit model, BQP is also the class of efficiently solvable problems on a universal adiabatic quantum computer. Its classical analog is the class bounded-error probabilistic polynomial time (BPP), and as expected BPP $\subseteq$ BQP (Bernstein and Vazirani, 1997). In addition, BQP $\subseteq$ QCMA (Aharonov and Naveh, 2002). Another interesting characterization is that BQP=QMAlog, where QMA $\mathrm { l o g }$ is the same as QMA except that the quantum proof has ${ \cal O } ( \log | \eta | )$ qubits instead of poly( $| \eta |$ ) (Marriott and Watrous, 2005).

This motivates the study of QMA, and in particular QMA completeness, as a tool for understanding universality. Indeed, it is often the case that whenever adiabatic universality can be proven for some class of Hamiltonians, then the local Hamiltonian problem with (roughly) the same class can be shown to be QMAcomplete and vice versa. Note, however, that there is no formal implication from either of those problems to the other (Aharonov et al., 2009). On the one hand, proving QMA-completeness is in general substantially harder than achieving universal AQC, where we can choose the initial state to be any easily prepared state that will help us solve the problem, so we can choose to work in any convenient subspace that is invariant under the Hamiltonian. Indeed, in the history-state construction, we introduce penalty terms to guard against illegal clock states [recall Eq. (75)]. For QMA, the states we work with are chosen adversarially from the full Hilbert space, and we must be able to check, using only local Hamiltonian terms, that they are of the correct (clock-state) form. On the other hand, proving adiabatic universality involves analyzing the spectral gap of the continuous sequence of Hamiltonians over the entire duration of the computation, whereas QMA-completeness proofs are only concerned with one Hamiltonian.

# D. QMA-completeness of the $k$ -local Hamiltonian problem and universal AQC

To prove that a promise problem is QMA-complete, one needs to prove that it is contained in QMA and that it is QMA-hard. The $k$ -local Hamiltonian Problem belongs to QMA for any constant $k$ , and in fact even for $k =$ $O \left( \log n \right)$ (Kitaev et al., 2000). For pedagogical proofs see (Aharonov and Naveh, 2002; Gharibian, 2013; Gharibian

et al., 2015).

The first example of a QMA-hard problem was the $k$ - local Hamiltonian problem for $k \geq 5$ (Kitaev et al., 2000), so that in particular the 5-local Hamiltonian problem is QMA-complete. This was reduced to 3-local (Kempe and Regev, 2003; Nagaj and Mozes, 2007) and then to 2-local (Kempe et al., 2006). Note that the 1-local Hamiltonian problem is in the complexity class P, since one can simply optimize for each 1-local term independently. Various simplifications of QMA-completeness for the 2-local case followed. In order to describe these, we first need to define a class of Hamiltonians:

$$
\begin{array} { r l } & { H _ { 1 } = \displaystyle \sum _ { ( i , j ) \in \mathcal { E } } J _ { i j } ^ { x } X _ { i } X _ { j } + J _ { i j } ^ { y } Y _ { i } Y _ { j } + J _ { i j } ^ { z } Z _ { i } Z _ { j } } \\ & { \qquad + \displaystyle \sum _ { i \in \mathcal { V } } h _ { i } ^ { x } X _ { i } + h _ { i } ^ { y } Y _ { i } + h _ { i } ^ { z } Z _ { i } \ , } \end{array}
$$

where $\nu$ and $\varepsilon$ are the vertex and edge sets of a graph ${ \mathcal { G } } =$ $( \nu , \mathcal { E } )$ , and all local fields $\{ h _ { i } ^ { \alpha } \}$ and couplings $\{ J _ { i j } ^ { \alpha } \}$ ( $\alpha \in$ $\{ x , y , z \} )$ are real. The Heisenberg model corresponds to $J _ { i j } ^ { x } = J _ { i \underline { { { j } } } } ^ { y } = J _ { i \underline { { { j } } } } ^ { z }$ , the $X Y$ model to y $J _ { i j } ^ { x } = J _ { i j } ^ { y }$ and $J _ { i j } ^ { z } = 0$ and the Ising model to $J _ { i j } ^ { x } = J _ { i j } ^ { y } = 0$ . When $J _ { i j } ^ { \alpha } < 0 \left( > 0 \right)$ the interaction between qubits $i$ and $j$ is ferromagnetic (antiferromagnetic). When we write “fully” below we mean that all interactions have the same sign. Unless explicitly mentioned otherwise we assume that the local fields are all zero.

Most of the simplifications of QMA-completeness are special cases of Eq. (96):

Geometrical locality: nearest-neighbor interactions with $\vec { \mathcal { G } }$ being a 2D square lattice (Oliveira and Terhal, 2008) or a triangular lattice (Piddock and Montanaro, 2015). Simple interactions in 2D: $Z Z X X$ and $Z X$ model (Biamonte and Love, 2008) [defined in Eqs. (99) and (100) below], fully ferromagnetic and fully antiferromagnetic Heisenberg model with local fields (Schuch and Verstraete, 2009), antiferromagnetic Heisenberg and $X Y$ models without local fields (Piddock and Montanaro, 2015).

Some of the simplifications of QMA completeness use other types of Hamiltonians:

Interacting fermions in 2D and the space-time construction (Breuckmann and Terhal, 2014).

• Multi-state particles in 1D (Aharonov et al., 2009; Hallgren et al., 2013; Nagaj, 2008).

Non-translationally invariant 1D systems (all twoparticle terms identical but position-dependent one-particle terms) (Kay, 2008).

• Translationally invariant 1D systems for which finding the ground state energy is complete for QMAEXP $^ { 2 5 }$ (Gottesman and Irani, 2013).

The 1D case is interesting since, as remarked in Sec. IV.E, the 1D restriction of MAX-2-SAT with $p$ -state variables is in P, yet (Aharonov et al., 2009) showed that for 12-state particles, the problem of approximating the ground state energy of a 1D system is QMA-complete. This result was improved to 11-state particles in (Nagaj, 2008), and then to 8-state particles in (Hallgren et al., 2013), who also pointed out a small error in (Aharonov et al., 2009) that could be fixed by using 13-state particles. Whether and at which point a further Hilbert space dimensionality reduction becomes impossible remains an interesting open problem.

The reduction from 5-local to 2-local is done using perturbative gadgets (Biamonte and Love, 2008; Bravyi et al., 2008a; Cao et al., 2015; Jordan and Farhi, 2008; Kempe et al., 2006; Oliveira and Terhal, 2008). The goal of the gadget is to approximate some target Hamiltonian $H ^ { \mathrm { T } }$ of $n$ qubits (e.g., the 5-local Hamiltonian from the history state construction at any time $s$ ) by a gadget Hamiltonian $H ^ { \mathrm { G } }$ acting on the same $n$ qubits as well as an additional $\mathrm { p o l y } ( n )$ ancilla qubits. The gadget Hamiltonian is typically written as

$$
H ^ { \mathrm { G } } = H ^ { \mathrm { A } } + \lambda V ~ ,
$$

where $H ^ { \mathrm { A } }$ is an unperturbed Hamiltonian (also called the penalty Hamiltonian), acting only on the ancilla space, and where $\lambda V$ is a perturbation that acts between the qubits of $H ^ { \mathrm { T } }$ and the ancilla qubits. Using perturbation theory, which we review in Appendix $\mathrm { E }$ , one can show that the lowest $2 ^ { n }$ eigenvalues of $H ^ { \mathrm { G } }$ differ from those of $H ^ { \mathrm { T } }$ by at most $\epsilon$ and the corresponding eigenstates have an overlap of at least $1 - \epsilon$ .

Completeness of the 2-local Hamiltonian problem means that every problem in QMA is reducible to the 2- local Hamiltonian decision problem in polynomial time. Since this reduction involves perturbative gadgets that preserve the spectrum of the original 5-local Hamiltonian, this means that the 2-local Hamiltonian derived from the 5-local Hamiltonian appearing in the universality proof of Sec. IV.B will also have an energy gap that is an inverse polynomial in the circuit length, and that the computation remains in the ground subspace with illegal clock states gapped away by the (now 2-local) penalty Hamiltonian. In the remainder of this subsection we briefly discuss a particularly simple form of 2-local Hamiltonians that is universal for AQC.

The QMA completeness of general 2-local Hamiltonians can be extended to show that a more restricted set of 2-local Hamiltonians composed of real-valued sums of the following pairwise products of Pauli matrices are QMAcomplete (Biamonte and Love, 2008):

$$
\{ I X , X I , I Z , Z I , Z X , X Z , Z Z , X X \} \ .
$$

The basic two steps to do this are: (1) Using the result of (Bernstein and Vazirani, 1997) that any quantum circuit can be represented using real-valued unitary gates operating on real-valued wavefunctions in the proof of the QMA-completeness of the 5-local Hamiltonian of the previous subsection, the Hamiltonian terms are all realvalued. This therefore extends QMA-completeness to 5- local real Hamiltonians. (2) The same gadgets used in (Kempe et al., 2006; Oliveira and Terhal, 2008) can be used to reduce the locality from five to two.

This can be further simplified to show that “ $Z Z X X$ ” Hamiltonians” that are linear combinations with real coefficients of only

$$
\{ I X , X I , I Z , Z I , Z Z , X X \}
$$

are QMA-complete. This is done by showing, using perturbation theory, that such Hamiltonians can be used to approximate the $\sigma ^ { z } \otimes \sigma ^ { x }$ and $\sigma ^ { x } \otimes \sigma ^ { z }$ terms. Similarly, perturbation theory can be used to show that “ $Z X$ ” Hamiltonians” that are linear combinations with real coefficients of only

$$
\{ I X , X I , I Z , Z I , Z X , X Z \}
$$

are QMA-complete (Biamonte and Love, 2008; Bravyi and Hastings, 2014; Cubitt and Montanaro, 2016).

# VI. STOQUASTIC ADIABATIC QUANTUM COMPUTATION

In this section we focus on the special class of “stoquastic Hamiltonians” [originally introduced in (Bravyi et al., 2008b)], that often arise in the context of quantum optimization.

Definition 5 (stoquastic Hamiltonian (Bravyi and Terhal, 2009)). A Hamiltonian $H$ is called stoquastic with respect to a basis $\boldsymbol { B }$ iff $H$ has real nonpositive off-diagonal matrix elements in the basis $\boldsymbol { \beta }$ .

For example, a Hamiltonian is stoquastic in the computational basis iff

$$
\langle x | H | x ^ { \prime } \rangle \leq 0 \forall x , x ^ { \prime } \in \{ 0 , 1 \} ^ { n } x \neq x ^ { \prime } .
$$

The computational basis is often singled out since it plays the role of the basis in which the final Hamiltonian is measured, which sometimes coincides with the basis in which that Hamiltonian is diagonal. The term “stoquastic” was introduced due to the similarity to stochastic matrices, such as arise in the theory of classical Markov chains.

Restricting to any basis still leaves some freedom in the definition. For example, a Hamiltonian $H \_ =$ $- \textstyle \sum _ { i } \sigma _ { i } ^ { x } + H _ { Z }$ , where $H _ { Z }$ is diagonal in the computational basis, is clearly stoquastic. However, applying a unitary transformation $\begin{array} { r } { U = \prod _ { i } \sigma _ { i } ^ { z } } \end{array}$ to the Hamiltonian gives $\begin{array} { r } { H ^ { \prime } = \sum \sigma _ { i } ^ { x } + H z } \end{array}$ , which according to Def. 5 is not stoquastic in the computational basis. Applying a local unitary basis transformation should not change the complexity of the problem. Therefore, for clarity we fix the basis such that the standard initial Hamiltonian always carries a minus sign, i.e., $- \sum _ { i } \sigma _ { i } ^ { x }$ . From this point forward, we restrict our discussion of stoquasticity to the standard computational basis. With this in mind, the class of stoquastic Hamiltonians includes the fully ferromagnetic Heisenberg and $X Y$ models, and the quantum transverse field Ising model [recall Eq. (96)].

Given the restriction of the Hamiltonian, one may ask whether there is a complexity class for which the $k$ -local stoquastic Hamiltonian problem is complete. This led to the introduction of the class StoqMA, for which the $k \geq 2$ -local stoquastic Hamiltonian is StoqMA-complete (Bravyi et al., 2006). This can be further refined to the result that the transverse Ising model on degree-3 graphs is StoqMA-complete (Bravyi and Hastings, 2017). Rather than give the formal (and rather involved) definition of StoqMA, we note that the only difference between StoqMA and MA is that a stoquastic verifier in StoqMA is allowed to do the final measurement in the $\{ | + \rangle , | - \rangle \}$ basis, whereas a classical coherent verifier in MA can only do a measurement in the standard $\{  { | 0 \rangle } ,  { | 1 \rangle } \}$ basis.26

Unlike MA and QMA, the threshold probabilities in StoqMA have an inverse polynomial rather than constant separation; this prevents amplification of the gap between the threshold probabilities based on repeated measurements with majority voting. Finally, it is known that MA $\subseteq$ StoqMA $\subseteq$ QMA (Bravyi et al., 2006).

To capture the important class of problems that are characterized by stoquastic evolution with the constraint of adiabatic evolution, we first introduce the following definition of a model of computation:

Definition 6 (StoqAQC). Stoquastic adiabatic quantum computation (StoqAQC) is the special case of AQC (Definition 1) restricted to $k$ -local ( $k$ fixed) stoquastic Hamiltonians.

Because we defined StoqAQC as a special case of AQC, the computation must proceed in the ground state. However, recall that the algorithm for the glued trees problem (Sec. III.D) is not subject to this ground state restriction and hence is not in StoqAQC. In Sec. VI.C we consider another model of stoquastic computation that is not subject to the ground state restriction.

StoqAQC has generated considerable interest since experimental implementations of stoquastic Hamiltonians are quite advanced (Bunyk et al., 2014; Weber et al., 2017). To characterize its computational power, we introduce a natural promise problem based on StoqAQC, and modeled after the $k$ -local Hamiltonian problem:27

Definition 7 (StoqAQCEval). The StoqAQCEval problem is defined on n qubits, with the following input:

• a continuous family of ( $k \geq 2$ )-local ( $k$ fixed) stoquastic Hamiltonians $\begin{array} { r } { H ( s ) = \sum _ { i = 1 } ^ { r } H _ { i } ( s ) } \end{array}$ with $r =$ poly(n) and parameterized by $s \in \lbrack 0 , 1 ]$ . For all $i$ and all $s$ , the non-zero entries of $H _ { i } ( s )$ are specified by poly(n) bits of precision, and $\| H _ { i } ( s ) \| =$ $p o l y ( n )$ . The ground state energy gap $\Delta [ H ( s ) ]$ satisfies $\Delta [ H ( s ) ] \ge 1 / p o l y ( n )$ for all $s$ .

![](images/55aeb82f9bf4a42589197126b7b41e553e90052203c369d936aa672f58b3f680.jpg)  
FIG. 4 Known relations between complexity classes relevant for AQC. The BStoqP class defined here (Def. 8) lies in the intersection StoqMA and BQP, and includes BPP.

two real numbers a and $b$ specified with poly $( n )$ bits of precision, and $b - a > 1 / p o l y ( n )$ .

The output ( $\boldsymbol { \theta }$ or $\mathit { 1 }$ ) answers the question: Is the smallest eigenvalue of $H ( s = 1 )$ smaller than a (output is 1), or are all eigenvalues larger than $b$ (output is 0)? Just as in the local Hamiltonian problem, we are promised that the outcome that the ground state energy is between a and b is not possible.

et al., 2008b). It is clear that BPP $\subseteq$ BStoqP, since 5-local StoqAQCEval is BPP-hard (using a a classical reversible circuit for universal AQC, with stoquastic gate terms and a 5-local stoquastic clock Hamiltonian). Finally, we know that BStoqP $\subseteq$ BQP, since StoqEvalAQC is in BQP by using the same proof that the adiabatic model in general can be simulated by the circuit model.

This allows us to (informally) define the complexity class that captures StoqAQC:

Definition 8 (BStoqP). BStoqP is the set of problems that are polynomial-time reducible to StoqAQCEval.

The StoqAQCEval problem is clearly in StoqMA, because the $k \_ \geq \ 2$ -local stoquastic Hamiltonian problem is StoqMA-complete (Bravyi et al., 2006). Hence BStoqP $\subseteq$ StoqMA, as depicted in Fig. 4, which summarizes the relations between many of the complexity classes we have discussed.28 NP and MA are unlikely to be subsets of BStoqP, since StoqAQC would not be expected to solve NP-complete problems in polynomial time. The tightest inclusion in a classical complexity class we know of is in AM,29 since the latter includes StoqMA (Bravyi

# A. Why it might be easy to simulate stoquastic Hamiltonians

In this subsection we briefly summarize the complexity-theoretic evidence obtained so far that suggests that the StoqAQC setting is less powerful than universal quantum computation. Let us start with a lemma that characterizes the “classicality” of ground states of stoquastic Hamiltonians.

Lemma 3. The ground state $| \psi \rangle$ of a stoquastic Hamiltonian $H$ can always be expressed using only real nonnegative amplitudes: $\begin{array} { r } { | \psi \rangle = \sum _ { x \in \{ 0 , 1 \} ^ { n } } a _ { x } | x \rangle } \end{array}$ , where $a _ { x } \geq 0$ $\forall x$ .

Proof. It follows directly from the stoquastic property that the corresponding Gibbs density matrix $\rho =$ $\exp ( - \beta H ) / \mathrm { T r } [ \exp ( - \beta H ) ]$ has non-negative matrix elements in the computational basis for any $\beta > 0$ . In particular, if $H$ is stoquastic then for sufficiently small $\beta$ , $1 - \beta H$ has only non-negative matrix elements. The largest eigenvalue of $1 - \beta H$ corresponds to the ground state energy of $H$ . Thus, by the Perron-Frobenius theorem (see Sec. III.E.1) the ground state of $H$ can be chosen to have non-negative amplitudes. □

Consequently, if the Hamiltonian is stoquastic, a classical probability distribution can be associated with the ground state. This raises the question as to whether StoqAQC is a model that is capable of quantum speedup over classical algorithms. Following is the evidence regarding this question.

1. The ground state energy of the fully ferromagnetic transverse field Ising model can be found to a given additive error in polynomial time with a classical algorithm on any graph, with or without a transverse magnetic field (Bravyi and Gosset, 2016).

2. In (Bravyi et al., 2008b) it was shown that for any fixed $k$ , stoquastic $k$ -local Hamiltonian is contained in the complexity class AM. Thus, unless QMA $\subseteq$ AM (which is believed to be unlikely), stoquastic $k$ -local Hamiltonian is not QMA-complete.

3. It was also shown in (Bravyi et al., 2008b) that gapped StoqAQC can be simulated in PostBPP, the complexity class described by a polynomialtime classical randomized computer with the ability to post-select on some subset of the bits after the algorithm is run. $^ { 3 0 }$ I.e., it suffices to call an oracle for problems in PostBPP a polynomial number of times to efficiently sample from the ground state of a gapped stoquastic Hamiltonian.31

Suppose that StoqAQC could be used to perform universal quantum computation. Since gapped StoqAQC can be simulated in PostBPP, this would imply that SampBQP $\subseteq$ SampPostBPP.32 In other words, this would imply that polynomial time quantum algorithms can be simulated classically in polynomial time using post-selection. This would then imply that PostBPP=PostBQP which in turn would collapse the polynomial hierarchy. Thus it is unlikely that StoqAQC is universal for AQC.

4. In (Bravyi and Terhal, 2009) it was shown that adiabatic evolution along a path composed entirely of stoquastic frustration-free Hamiltonians (recall Definition 4) may be simulated by a sequence of classical random walks, i.e., is contained in BPP.

With this evidence for the potential limitations of stoquastic Hamiltonians, the question arises if they are worthy of pursuit, either theoretically or experimentally. However, it is important to remember that the weakness of stoquastic Hamiltonians arises when one assumes that they generate an evolution that occurs in the ground state. Indeed, we will see in Sec. VI.C that excited state stoquastic evolution can be as powerful as universal AQC. Moreover, in the next subsection we briefly review counterexamples to the claim that stoquastic Hamiltonians are necessarily easy to simulate using heuristic classical algorithms.

# B. Why it might be hard to simulate stoquastic Hamiltonians

There does not exist a general theorem that rules out a quantum speedup of StoqAQC over all possible classical algorithms. However, it is often stated that Monte Carlo simulations of StoqAQC do not suffer from the sign problem and will therefore simulate StoqAQC without a slowdown. Specifically, the conjecture is that if the Monte Carlo simulation starts at $s = 0$ in the equilibrium state, and if $s$ changes by a small amount $\epsilon$ from one step to the next, where $\epsilon$ is polynomially small in the system size $n$ , the inverse temperature $\beta$ and the spectral gap $\Delta$ , then the Monte Carlo simulation stays close to the equilibrium state along the path. For sufficiently large $\beta$ , this would correspond to following the instantaneous ground state. In this subsection we briefly review theoretical evidence that such a conjecture is not always true. We focus on two of the most direct classical competitors to StoqAQC: path integral quantum Monte Carlo (PI-QMC), and diffusion quantum Monte Carlo (D-QMC).

# 1. Topological obstructions

In (Hastings and Freedman, 2013) examples were given of StoqAQC with a polynomially small eigenvalue gap, but where PI-QMC take exponential time to converge. Loosely, the failure of convergence was due to topological obstructions around which the worldlines (trajectories in imaginary time) can get tangled.

The simplest of the examples can be understood intuitively as follows. A sombrero-like potential is constructed for a single particle with a deep circular minimum of radius $r$ . The worldline of the particle in PI-QMC with closed boundary conditions is some closed path that follows this circle in imaginary time. Because of the depth of the potential at the minimum the distribution of trajectories has very small probability to include any point with radius larger than $r$ and it takes an exponential time in the winding number to transition from one winding number sector to another. Therefore, if an appropriate dimensionless combination of the radius $r$ or the mass of the particle is changed sufficiently fast then PI-QMC fails to equilibrate. At the same time it can be shown that for this example the gap closes polynomially and so one expects that adiabatic evolution requires only polynomial time to find the ground state.

While this example uses winding numbers to construct a protocol for which PI-QMC takes exponential time to equilibrate, PI-QMC can still find the ground state. To observe a more dramatic effect where not only equilibration is hampered but also the probability of finding the ground state is low, one can introduce stronger topological effects and additionally exploit the discrepancy between $L _ { 1 }$ and $L _ { 2 }$ -normalized wavefunctions. This was first done in the “bouquet of circles” example introduced in (Hastings and Freedman, 2013), which shows that PI-QMC can fail to converge even when using open boundary conditions. The example was designed so that the majority of the amplitude $\psi$ lies within an expander graph, although the majority of the probability $| \psi | ^ { 2 }$ does not. Because the endpoints of the wordlines are distributed according to $\psi$ and not $| \psi | ^ { 2 }$ , this effectively “pins” them to the expander graph. This pinning means that even though the worldline is in principle open, the worldline is nevertheless prevented from changing its topological sector within the bouquet of circles. This then causes failure of convergence.

A more general method using perturbative gadgets is explained in (Hastings and Freedman, 2013), that allows one to map between continuous variables and spins and applies to all the examples given there.

# 2. Non-topological obstructions

Diffusion Monte Carlo algorithms should not be affected by topological obstructions that depend on closed boundary conditions, since they do not exhibit periodicity in the imaginary time direction. Rather than use topological obstructions, it is possible to rely entirely on the discrepancy between $L _ { 1 }$ and $L _ { 2 }$ -normalization to design examples where Monte Carlo methods have differing convergence from AQC. This discrepancy was used in (Jarret et al., 2016) to ensure that the walkers in a DQMC algorithm never “learn” about a potential well that contains the solution, causing DQMC to take exponential time to converge. Since the gap for the adiabatic process is large, QA takes only polynomial time.

Let $H ( s )$ be some stoquastic Hamiltonian acting on a Hilbert space whose basis states can be equated with the vertices $V$ of some graph. Let $\psi _ { s } ( x ) : V \mapsto \mathbb { C }$ denote the ground state of $H ( s )$ . Define probability distributions $\begin{array} { r } { p _ { s } ^ { ( 1 ) } ( x ) = \frac { \psi _ { s } ( x ) } { \sum _ { y \in V } \psi _ { s } ( y ) } } \end{array}$ and $p _ { s } ^ { ( 2 ) } ( x ) = \psi _ { s } ^ { 2 } ( x )$ . The stoquasticity of $H ( s )$ ensures that $\psi _ { s } ( x ) \geq 0$ , so that $p _ { s } ^ { ( 1 ) } ( x )$ is a valid probability distribution.

D-QMC algorithms perform random walks designed to ensure that a population of random walkers converges to $p _ { s } ^ { ( 1 ) } ( x )$ . However, in exponentially large Hilbert spaces there can be vertices such that the distribution associated with the $L _ { 2 }$ -normalized wavefunction $p _ { s } ^ { ( 2 ) } ( x )$ is polynomial, but the distribution associated with the $L _ { 1 }$ - normalized wavefunction $p _ { s } ^ { ( 1 ) } ( x )$ is exponentially small. The idea behind the examples in (Jarret et al., 2016) is to exploit this discrepancy to design polynomial-time stoquastic adiabatic processes that the corresponding D-QMC simulations will fail to efficiently simulate.

The main example given in (Jarret et al., 2016) is the stoquastic Hamiltonian $H ( s ) = { \textstyle { \frac { 1 } { n } } } [ L + b ( s ) W ] - c ( s ) P$ , where $L$ is the graph Laplacian of the $n$ -bit hypercube, $W$ is the Hamming weight operator (i.e., $W | x \rangle = | x | | x \rangle$ where $| x |$ is the Hamming weight of the bit-string $x$ ), $P = | 0 \cdots 0 \rangle \langle 0 \cdots 0 |$ . In terms of Pauli matrices this Hamiltonian can be written, up to an overall constant, as

$$
H ( s ) = - { \frac { 1 } { n } } \sum _ { j = 1 } ^ { n } \left( X _ { j } + { \frac { 1 } { 2 } } b ( s ) Z _ { j } \right) - c ( s ) P .
$$

The schedules $b ( s )$ and $c ( s )$ are:

$$
b ( s ) = \left\{ \begin{array} { l l } { 2 s b } & { c ( s ) = \left\{ \begin{array} { l l } { 0 } & { s \in [ 0 , 1 / 2 ) } \\ { ( 2 s - 1 ) c } & { s \in [ 1 / 2 , 1 ] } \end{array} \right. \mathrm { ~ . ~ } } \end{array} \right.
$$

For $s \in [ 0 , 1 / 2 )$ this is a Hamiltonian of $n$ non-interacting qubits whose gap is easily seen to be $\textstyle { \frac { 2 } { n } } { \sqrt { 1 + ( s b / 2 ) ^ { 2 } } }$ , minimized at $s = 0$ where it equals $2 / n$ . The ground state is given by $| \psi ( \theta ) \rangle ^ { \otimes n }$ , where $| \psi ( \theta ) \rangle = \cos ( \theta / 2 ) | 0 \rangle +$ $\sin ( \theta / 2 ) | 1 \rangle$ and $\theta = \tan ^ { - 1 } [ 2 / ( s b ) ]$ . For $s \in [ 1 / 2 , 1 ]$ it can be shown that the minimum gap is attained at $s = 1 / 2$ , where it equals $1 / \sqrt { 2 n + O ( n ^ { - 3 / 2 } ) }$ . Thus the overall minimum gap is polynomial $( 2 / n )$ and the StoqAQC process converges to the ground state $| 0 \cdots 0 \rangle$ in polynomial time. By choosing $b$ so that at $s = 1$ we have $\cos ( \theta / 2 ) =$ $1 - 1 / ( 4 n )$ , it is easy to show from the analysis of the noninteracting problem that the probability of ending up in the ground state is $p _ { s = 1 } ^ { ( 2 ) } ( 0 \cdot \cdot \cdot 0 ) = \cos ^ { 2 n } ( \theta _ { s = 1 } / 2 ) \to e ^ { - 1 / 2 }$ in the limit $n \to \infty$ .

On the other hand, for the non-interacting problem (when $s \in [ 0 , 1 / 2 )$ ) the D-QMC process $^ { 3 3 }$ samples from the distribution $p _ { s } ^ { ( 1 ) } ( x ) \ = \ \sin ( \theta / 2 ) ^ { | x | } \cos ( \theta / 2 ) ^ { n - | x | } / Z _ { s }$ where $\begin{array} { r l r } { Z _ { s } } & { { } = } & { \sum _ { x \in \{ 0 , 1 \} ^ { n } } \sin ( \theta / 2 ) ^ { | x | } \cos ( \theta / 2 ) ^ { n - | x | } \quad = } \end{array}$ $[ \sin ( \theta / 2 ) + \cos ( \theta / 2 ) ] ^ { n }$ , so that for large $n$ we have $Z _ { 1 } \approx$ $( 1 + 1 / { \sqrt { 2 n } } ) ^ { n } \to e ^ { \sqrt { n / 2 } }$ for the same choice of $b$ . Thus, forat $s ~ = ~ 1 / 2$ $p _ { s = 1 / 2 } ^ { ( 1 ) } ( 0 \cdot \cdot \cdot 0 ) \ = \ \cos ^ { n } ( \theta _ { s = 1 } / 2 ) / Z _ { s = 1 } \ $ $e ^ { - 1 / 4 } e ^ { - \sqrt { n / 2 } }$ . Since at $s = 1 / 2$ the random walkers that diffuse in the D-QMC process have a probability to be at the all-zeros string that is of order $e ^ { - { \sqrt { n / 2 } } }$ , with high likelihood, no walkers will land on the all-zeros string until the number of time-steps times the number of walkers approaches $e ^ { { \sqrt { n / 2 } } }$ . Until this happens it is impossible for the distribution of walkers to be affected by the change in the potential at the all-zeros string that is occurring from $s = 1 / 2$ to $s = 1$ ; no walkers have landed there, and the D-QMC algorithm has therefore never queried the value of the potential at that site. Only after allowing for this exponential cost, and by appropriately choosing $c$ , does the D-QMC algorithm find the ground state with high probability.34

# C. QMA-complete problems and universal AQC using stoquastic Hamiltonians with excited states

Our definition of StoqAQC (Definition 6) stipulates that the computation must proceed in the ground state. It turns out that if this condition is relaxed, computation with stoquastic Hamiltonians is as powerful as AQC, i.e., it is universal. Here we review a construction by (Jordan et al., 2010) of a 3-local stoquastic Hamiltonian that, by allowing for excited state evolution, is both QMAcomplete and universal for AQC.

We start with the QMA-complete Hamiltonian introduced in Sec. V.D, that can be written as:

$$
H _ { Z Z X X } = \sum _ { i } d _ { i } X _ { i } + h _ { i } Z _ { i } + \sum _ { i \leq j } J _ { i j } ^ { x } X _ { i } X _ { j } + J _ { i j } ^ { z } Z _ { i } Z _ { j } \ ,
$$

where $d _ { i }$ , $h _ { i }$ , $J _ { i j } ^ { x }$ and $J _ { i j } ^ { z }$ are arbitrary real coefficients. The key idea is to eliminate the negative matrix elements in each term. Toward this end the Hamiltonian is written as:

$$
H _ { Z Z X X } = - \sum _ { k } \alpha _ { k } T _ { k } \ ,
$$

where $T _ { k } \ \in \ \{ \pm X _ { i } , \pm Z _ { i } , \pm X _ { i } X _ { j } , \pm Z _ { i } Z _ { j } \}$ and such that $\alpha _ { k } \ > \ 0$ . For an $n$ -qubit system, the operators $T _ { k }$ are represented by $2 ^ { n } \times 2 ^ { n }$ symmetric matrices with entries taking value $+ 1 , - 1 , 0$ . We use the regular representation of the $Z _ { 2 }$ group to make the replacement

$$
1 \to { \left( \begin{array} { l l } { 1 } & { 0 } \\ { 0 } & { 1 } \end{array} \right) } , \ - 1 \to { \left( \begin{array} { l l } { 0 } & { 1 } \\ { 1 } & { 0 } \end{array} \right) } , \ 0 \to { \left( \begin{array} { l l } { 0 } & { 0 } \\ { 0 } & { 0 } \end{array} \right) }
$$

in $T _ { k }$ to define a new operator $\tilde { T } _ { k }$ . The matrix representation of $\tilde { T } _ { k }$ is of size $2 ^ { n + 1 } \times 2 ^ { n + 1 }$ , and since the original $T _ { k }$ was either 1-local or 2-local acting on $n$ qubits, we can interpret $\tilde { T } _ { k }$ as being 2-local or 3-local acting on $n + 1$ qubits. Note furthermore that $T _ { k }$ is such that it only has one non-zero entry per row and column, hence with the substitution in Eq. (106), the $\tilde { T } _ { k }$ ’s are permutation matrices. We can write the following Hamiltonian acting on $n + 1$ qubits:

$$
\tilde { H } _ { Z Z X X } = - \sum _ { k } \alpha _ { k } \tilde { T } _ { k }
$$

which is a linear combination of permutation matrices with negative coefficients. This makes $\Dot { H } _ { Z Z X X }$ a (3-local) stoquastic Hamiltonian. We can write it as:

$$
\tilde { H } _ { Z Z X X } = H _ { Z Z X X } \otimes | - \rangle \langle - | + \bar { H } _ { Z Z X X } \otimes | + \rangle \langle + | ~ ,
$$

where $\begin{array} { r } { H _ { Z Z X X } = - \sum _ { k } \alpha _ { k } | T _ { k } | } \end{array}$ and $| T _ { k } |$ is the entrywise absolute value of $T _ { k }$ . To see why this is the case, first consider a positive element $( T _ { k } ) _ { i j }$ . Then:

$$
- \alpha _ { k } ( T _ { k } ) _ { i j } \otimes | - \rangle \langle - | - \alpha _ { k } ( T _ { k } ) _ { i j } \otimes | + \rangle \langle + | = - \alpha _ { k } ( T _ { k } ) _ { i j } \otimes \mathbb { 1 }
$$

corresponding to the first replacement in Eq. (106). For a negative element, we have:

$$
- \alpha _ { k } ( T _ { k } ) _ { i j } \otimes | - \rangle \langle - | + \alpha _ { k } ( T _ { k } ) _ { i j } \otimes | + \rangle \langle + | = - \alpha _ { k } ( T _ { k } ) _ { i j } \otimes \sigma ^ { x }
$$

corresponding to the second replacement in Eq. (106). The spectrum of $\tilde { H } _ { Z Z X X }$ separates into two sectors $\mathcal { L } _ { \pm }$ . The sector $\mathcal { L } _ { - }$ is spanned by $\left| \varepsilon _ { j } \right. \otimes \left| - \right.$ , where $\left. \varepsilon _ { j } \right.$ are the eigenstates of $H _ { Z Z X X }$ , while the sector $\mathcal { L } _ { + }$ is spanned by $\left| \bar { \varepsilon } _ { j } \right. \otimes \left| + \right.$ , where $\left. \bar { \varepsilon } _ { j } \right.$ are the eigenstates of $H _ { Z Z X X }$ . Because the Hamiltonian does not couple the two sectors (there are no interactions that take the ancilla qubit from $\left| \pm \right.$ to $\left| \mp \right.$ ), a closed system evolution initialized in the $\mathcal { L } _ { - }$ sector will remain in that sector.

Because the spectrum in the $\mathcal { L } _ { - }$ sector is identical to that of $H _ { Z Z X X }$ , which is capable of universal adiabatic quantum computation, then universal adiabatic quantum computation can be performed in the $\mathcal { L } _ { - }$ sector. However, the lowest energy state in $\mathcal { L } _ { - }$ may not necessarily be the ground state of $\tilde { H } _ { Z Z X X }$ . Therefore, this establishes universal AQC using a stoquastic Hamiltonian only if we do not restrict ourselves to the ground state of the Hamiltonian. Attempting to make the lowest energy state in $\mathcal { L } _ { - }$ be the ground state requires introducing a sufficiently large term proportional to $\mathbb { 1 } \otimes | + \rangle \langle + |$ to the Hamiltonian $\bar { H } _ { Z Z X X }$ , but such a term would make the new Hamiltonian non-stoquastic since it would introduce positive off-diagonal elements. Therefore this method does not establish universal adiabatic quantum computation using the ground state of a stoquastic Hamiltonian.

# D. Examples of slowdown by StoqAQC

It should not come as a surprise that AQC with an arbitrary final Hamiltonian, which is essentially a black box approach, does not guarantee quantum speedups. It can be vulnerable to the same sorts of locality traps confronted by heuristic classical algorithms such as simulated annealing.

A slowdown, or failure of AQC to provide a speedup, is a scenario wherein a more efficient classical algorithm is known. All the known examples that fall into this category arise when the gap closes “too fast” in the problem size. However, it is important to note that adiabatic theorems provide only upper bounds on run time, not lower bounds. Thus, e.g., an exponentially small gap does not strictly imply an exponentially long run time. The inverse gap is often treated as a proxy for run time, but a claim such as an equal scaling of the inverse gap and the run time does not hold as a general theorem.

With this caveat in mind, in this subsection we review such “small-gap” examples in increasing order of generality or difficulty of analysis, which all arise in the StoqAQC context. However, we must first note another important caveat. Namely, in some of the examples we present numerical evidence that is based, in necessity, on finite size calculations. One is then often tempted to extrapolate such evidence to the asymptotic scaling. Of course, any such extrapolations based purely on numerics are conjectures. For example, a claim of exponential scaling can never be proven based on numerics alone, as any finite set of data points can always be perfectly fit by a polynomial of sufficiently high degree. Nevertheless, numerics-driven conjectures about scaling can be quite useful, especially if supported by other, analytical arguments.

Subsequently, we will see in Sec. VII that there are various methods for circumventing slowdowns, e.g., via the introduction of non-stoquastic terms.

# 1. Perturbed Hamming Weight Problems with Exponentially Small Overlaps

The plain Hamming weight problem is described by

$$
H _ { \mathrm { H W } } ( s ) = ( 1 - s ) \frac 1 2 \sum _ { i } \left( 1 - \sigma _ { i } ^ { x } \right) + s \sum _ { x } \left| x \right| \left| x \right. \left. x \right| .
$$

Its cost function is simply the Hamming weight $| x |$ of the binary bit-string $x$ , which is trivially minimized at $x = 0 ^ { n }$ . Consider the following perturbation of the plain Hamming weight problem (van Dam et al., 2001):

$$
h ( x ) = { \left\{ \begin{array} { l l } { \left| x \right| { \mathrm { ~ i f ~ } } \left| x \right| < n } \\ { - 1 { \mathrm { ~ i f ~ } } \left| x \right| = n } \end{array} \right. } .
$$

This is a toy problem that is designed to be hard for classical algorithms based on local search: its global optimum lies in a narrow basin, while there is a local optimum with a much larger basin. An algorithm such as simulated annealing with single spin updates would require exponential time to find the global minimum.

Let us write the corresponding StoqAQC Hamiltonian to make the perturbation explicit:

$$
\begin{array} { r } { H ( s ) = H _ { \mathrm { H W } } ( s ) - s ( n + 1 ) | \mathbb { 1 } ^ { n } \rangle \langle \mathbb { 1 } ^ { n } | ~ , } \end{array}
$$

where $\left| 1 ^ { n } \right.$ is the all-one state. Denote the instantaneous eigenstates of $H _ { \mathrm { H W } } ( s )$ by $\{ | v _ { i } ( s ) \rangle \}$ ( $v _ { 0 }$ denotes the ground state). Note that the overlap of the all-one-state with the instantaneous ground state of the plain Hamming Weight algorithm is always exponentially small:

$$
\langle 1 ^ { n } | v _ { 0 } ( s ) \rangle \leq { \frac { 1 } { \sqrt { 2 ^ { n } } } } ~ .
$$

We will show that this fact causes the adiabatic algorithm as defined in Eq. (111) to take exponential time because it leads to an exponentially small gap.

Define a matrix $A ( s )$ with elements:

$$
A _ { i j } = \langle v _ { i } ( s ) | H ( s ) | v _ { j } ( s ) \rangle ~ .
$$

Note that $A ( 0 )$ is diagonal and $A _ { 0 0 } ( 0 ) \ = \ 0$ , equal to the ground state eigenvalue. Also $A ( 1 )$ is diagonal, but now $A _ { 2 ^ { n } - 1 , 2 ^ { n } - 1 } ( 1 ) \ = \ - 1$ is equal to the ground state eigenvalue. Define a matrix $B$ in the same basis as:

$$
B _ { i j } ( s ) = { \left\{ \begin{array} { l l } { A _ { 0 0 } ( s ) } & { i = j = 0 } \\ { 0 } & { i = 0 , j > 0 } \\ { 0 } & { i > 0 , j = 0 } \\ { A _ { i j } ( s ) } & { { \mathrm { o t h e r w i s e } } } \end{array} \right. }
$$

The matrix $B$ always has $A _ { 0 0 }$ as an eigenvalue. By construction, we know that at $s = 1$ , the matrix $B$ has $^ { - 1 }$ as its ground state eigenvalue (located in the $2 ^ { n - 1 } \times 2 ^ { n - 1 }$ sub-matrix). Because the matrix transforms continuously between these two extremes, there cannot be a jump in the ground state eigenvalue, so there must be a critical value of $s$ , which we denote by $s _ { c }$ , where $B$ has a vanishing gap.

The optimal matching distance between $A$ and $B$ expresses how close their eigenvalue spectra are:

$$
d ( A , B ) = \operatorname* { m i n } _ { \pi } \operatorname* { m a x } _ { 1 \leq j \leq 2 ^ { n } } \left| \lambda _ { j } - \mu _ { \pi ( j ) } \right| ,
$$

where $\pi$ denotes a permutation. Since $A$ and $B$ are Hermitian, this is upper-bounded by $\| A - B \| _ { 2 }$ (Bhatia, R., 1997). The matrix $A - B$ only has non-zero entries $( A - B ) _ { 0 , j > 0 } = A _ { 0 , j > 0 }$ and $( A - B ) _ { j > 0 , 0 } = A _ { j > 0 , 0 } =$ $A _ { 0 , j > 0 } ^ { * }$ , with ${ \cal A } _ { 0 , j > 0 } ~ = ~ - s ( n + 1 ) \langle v _ { 1 } ( s ) | 1 ^ { n } \rangle \langle 1 ^ { n } | v _ { j } ( s ) \rangle$

$$
\begin{array} { r l } & { \| A - B \| _ { 2 } = } \\ & { \quad s ( n + 1 ) | \langle v _ { 1 } ( s ) | 1 ^ { n } \rangle | \displaystyle \sqrt { \displaystyle \sum _ { j = 1 } ^ { 2 n - 1 } \langle 1 ^ { n } | v _ { j } ( s ) \rangle \langle v _ { j } ( s ) | 1 ^ { n } \rangle } } \\ & { \quad = s ( n + 1 ) | \langle v _ { 1 } ( s ) | 1 ^ { n } \rangle | \sqrt { 1 - | \langle 1 ^ { n } | v _ { 0 } ( s ) \rangle | ^ { 2 } } } \\ & { \quad \le s ( n + 1 ) | \langle v _ { 1 } ( s ) | 1 ^ { n } \rangle | \le \frac { s ( n + 1 ) } { \sqrt { 2 ^ { n } } } . } \end{array}
$$

Thus, the gap of $A$ [and hence of $H ( s ) ]$ is always upperbounded by the gap of $B$ plus twice $\| A - B \| _ { 2 }$ . Since at $\begin{array} { l l l } { s } & { = } & { s _ { c } } \end{array}$ the gap of $B$ is zero, it follows that the gap of $H ( s _ { c } )$ is $\leq \ s _ { c } ( n + 1 ) / \sqrt { 2 ^ { n - 2 } }$ (van Dam et al., 2001). Therefore, the exponentially small overlap between the unperturbed instantaneous ground state and the perturbed final ground state results in the adiabatic algorithm requiring exponential time to reach the final ground state. Informally, this can also be viewed as the inability of local quantum search (fluctuations induced by the local initial Hamiltonian) to explore the entire (non-local) energy landscape effectively.

# 2. 2-SAT on a Ring

In this subsection we review the “2-SAT on a Ring” problem introduced in the seminal work (Farhi et al., 2000), which launched the field of AQC. This example is instructive because of its use of the Jordan-Wigner and Fourier transformation techniques, and is also of historical interest. It also serves to illustrate that even a polynomially small gap does not guarantee a quantum speedup. We thus review it in detail.

Consider an $n$ -bit SAT problem with $n$ clauses. Each clause only acts on adjacent bits, i.e., the clause $C _ { j }$ only acts on bits $j$ and $j + 1$ , where we identify bit $n + 1$ with bit 1. Let each clause be of only two forms: “agree” clauses where 00 and 11 are satisfying assignments, and “disagree” clauses where 01 and 10 are satisfying assignments. Since an odd number of satisfied disagree clauses means that the first bit of the first disagree clause is the opposite of the second bit of the last disagree clause, yet bits 1 and $n { \mathrel { + { 1 } } }$ must agree, there must be an even number of disagree clauses in order for a satisfying assignment to exist. The classical computational cost of finding a satisfying assignment is at most $n$ : given the list of clauses, a satisfying assignment is found (assuming an even number of disagree clauses) simply by going around thesatisfying each clause one at a time. Note that if is a satisfying assignment then so is $\{ \neg w _ { i } \} _ { i = 1 } ^ { n }$ . $\{ w _ { i } \} _ { i = 1 } ^ { n }$

Let us now define the final Hamiltonian $\begin{array} { r l } { H _ { 1 } } & { { } = } \end{array}$ $\textstyle \sum _ { i = 1 } ^ { n } H _ { C _ { i } }$ associated with the SAT problem, where each clause is represented by:

$$
H _ { C _ { i } } = \frac { 1 } { 2 } \left( 1 - ( - 1 ) ^ { x _ { i } } \sigma _ { i } ^ { z } \sigma _ { i + 1 } ^ { z } \right)
$$

$x _ { i } = 0$ (1) if $C _ { i }$ is an agree (disagree) clause .

The ground states of $H _ { \mathrm { P } }$ are then given by $\left| 0 \right. _ { 1 } \otimes _ { i = 2 } ^ { n } \left| w _ { i } \right. _ { i }$ and $\otimes _ { i = 1 } ^ { n } | \neg w _ { i } \rangle _ { i }$ , where $\begin{array} { r } { w _ { i } = \bigoplus _ { j = 1 } ^ { i - 1 } x _ { j } } \end{array}$ ( $i \geq 2$ and addition modulo 2). It is possible to gauge away all the disagree clauses. To see this, let $U$ be the unitary transformation defined such that

$$
U | z _ { i } \rangle = \left\{ \begin{array} { l l } { { | \neg z _ { i } \rangle } ~ , ~ \mathrm { i f } ~ w _ { i } = 1 } \\ { { | z _ { i } \rangle } ~ , ~ \mathrm { i f } ~ w _ { j } = 0 } \end{array} \right. ~ .
$$

Under this unitary transformation we have:

$$
H _ { 1 } ^ { \prime } = U H _ { 1 } U ^ { \dag } = \sum _ { i } \frac { 1 } { 2 } \left( \mathbb { 1 } _ { i } - \sigma _ { i } ^ { z } \sigma _ { i + 1 } ^ { z } \right) \ ,
$$

i.e., the new final Hamiltonian is a sum of just agree clauses. Note that this unitary transformation requires us to know the ground state, but $H _ { 1 } ^ { \prime }$ and $H _ { 1 }$ are isospectral, so we can use it for convenience in our gap analysis. The adiabatic computation procedure will be governed by the following time-dependent Hamiltonian:

$$
H ( s ) = ( 1 - s ) H _ { 0 } + s H _ { 1 } ^ { \prime } \ , \quad 0 \leq s \leq 1 \ ,
$$

with the initial Hamiltonian $\begin{array} { r } { H _ { 0 } = \sum _ { i } \mathbb { 1 } _ { i } - \sigma _ { i } ^ { x } } \end{array}$ . We wish to diagonalize $H ( s )$ in order to find its ground state gap. First, define the negation operator $\begin{array} { r } { G = \prod _ { i = 1 } ^ { n } \sigma _ { i } ^ { x } } \end{array}$ such that:

$$
G \left( \otimes _ { i = 1 } ^ { n } \vert z _ { i } \rangle \right) = \otimes _ { i = 1 } ^ { n } \vert \neg z _ { i } \rangle \ ,
$$

which clearly commutes with $H ( s )$ . The uniform superposition state, which is the ground state of $H ( 0 )$ , is invariant under $G$ , i.e., it has eigenvalue $+ 1$ under $G$ . Therefore, the unitary dynamics will keep the state in the sector with $G = + 1$ if it starts in the ground state of $H ( 0 )$ . Let us then write $H ( s )$ purely in the $G = + 1$ sector. Second, define the Jordan-Wigner transformation

$$
\begin{array} { r l } & { b _ { j } = \sigma _ { 1 } ^ { x } \sigma _ { 2 } ^ { x } \ldots \sigma _ { j - 1 } ^ { x } \sigma _ { j } ^ { - } } \\ & { b _ { j } ^ { \dagger } = \sigma _ { 1 } ^ { x } \sigma _ { 2 } ^ { x } \ldots \sigma _ { j - 1 } ^ { x } \sigma _ { j } ^ { + } } \end{array}
$$

where $\begin{array} { r } { \sigma _ { j } ^ { \pm } = \frac { 1 } { 2 } \left( \sigma _ { j } ^ { z } \pm i \sigma _ { j } ^ { y } \right) } \end{array}$ . These are fermionic operators that satisfy:

$$
\begin{array} { l } { { \{ b _ { j } , b _ { k } \} = 0 \quad \mathrm { ( a m o u n t s ~ t o ~ } \left\{ \sigma _ { j } ^ { - } , \sigma _ { k } ^ { - } \right\} = 0 \mathrm { ) } } } \\ { { \{ b _ { j } , b _ { k } ^ { \dagger } \} = \delta _ { j k } \quad \mathrm { ( a m o u n t s ~ t o ~ } \left\{ \sigma _ { j } ^ { - } , \sigma _ { k } ^ { + } \right\} = \delta _ { j k } \mathrm { ) } \mathrm { ~ . } } } \end{array}
$$

Note that

$$
\begin{array} { l } { { b _ { j } ^ { \dagger } b _ { j } = \displaystyle \frac { 1 } { 2 } \left( \mathbb { 1 } _ { j } - \sigma _ { j } ^ { x } \right) \ , \ j = 1 , \ldots , n \ } } \\ { { \left( b _ { j } ^ { \dagger } - b _ { j } \right) \left( b _ { j + 1 } ^ { \dagger } + b _ { j + 1 } \right) = \sigma _ { j } ^ { z } \sigma _ { j + 1 } ^ { z } \ , \ j = 1 , \ldots , n - 1 \ } } \\ { { \left( 1 2 4 \right) \ } } \\ { { \left( b _ { n } ^ { \dagger } - b _ { n } \right) \left( b _ { 1 } ^ { \dagger } + b _ { 1 } \right) = - G \sigma _ { n } ^ { z } \sigma _ { 1 } ^ { z } \ . \ } } \end{array}
$$

In order to make Eqs. (124b) and (124c) consistent in the $G = + 1$ sector, we take $b _ { n + 1 } \equiv - b _ { 1 }$ . Using this, we have:

$$
\begin{array} { l } { { \displaystyle H ( s ) | _ { G = + 1 } = \sum _ { j = 1 } ^ { n } \left[ 2 ( 1 - s ) b _ { j } ^ { \dagger } b _ { j } \right. } } \\ { { \displaystyle \left. + \frac { s } { 2 } \left( \mathbb { 1 } _ { j } - \left( b _ { j } ^ { \dagger } - b _ { j } \right) \left( b _ { j + 1 } ^ { \dagger } + b _ { j + 1 } \right) \right) \right] } } \end{array}
$$

Third, since this Hamiltonian is invariant under translations $j \mapsto j + 1$ , define Fourier operators $\beta _ { p }$ :

$$
\beta _ { p } = \frac { 1 } { \sqrt { n } } \sum _ { j = 1 } ^ { n } e ^ { i \pi p j / n } b _ { j } \ , p = \pm 1 , \pm 3 , . . . , \pm ( n - 1 ) \ ,
$$

where for simplicity it is assumed that $n$ is even. Equivalently:

$$
b _ { j } = \frac { 1 } { \sqrt { n } } \sum _ { p = \pm 1 , . . . } e ^ { - i \pi p j / n } \beta _ { p } \ ,
$$

where we used the fact that $\begin{array} { r l } { \sum _ { p = \pm 1 , . . . } e ^ { i { \pi p ( j - j ^ { \prime } ) } / { n } } = } & { { } } \end{array}$ $n \delta _ { j , j ^ { \prime } }$ . Furthermore, note that:

$$
\begin{array} { c } { { \displaystyle \{ \beta _ { 2 a - 1 } , \beta _ { 2 b - 1 } \} = \displaystyle { \frac { 1 } { n } \sum _ { j , j ^ { \prime } } e ^ { i \pi ( ( 2 a - 1 ) j + ( 2 b - 1 ) j ^ { \prime } ) / n } \left\{ b _ { j } , b _ { j ^ { \prime } } \right\} } } } \\ { { { } } } \\ { { { } = 0 } } \\ { { \displaystyle { \left\{ \beta _ { 2 a - 1 } , \beta _ { 2 b - 1 } ^ { \dagger } \right\} = \displaystyle { \frac { 1 } { n } \sum _ { j , j ^ { \prime } } e ^ { i \pi ( ( 2 a - 1 ) j - ( 2 b - 1 ) j ^ { \prime } ) / n } \left\{ b _ { j } , b _ { j ^ { \prime } } ^ { \dagger } \right\} } } } } \\ { { { } } } \\ { { { = \displaystyle { \frac { 1 } { n } \sum _ { j = 1 } ^ { n } e ^ { 2 \pi i ( a - b ) / n } = \delta _ { a , b } \qquad ( 1 2 8 \mathrm { b } ) } . } } } \end{array}
$$

so the set $\{ \beta _ { p } \}$ comprises valid fermionic operators. Writing the Hamiltonian in terms of this set, we have:

$$
\begin{array} { r l } {  { H ( s ) = \sum _ { p = 1 , 3 , \dots } [ 2 ( 1 - s ) ( \beta _ { p } ^ { \dagger } \beta _ { p } + \beta _ { - p } ^ { \dagger } \beta _ { - p } )  } } \\ & {  + s ( \mathbb { 1 } - \cos ( \frac { \pi p } { n } ) ( \beta _ { p } ^ { \dagger } \beta _ { p } - \beta _ { - p } \beta _ { - p } ^ { \dagger } )  } \\ & {  + i \sin ( \frac { \pi p } { n } ) ( \beta _ { - p } ^ { \dagger } \beta _ { p } ^ { \dagger } - \beta _ { p } \beta _ { - p } ) ) ] } \\ & { \equiv \sum _ { p = 1 , 3 , \dots } A _ { p } ( s ) } \end{array}
$$

Now that $H ( s )$ has finally been written as sum of commuting operators $\left( \left[ A _ { p } , A _ { p ^ { \prime } } \right] \right. = \left. 0 \right.$ for $p \neq p ^ { \prime }$ ), we can diagonalize each summand separately. For a given $p$ , let us denote by $| \Omega _ { p } \rangle$ the state that is annihilated by $\beta _ { p }$ and $\beta _ { - p }$ , i.e., $\beta _ { p } | \Omega _ { p } \rangle \ = \ \beta _ { - p } | \Omega _ { p } \rangle \ = \ 0$ . Note that $A _ { p } ( s = 0 ) | \Omega _ { p } \rangle = 0$ , so $| \Omega _ { p } \rangle$ is the ground state of $A _ { p }$ at $s = 0$ (recall that we already knew that the ground state energy at $s = 0$ was zero). Let $| \Sigma _ { p } \rangle = \beta _ { - p } ^ { \dagger } \beta _ { p } ^ { \dagger } | \Omega _ { p } \rangle$ . $A _ { p } ( s )$ keeps states in the subspace spanned by $| \Omega _ { p } \rangle$ and $\left| \Sigma _ { p } \right.$ in the same subspace; the initial state is in this subspace, so we can restrict our attention to it. Let us write $A _ { p } ( s )$ in the $\{ | \Omega _ { p } \rangle , | \Sigma _ { p } \rangle \}$ basis:

$$
A _ { p } ( s ) = \left( \begin{array} { c c } { { s + s \cos \left( \frac { \pi p } { n } \right) } } & { { i s \sin \left( \frac { \pi p } { n } \right) } } \\ { { - i s \sin \left( \frac { \pi p } { n } \right) } } & { { 4 - 3 s - s \cos \left( \frac { \pi p } { n } \right) } } \end{array} \right) \ .
$$

Diagonalizing this, we find for the energies:

$$
E _ { p } ^ { \pm } ( s ) = 2 { - } s { \pm } \Big [ ( 2 - 3 s ) ^ { 2 } + 4 s ( 1 - s ) ( 1 - \cos \Big ( { \frac { \pi p } { n } } \Big ) \Big ] ^ { 1 / 2 } \ .
$$

The instantaneous ground state energy of $H ( s )$ is thus given by $\scriptstyle \sum _ { p = 1 , 3 , \ldots } E _ { p } ^ { - } ( s )$ . The first excited state energy is given by $\begin{array} { r } { E _ { 1 } ^ { + } ( s ) + \sum _ { p = 3 , . . . } E _ { p } ^ { - } ( s ) } \end{array}$ . The energy gap $\Delta ( s )$ is therefore given by:

$$
\begin{array} { l } { { \Delta ( s ) = E _ { 1 } ^ { + } ( s ) - E _ { 1 } ^ { - } ( s ) \qquad \mathrm { ( 1 2 ~ } } } \\ { { \qquad = 2 \left[ \mathrm { ( 2 - 3 } s ) ^ { 2 } + 4 s \mathrm { ( 1 - } s ) \mathrm { ( 1 - } \cos \left( \displaystyle \frac { \pi p } { n } \right) \right] ^ { 1 / 2 } \ . } } \end{array}
$$

The minimum occurs at $\begin{array} { r } { s ^ { * } = \frac { 2 \left( 2 + \cos \frac { \pi } { n } \right) } { 5 + 4 \cos \frac { \pi } { n } } \to 2 / 3 } \end{array}$ as $n $ $\infty$ . Therefore, the minimum gap is given by:

$$
\Delta ( s ^ { * } ) = 4 \left| \sin \frac { \pi } { n } \right| \frac { 1 } { \sqrt { 5 + 4 \cos \frac { \pi } { n } } } \to \frac { 4 \pi } { 3 n } ~ ,
$$

which implies a polynomial run time for the adiabatic algorithm. As mentioned, the classical computational cost of finding a satisfying assignment is at most $n$ . Therefore, despite the polynomially small gap in this example, there is no quantum speedup. This illustrates that a StoqAQC slowdown need not necessarily be associated with an exponentially small gap.

# 3. Weighted 2-SAT on a chain with periodicity

We now discuss another problem, proposed in (Reichardt, 2004), that combines 2-SAT with an exponential slowdown of StoqAQC. It can thus be viewed as exhibiting aspects of the two previous problems we discussed.

Consider a weighted 2-SAT problem on a chain with “agree” clauses between bits $i , i + 1$ for $i = 1 , \ldots , N - 1$ with weights:

$$
J _ { i } = \left\{ \begin{array} { l l } { w \mathrm { i f } \lceil \frac { i } { n } \rceil \mathrm { i s o d d , } } \\ { 1 \mathrm { i f } \lceil \frac { \ i } { n } \rceil \mathrm { i s e v e n } } \end{array} \right.
$$

where $n$ is the period and $w > 1$ . As for the previous 2-SAT problem, we can map this to a spin-chain with ferromagnetic couplings with strength given by $J _ { i }$ . The adiabatic Hamiltonian is given by:

$$
H ( s ) = - ( 1 - s ) \sum _ { i = 1 } ^ { N } \sigma _ { i } ^ { x } - s \sum _ { i = 1 } ^ { N - 1 } J _ { i } \sigma _ { i } ^ { z } \sigma _ { i + 1 } ^ { z } ~ .
$$

This chain has coefficients that alternate between $w$ and $1$ in sectors of size $n$ each, with the $b + 1$ odd-numbered sectors being “heavy” ( $J _ { i } = w > 1$ ), $b$ even-numbered sectors being “light” ( $J _ { i } = 1$ ), and where the total number of sectors is $( N - 1 ) / n = 2 b + 1$ . Since the chain is ferromagnetic, the ground state of $H ( 1 )$ is trivially the all-0 or all-1 computational-basis state. The problem is thus classically easy and can be solved by inspection or in time $O ( N )$ by a heuristic classical algorithm such as simulated annealing, by simply traversing the chain and updating one spin at a time.

Note that at $s \ = \ 0$ there is a unique ground state, while as we just noted, at $s = 1$ the ground state is doubly degenerate. Therefore, the relevant quantum ground state gap $\Delta$ is not the gap to the first excited state (since at the end of the evolution, this merges with the ground state), but to the second excited state.

It turns out this gap is exponentially small in the sector size $n$ across a constant range $s \in ( 1 / ( 1 + \underline { { w } } ) , 1 / 2 )$ . Moreover, there are exponentially many (in $\sqrt { N }$ ) exponentially small excitations above the ground state for $n \sim \sqrt { N }$ .

More precisely, let $\mu _ { w } = s w / ( 1 - s )$ . Theorem 4 in (Reichardt, 2004) states that:

1. For any fixed $s > 1 / ( 1 + w )$ , i.e., $\mu _ { w } < 1$ , $H ( s )$ has one eigenvalue only $O ( \mu _ { w } ^ { n } )$ above the ground state energy. This means that the gap $\Delta$ is exponentially decreasing with the sector size $n$ .   
2. For $s \in ( 1 / ( 1 + w ) , 1 / ( 1 + \sqrt { w } ) ]$ (i.e., again $\mu _ { w } < 1$ ), $H ( s )$ has $2 ^ { b + 1 } - 1$ eigenvalues only $O ( b \mu _ { w } ^ { n } )$ above the ground state energy. This means that there are exponentially many (in the number of odd sectors $b + 1$ ) excited states, that likewise have an exponentially small (in $n$ ) gap from the ground state. Note that $b = [ ( N - 1 ) / n + 1 ] / 2$ , so $b \sim \sqrt { N }$ when $n \sim \sqrt { N }$ .   
3. For $s \in [ 1 / ( 1 + \sqrt { w } ) , 1 / 2 )$ , where $\mu _ { 1 } = s / ( 1 - s ) > 1$ , $H ( s )$ has $2 ^ { b + 1 } - 1$ eigenvalues $O ( b \mu _ { 1 } ^ { - n } )$ above the ground state energy. This again means an exponentially large number (in $b$ ) of excited states with an exponentially small (in $n$ ) gap.

The proof uses a Jordan-Wigner transformation to diagonalize $H ( s )$ , similarly to the technique in Sec. VI.D.2. The spectral gaps of the $2 ^ { N } \times 2 ^ { N }$ matrix $H ( s )$ are the square roots of the eigenvalues of an $N \times N$ symmetric, tridiagonal matrix. The Sturm sequence of the principal leading minors of this matrix is then analyzed to bound the eigenvalue gaps of $H ( s )$ .

Why might we expect this problem to be hard for the adiabatic algorithm? Within any given light or heavy sector, the problem (at fixed $s$ ) is that of a uniform transverse field Ising chain. Consider the thermodynamic limit $N \gg 1$ , and also let $n \gg 1$ . In this limit the transverse field Ising chain encounters a phase transition separating the disordered phase and the ordered phase when $1 - s = s J _ { i }$ (Sachdev, 2001), i.e., at $s = 1 / ( 1 + J _ { i } )$ . (The boundary of the chain only adds $O ( 1 )$ energy, so it does not impact this intuitive argument in the thermodynamic limit.) This means that the heavy sectors encounter the phase transition at s = 11+w whereas the light sectors encounter the phase transition at $s = 1 / 2$ , i.e., the light sectors order after the heavy ones. At s = 11+w each heavy sector orders in either the all-0 or all-1 state, and different heavy sectors are separated by light sectors that have not ordered yet. Since the initial Hamiltonian generates only local spin flips, the algorithm is likely to get stuck in a local minimum with a domain wall in one or more disordered sectors, if run for less than exponential time in $n$ . This mechanism in which large local regions order before the whole is well-known in disordered, geometrically local optimization problems, giving rise to a Griffiths phase (Fisher, 1995).

# 4. Topological slowdown in a dimer model or local Ising ladder

Another interesting example of a local spin model that leads StoqAQC astray was given in (Laumann et al., 2012). They showed that a translation invariant quasi-1D transverse field Ising model with nearest-neighbor interactions only, the ground state of which is readily found by inspection, results in exponentially long run times for StoqAQC. The model can be understood as either a dimer model on a two-leg ladder of even length $L$ , or, using a duality transformation, a two-leg frustrated Ising ladder of the same length in a uniform magnetic field, the ground states of which map onto the dimer states. The frustrated Ising ladder Hamiltonian is:

$$
H _ { 1 } = - \sum _ { \langle i , j \rangle } J _ { i j } \sigma _ { i } ^ { z } \sigma _ { j } ^ { z } - K \sum _ { i \in \mathrm { ~ u p p e r } } \sigma _ { i } ^ { z } + \frac { 1 } { 2 } U \sum _ { i \in \mathrm { ~ l o w e r } } \sigma _ { i } ^ { z } \ ,
$$

where upper and lower refer to the legs of the ladder, $J _ { i j } = - K$ for the upper-leg couplings and $J _ { i j } = K$ for all other (lower-leg and rungs) couplings.

Quantum dynamics is introduced via a standard initial Hamiltonian $- \Gamma ( t ) \sum _ { i } \sigma _ { i } ^ { x }$ , where $\Gamma ( 0 ) \gg \| H _ { 1 } \|$ and $\Gamma ( t _ { f } ) = 0$ . The dimer model exhibits a first order quantum phase transition with an exponentially small gap when $K \gg U$ , which is inherited by the frustrated Ising ladder model. Namely, the system prefers the sector with exponentially many ground states, while any degeneracylifting interaction favors another containing only $O ( 1 )$ states. StoqAQC selects the wrong sector, tunneling out of which becomes exponentially slow as $\Gamma$ is reduced.

More specifically, for $K \ \gg \ U$ , the Hilbert space is spanned by an orthonormal basis of hardcore dimer coverings (“perfect matchings”) of the ladder. These fall into three sectors which are topological in that they are not connected by any local rearrangement of the dimers. The sectors are labeled by a winding number $w$ , the difference between the number of dimers on the top and bottom rows (on any fixed plaquette). The model assigns extensive energy $\propto L$ to every state in the $w = 0$ sector while leaving the two staggered states $w = \pm 1$ as ground states with energy 0. On the other hand, at large $\Gamma$ (strong transverse field) the $w = 0$ sector is favored. Intuitively, slowly turning the transverse field off by reducing $\Gamma$ does not help change the topological sector since any off-diagonal term in the dimer Hilbert space involving only a finite number of rungs in the ladder leaves the winding number $w$ invariant. This is depicted in Fig. 5. Numerical analysis of the Ising ladder confirms this picture by revealing that the gap is exponentially small in $L$ when $K > U$ . The critical point is found to be at $\Gamma _ { c } \approx U / b + U ^ { 2 } / ( 4 K b ^ { 3 } )$ , where $b \approx 0 . 6$ (from exact diagonalization numerics).

![](images/32796ca68b285057dc96276202fe16020eb9b4114fdbc17baecc48d1d45a66d4.jpg)  
FIG. 5 Energy spectrum of the dimer model on an even length periodic ladder, with the dimer configurations illustrated. The $w = \pm 1$ states are at energy $E = 0$ , while the $w = 0$ sector splits into a band for $\Gamma > 0$ . For sufficiently large $\Gamma$ , the $w = 0$ sector contains the ground state of the system. An unavoided level crossing (first order quantum phase transition) occurs at $\Gamma = \Gamma _ { c }$ , which is responsible for the quantum slowdown. From (Laumann et al., 2012).

# 5. Ferromagnetic Mean-field Models

The quantum ferromagnetic $p$ -spin model is given by:

$$
H = - \frac { 1 } { n ^ { p - 1 } } \left( \sum _ { i = 1 } ^ { n } \sigma _ { i } ^ { z } \right) ^ { p } - \Gamma \sum _ { i = 1 } ^ { n } \sigma _ { i } ^ { x } \ .
$$

By inspection it is clear that when $p$ is even, the ground state at $\Gamma = 0$ is either of the two fully-aligned ferromagnetic states, while when $p$ is odd, the unique ground state at $\Gamma = 0$ is the fully-aligned spin-down state. As $\Gamma$ is tuned from a large value towards zero, the system encounters a first-order phase transition for $p > 2$ . This can be readily shown by employing the Suzuki-Trotter decomposition and the static approximation (Chayes et al., 2008; J¨org et al., 2010a; Krzakala et al., 2008; Suzuki et al., 2013) to calculate the partition function $Z$ in the large $n$ limit, where

$$
Z = \int d m ~ e ^ { - \beta n F ( \beta , \Gamma , m ) } ~ .
$$

Here $\beta$ is the inverse temperature, $m$ is the Hubbard-Stratonovich field (Hubbard, 1959), and $F$ is the free

energy density given by:

$$
F = ( p - 1 ) m ^ { p } - \frac { 1 } { \beta } \log \left[ 2 \cosh \left( \beta \sqrt { \Gamma ^ { 2 } + p ^ { 2 } m ^ { 2 p - 2 } } \right) \right] \ .
$$

The dominant contribution to $F ^ { \prime }$ comes from the saddlepoint of the partition function $Z$ , which provide consistency equations for the field $m$ :

$$
m = p m ^ { p - 1 } \frac { \operatorname { t a n h } \left( \beta \sqrt { \Gamma ^ { 2 } + p ^ { 2 } m ^ { 2 ( p - 1 ) } } \right) } { \sqrt { \Gamma ^ { 2 } + p ^ { 2 } m ^ { 2 ( p - 1 ) } } } \ .
$$

Solving this equation numerically for $p > 2$ reveals a discontinuity in the value of $m$ that minimizes the free energy as $\Gamma$ is tuned through the phase transition point. At this critical point, the free energy exhibits a degenerate double-well potential, and an instantonic calculation on this potential gives an exponentially small energy gap with system size (J¨org et al., 2010a).

# 6. 3-Regular 3-XORSAT

All the problems we discussed so far were amenable to a classical solution “by inspection” (i.e., the solution is obvious from the form of the cost function). Some problems were even easy for classical heuristic algorithms performing local search. We now discuss a problem that is non-trivial in this respect, i.e., classically only yields in polynomial time to a tailored approach.

In 3-XORSAT, each clause involves three bits, and there are $M$ clauses and $n$ bits in total. A clause is satisfied if the sum of the three bits (mod 2) is a specified value; it can be 0 or 1 depending on the clause. For 3- regular 3-XORSAT, every bit is in exactly three clauses and $M = n$ . This problem is associated with a spin glass phase but is “glassy without being hard to solve” (Franz et al., 2001; Ricci-Tersenghi, 2010): the problem of finding a satisfying assignment can be solved in polynomial time using Gaussian elimination because the problem involves only linear constraints (mod 2) (Haanpaa et al., 2006).

A final Hamiltonian involving $n$ spins can be be written such that each satisfied clause gives energy $0$ and each unsatisfied clause gives energy 1:

$$
H _ { 1 } = \sum _ { c = 1 } ^ { n } \left( \frac { \mathbb { 1 } - J _ { c } \sigma _ { i _ { 1 } , c } ^ { z } \sigma _ { i _ { 2 } , c } ^ { z } \sigma _ { i _ { 3 } , c } ^ { z } } { 2 } \right) \ .
$$

Here the index $( i _ { k } , c )$ denotes the three bits associated with clause $c$ , and $J _ { c } \in \{ \pm 1 \}$ depending on whether the clause is satisfied if the sum of its bits (mod 2) is $0$ or 1. The StoqAQC Hamiltonian is then given, as usual, by $\begin{array} { r } { H ( s ) = - ( 1 - s ) \sum _ { i = 1 } ^ { n } \sigma _ { i } ^ { x } + s H _ { 1 } } \end{array}$ . The median minimum gap for random 3-regular 3-XORSAT has numerically been shown to be exponentially small in the system size up to $n = 2 4$ (J¨org et al., 2010b) and $n = 4 0$ (Farhi et al.,

2012) [both using the quantum cavity method (Krzakala et al., 2008; Laumann et al., 2008) and QMC simulations], with a first order quantum phase transition at $s = 1 / 2$ . Thus, the numerical evidence suggests that StoqAQC takes exponential time to solve this problem. The same is true for classical heuristic local search algorithms such as WalkSAT (Guidetti and Young, 2011).

We note that since the Hamiltonian gap is not a thermodynamic quantity, one must be careful not to automatically associate a first order quantum phase transition with an exponentially small gap. While the examples presented in this review agree with this rule [for additional examples see (Bapst and Semerjian, 2012; Dusuel and Vidal, 2005; J¨org et al., 2008, 2010a; Knysh and Smelyanskiy, 2006)], counterexamples wherein a first order quantum phase transition is associated with a polynomially small gap are known (Cabrera and Jullien, 1987; Laumann et al., 2012, 2015; Tsuda et al., 2013).

# 7. Sherrington-Kirkpatrick and Two-Pattern Gaussian Hopfield Models

The Sherrington-Kirkpatrick (SK) model, the prototypical spin glass model, is NP-hard, yet its quantum transverse field Ising model version (Das et al., 2005; Ishii and Yamamoto, 1985; Ray et al., 1989; Usadel, 1986) exhibits a second order phase transition separating the paramagnetic phase from the spin glass phase (Miller and Huse, 1993; Ye et al., 1993). The model is defined via the final Hamiltonian

$$
H _ { 1 } = \sum _ { i _ { 1 } < i _ { 2 } } J _ { i _ { 1 } i _ { 2 } } \sigma _ { i _ { 1 } } ^ { z } \sigma _ { i _ { 2 } } ^ { z }
$$

where the couplings $J _ { i _ { 1 } i _ { 2 } }$ are zero-mean, independent and identically distributed random variables (e.g., Gaussian, or bimodal, i.e., $J _ { i _ { 1 } i _ { 2 } } = \pm 1$ ) and every spin is coupled to every other spin. The adiabatic computation proceeds via

$$
H ( t ) = H _ { 1 } - \Gamma ( t ) \sum _ { i = 1 } ^ { n } \sigma _ { i } ^ { x } \ ,
$$

where $\Gamma$ is adiabatically reduced to zero.

The polynomial closing of the gap at this phase transition appears promising for AQC. However, a spin glass is dominated by a rough free energy landscape with many local minima forming bottlenecks for classical heuristic local-search algorithms (M. Mezard, G. Parisi and M.A. Virasoro, 1987; Nishimori, 2001).

To gain insight into this phenomenon, and in particular its impact on StoqAQC, (Knysh, 2016) studied another fully connected model with a vanishing classical gap: the Gaussian Hopfield model, defined generally via

$$
J _ { i _ { 1 } i _ { 2 } \cdots i _ { p } } = { \frac { 1 } { n ^ { p - 1 } } } \sum _ { \mu = 1 } ^ { r } \xi _ { i _ { 1 } } ^ { ( \mu ) } \cdot \cdot \cdot \xi _ { i _ { p } } ^ { ( \mu ) }
$$

(Hebb rule), where $\xi _ { i } ^ { ( \mu ) }$ are zero-mean i.i.d. random variables of unit variance. By focusing on the analytically more tractable Hopfield model, (Knysh, 2016) rigorously analyzed for $r \ = \ 2$ (the two-pattern case) and $p \ : = \ : 2$ (two-local interactions) the properties of local minima away from the global minimum.

The main insight gained from the theoretical analysis of (Knysh, 2016) is that the complexity of the model is not determined by the phase transition, but rather by the existence of small-gap bottlenecks in the spin glass phase. Namely, after the occurrence of the polynomially closing gap associated with the second order phase transition separating the paramagnetic and glass phases, there are $O ( \log n )$ additional gap minima in the spin glass phase appearing in an approximate geometric progression, a phenomenon that can be attributed to the self-similar properties of the free energy landscape in a $\Gamma$ interval bounded by the appearance of the spin-glass phase. At these bottlenecks, the gaps scale as a stretched exponential e−cΓ3/4m n3/4 , where $\Gamma _ { m }$ is the location of the $m$ -th minimum. This is illustrated in Fig. 6. Nevertheless this means that StoqAQC suffers a (stretched) exponential slowdown, since the two pattern Gaussian Hopfield model admits an efficient classical solution based on angle sorting and exhaustive search, that scales as $O [ n \log ( n ) ]$ (Knysh, 2016). Thus, this is another case where a StoqAQC algorithm is too generic to exploit problem structure, and consequently a tailored classical algorithm has exponentially better scaling.

![](images/559d2598ae4b29ca2a631c9048cf4cdf0782e7fea32ab57aed665c7848ce7e6e.jpg)  
FIG. 6 Illustration showing the gap behavior in the $r = 2$ , $p = 2$ Gaussian Hopfield model. The paramagetic-spin-glass transition occurs at $\Gamma _ { c }$ , with $\Gamma < \Gamma _ { c }$ denoting the spin-glass phase. The typical gap is denoted using big-O notation. The spin-glass phase contains $\log n$ additional minima in the gap (indicated by red arrows). $\Gamma _ { \mathrm { m i n } }$ corresponds to the lowest energy scale of the classical Hamiltonian, which in this case scales as $1 / N$ , where $N$ was used to represent the variable we denote by $n$ . From (Knysh, 2016).

# E. StoqAQC algorithms with a scaling advantage over simulated annealing

A substantial effort is underway to develop problems that may exhibit any form of a quantum speedup (recall the classification given in Sec. III). One approach has been to develop “tunneling gadgets”, i.e., small toy Hamiltonians that exhibit tunneling (Boixo et al., 2016), and use these gadgets to construct larger problems (Denchev et al., 2016). An alternative approach has been to develop instances that are believed to exhibit “small-and-thin” energy barriers in their classical energy landscape (Katzgraber et al., 2015) in the hope that such barriers persist in the quantum energy landscape where tunneling occurs. These approaches have been used primarily to assess the performance of the D-Wave devices and are based on numerical analysis, which makes extrapolation and conclusions about asymptotic scaling rather challenging (Brady and Dam, 2016; Mandr\`a et al., 2016).

In this subsection we consider several examples of StoqAQC with a demonstrable quantum scaling advantage over simulated annealing (SA). While none of the examples are demonstrations of an unqualified quantum speedup, these examples are illustrative in that they reveal important qualitative differences between SA, where thermal fluctuations are used to explore the energy landscape, and StoqAQC, where quantum fluctuations are used to explore a different energy landscape. Still, these results are based on a comparison with SA that uses only single-spin updates. SA-like algorithms with cluster-spin updates can be significantly more efficient (Houdayer, J., 2001; Mandr\`a et al., 2016; Swendsen and Wang, 1987; Wolff, 1989; Zhu et al., 2015; Zintchenko et al., 2015), and their performance relative to StoqAQC is largely an open question. The same is true for parallel tempering (aka exchange Monte Carlo) (Earl and Deem, 2005; Hukushima and Nemoto, 1996; Katzgraber et al., 2006; Marinari and Parisi, 1992; Swendsen and Wang, 1986).

# 1. Spike-like Perturbed Hamming Weight Problems

We start with a problem for which there is no (limited) quantum speedup, in order to set up the more interesting problems that follow. Consider a cost function $f ( x )$ to be minimized with $x \in \{ 0 , 1 \} ^ { n }$ an $n$ -bit string. The final Hamiltonian can generically be written as:

$$
H _ { 1 } = \sum _ { x } f ( x ) | x \rangle \langle x | ~ .
$$

We first consider the cost function of the “plain” Hamming weight problem:

$$
f ( x ) = \left| x \right|
$$

where $| x |$ denotes the Hamming weight of the $n$ -bit string $x$ [as in Eq. (109)]. This problem is equivalent to a system of $n$ non-interacting spins in a global (longitudinal) field, which is of course a trivial problem that can be solved in time $O ( 1 )$ , e.g., by parallelized SA running with a a single thread for each spin. The scaling of the time needed by the quantum algorithm is $O ( n ^ { 1 / 2 } )$ , and the full cost of the quantum algorithm is $O ( n ^ { 3 / 2 } )$ according to Eq. (1), since it requires $O ( n )$ single-qubit terms in the Hamiltonian. A fairer comparison is to an SA algorithm that is ignorant of the structure of the problem. In this case one can show that the cost for single-spin update SA with random spin selection is lower bounded by ${ \mathcal { O } } ( n \log n )$ (Muthukrishnan et al., 2016).

Next we consider a more interesting problem, referred to as the “spike”, first studied in (Farhi et al., 2002a). The cost function is given by:

$$
f ( x ) = { \left\{ \begin{array} { l l } { n } & { { \mathrm { i f ~ } } | x | = n / 4 } \\ { | x | } & { { \mathrm { o t h e r w i s e } } } \end{array} \right. }
$$

Since the barrier scales with $n$ , we can expect that singlespin-update SA will take $\exp ( n )$ time to traverse the barrier. However, it can be shown that the quantum gap scales as $\Omega ( n ^ { - 1 / 2 } )$ (Farhi et al., 2002a; Kong and Crosson, 2015), so the adiabatic algorithm only takes polynomial time.

This type of “perturbed” Hamming weight problem can be generalized, while still retaining an advantage over single-spin-update SA. For cost functions of the form

$$
f ( x ) = { \left\{ \begin{array} { l l } { | x | + h ( n ) { \mathrm { ~ i f ~ } } l ( n ) < | x | < u ( n ) } \\ { | x | } & { { \mathrm { o t h e r w i s e } } } \end{array} \right. }
$$

satisfying $h [ ( u - l ) / \sqrt { l } ] = o ( 1 )$ , the minimum gap of the quantum algorithm is lower bounded by a constant (Reichardt, 2004) [see Appendix A of Ref. (Muthukrishnan et al., 2016) for a pedagogical review of the proof]. The SA run time, on the other hand, scales exponentially in $\operatorname* { m a x } _ { n } h ( n )$ .

Similarly, consider barriers with width proportional to $n ^ { \alpha }$ and height proportional to $n ^ { \beta }$ , i.e.

$$
f ( x ) = { \left\{ \begin{array} { l l } { \left| x \right| + n ^ { \alpha } { \mathrm { ~ i f ~ } } { \frac { n } { 4 } } - { \frac { 1 } { 2 } } n ^ { \beta } < \left| x \right| < { \frac { n } { 4 } } + { \frac { 1 } { 2 } } n ^ { \beta } } \\ { \left| x \right| } & { { \mathrm { o t h e r w i s e } } } \end{array} \right. } .
$$

When $\alpha$ and $\beta$ satisfy $\alpha + \beta \geq 1 / 2$ , $\alpha < 1 / 2$ , and $2 \alpha +$ $\beta \leq 1$ , the minimum gap scales polynomially as $n ^ { 1 / 2 - \alpha - \beta }$ (Brady and van Dam, 2016a,b), while the SA run time scales exponentially in $n ^ { \alpha }$ .

# 2. Large plateaus

The above examples have relied on energy barriers in the classical cost that scale with problem size to foil single-spin-update SA. This agrees with the intuition that a StoqAQC advantage over SA is associated with tall and thin barriers (Das and Chakrabarti, 2008; Ray et al., 1989). However, somewhat counterintuitively, it is also possible to foil SA by having very large plateaus in the classical cost function. Specifically, consider:

$$
f ( x ) = { \left\{ \begin{array} { l l } { u - 1 } & { { \mathrm { i f ~ } } l < | x | < u } \\ { | x | } & { { \mathrm { o t h e r w i s e } } } \end{array} \right. }
$$

where $l , u = \mathcal { O } ( 1 )$ [a special case of Eq. (148)]. SA with single-spin-updates and random spin selection has run time $O ( n ^ { u - l - 1 } )$ , where $u - l - 1$ is the plateau width (Muthukrishnan et al., 2016). This polynomial scaling arises because the energy landscape provides no preferred direction and SA then behaves as a random walker on the plateau. Numerical diagonalization shows that the quantum minimum gap is constant and the adiabatic run time is only $O ( n ^ { 1 / 2 } )$ , where the scaling with $n$ arises from the numerator of the adiabatic condition (Muthukrishnan et al., 2016). Thus StoqAQC has a polynomial scaling advantage over SA in this case.

A natural question is whether these potential quantum speedup results for StoqAQC relative to SA survive when other algorithms are considered. The answer is negative. (Muthukrishnan et al., 2016) showed that a diabatic evolution is more efficient than the adiabatic evolution to solve these problems, and a similar efficiency is achieved using classical spin-vector dynamics. There is also a growing body of numerical (Brady and van Dam, 2016a; Crosson and Deng, 2014; Denchev et al., 2016; Muthukrishnan et al., 2016) and analytical (Crosson and Harrow, 2016; Isakov et al., 2016) research that shows that quantum Monte Carlo methods exhibit similar or even identical advantages over SA for many spike-like perturbed Hamming weight problems.

# F. StoqAQC algorithms with undetermined speedup

In this subsection we focus on examples where it is currently unknown whether there is a quantum speedup or slowdown for StoqAQC.

# 1. Number partitioning

The number partitioning problem is a canonical NPcomplete problem (M.R. Garey and D.S. Johnson, 1979) that is defined as follows: given a set of $n$ positive numbers $\{ a _ { i } \} _ { i = 1 } ^ { n }$ , the objective is to find a partition $\mathcal { P }$ of this set that minimizes the partition residue $E$ defined as:

$$
E = \left| \sum _ { j \in \mathcal { P } } a _ { j } - \sum _ { j \notin \mathcal { P } } a _ { j } \right| \ .
$$

The problem exhibits an easy-hard phase transition at the critical value $b / n \ = \ 1$ , where $b$ is the number of bits used to represent the set $\left\{ { { a } _ { i } } \right\}$ (Borgs et al., 2001; Mertens, 1998). In the hard phase it roughly corresponds to finding the minimum in a set of $2 ^ { n }$ numbers (Mertens, 2001). To translate it into Ising spin variables let $s _ { j } = 1$ when $j \in \mathcal { P }$ and $s _ { j } = - 1$ otherwise, so that

$$
E = \left| \sum _ { j = 1 } ^ { n } a _ { j } s _ { j } \right| \ ,
$$

which can then be turned into a Mattis-like Ising Hamiltonian whose ground state is the minimizing partition:

$$
H _ { 1 } = \sum _ { i , j = 1 } ^ { n } a _ { i } a _ { j } s _ { i } s _ { j } \ .
$$

The energy landscape of this final Hamiltonian is known to be extremely rugged in the hard phase (Smelyanskiy et al., 2002; Stadler et al., 2003), and the asymptotic behavior can already be seen for small sizes $n$ . While SA effectively requires the searching of all possible bit configurations with a run time $\propto 2 ^ { 0 . 9 8 n }$ (Stadler et al., 2003), numerical simulations of StoqAQC exhibit a slightly better run time $\propto 2 ^ { 0 . 8 n }$ (Denchev et al., 2016). State-of-theart classical algorithms have scalings as low as $2 ^ { 0 . 2 9 1 n }$ (Becker et al., 2011).

It should be noted that number partitioning is known as the “easiest hard problem” (Hayes, 2002) due to the existence of efficient approximation algorithms that apply in most (though of course not all) cases, e.g., a polynomial time approximation algorithm known as the differencing method (Karmarkar and Karp, 1982). It should further be noted that if all the $a _ { j }$ ’s are bounded by a polynomial in $n$ , then integer partitioning can be solved in polynomial time by dynamic programming (Mertens, 2003). The NP-hardness of the number partitioning problem requires input numbers of size exponentially large in $n$ or, after division by the maximal input number, of exponentially high precision. This is problematic since the $\{ a _ { j } \}$ are used as coupling coefficients in the adiabatic Hamiltonian (153), and suggests that a different encoding will be needed in order to allow AQC to meaningfully address number partitioning.

# 2. Exact Cover and its generalizations

We briefly review the adiabatic algorithm for Exact Cover, which initiated and sparked the tremendous interest in the power of AQC when it was first studied in (Farhi et al., 2001). While the optimistic claim made in that paper, that “the quantum adiabatic algorithm worked well, providing evidence that quantum computers (if large ones can be built) may be able to outperform ordinary computers on hard sets of instances of NP-complete problems” turned out to be premature, the historical impact of this study was large, and it led to the avalanche of work that forms the core of this review.

The Exact Cover 3 (EC3) problem is an NP-complete problem that is a particular formulation of 3-SAT [recall Sec. V.A] whereby each clause $C$ (composed of three bits $x _ { C _ { 1 } } , x _ { C _ { 2 } } , x _ { C _ { 3 } }$ that are taken from the set of variables $\{ x _ { i } \in \{ 0 , 1 \} \} _ { i = 1 } ^ { n } )$ is satisfied if $x _ { C _ { 1 } } + x _ { C _ { 2 } } + x _ { C _ { 3 } } = 1$ . There are only three satisfying assignments: (1,0,0), (0,1,0), and (0,0,1). A 3-local Hamiltonian $H _ { C }$ can be associated with each clause, that assigns an energy penalty to the unsatisfying assignments (Farhi et al., 2001; Latorre and Orus, 2004):

$$
\begin{array} { r l r } {  { H _ { C } = \frac { 1 } { 8 } [ ( 1 + \sigma _ { C _ { 1 } } ^ { z } ) ( 1 + \sigma _ { C _ { 2 } } ^ { z } ) ( 1 + \sigma _ { C _ { 3 } } ^ { z } )  } } \\ & { } & {  + ( 1 - \sigma _ { C _ { 1 } } ^ { z } ) ( 1 - \sigma _ { C _ { 2 } } ^ { z } ) ( 1 - \sigma _ { C _ { 3 } } ^ { z } )  } \\ & { } & {  + ( 1 - \sigma _ { C _ { 1 } } ^ { z } ) ( 1 - \sigma _ { C _ { 2 } } ^ { z } ) ( 1 + \sigma _ { C _ { 3 } } ^ { z } )  } \\ & { } & {  + ( 1 - \sigma _ { C _ { 1 } } ^ { z } ) ( 1 + \sigma _ { C _ { 2 } } ^ { z } ) ( 1 - \sigma _ { C _ { 3 } } ^ { z } )  } \\ & { } & {  + ( 1 + \sigma _ { C _ { 1 } } ^ { z } ) ( 1 - \sigma _ { C _ { 2 } } ^ { z } ) ( 1 - \sigma _ { C _ { 3 } } ^ { z } ) ] \ . } \end{array}
$$

A 2-local alternative is (Young et al., 2010):

$$
H _ { C } = \frac { 1 } { 4 } \left( \sigma _ { C _ { 1 } } ^ { z } + \sigma _ { C _ { 2 } } ^ { z } + \sigma _ { C _ { 3 } } ^ { z } - 1 \right) ^ { 2 } \ .
$$

The final Hamiltonian is then given by $\begin{array} { r } { H _ { 1 } = \sum _ { C } H _ { \mathrm C } } \end{array}$ . If the ground state energy is $0$ , then an assignment exists that satisfies all clauses. The adiabatic algorithm is given as usual by $\begin{array} { r } { H _ { 0 } = \sum _ { i = 1 } ^ { n } \frac { 1 } { 2 } \left( 1 - \sigma _ { i } ^ { x } \right) } \end{array}$ . $H ( s ) \ = \ ( 1 - s ) H _ { 0 } + s H _ { 1 }$ , with

For instances with a unique satisfying assignment, while the initial (small $n$ ) scaling of the typical minimum gap (median) is consistent with polynomial (Farhi et al., 2001; Latorre and Orus, 2004), the true (large $n$ ) scaling is exponential and can be associated with a first order phase transition (Young et al., 2008, 2010) occurring at intermediate $s = s _ { c } > 0$ . The fraction of instances with this behavior increases with increasing problem size (Young et al., 2010). This illustrates the perils of extrapolating the asymptotic scaling from studies based on small problem sizes.

A natural generalization of the Exact Cover problem is to have the sum of $K$ variables sum to 1 for a clause to be satisfied, which defines the problem known as “1- in- $K$ SAT”. Another is to have the clause satisfied unless all the variables are equal, which defines the problem “ $K$ -Not-All-Equal-SAT”. Both of these are NP-complete and have been shown analytically to exhibit a first order phase transition for sufficiently large $K$ (Smelyanskiy et al., 2004). Numerical results for locked 1-in-3 SAT and locked 1-in-4 SAT — where “locked’ is the additional requirement that every variable is in at least two clauses and that one cannot get from one satisfying assignment to another by flipping a single variable (Zdeborov´a and M´ezard, 2008a,b) — have been shown to exhibit an exponentially small gap at the satisfiability transition (Hen and Young, 2011).

Since all these problems are NP-complete, there is no polynomial-time classical algorithm known for their worst-case instances. Using StoqAQC has, in all cases that have been studied to date, resulted in exponentially small gaps. Thus, whether these problems can be sped up (even polynomially) is at this time still an open problem.

# 3. 3-Regular MAXCUT

For 3-regular MAXCUT, the problem is to find the assignment that gives the maximum number of satisfied clauses, where each bit appears in exactly three clauses. Each clause involves only two bits and is satisfied if and only if the sum of the two bits (mod 2) is 1. The number of clauses is $M = 3 n / 2$ . The final Hamiltonian can be written as:

$$
H _ { 1 } = \sum _ { c = 1 } ^ { 3 n / 2 } \left( \frac { \mathbb { 1 } + \sigma _ { i _ { 1 } , c } ^ { z } \sigma _ { i _ { 2 } , c } ^ { z } } { 2 } \right) \mathrm { ~ , ~ }
$$

where the index $( i _ { k } , c )$ denotes the two bits associated with clause $c$ . This model can also be viewed as an antiferromagnet on a 3-regular random graph. Because the random graph in general has loops of odd length, it is not possible to satisfy all of the clauses. This problem is NP hard.

For random instances of this problem, where there is a doubly degenerate ground state (the smallest possible because of the $Z _ { 2 }$ symmetry) and with a specified energy of $n / 8$ , the standard adiabatic Hamiltonian $\begin{array} { r } { H ( s ) = - ( 1 - s ) \sum _ { i = 1 } ^ { n } \sigma _ { i } ^ { x } + s H _ { 1 } } \end{array}$ exhibits, for sufficiently large sizes of up to $n = 1 6 0$ , two minima in the energy gap (Farhi et al., 2012) (see Fig. 7 for an example). The first minimum, at $s \approx 0 . 3 6$ , is associated with a secondorder phase transition from paramagnetic to glassy, and the gap closes polynomially with system size. The second minimum occurs inside the spin-glass phase, with a gap that closes exponentially (or possibly a stretched exponential). Therefore, while the first minimum does not pose a problem for the adiabatic algorithm (although it has been shown that the quantum algorithm with a linear interpolating schedule does not pass through the associated glass phase transition faster than SA (Liu et al., 2015)), the second minimum implies an exponential run time.

![](images/081c9d5af4db8eed458f037cdfb8a937f6e5d7f9357d6a4081bb25e5d0c04bce.jpg)  
FIG. 7 The gap to the first even excited state for an instance of size $n = 1 2 8$ , exhibiting two minima. The lower minimum occurs well within the spin-glass phase, while the higher minimum is associated with the second order phase transition. From (Farhi et al., 2012).

# 4. Ramsey numbers

An adiabatic algorithm for the calculation of the Ramsey numbers $R ( k , l )$ was proposed in (Gaitan and Clark, 2012). $R ( k , l )$ is the smallest integer $r$ such that every graph on $r$ or more vertices contains either a $k$ -clique or an $\it l$ -independent set.35 Computing them by brute force is doubly exponential in $N = \operatorname* { m a x } \{ k , l \}$ [note that $R ( k , l ) = R ( l , k ) ]$ using graph coloring techniques, as follows: Try every one of the $2 ^ { N ( N - 1 ) / 2 }$ colorings of the edges of the complete graph $K _ { N }$ with the colors blue and red. For every coloring, check whether or not there is an induced subgraph on $k$ vertices with only blue edges, or an induced subgraph on $\it l$ vertices with only red edges. If every coloring contains at least one of the desired subgraphs, we are done. Otherwise, increment $N$ by $^ { 1 }$ and repeat. Except for certain special values of $k$ and $\it l$ , no better algorithm is currently known.

The idea in (Gaitan and Clark, 2012) is to construct a cost function $h ( G )$ for a graph $G$ where

$$
h ( G ) = { \mathcal { C } } ( G ) + { \mathcal { T } } ( G )
$$

where ${ \mathcal { C } } ( G )$ counts the number of $m$ -cliques in the graph $G$ and ${ \mathcal { T } } ( G )$ counts the number of $\it l$ -independent sets in the graph $G$ . The cost $h ( G )$ equals zero only if there does not exist an $k$ -clique or an $\it l$ -independent set. This will only occur if $R ( k , l ) ~ > ~ N$ . The algorithm then proceeds as follows. By mapping $h ( G )$ over $K _ { N }$ $\begin{array} { r } { H ( s ) = - ( 1 - s ) \sum _ { i = 1 } ^ { n } \sigma _ { i } ^ { x } + s H _ { 1 } } \end{array}$ to a final Hamiltonian $H _ { 1 }$ is performed and the final , the adiabatic algorithm energy of the state is measured. If $h ( G ) = 0$ , then $N$ is incremented by 1 and the experiment is repeated. This process continues until the first occurrence of $h ( G ) > 0$ , in which case $N = R ( k , l )$ . Thus the algorithm is essentially an adiabatic version of the graph coloring method described above. It is unknown whether its StoqAQC version improves upon the classical brute force 2N(N−1)/2 scaling. The adiabatic quantum algorithm was simulated in (Gaitan and Clark, 2012) and shown to correctly determines the Ramsey numbers $R ( 3 , 3 )$ and $R ( 2 , s )$ for $5 \leq s \leq 7$ . It was also shown there that Ramsey number computation is in QMA.

An adiabatic algorithm for generalized Ramsey numbers (where the induced subgraphs are trees rather than complete graphs) was presented in (Ranjbar et al., 2016). Whether this results in a quantum speedup is also unknown. We also remark that Ising formulations for many NP-complete and NP-hard problems, including all of Karp’s 21 NP-complete problems (Karp, 1972), are known (Lucas, 2014), but it is unknown whether they are amenable to a quantum speedup.

# 5. Finding largest cliques in random graphs

The fastest algorithm known to date for the NP-hard problem of finding a largest clique in a graph runs in time $O ( 2 ^ { 0 . 2 4 9 n } )$ for a graph with $n$ vertices (Robson, 2001).36 For random graphs, a super-polynomial time is required to find cliques larger than $\log n$ using the Metropolis algorithm, while the maximum clique is likely to be of size very close to $2 \log n$ (Jerrum, 1992). One of the earliest papers on the quantum adiabatic algorithm was concerned with the largest clique problem for random graphs (Childs et al., 2002), though the algorithm presented there works for general graphs. The results were numerical and showed, by fixing the desired success probability, that the median time required by the adiabatic algorithm to find the largest clique in a random graph are consistent with quadratic growth for graphs of up to 18 vertices. These results on small graphs probably do not capture the asymptotic behavior of the algorithm (the coefficients grow rapidly and have alternating sign), which is likely to be dominated by exponentially small gaps [however, to the extent that these are due to perturbative crossings, they can be avoided by techniques we discuss in Sec. VII.G, in particular as related to the maximum independent set problem (Choi, 2011)].

# 6. Graph isomorphism

In the graph isomorphism problem, two $N$ -vertex graphs $G$ and $G ^ { \prime }$ are given, and the task is to determine whether there exists a permutation of the vertices of $G$ such that it preserves the adjacency and transforms $G$ to $G ^ { \prime }$ , in which case the graphs are said to be isomorphic. If and only if the graphs are isomorphic does there exist a permutation matrix $\sigma$ that satisfies

$$
A ^ { \prime } = \sigma A \sigma ^ { T } \ ,
$$

where $A$ and $A ^ { \prime }$ are the adjacency matrices of $G$ and $G ^ { \prime }$ respectively. An adiabatic algorithm to determine whether a pair of graphs are isomorphic was first proposed in (Hen and Young, 2012), mostly for strongly regular graphs, and generalized to arbitrary graphs in (Gaitan and Clark, 2014), which also showed how to determine the permutation(s) that connect a pair of isomorphic graphs, and the automorphism group of a given graph. The final Hamiltonian formulated in (Gaitan and Clark, 2014) is such that when the ground state energy vanishes the graphs are isomorphic and the bit-string $s = ( s _ { 0 } , \ldots , s _ { N - 1 } )$ associated with the ground state gives an $N \times N$ permutation matrix $\sigma ( s )$ to perform the transformation:

$$
\begin{array} { r } { \sigma ( s ) _ { i j } = \left\{ \begin{array} { l l } { 0 } & { \mathrm { i f } \ s _ { j } > N - 1 } \\ { \delta _ { i , s _ { j } } } & { \mathrm { i f } \ 0 \le s _ { j } \le N - 1 } \end{array} \right. . } \end{array}
$$

The computational complexity of these adiabatic algorithm is currently unknown. However, a recent breakthrough gave a quasipolynomial $( \exp [ ( \log n ) ^ { O ( 1 ) } ] )$ ) time classical algorithm for graph isomorphism (Babai, 2015). It seems unlikely that this can be improved upon by using StoqAQC without deeply exploiting problem structure.

# 7. Machine learning

Quantum machine learning is currently an exciting and rapidly moving frontier in the context of the circuit model (Lloyd et al., 2014; Rebentrost et al., 2014; Wiebe et al., 2014), though it must be evaluated carefully (Aaronson, 2015). One StoqAQC approach is to find a quantum version of the classical method of boosting, wherein multiple weak classifiers (or features) are combined to create a single strong classifier (Freund et al., 1999; Meir, 2003). The task is to find the optimal set of weights of the weak classifiers so as to minimize the training error of the strong classifier on a training data set. After this training step, the strong classifier is then applied to a test data set. This optimization problem can be mapped to a quadratic unconstrained binary optimization (QUBO) problem, which can then be trivially turned into an Ising spin Hamiltonian suitable for adiabatic quantum optimization, where the binary variables represent the weights. This idea was implemented in (Babbush et al., 2014a; Denchev et al., 2012; Neven et al., 2008a, 2009, 2008b; Pudenz and Lidar, 2013), where the ground states found by the adiabatic algorithm encode the solution for the weights.

Another idea is to learn the weights of a Boltzmann machine or, after the introduction of a hidden layer, a reduced Boltzmann machine (Hinton et al., 2006). The latter forms the basis for various modern methods of deep learning. StoqAQC approaches for this problem were developed in (Adachi and Henderson, 2015; Amin et al., 2016; Benedetti et al., 2016)

Neither the classical nor the quantum computational complexity is known in this case, but scaling of the solution time with problem size is not the only relevant criterion: classification accuracy on the test data set is clearly another crucial metric. It is possible, though at this point entirely speculative, that the quantum method will lead to better classification performance. This can come about in the case of ground state degeneracy, if the weights are reconstructed via ground state solutions and if quantum and classical heuristics for solving the QUBO problem find different ground states (Azinovi´c et al., 2016; Mandr\`a et al., 2017; Matsuda et al., 2009; Zhang et al., 2017).

# G. Speedup mechanisms?

While the universality of AQC suggests that similar speedup mechanisms are at play as in the circuit model of quantum computing, the situation is less clear regarding StoqAQC. Here we discuss two potential mechanisms, tunneling and entanglement, that might be thought to endow StoqAQC with an advantage over classical algorithms.

# 1. The role of tunneling

It is often stated that an advantage of StoqAQC over classical heuristic local-search algorithms is that the quantum system has the ability to tunnel through energy barriers, which can provide an advantage over classical algorithms such as simulated annealing that only allow probabilistic hopping over the same barriers. Indeed, such a qualitative picture motivated some of the early research on quantum annealing [e.g., (Finnila et al., 1994)]. However, this statement requires a careful interpretation as it has the potential to be misleading. Whereas only the final cost function — which generates the energy landscape that the classical random walker explores — matters for the classical algorithm, this energy landscape does not become relevant for the quantum evolution until the end. Therefore, tunneling does not occur on the energy landscape defined by the final cost function alone, if it occurs at all. A different notion of tunneling is at work, which we now explain.

The standard notion of tunneling from single-particle quantum mechanics involves a semiclassical potential where classically allowed and classically forbidden regions can be defined. Starting from a many-body Hamiltonian, there is no unique way to take the semiclassical limit. Consider one such limit, based on the spin-coherent path integral formalism (Klauder, 1979):

![](images/cb52274930ba047c44abe48039113fef9c6ff32e74af61a1e58c35c1b7e5dd3b.jpg)  
FIG. 8 Analysis of tunneling in the Grover problem. (a) The semiclassical potential for $n = 2 0$ at different dimensionless times $s$ . The arrows indicate the behavior of the local minima as $s$ increases. There is a discrete jump in the position of the global minimum at $s = 1 / 2$ , where it changes from being at $\theta \approx \pi / 2$ to $\theta \approx 0$ , corresponding to a first order quantum phase transition. (b) The behavior of the potential when the two minima are degenerate at $s = 1 / 2$ . As $_ { n }$ grows, both the barrier height grows (and saturates at 1) and the curvature of the local minima grows. (c) The expectation value of the Hamming Weight operator [defined in Eq. 167] of the instantaneous ground state as $n$ grows. This is to be interpreted as the system requiring $O ( n )$ spins to tunnel in order to follow the instantaneous ground state as the system crosses the minimum gap at $s = 1 / 2$ .

$$
\langle \Omega ( t _ { f } ) | \mathrm { T e x p } [ - i \int _ { 0 } ^ { t _ { f } } d \tau H ( \tau ) ] | \Omega ( 0 ) \rangle = \int { \mathcal { D } } \Omega ( t ) e ^ { { \frac { i } { \hbar } } S [ \Omega ( t ) ] } ,
$$

where the action $S [ \Omega ( t ) ]$ is given by:

$$
S [ \Omega ( t ) ] = \int _ { 0 } ^ { t _ { f } } d t \left( i \hbar \langle \Omega ( t ) | \partial _ { t } | \Omega ( t ) \rangle - \langle \Omega ( t ) | H ( t ) | \Omega ( t ) \rangle \right) \ ,
$$

and

$$
\begin{array} { r l r } {  { | \Omega \rangle \equiv | \theta , \varphi \rangle } } \\ & { } & { \equiv \otimes _ { j = 1 } ^ { n } [ \cos ( \theta _ { j } / 2 ) | 0 \rangle _ { j } + e ^ { i \varphi _ { j } } \sin ( \theta _ { j } / 2 ) | 1 \rangle _ { j } ] ~ . } \end{array}
$$

is the spin-coherent state (Arecchi et al., 1972).

Despite the absence of a true kinetic term, we can identify the semiclassical potential as:

$$
V _ { \mathrm { S C } } ( \{ \theta _ { j } \} , \{ \varphi _ { j } \} , t ) = \langle \Omega | H ( t ) | \Omega \rangle
$$

This form for $V _ { \mathrm { S C } }$ has been used (Boixo et al., 2016; Farhi et al., 2002a; Muthukrishnan et al., 2016; Schaller and Sch¨utzhold, 2010) to capture many of the relevant features of StoqAQC problems endowed with qubitpermutation symmetry; this symmetry often allows for analytical and numerical progress.37

We illustrate this approach with the Grover Hamiltonian [Eq. (16)]. Recall that the final Hamiltonian is $H _ { 1 } = \mathbb { 1 } - | m \rangle \langle m |$ , where $| m \rangle$ is the marked state associated with the marked item. As a cost function, this is the antithesis of the “tall and narrow” potential that is often associated with a classical speedup: $\langle x | H _ { 1 } | x \rangle = 1 - \delta _ { x , m }$ i.e., the potential is flat everywhere, except for a well of constant depth at the marked state. Nevertheless, we now show that following the instantaneous ground state will involve the tunneling of $O ( n )$ qubits.

Without loss of generality we may assume that the “marked” state is the all-zero bit string. Setting $\theta _ { j } \equiv \theta$ and $\varphi _ { j } \equiv \varphi \forall j$ in Eq. (162), the Hamiltonian can be written succinctly as:

$$
\begin{array} { r c l } { { } } & { { } } & { { H ( s ) = ( 1 - s ) \left( 1 1 - | \Omega ( \pi / 2 , 0 ) \rangle \langle \Omega ( \pi / 2 , 0 ) | \right) } } \\ { { } } & { { } } & { { ~ + s \left( 1 - | \Omega ( 0 , 0 ) \rangle \langle \Omega ( 0 , 0 ) | \right) ~ . } } \end{array}
$$

The semiclassical potential for the Grover problem is then:

$$
\begin{array} { l } { { \displaystyle V _ { \mathrm { S C } } ( \theta , 0 ) = ( 1 - s ) \left( 1 - \frac { 1 } { 2 ^ { n } } \left( 1 + \sin \theta \right) ^ { n } \right) } } \\ { { \displaystyle ~ + s \left( 1 - \frac { 1 } { 2 ^ { n } } \left( 1 + \cos \theta \right) ^ { n } \right) ~ . } } \end{array}
$$

The locations of the two degenerate minima at $s = 1 / 2$ are given by the pair of transcendental equation:

$$
{ \begin{array} { r c l } { \displaystyle { \frac { 1 - \cos \theta + \sin \theta } { 1 + \cos \theta - \sin \theta } } = \displaystyle \left( { \frac { 1 + \sin \theta } { 1 + \cos \theta } } \right) ^ { n } ~ , } & \\ { \displaystyle { \frac { 1 + \cos \theta - \sin \theta } { 1 - \cos \theta + \sin \theta } } = \displaystyle \left( { \frac { 1 + \cos \theta } { 1 + \sin \theta } } \right) ^ { n } ~ , } & \end{array} }
$$

which in the limit of $n \to \infty$ have solutions $0$ and $\pi / 2$ respectively. This equation is invariant under $\theta  \pi / 2 - \theta$ , which corresponds to the two minima. Since the semiclassical potential in Eq. (165) at $s = 1 / 2$ is also invariant under $\theta \to \pi / 2 - \theta$ , the local minima have identical structure. Using the Hamming Weight operator defined as:

$$
\mathrm { H W } = \frac { 1 } { 2 } \sum _ { i = 1 } ^ { n } \left( \mathbb { 1 } - \sigma _ { i } ^ { z } \right)
$$

this potential suggests that in the large $n$ limit, we can expect that $n / 2$ spins need to be flipped in order to move from the $\theta \approx \pi / 2$ minimum to the $\theta \approx 0$ minimum, i.e.,

$$
\langle \Omega ( \pi / 2 , 0 ) | \mathrm { H W } | \Omega ( \pi / 2 , 0 ) \rangle - \langle \Omega ( 0 , 0 ) | \mathrm { H W } | \Omega ( 0 , 0 ) \rangle = n / 2 \ .
$$

The instantaneous ground state, as it passes through the minimum gap at $s = 1 / 2$ , indeed exhibits this behavior, as shown in Fig. 8.

However, the more general role of tunneling in providing quantum speedups is not by any means evident. This topic was studied in detail in (Muthukrishnan et al., 2016), which showed that tunneling is neither necessary nor sufficient for speedups in the class of perturbed Hamming weight optimization problems with qubit permutation symmetry.

Our discussion here has been restricted to coherent tunneling, and compelling arguments have been presented in (Andriyash and Amin, 2017; Boixo et al., 2016; Denchev et al., 2016) that incoherent, thermally assisted tunneling plays a computational role in quantum annealing. However, this mechanism is in the open-system setting, which is outside the scope of this review. Moreover, its role in (Boixo et al., 2016; Denchev et al., 2016) is limited to a prefactor, and does not translate into a scaling advantage, i.e., it does not qualify as a speedup according to the classification of (Rønnow et al., 2014).

# 2. The role of entanglement

The role that entanglement plays in quantum computation with pure states in the circuit model depends on the entanglement measure used. On the one hand, it is well known that for any circuit-model quantum algorithm operating on pure states, the presence of multi-partite entanglement quantified via the Schmidt-rank (with a number of parties that increases unboundedly with input size), is necessary if the quantum algorithm is to offer an exponential speedup over classical computation (Jozsa and Linden, 2003). On the other hand, universal quantum computation can be achieved in the standard pure-state circuit model while the entanglement entropy (or any other suitably continuous entanglement measure) of every bipartition is small in each step of the computation (Van den Nest, 2013). The corresponding role of entanglement in the computational efficiency of AQC remains an open question. Partly this is because the connection between entanglement and spectral gaps is not yet very well understood, and partly this is because even if entanglement is present, its computational role in AQC is unclear.

The area law asserts that for any subset $S$ of particles, the entanglement entropy between $S$ and its complement is bounded by the surface area of $S$ rather than the trivial bound of the volume of $S$ . While generic quantum states do not obey an area law (Hayden et al., 2006), and there are 1D systems for which there is exponentially more entanglement than suggested by the area law (Movassagh and Shor, 2016), a sweeping conjecture in condensed matter physics is that in a gapped system the entanglement spreads only over a finite length, which leads to area laws for the entanglement entropy (Eisert et al., 2010). $^ { 3 8 }$ E.g., the area law for gapped 1D systems, proved in (Hastings, 2007), states that for the ground state, the entanglement of any interval is upper bounded by a constant independent of the size of the interval. While this leaves open the question of the general dependence of the upper bound on the spectral gap $\Delta$ , this means that the ground state of such systems is accurately described by polynomialsize matrix product states (MPSs) (Ostlund and Rom-¨ mer, 1995; White, 1992; White and Noack, 1992). In (Gottesman and Hastings, 2010) it was shown that for certain 1D system the entanglement entropy in some regions can be as high as $\mathrm { p o l y } ( 1 / \Delta )$ . This demonstrates that the entanglement entropy can become large as the gap becomes small. Two other important recent results are the existence of a polynomial time algorithm for the ground state of 1D gapped local Hamiltonians with constant ground-state energy (Huang, 2014; Landau et al., 2015), and the fact that 1D quantum many-body states satisfying exponential decay of correlations always fulfill an area law (Brandao and Horodecki, 2013).

However, the connection between entanglement entropy and gaps is not nearly as clear in higher dimensional systems, even though entanglement close to quantum phase transitions is a well developed subject (Amico et al., 2008; Osborne and Nielsen, 2002; Osterloh et al., 2002; Vidal et al., 2003; Wu et al., 2004).

It is not surprising that entanglement is necessary for the computation to succeed if the intermediate ground states that the system must follow are entangled. This was verified explicitly in (Bauer et al., 2015), where the quantum state was represented by an MPS and projected entangled-pair states (PEPS) (Verstraete and Cirac, 2004; Verstraete et al., 2008). This work showed that the probability of finding the ground state of an Ising spin glass on either a planar or non-planar twodimensional graph increases with the amount of entanglement in the MPS state or PEPS state. Furthermore, even a small amount of entanglement gives improved success probability over a mean-field model. However, this does not resolve the role entanglement plays in generating a speedup.

In an attempt to address this, the entanglement entropy for the adiabatic Grover algorithm was studied, and it was found to be bounded ( $\leq$ 1) throughout the evolution (Or´us and Latorre, 2004). This was also observed numerically for systems with 10 qubits (Wen and Qiu, 2008). In an effort to check whether more entanglement may help the Grover speedup, (Wen et al., 2009) considered adding an additional term to the Hamiltonian to make the ground state more entangled, to reach an $O ( 1 )$ scaling in a Grover search task. However, since it is impossible to achieve a better-than-quadratic speedup in the Grover search problem without introducing an explicit dependence on the marked state (Bennett et al., 1997), this result is not conclusive in linking entanglement with enhanced computational efficiency. Furthermore, a two-dimensional path for the Grover problem using the quantum adiabatic brachistochrone approach [see Sec. VII.B] that gives a higher success probability for the same evolution time relative to the standard onedimensional path for the Grover problem, in fact has less entanglement (negativity) (Rezakhani et al., 2009).

The entanglement entropy in the adiabatic algorithm for the Exact Cover problem, where no speedup is known (recall Sec. VI.F.2), scales linearly with problem size for $n \leq 2 0$ (Latorre and Orus, 2004; Or´us and Latorre, 2004).

Further studies have also shown this lack of correlation between performance and the amount of entanglement entropy. In (Hauke et al., 2015) simulations of adiabatic quantum optimization were performed of a trapped ion Hamiltonian with $n = 1 6$ of the form:

$$
H _ { 1 } = J \sum _ { i \neq j } ^ { n } \frac { \sigma _ { i } ^ { z } \sigma _ { j } ^ { z } } { \left| i - j \right| } + \sum _ { i } { h _ { i } ^ { z } } \sigma _ { i } ^ { z } + V \sum _ { i \neq j } ^ { n } \sigma _ { i } ^ { z } \sigma _ { j } ^ { z } \ ,
$$

with 100 disorder realizations of $h _ { i } ^ { z }$ . It was found that a large entanglement entropy has little significance for the success probability of the optimization task.

Overall, these results indicate that the connection between entanglement and algorithmic efficiency in AQC is currently wide open and deserves further study.

# VII. CIRCUMVENTING SLOWDOWN MECHANISMS FOR AQC

In this section we collect several insights into mechanisms that explain slowdowns in the performance of adiabatic algorithms. We also discuss mechanisms for circumventing such slowdowns. Several important ideas will be reviewed: avoiding the use certain initial and final Hamiltonians, modifying the adiabatic schedule, avoiding quantum phase transitions, and avoiding perturbative energy level crossings.

# A. Avoiding poor choices for the initial and final Hamiltonians

We first show that if one chooses the initial Hamiltonian to be the one-dimensional projector onto the uniform superposition state $| \phi \rangle$ , and uses a linear interpolation, then an improvement beyond a Grover-like quadratic speedup is impossible as long as the final Hamiltonian $H _ { 1 }$ is diagonal in the computational basis. Specifically, for an adiabatic algorithm of the form

$$
H ( t ) = \left( 1 - \frac { t } { t _ { f } } \right) E \left( \mathbb { 1 } - | \phi \rangle \langle \phi | \right) + \frac { t } { t _ { f } } H _ { 1 } ,
$$

the run time $t _ { f }$ for measuring the ground state of $H _ { 1 }$ with probability $p$ is lower bounded by [Theorem 1 of (Farhi et al., 2008); see also ( $7$ nidariˇc and Horvat , 2006)]:

$$
t _ { f } \geq \frac { 2 } { E } \left( 1 - \sqrt { 1 - p } \right) \sqrt { \frac { N } { k } } - 2 \frac { \sqrt { p } } { E } ~ ,
$$

where $N \ = \ 2 ^ { \pi }$ and $k$ is the degeneracy of the ground state of $H _ { 1 }$ . To see this, define an operator $V _ { x }$ for $x =$ $0 , \ldots , N - 1$ that is diagonal in the computational basis:

$$
\langle z | V _ { x } | z \rangle = e ^ { 2 \pi i z x / N } \ ,
$$

and let |xi = Vx|φi = √1 $\begin{array} { r } { | x \rangle = V _ { x } | \phi \rangle = \frac { 1 } { \sqrt { N } } \sum _ { z = 0 } ^ { N - 1 } e ^ { 2 \pi i z x / N } | z \rangle } \end{array}$ PN−1 e2πizx/N z . Now define the modified adiabatic algorithm:

$$
H _ { x } ( t ) = \left( 1 - \frac { t } { t _ { f } } \right) E \left( \mathbb { 1 } - | x \rangle \langle x | \right) + \frac { t } { t _ { f } } H _ { 1 } .
$$

Note that $| x = 0 \rangle = | \phi \rangle$ implies that $H _ { 0 } ( t ) = H ( t )$ . For each $x$ , the final state is given by $| \psi _ { x } \rangle = U _ { x } ( t _ { f } , 0 ) | x \rangle$ , with success probability $p _ { x } ~ = ~ \langle \psi _ { x } | P | \psi _ { x } \rangle$ , where $P$ is the projector onto the ground subspace of $H _ { 1 }$ . Using $H _ { x } ( t ) = V _ { x } H _ { 0 } V _ { x } ^ { \dagger }$ , we have $U _ { x } ( t , 0 ) = V _ { x } U _ { 0 } ( t , 0 ) V _ { x } ^ { \dagger }$ , and hence $p _ { x } = p , \forall x$ since $V _ { x }$ commutes with $P$ . We should already see a potential problem for having $t _ { f }$ scale better than $\sqrt { N }$ , since if we were to run the algorithm backward, we would find the state $| x \rangle$ , which would be solving the Grover problem (note that the initial Hamiltonian (173) is the Grover Hamiltonian in a rotated basis).

Now define an evolution according to an $x$ -independent Hamiltonian:

$$
H _ { \mathrm { R } } ( t ) = \left( 1 - \frac { t } { t _ { f } } \right) E 1 + \frac { t } { t _ { f } } H _ { 1 } \ ,
$$

and let $\begin{array} { r } { | g _ { x } \rangle = \frac { 1 } { \sqrt { p } } P | \psi _ { x } \rangle } \end{array}$ . Consider the difference in the reverse-evolutions associated with $H _ { \mathrm { R } } ( t )$ and $H _ { x } ( t )$ from $\left| g _ { x } \right.$ :

$$
S ( t ) = \sum _ { x } \parallel \left( U _ { x } ^ { \dagger } ( t _ { f } , t ) - U _ { \mathrm { R } } ^ { \dagger } ( t _ { f } , t ) \right) | g _ { x } \rangle \parallel ^ { 2 } .
$$

We can write $| g _ { x } \rangle = \sqrt { p } | \psi _ { x } \rangle + \sqrt { 1 - p } | \psi _ { x } ^ { \bot } \rangle$ , where $| \psi _ { x } ^ { \perp } \rangle$ is orthogonal to $| \psi _ { x } \rangle$ . Using $U _ { x } ^ { \dagger } ( t _ { f } , 0 ) | \psi _ { x } \rangle ~ = ~ | x \rangle$ and

defining $| \mathrm { R } _ { x } \rangle = U _ { \mathrm { R } } ^ { \dagger } ( t _ { f } , 0 ) | g _ { x } \rangle$ , we have:

$$
\begin{array} { r l r } {  { S ( 0 ) = \sum _ { x } \| \sqrt { p } | x \rangle + \sqrt { 1 - p } | x ^ { \perp } \rangle - | \mathrm { R } _ { x } \rangle \| ^ { 2 } } } & { { \scriptstyle ( 1 7 6 \mathrm { \AA } } } \\ & { } & { ~ = 2 N - \sum _ { x } [ \sqrt { p } \langle x | \mathrm { R } _ { x } \rangle + \sqrt { 1 - p } \langle x ^ { \perp } | \mathrm { R } _ { x } \rangle + \mathrm { c . c . } ] } \\ & { } & { ~ \quad \quad ( 1 7 6 \mathrm { \AA } } \\ & { } & { \quad \geq 2 N - 2 \sqrt { p } \sum _ { x } | \langle x | \mathrm { R } _ { x } \rangle | - 2 N \sqrt { 1 - p } . \quad \quad ( 1 7 6 \mathrm { \AA } } \end{array}
$$

Since $H _ { \mathrm { R } }$ commutes with $H _ { 1 }$ , the state $\left| \mathrm { R } _ { x } \right.$ is an element of the $k$ -dimensional ground subspace of $H _ { 1 }$ . Choosing a basis $\{ \left| G _ { i } \right. \} _ { i = 1 } ^ { k }$ for this subspace, and writing $| \mathrm { R } _ { x } \rangle =$ Pki=1 αx,i|Gii, we have:

$$
\begin{array} { r l r } {  { \sum _ { x } | \langle x | \mathrm { R } _ { x } \rangle | \le \sum _ { x , i } | \alpha _ { x , i } | \cdot | \langle x | G _ { i } \rangle | } } \\ & { } & { \le \sqrt { \sum _ { x , i } | \alpha _ { x , i } | \sum _ { x ^ { \prime } , i ^ { \prime } } | \langle x ^ { \prime } | G _ { i ^ { \prime } } \rangle | } = \sqrt { N k } . } \end{array}
$$

Therefore, we have:

$$
S ( 0 ) \geq 2 N \left( 1 - \sqrt { 1 - p } \right) - 2 \sqrt { N k p } .
$$

In order to upper-bound $S ( 0 )$ , we use $S ( t _ { f } ) - S ( 0 ) \ \leq$ $\int _ { 0 } ^ { t _ { f } } | \frac { d } { d t } S ( t ) | d t$ with $S ( t _ { f } ) = 0$ . The derivative can be computed using the Schr¨odinger equation:

$$
\begin{array} { r l r } { \displaystyle \frac { d } { d t } S ( t ) = - i \sum _ { x } \langle g _ { x } | U _ { x } ( t _ { f } , t ) \left[ H _ { x } ( t ) - H _ { \mathrm { R } } ( t ) \right] U _ { \mathrm { R } } ^ { \dagger } ( t _ { f } , t ) | g _ { x } \rangle } & { } & \\ { + \mathrm { c . c . } } & { } & \\ { = - 2 \Im \sum _ { x } \left( 1 - \frac { t } { t _ { f } } \right) E \langle g _ { x } | U _ { x } ( t _ { f } , t ) | x \rangle \times } & { } & \\ { \langle x | U _ { \mathrm { R } } ^ { \dagger } ( t _ { f } , t ) | g _ { x } \rangle } & { } & { ( 1 7 9 ) } \end{array}
$$

Thus:

$$
\begin{array} { r c l } { { \displaystyle \left. \frac { d } { d t } S ( t ) \right. \le 2 E \left( 1 - \frac { t } { t _ { f } } \right) \sum _ { x } \left. \langle x \vert U _ { \mathrm { R } } ^ { \dagger } ( t _ { f } , t ) \vert g _ { x } \rangle \right. } } \\ { { \displaystyle \le 2 E \left( 1 - \frac { t } { t _ { f } } \right) \sqrt { N k } \ , } } \end{array}
$$

where in Eq. (180a) we used the same trick as in Eq. (177). Therefore, $\begin{array} { r } { \int _ { 0 } ^ { t _ { f } } | \frac { d } { d t } S ( t ) | d t \le E t _ { f } \sqrt { N k } } \end{array}$ . Putting the upper and lower bound for $S ( 0 )$ together, we have:

$$
E t _ { f } \sqrt { N k } \ge 2 N \left( 1 - \sqrt { 1 - p } \right) - 2 \sqrt { N k p } ,
$$

which yields Eq. (171).

As an example of the relevance of this result, consider the trivial case of $n$ decoupled spins in a global magnetic field. For an initial Hamiltonian that reflects the bit-structure of the problem, e.g., the standard $H _ { 0 } \ =$ $- \sum _ { i } \sigma _ { i } ^ { x }$ , the run time of the adiabatic algorithm scales as $\sqrt { n }$ (Brady and van Dam, 2017; Muthukrishnan et al., 2016). If, however, we were to choose instead the projector initial Hamiltonian, the result above shows that we would find a dramatically poor scaling despite the simplicity of the final Hamiltonian.

A similar result is found if all structure is removed from the final Hamiltonian. Namely, if $\begin{array} { r } { H _ { 1 } = \sum _ { z } { h ( z ) } { | z \rangle } \langle z { | } } \end{array}$ , we can define a permutation $\pi$ over the $N$ computational basis states such that $h ^ { [ \pi ] } ( z ) = h ( \pi ^ { - 1 } ( z ) )$ . Assume that the initial Hamiltonian is $\pi$ -independent and that $c ( t )$ satisfies $| c ( t ) | \leq 1$ . Then, for the permuted Hamiltonian $\begin{array} { r } { H _ { 1 , \pi } = \sum _ { z } { h ( z ) | \pi ( z ) \rangle \langle \pi ( z ) | } } \end{array}$ , one can show that if the adiabatic algorithm

$$
H _ { \pi } ( t ) = H _ { 0 } + c ( t ) H _ { 1 , \pi }
$$

succeeds with probability $p$ for a set of $\epsilon N !$ permutations, then [Theorem 2 of (Farhi et al., 2008)]:

$$
t _ { f } \ge \frac { \epsilon ^ { 2 } p } { 1 6 h ^ { * } } \sqrt { N - 1 } - \frac { \epsilon \sqrt { \epsilon / 2 } } { 4 h ^ { * } } ~ ,
$$

where $\begin{array} { r } { h ^ { * } = \sqrt { \sum _ { z } h ( z ) ^ { 2 } / N - 1 } } \end{array}$ . This result means that no algorithm of the form of Eq. (182) can find the minimum of $H _ { 1 , \pi }$ with a constant probability for even a fraction of all permutations if $t _ { f }$ is $o ( \sqrt { N } )$ .

The lesson from this analysis is what not to do when designing quantum adiabatic algorithms: avoid choosing the initial Hamiltonian to be the one-dimensional projector onto the uniform superposition state if a betterthan-quadratic speedup is hoped for, and avoid removing structure from the final Hamiltonian.

# B. Quantum Adiabatic Brachistochrone

Modifying the adiabatic schedule adaptively so that it slows down as the gap decreases is an approach that is essential for obtaining a quadratic speedup using the adiabatic Grover algorithm [recall Sec. III.A]. Here we discuss how such ideas, including the condition for the locally optimized schedule [Eq. (24)] can be understood as arising from a variational time-optimal strategy for determining the interpolating Hamiltonian between $H _ { 0 }$ and $H _ { 1 }$ (Rezakhani et al., 2009). By time-optimal, we mean a strategy that gives rise to the shortest total evolution time $t _ { f }$ while guaranteeing that the final evolved state $| \psi ( t _ { f } ) \rangle$ is close to the desired final ground state $| \varepsilon _ { 0 } ( t _ { f } ) \rangle$ . The success of the strategy is judged by the trade-off between $t _ { f }$ and the fidelity $F ( t _ { f } ) = \left| \langle \psi ( t _ { f } ) | \varepsilon _ { 0 } ( t _ { f } ) \rangle \right| ^ { 2 }$ . We first discuss this method generally and then show how it applies to the adiabatic Grover case.

The interpolating Hamiltonian’s time-dependence comes from a set of control parameters $\begin{array} { r l } { \vec { x } ( t ) } & { { } = } \end{array}$ $\left( x ^ { 1 } ( t ) , \ldots , x ^ { M } ( t ) \right)$ , i.e., $H ( t ) = H [ \vec { x } ( t ) ]$ . We can parameterize $\vec { x } ( t )$ in terms of a dimensionless time parameter $s ( t )$ with $s ( 0 ) = 0$ and $s ( t _ { f } ) = 1$ , where $\begin{array} { r } { v = \frac { d s } { d t } } \end{array}$ characterizes the speed with of motion along the control trajectory $\vec { x } [ s ( t ) ]$ . The total evolution time is then given by:

$$
t _ { f } = \int _ { 0 } ^ { 1 } \frac { d s } { v ( s ) } .
$$

Motivated by the form of the adiabatic condition, let us define the following Lagrangian

$$
\begin{array} { l } { \displaystyle \mathcal { L } [ \vec { x } ( s ) , \dot { \vec { x } } ( s ) ] \equiv \frac { \| \partial _ { s } H ( s ) \| _ { \mathrm { H S } } ^ { 2 } } { \Delta ^ { p } ( s ) } ~ ( 1 8 5 ) } \\ { \displaystyle = \sum _ { i , j } \frac { \mathrm { T r } \left( \partial _ { x ^ { i } } H ( s ) \partial _ { x ^ { j } } H ( s ) \right) } { \Delta ^ { p } ( s ) } \partial _ { s } x ^ { i } ( s ) \partial _ { s } x ^ { j } ( s ) } \end{array}
$$

$p > 0 )$ ), and adiabatic-time functional

$$
\mathcal { T } [ \vec { x } ( s ) ] = \int _ { 0 } ^ { 1 } d s \mathcal { L } [ \vec { x } ( s ) , \dot { \vec { x } } ( s ) ] ~ ,
$$

where $\| A \| _ { \mathrm { H S } } \equiv \sqrt { \mathrm { T r } \left( A ^ { \dagger } A \right) }$ is the Hilbert-Schmidt norm, chosen to ensure analyticity (this choice is not unique, but other choices may not induce a corresponding Riemannian geometry). The time-optimal curve $\vec { x } _ { \mathrm { Q A B } } ( s )$ is the quantum adiabatic brachistochrone (QAB), and is the solution of the variational equation $\delta T [ \vec { x } ( s ) ] / \delta \vec { x } ( s ) =$ 0.

Alternatively, the problem can be thought of in geometrical terms. The integral in Eq. (186) is of the form $\begin{array} { r } { \int d s \sum _ { i , j } g _ { i j } ( \vec { x } ) \partial _ { s } x ^ { i } \partial _ { s } x ^ { j } } \end{array}$ , which defines a reparametrization-invariant object. Therefore, using results from differential geometry, the Euler-Lagrange equations derived from extremizing Eq. (186) are simply the geodesic equations associated with the metric $g _ { i j }$ appearing in ${ \mathcal { L } } [ { \vec { x } } ( s ) , { \dot { \vec { x } } } ( s ) ] = g _ { i j } ( { \vec { x } } ) { \dot { x } } ^ { i } { \dot { x } } ^ { j }$ (Einstein summation convention):

$\Gamma \sim g ^ { - 1 } \partial g \sim \Delta ^ { - 1 } \partial \Delta$ , and $\mathbf { R } \sim \partial ^ { 2 } g + g \Gamma ^ { 2 } \sim \Delta ^ { - p - 2 }$ .   
Thus, the smaller the gap, the higher the curvature.

Let us illustrate with a simple example. Consider the following Hamiltonian with $a$ single control parameter $x ^ { 1 } ( s )$ :

$$
H ( s ) = \left( 1 - x ^ { 1 } ( s ) \right) { \cal P } _ { a } ^ { \perp } + x ^ { 1 } ( s ) { \cal P } _ { b } ^ { \perp } \ ,
$$

where we have defined the projector $P _ { a } ^ { \perp } = \mathbb { 1 } - | a \rangle \langle a |$ and similarly for $P _ { b } ^ { \perp }$ . This includes the Grover problem as the special case where $| a \rangle$ is the uniform superposition and $| b \rangle$ is the marked state. We can always find a state $| a ^ { \perp } \rangle$ such that $| b \rangle = \alpha _ { 0 } | a \rangle + \alpha _ { 1 } | a ^ { \bot } \rangle$ , where $\alpha _ { 0 } = \langle a | b \rangle$ . Therefore, the evolution according to $H ( s )$ occurs in a two dimensional subspace spanned by $| a \rangle$ and $| a ^ { \perp } \rangle$ , and:

$$
\begin{array} { c } { { \partial _ { x ^ { 1 } } H ( s ) = - P _ { a } ^ { \perp } + P _ { b } ^ { \perp } } } \\ { { \mathrm { T r } \left( \partial _ { x ^ { 1 } } H ( s ) \partial _ { x ^ { 1 } } H ( s ) \right) = 2 \left( 1 - | \alpha _ { 0 } | ^ { 2 } \right) } } \\ { { \Delta ( s ) = \sqrt { 1 - 4 \left( 1 - | \alpha _ { 0 } | ^ { 2 } \right) x ^ { 1 } ( s ) ( 1 - x ^ { 1 } ( s ) ) } } } \\ { { g _ { 1 1 } = \displaystyle \frac { 2 ( 1 - | \alpha _ { 0 } | ^ { 2 } ) } { \Delta ( s ) ^ { 3 } } ~ . } } \end{array}
$$

The geodesic equation is then given by:

$$
\begin{array} { l } { \displaystyle \frac { d ^ { 2 } } { d s ^ { 2 } } x ^ { 1 } ( s ) \qquad \quad ( 1 9 1 ) } \\ { \displaystyle \quad + \frac { p \left( 1 - 2 x ^ { 1 } ( s ) \right) \left( 1 - | \alpha _ { 0 } | ^ { 2 } \right) } { 1 - 4 x ^ { 1 } ( s ) \left( 1 - x ^ { 1 } ( s ) \right) \left( 1 - | \alpha _ { 0 } | ^ { 2 } \right) } \left( \frac { d } { d s } x ^ { 1 } ( s ) \right) ^ { 2 } = 0 . } \end{array}
$$

In the case of $p = 4$ , we can solve this equation analytically, and the solution with the boundary conditions $x ^ { 1 } ( 0 ) = 1 - x ^ { 1 } ( 1 ) = 0$ is given by:

$$
x ^ { 1 } ( s ) = { \frac { 1 } { 2 } } + { \frac { | \alpha _ { 0 } | } { 2 { \sqrt { 1 - | \alpha _ { 0 } | ^ { 2 } } } } } \tan \left[ \cos ^ { - 1 } \left( | \alpha _ { 0 } | \right) ( 2 s - 1 ) \right]
$$

$$
\partial _ { s } ^ { 2 } x ^ { k } + \Gamma _ { i j } ^ { k } \partial _ { s } x ^ { i } \partial _ { s } x ^ { j } = 0 \ ,
$$

wherefel sym $\begin{array} { r } { \Gamma _ { i j } ^ { k } = \frac { 1 } { 2 } g ^ { k l } \left( \partial _ { j } g _ { l i } + \partial _ { i } g _ { l j } - \partial _ { l } g _ { i j } \right) } \end{array}$ are the Christof-d

$$
g _ { i j } ( \vec { x } ) = \frac { \mathrm { T r } [ \partial _ { i } H ( \vec { x } ) \partial _ { j } H ( \vec { x } ) ] } { \Delta ^ { p } ( \vec { x } ) } \ .
$$

To find the variational time-optimal strategy associated with minimizing Eq. (186), the procedure is thus as follows: (a) solve Eq. (187) to find the optimal path $\vec { x } _ { \mathrm { Q A B } } ( s )$ ; (b) compute the adiabatic error using the Schr¨odinger equation along this optimal path (or multiparameter schedule). Note that to compute the metric requires knowledge of the gap, or at least an estimate thereof.

The optimal path is a geodesic in the parameter manifold endowed with the Riemannian metric $g$ . This metric gives rise to a curvature tensor $\mathbf { R }$ , which can be computed from the metric tensor and the connection using standard methods (Nakahara, M., 1990). Namely, (note that cos−1(|α0|) = tan−1  √1−|α0|2α . Remarkably, this is equivalent to the expression we found for the Grover problem [Eq. (29)] if we take $\alpha _ { 0 } = 1 / \sqrt { N }$ , despite the different choice of norm and value of $p$ . This shows that the optimal schedule for the Grover problem has a deep differential geometric origin.

We can extend the analysis to two control parameters such that the time-dependent Hamiltonian is given by:

$$
H ( s ) = x ^ { 1 } ( s ) P _ { a } ^ { \perp } + x ^ { 2 } ( s ) P _ { b } ^ { \perp } \ .
$$

The associated QAB (or geodesic) path can be found numerically, and it turns out that it is not of the form $x ^ { 2 } ( s ) = 1 - x ^ { 1 } ( s )$ , i.e., it is different from the (Roland and Cerf, 2002) path given by Eq. (192). The optimal two-parameter path reduces the adiabatic error relative to the latter [see Fig. $9 ( \mathrm { a } ) ]$ , but can of course not reduce the (already optimal) $\sqrt { N }$ scaling. The two-parameter QAB also has lower curvature than the Roland-Cerf path [see Fig. 9(b)], which implies that it follows a path with a larger gap and less entanglement than the latter (Rezakhani et al., 2009), as mentioned in Sec. VI.G.2.

The differential geometric approach to AQC was further explored in (Rezakhani et al., 2010a), where its connections to quantum phase transitions were elucidated, within a unifying information-geometric framework. See also (Zulkowski and DeWeese, 2015).

![](images/ab39fd20bbda1921661ab0d0965a7496df9dce585de675fa631dcde8587f55b5.jpg)  
FIG. 9 (a) Final-time error $\delta ( T ) = \sqrt { 1 - F ( T ) }$ ( $T = T _ { f }$ in our notation) for the single-control (denoted RC for Roland-Cerf) and two-parameter control (denoted geodesic2) geodesic paths for the Grover problem with $n = 6$ . Squares (cyan) indicate where the two-parameter geodesic path outperforms (i.e. has a lower error than) the single-parameter path; circles (red) correspond to the opposite case. (b) The curvature tensor component $R _ { 1 2 1 2 }$ for $n = 3$ . The curves on the curvature surface show the case of the standard linear interpolation $x _ { 2 } = 1 - x _ { 1 }$ (denoted Crit.), the path followed by the one-parameter geodesic (denoted RC), and the path followed by the two-parameter geodesic (denoted QAB). From (Rezakhani et al., 2009).

# C. Modifying the initial Hamiltonian

Rather than modifying the adiabatic interpolation, one may modify the initial Hamiltonian. Such a strategy was pursued in (Farhi et al., 2011) and tried on a particular set of 3-SAT instances, where the clauses are picked randomly subject to satisfying two disparate planted solutions and then penalizing one of them with a single additional clause. This was done in order to generate instances with an avoided crossing at the final time $s = 1$ , reproducing the type of obstacle to AQC envisioned in (Altshuler et al., 2010).

It was then shown that in this case, by picking a random initial Hamiltonian of the form

$$
H _ { 0 } = \frac { 1 } { 2 } \sum _ { i = 1 } ^ { n } c _ { i } \left( \mathbb { 1 } - \sigma _ { i } ^ { x } \right) ~ ,
$$

where $c _ { i }$ is a random variable taking value $1 / 2$ or $3 / 2$ with equal probability, it is possible to remove the small gap encountered by the standard adiabatic algorithm with high probability. Since this strategy does not rely on information about the specific instance, it appears to be quite general. Therefore, if the algorithm is to be run on a single instance of some optimization problem, the adiabatic algorithm should be run repeatedly with different initial Hamiltonians (Farhi et al., 2011).

An alternative approach based on modifying the initial Hamiltonian, with a different goal, was proposed in (Perdomo-Ortiz et al., 2011), whereby an initial guess for the solution (a computational basis state) is used as the initial state of the adiabatic algorithm. An initial Hamiltonian is used with this state as its ground state. Evolution to the final Hamiltonian then proceeds according to a standard schedule. If the final state that is measured is not the ground state of the final Hamiltonian (due to diabatic transitions), the algorithm can be repeated with the measured state as the new initial state. Such “warm start” repetitions of the algorithm exhibited improved performance compared to the standard approach for 3-SAT problems, although the results were limited to relatively small system sizes of 6 and 7 qubits.

# D. Modifying the final Hamiltonian

The same problem can be specified by two or more different final Hamiltonians, as we saw, e.g., in the case of Exact Cover 3 (EC3), in terms of Eqs. (154) and (155). It was claimed in (Altshuler et al., 2010) that adiabatic quantum optimization fails for random instances of EC3 because of Anderson localization. The claim, which we discuss in more detail in Sec. VII.G, was based on the form given in Eq. (155). However, as argued in (Choi, 2011), it is possible to reformulate the final Hamiltonian for EC3 such that the argument in (Altshuler et al., 2010) may not apply. Namely, for any pair of binary variables $x c _ { i } , x c _ { j }$ in the same clause $C$ , add a term $D _ { i j } x _ { C _ { i } } x _ { C _ { j } }$ with $D _ { i j } > 0$ ; this is permissible since in order for a clause to be satisfied, exactly one variable must take value 1, whereas the other two are 0. Numerical evidence for up to 15 bits suggests that the addition of the new set of arbitrary parameters $D _ { i j }$ may avoid the Anderson localization issue (Choi, 2011). This example illustrates a general principle, that it can be incorrect to conclude from the failure of one specific choice of the final Hamiltonian that all quantum adiabatic algorithms fail for the same problem.

# E. Adding a catalyst Hamiltonian

We define a “catalyst” as a term that (1) vanishes at the initial and final times, but is present at intermediate times, (2) is a sum of local terms with the same qubitinteraction graph as the final Hamiltonian $H _ { 1 }$ , (3) does not use any other information specific to the particular instance.

Consider, e.g.:

$$
H ( s ) = ( 1 - s ) H _ { 0 } + s ( 1 - s ) H _ { \mathrm { C } } + s H _ { 1 } \ .
$$

The specific form of $H _ { \mathrm { { C } } }$ is of course important, but even a randomly chosen catalyst can help (Farhi et al., 2011, 2002b; Zeng et al., 2016). We illustrate how $H _ { \mathrm { { C } } }$ can turn a slowdown (exponential run time) into a success (at worst polynomial run time) for a specific problem with a specific $H _ { \mathrm { { C } } }$ that is analytically tractable. Consider a final Hamiltonian of the form

$$
H _ { 1 } = \sum _ { z } h ( z ) | z \rangle \langle z | \ ,
$$

where $z$ denotes an $n$ -bit string, and $\begin{array} { r l } { h ( z ) } & { { } = } \end{array}$ $\begin{array} { r } { \sum _ { i < j < k } h _ { 3 } ( z _ { i } , z _ { j } , z _ { k } ) } \end{array}$ with

$$
h _ { 3 } ( z _ { 1 } , z _ { 2 } , z _ { 3 } ) = \left\{ \begin{array} { l l } { { 0 , ~ z _ { 1 } + z _ { 2 } + z _ { 3 } = 0 } } \\ { { 3 , ~ z _ { 1 } + z _ { 2 } + z _ { 3 } = 1 } } \\ { { 1 , ~ z _ { 1 } + z _ { 2 } + z _ { 3 } = 2 } } \\ { { 1 , ~ z _ { 1 } + z _ { 2 } + z _ { 3 } = 3 } } \end{array} \right. .
$$

The all-zero bit string minimizes the final Hamiltonian with energy 0.

The cost function $h ( z )$ is bit-permutation symmetric and only depends on the Hamming weight $| z |$ , which facilitates the analysis. Specifically (Farhi et al., 2002a):

$$
\begin{array} { c } { { h ( z ) = \displaystyle \frac { 3 } { 2 } | z | \left( n - | z | \right) \left( n - | z | - 1 \right) + \displaystyle \frac { 1 } { 2 } | z | \left( | z | - 1 \right) \left( n - | z | \right) } } \\ { { + \displaystyle \frac { 1 } { 6 } | z | \left( | z | - 1 \right) \left( | z | - 2 \right) ~ . } } \end{array}
$$

The final Hamiltonian cthe total spin operators $\begin{array} { r } { S ^ { \alpha } = \frac { 1 } { 2 } \sum _ { i = 1 } ^ { n } \sigma _ { i } ^ { \alpha } } \end{array}$ n in terms ofby using the mapping $\textstyle | z | \mapsto { \frac { n } { 2 } } - S ^ { z }$ . The initial Hamiltonian is taken to be

$$
H _ { 0 } = \frac { ( n - 1 ) ( n - 2 ) } { 2 } \left( \frac { n } { 2 } \mathbb { 1 } - S ^ { x } \right) ~ ,
$$

[the unconventional normalization is to ensure that both $H _ { 1 }$ and $H _ { 0 }$ scale similarly with $n$ (Farhi et al., 2000)]. $H _ { \mathrm { C } }$ is taken to be identical for all combinations of three bits in order to preserve the permutation symmetry:

$$
H _ { \mathrm { C } } = - 2 n \left( S ^ { x } S ^ { z } + S ^ { z } S ^ { x } \right) .
$$

Note that this catalyst is non-stoquastic. A useful way to characterize the change due to the introduction of $H _ { \mathrm { C } }$ is

to study the semi-classical potential associated with the Hamiltonian:

$$
V ( s , \theta , \varphi ) = \langle \theta , \varphi | H ( s ) | \theta , \varphi \rangle \ ,
$$

where $| \theta , \varphi \rangle$ is the spin-coherent state defined in Eq. (162). In the large $n$ limit we have (Farhi et al., 2002b):

$$
\begin{array} { l } { \displaystyle \operatorname* { l i m } _ { n \to \infty } V / ( 2 / n ) ^ { 3 } = 2 ( 1 - s ) ( 1 - \sin \theta \cos \varphi ) \qquad } \\ { \displaystyle \qquad + \frac 1 6 s \left( 1 3 + 3 \cos \theta - 9 \cos ^ { 2 } \theta - 7 \cos ^ { 3 } \theta \right) } \\ { \displaystyle \qquad - 8 s ( 1 - s ) \cos \theta \sin \theta \cos \varphi \ , \qquad ( 2 0 2 ) } \end{array}
$$

where the three terms arise from the initial, final and catalyst Hamiltonians, respectively. We display the behavior of this potential in Fig. 10. In the absence of $H _ { \mathrm { { C } } }$ , there is a value of $s$ where the potential has degenerate minima, and the system must tunnel from the right well to the left well in order to follow the global minimum. This point is associated with an exponentially small gap (Farhi et al., 2002a), i.e., the algorithm requires exponential time to follow the global minimum. However, in the presence of $H _ { \mathrm { { C } } }$ the potential never exhibits such an obstacle; there is always a single global minimum that the system can follow from $s = 0$ to $s = 1$ with polynomial run time.

Using this method of introducing a catalyst Hamiltonian, improvements were generally observed on a large number of MAX 2-SAT instances of size $n = 2 0$ (by directly solving the Schr¨odinger equation) (Crosson et al., 2014). Both stoquastic and non-stoquastic $H _ { \mathrm { { C } } }$ were tried and improved the success rate, but the difference between stoquastic and non-stoquastic was not decisive.

A similar study was performed in (Hormozi et al., 2017) on fully-connected Ising instances, $\begin{array} { r l } { H _ { 1 } } & { { } = } \end{array}$ $\begin{array} { r } { \sum _ { i = 1 } ^ { n } h _ { i } \sigma _ { i } ^ { z } + \sum _ { i < j } ^ { n } J _ { i j } \sigma _ { i } ^ { z } \sigma _ { j } ^ { z } } \end{array}$ , of size $n \leq 1 7$ , where the $J _ { i j }$ ’s and $h _ { i }$ ’s were picked from a continuous Gaussian distribution with zero mean and unit variance. The authors observed that a stoquastic catalyst generally improves the performance of easy instances by boosting the minimum gap and reducing the number of anticrossings. The fraction of instances affected tends to grow with increasing problem size. This is in stark contrast to non-stoquastic catalysts that tend to improve the performance of the very hard instances, but the fraction of improved instances remains constant with increasing problem size. Furthermore, the gap does not generically increase with the addition of this catalyst, and the number of anticrossings grows. This latter feature leads to the increased success probability as population lost from the ground state at one anticrossing can be recovered at a later anticrossing.

![](images/65eda54ffa1e300f6a9580ccc1c3fc466d135b3b416fa9217150195f17e12086.jpg)  
FIG. 10 The diamonds represent the minima followed by a polynomial run time. In the case with $H _ { \mathrm { C } }$ , the potential can follow the global minimum polynomial time. In the case without $H _ { \mathrm { C } }$ , there is an $s$ value where the potential has a degenerate minimum, and the algorithm cannot tunnel to the new global minimum in polynomial time.

# F. Addition of non-stoquastic terms

The addition of non-stoquastic terms was already considered numerically in the previous subsection; here we focus on analytical results obtained for certain mean field models.

Quantum statistical-mechanical techniques (Trotter-Suzuki decomposition, replica method under the replicasymmetric ansatz, and the static approximation) were used in (Nishimori, 2016; Seki and Nishimori, 2012, 2015;

Seoane and Nishimori, 2012) to analyze infinite-range Ising models with ferromagnetic as well as random interactions. These studies concluded that non-stoquastic terms can sometimes modify first-order quantum phase transitions (with an exponentially small gap) in the stoquastic Hamiltonian to second-order transitions (with a polynomially small gap) in the modified, non-stoquastic Hamiltonian.

The Hamiltonian is of the form

$$
H ( s , \lambda ) = ( 1 - s ) H _ { 0 } - s \left( \lambda H _ { 1 , z } ^ { ( p ) } + ( 1 - \lambda ) H _ { 1 , x } ^ { ( k ) } \right)
$$

where $\begin{array} { r } { H _ { 0 } = - \sum _ { i = 1 } ^ { n } \sigma _ { i } ^ { x } } \end{array}$ is a standard initial Hamiltonian, and

$$
H _ { 1 , \alpha } ^ { ( q ) } = n \left( \frac { 1 } { n } \sum _ { i = 1 } ^ { n } \sigma _ { i } ^ { \alpha } \right) ^ { q } , \quad \alpha \in \{ x , z \} \ , \quad q \in \{ p , k \} \ ,
$$

where uastic term  that determ $\lambda ~ \in ~ [ 0 , 1 ]$ $H _ { 1 , x } ^ { ( k ) }$ controls the strength of the non- , and both he locality o $p$ and  the m $k$ are integersdel. The pa-$\geq 2$ rameter $\lambda$ is increased to 1 along with $s$ , so that the netic Ising model final Hamiltonian is the infinite-range ${ \cal H } ( 1 , 1 ) = - { \cal H } _ { 1 , z } ^ { ( p ) }$ . A $p$ -body ferromag- so the -pattern Hopfield model was studied, where $\lambda H _ { 1 , z } ^ { ( p ) }$ is replaced by $\begin{array} { r } { - \sum _ { 1 \leq i _ { 1 } < \cdots < i _ { p } \leq n } J _ { i _ { 1 } \cdots i _ { p } } \sigma _ { i _ { 1 } } ^ { z } \cdot \cdot \cdot \sigma _ { i _ { p } } ^ { z } } \end{array}$ , where $J _ { i _ { 1 } \cdots i _ { p } }$ is given in Eq. (144), with $\xi _ { i _ { p } }$ being $\pm 1$ with equal probability.

In the ferromagnetic case (Seki and Nishimori, 2012; Seoane and Nishimori, 2012) showed that for $p \geq 4$ , a two-local non-stoquastic $X X$ term $^ { 3 9 }$ changes the first order phase transition to a second order one, for an appropriately chosen path in the $( \lambda , s )$ plane, starting from $( \lambda _ { 0 } , 0 )$ (with arbitrary $\lambda _ { 0 }$ ) and ending at $( 1 , 1 )$ . The situation in the Hopfield model case is identical to the ferromagnetic case, for an extensive number of patterns $r \propto n$ . For a fixed number of patterns $p \geq 5$ is sufficient and $p > 3$ is necessary in order to avoid first order phase transitions (Seki and Nishimori, 2015).

# G. Avoiding perturbative crossings

An important slowdown mechanism we already alluded to in Sec. VII.C is due to anti-crossings very close to the end of the evolution, that can result in an extremely small minimum gap. These crossings are often referred to as perturbative, because a perturbative expansion back in time from the final Hamiltonian [e.g., perturbation theory in $\Gamma$ for Eq. (143)] yields perturbed states that cross in energy very close to where the exact eigenstates anti-cross, with a gap that is exponentially small in the Hamming weight of the unperturbed crossing states (Amin and Choi, 2009) [shown there in the context of the weighted maximum independent set problem; see also (Farhi et al., 2011; Foini et al., 2010)]. This problem of perturbative crossings was demonstrated for the NP-complete Exact Cover problem [recall Sec. VI.F.2] in (Altshuler et al., 2010), who related the mechanism of exponentially small spectral gaps to Anderson localization of the eigenfunctions of $H ( s )$ in the space of the solutions. They showed that the Hamming weight between such states can be $\Theta ( n )$ , which is clearly problematic for the adiabatic algorithm. It was also claimed in (Altshuler et al., 2010) that these anti-crossings appear with high probability as the transverse field goes to zero; however the latter claim did not survive a more accurate analysis that took into account the extreme value statistics of the energy levels: the exponential degeneracy of the ground state, which is a distinguishing feature of random NP-complete problems with a discrete spectrum (such as Exact Cover), dooms the proposed mechanism (Knysh, 2016; Knysh and Smelyanskiy, 2010).

Nevertheless, this does not rule out the occurrence of exponentially small gaps close to the end of the evolution. Furthermore, it is plausible that the mechanism for avoided level crossings presented in (Altshuler et al., 2010) may not necessarily be restricted to the end of the evolution, but may occur throughout a many-bodylocalized phase (Laumann et al., 2015). In light of this we now discuss a rather general way to circumvent such perturbative crossings, that differs from the random initial Hamiltonian approach presented in Sec. VII.C.

Using the NP-hard maximum independent set problem, it was shown that this problem occurs only for one particular implementation of the adiabatic algorithm, and different choices can avoid the problem (Choi, 2010). In fact, (Dickson and Amin, 2011) showed that there is always some choice of the initial and final Hamiltonians that avoids such perturbative crossings (note that this does not include non-perturbative crossings). Furthermore, this choice can be made efficiently, i.e., in polynomial time, space and energy (Dickson, 2011), as we now summarize.

The idea of (Dickson, 2011) is to cause the ground state to diverge from all other states by changing the degeneracy of the spectrum of the final Hamiltonian, such that the ground state is the most degenerate, the first excited state less degenerate, up to the highest excited state, which will be the least degenerate. Consider an $n$ -qubit Ising Hamiltonian of the form

$$
H _ { 1 } = \sum _ { i \in { \cal M } } h _ { i } \sigma _ { i } ^ { z } + \sum _ { \{ i , j \} \in { \cal M } } J _ { i j } \sigma _ { i } ^ { z } \sigma _ { j } ^ { z } \ ,
$$

where $h _ { i } , J _ { i j } \in \{ 0 , \pm 1 \}$ and $M$ specifies the non-zero terms, of which there are $m$ . In order to simplify the analysis, assume that there are no single bit-flip degeneracies, meaning that there are no degenerate states that are Hamming distance 1 from each other. For each non-zero $h _ { i }$ term that the ground state satisfies, i.e., $h _ { i } \sigma _ { i } ^ { z } = - 1$ , add $a \geq 1$ ancilla qubits with an interaction of the form:

$$
H _ { h } = \sum _ { k = 1 } ^ { a } b \left( h _ { i } \sigma _ { i } ^ { z } + 1 \right) \left( \sigma _ { i _ { k } } ^ { z } + 1 \right) / 2 ,
$$

where $\{ i _ { 1 } , \ldots , i _ { a } \} \in M _ { h }$ . This term vanishes when the term $h _ { i }$ is satisfied, regardless of the orientation of the $a$ ancillas, whereas otherwise it gives an energy $b n _ { 1 }$ , where $n _ { 1 }$ is the number of ancillas pointing up. Note that when the term is unsatisfied, when all ancilla spins point down the energy cost is zero. This is important because we do not want to change the energy of the ground state configuration.

Similarly, for each (non-zero) $J _ { i j }$ , also add $a$ ancillas with the following interaction term:

$$
H _ { J } = \sum _ { k = 1 } ^ { a } \left( J _ { i j } \sigma _ { i } ^ { z } \sigma _ { j } ^ { z } + 1 \right) \left( \sigma _ { ( i j ) _ { k } } ^ { z } + 1 \right) / 2 ,
$$

where $\{ i j _ { 1 } , \dotsc , i j _ { a } \} \in M _ { J }$ . This introduces 3-local terms; it is possible to use 2-local terms to achieve the same result at the expense of introducing an additional ancilla for each term [see the Appendix of (Dickson, 2011) for details].

The spectrum of the new Hamiltonian (with $m a$ additional ancilla qubits) is the original spectrum when all ancilla qubits point down, and all the new energy states correspond to flips of the ancilla qubits, with increased energy. Note that this means that no new local minima were introduced. Now consider the following adiabatic algorithm Hamiltonian:

$$
H = \lambda H _ { 0 } + H _ { 1 } ^ { \prime } \ , \quad H _ { 1 } ^ { \prime } = H _ { 1 } + H _ { h } + H _ { J } \ ,
$$

with $\lambda$ decreased from $\infty$ (proportional to abm suffices) to $0$ , and where the initial Hamiltonian includes transverse fields on the ancilla qubits:

$$
H _ { 0 } = - \sum _ { i \in M \cup M _ { h } \cup M _ { J } } \sigma _ { i } ^ { x } \mathrm { ~ . ~ }
$$

Consider a non-degenerate classical state $\alpha$ with energy $E _ { \alpha }$ under the action of $H _ { 1 }$ . It becomes degenerate under the action of $H _ { 1 } ^ { \prime }$ . Let $| \alpha \rangle$ denote the uniform superposition over all these degenerate states with energy $E _ { \alpha }$ . Introducing $\lambda > 0$ breaks the degeneracy, and from first order degenerate perturbation theory (see Appendix E.1) the state $| \alpha \rangle$ is the new lowest energy eigenstate within the subspace spanned by the unperturbed degenerate $E _ { \alpha }$ The correction to its energy is, where $E _ { | \alpha \rangle } = E _ { \alpha } + \lambda E _ { | \alpha \rangle } ^ { ( 1 ) } + . . .$

$$
\begin{array} { r l } & { E _ { \alpha } = - \left( \# \mathrm { o f ~ t e r m s ~ i n ~ } H _ { 1 } ^ { \prime } \mathrm { ~ s a t i s f i e d ~ b y ~ } \alpha \right) } \\ & { ~ + \left( \# \mathrm { o f ~ t e r m s ~ i n ~ } H _ { 1 } ^ { \prime } \mathrm { ~ u n s a t i s f i e d ~ b y ~ } \alpha \right) } \\ & { ~ = - 2 ( \# \mathrm { ~ o f ~ t e r m s ~ i n ~ } H _ { 1 } ^ { \prime } \mathrm { ~ s a t i s f i e d ~ b y ~ } \alpha ) + m } \end{array}
$$

(recall that $h _ { i } , J _ { i j } \in \{ 0 , \pm 1 \}$ ), and

$$
\begin{array} { r c l } { { } } & { { } } & { { E _ { | \alpha \rangle } ^ { ( 1 ) } = \langle \alpha | H _ { 0 } | \alpha \rangle } } \\ { { } } & { { } } & { { ~ = - a \left( \# \mathrm { ~ o f ~ t e r m s ~ i n ~ } H _ { 1 } ^ { \prime } \mathrm { ~ s a t i s f i e d ~ b y ~ } \alpha \right) } } \\ { { } } & { { } } & { { ~ = { \frac { a } { 2 } } \left( E _ { \alpha } - m \right) ~ . } } \end{array}
$$

Note that in $E _ { \alpha }$ the contribution is entirely due to $H _ { 1 }$ , while in $E _ { | \alpha \rangle } ^ { ( 1 ) }$ the contribution is entirely due to $H _ { h } + H _ { J }$ .

Taking $a = b = n ^ { 2 }$ , it can be shown that higher order corrections do not depend on $a$ , and hence the first order correction dominates the behavior. Therefore, it is clear that a state $| \alpha \rangle$ with a lower (final) energy than a state $| \beta \rangle$ has a larger negative slope (first-order perturbation energy correction). Therefore, the states $| \alpha \rangle$ and $| \beta \rangle$ grow farther apart for $\lambda > 0$ according to first order perturbation theory. This means that the perturbative crossing is avoided.

This method works in general for the problem of finding the ground state of an arbitrarily-connected Ising model with local fields, and is fully stoquastic. Thus, all NP-complete problems can be attacked using StoqAQC without encountering perturbative crossings. Of course, this does not prove that StoqAQC can solve NP-complete problems in polynomial time. However, it does mean that proving otherwise requires identifying some effect other than perturbative crossings that unavoidably results in exponentially long adiabatic run times.

avoided-level crossing. An instance of this behavior is shown in Fig. 11.

![](images/39e9311b03059d1a82d7ae02047d296fbde1400cb151d3f582d0809070dd0928.jpg)  
FIG. 11 Overlap squared of the evolved wavefunction $| \psi ( t ) \rangle$ and the instantaneous ground state $| \psi _ { 0 } ( t ) \rangle$ and first excited state $| \psi _ { 1 } ( t ) \rangle$ for an instance of MAX-2-SAT with $n = 2 0$ and with a total time $T = 1 0$ . Because of the rapid evolution, population leaks out of the ground state and hence the decrease in the ground state population. There is an avoided level crossing at approximately $t / T = 0 . 6 5$ , where the population between the ground state and first excited state are effectively swapped. Therefore, if more substantial leaking into the first excited state occurs, this will lead to an increase in probability of finding the ground state at the end of the evolution. From (Crosson et al., 2014).

# H. Evolving non-adiabatically

Our discussion so far has been restricted to adiabatic evolutions, where the minimum gap controls the efficiency of the quantum algorithm. However, as we have seen with the glued-trees problem in Sec. III.D, the quantum evolution can take advantage of the presence of two avoided-level crossings (and their associated exponentially small gaps) to leave and return to the ground state with high probability in polynomial time, whereas an adiabatic evolution would have required exponential time. Setting aside the fascinating and intricate field of open-system AQC where relaxation can play a beneficial role in returning the computation to the ground state [the subject of a separate review (Albash and Lidar, 2017)], this is one among several cases where non-adiabatic, i.e., diabatic evolution enhances the performance of a quantum algorithm based on Hamiltonian computation. Another example is (Crosson et al., 2014) [see also (Hormozi et al., 2017)] where it was observed that evolving rapidly (as well as starting from excited states) increased the success probability on the hardest instances of randomly generated $n = 2 0$ MAX-2-SAT instances with a unique ground state. When evolving rapidly, population leaks into the first excited state before the avoided-level crossing and then returns to the ground state after the

A similar result was observed in (Muthukrishnan et al., 2016) for a large class of Perturbed Hamming Weight problems (recall Sec. VI.E.1), but with the difference that the rapid evolution diabatically pushes population to higher excited states and then returns to the ground state through a series of avoided-level crossings, a phenomenon called “diabatic cascade”.

These results raise the question of whether adiabatic evolution is in fact the most efficient choice for running a quantum adiabatic algorithm. After all, the goal is to find the ground state once, with the highest probability and in the shortest amount of time. Therefore, rather than maximizing the probability by increasing the evolution time $t _ { f }$ , we can instead use many rapid repetitions of the algorithm to simultaneously shorten $t _ { f }$ and increase the success probability. Let $p _ { \mathrm { S } } ( t _ { f } )$ denote the single-run success probability of the algorithm with evolution time $t _ { f }$ . The probability of failing to find the ground state after $R$ independent repetitions is $( 1 - p _ { \mathrm { { S } } } ) ^ { R }$ , so the probability of succeeding at least once is $1 - ( 1 - p _ { \mathrm { { S } } } ) ^ { R }$ , which we set equal to the desired probability $p _ { \mathrm { d } }$ . The tradeoff between success probability and run time is therefore well captured by the time-to-solution (TTS) metric, which measures the time required to find the ground state at least once with probability $p _ { \mathrm { d } }$ (typically taken to be

$$
\mathrm { T T S } ( t _ { f } ) = t _ { f } \frac { \ln ( 1 - p _ { \mathrm { d } } ) } { \ln [ 1 - p _ { \mathrm { S } } ( t _ { f } ) ] } \ .
$$

Other metrics exist that quantify this tradeoff, e.g., without insisting on finding the ground state (King et al., 2015), or that make use of optimal stopping theory and assign a cost to each run (Vinci and Lidar, 2016).

For $p _ { \mathrm { S } } \lesssim 1$ (close to the adiabatic limit), only a single (or few) repetitions of the algorithm are necessary and the TTS scales linearly with $t _ { f }$ . As $t _ { f }$ is lowered, the success probability typically decreases and more repetitions are necessary, but the TTS may in fact be lower because of the smaller $t _ { f }$ value. The optimal $t _ { f }$ for the algorithm minimizes the TTS, and is defined as:

$$
\mathrm { T T S } _ { \mathrm { o p t } } = \operatorname * { m i n } _ { t _ { f } > 0 } \mathrm { T T S } ( t _ { f } ) \ .
$$

Benchmarking of algorithms then proceeds as follows. For a specific class of problem instances of varying sizes $n$ , $\mathrm { T I S _ { o p t } }$ is calculated for each size $n$ . The scaling of the algorithm with $n$ is then determined from the scaling with $n$ of TTS $\mathrm { \Gamma _ { o p t } }$ , as, e.g., in (Boixo et al., 2014).

One benefit of this approach is in obtaining a quantum scaling advantage over specific classical algorithms.. For example, the constant gap perturbed Hamming weight oracular problems (Reichardt, 2004) [Sec. VI.D.1] and the “spike” problem of (Farhi et al., 2002a) [Sec. VI.E.1] with a polynomially closing quantum gap, can be solved in $O ( 1 )$ time using a classical algorithm. However, QA exhibits a scaling advantage over SA for these problems in the sense that QA offers a TTS that scales better than SA with single-spin updates (Muthukrishnan et al., 2016).

# VIII. OUTLOOK AND CHALLENGES

Adiabatic quantum computing has blossomed from a speculative alternative approach for solving optimization problems, to a formidable alternative to other universal models of quantum computing, with deep connections to both classical and quantum complexity theory, and condensed matter physics.

In this review we have given an account of most of the major theoretical developments in the field. Of course, some omissions were inevitable. For example, a potentially promising application of AQC is in quantum chemistry, where the calculation of molecular energies can be formulated in terms of a second-quantized fermionic Hamiltonian that is mapped, via a generalized Jordan-Wigner transformation (Bravyi and Kitaev, 2002; P. Jordan and E. Wigner, 1928), to a non-stoquastic qubit Hamiltonian (Aspuru-Guzik et al., 2005; Seeley et al., 2012). This mapping generates $k$ -local interactions, but perturbative gadgets can be used to reduce the problem to only 2-local interactions (Babbush et al., 2014b). The ground state of the mapped Hamiltonian can then be prepared using adiabatic evolution followed by appropriate measurements to determine the energy spectrum. However, the scaling of the minimum gap for such a preparation procedure is not known, and hence this is an example of AQC with a non-stoquastic Hamiltonian for which it is unknown whether a quantum speedup is possible. A variety of other interesting AQC results with an unknown speedup, and which we did not have the space to review here in detail, can be found in (Behrman and Steck, 2016; Cao et al., 2016; Chancellor, 2016; Dulny and Kim, 2016; Durkin, 2016; Goto, 2016; Hashizume et al., 2015; Inack and Pilati, 2015; Karimi and Rosenberg, 2016; Karimi and Ronagh, 2016; Kurihara et al., 2014; Miyahara and Tsumura, 2016; O’Gorman et al., 2015; Rajak and Chakrabarti, 2014; Raymond et al., 2016; Rosenberg et al., 2016; Santra et al., 2016; Sato et al., 2014).

Moreover, to make the review comprehensive and detailed enough to be self-contained, we focused only on the closed-system setting, thus completely ignoring the important problem of AQC in open systems, with the associated questions of error correction and fault tolerance. We also left out the experimental work on AQC and quantum annealing. These important topics will be the subject of a separate review (Albash and Lidar, 2017).

Due to the prominence of stoquastic Hamiltonians in the body of work on AQC, we coined a new term, StoqAQC, which is roughly what was meant when the term “quantum adiabatic algorithm” was first introduced. Correspondingly, we devoted a substantial part of this review to StoqAQC, despite the fact that there are indications that this model of computation may not be more powerful than classical computing. Its prominence is explained by the fact that it is easier to analyze than universal AQC, which requires non-stoquastic terms, and by the fact that it is easier to implement experimentally [see, e.g., (Bunyk et al., 2014; Weber et al., 2017)]. The relatively short history of AQC has witnessed a fascinating battle of sorts between attempts to show that StoqAQC fails to deliver quantum speedups, and corresponding refutations by clever tweaks. To put this and other results we have discussed in the proper perspective, we conclude with a list of 10 key theoretical challenges for the field of AQC:

1. Prove or disprove that StoqAQC is classically efficiently simulatable.   
2. Find an NP-hard optimization for which AQC gives a quantum speedup in the worst case.   
3. Find a class of non-oracular, physically realizable optimization problems for which AQC gives a quantum speedup.   
4. Identify a subset of non-stoquastic Hamiltonians

for which ground state preparation can be done efficiently using adiabatic evolution.

5. Formulate every quantum algorithm that gives a speedup in the circuit model natively as an AQC algorithm (i.e., directly, without using perturbative gadgets).   
6. Find a problem that can be solved with a quantum speedup using AQC, that was not previously known from other models of quantum computing.   
7. Give a way to decide whether adiabatic evolution gives rise to a stronger or weaker speedup than nonadiabatic (diabatic) evolution for a given problem.   
8. Predict the optimal adiabatic schedule for a given problem without a priori knowledge of the size and/or position of its spectral gap.   
9. Prove or disprove that tunneling can generate a (scaling, not prefactor) quantum speedup in AQC.   
10. Establish the relation between entanglement and quantum speedups using AQC.

Solving these problems will likely keep researchers busy for years to come, require interdisciplinary collaborations, and will significantly advance our understanding of AQC. We hope that this review will catalyze new and productive approaches, enhancing our repertoire of algorithms that give rise to quantum speedups from the unique perspective of AQC.

# ACKNOWLEDGMENTS

We are grateful to Vicky Choi, Elizabeth Crosson, Itay Hen, Milad Marvian, Siddharth Muthukrishnan, Hidetoshi Nishimori, and Rolando Somma for useful discussions. This work was supported under ARO Grant No. W911NF-12-1-0523, ARO MURI Grants No. W911NF-11-1-0268 and No. W911NF-15-1-0582, and NSF Grant No. INSPIRE-1551064. The research is based upon work (partially) supported by the Office of the Director of National Intelligence (ODNI), Intelligence Advanced Research Projects Activity (IARPA), via the U.S. Army Research Office contract W911NF-17-C-0050. The views and conclusions contained herein are those of the authors and should not be interpreted as necessarily representing the official policies or endorsements, either expressed or implied, of the ODNI, IARPA, or the U.S. Government. The U.S. Government is authorized to reproduce and distribute reprints for Governmental purposes notwithstanding any copyright annotation thereon.

# Appendix A: Technical calculations

# 1. Upper bound on the adiabatic path length $L$

Right below Eq. (14) we claimed that an upper bound on $L$ is $\operatorname* { m a x } _ { s } \| \dot { H } ( s ) \| / \Delta$ . To see this differentiate the eigenstate equation $H | \varepsilon _ { a } \rangle = \varepsilon _ { a } | \varepsilon _ { a } \rangle$ for the normalized instantaneous eigenstate $\left. \varepsilon _ { a } \right.$ and inner-multiply by $\left. \varepsilon _ { b } \right.$ , with $b \neq a$ , to get $( \varepsilon _ { a } - \varepsilon _ { b } ) \langle \varepsilon _ { b } | \dot { \varepsilon } _ { a } \rangle = \langle \varepsilon _ { b } | \dot { H } | \varepsilon _ { a } \rangle$ . Let $\Delta _ { b a } = \varepsilon _ { b } - \varepsilon _ { a }$ and $\Delta _ { a } = \mathrm { m i n } _ { b } \mathrm { m i n } _ { s } \Delta _ { b a } ( s )$ . Using our phase choice:

$$
\begin{array} { l } { \displaystyle | \dot { \varepsilon } _ { a } \rangle = \displaystyle \sum _ { b } | \varepsilon _ { b } \rangle \langle \varepsilon _ { b } | \dot { \varepsilon } _ { a } \rangle = \displaystyle \sum _ { b \neq a } | \varepsilon _ { b } \rangle \langle \varepsilon _ { b } | \dot { \varepsilon } _ { a } \rangle } \\ { \displaystyle = - \sum _ { b \neq a } | \varepsilon _ { b } \rangle \langle \varepsilon _ { b } | \dot { H } | \varepsilon _ { a } \rangle / \Delta _ { b a } \ . } \end{array}
$$

Thus

$$
\begin{array} { l } { \displaystyle \| | \dot { \varepsilon } _ { a } \rangle \| \leq \displaystyle \frac { 1 } { \Delta _ { a } } \| \sum _ { b \neq a } | \varepsilon _ { b } \rangle \langle \varepsilon _ { b } | \dot { H } | \varepsilon _ { a } \rangle \| } \\ { \displaystyle \leq \frac { 1 } { \Delta _ { a } } \| \sum _ { b \neq a } | \varepsilon _ { b } \rangle \langle \varepsilon _ { b } | \| \| \dot { H } | \varepsilon _ { a } \rangle \| \leq \frac { 1 } { \Delta _ { a } } \| \dot { H } | \| ~ , } \end{array}
$$

where in the last equality we used the definition of the operator norm and the fact that $\sum _ { b \neq a } \left. \varepsilon _ { b } \right. \left. \varepsilon _ { b } \right.$ is a projector. Integration just multiplies by $^ { 1 }$ .

# 2. Proof of the inequality given in Eq. (25)

Note that

$$
\begin{array} { r l } & { \| \partial _ { s } H [ A ( s ) ] \| = | \partial _ { s } A | \| H _ { 1 } - H _ { 0 } \| \leq 2 | \partial _ { s } A | } \\ & { \big \| \partial _ { s } ^ { 2 } H [ A ( s ) ] \big \| \leq 2 | \partial _ { s } ^ { 2 } A | } \end{array}
$$

for the interpolating Hamiltonian (16). Also note that

$$
\begin{array} { c } { { \partial _ { s } ^ { 2 } A ( s ) = c p \Delta ^ { p - 1 } [ A ( s ) ] \frac { d \Delta } { d A } \partial _ { s } A ( s ) } } \\ { { = c ^ { 2 } p \frac { d \Delta } { d A } \Delta ^ { 2 p - 1 } [ A ( s ) ] ~ . } } \end{array}
$$

Thus:

$$
\begin{array} { r l } & { \int _ { 0 } ^ { 1 } \left( \frac { \displaystyle | \partial _ { s } ^ { 2 } H [ A ( s ) ] | } { \Delta ^ { 2 } [ A ( s ) ] } + \frac { \displaystyle | \partial _ { s } H [ A ( s ) ] | ^ { 2 } } { \Delta ^ { 3 } [ A ( s ) ] } \right) d s } \\ & { \quad \le 2 \int _ { 0 } ^ { 1 } \left( \frac { | \partial _ { s } ^ { 2 } A | } { \Delta ^ { 2 } [ A ( s ) ] } + \frac { 2 | \partial _ { s } A | ^ { 2 } } { \Delta ^ { 3 } [ A ( s ) ] } \right) d s } \\ & { \quad = \int _ { 0 } ^ { 1 } 2 e ^ { 2 } \left( p \frac { d \Delta } { d A } + 2 \right) \Delta ^ { 2 p - 3 } [ A ( s ) ] d s } \\ & { \quad = 2 e \int _ { 0 } ^ { 1 } \left( p \frac { d \Delta } { d u } + 2 \right) \Delta ^ { p - 3 } ( u ) d u } \\ & { \quad = 4 c \int _ { 0 } ^ { 1 } \Delta ^ { p - 3 } ( u ) d u , } \end{array}
$$

where in line (A5c) we used the change of variables $u \ = \ A ( s )$ , so that $d s = d u / \partial _ { s } A = d u / [ c \Delta ^ { p } ( u ) ]$ , and in line (A5d) we used $\begin{array} { l } { { B ( p ) } } \end{array} \equiv \ 2 c \int _ { 0 } ^ { 1 } \Delta ^ { p - 3 } d \Delta \ = \ 0$ , since $\begin{array} { r } { \frac { 2 c } { p - 2 } \left( \Delta ^ { p - 2 } ( 1 ) - \Delta ^ { p - 2 } ( 0 ) \right) = 0 } \end{array}$ $B ( 2 ) = 2 c \ln [ \Delta ( 1 ) / \Delta ( 0 ) ] = 0$ 6, due to the boundary con- and $B ( p \neq 2 ) =$ ditions $\Delta ( 0 ) = \Delta ( 1 ) = 1$ [Eq. (18a)].

# Appendix B: A lower bound for the adiabatic Grover search problem

Here we show that there is no schedule that gives a better scaling for the adiabatic Grover problem than the one discussed in Sec. III.A.2, resulting in a quadratic quantum speedup. The argument is due to (Roland and Cerf, 2002), which in turn is based on the general Hamiltonian quantum computation argument by (Farhi and Gutmann, 1998).

To show this, consider two different searches, one for $m$ and another for $m ^ { \prime }$ . We do not allow the schedule to depend on $m$ , i.e., the same schedule must apply to all marked states. Let us denote the states for each at the end of the algorithm by $| \psi _ { m } ( t _ { f } ) \rangle$ and $| \psi _ { m ^ { \prime } } ( t _ { f } ) \rangle$ . In order to be able to distinguish if the search gave $m$ or $m ^ { \prime }$ , we must require that $| \psi _ { m } ( t _ { f } ) \rangle$ and $| \psi _ { m ^ { \prime } } ( t _ { f } ) \rangle$ are sufficiently different. Let us define the distance (or infidelity)

$$
D _ { m m ^ { \prime } } ( t ) \equiv 1 - | \langle \psi _ { m } ( t ) | \psi _ { m ^ { \prime } } ( t ) \rangle | ^ { 2 } \ ,
$$

[note that $D _ { m m ^ { \prime } } ( 0 ) = D _ { m m } ( t ) = 0 ]$ and demand that:

$$
D _ { m m ^ { \prime } } ( t _ { f } ) \geq \epsilon ~ , ~ m \neq m ^ { \prime } ~ .
$$

First, we have a lower bound on the sum:

$$
\begin{array} { r l } { \displaystyle \sum _ { m , m ^ { \prime } } D _ { m m ^ { \prime } } ( t _ { f } ) = \displaystyle \sum _ { m \neq m ^ { \prime } } D _ { m m ^ { \prime } } ( t _ { f } ) } & { } \\ { \displaystyle \geq \sum _ { m \neq m ^ { \prime } } \epsilon = N ( N - 1 ) \epsilon . } \end{array}
$$

Next, let us find an upper bound on the sum. We write the Hamiltonian (16) explicitly as $H ( t ) = \mathbb { 1 } - [ 1 -$ $A ( t ) ] | \phi \rangle \langle \phi | + H _ { 1 m } ( t )$ where $H _ { 1 m } ( t ) = - A ( t ) | m \rangle \langle m |$ . 40 Then:

$$
\begin{array} { r l r } {  { \frac { d } { d t } D _ { m m ^ { \prime } } ( t ) = 2 \Im [ \langle \psi _ { m } | ( H _ { 1 m } - H _ { 1 m ^ { \prime } } ) | \psi _ { m ^ { \prime } } \rangle \langle \psi _ { m ^ { \prime } } | \psi _ { m } \rangle ] } } \\ & { } & { \leq 2  \langle \psi _ { m } | ( H _ { 1 m } - H _ { 1 m ^ { \prime } } ) | \psi _ { m ^ { \prime } } \rangle \langle \psi _ { m ^ { \prime } } | \psi _ { m } \rangle  } \\ & { } & { \leq 2 | \langle \psi _ { m } | H _ { 1 m } | \psi _ { m ^ { \prime } } \rangle | + 2 | \langle \psi _ { m } | H _ { 1 m ^ { \prime } } | \psi _ { m ^ { \prime } } \rangle | . } \end{array}
$$

Let us now sum over all $m$ and $m ^ { \prime }$ :

$$
\begin{array} { r l r } {  { \sum _ { m , m ^ { \prime } } \frac { d } { d t } D _ { m m ^ { \prime } } ( t ) \leq 4 \sum _ { m , m ^ { \prime } } | \langle \psi _ { m } | H _ { 1 m } | \psi _ { m ^ { \prime } } \rangle | } } & { { } \mathrm { ( B 5 } } \\ & { } & { \leq 4 \sum _ { m , m ^ { \prime } } \| H _ { 1 m } | \psi _ { m ^ { \prime } } \rangle \| \| | \psi _ { m } \rangle \| = 4 \sum _ { m , m ^ { \prime } } \| H _ { 1 m } | \psi _ { m ^ { \prime } } \rangle \| ~ , } \end{array}
$$

where we first used the fact that under the sum the two terms in the last line of Eq. (B4) are identical, and then we used the Cauchy-Schwartz inequality ( $| \langle x | y \rangle | \leq$ $\| x \| \| y \| )$ . Now we note that:

$$
\begin{array} { r l r } {  { \sum _ { m } \| H _ { 1 m } | \psi _ { m ^ { \prime } } \rangle \| ^ { 2 } = \sum _ { m } \langle \psi _ { m ^ { \prime } } | H _ { 1 m } H _ { 1 m } | \psi _ { m ^ { \prime } } \rangle } } & { { \mathrm { ( B 6 ) } } } \\ & { } & { \quad = A ^ { 2 } ( t ) \sum _ { m } \langle \psi _ { m ^ { \prime } } | m \rangle \langle m | \psi _ { m ^ { \prime } } \rangle = A ^ { 2 } ( t ) ~ , } \end{array}
$$

so that

$$
\left( \sum _ { m } \| H _ { 1 m } | \psi _ { m ^ { \prime } } \rangle \| \right) ^ { 2 } = \left( \vec { x } \cdot \vec { y } \right) ^ { 2 } \leq ( \vec { x } \cdot \vec { x } ) ( \vec { y } \cdot \vec { y } ) = N A ^ { 2 } ( t ) ,
$$

where $\vec { x } ~ = ~ \left( | | H _ { 1 1 } | \psi _ { m ^ { \prime } } \rangle | | , | | H _ { 1 2 } | \psi _ { m ^ { \prime } } \rangle | | , . . . , | | H _ { 1 N } | \psi _ { m ^ { \prime } } \rangle | | \right)$ and $\vec { y } = ( 1 , 1 , \dots , 1 )$ . Therefore, we have:

$$
\begin{array} { r l r } {  { \sum _ { m , m ^ { \prime } } \frac { d } { d t } D _ { m m ^ { \prime } } ( t ) \leq 4 \sum _ { m , m ^ { \prime } } \| H _ { 1 m } \| \psi _ { m ^ { \prime } } \rangle \| } } \\ & { } & { \leq 4 \sum _ { m ^ { \prime } } \sqrt { N } A ( t ) = 4 N \sqrt { N } A ( t ) . } \end{array}
$$

If we integrate both sides we have:

$$
\sum _ { m , m ^ { \prime } } D _ { m m ^ { \prime } } ( t _ { f } ) \leq 4 N \sqrt { N } \int _ { 0 } ^ { t _ { f } } A ( t ) d t \leq 4 N \sqrt { N } t _ { f } \ .
$$

Combining this with Eq. (B3), we have $N ( N - 1 ) \epsilon \leq$ $4 N \sqrt { N } t _ { f }$ , and hence:

$$
t _ { f } \ge { \frac { \epsilon } { 4 } } { \frac { N - 1 } { \sqrt { N } } } \ ,
$$

so that the computation must last a minimum time of $O ( { \sqrt { N } } )$ if the schedule is to be agnostic about the identity of the marked state. Therefore, the solution using the locally optimized schedule is asymptotically optimal.

# Appendix C: Technical details for the proof of the universality of AQC using the History State construction

We add details to the proof sketch given in Sec. IV.B.

# 1. $| \gamma ( 0 ) \rangle$ is the ground state of $H _ { \mathrm { i n i t } }$

Let us first check that $| \gamma ( 0 ) \rangle$ is the ground state of $H _ { \mathrm { i n i t } }$ with eigenvalue 0. Note that $H _ { \mathrm { i n i t } }$ is a sum of projectors, so it is positive semi-definite. Therefore if we find a state with energy $0$ , then it is definitely a ground state. The all-zero clock state is annihilated by $H _ { \mathrm { c } }$ , $H _ { \mathrm { i n p u t } }$ , and $H _ { \mathrm { c - i n i t } }$ , so we have $H _ { \mathrm { i n i t } } | \gamma ( 0 ) \rangle = 0$ , i.e., $| \gamma ( 0 ) \rangle$ is a ground state of $H _ { \mathrm { i n p u t } }$ . We shall show later that it is a unique ground state.

# 2. $| \eta \rangle$ is a ground state of $H _ { \mathrm { f i n a l } }$

Next we check that $| \eta \rangle$ is a ground state of $H _ { \mathrm { f i n a l } }$ with eigenvalue 0. First, we wish to show that $H _ { \mathrm { f i n a l } }$ is positive semi-definite. We already know that $H _ { \mathrm { i n p u t } }$ and $H _ { \mathrm { c } }$ are positive semi-definite, so we only need to show this to be the case for the $H _ { \ell }$ ’s. This follows since it is easily checked that $H _ { \ell } = H _ { \ell } ^ { \dagger } = \textstyle { \frac { 1 } { 2 } } H _ { \ell } ^ { 2 }$ , so that $\langle X | H _ { \ell } | X \rangle =$ $\begin{array} { r } { \frac { 1 } { 2 } \langle X | H _ { \ell } ^ { \dagger } H _ { \ell } | X \rangle = \frac { 1 } { 2 } \| H _ { \ell } | X \rangle \| ^ { 2 } \geq 0 } \end{array}$ . Thus $H ( s )$ is positive semi-definite, since it is a sum of positive semi-definite terms.

Let us now check that $H _ { \mathrm { f i n a l } }$ annihilates $| \eta \rangle$ . First, because $| \eta \rangle$ only involves legal clock states, it is annihilated by $H _ { \mathrm { c } }$ . Next,

$$
H _ { \mathrm { i n p u t } } | \eta \rangle = H _ { \mathrm { i n p u t } } \frac { 1 } { \sqrt { L + 1 } } | \alpha ( 0 ) \rangle \otimes | 0 ^ { L } \rangle _ { \mathrm { c } } = 0 ~ .
$$

Finally, note that the only non-zero terms in $\textstyle \sum _ { \ell = 0 } ^ { L } H _ { \ell } | \eta \rangle$ are of the form:

$$
\begin{array} { r l r } { \ } & { } & { H _ { \ell } | \alpha ( \ell - 1 ) \rangle \otimes | 1 ^ { \ell - 1 } 0 ^ { L - \ell + 1 } \rangle _ { \mathrm { c } } = } \\ { \ } & { } & { | \alpha ( \ell - 1 ) \rangle \otimes | 1 ^ { \ell - 1 } 0 ^ { L - \ell + 1 } \rangle _ { \mathrm { c } } - | \alpha ( \ell ) \rangle \otimes | 1 ^ { \ell } 0 ^ { L - \ell } \rangle _ { \mathrm { c } } } \\ { \ } & { } & { H _ { \ell } | \alpha ( \ell ) \rangle \otimes | 1 ^ { \ell } 0 ^ { L - \ell } \rangle _ { \mathrm { c } } = } \\ { \ } & { } & { - | \alpha ( \ell - 1 ) \rangle \otimes | 1 ^ { \ell - 1 } 0 ^ { L - \ell + 1 } \rangle _ { \mathrm { c } } + | \alpha ( \ell ) \rangle \otimes | 1 ^ { \ell } 0 ^ { L - \ell } \rangle _ { \mathrm { c } } , } \end{array} ( \mathrm { C 2 }
$$

which cancel. Therefore, $| \eta \rangle$ has eigenvalue $0$ and is a ground state of $H _ { \mathrm { f i n a l } }$ .

# 3. Gap bound in the space spanned by $\{ | \gamma ( \ell ) \rangle \} _ { \ell = 0 } ^ { L }$

Let $S _ { 0 }$ be the space spanned by $\{ | \gamma ( \ell ) \rangle \} _ { \ell = 0 } ^ { L }$ . Let us show that $H ( s )$ acting on any state in $S _ { 0 }$ keeps it in this subspace:

$$
\begin{array} { r l } & { \qquad H _ { \mathrm { c } } | \gamma ( \ell ) \rangle = 0 \ , } \\ & { H _ { \mathrm { i n p u t } } | \gamma ( \ell ) \rangle = 0 \ , } \\ & { H _ { \mathrm { c - i n i t } } | \gamma ( \ell ) \rangle = \left\{ \begin{array} { l l } { 0 \ , } & { \ell = 0 } \\ { | \gamma ( \ell ) \rangle \ , \ \ell \neq 0 \ } \end{array} \right. } \\ & { \qquad H _ { \ell } | \gamma ( \ell ^ { \prime } ) \rangle = \delta _ { \ell ^ { \prime } , \ell } \left( | \gamma ( \ell - 1 ) \rangle - | \gamma ( \ell ) \rangle \right) } \\ & { \qquad + \delta _ { \ell ^ { \prime } , \ell } \left( | \gamma ( \ell ) \rangle - | \gamma ( \ell - 1 ) \rangle \right) \ . } \end{array}
$$

Since the initial state $| \gamma ( 0 ) \rangle \in S _ { 0 }$ , the dynamics generated by $H ( s )$ keep the state in $S _ { 0 }$ . Thus, it is sufficient to bound the gap in this subspace. In the basis given by $\{ | \gamma ( \ell ) \rangle \} _ { \ell = 0 } ^ { L }$ , we can write an $\left( L + 1 \right) \times \left( L + 1 \right)$ matrix representation of the Hamiltonian in the $S _ { 0 }$ subspace, which,

using Eq. (C3), is:

$$
\begin{array} { r l } { H _ { S _ { 0 } } ( s ) = ( 1 - s ) \left( \begin{array} { l l l l } { 0 } & { 0 } & { 0 } & { \cdots } & \\ { 0 } & { 1 } & { 0 } & & \\ & { 1 } & & & \\ & & { \ddots } & & \\ & & & { 1 } & { 0 } \\ & & & & { 1 } \end{array} \right) } & { { } } \\ { + s \left( \begin{array} { l l l l } { - \frac { 1 } { 2 } } & { - \frac { 1 } { 2 } } & { 0 } & { 0 } & { \cdots } & { 0 } \\ { 0 } & { 1 } & { - \frac { 1 } { 2 } } & & { 1 } \\ { 0 } & { - \frac { 1 } { 2 } } & { 1 } & { - \frac { 1 } { 2 } } & & \\ { \vdots } & { \ddots } & { \ddots } & { \ddots } \\ { 0 } & { - \frac { 1 } { 2 } } & { - \frac { 1 } { 2 } } & { \frac { 1 } { 2 } } \\ { 0 } & { 0 } & { - \frac { 1 } { 2 } } & { - \frac { 1 } { 2 } } \end{array} \right) } & { { } , } \end{array}
$$

# a. Bound for $s < 1 / 3$

Let us first bound the gap for $s < 1 / 3$ . The Gerschgorin circle theorem states (Gershgorin, 1931): Let $A$ be any matrix with entries $a _ { i j }$ . Consider the disk $D _ { i }$ (for $1 \ \leq \ i \ \leq \ n$ ) in the complex plane defined as: $\begin{array} { r } { D _ { i } = \Big \{ z \ \Big | \ | z - a _ { i i } | \le \sum _ { j \neq i } | a _ { i j } | \Big \} } \end{array}$ . Then the eigenvalues of $A$ are contained in $\cup _ { i } D _ { i }$ and any connected component of $\cup _ { i } D _ { i }$ contains as many eigenvalues of $A$ as the number of disks that form the component.

Consider the cases $i = 1$ , $i = L + 1$ , and $i \neq 1 , { \cal L } + 1$ separately. Note that when $s < 1 / 3$ :

$$
\left[ H _ { S _ { 0 } } ( s ) \right] _ { 1 1 } = { \frac { 1 } { 2 } } s < { \frac { 1 } { 6 } } \ , \quad \sum _ { j \neq 1 } | a _ { 1 j } | = { \frac { 1 } { 2 } } s < { \frac { 1 } { 6 } } \ ,
$$

$$
\begin{array} { c } { { \displaystyle { \left[ H _ { S _ { 0 } } ( s ) \right] _ { L + 1 , L + 1 } = 1 - \frac { 1 } { 2 } s > 5 / 6 } } } \\ { { \displaystyle { \sum _ { j \ne L + 1 } \left| a _ { L + 1 , j } \right| = s < \frac { 1 } { 3 } } , } } \\ { { \displaystyle { \left[ H _ { S _ { 0 } } ( s ) \right] _ { i i } = 1 \ , \quad { \it i \ne } 1 , L + 1 } } } \\ { { \displaystyle { \sum _ { j \ne i } \left| a _ { 1 j } \right| = \frac { 1 } { 2 } s < \frac { 1 } { 3 } } . } } \end{array}
$$

Therefore, we can identify a disk $D _ { 1 }$ centered at $z \leq \frac { 1 } { 6 }$ on the real line with radius $\leq \frac { 1 } { 6 }$ . The closest possible disk to it which does not overlap it, is the disk $D _ { L + 1 }$ centered at $z \geq 5 / 6$ with a radius $\leq 1 / 3$ . Therefore, since no disks intersect $D _ { 1 }$ , it covers the smallest values on the real line, and it follows that the ground state for $s < 1 / 3$ is unique. Furthermore, we have learned that the minimum gap is a constant of at least $1 / 6$ , since that is the closest distance between $D _ { 1 }$ and $D _ { L + 1 }$ . (This also proves that $| \gamma ( 0 ) \rangle$ is the unique ground state at $s = 0$ .)

Now let $s \geq 1 / 3$ and consider the matrix representation of $G ( s ) \equiv \mathbb { 1 } - H _ { S _ { 0 } } ( s )$ in the same basis:

$$
G ( s ) = \left( \begin{array} { c c c c c } { { 1 - { \frac { 1 } { 2 } } s } } & { { { \frac { 1 } { 2 } } s } } & { { } } & { { } } & { { } } \\ { { { \frac { 1 } { 2 } } s } } & { { 0 } } & { { { \frac { 1 } { 2 } } s } } & { { } } & { { } } \\ { { } } & { { \ddots } } & { { \ddots } } & { { \ddots } } & { { } } \\ { { } } & { { } } & { { } } & { { 0 } } & { { { \frac { 1 } { 2 } } s } } \\ { { } } & { { } } & { { } } & { { { \frac { 1 } { 2 } } s } } & { { { \frac { 1 } { 2 } } s } } \end{array} \right) \ .
$$

This matrix is Hermitian and has all non-negative real entries for $0 < s \le 1$ . Note that increasing powers of $G ( s )$ fill more of the matrix, and $G ( s ) ^ { L + 1 }$ has all positive entries for $0 < s \le 1$ . We can thus invoke Perron’s theorem:

Let $G$ be a Hermitian matrix with real non-negative entries. If there exists $a$ finite $k$ such that all entries of $G ^ { k }$ are positive, then $G$ ’s largest eigenvalue is positive and all other eigenvalues are strictly smaller in absolute value. The eigenvector corresponding to the largest eigenvalue is unique, and all its entries are positive.

Therefore, by Perron’s theorem, $G ( s )$ ’s largest eigenvalue $\mu$ must be positive, and the associated unique eigenvector $\vec { \alpha } = \left( \alpha _ { 1 } , \ldots , \alpha _ { L + 1 } \right)$ has $\alpha _ { i } > 0$ . Let us use this to define a matrix $P$ with entries $\begin{array} { r } { P _ { i j } = \frac { \alpha _ { j } } { \mu \alpha _ { i } } G _ { i j } \ge 0 } \end{array}$ , such that

$$
\sum _ { j } P _ { i j } = \frac { 1 } { \mu \alpha _ { i } } \sum _ { j } G _ { i j } \alpha _ { j } = 1 \ ,
$$

where we used that $\vec { \alpha }$ is an eigenvector of $G$ with eigenvalue $\mu$ . Thus $P$ is a stochastic matrix (it has only nonnegative entries and its rows sum to $^ { 1 }$ ). Now note that if $\left( \alpha _ { 1 } v _ { 1 } , \ldots \alpha _ { L + 1 } v _ { L + 1 } \right)$ is a left eigenvector of $P$ with eigenvalue $\nu / \mu$ , then $( v _ { 1 } , \ldots v _ { L + 1 } )$ is an eigenvector of $G$ with eigenvalue $\nu$ :

$$
\begin{array} { r c l } { { \displaystyle \frac { \nu } { \mu } \alpha _ { j } v _ { j } ~ = ~ \sum _ { i } \alpha _ { i } v _ { i } P _ { i j } = \sum _ { i } v _ { i } \frac { \alpha _ { j } } { \mu } G _ { i j } = \frac { \alpha _ { j } } { \mu } \sum _ { i } G _ { j i } v _ { i } } } \\ { { { } } } & { { { } } } & { { { } } } \\ { { \displaystyle \Longrightarrow \nu v _ { j } = \sum _ { i } G _ { j i } v _ { i } ~ . } } & { { ( \mathrm { C } \wp ) } } \end{array}
$$

It is straightforward to check that the reverse also holds: if $( v _ { 1 } , \ldots v _ { L + 1 } )$ is an eigenvector of $G$ with eigenvalue $\nu$ , then $\left( \alpha _ { 1 } v _ { 1 } , \ldots \alpha _ { L + 1 } v _ { L + 1 } \right)$ is a left eigenvector of $P$ with eigenvalue $\nu / \mu$ . By taking $\vec { v } = \vec { \alpha }$ , which corresponds to the largest eigenvalue ( $\nu = \mu$ ) of $G$ , it then follows that $\vec { \alpha ^ { 2 } } = \left( \alpha _ { 1 } ^ { 2 } , \dots \alpha _ { L + 1 } ^ { 2 } \right)$ is a left eigenvector of $P$ with the maximal eigenvalue 1. If we normalize $\scriptstyle { \vec { \alpha ^ { 2 } } }$ , i.e., define

$$
\vec { \Pi } = \frac { 1 } { Z } \left( \alpha _ { 1 } ^ { 2 } , \ldots \alpha _ { L + 1 } ^ { 2 } \right) , Z = \sum _ { i } \alpha _ { i } ^ { 2 } \ ,
$$

then $\vec { \Pi }$ is the limiting distribution of $P$ , i.e., $P \vec { \Pi } = \vec { \Pi }$ . We can then relate the energy gap between the highest and second highest eigenvalue (let us denote it by $\delta / \mu$ ) of

$P$ to the energy gap between the ground state energy of $H$ (given by $1 - \mu = \lambda$ ) and the first excited state (given by $1 - \delta$ )

$$
\Delta _ { \mathrm { l a r g e s t } } ( P ) = 1 - \frac { \delta } { \mu } = \frac { \mu - \delta } { \mu } = \frac { \Delta ( H _ { S _ { 0 } } ) } { 1 - \lambda } .
$$

where “largest” denotes the gap from the largest eigenvalue of $P$ to the next largest eigenvalue. We wish to bound the gap of $P$ and hence of $H ( s )$ . Let us define a non-empty set $B \subseteq \{ 1 , 2 , \dots , L + 1 \}$ satisfying $\textstyle \sum _ { i \in B } \Pi _ { i } \leq { \frac { 1 } { 2 } }$ , where $\Pi _ { i }$ are the entries of $\vec { \Pi }$ . Then the conductance of $P$ , $\varphi ( P )$ is defined as:

$$
\varphi ( P ) = \operatorname* { m i n } _ { \boldsymbol { B } } \frac { { F } ( \boldsymbol { B } ) } { \Pi ( \boldsymbol { B } ) } \ ,
$$

where

$$
\begin{array} { l } { { \displaystyle { \cal F } ( \mathcal { B } ) = \sum _ { i \in \mathcal { B } } \sum _ { j \not \in \mathcal { B } } \Pi _ { i } P _ { i j } ~ , } } \\ { { } } \\ { { \Pi ( \mathcal { B } ) = \displaystyle \sum _ { i \in \mathcal { B } } \Pi _ { i } ~ . } } \end{array}
$$

The Conductance bound (Sinclair and Jerrum, 1989) then states that

$$
\Delta _ { \mathrm { l a r g e s t } } ( P ) \geq { \frac { 1 } { 2 } } \varphi ( P ) ^ { 2 } ~ .
$$

To use the result of the Conductance bound, we would like to show that the ground state of $H ( s )$ [and hence the eigenstate associated with the largest eigenvalue of $G ( s ) ]$ is monotone, i.e., that $\alpha _ { 1 } \geq \alpha _ { 2 } \geq \cdot \cdot \cdot \geq \alpha _ { L + 1 } \geq 0$ . The case $s = 0$ is obvious, so consider $s > 0$ . First note that $G ( s )$ applied to a monotone vector generates a monotone vector, i.e., $G ( s )$ preserves monotonicity. To see, this consider $G ( s ) { \vec { v } } = { \vec { w } }$ with $\vec { v }$ monotone. The components of $\vec { w }$ are given by:

$$
\begin{array} { c } { { w _ { 1 } = \left( 1 - \displaystyle \frac 1 2 s \right) v _ { 1 } + \displaystyle \frac 1 2 s v _ { 2 } } } \\ { { { } } } \\ { { w _ { k } = \displaystyle \frac 1 2 s v _ { k - 1 } + \displaystyle \frac 1 2 s v _ { k + 1 } \ , \quad 2 \leq k \leq L } } \\ { { { } } } \\ { { w _ { L + 1 } = \displaystyle \frac 1 2 s v _ { L } + \displaystyle \frac 1 2 s v _ { L + 1 } } } \end{array}
$$

Therefore we have:

$$
\begin{array} { c c } { { w _ { 1 } - w _ { 2 } = ( 1 - s ) v _ { 1 } + \displaystyle \frac { 1 } { 2 } s \left( v _ { 2 } - v _ { 3 } \right) } } & { { \mathrm { ( C 1 5 a ) } } } \\ { { } } & { { } } \\ { { w _ { k } - w _ { k + 1 } = \displaystyle \frac { 1 } { 2 } s \left( v _ { 1 } - v _ { 2 } + v _ { 3 } - v _ { 4 } \right) ~ , } } & { { 2 \leq k \leq L - 1 } } \\ { { } } & { { } } \\ { { \mathrm { ( C 1 5 b ) } } } & { { } } \\ { { w _ { L } - w _ { L + 1 } = \displaystyle \frac { 1 } { 2 } s \left( v _ { L - 1 } - v _ { L } \right) ~ , } } & { { \mathrm { ( C 1 5 c ) } } } \end{array}
$$

which clearly are all $\geq 0$ by the monotonicity of $\vec { v }$ and $s \leq 1$ . Therefore $\vec { w }$ is also monotone.

Recall that $G ( s )$ is Hermitian, so it has an orthonormal set of eigenvectors $\{ | v _ { i } \rangle \} _ { i = 1 } ^ { L + 1 }$ with eigenvalues $\mu _ { i }$ , where $| v _ { 1 } \rangle = \vec { \alpha }$ and  we ca $\mu _ { 1 } = \mu$ $^ { 4 1 }$ Because these eigenvect find a set of coefficients $\left\{ c _ { i } \right\} _ { i = 1 } ^ { L + 1 }$

$$
\sum _ { i } c _ { i } | v _ { i } \rangle = ( 1 , . . . , 1 ) = \vec { 1 } .
$$

Then:

$$
\begin{array} { r l r } & { } & { \left( \frac { 1 } { \mu _ { 1 } } G ( s ) \right) ^ { k } \displaystyle \sum _ { i } c _ { i } | v _ { i } \rangle = \displaystyle \sum _ { i } \left( \frac { \mu _ { i } } { \mu _ { 1 } } \right) ^ { k } c _ { i } | v _ { i } \rangle \quad } \\ & { } & { \implies \left( \frac { 1 } { \mu _ { 1 } } G ( s ) \right) ^ { k } \vec { 1 } ^ { \mathrm { T } } = \displaystyle \sum _ { i } \left( \frac { \mu _ { i } } { \mu _ { 1 } } \right) ^ { k } \vec { 1 } ^ { \mathrm { T } } . } \end{array}
$$

Using $| \mu _ { i } | ~ < ~ \mu _ { 1 }$ by Perron’s theorem, we have from Eq. (C17a) that:

$$
\operatorname * { l i m } _ { k  \infty } ( \frac { 1 } { \mu _ { 1 } } G ( s ) ) ^ { k } \sum _ { i } c _ { i } | v _ { i } \rangle = c _ { 1 } | v _ { 1 } \rangle ~ ,
$$

Since the quantities $\begin{array} { r } { \bigg ( \frac { 1 } { \mu _ { 1 } } G ( s ) \bigg ) ^ { k } } \end{array}$ (for $k \geq L + 1$ ), $\textstyle \sum _ { i } c _ { i } | v _ { i } \rangle = { \vec { 1 } }$ , and $| v _ { 1 } \rangle = \vec { \alpha }$ are all positive, it follows that also $c _ { 1 } > 0$ . Since $\vec { 1 }$ is monotone and $G ( s )$ preserves monotonicity, we have finally established that $| v _ { 1 } \rangle = \vec { \alpha }$ is monotone. This then implies that $\vec { \Pi }$ [Eq. ( C9)] is monotone.

We are ready to calculate the conductance $\varphi ( P )$ . First, consider the case where the first index (of $\vec { \Pi }$ ) is in the set $\boldsymbol { B }$ , i.e., $1 \in B$ . Let $k$ be the smallest index such that $k \in B$ but $k + 1 \notin B$ . (Note that from the form of $P$ , only $P _ { 1 1 }$ , $P _ { j , j + 1 }$ , $P _ { L + 1 , L + 1 }$ are nonzero.) Then we have for $F ( B )$ :

$$
\begin{array} { r l r } {  { F ( \mathcal { B } ) = \sum _ { i \in \mathcal { B } , i \not = k } \sum _ { j \not \in \mathcal { B } } \Pi _ { i } P _ { i j } + \Pi _ { k } P _ { k , k + 1 } \geq \Pi _ { k } P _ { k , k + 1 } } } \\ & { } & { \quad = \Pi _ { k } \frac { \sqrt { \Pi _ { k + 1 } } } { \mu \sqrt { \Pi _ { k } } } [ G ( s ) ] _ { k , k + 1 } = \frac { \sqrt { \Pi _ { k } \Pi _ { k + 1 } } } { 1 - \lambda } [ G ( s ) ] _ { k , k + 1 } } \\ & { } & { \quad \geq \frac { \Pi _ { k + 1 } } { 1 - \lambda } [ G ( s ) ] _ { k , k + 1 } ~ , \ ~ ( \mathrm { C 1 9 } ) } \end{array}
$$

where the last inequality follows from the monotonicity of $\vec { \Pi }$ . Because $0 < 1 - \lambda \leq 1$ , and $[ G ( s ) ] _ { k , k + 1 } = \textstyle { \frac { 1 } { 2 } } s \geq 1 / 6$ for $s \geq 1 / 3$ , it follows that:

$$
F ( \mathcal { B } = \{ 1 , \mathrm { o t h e r s } , k \} ) \ge \frac { \Pi _ { k + 1 } } { 6 } \ .
$$

Since by definition $\Pi ( B ) \leq 1 / 2$ , then $\Pi ( B ) \ge 1 / 2$ where $\boldsymbol { B }$ is the complement of $\boldsymbol { \beta }$ , but since the largest possible

size of $\boldsymbol { B }$ is $L$ (recall that $1 \in B$ ), it follows that $\Pi ( \hat { B } ) \leq$ $L \Pi _ { k + 1 }$ , so that $\Pi _ { k + 1 } \geq 1 / ( 2 L )$ , and hence:

$$
\frac { F ( \boldsymbol { B } = \left\{ 1 , \mathrm { o t h e r s } , \boldsymbol { k } \right\} ) } { \Pi ( \boldsymbol { B } ) } \ge \frac { 1 } { 6 L } \ .
$$

Next consider the case where $1 \notin B$ . Now let $k$ be the smallest index such that $k \not \in B$ but $k + 1 \in B$ . Then:

$$
\begin{array} { l } { { \displaystyle F ( \mathcal B ) = \sum _ { i \in \mathcal B , i \ne k + 1 } \sum _ { j \notin \mathcal B } \Pi _ { i } P _ { i j } + \Pi _ { k + 1 } P _ { k + 1 , k } } } \\ { { \displaystyle \ge \Pi _ { k + 1 } P _ { k + 1 , k } \ge \frac { \Pi _ { k + 1 } } { 6 } . } } \end{array}
$$

In this case, since the maximum size of $\boldsymbol { B }$ is $L$ but it excludes the index 1, we have $\Pi ( \boldsymbol { B } ) \le L \Pi _ { k + 1 }$ , so that $F ( \boldsymbol { B } ) \ge \Pi ( \boldsymbol { B } ) / ( 6 L )$ . Therefore, we again find the condition (C21). Thus, by the conductance bound [Eq. (C13)]:

$$
\Delta ( P ) = \frac { \Delta ( H _ { S _ { 0 } } ) } { 1 - \lambda } \geq \frac 1 2 \left( \frac { 1 } { 6 L } \right) ^ { 2 } .
$$

Now since $\lambda$ is the ground state of $H _ { S _ { 0 } }$ , for any state in $| v \rangle \in S _ { 0 }$ , we must have $\langle v | H _ { S _ { 0 } } | v \rangle \geq \lambda$ . In particular:

$$
\langle \gamma ( 0 ) | H _ { S _ { 0 } } | \gamma ( 0 ) \rangle = { \frac { 1 } { 2 } } s \geq \lambda ,
$$

i.e., $\lambda \leq 1 / 2$ . This finally yields Eq. (79).

# 4. Gap bound in the entire Hilbert space

Let us now go a step further and show how the global gap (i.e., not restricted to the $S _ { 0 }$ subspace) scales with $L$ . Let $\boldsymbol { S }$ denote the subspace spanned by all legal clock states. The dimensions of this subspace will be $\dim ( S ) =$ $( L + 1 ) 2 ^ { n }$ , since we have $L + 1$ legal clock states and $2 ^ { n }$ computational states. $H ( s )$ acting on any state in $\boldsymbol { S }$ does not generate any illegal clock states, so for any $| v \rangle \in { \mathcal { S } }$ we have $H ( s ) | v \rangle \in { \mathcal { S } }$ . Similarly, for any state in the orthogonal subspace $\boldsymbol { S ^ { \perp } }$ , i.e., the subspace of illegal clock states, for any state $| v ^ { \perp } \rangle \in \mathcal { S } ^ { \perp }$ , we have $H ( s ) | v ^ { \perp } \rangle \in { \mathcal { S } } ^ { \perp }$ . Therefore, the eigenstates of $H ( s )$ below either to $\boldsymbol { S }$ or to $\mathcal { S } ^ { \perp }$ , and $H ( s )$ is block diagonal with blocks $H _ { S } ( s )$ and $H _ { S ^ { \perp } } ( s )$ that can be diagonalized independently.

Let us first restrict to $H _ { S ^ { \perp } } ( s )$ . $H _ { c }$ penalizes all illegal clock states by at least one unit of energy and acts as the identity on the computational qubits. Therefore, it shifts the entire spectrum of $\boldsymbol { S ^ { \perp } }$ by at least one unit of energy. Since the remaining terms are positive semi-definite, they cannot lower the energy. Therefore, regardless of the form of the ground state in the subspace, it has an energy of at least one unit.

Let us now restrict to $H _ { S } ( s )$ and define:

$$
| \gamma _ { j } ( \ell ) \rangle = | \alpha _ { j } ( \ell ) \rangle \otimes | 1 ^ { \ell } 0 ^ { L - \ell } \rangle _ { \mathrm { c } } ,
$$

where $| \alpha _ { j } ( \ell ) \rangle$ is the state of the circuit at time $\ell$ had the input state been given by the binary representation of $j$ (e.g., if $j = 4$ , the input configuration of the circuit would havLet een den $\left| 0 ^ { n - 3 } 1 _ { 3 } 0 _ { 2 } 0 _ { 1 } \right. )$ . Note tha spanned by $| \gamma _ { 0 } ( \ell ) \rangle ~ = ~ | \gamma ( \ell ) \rangle$ $S _ { j }$ $\{ | \gamma _ { j } ( \ell ) \rangle \} _ { \ell = 0 } ^ { L }$ $H _ { S } ( s )$ cannot mix states with different $j$ subindices (it can only propagate forward or backward in $\ell$ ), $H _ { S } ( s )$ is block diagonal in the subspaces $S _ { j }$ . Therefore, we only need to find the minimum ground state energy of $H _ { S _ { j > 0 } } ( s )$ to determine the minimum gap from $H _ { S _ { 0 } } ( s )$ .

In order to determine the ground state energy of ${ \cal H } _ { S _ { j } }$ , we notice that we can write:

$$
H _ { S _ { j } } ( s ) = H _ { 0 } ( s ) + H _ { S _ { j } , \mathrm { i n p u t } } \ , \quad j > 0
$$

where $H _ { 0 } ( s )$ has exactly the same spectral properties as $H _ { S _ { 0 } }$ except in the $S _ { j }$ subspace. The reason for this decomposition is because $H _ { \mathrm { i n p u t } }$ is zero in $S _ { 0 }$ and hence is absent from $H _ { S _ { 0 } } ( s )$ . Note that:

$$
H _ { S _ { j } , \mathrm { i n p u t } } | \gamma _ { j } ( \ell ) \rangle = \left\{ \begin{array} { l l } { k | \gamma _ { j } ( 0 ) \rangle , \ \ell = 0 } \\ { 0 \ , \ell > 0 } \end{array} \right.
$$

(recall that $H _ { \mathrm { i n p u t } }$ projects onto the 0 clock state, which is why for $\{ | \gamma _ { j } ( \ell ) \rangle \} _ { \ell = 0 } ^ { L }$ $\ell > 0$ , we can write the matrix representation of we have zero.) Therefore, in the basis $H _ { S _ { j } , \mathrm { i n p u t } }$ as:

$$
\begin{array} { r } { H _ { S _ { j } , \mathrm { i n p u t } } = \left( \begin{array} { l l l } { k } & { } & { } & { 0 } \\ { } & { 0 } & { } \\ { } & { } & { \ddots } \\ { 0 } & { } & { } & { 0 } \end{array} \right) , } \end{array}
$$

where $k \geq 1$ denotes the number of $^ { 1 }$ ’s in the binary representation of $j > 0$ . In particular, note that it is diagonal in this basis. We now use the Geometrical Lemma (Aharonov and Naveh, 2002; Kitaev et al., 2000):

Lemma 4 (Geometrical Lemma). Let $H _ { 1 }$ and $H _ { 2 }$ be two Hamiltonians with ground state energies $g _ { 1 }$ and $g _ { 2 }$ respectively. Both Hamiltonians have a ground state energy gap to the first excited state that is larger than $\Lambda$ . Let the angle between the two ground subspaces be $\theta . ^ { 4 2 }$ . Then the ground state energy $\left( g _ { 0 } \right)$ of $H _ { 0 } = H _ { 1 } + H _ { 2 }$ is at least $g _ { 1 } + g _ { 2 } + \Lambda ( 1 - \cos \theta )$ .

Let $H _ { 1 } = H _ { 0 }$ and $H _ { 2 } = H _ { S _ { 1 } , \mathrm { i n p u t } }$ . We saw that the ground state gap of $H _ { 1 }$ is $\Omega ( 1 / L ^ { 2 } )$ and that of $H _ { 2 }$ is 1, so we can take $\Lambda = \Omega ( 1 / L ^ { 2 } )$ . The ground state energy of $H _ { 2 }$ is $g _ { 2 } = 0$ . Therefore, using the Geometrical Lemma, we have $g _ { 0 } - g _ { 1 } \ge \Lambda ( 1 - \cos \theta )$ . It remains to bound the angle between the two ground spaces. From Eq. (C28), it is clear that the (degenerate) ground state of

$H _ { 2 }$ can be written as a linear combination of $\{ | \gamma _ { j } ( \ell ) \rangle \} _ { \ell = 1 } ^ { L }$ whereas the (unique) ground state of $H _ { 1 }$ can be written as a monotone vector in $\{ | \gamma _ { j } ( \ell ) \rangle \} _ { \ell = 0 } ^ { L }$ . Therefore:

$$
\begin{array} { r l } & { \displaystyle \cos \theta = \displaystyle \operatorname* { m a x } _ { \left\{ c _ { \ell ^ { \prime } } \right\} } \left. \displaystyle \sum _ { \ell = 0 } ^ { L } \alpha _ { \ell } \langle \gamma _ { j } ( \ell ) | \displaystyle \sum _ { \ell ^ { \prime } = 1 } ^ { L } c _ { \ell ^ { \prime } } | \gamma _ { j } ( \ell ^ { \prime } ) \rangle \right. } \\ & { \displaystyle \quad = \operatorname* { m a x } _ { \left\{ c _ { \ell ^ { \prime } } \right\} } \left. \displaystyle \sum _ { \ell = 1 } ^ { L } \alpha _ { \ell } c _ { \ell } \langle \gamma _ { j } ( \ell ) | \gamma _ { j } ( \ell ) \rangle \right. } \\ & { \displaystyle \quad \leq \operatorname* { m a x } _ { \left\{ c _ { \ell ^ { \prime } } \right\} } \displaystyle \sum _ { \ell = 1 } ^ { L } \alpha _ { \ell } \left. c _ { \ell } \right. \leq \sqrt { \displaystyle \frac { L } { L + 1 } } \leq 1 - \frac { 1 } { 2 L } , } \end{array}
$$

where we have used that $\vec { \alpha }$ is monotone so that $c _ { \ell } =$ $\alpha _ { \ell } \sqrt { \frac { L + 1 } { L } }$ maximizes the sum. Therefore, the global gap can be bounded from below by $\Omega ( 1 / L ^ { 3 } )$ , which is Eq. (80).

# Appendix D: Proof of the Amplification Lemma (Claim 1)

To prove Claim 1, define a new verifier $V ^ { * } ( \eta , X )$ which amounts to repeating $V ( \eta , X )$ $K$ times, where $K = \mathrm { p o l y } ( | \eta | )$ to keep the verifier efficient, and taking a majority vote on the output, i.e., $\operatorname* { P r } ( V ^ { * } ( \eta , X ) = 1 ) =$ $\textstyle \operatorname* { P r } \left( \sum _ { i = 1 } ^ { K } V _ { i } > K / 2 \right)$ , where $V _ { i } \in \{ 0 , 1 \}$ is the random number associated with the $i$ -th run of $V ( \eta , X )$ .

Now recall the multiplicative Chernoff bound:

$$
\begin{array} { r l } & { \operatorname* { P r } \left( \displaystyle \sum _ { i = 1 } ^ { K } Y _ { i } \leq \left( 1 - \beta \right) K p \right) \leq e ^ { - \beta ^ { 2 } K p / 2 } , 0 < \beta < 1 } \\ & { \operatorname* { P r } \left( \displaystyle \sum _ { i = 1 } ^ { K } Y _ { i } \geq \left( 1 + \beta \right) K p \right) \leq e ^ { - \beta ^ { 2 } K p / \left( 2 + \beta \right) } , 0 < \beta , } \end{array}
$$

for $p \ = \ \mathbb { E } ( Y )$ where $Y \in \{ 0 , 1 \}$ is a random variable. Consider first take the case where $Q ( \eta ) = 1$ . In that case, $p \geq 2 / 3$ . If we now pick $\beta = 1 - 1 / ( 2 p )$ (i.e., $1 / 4 \le \beta \le 1 / 2$ ) in the Chernoff bound, then:

$$
\begin{array} { r l r } {  { \operatorname* { P r } ( \sum _ { i = 1 } ^ { K } V _ { i } > \frac { K } { 2 } ) = 1 - \operatorname* { P r } ( \sum _ { i = 1 } ^ { K } V _ { i } \leq \frac { K } { 2 } ) } } & { } & \\ & { } & { \geq 1 - e ^ { - \frac { ( p - 1 / 2 ) ^ { 2 } K } { 2 p } } \geq 1 - e ^ { - \frac { ( 2 / 3 - 1 / 2 ) ^ { 2 } K } { 4 / 3 } } ~ . } \end{array}
$$

For the case where $Q ( \eta ) = 0$ , $p \leq 1 / 3$ , take $\beta = 1 / ( 2 p ) -$ $1 > 0$ , so that:

$$
\begin{array} { r l r } {  { \operatorname* { P r } ( \sum _ { i = 1 } ^ { K } V _ { i } > \frac { K } { 2 } ) \le \operatorname* { P r } ( \sum _ { i = 1 } ^ { K } V _ { i } \ge \frac { K } { 2 } ) } } & { } & \\ & { } & { \le e ^ { - \frac { ( p - 1 / 2 ) ^ { 2 } K } { p ( p + 1 / 2 ) } } \le e ^ { - \frac { ( 1 / 3 - 1 / 2 ) ^ { 2 } K } { ( 1 / 3 + 1 / 2 ) / 3 } } . } \end{array}
$$

This shows that $\mathrm { M A } ( 2 / 3 , 1 / 3 ) = \mathrm { M A } ( 1 - e ^ { - | \eta | ^ { g } } , e ^ { - | \eta | ^ { g } } )$ , since $K = \mathrm { p o l y } ( | \boldsymbol { \eta } | )$ .

To show that $\mathrm { M A } ( c , c - 1 / | \eta | ^ { g } ) \subseteq \mathrm { M A } ( 2 / 3 , 1 / 3 )$ , it is sufficient to show that when $Q ( \eta ) = 0$ it is exponentially unlikely that Merlin is able to fool Arthur that $Q ( \eta ) =$ 1. Therefore consider the probability of fooling Arthur, i.e., $\operatorname* { P r } \left( V ^ { * } ( \eta , X ) = 1 \right) > c$ when $Q ( \eta ) = 0$ . Take $p =$ $\operatorname* { P r } \left( V ( \eta , X ) = 1 \right) = c - 1 / | \eta | ^ { g }$ . Then:

$$
\begin{array} { l } { \displaystyle \operatorname* { P r } \left( \mathrm { A r t h u r ~ f o o l e d } \right) = \operatorname* { P r } \left( \sum _ { i = 1 } ^ { K } V _ { i } \geq K c \right) } \\ { \displaystyle \qquad = \operatorname* { P r } \left( \frac { 1 } { K } \sum _ { i = 1 } ^ { K } V _ { i } \geq p + \epsilon \right) \ , } \end{array}
$$

where we take $\epsilon = 1 / | \eta | ^ { g }$ . Recall the additive Chernoff bound:

$$
\operatorname* { P r } \left( \frac { 1 } { K } \sum _ { i = 1 } ^ { K } Y _ { i } \geq p + \epsilon \right) \leq e ^ { - K D ( p + \epsilon \| p ) } ~ ,
$$

where

$$
D ( x \| y ) = x \ln { \frac { x } { y } } + ( 1 - x ) \ln { \frac { 1 - x } { 1 - y } }
$$

is the Kullback-Leibler divergence. Expanding $D ( p +$ $\begin{array} { r } { \epsilon \| p ) = \frac { \epsilon ^ { 2 } } { 2 p ( 1 - p ) } + O ( \epsilon ^ { 3 } ) } \end{array}$ , we see that if $K = \epsilon ^ { - 2 - \varepsilon }$ , where $0 ~ < ~ \varepsilon ~ \ll ~ 1$ , then we can exponentially suppress the probability that Arthur is fooled by Merlin while keeping $K = \mathrm { p o l y } ( | \boldsymbol { \eta } | )$ .

# Appendix E: Perturbative Gadgets

In this section we review the subject of perturbative gadgets, which have played an important role in the reduction of the locality of interactions in the proofs of QMA completeness and the universality of AQC. These tools are generally useful. Our discussion is based primarily on (Jordan and Farhi, 2008) [see also (Bravyi et al., 2008a)]. To set up the appropriate tools we first briefly review degenerate perturbation theory.

# 1. Degenerate Perturbation Theory \`a la (Bloch, 1958)

Consider $H = H _ { 0 } + \lambda V$ where $H _ { 0 }$ has a $d$ -dimensional degenerate ground subspace $\mathcal { E } _ { 0 }$ with energy 0. Let $| \psi _ { 1 } \rangle , \dots | \psi _ { d } \rangle$ be the lowest $d$ energy eigenstates of $H$ with energies $E _ { 1 } , \ldots , E _ { d }$ , and let their span define the subspace $\varepsilon$ . The goal is to define a perturbative expansion (in $\lambda$ ) for the effective Hamiltonian $H _ { \mathrm { e f f } }$ of $H$ , defined as:

$$
H _ { \mathrm { e f f } } ( H , d ) = \sum _ { j = 1 } ^ { d } E _ { j } | \psi _ { j } \rangle \langle \psi _ { j } | ~ .
$$

We will show that this expansion converges provided $\lambda$ satisfies

$$
\| \lambda V \| < \gamma / 4 \ ,
$$

where $\gamma$ is the gap to the first excited state of $H _ { 0 }$ . We first show how to construct this effective Hamiltonian in terms of other, more convenient operators.

Let $P _ { 0 }$ be the projection onto $\dot { \varepsilon _ { \mathrm { 0 } } }$ , and define:

$$
| \alpha _ { j } \rangle = P _ { 0 } | \psi _ { j } \rangle \ , \quad j = 1 , \ldots , d \ .
$$

For Eq. $\lambda$ sufficiently smalE2)], the states l amount to satisfyingare linearly indepen-$\{ | \alpha _ { j } \rangle \} _ { j = 1 } ^ { d }$   
dent since the states $\{ | \psi _ { j } \rangle \} _ { j = \underline { { 1 } } } ^ { d } $ are only slightly perom the eigenstaare not necess s of ily o $H _ { 0 }$ . Note that the statesogonal or normalized.   
$\{ \vert \alpha _ { j } \rangle \} _ { j = 1 } ^ { d }$ $\boldsymbol { \mathcal { U } }$

$$
\begin{array} { l } { { \mathcal { U } | \alpha _ { j } \rangle = | \psi _ { j } \rangle ~ , ~ j = 1 , \ldots , d } } \\ { { \mathcal { U } | \phi \rangle = 0 ~ , ~ \forall | \phi \rangle \in \mathcal { E } _ { 0 } ^ { \perp } ~ . } } \end{array}
$$

This means that:

$$
\begin{array} { r c l } { { P _ { 0 } { \mathcal U } | \alpha _ { j } \rangle } } & { { = } } & { { P _ { 0 } | \psi _ { j } \rangle = | \alpha _ { j } \rangle } } \\ { { } } & { { } } & { { } } \\ { { } } & { { } } & { { \Longrightarrow P _ { 0 } ^ { 2 } { \mathcal U } | \alpha _ { j } \rangle = P _ { 0 } { \mathcal U } | \alpha _ { j } \rangle = P _ { 0 } | \alpha _ { j } \rangle } } \\ { { } } & { { } } & { { } } \\ { { } } & { { } } & { { \Longrightarrow P _ { 0 } { \mathcal U } = P _ { 0 } ~ . } } \end{array}
$$

Let $\tilde { \mathcal { U } }$ be the operator satisfying:

$$
\begin{array} { l } { { \tilde { \mathcal { U } } | \psi _ { j } \rangle = | \alpha _ { j } \rangle ~ , ~ j = 1 , \dots , d } } \\ { { \tilde { \mathcal { U } } | \phi \rangle = 0 ~ , ~ \forall | \phi \rangle \in \mathcal { E } ^ { \perp } ~ . } } \end{array}
$$

Note that $\tilde { \mathcal { U } }$ is not the inverse of $\boldsymbol { u }$ because $\boldsymbol { \mathcal { U } }$ is not invertible on the entire Hilbert space. Also, $\tilde { \mathcal { U } }$ is not $P _ { 0 }$ because of Eq. (E6b) (it annihilates all states outside of $\varepsilon$ ). Note that:

$$
\mathcal { U } P _ { 0 } \tilde { \mathcal { U } } | \psi _ { j } \rangle = | \psi _ { j } \rangle ~ .
$$

Now define:

$$
\mathcal { A } = \lambda P _ { 0 } V \mathcal { U } .
$$

Note that the stawith eigenvalues $\{ | \alpha _ { i } \rangle \} _ { i = 1 } ^ { d }$ are right eigenvectors of espectively: $\boldsymbol { A }$ $E _ { 1 } , \ldots , E _ { d }$

$$
\begin{array} { r l r } {  { A | \alpha _ { j } \rangle = \lambda P _ { 0 } V | \psi _ { j } \rangle = P _ { 0 } ( H _ { 0 } + \lambda V ) | \psi _ { j } \rangle = P _ { 0 } E _ { j } | \psi _ { j } \rangle } } \\ & { } & { \quad = E _ { j } | \alpha _ { j } \rangle ~ , ~ \mathrm { ( E } } \end{array}
$$

where we used that $P _ { 0 } H _ { 0 } = 0$ because the eigenvalue of the ground subspace of $H _ { 0 }$ is zero. The effective Hamiltonian associated with $H$ can now be constructed using $\mathcal { U } , \tilde { \mathcal { U } } , \mathcal { A }$ :

$$
H _ { \mathrm { e f f } } ( { \cal H } , d ) = \mathcal { U } \mathcal { A } \tilde { \mathcal { U } } .
$$

To see this note that:

$$
\begin{array} { r l } & { \mathcal { U } \mathcal { A } \tilde { \mathcal { U } } | \phi \rangle = 0 \ , \quad \forall | \phi \rangle \in \mathcal { E } ^ { \perp } } \\ & { \mathcal { U } \mathcal { A } \tilde { \mathcal { U } } | \psi _ { j } \rangle = \mathcal { U } \mathcal { A } | \alpha _ { j } \rangle = E _ { j } \mathcal { U } | \alpha _ { j } \rangle = E _ { j } | \psi _ { j } \rangle \ , } \end{array}
$$

which is identical to the action of $H _ { \mathrm { e f f } }$ on a complete set of vectors. The strategy is now to find a perturbative expansion for $\boldsymbol { u }$ (we will not need the explicit expansion of $\tilde { \mathcal { U } }$ , so we do not provide it here), construct $\boldsymbol { A }$ using UEq. ( $\mathrm { E 8 }$ ), find $\{ | \alpha _ { j } \rangle \} _ { j = 1 } ^ { d }$ and $\{ E _ { j } \} _ { j = 1 } ^ { d }$ Aas, respectively, the right eigenvectors and eigenvalues of $\mathcal { A }$ , and apply $\boldsymbol { \mathcal { U } }$ to $\left| \alpha _ { j } \right.$ to get a perturbative expansion for $| \psi _ { j } \rangle$ .

It can be shown that the desired perturbative expansion of $\boldsymbol { u }$ and $\mathcal { A }$ is given by:

$$
\begin{array} { l } { \displaystyle \mathcal { U } = P _ { 0 } + \sum _ { m = 1 } ^ { \infty } \mathcal { U } _ { m } } \\ { \displaystyle \mathcal { A } = P _ { 0 } V \sum _ { m = 1 } ^ { \infty } \mathcal { U } _ { m } = \sum _ { m = 1 } ^ { \infty } A _ { m } ~ , } \end{array}
$$

where

$$
\mathcal { U } _ { m } = \sum _ { \stackrel { \ell _ { 1 } \geq 1 , \ell _ { 2 } \geq 0 , \ldots , \ell _ { m } \geq 0 } { \ell _ { 1 } + \cdots + \ell _ { m } = m } } ( S _ { \ell _ { 1 } } \lambda V ) ( S _ { \ell _ { 2 } } \lambda V ) \ldots ( S _ { \ell _ { m } } \lambda V ) P _ { 0 } ,
$$

$$
S _ { \ell } = \left\{ \begin{array} { r } { { \frac { 1 } { ( - H _ { 0 } ) ^ { \ell } } ( \mathbb { 1 } - P _ { 0 } ) \ , \ \ell > 0 } } \\ { { - P _ { 0 } \ , \ \ell = 0 } } \end{array} \right. \ .
$$

The series in Eq. (E12) converges for $\| \lambda V \| < \gamma / 4$ . To see this note that:

$$
\begin{array} { l } { \displaystyle \| \mathcal { U } \| = \| \mathcal { U } _ { 0 } + \sum _ { m = 1 } ^ { \infty } \mathcal { U } _ { m } \| \le \| \mathcal { U } _ { 0 } \| + \sum _ { m = 1 } ^ { \infty } \| \mathcal { U } _ { m } \| } \\ { \displaystyle \quad \le 1 + \sum _ { m = 1 } ^ { \infty } \lambda ^ { m } { \sum } ^ { \prime } \| S _ { \ell _ { 1 } } V S _ { \ell _ { 2 } } \dots S _ { \ell _ { m } } V P _ { 0 } \| } \\ { \displaystyle \le 1 + \sum _ { m = 1 } ^ { \infty } \lambda ^ { m } { \sum } ^ { \prime } \| S _ { \ell _ { 1 } } \| \dots \| S _ { \ell _ { m } } \| \| V \| \ , } \end{array}
$$

where the sum $\Sigma ^ { \prime }$ involves summing all the different ways to add up to $m$ while satisfying convexity, i.e., $\ell _ { 1 } + \ell _ { 2 } +$ $\cdots \ell _ { p } \geq p$ . Because of the form of $S _ { \ell }$ [Eq. (E13b)], we have:

$$
\| S _ { \ell } \| = \left( \frac { 1 } { E _ { 1 } ^ { ( 0 ) } } \right) ^ { \ell } = \frac { 1 } { \gamma ^ { \ell } } ~ ,
$$

where $E _ { 1 } ^ { ( 0 ) }$ is the energy of the first excited state of $H _ { 0 }$ (corresponds to the state that minimizes $H _ { 0 } Q _ { 0 }$ to calculate the operator norm). Therefore, we have:

$$
\| \mathcal { U } \| \leq 1 + \sum _ { m = 1 } ^ { \infty } \lambda ^ { m } \sum ^ { \prime } \frac { \| V \| ^ { m } } { \gamma ^ { m } } \ .
$$

The sum $\Sigma ^ { \prime }$ is less than the number of ways to add up to $\binom { 2 m - 1 } { m }$ $m$ using . Ho $m$ non-negative integers, which is given by ever, since $\sum _ { j = 0 } ^ { 2 m - 1 } { \binom { 2 m - 1 } { j } } = 2 ^ { 2 m - 1 }$ , it is

clear that $\binom { 2 m - 1 } { m } ~ \leq ~ 2 ^ { 2 m - 1 }$ . Therefore, we can upper bound the sum with this value:

$$
\| \boldsymbol { \mathcal { U } } \| \leq 1 + \sum _ { m = 1 } ^ { \infty } 2 ^ { 2 m - 1 } \frac { \| \lambda V \| ^ { m } } { \gamma ^ { m } } \ .
$$

This series converges if the condition for $\lambda$ in Eq. (E2) is satisfied.

# 2. Perturbative Gadgets

For a $k$ -local target Hamiltonian $H ^ { \mathrm { T } }$ , the goal is to construct a 2-local “gadget” Hamiltonian $H ^ { \mathrm { G } }$ , whose low energy spectrum (captured by an effective Hamiltonian $H _ { \mathrm { e f f } }$ ) approximates the spectrum of $H ^ { \mathrm { T } }$ . In order to do so, we shall use the expression in Eq. (E10) for the effective Hamiltonian in terms of the operators $\boldsymbol { \mathcal { U } }$ and $\mathcal { A }$ and use their perturbative expansion from the previous subsection. We shall show that for our gadget Hamiltonian, the perturbative expansion of the effective Hamiltonian matches that of the target Hamiltonian.

The perturbative gadget we review here uses a strongly bound set of ancillas, coupled to the target qubits via weaker interactions, where the latter are treated as a perturbation. $H ^ { \mathrm { T } }$ is then generated in low order perturbation theory of the combined system consisting of both ancilla and target qubits. Such gadgets first appeared in the proof of QMA-completeness of the 2-local Hamiltonian problem via a reduction from 3-local Hamiltonian, where they were used to construct effective 3-body interactions from 2-body ones (Kempe et al., 2006).

Let $H _ { s }$ denote a $k$ -local term. For the $i$ -th qubit in $H _ { s }$ , we associate an arbitrary direction in $\mathbb { R } ^ { 3 }$ denoted by $\hat { n } _ { s , i }$ . A general $k$ -local target Hamiltonian acting on $n$ qubits can then be expressed as:

$$
H ^ { \mathrm { T } } = \sum _ { s = 1 } ^ { r } c _ { s } H _ { s } \ ,
$$

with $H _ { s } = \sigma _ { s , 1 } \sigma _ { s , 2 } \ldots \sigma _ { s , k }$ where $\sigma _ { s , j } = \hat { n } _ { s , j } \cdot \vec { \sigma } _ { s , j }$ . The goal is to simulate $H ^ { \mathrm { T } }$ using only 2-local interactions. Toward this end, introduce $k$ ancilla qubits for each $H _ { s }$ , for a total of $r k$ ancilla qubits. Define

$$
\begin{array} { l } { { \displaystyle { H ^ { \mathrm { G } } = H ^ { \mathrm { A } } + \lambda V = \sum _ { s = 1 } ^ { r } H _ { s } ^ { \mathrm { A } } + \lambda \sum _ { s = 1 } ^ { r } V _ { s } } } } \\ { { \displaystyle { H _ { s } ^ { \mathrm { A } } = \sum _ { i < j } ^ { k } \frac { 1 } { 2 } \left( 1 - Z _ { s , i } Z _ { s , j } \right) } } } \\ { { \displaystyle V _ { s } = \sum _ { j = 1 } ^ { k } c _ { s , j } \sigma _ { s , j } \otimes X _ { s , j } } } \\ { { \displaystyle c _ { s , j } = \left\{ \begin{array} { l l } { { c _ { s } , } } & { { j = 1 } } \\ { { 1 , } } & { { j \neq 1 } } \end{array} \right. , } } \end{array}
$$

where $X _ { s , j } , Z _ { s , j }$ are the Pauli- $( x , z )$ operators on the $j$ -th ancilla qubit of $H _ { s }$ . Note that the ground state of $H _ { s } ^ { \mathrm { A } }$ is given by the span of $\left\{ | 0 _ { 1 } \dots . . . 0 _ { k } \rangle _ { s } ^ { \mathrm { A } } , | 1 _ { 1 } \dots . . . 1 _ { k } \rangle _ { s } ^ { \mathrm { A } } \right\}$ .

Consider the $k$ -local ancilla operator $X _ { s } ~ \equiv ~ X _ { s , 1 } \otimes$ $X _ { s , 2 } \otimes \cdots \otimes X _ { s , k }$ his operator clearly commuand the set of operators $H _ { \mathrm { G } }$ $H _ { \mathrm { G } }$ $\{ X _ { s } \} _ { s = 1 } ^ { r }$ share a set of eigenstates. The operator $X _ { s }$ has eigenvalues $\pm 1$ , each with degeneracy $2 ^ { k - 1 }$ (to see this simply write $X _ { s }$ in the basis $\{ | \pm \rangle _ { s , 1 } \otimes | \pm \rangle _ { s , 2 } \otimes \cdot \cdot \cdot \otimes | \pm \rangle _ { s , k } \}$ ). Therefore, $H ^ { \mathrm { G } }$ can be block diagonalized into $2 ^ { r }$ blocks, where each block corresponds to a fixed $X _ { s } ~ = ~ \pm 1$ for $s = 1 , \ldots , r$ with dimension $2 ^ { n } 2 ^ { r ( k - 1 ) }$ . Let $H _ { + } ^ { \mathrm { G } }$ denote the block with $X _ { s } = 1 \mathrm { ~ , } \forall s$ .

Note that since $H _ { + } ^ { \mathrm { G } }$ will be used to approximate $H ^ { \mathrm { G } }$ , the system will need to be initialized to have $X _ { s } = 1 \mathrm { ~ , } \forall s$ . The eigenstate of $X _ { s }$ with eigenvalue $^ { 1 }$ is given by

$$
| + \rangle _ { s } = \frac { 1 } { \sqrt { 2 } } \left( | 0 _ { 1 } \dots . . . 0 _ { k } \rangle _ { s } + | 1 _ { 1 } . . . . 1 _ { k } \rangle _ { s } \right) ,
$$

so the ancilla qubits must be initialized to be in the state $\otimes _ { r = 1 } ^ { s } | + \rangle _ { s }$ .

We wish to show that the low energy spectrum of $H _ { + } ^ { \mathrm { G } }$ approximates the spectrum of $H ^ { \mathrm { T } }$ . Our task is to calculate $H _ { \mathrm { e f f } } ( H _ { + } ^ { \mathrm { G } } , 2 ^ { n } )$ [in the notation of Eq. (E1)] perturbatively to $k$ -th order in $\lambda$ . $\lambda V$ will perturb the ground subspace of $H ^ { \mathrm { A } }$ in two ways:

1. It shifts the energy of the entire subspace;

2. It splits the degeneracy of the ground subspace beginning at $k$ -th order in perturbation theory. It is this splitting that will allow us to mimic the spectrum of $H _ { \mathrm { T } }$ .

We analyze the shift and splitting separately. To do this, define:

$$
\tilde { H } _ { \mathrm { e f f } } ( H , d , \Delta ) \equiv H _ { \mathrm { e f f } } ( H , d ) - \Delta \Pi ,
$$

where $\mathrm { I I }$ is the projection onto the space spanned by $\{ | E _ { j } \rangle \} _ { j = 1 } ^ { d }$ . Note that the eigenstates of $\ddot { H } _ { \mathrm { e f f } }$ and $H _ { \mathrm { e f f } }$ are identical, and the energy gaps between energy levels are identical too.

tart with, so that $r \ = \ 1$ $\boldsymbol { H ^ { \mathrm { T } } } =$ $\sigma _ { 1 } \sigma _ { 2 } \ldots \sigma _ { k }$ $\begin{array} { r } { V = \sum _ { j = 1 } ^ { k } \sigma _ { j } \otimes X _ { j } } \end{array}$ $\begin{array} { r } { H ^ { \mathrm { A } } \ = \ \sum _ { i = 1 } ^ { k } \sum _ { j = i + 1 } ^ { k } \frac { 1 } { 2 } \left( 1 - Z _ { i } Z _ { j } \right) } \end{array}$ i=1 j=i+1 2. We first wish to construct $\boldsymbol { A }$ [Eq. $\mathrm { E 8 }$ )] for $H _ { + } ^ { \mathrm { G } }$ . Note that $H ^ { \mathrm { A } }$ has a ground state of zero energy (corresponds to all qubits with $Z _ { i } = 1$ or all qubits with $Z _ { i } = - 1$ ), and the first excited state has energy $\gamma = k - 1$ (let $Z _ { 1 } ~ = ~ - 1$ , all the rest are $+ 1$ ). Furthermore:

$$
\| V \| = \| \sum _ { j = 1 } ^ { k } \sigma _ { j } \otimes X _ { j } \| \leq \sum _ { j = 1 } ^ { k } \| \sigma _ { j } \otimes X _ { j } \| = k ~ .
$$

Therefore, by Eq. (E2), the perturbative expansion will converge if $\lambda \ < \ \frac { k - 1 } { 4 k }$ . Because of the form of $\mathcal { A }$ [Eq. (E12b)], all $A _ { m }$ terms are sandwiched between $P _ { 0 }$ operators. Thus, all non-zero terms in $\boldsymbol { A }$ must take states in $\mathcal { E } _ { 0 }$ and return them to states in $\dot { \varepsilon _ { \mathrm { 0 } } }$ . Since we have restricted to the $X = \otimes _ { i = 1 } ^ { k } X _ { i } = + 1$ sector, $\mathcal { E } _ { 0 }$ is restricted to have the ancilla qubits in the $| + \rangle$ state [Eq. (E20)]. Therefore, we can write:

$$
P _ { 0 } = \mathbb { 1 } \otimes P _ { + } ~ ,
$$

where $P _ { + }$ is the projection onto the $| + \rangle$ ancilla state.

Each term in $\begin{array} { r } { V = \sum _ { j = 1 } ^ { k } \sigma _ { j } \otimes X _ { j } } \end{array}$ only flips a single ancilla qubit. Therefore, in order for $\mathcal { A }$ take a state out of $\mathcal { E } _ { 0 }$ and return it, the power of $V$ must either flip all ancilla qubits or flip some and return them back to their original value. The former process (flipping all qubits) first happens at $k$ -th order in perturbation theory. The latter process (flipping and returning) can happen at lower orders than $k$ , but $\mathcal { A }$ is then proportional to $P _ { 0 }$ since the product of $V$ ’s effectively cancel. To see how this works, consider $\boldsymbol { A }$ up to second order for $k > 2$ . From the perturbation expansion [Eq. (E12b)] we have:

$$
\begin{array} { r } { A _ { \le 2 } = \lambda P _ { 0 } V P _ { 0 } + \lambda ^ { 2 } P _ { 0 } V S _ { 1 } V P _ { 0 } \ , } \end{array}
$$

but $P _ { 0 } V P _ { 0 } = 0$ since $V | + \rangle$ is orthogonal to $| + \rangle$ . On the other hand, $V P _ { 0 }$ takes the system to a state with energy $k - 1$ for $H ^ { \mathrm { A } }$ , so $S _ { 1 } V P _ { 0 } = - V P _ { 0 } / ( k - 1 )$ . Therefore:

$$
A _ { \le 2 } = - \frac { \lambda ^ { 2 } } { k - 1 } P _ { 0 } V ^ { 2 } P _ { 0 } \ .
$$

Now note that:

$$
V ^ { 2 } = \sum _ { i } \left( \sigma _ { i } \otimes X _ { i } \right) ^ { 2 } + \sum _ { i \ne j } \left( \sigma _ { i } \otimes X _ { i } \right) \left( \sigma _ { j } \otimes X _ { j } \right) \ .
$$

The cross-terms are annihilated by $P _ { 0 } \cdot P _ { 0 }$ since they take the state out of $\mathcal { E } _ { 0 }$ . The diagonal term is proportional to the identity on the ancilla qubits, so we have:

$$
\ A _ { \le 2 } = - { \frac { \lambda ^ { 2 } } { k - 1 } } \Omega P _ { 0 } \ ,
$$

where $\Omega$ is an operator that depends on the particular orientation of the $\sigma _ { j }$ ’s. This argument extends to order $k - 1$ so that:

$$
\ A _ { \leq k - 1 } = \sum _ { m \ \mathrm { e v e n } } \lambda ^ { m } \Omega _ { m } P _ { 0 } \ .
$$

At order $k$ , something new happens. There are now crossterm that involve all $X _ { i }$ ’s once, i.e.,

$$
\lambda ^ { k } P _ { 0 } \left( \sigma _ { 1 } \otimes X _ { 1 } \right) S _ { 1 } \left( \sigma _ { 2 } \otimes X _ { 2 } \right) S _ { 1 } \ldots S _ { 1 } \left( \sigma _ { k } \otimes X _ { k } \right) P _ { 0 } \ .
$$

The $S _ { 1 }$ operator measures the successive change in energy of the system to give an overall constant of:

$$
\begin{array} { r l r } {  { ( - \frac { 1 } { k - 1 } ) ( - \frac { 1 } { 2 ( k - 2 ) } ) \ldots ( - \frac { 1 } { ( k - 1 ) 1 } ) } } \\ & { } & { = \displaystyle \prod _ { j = 1 } ^ { k - 1 } ( - \frac { 1 } { j ( k - j ) } ) = \frac { ( - 1 ) ^ { k - 1 } } { ( k - 1 ) ! ^ { 2 } } ~ . } \end{array}
$$

Therefore, the cross-terms (of which there are $k !$ , since the operators can be multiplied in any order) then take the form:

$$
- \frac { ( - \lambda ) ^ { k } k ! } { ( k - 1 ) ! ^ { 2 } } P _ { 0 } \left( \sigma _ { 1 } \dots \sigma _ { k } \otimes X \right) P _ { 0 } ~ .
$$

Thus:

$$
\mathcal { A } _ { \leq k } = f ( \lambda ) P _ { 0 } - \frac { k ( - \lambda ) ^ { k } } { ( k - 1 ) ! } P _ { 0 } \left( H ^ { \mathrm { T } } \otimes X \right) P _ { 0 } ~ ,
$$

where $f ( \lambda )$ is some $k$ -th order polynomial in $\lambda$ , with coefficients that depend on $H ^ { \mathrm { T } }$ . Using the form of $H _ { \mathrm { e f f } }$ in Eq. (E10), we have:

$$
\begin{array} { r l r } {  { H _ { \mathrm { e f f } } ( H _ { - } ^ { \mathrm { G } } , 2 ^ { n } ) = f ( \lambda ) \mathcal { U } P _ { 0 } \tilde { \mathcal { U } } } } & { \mathrm { ( E ) } } \\ & { } & { - \mathcal { U } ( \frac { k ( - \lambda ) ^ { k } } { ( k - 1 ) ! } P _ { 0 } ( H ^ { \mathrm { T } } \otimes X ) P _ { 0 } + O ( \lambda ^ { k + 1 } ) ) \tilde { \mathcal { U } } ~ . } \end{array}
$$

Recall that $\mathcal { U } P _ { 0 } \tilde { \mathcal { U } } | \psi _ { j } \rangle = | \psi _ { j } \rangle$ [Eq. E7] so ${ \mathcal { U } } P _ { 0 } { \tilde { \mathcal { U } } }$ acts as the identity in $\varepsilon$ so that the first term in Eq. (E32) can be dropped. Furthermore, we can replace $\boldsymbol { \mathcal { U } }$ and $\ddot { \mathcal { U } }$ in the second term by their $\lambda ^ { 0 }$ counterpart since we are only keeping terms to order $k$ and the term in the parenthesis is already of order $k$ . Therefore:

$$
\begin{array} { l } { { \displaystyle \tilde { H } _ { \mathrm { e f f } } ( H _ { + } ^ { \mathrm { G } } , 2 ^ { n } , f ( \lambda ) ) = - \frac { k ( - \lambda ) ^ { k } } { ( k - 1 ) ! } P _ { 0 } \left( H ^ { \mathrm { T } } \otimes X \right) P _ { 0 } } } \\ { { \displaystyle ~ + O ( \lambda ^ { k + 1 } ) \qquad ( \mathrm { E 3 3 } ) } } \\ { { \displaystyle ~ = - \frac { k ( - \lambda ) ^ { k } } { ( k - 1 ) ! } \left( H ^ { \mathrm { T } } \otimes P _ { + } \right) + O ( \lambda ^ { k + 1 } ) ~ . } } \end{array}
$$

This shows that the target Hamiltonian $H ^ { \mathrm { T } }$ appears as the leading order term in the effective Hamiltonian that describes the $2 ^ { n }$ -Hilbert space of the $n$ target qubits, albeit with a diminished magnitude of order $\lambda ^ { k } / ( k - 1 ) !$ .

Let us now consider the general $r$ case, i.e., the Hamiltonian in Eq. (E18). We note that just as in the $r = 1$ case, $H ^ { \mathrm { A } }$ again has an energy gap of $k - 1$ . Generalizing from Eq. (E22), the perturbative expansion then converges for:

$$
\lambda < \frac { k - 1 } { 4 \vert \vert V \vert \vert } \ .
$$

In the sector where $X _ { s } = + 1$ , $H ^ { \mathrm { A } }$ has the state $\otimes _ { s = 1 } ^ { r } | + \rangle _ { s }$ as a ground state. Since $H ^ { \mathrm { A } }$ acts as the identity on the computational qubits, the ground state is $2 ^ { n }$ -fold degenerate.

In the perturbation expansion for $\mathcal { A }$ , products of $V$ again appear. Each $V _ { s }$ acts on a different ancilla register. Therefore, at order $k$ , cross-terms of different $V _ { s }$ ’s cannot flip all $k$ ancilla qubits in a register, so they are annihilated by $P _ { 0 } \cdot P _ { 0 }$ . The only cross-terms that contribute are $k$ products of a given $s$ where each ancilla qubit appears once. Therefore, the natural generalization of the previous result is recovered, namely, Eq. (E33) continues to hold with $H ^ { \mathrm { T } }$ replaced by the sum over $r$ terms as in Eq. (E18), where again $f ( \lambda )$ is some polynomial in $\lambda$ of order $k$ with coefficients that depend on $c _ { s } H _ { s }$ , and where $P _ { + }$ is the projector onto $\otimes _ { s } | + \rangle _ { s }$ .

Note that the convergence condition (E34) requires the interaction term $V$ to be stronger than the effective interaction it generates, which scales as $\lambda ^ { k }$ [as can be seen from Eq. (E33)]. This may pose implementation difficulties, since a practical device is likely to have only a limited range of interaction strengths. Weaker gadgets can be implemented that circumvent this problem, albeit at the cost of a larger overhead of ancillary qubits (Cao and Nagaj, 2015). The idea is to replace strong interactions by repetition of interactions with “classical” ancillas. Additional gadgets simplifications and resource reductions were proposed in (Cao et al., 2015).

# REFERENCES

Aaronson, S. (2010), arXiv:1009.5104 .   
Aaronson, S. (2015), Nat Phys 11 (4), 291.   
Adachi, S. H., and M. P. Henderson (2015), arXiv:1510.06356   
Aharonov, D., W. van Dam, J. Kempe, Z. Landau, S. Lloyd, and O. Regev (2007), SIAM J. Comput. 37 (1), 166.   
Aharonov, D., D. Gottesman, S. Irani, and J. Kempe (2009), Communications in Mathematical Physics 287 (1), 41.   
Aharonov, D., and T. Naveh (2002), arXiv:quant-ph/0210077   
Aharonov, D., and A. Ta-Shma (2003), in Proceedings of the Thirty-fifth Annual ACM Symposium on Theory of Computing, STOC ’03 (ACM, New York, NY, USA) pp. 20–29.   
Albash, T., and D. Lidar (2017), Rev. Mod. Phys. , to be published.   
Altshuler, B., H. Krovi, and J. Roland (2010), Proceedings of the National Academy of Sciences 107 (28), 12446.   
Amara, P., D. Hsu, and J. E. Straub (1993), The Journal of Physical Chemistry, The Journal of Physical Chemistry 97 (25), 6715.   
Ambainis, A., and O. Regev (2004), arXiv:quant-ph/0411152   
Amico, L., R. Fazio, A. Osterloh, and V. Vedral (2008), Reviews of Modern Physics 80 (2), 517.   
Amin, M. H., E. Andriyash, J. Rolfe, B. Kulchytskyy, and R. Melko (2016), arXiv:1601.02036   
Amin, M. H. S. (2009), Phys. Rev. Lett. 102, 220401.   
Amin, M. H. S., and V. Choi (2009), Physical Review A 80 (6), 062326.   
Andriyash, E., and M. H. Amin (2017), ArXiv e-prints arXiv:1703.09277 [quant-ph].   
Apolloni, B., C. Carvalho, and D. de Falco (1989), Stochastic Processes and their Applications 33 (2), 233.   
Apolloni, B., N. Cesa-Bianchi, and D. de Falco (1988), in Proceedings of the Ascona/Locarno Conference, p. 97.   
Arecchi, F. T., E. Courtens, R. Gilmore, and H. Thomas (1972), Phys. Rev. A 6, 2211.   
Aspuru-Guzik, A., A. D. Dutoi, P. J. Love, and M. Head-Gordon (2005), Science 309 (5741), 1704.   
Averin, D. V. (1998), Solid State Communications 105 (10), 659.   
Avron, J. E., and A. Elgart (1999), Commun. Math. Phys. 203 (2), 445.   
Awerbuch, B. (1985), Journal of the ACM (JACM) 32 (4), 804.   
Azinovi´c, M., D. Herr, B. Heim, E. Brown, and M. Troyer (2016), arXiv:1607.03329   
Babai, L. (2015), arXiv:1512.03547 .   
Babbush, R., V. Denchev, N. Ding, S. Isakov, and H. Neven (2014a), arXiv:1406.4203   
Babbush, R., P. J. Love, and A. Aspuru-Guzik (2014b), Scientific Reports 4, 6603 EP   
Bapst, V., and G. Semerjian (2012), Journal of Statistical Mechanics: Theory and Experiment 2012 (06), P06007.   
Barabasi, A. L., and R. Albert (1999), Science 286 (5439), 509.   
Batu, T., L. Fortnow, R. Rubinfeld, W. D. Smith, and P. White (2000), in Proceedings 41st Annual Symposium on Foundations of Computer Science, pp. 259–269.   
Bauer, B., L. Wang, I. Pizorn, and M. Troyer (2015), arXiv:1501.06914   
Becker, A., J.-S. Coron, and A. Joux (2011), “Improved generic algorithms for hard knapsacks,” in Advances in Cryptology – EUROCRYPT 2011: 30th Annual International Conference on the Theory and Applications of Cryptographic Techniques, Tallinn, Estonia, May 15-19, 2011. Proceedings, edited by K. G. Paterson (Springer Berlin Heidelberg, Berlin, Heidelberg) pp. 364–385.   
Behrman, E. C., and J. E. Steck (2016), arXiv:1603.01752 .   
Benedetti, M., J. Realpe-G´omez, R. Biswas, and A. Perdomo-Ortiz (2016), Physical Review A 94 (2), 022308.   
Benioff, P. (1980), Journal of Statistical Physics 22 (5), 563.   
Benioff, P. (1982), Physical Review Letters 48 (23), 1581.   
Bennett, C., E. Bernstein, G. Brassard, and U. Vazirani (1997), SIAM Journal on Computing, SIAM Journal on Computing 26 (5), 1510.   
Bernstein, E., and U. Vazirani (1993), in Proceedings of the Twenty-fifth Annual ACM Symposium on Theory of Computing, STOC ’93 (ACM, New York, NY, USA) pp. 11–20.   
Bernstein, E., and U. Vazirani (1997), SIAM Journal on Computing 26 (5), 1411.   
Bhatia, R., (1997), Matrix Analysis, Graduate Texts in Mathematics No. 169 (Springer-Verlag, New York).   
Biamonte, J. D., and P. J. Love (2008), Phys. Rev. A 78, 012352.   
Biham, E., O. Biham, D. Biron, M. Grassl, and D. A. Lidar (1999), Physical Review A 60 (4), 2742.   
Bisseling, R. H. (2004), Parallel scientific computation (Oxford University Press Oxford).   
Bloch, C. (1958), Nuclear Physics 6, 329 .   
Boixo, S., E. Knill, and R. D. Somma (2009a), Quantum Information and Computation 9, 833.   
Boixo, S., E. Knill, and R. D. Somma (2009b), Quant. Inf. & Comp. 9, 833.   
Boixo, S., E. Knill, and R. D. Somma (2010), arXiv:1005.3034 (unpublished)   
Boixo, S., T. F. Ronnow, S. V. Isakov, Z. Wang, D. Wecker, D. A. Lidar, J. M. Martinis, and M. Troyer (2014), Nat. Phys. 10 (3), 218.   
Boixo, S., V. N. Smelyanskiy, A. Shabani, S. V. Isakov, M. Dykman, V. S. Denchev, M. H. Amin, A. Y. Smirnov, M. Mohseni, and H. Neven (2016), Nat Commun 7.   
Boixo, S., and R. D. Somma (2010), Physical Review A 81 (3), 032308.   
Bollob´as, B., O. Riordan, J. Spencer, and G. Tusn´ady (2001), Random Structures and Algorithms 18, 279.   
Borgs, C., J. Chayes, and B. Pittel (2001), Random Structures & Algorithms 19 (3-4), 247.   
Born, M., and V. Fock (1928), Z. Physik 51 (3-4), 165.   
Born, M., and R. Oppenheimer (1927), Annalen der Physik 389 (20), 457.   
Boyer, M., G. Brassard, P. Høyer, and A. Tapp (1998), Fortschritte der Physik 46 (4-5), 493.   
Brady, L. T., and W. van Dam (2016a), Phys. Rev. A 93, 032304.   
Brady, L. T., and W. van Dam (2016b), Phys. Rev. A 94, 032309.   
Brady, L. T., and W. van Dam (2017), Phys. Rev. A 95, 032335.   
Brady, L. T., and W. v. Dam (2016), arXiv:1609.09137 .   
Brandao, F. G. S. L., and M. Horodecki (2013), Nat Phys 9 (11), 721.   
Bravyi, S., A. J. Bessen, and B. M. Terhal (2006), eprint arXiv:quant-ph/0611021 quant-ph/0611021.   
Bravyi, S., D. P. DiVincenzo, D. Loss, and B. M. Terhal (2008a), Physical Review Letters 101 (7), 070503.   
Bravyi, S., D. P. DiVincenzo, R. I. Oliveira, and B. M. Terhal (2008b), Quant. Inf. Comp. 8 (5), 0361.   
Bravyi, S., and D. Gosset (2016), arXiv:1612.05602 .   
Bravyi, S., and M. Hastings (2014), arXiv:1410.0703   
Bravyi, S., and M. Hastings (2017), Communications in Mathematical Physics 349 (1), 1.   
Bravyi, S., and B. M. Terhal (2009), SIAM Journal on Computing, SIAM Journal on Computing 39 (4), 1462.   
Bravyi, S. B., and A. Y. Kitaev (2002), Annals of Physics 298 (1), 210 .   
Breuckmann, N. P., and B. M. Terhal (2014), Journal of Physics A: Mathematical and Theoretical 47 (19), 195304.   
Brin, S., and L. Page (1998), Computer Networks and ISDN Systems 30, 107.   
Brooke, J., D. Bitko, T. F., Rosenbaum, and G. Aeppli (1999), Science 284 (5415), 779.   
Brooke, J., T. F. Rosenbaum, and G. Aeppli (2001), Nature 413 (6856), 610.   
Buhrman, H., R. Cleve, J. Watrous, and R. de Wolf (2001), Phys. Rev. Lett. 87, 167902.   
Bunyk, P. I., E. M. Hoskinson, M. W. Johnson, E. Tolkacheva, F. Altomare, A. Berkley, R. Harris, J. P. Hilton, T. Lanting, A. Przybysz, and J. Whittaker (Aug. 2014), Applied Superconductivity, IEEE Transactions on, Applied Superconductivity, IEEE Transactions on 24 (4), 1.   
C. Zener, (1932), Proc. R. Soc. London Ser. A 137, 696.   
Cabrera, G. G., and R. Jullien (1987), Physical Review B 35 (13), 7062.   
Cao, Y., R. Babbush, J. Biamonte, and S. Kais (2015), Phys. Rev. A 91, 012315.   
Cao, Y., S. Jiang, D. Perouli, and S. Kais (2016), arXiv:1608.08547   
Cao, Y., and D. Nagaj (2015), Quantum Information & Computation 15 (13 & 14), 1197.   
Cao, Z., and A. Elgart (2012), Journal of Mathematical Physics 53 (3), 032201.   
Chancellor, N. (2016), arXiv:1606.06833 .   
Chayes, L., N. Crawford, D. Ioffe, and A. Levit (2008), Journal of Statistical Physics 133 (1), 131.   
Cheung, D., P. Høyer, and N. Wiebe (2011), Journal of Physics A: Mathematical and Theoretical 44 (41), 415302.   
Childs, A. M., R. Cleve, E. Deotto, E. Farhi, S. Gutmann, and D. A. Spielman (2003), in Proceedings of the Thirtyfifth Annual ACM Symposium on Theory of Computing, STOC ’03 (ACM, New York, NY, USA) pp. 59–68.   
Childs, A. M., E. Farhi, J. Goldstone, and S. Gutmann (2002), Quantum Inf. Comput. 2, 181.   
Childs, A. M., D. Gosset, and Z. Webb (2013), arXiv:1311.3297   
Choi, V. (2010), arXiv:1004.2226 .   
Choi, V. (2011), Proceedings of the National Academy of Sciences 108 (7), E19.   
Collins, D., K. W. Kim, and W. C. Holton (1998), Phys. Rev. A 58, R1633.   
Crosson, E., and M. Deng (2014), ArXiv e-prints arXiv:1410.8484 [quant-ph].   
Crosson, E., E. Farhi, C. Y.-Y. Lin, H.-H. Lin, and P. Shor (2014), arXiv preprint arXiv:1401.7320 .   
Crosson, E., and A. Harrow (2016), arXiv preprint arXiv:1601.03030   
Cubitt, T., and A. Montanaro (2016), SIAM Journal on Computing, SIAM Journal on Computing 45 (2), 268.   
van Dam, W., M. Mosca, and U. Vazirani (2001), Foundations of Computer Science, 2001. Proceedings. 42nd IEEE Symposium on, Foundations of Computer Science, 2001. Proceedings. 42nd IEEE Symposium on , 279.   
Das, A., and B. K. Chakrabarti (2008), Rev. Mod. Phys. 80, 1061.   
Das, A., B. K. Chakrabarti, and R. B. Stinchcombe (2005), Physical Review E 72 (2), 026701.   
Das, S., R. Kobes, and G. Kunstatter (2002), Phys. Rev. A 65, 062310.   
Das Sarma, A., A. R. Molla, G. Pandurangan, and E. Upfal (2015), Special Issue on Distributed Computing and Networking, Theoretical Computer Science 561, Part B, 113.   
Denchev, V. S., S. Boixo, S. V. Isakov, N. Ding, R. Babbush, V. Smelyanskiy, J. Martinis, and H. Neven (2016), Phys. Rev. X 6, 031015.   
Denchev, V. S., N. Ding, S. V. N. Vishwanathan, and H. Neven (2012), arXiv:1205.1148 .   
Deutsch, D. (1985), Proceedings of the Royal Society of London A: Mathematical, Physical and Engineering Sciences 400 (1818), 97.   
Deutsch, D. (1989), Proceedings of the Royal Society of London. A. Mathematical and Physical Sciences 425 (1868), 73.   
Deutsch, D., and R. Jozsa (1992), Proceedings of the Royal Society of London A: Mathematical, Physical and Engineering Sciences 439 (1907), 553.   
Dickson, N. G. (2011), New Journal of Physics 13 (7), 073011.   
Dickson, N. G., and M. H. S. Amin (2011), Phys. Rev. Lett. 106 (5), 050502.   
Du, J., L. Hu, Y. Wang, J. Wu, M. Zhao, and D. Suter (2008), Phys. Rev. Lett. 101 (6), 060403.   
Dulny, J., and M. Kim (2016), arXiv:1603.07980   
Durkin, G. A. (2016), Physical Review A 94 (4), 043821.   
Dusuel, S., and J. Vidal (2005), Phys. Rev. B 71, 224420.   
Earl, D. J., and M. W. Deem (2005), Physical Chemistry Chemical Physics 7 (23), 3910.   
Ehrenfest, P. (1916), Verslagen Kon. Akad. Amserdam 25, 412 .   
Einstein, A. (1914), Verh. d. D. phys. Ges. 16, 826.   
Eisert, J., M. Cramer, and M. B. Plenio (2010), Reviews of Modern Physics 82 (1), 277   
Elgart, A., and G. A. Hagedorn (2012), Journal of Mathematical Physics 53 (10), 102202.   
Farhi, E., J. Goldstone, D. Gosset, S. Gutmann, H. B. Meyer, and P. Shor (2011), Quantum Info. Comput. 11 (3), 181.   
Farhi, E., J. Goldstone, and S. Gutmann (2002a), arXiv:quant-ph/0201031 .   
Farhi, E., J. Goldstone, and S. Gutmann (2002b), arXiv:quant-ph/0208135   
Farhi, E., J. Goldstone, S. Gutmann, J. Lapan, A. Lundgren, and D. Preda (2001), Science 292 (5516), 472.   
Farhi, E., J. Goldstone, S. Gutmann, and D. Nagaj (2008), International Journal of Quantum Information 06 (03), 503.   
Farhi, E., J. Goldstone, S. Gutmann, and M. Sipser (2000), arXiv:quant-ph/0001106 .   
Farhi, E., D. Gosset, I. Hen, A. W. Sandvik, P. Shor, A. P. Young, and F. Zamponi (2012), Phys. Rev. A 86, 052334.   
Farhi, E., and S. Gutmann (1998), Phys. Rev. A 57, 2403.   
Farhi, E., and A. W. Harrow (2016), arXiv:1602.07674   
Feynman, R. P. (1982), International Journal of Theoretical Physics 21 (6), 467.   
Feynman, R. P. (1985), Optics News, Optics News 11 (2), 11.   
Finnila, A. B., M. A. Gomez, C. Sebenik, C. Stenson, and J. D. Doll (1994), Chemical Physics Letters 219 (5–6), 343.   
Fisher, D. S. (1995), Physical Review B 51 (10), 6411.   
Foini, L., G. Semerjian, and F. Zamponi (2010), Phys. Rev. Lett. 105, 167204.   
Franz, S., M. M´ezard, F. Ricci-Tersenghi, M. Weigt, and R. Zecchina (2001), EPL (Europhysics Letters) 55 (4), 465.   
Frees, A., J. K. Gamble, K. Rudinger, E. Bach, M. Friesen, R. Joynt, and S. N. Coppersmith (2013), Physical Review A 88 (3), 032307.   
Freund, Y., R. Schapire, and N. Abe (1999), Journal of Japanese Society for Artificial Intelligence 14, 771.   
Gaitan, F., and L. Clark (2012), Physical Review Letters 108 (1), 010501.   
Gaitan, F., and L. Clark (2014), Physical Review A 89 (2), 022342.   
Garnerone, S., P. Zanardi, and D. A. Lidar (2012), Phys. Rev. Lett. 108 (23), 230506.   
Garrido, L. M. and Sancho, F. J., (1962), Physica 28, 553.   
Ge, Y., A. Moln´ar, and J. I. Cirac (2015), arXiv:1508.00570   
Gershgorin, S. (1931), Bull. Acad. Sci. URSS 1931 (6), 749.   
Gharibian, S. (2013), Approximation, Proof Systems, and Correlations in a Quantum World, Ph.D. thesis (University of Waterloo).   
Gharibian, S., Y. Huang, Z. Landau, and S. W. Shin (2015), Foundations and TrendsR in Theoretical Computer Science 10 (3), 159.   
Goldreich, O. (2008), Computational Complexity: A Conceptual Perspective (Cambridge University Press).   
Gosset, D., B. M. Terhal, and A. Vershynina (2015), Physical Review Letters 114 (14), 140501.   
Goto, H. (2016), Scientific Reports 6, 21686 EP .   
Gottesman, D., and M. B. Hastings (2010), New J. of Phys. 12 (2), 025002.   
Gottesman, D., and S. Irani (2013), Theory of Computing 9, 31.   
Grover, L. K. (1997), Phys. Rev. Lett. 79 (2), 325.   
Guidetti, M., and A. P. Young (2011), Phys. Rev. E 84, 011102.   
Haanpaa, H., M. Jarvisalo, P. Kaski, and I. Niemela (2006), Journal on Satisfiability, Boolean Modeling and Computation 2, 27.   
Hagedorn, G. A., and A. Joye (2002), Journal of Mathematical Analysis and Applications 267 (1), 235.   
Hallgren, S., D. Nagaj, and S. Narayanaswami (2013), Quantum Information $\&$ Computation 13 (9 & 10), 0721.   
Han, Y., L. A. Hemaspaandra, and T. Thierauf (1993), “Threshold computation and cryptographic security,” in Algorithms and Computation: 4th International Symposium, ISAAC ’93 Hong Kong, December 15–17, 1993 Proceedings, edited by K. W. Ng, P. Raghavan, N. V. Balasubramanian, and F. Y. L. Chin (Springer Berlin Heidelberg, Berlin, Heidelberg) pp. 230–239.   
Hashizume, Y., T. Koizumi, K. Akitaya, T. Nakajima, S. Okamura, and M. Suzuki (2015), Physical Review E 92 (2), 023302.   
Hastings, M. B. (2007), Journal of Statistical Mechanics: Theory and Experiment 2007 (08), P08024.   
Hastings, M. B. (2009), Phys. Rev. Lett. 103, 050502.   
Hastings, M. B., and M. H. Freedman (2013), Quant. Inf. & Comp. 13, 1038.   
Hauke, P., L. Bonnes, M. Heyl, and W. Lechner (2015), Frontiers in Physics 3.   
Hayden, P., D. W. Leung, and A. Winter (2006), Communications in Mathematical Physics 265 (1), 95.   
Hayes, B. (2002), American Scientist 90 (3), 113.   
Hen, I. (2014a), Journal of Physics A: Mathematical and Theoretical 47 (4), 045305.   
Hen, I. (2014b), Europhysics Letters 105 (5), 50005.   
Hen, I. (2017), EPL (Europhysics Letters) 118 (3), 30003.   
Hen, I., and A. P. Young (2011), Phys. Rev. E 84, 061152.   
Hen, I., and A. P. Young (2012), Phys. Rev. A 86, 042310.   
Hinton, G. E., S. Osindero, and Y.-W. Teh (2006), Neural Computation, Neural Computation 18 (7), 1527.   
Hoeffding, W. (1963), J. of the American Statistical Association 58 (301), 13.   
Hormozi, L., E. W. Brown, G. Carleo, and M. Troyer (2017), Phys. Rev. B 95, 184416.   
Horn, R. A., and C. R. Johnson (2012), Matrix Analysis (Cambridge University Press).   
Houdayer, J., (2001), Eur. Phys. J. B 22 (4), 479.   
Huang, Y. (2014), arXiv:1406.6355 .   
Hubbard, J. (1959), Phys. Rev. Lett. 3, 77.   
Hukushima, K., and K. Nemoto (1996), Journal of the Physical Society of Japan 65 (6), 1604.   
Impagliazzo, R., and R. Paturi (2001), Journal of Computer and System Sciences 62 (2), 367   
Inack, E. M., and S. Pilati (2015), Physical Review E 92 (5), 053304.   
Isakov, S. V., G. Mazzola, V. N. Smelyanskiy, Z. Jiang, S. Boixo, H. Neven, and M. Troyer (2016), Physical Review Letters 117 (18), 180402.   
Ishii, H., and T. Yamamoto (1985), Journal of Physics C: Solid State Physics 18 (33), 6225.   
Jansen, S., M.-B. Ruskai, and R. Seiler (2007), J. Math. Phys. 48 (10), 102111.   
Janzing, D. (2007), Phys. Rev. A 75, 012307.   
Janzing, D., P. Wocjan, and S. Zhang (2008), New Journal of Physics 10 (9), 093004.   
Jarret, M., S. P. Jordan, and B. Lackey (2016), Physical Review A 94 (4), 042318.   
Jerrum, M. (1992), Random Structures & Algorithms 3 (4), 347.   
Johnson, M. W., M. H. S. Amin, S. Gildert, T. Lanting, F. Hamze, N. Dickson, R. Harris, A. J. Berkley, J. Johansson, P. Bunyk, E. M. Chapple, C. Enderud, J. P. Hilton, K. Karimi, E. Ladizinsky, N. Ladizinsky, T. Oh, I. Perminov, C. Rich, M. C. Thom, E. Tolkacheva, C. J. S. Truncik, S. Uchaikin, J. Wang, B. Wilson, and G. Rose (2011), Nature 473 (7346), 194.   
Jordan, S. P. (2016a), “AQC 2016 - Adiabatic Quantum Computer vs. Diffusion Monte Carlo,” website.   
Jordan, S. P. (2016b), “Quantum algorithm zoo,” website.   
Jordan, S. P., and E. Farhi (2008), Phys. Rev. A 77, 062329.   
Jordan, S. P., D. Gosset, and P. J. Love (2010), Physical Review A 81 (3), 032331.   
J¨org, T., F. Krzakala, J. Kurchan, and A. C. Maggs (2008), Phys. Rev. Lett. 101, 147204.   
J¨org, T., F. Krzakala, J. Kurchan, A. C. Maggs, and J. Pujos (2010a), EPL (Europhysics Letters) 89 (4), 40004.   
J¨org, T., F. Krzakala, G. Semerjian, and F. Zamponi (2010b), Phys. Rev. Lett. 104, 207206.   
Joye, A. (1994), Asymptotic Analysis 9 (3), 209.   
Jozsa, R., and N. Linden (2003), Proceedings of the Royal Society of London. Series A: Mathematical, Physical and Engineering Sciences 459 (2036), 2011   
Kadowaki, T., and H. Nishimori (1998), Phys. Rev. E 58 (5), 5355.   
Karimi, H., and G. Rosenberg (2016), arXiv:1606.07797 .   
Karimi, S., and P. Ronagh (2016), arXiv:1605.09462   
Karmarkar, N., and R. Karp (1982), The differencing method of set partitioning, Tech. Rep. UCB/CSD 82/113 (University of California at Berkeley).   
Karp, R. (1972), in Complexity of Computer Computations, The IBM Research Symposia Series, edited by R. E. Miller and J. W. Thatcher (Plenum, New York) Chap. 9, p. 85.   
Kato, T. (1950), J. Phys. Soc. Jpn. 5 (6), 435.   
Katzgraber, H. G., F. Hamze, Z. Zhu, A. J. Ochoa, and H. Munoz-Bauza (2015), arXiv:1505.01545 .   
Katzgraber, H. G., S. Trebst, D. A. Huse, and M. Troyer (2006), J. Stat. Mech. 2006 (03), P03018.   
Kay, A. (2008), Physical Review A 78 (1), 012346.   
Kempe, J., A. Kitaev, and O. Regev (2006), SIAM Journal on Computing 35 (5), 1070.   
Kempe, J., and O. Regev (2003), Quantum Information & Computation 3 (3), 258, quant-ph/0302079.   
King, J., S. Yarkoni, M. M. Nevisi, J. P. Hilton, and C. C. McGeoch (2015), arXiv:1508.05087   
Kirkpatrick, S., C. D. Gelatt, and M. P. Vecchi (1983), Science 220 (4598), 671.   
Kitaev, A. Y., A. H. Shen, and M. N. Vyalyi (2000), Classical and Quantum Computation, Graduate Studies in Mathematics, Vol. 47 (American Mathematical Society, Providence, RI).   
Klarsfeld, S., and J. A. Oteo (1989), Journal of Physics A: Mathematical and General 22 (21), 4565.   
Klauder, J. R. (1979), Physical Review D 19 (8), 2349.   
Kleinberg, J. M., R. Kumar, P. Raghavan, S. Rajagopalan, and A. S. Tomkins (1999), in Computing and Combinatorics (Proceedings of the 5th Annual International Conference, COCOON’99) p. 1.   
Knysh, S. (2016), Nat Commun 7, 12370.   
Knysh, S., and V. Smelyanskiy (2010), arXiv:1005.3011 .   
Knysh, S., and V. N. Smelyanskiy (2006), arXiv:condmat/0602257 .   
Kong, L., and E. Crosson (2015), arXiv:1511.06991   
Krzakala, F., A. Rosso, G. Semerjian, and F. Zamponi (2008), Phys. Rev. B 78, 134428.   
Kumar, V., A. Grama, A. Gupta, and G. Karypis (2003), Introduction to Parallel Computing. 2nd (Addison Wesley).   
Kurihara, K., S. Tanaka, and S. Miyashita (2014), arXiv:1408.2035 .   
Landau, Z., U. Vazirani, and T. Vidick (2015), Nat Phys 11 (7), 566.   
Landau, L. D., (1932), Phys. Z. Sowjetunion 2, 46.   
Langville, A. N., and C. D. Meyer (2006), Google’s PageRank and Beyond: The Science of Search Engine Rankings (Princeton University Press).   
Latorre, J. I., and R. Orus (2004), Physical Review A 69 (6), 062302.   
Laumann, C., A. Scardicchio, and S. L. Sondhi (2008), Physical Review B 78 (13), 134424.   
Laumann, C. R., R. Moessner, A. Scardicchio, and S. L. Sondhi (2012), Physical Review Letters 109 (3), 030502.   
Laumann, C. R., R. Moessner, A. Scardicchio, and S. L. Sondhi (2015), The European Physical Journal Special Topics 224 (1), 75.   
Lidar, D. A., A. T. Rezakhani, and A. Hamma (2009), J. Math. Phys. 50 (10), 102106.   
Liu, C.-W., A. Polkovnikov, and A. W. Sandvik (2015), Phys. Rev. Lett. 114, 147203   
Lloyd, S., M. Mohseni, and P. Rebentrost (2014), Nat. Phys. 10 (9), 631.   
Lloyd, S., and B. M. Terhal (2016), New Journal of Physics 18 (2), 023042.   
Lucas, A. (2014), Front. Phys. 2, 5.   
M. Mezard, G. Parisi and M.A. Virasoro, (1987), Spin Glass Theory and Beyond, World Scientific Lecture Notes in Physics (World Scientific, Singapore).   
Mandr\`a, S., Z. Zhu, and H. G. Katzgraber (2017), Phys. Rev. Lett. 118, 070502.   
Mandr\`a, S., Z. Zhu, W. Wang, A. Perdomo-Ortiz, and H. G. Katzgraber (2016), Physical Review A 94 (2), 022337.   
Mao, W. (2005a), Physical Review A 71 (6), 060309.   
Mao, W. (2005b), Physical Review A 72 (5), 052316.   
Margolus, N. (1990), in Complexity, Entropy, and the Physics of Information, SFI Studies in the Sciences of Complexity, Vol. VIII, edited by W. Zurek (Addison-Wesley) pp. 273– 287.   
Marinari, E., and G. Parisi (1992), EPL (Europhysics Letters) 19 (6), 451.   
Marriott, C., and J. Watrous (2005), J. Comput. Complex. 14 (2), 122.   
Marzlin, K.-P., and B. C. Sanders (2004), Phys. Rev. Lett. 93, 160408.   
Matsuda, Y., H. Nishimori, and H. G. Katzgraber (2009), New J. Phys. 11 (7), 073021.   
Meir, R. (2003), in Advanced Lectures on Machine Learning, Lecture Notes in Computer Science, Vol. 2600, edited by S. Mendelson and A. Smola (Springer Berlin / Heidelberg) pp. 118–183.   
Mertens, S. (1998), Physical Review Letters 81 (20), 4281.   
Mertens, S. (2001), Phase Transitions in Combinatorial Problems, Theoretical Computer Science 265 (1), 79.   
Mertens, S. (2003), arXiv:cond-mat/0310317   
Messiah, A., (1962), Quantum Mechanics, Vol. II (North-Holland Publishing Company, Amsterdam).   
Miller, J., and D. A. Huse (1993), Phys. Rev. Lett. 70, 3147.   
Miyahara, H., and K. Tsumura (2016), arXiv:1606.01484 .   
Mizel, A. (2004), Phys. Rev. A 70, 012304.   
Mizel, A., D. A. Lidar, and M. Mitchell (2007), Phys. Rev. Lett. 99, 070502.   
Mizel, A., M. W. Mitchell, and M. L. Cohen (2001), Phys. Rev. A 63, 040302.   
Mizel, A., M. W. Mitchell, and M. L. Cohen (2002), Phys. Rev. A 65, 022315.   
Moussa, J. E. (2013), ArXiv e-prints arXiv:1310.6676 [quantph].   
Movassagh, R., and P. W. Shor (2016), Proceedings of the National Academy of Sciences 113 (47), 13278.   
M.R. Garey and D.S. Johnson, (1979), Computers and Intractability: A Guide to the Theory of NP-Completeness (W.H. Freeman, New York).   
Muthukrishnan, S., T. Albash, and D. A. Lidar (2016), Phys. Rev. X 6, 031010.   
Nagaj, D. (2008), arXiv:0808.2117 .   
Nagaj, D., and S. Mozes (2007), Journal of Mathematical Physics 48 (7), 072104.   
Nagaj, D., and P. Wocjan (2008), Physical Review A 78 (3), 032311.   
Nagaj, D., P. Wocjan, and Y. Zhang (2009), Quant. Inf. Comput. 9 (11-12), 1053.   
Nakahara, M., (1990), Geometry, topology and Physics (Institute of Physics Publishing).   
Nayak, C., S. H. Simon, A. Stern, M. Freedman, and S. Das Sarma (2008), Reviews of Modern Physics 80 (3), 1083.   
Nenciu, G. (1993), Commun.Math. Phys. 152 (3), 479.   
Van den Nest, M. (2013), Physical Review Letters 110 (6), 060504.   
Neven, H., V. S. Denchev, G. Rose, and W. G. Macready (2008a), arXiv:0811.0416 .   
Neven, H., V. S. Denchev, G. Rose, and W. G. Macready (2009), arXiv:0912.0779 .   
Neven, H., G. Rose, and W. G. Macready (2008b), arXiv:0804.4457 .   
Nielsen, M., and I. Chuang (2000), Quantum Computation and Quantum Information, Cambridge Series on Information and the Natural Sciences (Cambridge University Press).   
Nishimori, H. (2001), Statistical Physics of Spin Glasses and Information Processing: An Introduction (Oxford University Press, Oxford, UK).   
Nishimori, H. (2016), arXiv:1609.03785 .   
Nussbaum, R. (2003), arXiv:math/0307056.   
O’Gorman, B., R. Babbush, A. Perdomo-Ortiz, A. Aspuru-Guzik, and V. Smelyanskiy (2015), The European Physical Journal Special Topics 224 (1), 163.   
O’Hara, M. J., and D. P. O’Leary (2008), Phys. Rev. A 77, 042319.   
Oliveira, R., and B. M. Terhal (2008), Quantum Info. Comput. 8 (10), 900.   
Or´us, R., and J. Latorre (2004), Physical Review A 69 (5), 052308.   
Osborne, T. J. (2007), Physical Review A 75 (3), 032321.   
Osborne, T. J., and M. A. Nielsen (2002), Physical Review A 66 (3), 032110.   
Osterloh, A., L. Amico, G. Falci, and R. Fazio (2002), Nature 416, 608.   
Ostlund, S., and S. Rommer (1995), ¨ Phys. Rev. Lett. 75, 3537.   
P. Jordan and E. Wigner, (1928), Z. Phys. 47, 631.   
Papageorgiou, A., and J. F. Traub (2013), Phys. Rev. A 88, 022316.   
Perdomo-Ortiz, A., S. E. Venegas-Andraca, and A. Aspuru-Guzik (2011), Quantum Information Processing 10 (1), 33.   
Piddock, S., and A. Montanaro (2015), arXiv:1506.04014 .   
Powles, J. G. (1958), Proceedings of the Physical Society 71 (3), 497.   
Pudenz, K. L., and D. A. Lidar (2013), Quantum Information Processing 12 (5), 2027.   
Rajak, A., and B. K. Chakrabarti (2014), Indian Journal of Physics 88 (9), 951.   
Ramsey, F. P. (1930), Proceedings of the London Mathematical Society s2-30 (1), 264.   
Ranjbar, M., W. G. Macready, L. Clark, and F. Gaitan (2016), Quantum Information Processing 15 (9), 3519.   
Rauber, T., and G. R¨unger (2010), Parallel programming: For multicore and cluster systems (Springer).   
Raussendorf, R., and H. J. Briegel (2001), Physical Review Letters 86 (22), 5188.   
Ray, P., B. K. Chakrabarti, and A. Chakrabarti (1989), Phys. Rev. B 39, 11828.   
Raymond, J., S. Yarkoni, and E. Andriyash (2016), arXiv:1606.00919 .   
Rebentrost, P., M. Mohseni, and S. Lloyd (2014), Phys. Rev. Lett. 113 (13), 130503.   
Reichardt, B. W. (2004), in Proceedings of the Thirty-sixth Annual ACM Symposium on Theory of Computing, STOC ’04 (ACM, New York, NY, USA) pp. 502–510, erratum: http://www-bcf.usc.edu/\~breichar/Correction.txt.   
Rezakhani, A. T., D. F. Abasto, D. A. Lidar, and P. Zanardi (2010a), Phys. Rev. A 82, 012321.   
Rezakhani, A. T., W. J. Kuo, A. Hamma, D. A. Lidar, and P. Zanardi (2009), Phys. Rev. Lett. 103 (8), 080502.   
Rezakhani, A. T., A. K. Pimachev, and D. A. Lidar (2010b), Phys. Rev. A 82 (5), 052305.   
Ricci-Tersenghi, F. (2010), Science 330 (6011), 1639.   
Robson, J. (2001), Finding a maximum independent set in time $O ( 2 ^ { n / 4 } )$ , Tech. Rep. (Laboratoire Bordelais de Recherche en Informatique).   
Roland, J., and N. J. Cerf (2002), Phys. Rev. A 65 (4), 042308.   
Rønnow, T. F., Z. Wang, J. Job, S. Boixo, S. V. Isakov, D. Wecker, J. M. Martinis, D. A. Lidar, and M. Troyer (2014), Science 345 (6195), 420.   
Rosenberg, G., P. Haghnegahdar, P. Goddard, P. Carr, K. Wu, and M. L. de Prado (2016), IEEE Journal of Selected Topics in Signal Processing, IEEE Journal of Selected Topics in Signal Processing 10 (6), 1053.   
Sachdev, S. (2001), Quantum Phase Transitions (Cambridge University Press, Cambridge, UK).   
Santra, S., O. Shehab, and R. Balu (2016), arXiv:1602.08149   
Sarandy, M. S., and D. A. Lidar (2005), Phys. Rev. Lett. 95 (25), 250503.   
Sato, I., K. Kurihara, S. Tanaka, H. Nakagawa, and S. Miyashita (2014), arXiv:1408.2037   
Schaller, G. (2008), Physical Review A 78 (3), 032328.   
Schaller, G., and R. Sch¨utzhold (2010), Quantum Info. Comput. 10 (1), 109.   
Schollw¨ock, U. (2005), Reviews of Modern Physics 77 (1), 259.   
Schuch, N., and F. Verstraete (2009), Nat Phys 5 (10), 732.   
Seeley, J. T., M. J. Richard, and P. J. Love (2012), The Journal of Chemical Physics 137 (22), 224109.   
Seki, Y., and H. Nishimori (2012), Phys. Rev. E 85, 051112.   
Seki, Y., and H. Nishimori (2015), Journal of Physics A: Mathematical and Theoretical 48 (33), 335301.   
Seoane, B., and H. Nishimori (2012), Journal of Physics A: Mathematical and Theoretical 45 (43), 435301.   
Shor, P. W. (1997), SIAM J. Comput. 26, 1484.   
Shor, P. W. (20-22 Nov 1994), Foundations of Computer Science, 1994 Proceedings., 35th Annual Symposium on, Foundations of Computer Science, 1994 Proceedings., 35th Annual Symposium on , 124.   
Simon, D. R. (1997), SIAM Journal on Computing 26 (5), 1474.   
Sinclair, A., and M. Jerrum (1989), Information and Computation 82 (1), 93 .   
Siu, M. S. (2005), Phys. Rev. A 71, 062314.   
Smelyanskiy, V. N., S. Knysh, and R. D. Morris (2004), Phys. Rev. E 70, 036702.   
Smelyanskiy, V. N., U. V. Toussaint, and D. A. Timucin (2001), arXiv:quant-ph/0112143 .   
Smelyanskiy, V. N., U. v. Toussaint, and D. A. Timucin (2002), arXiv:quant-ph/0202155 .   
Somma, R., and S. Boixo (2013), SIAM Journal on Computing 42 (2), 593.   
Somma, R. D., D. Nagaj, and M. Kieferov´a (2012), Phys. Rev. Lett. 109 (5), 050501.   
Somorjai, R. L. (1991), The Journal of Physical Chemistry 95 (10), 4141.   
Stadler, P. F., W. Hordijk, and J. F. Fontanari (2003), Phys. Rev. E 67, 056701.   
Suzuki, S., J. Inoue, and B. Chakrabarti (2013), Quantum Ising Phases and Transitions in Transverse Ising Models , 2nd ed., Lecture Notes in Physics, Vol. 862 (Springer Verlag, Berlin).   
Swendsen, R. H., and J.-S. Wang (1986), Phys. Rev. Lett. 57 (21), 2607.   
Swendsen, R. H., and J.-S. Wang (1987), Physical Review Letters 58 (2), 86.   
Teufel, S. (2003), Adiabatic Perturbation Theory in Quantum Dynamics, Lecture Notes in Mathematics, Vol. 1821 (Springer-Verlag, Berlin).   
Tong, D. M., K. Singh, L. C. Kwek, and C. H. Oh (2005), Phys. Rev. Lett. 95 (11), 110407.   
Tsuda, J., Y. Yamanaka, and H. Nishimori (2013), Journal of the Physical Society of Japan, Journal of the Physical Society of Japan 82 (11), 114004.   
Usadel, K. (1986), Solid State Communications 58 (9), 629 .   
Valiant, L. G. (1990), Commun. ACM 33 (8), 103.   
Venuti, L. C., T. Albash, D. A. Lidar, and P. Zanardi (2016), Phys. Rev. A 93, 032118.   
Verstraete, F., and J. I. Cirac (2004), arXiv:condmat/0407066 .   
Verstraete, F., V. Murg, and J. I. Cirac (2008), Advances in Physics 57 (2), 143.   
Vidal, G., J. I. Latorre, E. Rico, and A. Kitaev (2003), Physical Review Letters 90 (22), 227902.   
Vinci, W., and D. A. Lidar (2016), arXiv:1608.05764 .   
Weber, S. J., G. O. Samach, D. Hover, S. Gustavsson, D. K. Kim, D. Rosenberg, A. P. Sears, F. Yan, J. L. Yoder, W. D. Oliver, and A. J. Kerman (2017), arXiv:1701.06544 .   
Wei, Z., and M. Ying (2006), Physics Letters A 354 (4), 271.   
Wen, J., Y. Huang, and D. Qiu (2009), International Journal of Quantum Information, International Journal of Quantum Information 07 (08), 1531.   
Wen, J., and D. Qiu (2008), International Journal of Quantum Information, International Journal of Quantum Information 06 (05), 997.   
White, S. R. (1992), Phys. Rev. Lett. 69, 2863.   
White, S. R., and R. M. Noack (1992), Phys. Rev. Lett. 68, 3487.   
Wiebe, N., and N. S. Babcock (2012), New J. Phys. 14 (1), 013024.   
Wiebe, N., A. Kapoor, and K. M. Svore (2014), arXiv:1412.3489 .   
Wolff, U. (1989), Phys. Rev. Lett. 62, 361.   
Wu, J.-d., M.-s. Zhao, J.-l. Chen, and Y.-d. Zhang (2008), Physical Review A 77 (6), 062114.   
Wu, L. A., M. S. Sarandy, and D. A. Lidar (2004), Phys. Rev. Lett. 93 (25), 250404.   
Yao, A. (1993), in Proc. 34th IEEE Symp. on Foundations of Computer science, p. 352.   
Ye, J., S. Sachdev, and N. Read (1993), Phys. Rev. Lett. 70, 4011.   
Young, A. P., S. Knysh, and V. N. Smelyanskiy (2008), Phys. Rev. Lett. 101, 170503.   
Young, A. P., S. Knysh, and V. N. Smelyanskiy (2010), Phys. Rev. Lett. 104, 020502.   
Zalka, C. (1999), Physical Review A 60 (4), 2746.   
Zanardi, P., and M. Rasetti (1999), Physics Letters A 264 (2– 3), 94.   
Zdeborov´a, L., and M. M´ezard (2008a), Journal of Statistical Mechanics: Theory and Experiment 2008 (12), P12004.   
Zdeborov´a, L., and M. M´ezard (2008b), Phys. Rev. Lett. 101, 078702.   
Zeng, L., J. Zhang, and M. Sarovar (2016), Journal of Physics A: Mathematical and Theoretical 49 (16), 165305.   
Zhang, B. H., G. Wagenbreth, V. Martin-Mayor, and I. Hen (2017), Scientific Reports 7 (1), 1044.   
Zhu, Z., A. J. Ochoa, and H. G. Katzgraber (2015), Phys. Rev. Lett. 115, 077201.   
Zintchenko, I., M. B. Hastings, and M. Troyer (2015), Physical Review B 91 (2), 024201.   
Znidariˇc, M., and M. Horvat (2006), ˇ Physical Review A 73 (2), 022329.   
Zulkowski, P. R., and M. R. DeWeese (2015), Physical Review E 92 (3), 032113.