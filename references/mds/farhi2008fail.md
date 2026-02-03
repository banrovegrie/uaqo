# How to Make the Quantum Adiabatic Algorithm Fail

Edward Farhi,1, ∗ Jeffrey Goldstone,1 Sam Gutmann,2 and Daniel Nagaj $^ { 1 }$ $\jmath$ Center for Theoretical Physics, Massachusetts Institute of Technology, Cambridge, Massachusetts, 02139 $\mathcal { L }$ Department of Mathematics, Northeastern University, Boston, Massachusetts, 02115 (Dated: Dec 19, 2005)

The quantum adiabatic algorithm is a Hamiltonian based quantum algorithm designed to find the minimum of a classical cost function whose domain has size $N$ . We show that poor choices for the Hamiltonian can guarantee that the algorithm will not find the minimum if the run time grows more slowly than $\sqrt { N }$ . These poor choices are nonlocal and wash out any structure in the cost function to be minimized and the best that can be hoped for is Grover speedup. These failures tell us what not to do when designing quantum adiabatic algorithms.

# I. INTRODUCTION

The quantum adiabatic algorithm was introduced [1] as a quantum algorithm for finding the minimum of a classical cost function $h ( z )$ , where $z = 0 , \dots , N - 1$ . This cost function is used to define a quantum Hamiltonian diagonal in the $z$ basis:

$$
H _ { P } = \sum _ { z = 0 } ^ { N - 1 } h ( z ) | z \rangle .
$$

The goal is now to find the ground state of $H _ { P }$ . To this end a “beginning” Hamiltonian $H _ { B }$ is introduced with a known and easy to construct ground state $\left| g _ { B } \right.$ . The quantum computer is a system governed by the time dependent Hamiltonian

$$
H ( t ) = ( 1 - t / T ) H _ { B } + ( t / T ) H _ { P } ,
$$

where $T$ controls the rate of change of $H ( t )$ . Note that $H ( 0 ) = H _ { B }$ and $H ( T ) = H _ { P }$ . The state of the system obeys the Schr¨odinger equation,

$$
i \frac { \mathrm { d } } { \mathrm { d } t } | \psi ( t ) \rangle = H ( t ) | \psi ( t ) \rangle ,
$$

where we choose

$$
| \psi ( 0 ) \rangle = | g _ { B } \rangle
$$

and run the algorithm for time $T$ . By the adiabatic theorem, if $T$ is large enough then $| \psi ( T ) \rangle$ will have a large component in the ground state subspace of $H _ { P }$ . (Note we are not bothering to state the necessary condition on the lack of degeneracy of the spectrum of $H ( t )$ for $0 < t < T$ , since it will not play a role in the results we establish in this paper.) A measurement of $z$ can then be used to find the minimum of $h ( z )$ . The algorithm is useful if the required run time $T$ is not too large as a function of $N$ .

There is hope that there may be combinatorial search problems, defined on $n$ bits so that $N =$ $2 ^ { n }$ , where for certain “interesting” subsets of the instances the run time $T$ grows subexponentially in $n$ . A positive result of this kind would greatly expand the known power of quantum computers. At the same time it is worthwhile to understand the circumstances under which the algorithm is doomed to fail.

In this paper we prove some general results which show that with certain choices of $H _ { B }$ or $H _ { P }$ the algorithm will not succeed if $T$ is $o ( \sqrt { N } )$ , that is $T / \sqrt { N } \to 0$ as $N \to \infty$ , so that improvement beyond Grover speedup is impossible. We view these failures as due to poor choices for $H _ { B }$ and $H _ { P }$ , which teach us what not to do when looking for good algorithms. We guarantee failure by removing any structure which might exist in $h ( z )$ from either $H _ { B }$ or $H _ { P }$ . By structure we mean that $z$ is written as a bit string and both $H _ { B }$ and $H _ { P }$ are sums of terms involving only a few of the corresponding qubits.

In Section II we show that regardless of the form of $h ( z )$ if $H _ { B }$ is a one dimensional projector onto the uniform superposition of all the basis states $| z \rangle$ , then the quantum adiabatic algorithm fails. Here all the $| z \rangle$ states are treated identically by $H _ { B }$ so any structure contained in $h ( z )$ is lost in $H _ { B }$ . In Section III we consider a scrambled $H _ { P }$ that we get by replacing the cost function $h ( z )$ by $h ( \pi ( z ) )$ where $\pi$ is a permutation of $0$ to $N - 1$ . Here the values of $h ( z )$ and $h ( \pi ( z ) )$ are the same but the relationship between input and output is scrambled by the permutation. This effectively destroys any structure in $h ( z )$ and typically results in algorithmic failure.

The quantum adiabatic algorithm is a special case of Hamiltonian based continuous time quantum algorithms, where the quantum state obeys (3) and the algorithm consists of specifying $H ( t )$ , the initial state $| \psi ( 0 ) \rangle$ , a run time $T$ and the operators to be measured at the end of the run. In the Hamiltonian language, the Grover problem can be recast as the problem of finding the ground state of

$$
H _ { w } = E ( \mathbb { I } - | w \rangle \langle w | ) ,
$$

where $w$ lies between 0 and $N - 1$ . The algorithm designer can apply $H _ { w }$ , but in this oracular setting, $w$ is not known. In reference [2] the following result was proved. Let

$$
H ( t ) = H _ { D } ( t ) + H _ { w } ,
$$

where $H _ { D }$ is any time dependent “driver” Hamiltonian independent of $w$ . Assume also that the initial state $| \psi ( 0 ) \rangle$ is independent of $w$ . For each $w$ we want the algorithm to be successful, that is $| \psi ( T ) \rangle = | w \rangle$ . It then follows that

$$
T \geq { \frac { \sqrt { N } } { 2 E } } .
$$

The proof of this result is a continuous-time version of the BBBV oracular proof [3]. Our proof techniques in this paper are similar to the methods used to prove the result just stated.

# II. GENERAL SEARCH STARTING WITH A ONE-DIMENSIONAL PROJECTOR

In this section we consider a completely general cost function $h ( z )$ with $z = 0 , \dots , N - 1$ . The goal is to use the quantum adiabatic algorithm to find the ground state of $H _ { P }$ given by (1) with $H ( t )$ given by (2). Let

$$
| s \rangle = \frac { 1 } { \sqrt { N } } \sum _ { z = 0 } ^ { N - 1 } | z \rangle
$$

be the uniform superposition over all possible values $z$ . If we pick

$$
H _ { B } = E ( \mathbb { I } - | s \rangle \langle s | )
$$

and $| \psi ( 0 ) \rangle = | s \rangle$ , then the adiabatic algorithm fails in the following sense:

Theorem 1. Let $H _ { P }$ be diagonal in the $z$ basis with a ground state subspace of dimension $k$ . Let

$$
H ( t ) = ( 1 - t / T ) E \left( \mathbb { I } - | s \rangle \langle s | \right) + ( t / T ) H _ { P } .
$$

Let $P$ be the projector onto the ground state subspace of $H _ { P }$ and let $b > 0$ be the success probability, that is, $b = \langle \psi ( T ) | P | \psi ( T ) \rangle$ . Then

$$
T \geq \frac { b } { E } \sqrt { \frac { N } { k } } - \frac { 2 \sqrt { b } } { E } .
$$

Proof. Keeping $H _ { P }$ fixed, we introduce $N - 1$ additional beginning Hamiltonians as follows. For $x = 0 , \ldots , N - 1$ let $V _ { x }$ be a unitary operator diagonal in the $z$ basis with

$$
\langle z | V _ { x } | z \rangle = e ^ { 2 \pi i z x / N }
$$

and let

$$
| x \rangle = V _ { x } | s \rangle = { \frac { 1 } { \sqrt { N } } } \sum _ { z = 0 } ^ { N - 1 } e ^ { 2 \pi i z x / N } | z \rangle
$$

so that the $\{ | x \rangle \}$ form an orthonormal basis. Note also that

$$
| x = 0 \rangle = | s \rangle .
$$

We now define

$$
H _ { x } ( t ) = ( 1 - t / T ) E ( \mathbb { I } - | x \rangle \langle x | ) + ( t / T ) H _ { P } ,
$$

with corresponding evolution operator $U _ { x } ( t _ { 2 } , t _ { 1 } )$ . Note that $H ( t )$ above is $H _ { 0 } ( t )$ with the corresponding evolution operator $U _ { 0 }$ . For each $x$ we evolve with $H _ { x } ( t )$ from the ground state of $H _ { x } ( 0 )$ , which is $| x \rangle$ . Note that $H _ { x } = V _ { x } H _ { 0 } V _ { x } ^ { \dagger }$ and $U _ { x } = V _ { x } U _ { 0 } V _ { x } ^ { \dagger }$ . Let $| f _ { x } \rangle = U _ { x } ( T , 0 ) | x \rangle$ . For each $x$ the success probability is $\langle f _ { x } | P | f _ { x } \rangle$ , which is equal to $b$ since $P$ commutes with $V _ { x }$ . The key point is that if we run the Hamiltonian evolution with $H _ { x }$ backwards in time, we would then be finding $x$ , that is, solving the Grover problem. However, this should not be possible unless the run time $T$ is of order $\sqrt { N }$ .

Let $U _ { R }$ be the evolution operator corresponding to an $x$ -independent reference Hamiltonian

$$
H _ { R } ( t ) = ( 1 - t / T ) E + ( t / T ) H _ { P } .
$$

Let $\begin{array} { r } { | g _ { x } \rangle = \frac { 1 } { \sqrt { b } } P | f _ { x } \rangle } \end{array}$ be the normalized component of $\left| f _ { x } \right.$ in the ground state subspace of $H _ { P }$ . We consider the difference in backward evolution from $\left| g _ { x } \right.$ with Hamiltonians $H _ { x }$ and $H _ { R }$ , and sum on $x$ ,

$$
S ( t ) = \sum _ { x } \left\| { U _ { x } ^ { \dagger } ( T , t ) } | g _ { x } \rangle - { U _ { R } ^ { \dagger } ( T , t ) } | g _ { x } \rangle \right\| ^ { 2 } .
$$

Clearly $S ( T ) = 0$ , and

$$
S ( 0 ) \ = \ \sum _ { x } \left\| U _ { x } ^ { \dagger } ( T , 0 ) \vert g _ { x } \rangle - U _ { R } ^ { \dagger } ( T , 0 ) \vert g _ { x } \rangle \right\| ^ { 2 } .
$$

Now $| g _ { x } \rangle = \sqrt { b } | f _ { x } \rangle + \sqrt { 1 - b } | f _ { x } ^ { \perp } \rangle$ where $| f _ { x } ^ { \perp } \rangle$ is orthogonal to $\left| f _ { x } \right.$ . Since $U _ { x } ^ { \dagger } ( T , 0 ) | f _ { x } \rangle = | x \rangle$ we have

$$
S ( 0 ) = \sum _ { x } \left\| { \sqrt { b } } | x \rangle + { \sqrt { 1 - b } } | x ^ { \perp } \rangle - | i _ { x } \rangle \right\| ^ { 2 } ,
$$

where for each $x$ , $| x ^ { \perp } \rangle$ and $| i _ { x } \rangle$ are normalized states with $| x ^ { \perp } \rangle$ orthogonal to $| x \rangle$ . Since $H _ { R }$ commutes with $H _ { P }$ , $| i _ { x } \rangle = U _ { R } ^ { \dagger } ( T , 0 ) | g _ { x } \rangle$ is an element of the $k$ -dimensional ground state subspace of $H _ { P }$ . We have

$$
\begin{array} { l } { S ( 0 ) \ = \ 2 N - \displaystyle \sum _ { x } \Big [ \sqrt { b } \langle x | i _ { x } \rangle + \sqrt { 1 - b } \langle x ^ { \perp } | i _ { x } \rangle + c . c . \Big ] } \\ { \displaystyle \geq \ 2 N - 2 \sqrt { b } \displaystyle \sum _ { x } \Big \vert \langle x | i _ { x } \rangle \Big \vert - 2 N \sqrt { 1 - b } . } \end{array}
$$

Choosing a basis $\{ | G _ { j } \rangle \}$ for the $k$ dimensional ground state subspace of $H _ { P }$ and writing $| i _ { x } \rangle =$ $a _ { x 1 } | G _ { 1 } \rangle + \cdot \cdot \cdot + a _ { x k } | G _ { k } \rangle$ gives

$$
\begin{array} { r l r } {  { \sum _ { x } \Big | \langle x | i _ { x } \rangle \Big | \le \sum _ { x , j } | a _ { x j } | \cdot \Big | \langle x | G _ { j } \rangle \Big | } } \\ & { \le } & { \sqrt { \sum _ { x , j } | a _ { x j } | ^ { 2 } \sum _ { x ^ { \prime } , j ^ { \prime } } | \langle x ^ { \prime } | G _ { j ^ { \prime } } \rangle | ^ { 2 } } = \sqrt { N k } . } \end{array}
$$

Thus

$$
S ( 0 ) \geq 2 N ( 1 - \sqrt { 1 - b } ) - 2 \sqrt { b } \sqrt { N k } .
$$

We will use the Schr¨odinger equation to find the time derivative of $S ( t )$ :

$$
\begin{array} { r c l } { \displaystyle \frac { \mathrm { d } } { \mathrm { d } t } S ( t ) = - \sum _ { x } \frac { \mathrm { d } } { \mathrm { d } t } \Big [ \langle g _ { x } | U _ { x } ( T , t ) U _ { R } ^ { \dagger } ( T , t ) | g _ { x } \rangle + c . c . \Big ] } \\ { = - i \displaystyle \sum _ { x } \langle g _ { x } | U _ { x } ( T , t ) [ H _ { x } ( t ) - H _ { R } ( t ) ] U _ { R } ^ { \dagger } ( T , t ) | g _ { x } \rangle + c . c . } \\ { = - 2 \operatorname { I m } \sum _ { x } ( 1 - t / T ) E \langle g _ { x } | U _ { x } ( T , t ) | x \rangle \langle x | U _ { R } ^ { \dagger } ( T , t ) | g _ { x } \rangle . } \end{array}
$$

Now

$$
\begin{array} { r l r } {  { | \frac { \mathrm { d } } { \mathrm { d } t } S ( t ) | \le 2 E ( 1 - t / T ) \sum _ { x } | \langle g _ { x } | U _ { x } ( T , t ) | x \rangle \langle x | U _ { R } ^ { \dagger } ( T , t ) | g _ { x } \rangle | } } \\ & { \le } & { 2 E ( 1 - t / T ) \sum _ { x } | \langle x | U _ { R } ^ { \dagger } ( T , t ) | g _ { x } \rangle | . ~ } \end{array}
$$

Using the same technique as in (9), we obtain

$$
\left| { \frac { \mathrm { d } } { \mathrm { d } t } } S ( t ) \right| \ \leq \ 2 E ( 1 - t / T ) { \sqrt { N k } } .
$$

Therefore

$$
\int _ { 0 } ^ { T } \left| { \frac { \mathrm { d } } { \mathrm { d } t } } S ( t ) \right| \mathrm { d } t \leq E T { \sqrt { N k } } .
$$

Now $\begin{array} { r } { S ( 0 ) \le S ( T ) + \int _ { 0 } ^ { T } \left| \frac { \mathrm { d } } { \mathrm { d } t } S ( t ) \right| \mathrm { d } t } \end{array}$ and $S ( T ) = 0$ so

$$
S ( 0 ) \leq E T { \sqrt { N k } } .
$$

Combining this with (10) gives

$$
E T \sqrt { N k } \ge 2 N ( 1 - \sqrt { 1 - b } ) - 2 \sqrt { b } \sqrt { N k } ,
$$

which implies what we wanted to prove:

$$
T \geq \frac { b } { E } \sqrt { \frac { N } { k } } - \frac { 2 \sqrt { b } } { E } .
$$

How do we interpret Theorem 1? The goal is to find the minimum of the cost function $h ( z )$ using the quantum adiabatic algorithm. It is natural to pick for $H _ { B }$ a Hamiltonian whose ground state is $| s \rangle$ , the uniform superposition of all $| z \rangle$ states. However if we pick $H _ { B }$ to be the one dimensional projector $E ( \mathbb { I } - | s \rangle \langle s | )$ the algorithm will not find the ground state if $T / \sqrt { N }$ goes to $0$ as $N$ goes to infinity. The problem is that $H _ { B }$ has no structure and makes no reference to $h ( z )$ . Our hope is that the algorithm might be useful for interesting computational problems if $H _ { B }$ has structure that reflects the form of $h ( z )$ .

Note that Theorem 1 explains the algorithmic failure discovered by $\check { Z }$ nidariˇc and Horvat [4] for a particular set of $h ( z )$ .

For a simple but convincing example of the importance of the choice of $H _ { B }$ , suppose we take a decoupled $n$ bit problem which consists of $n$ clauses each acting on one bit, say for each bit $j$

$$
h _ { j } ( z ) = { \left\{ \begin{array} { l l } { 0 } & { { \mathrm { ~ i f ~ } } z _ { j } = 0 , } \\ { 1 } & { { \mathrm { ~ i f ~ } } z _ { j } = 1 , } \end{array} \right. }
$$

so

$$
h ( z ) = z _ { 1 } + z _ { 2 } + \cdot \cdot \cdot + z _ { n } .
$$

Let us pick a beginning Hamiltonian reflecting the bit structure of the problem,

$$
H _ { B } = \sum _ { j = 1 } ^ { n } \frac { 1 } { 2 } \left( 1 - \sigma _ { x } ^ { ( j ) } \right) .
$$

The ground state of $H _ { B }$ is $| s \rangle$ , The quantum adiabatic algorithm acts on each bit independently, producing a success probability of

$$
p = ( 1 - q ( T ) ) ^ { n } ,
$$

where $q ( T ) \to 0$ as $T \to \infty$ is the transition probability between the ground state and the excited state of a single qubit. As long as $n q ( T ) \to c o n s t$ . we have a constant probability of success. This can be achieved for $T$ of order $\sqrt { n }$ , because for a two level system with a nonzero gap, the probability of a transition is $q ( T ) = O ( T ^ { - 2 } )$ . (For details, see Appendix A.) However, from Theorem 1 we see that a poor choice of $H _ { B }$ would make the quantum adiabatic algorithm fail on this simple decoupled $n$ bit problem by destroying the bit structure.

Next, suppose the satisfiability problem we are trying to solve has clauses involving say 3 bits. If clause $c$ involves bits $i _ { c }$ , $j _ { c }$ and $k _ { c }$ we may define the clause cost function

$$
h _ { c } ( z ) = \left\{ \begin{array} { l l } { { 0 } } & { { \mathrm { i f } \ z _ { i _ { c } } , z _ { j _ { c } } , z _ { k _ { c } } \mathrm { s a t i s f y \ c l a u s e } c , } } \\ { { 1 } } & { { \mathrm { o t h e r w i s e } . } } \end{array} \right.
$$

![](images/10e227bcae5f4476e3e9a02ad332184bc9f5dbfe76e4889d947c3525b172a638.jpg)  
FIG. 1: Median required run time $T$ versus bit number. At each bit number there are 50 random instances of Exact Cover with a single satisfying assignment. We choose the required run time to be the value of $T$ for which quantum adiabatic algorithm has success probability between 0.2 and 0.21. For the projector beginning Hamiltonian we use (8) with $E = n / 2$ . The plot is log-linear. The error bars show the $9 5 \%$ confidence interval for the true medians.

The total cost function is then

$$
h ( z ) = \sum _ { c } h _ { c } ( z ) .
$$

To get $H _ { B }$ to reflect the bit and clause structure we may pick

$$
H _ { B , c } = \frac { 1 } { 2 } \left[ ( 1 - \sigma _ { x } ^ { ( i _ { c } ) } ) + ( 1 - \sigma _ { x } ^ { ( j _ { c } ) } ) + ( 1 - \sigma _ { x } ^ { ( k _ { c } ) } ) \right]
$$

with

$$
H _ { B } = \sum _ { c } H _ { B , c } .
$$

In this case the ground state of $H _ { B }$ is again $| s \rangle$ . With this setup, Theorem 1 does not apply.

We did a numerical study of a particular satisfiability problem, Exact Cover. For this problem if clause $c$ involves bits $i _ { c }$ , $j _ { c }$ and $k _ { c }$ , the cost function is

$$
h _ { c } ( z ) = { \left\{ \begin{array} { l l } { 0 } & { { \mathrm { ~ i f ~ } } z _ { i _ { c } } + z _ { j _ { c } } + z _ { k _ { c } } = 1 , } \\ { 1 } & { { \mathrm { ~ o t h e r w i s e . } } } \end{array} \right. }
$$

Some data is presented in FIG. 1. Here we see that with a structured beginning Hamiltonian the required run times are substantially lower than with the projector $H _ { B }$ .

In the previous section we showed that removing all structure from $H _ { B }$ dooms the quantum adiabatic algorthm to failure. In this section we remove structure from the problem to be solved $H _ { P }$ ) and show that this leads to algorithmic failure. Let $h ( z )$ be a cost function whose minumum we seek. Let $\pi$ be a permutation of $0 , 1 , \ldots , N - 1$ and let

$$
h ^ { [ \pi ] } ( z ) = h \left( \pi ^ { - 1 } ( z ) \right) .
$$

We will show that no continuous time quantum algorithm (of a very general form) can find the minimum of $h ^ { [ \pi ] }$ for even a small fraction of all $\pi$ if $T$ is $o ( \sqrt { N } )$ . Classically, this problem takes order $N$ calls to an oracle.

Without loss of generality let $h ( 0 ) = 0$ , and $h ( 1 ) , h ( 2 ) , \ldots , h ( N - 1 )$ all be positive. For any permutation $\pi$ of $0 , 1 , \ldots , N - 1$ we define a problem Hamiltonian $H _ { P , \pi }$ , diagonal in the $z$ basis, as

$$
H _ { P , \pi } = \sum _ { z = 0 } ^ { N - 1 } h ^ { [ \pi ] } ( z ) | z \rangle \langle z | = \sum _ { z = 0 } ^ { N - 1 } h ( z ) | \pi ( z ) \rangle \langle \pi ( z ) | .
$$

Now consider the Hamiltonian

$$
H _ { \pi } ( t ) = H _ { D } ( t ) + c ( t ) H _ { P , \pi }
$$

for an arbitrary $\boldsymbol { \mathscr { u } }$ -independent driving Hamiltonian $H _ { D } ( t )$ with $| c ( t ) | \leq 1$ for all $t$ . Using this composite Hamiltonian, we evolve the $\pi$ -independent starting state $| \psi ( 0 ) \rangle$ for time $T$ , reaching the state $| \psi _ { \pi } ( T ) \rangle$ . This setup is more general than the quantum adiabatic algorithm since we do not require $H _ { D } ( t )$ or $c ( t )$ to be slowly varying. Success is achieved if the overlap of $| \psi _ { \pi } ( T ) \rangle$ with $| \pi ( 0 ) \rangle$ is large.

We first show

Lemma 1.

$$
\displaystyle \sum _ { \pi , \pi ^ { \prime } } \left\| | \psi _ { \pi } ( T ) \rangle - | \psi _ { \pi ^ { \prime } } ( T ) \rangle \right\| ^ { 2 } \leq 4 h ^ { * } T N ! \sqrt { N - 1 } ,
$$

where the sum is over all pairs of permutations $\pi , \pi ^ { \prime }$ that differ by a single transposition involving $\pi ( 0 )$ , and $h ^ { * } = \sqrt { \sum h ( z ) ^ { 2 } / ( N - 1 ) }$ .

Proof. For two different permutations $\pi$ and $\pi ^ { \prime }$ let $| \psi _ { \pi } ( t ) \rangle$ be the state obtained by evolving from $| \psi ( 0 ) \rangle$ with $H _ { \pi }$ and let $\vert \psi _ { \pi ^ { \prime } } ( t ) \rangle$ be the state obtained by evolving from $| \psi ( 0 ) \rangle$ with $H _ { \pi ^ { \prime } }$ . Now

$$
\begin{array} { l } { \displaystyle \frac { \mathrm { d } } { \mathrm { d } t } \Big \| | \psi _ { \pi } ( t ) \rangle - | \psi _ { \pi ^ { \prime } } ( t ) \rangle \Big \| ^ { 2 } = - \frac { \mathrm { d } } { \mathrm { d } t } \langle \psi _ { \pi } ( t ) | \psi _ { \pi ^ { \prime } } ( t ) \rangle + c . c . } \\ { = i \langle \psi _ { \pi } ( t ) | ( H _ { \pi } ( t ) - H _ { \pi ^ { \prime } } ( t ) ) | \psi _ { \pi ^ { \prime } } ( t ) \rangle + c . c . } \\ { \leq 2 \Big | \langle \psi _ { \pi } ( t ) | ( H _ { \pi } ( t ) - H _ { \pi ^ { \prime } } ( t ) ) | \psi _ { \pi ^ { \prime } } ( t ) \rangle \Big | . } \end{array}
$$

We now consider the case when $\pi$ and $\pi ^ { \prime }$ differ by a single transposition involving $\pi ( 0 )$ . Specifically, $\pi ^ { \prime } = \pi \circ ( a  0 )$ for some $a$ . Now if $\pi ( 0 ) = i$ and $\pi ( a ) = j$ , we have $\pi ^ { \prime } ( 0 ) = j$ and $\pi ^ { \prime } ( a ) = i$ . Therefore, since $h ( 0 ) = 0$ ,

$$
H _ { P , \pi } - H _ { P , \pi ^ { \prime } } = c ( t ) h ( a ) \left( | j \rangle \langle j | - | i \rangle \langle i | \right) = c ( t ) h ( a ) \left( | \pi ( a ) \rangle \langle \pi ( a ) | - | \pi ^ { \prime } ( a ) \rangle \langle \pi ^ { \prime } ( a ) | \right) ,
$$

so we can write

$$
\frac { \mathrm { d } } { \mathrm { d } t } \sum _ { \pi , \pi ^ { \prime } } \left. \left. \psi _ { \pi } ( t ) \right. - \left. \psi _ { \pi ^ { \prime } } ( t ) \right. \right. ^ { 2 } \leq 2 | c ( t ) | \sum _ { \pi , \pi ^ { \prime } } h ( a ) \Big \vert \langle \psi _ { \pi } ( t ) | \left( | \pi ( a ) \rangle \langle \pi ( a ) | - | \pi ^ { \prime } ( a ) \rangle \langle \pi ^ { \prime } ( a ) | \right) | \sin \theta \rangle \langle \pi ^ { \prime } ( a ) | .
$$

This further simplifies to

$$
\begin{array} { r l } { \displaystyle \frac { 1 } { t } \sum _ { \tau , \tau ^ { \prime \prime } } \left\| | \psi _ { x } ( t ) \rangle - | \psi _ { x ^ { \prime } } ( t ) \rangle \right\| ^ { 2 } \leq } & { 2 \sum _ { \tau , \tau ^ { \prime \prime } } h ( a ) \left( \left| \langle \psi _ { \tau } ( t ) | \tau ( a ) \rangle \right| + \left| \langle \tau ^ { \prime } ( a ) | \psi _ { \tau } ( t ) \rangle \right| \right) } \\ & { = 2 \sum _ { \tau } \displaystyle \sum _ { \alpha \neq 0 } h ( a ) \left| \langle \psi _ { \tau } ( t ) | \tau ( a ) \rangle \right| + 2 \sum _ { \tau ^ { \prime } } \sum _ { \alpha \neq 0 } h ( a ) \left| \langle \tau ^ { \prime } ( a ) | \psi _ { \tau ^ { \prime } } ( t ) \rangle \right| } \\ & { = 4 \sum _ { \tau } \displaystyle \sum _ { \alpha \neq 0 } h ( a ) \Big | \langle \psi _ { \tau } ( t ) | \pi ( a ) \rangle \Big | } \\ & { = 4 \sum _ { \tau } \displaystyle \sum _ { \alpha } h ( a ) \Big | \langle \psi _ { \tau } ( t ) | \pi ( a ) \rangle \Big | } \\ & { \leq 4 \sum _ { \tau } \displaystyle \sqrt { \sum _ { a } h ( a ) } \left| \langle \psi _ { \tau } ( t ) | \pi ( a ) \rangle \right| } \end{array}
$$

where we used the Cauchy-Schwartz inequality to obtain the last line. Integrating this inequality for time $T$ , we obtain the result we wanted to prove,

$$
\displaystyle \sum _ { \pi , \pi ^ { \prime } } \left\| | \psi _ { \pi } ( T ) \rangle - | \psi _ { \pi ^ { \prime } } ( T ) \rangle \right\| ^ { 2 } \ \leq \ 4 h ^ { * } T N ! \sqrt { N - 1 } ,
$$

where the sum is over $\pi$ and $\pi ^ { \prime }$ differing by a single transposition involving $\pi ( 0 )$ .

Next we establish

Lemma 2. Suppose $| 1 \rangle$ , $\left| 2 \right.$ , $| L \rangle$ are orthonormal vectors and $\left| \langle \psi _ { i } | i \rangle \right| ^ { 2 } \geq b$ for normalized vectors $| \psi _ { i } \rangle$ , where $i = 1 , \ldots , L$ . Then for any normalized $| \varphi \rangle$ ,

$$
\sum _ { i = 1 } ^ { L } { \Big \| } | \psi _ { i } \rangle - | \varphi \rangle { \Big \| } ^ { 2 } \geq b L - 2 { \sqrt { L } } .
$$

Proof. Write

$$
\begin{array} { l } { \displaystyle \sum _ { i } \left\| | \psi _ { i } \rangle - | \varphi \rangle \right\| ^ { 2 } \geq \displaystyle \sum _ { i } \left| \langle i | \psi _ { i } \rangle - \langle i | \varphi \rangle \right| ^ { 2 } } \\ { \geq \displaystyle \sum _ { i } \left| \langle i | \psi _ { i } \rangle \right| ^ { 2 } - 2 \displaystyle \sum _ { i } \left| \langle i | \psi _ { i } \rangle \right| \left| \langle i | \varphi \rangle \right| } \end{array}
$$

and use the Cauchy-Schwartz inequality to obtain

$$
\begin{array} { l } { \displaystyle \sum _ { i } \left\| | \psi _ { i } \rangle - | \varphi \rangle \right\| ^ { 2 } \geq b L - 2 \sqrt { \displaystyle \sum _ { i } \left| \langle i | \psi _ { i } \rangle \right| ^ { 2 } } \sqrt { \displaystyle \sum _ { i } \left| \langle i | \varphi \rangle \right| ^ { 2 } } } \\ { \geq b L - 2 \sqrt { L } . } \end{array}
$$

We are now ready to state the main result of this section.

Theorem 2. Suppose that a continuous time algorithm of the form (14) succeeds with probability at least $b$ , i.e. $\left| \langle \psi _ { \pi } ( T ) | \pi ( 0 ) \rangle \right| ^ { 2 } \geq b$ , for a set of $\epsilon N$ ! permutations. Then

$$
T \geq \frac { \epsilon ^ { 2 } b } { 1 6 h ^ { * } } \sqrt { N - 1 } - \frac { \epsilon \sqrt { \epsilon / 2 } } { 4 h ^ { * } } .
$$

Proof. For any permutation $\pi$ , there are $N - 1$ permutations $\boldsymbol { \pi } _ { a } ^ { \prime }$ obtained from $\pi$ by first transposing $0$ and $a$ . For each $\pi$ let $S _ { \pi }$ be the subset of those $N - 1$ permutations on which the algorithm succeeds with probability at least $b$ . Any such permutation appears in exactly $N - 1$ of the sets $S _ { \pi }$ so we have

$$
\sum _ { \pi } | S _ { \pi } | = ( N - 1 ) \epsilon N ! .
$$

Let $M$ be the number of sets $S _ { \pi }$ with $\begin{array} { r } { | S _ { \pi } | \geq \frac { \epsilon } { 2 } ( N - 1 ) } \end{array}$ . Now

$$
\begin{array} { r c l } { { } } & { { } } & { { \displaystyle \sum _ { \pi } | { \cal S } _ { \pi } | = \displaystyle \sum _ { | { \cal S } _ { \pi } | \geq \frac { \epsilon } { 2 } ( N - 1 ) } | { \cal S } _ { \pi } | + \displaystyle \sum _ { | { \cal S } _ { \pi } | < \frac { \epsilon } { 2 } ( N - 1 ) } | { \cal S } _ { \pi } | } } \\ { { } } & { { } } & { { \displaystyle \sum _ { \pi } | { \cal S } _ { \pi } | \leq { \cal M } ( N - 1 ) + ( N ! - { \cal M } ) \displaystyle \frac { \epsilon } { 2 } ( N - 1 ) , } } \\ { { } } & { { } } & { { ( N - 1 ) \epsilon N ! \leq { \cal M } ( N - 1 ) + N ! \displaystyle \frac { \epsilon } { 2 } ( N - 1 ) , } } \end{array}
$$

so $M \geq \frac { \epsilon } { 2 } N !$ , i.e. at least $\begin{array} { l } { \displaystyle { \frac { \epsilon } { 2 } N ! } } \end{array}$ of the sets $S _ { \pi }$ must contain at least $\frac { \epsilon } { 2 } ( N - 1 )$ permutations on which the algorithm succeeds with probability at least $b$ . For the corresponding $\pi$ , we have

$$
\sum _ { \pi _ { a } ^ { \prime } } \left\| | \psi _ { \pi } ( T ) \rangle - | \psi _ { \pi _ { a } ^ { \prime } } ( T ) \rangle \right\| ^ { 2 } \geq b \frac { \epsilon } { 2 } ( N - 1 ) - 2 \sqrt { \frac { \epsilon } { 2 } ( N - 1 ) } .
$$

by Lemma 2. (Note that the algorithm is not assumed to succeed with probability $b$ on $\pi$ .) Since there are at least $\frac { \epsilon } { 2 } N !$ such $\pi$ ,

$$
\sum _ { \pi , \pi ^ { \prime } } \left\| | \psi _ { \pi } ( T ) \rangle - | \psi _ { \pi ^ { \prime } } ( T ) \rangle \right\| ^ { 2 } \geq \frac { \epsilon } { 2 } N ! \left( b \frac { \epsilon } { 2 } ( N - 1 ) - 2 \sqrt { \frac { \epsilon } { 2 } ( N - 1 ) } \right) ,
$$

where the sum is over all permutations $\pi$ and $\pi ^ { \prime }$ which differ by a single transposition involving $\pi ( 0 )$ . Combining this with Lemma 1 we obtain

$$
T \geq \frac { \epsilon ^ { 2 } b } { 1 6 h ^ { * } } \sqrt { N - 1 } - \frac { \epsilon \sqrt { \epsilon / 2 } } { 4 h ^ { * } } ,
$$

which is what we wanted to prove.

What we have just shown is that no continuous time algorithm of the form (14) can find the minimum of $H _ { P , \pi }$ with a constant success probability for even a fraction $\epsilon N !$ of all permutations $\pi$ if $T$ is $o ( \sqrt { N } )$ . A typical permutation $\pi$ yields an $H _ { P , \pi }$ with no structure relevant to any fixed $H _ { D }$ and the algorithm can not find the ground state of $H _ { P , \pi }$ efficiently.

To illustrate the nature of this failure for the quantum adiabatic algorithm for a typical permutation, consider again the decoupled $n$ bit problem with $h ( z )$ given by (11) and $H _ { B }$ given by (12). The lowest curve in FIG. 2 shows the ground state energy divided by $n$ as a function of $t$ .

![](images/42607c8b1975609ef701d22a43375c8d22296c8a3e9be8b34d4c96cec7a37218.jpg)  
FIG. 2: The scaled ground state energy $E / n$ for a quantum adiabatic algorithm Hamiltonian of a decoupled problem. The lowest curve corresponds to the original decoupled problem. The upper “triangular” curves correspond to single instances of the $n$ -bit decoupled problem, where the problem Hamiltonian was scrambled.

(Since the system is decoupled this is actually the ground state energy of a single qubit.) We then consider the $n$ bit scrambled problem for different values of $n$ . At each $n$ we pick a single random permutation $\pi$ of $0 , \ldots , ( 2 ^ { n } - 1 )$ and apply it to obtain a cost function $h ( \pi ^ { - 1 } ( z ) )$ while keeping $H _ { B }$ fixed. The ground state energy divided by $n$ is now plotted for $n = 9 , 1 2 , 1 5$ and 18. From these scrambled problems it is clear that if we let $n$ get large the typical curves will approach a triangle with a discontinuous first derivative at $t = T / 2$ . For large $n$ , the ground state changes dramatically as $t$ passes through $T / 2$ . In order to keep the quantum system in the ground state we need to go very slowly near $t = T / 2$ and this results in a long required run time.

# IV. CONCLUSIONS

In this paper we have two main results about the performance of the quantum adiabatic algorithm when used to find the minimum of a classical cost function $h ( z )$ with $z = 0 , \ldots , N - 1$ . Theorem 1 says that for any cost function $h ( z )$ , if the beginning Hamiltonian is a one dimensional projector onto the uniform superposition of all the $| z \rangle$ basis states, the algorithm will not find the minimum of $h$ if $T$ is less then of order $\sqrt { N }$ . This is true regardless of how simple it is to classically find the minimum of $h ( z )$ .

In Theorem 2 we start with any beginning Hamiltonian and classical cost function $h$ . Replacing $h ( z )$ by a scrambled version, i.e. $h ^ { [ \pi ] } ( z ) = h ( \pi ( z ) )$ with $\pi$ a permutation of $0$ to $N - 1$ , will make it impossible for the algorithm to find the minimum of $h ^ { [ \pi ] }$ in time less than order $\sqrt { N }$ for a typical permutation $\pi$ . For example suppose we have a cost function $h ( z )$ and have chosen $H _ { B }$ so that the quantum algorithm finds the minimum in time of order $\log N$ . Still scrambling the cost function results in algorithmic failure.

These results do not imply anything about the more interesting case where $H _ { B }$ and $H _ { P }$ are structured, i.e., sums of terms each operating only on several qubits.

# Acknowledgements

The authors gratefully acknowledge support from the National Security Agency (NSA) and Advanced Research and Development Activity (ARDA) under Army Research Office (ARO) contract W911NF-04-1-0216.

# APPENDIX A: TRANSITIONS IN A TWO LEVEL SYSTEM

Let us consider a two level system with Hamiltonian

$$
H ( s ) = E _ { 0 } ( s ) | \phi _ { 0 } ( s ) \rangle \langle \phi _ { 0 } ( s ) | + E _ { 1 } ( s ) | \phi _ { 1 } ( s ) \rangle \langle \phi _ { 1 } ( s ) | ,
$$

which varies smoothly with $s = t / T$ . Here $| \phi _ { 0 } ( s ) \rangle$ and $| \phi _ { 1 } ( s ) \rangle$ are orthonormal for all $s$ . The Schr¨odinger equation reads

$$
i \frac { \mathrm { d } } { \mathrm { d } s } | \psi \rangle = T H ( s ) | \psi \rangle .
$$

The two energy levels in the system are separated by a gap

$$
g ( s ) = E _ { 1 } ( s ) - E _ { 0 } ( s ) ,
$$

which we assume is always larger than 0. Let us introduce $\theta$ (with the dimension of energy) as

$$
\theta ( s ) = \int _ { 0 } ^ { s } g ( s ^ { \prime } ) \mathrm { d } s ^ { \prime } ,
$$

and let

$$
\begin{array} { r } { | \psi ( s ) \rangle = c _ { 0 } ( s ) e ^ { - i T \int _ { 0 } ^ { s } E _ { 0 } ( s ^ { \prime } ) \mathrm { d } s ^ { \prime } } | \phi _ { 0 } ( s ) \rangle + c _ { 1 } ( s ) e ^ { - i T \int _ { 0 } ^ { s } E _ { 1 } ( s ^ { \prime } ) \mathrm { d } s ^ { \prime } } | \phi _ { 1 } ( s ) \rangle . } \end{array}
$$

We pick the phases of $| \phi _ { 1 } ( s ) \rangle$ and $| \phi _ { 0 } ( s ) \rangle$ such that $\langle \phi _ { 1 } ( s ) | _ { \mathrm { d } s } ^ { \mathrm { d } } | \phi _ { 1 } ( s ) \rangle = \langle \phi _ { 0 } ( s ) | _ { \mathrm { d } s } ^ { \mathrm { d } } | \phi _ { 0 } ( s ) \rangle = 0$ Plugging (A1) into the Schr¨odinger equation gives

$$
\begin{array} { l } { \displaystyle \frac { \mathrm { d } c _ { 0 } } { \mathrm { d } s } = c _ { 1 } e ^ { - i T \theta } \Big < \phi _ { 1 } \Big | \frac { \mathrm { d } } { \mathrm { d } s } \Big | \phi _ { 0 } \Big > ^ { * } , } \\ { \displaystyle \frac { \mathrm { d } c _ { 1 } } { \mathrm { d } s } = - c _ { 0 } e ^ { i T \theta } \Big < \phi _ { 1 } \Big | \frac { \mathrm { d } } { \mathrm { d } s } \Big | \phi _ { 0 } \Big > , } \end{array}
$$

or equivalently,

$$
\begin{array} { r c l } { { } } & { { } } & { { \displaystyle { \frac { \mathrm { d } c _ { 0 } } { \mathrm { d } \theta } } = c _ { 1 } e ^ { - i T \theta } f ^ { * } , } } \\ { { } } & { { } } & { { \displaystyle { \frac { \mathrm { d } c _ { 1 } } { \mathrm { d } \theta } } = - c _ { 0 } e ^ { i T \theta } f , } } \end{array}
$$

where

$$
f ( \theta ) \equiv \Big \langle \phi _ { 1 } \Big \vert \frac { \mathrm { d } } { \mathrm { d } \theta } \Big \vert \phi _ { 0 } \Big \rangle = - \frac { 1 } { g } \Big \langle \phi _ { 1 } \Big \vert \frac { \mathrm { d } H } { \mathrm { d } \theta } \Big \vert \phi _ { 0 } \Big \rangle = - \frac { 1 } { g ^ { 2 } } \Big \langle \phi _ { 1 } \Big \vert \frac { \mathrm { d } H } { \mathrm { d } s } \Big \vert \phi _ { 0 } \Big \rangle .
$$

Now let $\theta ( 1 ) = \theta$ . We have $c _ { 1 } ( 0 ) = 0$ and we want the transition amplitude at $s = 1$ which is

$$
\begin{array} { l } { \displaystyle { c _ { 1 } ( \bar { \theta } ) = - \int _ { 0 } ^ { \bar { \theta } } c _ { 0 } e ^ { i T \theta } f \mathrm { d } \theta } } \\ { = \displaystyle { \left[ - c _ { 0 } f \frac { e ^ { i T \theta } } { i T } \right] _ { 0 } ^ { \bar { \theta } } + \frac { 1 } { i T } \int _ { 0 } ^ { \bar { \theta } } e ^ { i T \theta } \left( \frac { \mathrm { d } c _ { 0 } } { \mathrm { d } \theta } f + c _ { 0 } \frac { \mathrm { d } f } { \mathrm { d } \theta } \right) \mathrm { d } \theta } } \\ { = \displaystyle { \frac { 1 } { T } \left( \left[ i c _ { 0 } f e ^ { i T \theta } \right] _ { 0 } ^ { \bar { \theta } } - i \int _ { 0 } ^ { \bar { \theta } } \left( c _ { 1 } f f ^ { * } + e ^ { i T \theta } c _ { 0 } \frac { \mathrm { d } f } { \mathrm { d } \theta } \right) \mathrm { d } \theta \right) } . } \end{array}
$$

Now $| c _ { 0 } | \le 1$ and $| c _ { 1 } | \le 1$ . As long as the gap does not vanish $| f ( \theta ) |$ and $\left| { \frac { \mathrm { d } { \boldsymbol { f } } } { \mathrm { d } \theta } } \right|$ are bounded so we have that $\begin{array} { r } { | c _ { 1 } ( \bar { \theta } ) | = O \left( \frac { 1 } { T } \right) } \end{array}$ . The probability of transition to the excited state for a two-level system with a nonzero gap is thus

$$
\left| c _ { 1 } ( \bar { \theta } ) \right| ^ { 2 } = O ( T ^ { - 2 } ) .
$$

[1] E. Farhi, J. Goldstone, S. Gutmann, M. Sipser, Quantum Computation by Adiabatic Evolution, quantph/0001106 (2000)   
[2] E. Farhi, S. Gutmann, Analog Analogue of a Digital Quantum Computation, Phys. Rev. A 57, 2403 (1998), quant-ph/9612026   
[3] C. H. Bennett, E. Bernstein, G. Brassard, and U. V. Vazirani, Strengths and Weaknesses of Quantum Computing, SIAM Journal on Computing 26:1510-1523 (1997), quant-ph/9701001   
[4] M. Znidariˇc, M. Horvat, ˇ Exponential Complexity of an Adiabatic Algorithm for an NP-complete Problem, quant-ph/0509162 (2005)