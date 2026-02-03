# The Complexity of the Local Hamiltonian Problem

Julia Kempe CNRS & LRI, Universit´e de Paris-Sud, 91405 Orsay, France, and UC Berkeley, Berkeley, CA94720

Alexei Kitaev Departments of Physics and Computer Science, California Institute of Technology, Pasadena, CA 91125

Oded Regev Department of Computer Science, Tel-Aviv University, Tel-Aviv 69978, Israel

November 26, 2024

# Abstract

The $k$ -LOCAL HAMILTONIAN problem is a natural complete problem for the complexity class QMA, the quantum analog of NP. It is similar in spirit to MAX- $k$ -SAT, which is NPcomplete for $k \geq 2$ . It was known that the problem is QMA-complete for any $k \geq 3$ . On the other hand 1-LOCAL HAMILTONIAN is in P, and hence not believed to be QMA-complete. The complexity of the 2-LOCAL HAMILTONIAN problem has long been outstanding. Here we settle the question and show that it is QMA-complete. We provide two independent proofs; our first proof uses only elementary linear algebra. Our second proof uses a powerful technique for analyzing the sum of two Hamiltonians; this technique is based on perturbation theory and we believe that it might prove useful elsewhere. Using our techniques we also show that adiabatic computation with two-local interactions on qubits is equivalent to standard quantum computation.

# 1 Introduction

Quantum complexity theory has emerged alongside the first efficient quantum algorithms in an attempt to formalize the notion of an efficient algorithm. In analogy to classical complexity theory, several new quantum complexity classes have appeared. A major challenge today consists in understanding their structure and the interrelation between classical and quantum classes.

One of the most important classical complexity classes is NP - nondeterministic polynomial time. This class comprises languages that can be verified in polynomial time by a deterministic verifier. The celebrated Cook-Levin theorem (see, e.g., [Pap94]) shows that this class has complete problems. More formally, it states that SAT is NP-complete, i.e., it is in NP and any other language in NP can be reduced to it with polynomial overhead. In SAT we are given a set of clauses (disjunctions) over $n$ variables and asked whether there is an assignment that satisfies all clauses. One can consider the restriction of SAT in which each clause consists of at most $k$ literals. This is known as the $k$ -SAT problem. It is known that 3-SAT is still NP-complete while 2-SAT is in $\mathsf { P }$ , i.e., has a polynomial time solution. We can also consider the MAX- $k$ -SAT problem: here, given a $k$ -SAT formula and a number $m$ we are asked whether there exists an assignment that satisfies at least $m$ clauses. It turns out that MAX-2-SAT is already NP-complete; MAX-1-SAT is clearly in P.

The class QMA is the quantum analogue of NP in a probabilistic setting, i.e., the class of all languages that can be probabilistically verified by a quantum verifier in polynomial time (the name is derived from the classical class MA, which is the randomized analogue of NP). This class, which is also called BQNP, was first studied in [Kni96, KSV02]; the name QMA was given to it by Watrous [Wat00]. Several problems in QMA have been identified [Wat00, KSV02, JWB03]. For a good introduction to the class QMA, see the book by Kitaev et al. [KSV02] and the paper by Watrous [Wat00].

Kitaev, inspired by ideas due to Feynman, defined the quantum analogue of the classical SAT problem, the LOCAL HAMILTONIAN problem [KSV02].1 An instance of $k$ -LOCAL HAMILTONIAN can be viewed as a set of local constraints on $n$ qubits, each involving at most $k$ of them. We are asked whether there is a state of the $n$ qubits such that the expected number of violated constraints is either below a certain threshold or above another, with a promise that one of the two cases holds and both thresholds are at least a constant apart. More formally, we are to determine whether the groundstate energy of a given $k$ -local Hamiltonian is below one threshold or above another.

Kitaev proved [KSV02] that the 5-LOCAL HAMILTONIAN problem is QMA-complete. Later, Kempe and Regev showed that already 3-LOCAL HAMILTONIAN is complete for QMA [KR03]. In addition, it is easy to see that 1-LOCAL HAMILTONIAN is in P. The complexity of the 2-LOCAL HAMILTONIAN problem was left as an open question in [AN02, WB03, KR03, BV05]. It is not hard to see that the $k$ -LOCAL HAMILTONIAN problem contains the MAX-K-SAT problem as a special case.2 Using the known NP-completeness of MAX-2-SAT, we obtain that 2-LOCAL HAMILTONIAN is NP-hard, i.e., any problem in NP can be reduced to it with polynomial overhead. But is it also QMA-complete? Or perhaps it lies in some intermediate class between NP and QMA? Some special cases of the problem were considered by Bravyi and Vyalyi [BV05]; however, the question still remained open.

In this paper we settle the question of the complexity of 2-LOCAL HAMILTONIAN and show

Theorem 1 The 2-LOCAL HAMILTONIAN problem is QMA-complete.

In [KSV02] it was shown that the $k$ -LOCAL HAMILTONIAN problem is in QMA for any constant $k$ (and in fact even for $k = O ( \log n )$ where $n$ is the total number of qubits). Hence, our task in this paper is to show that any problem in QMA can be reduced to the 2-LOCAL HAMILTONIAN problem with a polynomial overhead. We give two self-contained proofs for this.

Our first proof is based on a careful selection of gates in a quantum circuit and several applications of a lemma called the projection lemma. The proof is quite involved; however, it uses only elementary linear algebra and hence might appeal to some readers.

Our second proof is based on perturbation theory – a collection of techniques that are used to analyze sums of Hamiltonians. This proof is more mathematically involved. Nevertheless, it might give more intuition as to why the 2-LOCAL HAMILTONIAN problem is QMA-complete. Unlike the first proof which shows how to represent any QMA circuit by a 2-local Hamiltonian, the second proof shows a reduction from the 3-LOCAL HAMILTONIAN problem (which is already known to be QMA-complete [KR03]) to the 2-LOCAL HAMILTONIAN problem. To the best of our knowledge, this is the first reduction inside QMA (i.e., not from the circuit problem). This proof involves what is known as third order perturbation theory (interestingly, the projection lemma used in our first proof can be viewed as an instance of first order perturbation theory). We are not aware of any similar application of perturbation theory in the literature and we hope that our techniques will be useful elsewhere.

Adiabatic computation: It has been shown in $[ \mathrm { A v K ^ { + } 0 4 } ]$ that the model of adiabatic computation with 3-local interactions is equivalent to the standard model of quantum computation (i.e., the quantum circuit model).3 We strengthen this result by showing that 2-local interactions suffice.4 Namely, the model of adiabatic computation with 2-local interactions is equivalent to the standard model of quantum computation. We obtain this result by applying the technique of perturbation theory, which we develop in the second proof of the main theorem.

Recent work: After a preliminary version of our paper has appeared [KKR04], Oliveira and Terhal [OT05] have generalized our results and have shown that the 2-LOCAL HAMILTONIAN problem remains QMA-complete even if the Hamiltonians are restricted to nearest neighbor interactions between qubits on a 2-dimensional grid. Similarly, they show that the model of adiabatic computation with 2-local Hamiltonians between nearest neighbor qubits on a 2-dimensional grid is equivalent to standard quantum computation. Their proof applies the perturbation theory techniques that we develop in this paper and introduces several novel “perturbation gadgets” akin to our three-qubit gadget in Section 6.2.

Structure: We start by describing our notation and some basics in Section 2. Our first proof is developed in Sections 3, 4 and 5. The main tool in this proof, which we name the projection lemma, appears in Section 3. Using this lemma, we rederive in Section 4 some of the previously known results. Then we give the first proof of our main theorem in Section 5. In Section 6 we give the second proof of our main theorem. This proof does not require the projection lemma and is in fact independent of the first proof. Hence, some readers might choose to skip Sections 3, 4 and 5 and go directly to Section 6. In Section 7 we show how to use our techniques to prove that 2-local adiabatic computation is equivalent to standard quantum computation. Some open questions are mentioned in Section 8.

# 2 Preliminaries

QMA is naturally defined as a class of promise problems: A promise problem $L$ is a pair $( L _ { y e s } , L _ { n o } )$ of disjoint sets of strings corresponding to YES and NO instances of the problem. The problem is to determine, given a string $x \in L _ { y e s } \cup L _ { n o } ,$ whether $x \in L _ { y e s }$ or $x \in L _ { n o }$ . Let $\boldsymbol { B }$ be the Hilbert space of a qubit.

Definition 1 (QMA) Fix $\varepsilon = \varepsilon ( | x | )$ such that $\varepsilon = 2 ^ { - \Omega ( | x | ) }$ . Then, a promise problem $L$ is in QMA if there exists a quantum polynomial time verifier $V$ and a polynomial $p$ such that:

$$
\begin{array} { r l } { - \ \forall x \in L _ { y e s } } & { \exists | \xi \rangle \in B ^ { \otimes p ( | x | ) } \quad \operatorname* { P r } \left( V ( | x \rangle , | \xi \rangle ) = 1 \right) \geq 1 - \varepsilon } \\ { - \ \forall x \in L _ { n o } } & { \forall | \xi \rangle \in B ^ { \otimes p ( | x | ) } \quad \operatorname* { P r } \left( V ( | x \rangle , | \xi \rangle ) = 1 \right) \leq \varepsilon } \end{array}
$$

where $\operatorname* { P r } \left( V ( | x \rangle , | \xi \rangle ) = 1 \right)$ ) denotes the probability that $V$ outputs 1 given $| x \rangle$ and $| \xi \rangle$

We note that in the original definition $\varepsilon$ was defined to be $2 ^ { - \Omega ( | x | ) } \leq \varepsilon \leq 1 / 3$ . By using amplification methods, it was shown in [KSV02] that for any choice of $\varepsilon$ in this range the resulting classes are equivalent. Hence our definition is equivalent to the original one. In a related result, Marriott and Watrous [MW04] showed that exponentially small $\varepsilon$ can be achieved without amplification with a polynomial overhead in the verifier’s computation.

A natural choice for the quantum analogue of SAT is the LOCAL HAMILTONIAN problem. As we will see later, this problem is indeed a complete problem for QMA.

Definition 2 We say that an operator $H : B ^ { \otimes n } \to B ^ { \otimes n }$ on n qubits is a $k$ -local Hamiltonian if $H$ is expressible as $\begin{array} { r } { H = \sum _ { j = 1 } ^ { r } H _ { j } } \end{array}$ where each term is a Hermitian operator acting on at most $k$ qubits.

Definition 3 The (promise) problem $k$ -LOCAL HAMILTONIAN is defined as follows. We are given a $k$ - local Hamiltonian on $n$ -qubits $\begin{array} { r } { H = \sum _ { j = 1 } ^ { r } H _ { j } } \end{array}$ with $r = \mathrm { p o l y } ( n )$ . Each $H _ { j }$ has a bounded operator norm $\| H _ { j } \| \le \mathrm { p o l y } ( n )$ and its entries are specified by poly $( n )$ bits. In addition, we are given two constants a and $b$ with $a < b$ . In YES instances, the smallest eigenvalue of $H$ is at most a. In NO instances, it is larger than $b$ . We should decide which one is the case.

We will frequently refer to the lowest eigenvalue of some Hamiltonian $H$

Definition 4 Let $\lambda ( H )$ denote the lowest eigenvalue of the Hamiltonian $H$

Another important notion that will be used in this paper is that of a restriction of a Hamiltonian.

Definition 5 Let $H$ be a Hamiltonian and let Π be a projection on some subspace $\boldsymbol { \mathcal { S } }$ . Then we say that the Hamiltonian ΠHΠ on $\boldsymbol { \mathcal { S } }$ is the restriction of $H$ to $\boldsymbol { s }$ . We denote this restriction by $H | _ { S }$ .

# 3 Projection Lemma

Our main technical tool is the projection lemma. This lemma (in a slightly different form) was already used in [KR03] and $[ \mathrm { A v K ^ { + } 0 4 } ]$ but not as extensively as it is used in this paper (in fact, we apply it four times in the first proof of our main theorem). The lemma allows us to successively cut out parts of the Hilbert space by giving them a large penalty. More precisely, assume we work in some Hilbert space $\mathcal { H }$ and let $H _ { 1 }$ be some Hamiltonian. For some subspace $s \subseteq \varkappa ,$ let $H _ { 2 }$ be a Hamiltonian with the property that $\boldsymbol { s }$ is an eigenspace of eigenvalue 0 and $S ^ { \perp }$ has eigenvalues at least $J$ for some large $J \gg \| H _ { 1 } \|$ . In other words, $H _ { 2 }$ gives a very high penalty to states in $S ^ { \perp }$ . Now consider the Hamiltonian $H = H _ { 1 } + H _ { 2 }$ . The projection lemma says that $\lambda ( H )$ , the lowest eigenvalue of $H$ , is very close to $\lambda ( H _ { 1 } | _ { \cal S } )$ , the lowest eigenvalue of the restriction of $H _ { 1 }$ to $s$ . The intuitive reason for this is the following. By adding $H _ { 2 }$ we give a very high penalty to any vector that has even a small projection in the $\mathcal { S } ^ { \perp }$ direction. Hence, all eigenvectors with low eigenvalue (and in particular the one corresponding to $\lambda ( H ) ,$ ) have to lie very close to $\boldsymbol { s }$ . From this it follows that these eigenvectors correspond to the eigenvectors of $H _ { 1 } | _ { \cal S }$ .

The strength of this lemma comes from the following fact. Even though $H _ { 1 }$ and $H _ { 2 }$ are local Hamiltonians, $H _ { 1 } | _ { \cal S }$ is not necessarily so. In other words, the projection lemma allows us to approximate a non-local Hamiltonian by a local Hamiltonian.

Lemma 1 Let $H = H _ { 1 } + H _ { 2 }$ be the sum of two Hamiltonians operating on some Hilbert space $\mathcal { H } = \mathcal { S } + \mathcal { S } ^ { \perp }$ . The Hamiltonian $H _ { 2 }$ is such that $s$ is a zero eigenspace and the eigenvectors in $S ^ { \perp }$ have eigenvalue at least $J > 2 \| H _ { 1 } \|$ . Then,

$$
\lambda ( H _ { 1 } | _ { \cal S } ) - \frac { \| H _ { 1 } \| ^ { 2 } } { J - 2 \| H _ { 1 } \| } \le \lambda ( H ) \le \lambda ( H _ { 1 } | _ { \cal S } ) .
$$

Notice that with, say, $J \ge 8 \| H _ { 1 } \| ^ { 2 } + 2 \| H _ { 1 } \| = \mathrm { p o l y } ( \| H _ { 1 } \| )$ we have $\lambda ( H _ { 1 } | _ { \cal S } ) - 1 / 8 \le \lambda ( H ) \le$ $\lambda ( H _ { 1 } | _ { \cal S } )$ .

Proof: First, we show that $\lambda ( H ) \leq \lambda ( H _ { 1 } | _ { \cal { S } } )$ . Let $| \eta \rangle \in \mathcal { S }$ be the eigenvector of $H _ { 1 } | _ { \cal S }$ corresponding to $\lambda ( H _ { 1 } | _ { \cal S } )$ . Using $H _ { 2 } | \eta \rangle = 0 .$ ,

$$
\langle \eta | H | \eta \rangle = \langle \eta | H _ { 1 } | \eta \rangle + \langle \eta | H _ { 2 } | \eta \rangle = \lambda ( H _ { 1 } | \varsigma )
$$

and hence $H$ must have an eigenvector of eigenvalue at most $\lambda ( H _ { 1 } | _ { \cal S } )$ .

We now show the lower bound on $\lambda ( H )$ . We can write any unit vector $\vert v \rangle \in \mathcal { H }$ as $| v \rangle =$ $\alpha _ { 1 } | v _ { 1 } \rangle + \alpha _ { 2 } | v _ { 2 } \rangle$ where $\vert v _ { 1 } \rangle \in S$ and $\left| v _ { 2 } \right. \in \mathcal { S } ^ { \perp }$ are two unit vectors, $\alpha _ { 1 } , \alpha _ { 2 } \in \mathbb { R } , \alpha _ { 1 } , \alpha _ { 2 } \geq 0$ and $\alpha _ { 1 } ^ { 2 } + \alpha _ { 2 } ^ { 2 } = 1$ . Let $K = \| H _ { 1 } \|$ . Then we have,

$$
\begin{array} { l l l } { \langle v | H | v \rangle } & { \ge } & { \langle v | H _ { 1 } | v \rangle + J \alpha _ { 2 } ^ { 2 } } \\ & { = } & { ( 1 - \alpha _ { 2 } ^ { 2 } ) \langle v _ { 1 } | H _ { 1 } | v _ { 1 } \rangle + 2 \alpha _ { 1 } \alpha _ { 2 } \mathrm { R e } \langle v _ { 1 } | H _ { 1 } | v _ { 2 } \rangle + \alpha _ { 2 } ^ { 2 } \langle v _ { 2 } | H _ { 1 } | v _ { 2 } \rangle + J \alpha _ { 2 } ^ { 2 } } \\ & { \ge } & { \langle v _ { 1 } | H _ { 1 } | v _ { 1 } \rangle - K \alpha _ { 2 } ^ { 2 } - 2 K \alpha _ { 2 } - K \alpha _ { 2 } ^ { 2 } + J \alpha _ { 2 } ^ { 2 } } \\ & { = } & { \langle v _ { 1 } | H _ { 1 } | v _ { 1 } \rangle + ( J - 2 K ) \alpha _ { 2 } ^ { 2 } - 2 K \alpha _ { 2 } } \\ & { \ge } & { \lambda ( H _ { 1 } | \boldsymbol { s } ) + ( J - 2 K ) \alpha _ { 2 } ^ { 2 } - 2 K \alpha _ { 2 } } \end{array}
$$

where we used $\alpha _ { 1 } ^ { 2 } = 1 - \alpha _ { 2 } ^ { 2 }$ and $\alpha _ { 1 } \leq 1$ . Since $( J - 2 K ) \alpha _ { 2 } ^ { 2 } - 2 K \alpha _ { 2 }$ is minimized for $\alpha _ { 2 } = K / ( J { - } 2 K ) ,$ we have

$$
\langle v | H | v \rangle \geq \lambda ( H _ { 1 } | s ) - { \frac { K ^ { 2 } } { J - 2 K } } .
$$

# 4 Kitaev’s Construction

In this section we reprove Kitaev’s result that $O ( \log n )$ -LOCAL HAMILTONIAN is QMA-complete. The difference between our version of the proof and the original one in [KSV02] is that we do not use their geometrical lemma to obtain the result, but rather apply our Lemma 1. This paves the way to the later proof that 2-LOCAL HAMILTONIAN is QMA-complete.

As mentioned before, the proof that $O ( \log n )$ -LOCAL HAMILTONIAN is in QMA appears in [KSV02]. Hence, our goal is to show that any problem in QMA can be reduced to $O ( \log n )$ -LOCAL HAMILTONIAN. Let $V _ { x } = V ( | x \rangle , \cdot ) = U _ { T } \cdot \cdot \cdot U _ { 1 }$ be a quantum verifier circuit of size $T = \mathrm { p o l y } ( | x | )$ operating on $N = \mathrm { p o l y } ( | x | )$ qubits.5 Here and in what follows later we assume without loss of generality that each $U _ { i }$ is either a one-qubit gate or a two-qubit gate. We further assume that $T \geq N$ and that initially, the first $m = p ( | x | )$ qubits contain the proof and the remaining ancillary $N - m$ qubits are zero (see Definition 1). Finally, we assume that the output of the circuit is written into the first qubit (i.e., it is $| 1 \rangle$ if the circuit accepts). See Figure 1.

![](images/9ede6dff7363ca82d16ba31d27bab6f2bb86c8083043b228beb7cccf7f6b93b7.jpg)  
Figure 1: A circuit with $T = 1 1$ , $N = 4$ and $m = 2$ .

The constructed Hamiltonian $H$ operates on a space of $n = N + \log ( T + 1 )$ qubits. The first $N$ qubits represent the computation and the last $\log ( T + 1 )$ qubits represent the possible values $0 , \ldots , T$ for the clock:

$$
H = H _ { o u t } + J _ { i n } H _ { i n } + J _ { p r o p } H _ { p r o p } .
$$

The coefficients $J _ { i n }$ and $J _ { p r o p }$ will be chosen later to be some large polynomials in $N$ . The terms are given by

$$
\begin{array} { r l r } { H _ { i n } = \displaystyle \sum _ { i = m + 1 } ^ { N } | 1 \rangle \langle 1 | _ { i } \otimes | 0 \rangle \langle 0 | \qquad } & { H _ { o u t } = ( T + 1 ) | 0 \rangle \langle 0 | _ { 1 } \otimes | T \rangle \langle T | } & \\ { H _ { p r o p } = \displaystyle \sum _ { t = 1 } ^ { T } H _ { p r o p , t } } & \end{array}
$$

and

$$
H _ { p r o p , t } = \frac { 1 } { 2 } \left( I \otimes | t \rangle \langle t | + I \otimes | t - 1 \rangle \langle t - 1 | - U _ { t } \otimes | t \rangle \langle t - 1 | - U _ { t } ^ { \dagger } \otimes | t - 1 \rangle \langle t | \right)
$$

for $1 \leq t \leq T$ where $| \alpha \rangle \langle \alpha | _ { i }$ denotes the projection on the subspace in which the $i ^ { \prime } \mathrm { t h }$ qubit is $| \alpha \rangle$ . It is understood that the first part of each tensor product acts on the space of the $N$ computation qubits and the second part acts on the clock qubits. $U _ { t }$ and $U _ { t } ^ { \dagger }$ in $H _ { p r o p , t }$ act on the same computational qubits as $U _ { t }$ does when it is employed in the verifier’s circuit $V _ { x }$ . Intuitively, each

Hamiltonian ‘checks’ a certain property by increasing the eigenvalue if the property doesn’t hold: The Hamiltonian $H _ { i n }$ checks that the input of the circuit is correct (i.e., none of the last $N - m$ computation qubits is 1), $H _ { o u t }$ checks that the output bit indicates acceptance and $H _ { p r o p }$ checks that the propagation is according to the circuit. Notice that these Hamiltonians are $O ( \log n )$ -local since there are $\log ( T + 1 ) = O ( \log n )$ clock qubits.

To show that a problem in QMA reduces to the $O ( \log n )$ -LOCAL HAMILTONIAN problem with $H$ chosen as above, we prove the following lemma.

Lemma 2 If the circuit $V _ { x }$ accepts with probability more than $1 - \varepsilon$ on some input $| \xi , 0 \rangle$ , then the Hamiltonian $H$ has an eigenvalue smaller than $\varepsilon$ . If the circuit $V _ { x }$ accepts with probability less than $\varepsilon$ on all inputs $| \xi , 0 \rangle$ , then all eigenvalues of $H$ are larger than $\frac { 3 } { 4 } - \varepsilon$ .

Proof: Assume the circuit $V _ { x }$ accepts with probability more than $1 - \varepsilon$ on some $| \xi , 0 \rangle$ . Define

$$
| \eta \rangle = \frac { 1 } { \sqrt { T + 1 } } \sum _ { t = 0 } ^ { T } U _ { t } \cdot \cdot \cdot U _ { 1 } | \xi , 0 \rangle \otimes | t \rangle .
$$

It can be seen that $\langle \eta | H _ { p r o p } | \eta \rangle = \langle \eta | H _ { i n } | \eta \rangle = 0$ and that $\langle \eta | H _ { o u t } | \eta \rangle \ < \ \varepsilon$ . Hence, the smallest eigenvalue of $H$ is less than $\varepsilon$ . It remains to prove the second part of the lemma. So now assume the circuit $V _ { x }$ accepts with probability less than $\varepsilon$ on all inputs $| \xi , 0 \rangle$ .

Let $ { \boldsymbol { S } } _ { p r o p }$ be the groundspace of the Hamiltonian $H _ { p r o p }$ . It is easy to see that $ { \boldsymbol { S } } _ { p r o p }$ is a $2 ^ { N }$ dimensional space whose basis is given by the states

$$
| \eta _ { i } \rangle = { \frac { 1 } { \sqrt { T + 1 } } } \sum _ { t = 0 } ^ { T } U _ { t } \cdot \cdot \cdot U _ { 1 } | i \rangle \otimes | t \rangle
$$

where $i \in \{ 0 , \ldots , 2 ^ { N } - 1 \}$ and $| i \rangle$ represents the $i$ th vector in the computational basis on the $N$ computation qubits. These states have eigenvalue 0. The states in $ { \boldsymbol { S } } _ { p r o p }$ represent the correct propagation from an initial state on the $N$ computation qubits according to the verifier’s circuit $V _ { x }$ .

We would like to apply Lemma 1 with the space $ { \boldsymbol { S } } _ { p r o p }$ . For that, we need to establish that $J _ { p r o p } H _ { p r o p }$ gives a sufficiently large $\mathrm { ( p o l y } ( N ) )$ penalty to states in $\mathcal { S } _ { p r o p } ^ { \perp }$ . In other words, the smallest non-zero eigenvalue of $H _ { p r o p }$ has to be lower bounded by some inverse polynomial in $N$ . This has been shown in [KSV02], but we wish to briefly recall it here, as it will apply in several instances throughout this paper.

Claim 2 ([KSV02]) The smallest non-zero eigenvalue of $H _ { p r o p }$ is at least $c / T ^ { 2 }$ for some constant $c > 0$ .

Proof: We first apply the change of basis

$$
W = \sum _ { t = 0 } ^ { T } U _ { t } \cdot \cdot \cdot U _ { 1 } \otimes | t \rangle \langle t |
$$

which transforms $H _ { p r o p }$ to

$$
W ^ { \dagger } H _ { p r o p } W = \sum _ { t = 1 } ^ { T } I \otimes \frac { 1 } { 2 } \left( | t \rangle \langle t | + | t - 1 \rangle \langle t - 1 | - | t \rangle \langle t - 1 | - | t - 1 \rangle \langle t | \right) .
$$

The eigenspectrum of $H _ { p r o p }$ is unchanged by this transformation. The resulting Hamiltonian is block-diagonal with $2 ^ { N }$ blocks of size $T + 1$ .

$$
\begin{array} { r l r } { W ^ { \dagger } H _ { p r o p } W } & { = } & { I \otimes \left( \begin{array} { c c c c c c c } { \frac 1 2 } & { - \frac 1 2 } & { 0 } & { \cdots } & { 0 } & { 0 } \\ { - \frac 1 2 } & { 1 } & { - \frac 1 2 } & { 0 } & { \ddots } & { } & { \vdots } \\ { 0 } & { - \frac 1 2 } & { 1 } & { - \frac 1 2 } & { 0 } & { \ddots } & { } \\ { \ddots } & { \ddots } & { \ddots } & { \ddots } & { \ddots } & { } \\ { \vdots } & { 0 } & { - \frac 1 2 } & { 1 } & { - \frac 1 2 } & { 0 } \\ { 0 } & { 0 } & { - \frac 1 2 } & { 1 } & { - \frac 1 2 } \\ { 0 } & { \cdots } & { 0 } & { 0 } & { - \frac 1 2 } & { \frac 1 2 } \end{array} \right) . } \end{array}
$$

Using standard techniques, one can show that the smallest non-zero eigenvalue of each $( T + 1 ) \times$ $( T + 1 )$ block matrix is bounded from below by $c / T ^ { 2 }$ , for some constant $c > 0$ .

Hence any eigenvector of $J _ { p r o p } H _ { p r o p }$ orthogonal to $ { \boldsymbol { S } } _ { p r o p }$ has eigenvalue at least $J = { c J _ { p r o p } } / { T ^ { 2 } }$ . Let us apply Lemma 1 with

$$
H _ { 1 } = H _ { o u t } + J _ { i n } H _ { i n } \phantom { 0 0 0 0 0 0 } H _ { 2 } = J _ { p r o p } H _ { p r o p } .
$$

Note that $\begin{array} { r } { \| H _ { 1 } \| \leq \| H _ { o u t } \| + J _ { i n } \| H _ { i n } \| \leq T + 1 + J _ { i n } N \leq \mathrm { p o l y } ( N ) } \end{array}$ since $H _ { i n }$ and $H _ { o u t }$ are sums of orthogonal projectors and $J _ { i n } = \mathrm { p o l y } ( N )$ . Lemma 1 implies that we can choose $J _ { p r o p } = J T ^ { 2 } / c =$ $\mathrm { p o l y } ( N ) .$ , such that $\lambda ( H )$ is lower bounded by $\begin{array} { r } { \lambda ( H _ { 1 } | _ { S _ { p r o p } } ) \ : - \ : \frac { 1 } { 8 } } \end{array}$ . With this in mind, let us now consider the Hamiltonian $H _ { 1 } | _ { S _ { p r o p } }$ on $ { \boldsymbol { S } } _ { p r o p }$ .

Let $S _ { i n } \subset S _ { p r o p }$ be the groundspace of $H _ { i n } | _ { S _ { p r o p } }$ . Then $\mathcal { S } _ { i n }$ is a $2 ^ { m }$ -dimensional space whose basis is given by states as in Eq. (3) with $\left| i \right. = \left| j , 0 \right.$ , where $| j \rangle$ is a computational basis state on the first $m$ computation qubits. We apply Lemma 1 again inside $ { \boldsymbol { S } } _ { p r o p }$ with

$$
H _ { 1 } = H _ { o u t } | _ { \cal S _ { p r o p } } H _ { 2 } = J _ { i n } H _ { i n } | _ { \cal S _ { p r o p } } .
$$

This time, $\lVert H _ { 1 } \rVert \le \lVert H _ { o u t } \rVert = T + 1 = \mathrm { p o l y } ( N )$ . Any eigenvector of $H _ { 2 }$ orthogonal to $\mathcal { S } _ { i n }$ inside $ { \boldsymbol { S } } _ { p r o p }$ has eigenvalue at least $J _ { i n } / ( T + 1 )$ . Hence, there is a $J _ { i n } = \mathrm { p o l y } ( N )$ such that $\lambda ( H _ { 1 } + H _ { 2 } )$ is lower bounded by $\begin{array} { r } { \lambda ( H _ { o u t } | _ { S _ { i n } } ) - \frac { 1 } { 8 } } \end{array}$ .

Since the circuit $V _ { x }$ accepts with probability less than $\varepsilon$ on all inputs $| \xi , 0 \rangle$ , we have that all eigenvalues of $H _ { o u t } | _ { S _ { i n } }$ are larger than $1 - \varepsilon$ . Hence the smallest eigenvalue of $H$ is larger than $\begin{array} { r } { 1 - \varepsilon - \frac { 2 } { 8 } = \frac { 3 } { 4 } - \varepsilon , } \end{array}$ S  proving the second part of the lemma. •

# 5 The 2-local Construction

Previous constructions: Let us give an informal description of ideas used in previous improvements on Kitaev’s construction; these ideas will also appear in our proof. The first idea is to represent the clock register in unary notation. Then, the clock register consists of $T$ qubits and time step $t \in \{ 0 , \ldots , T \}$ is represented by $\lvert 1 ^ { t } 0 ^ { T - t } \rangle$ . The crucial observation is that clock terms that used to involve $\log ( T + 1 )$ qubits, can now be replaced by 3-local terms that are essentially equivalent. For example, a term like $\left| { t - 1 } \right. \left. { t } \right|$ can be replaced by the term $| 1 0 0 \rangle \langle 1 1 0 | _ { t - 1 , t , t + 1 }$ . Since the gates $U _ { t }$ involve at most two qubits, we obtain a 5-local Hamiltonian. This is essentially the way 5-LOCAL HAMILTONIAN was shown to be QMA-complete in [KSV02]. The only minor complication is that we need to get rid of illegal clock states (i.e., ones that are not a unary representation). This is done by the addition of a (2-local) Hamiltonian $H _ { c l o c k }$ that penalizes a clock state whenever 1 appears after 0.

This result was further improved to 3-LOCAL HAMILTONIAN in [KR03]. The main idea there is to replace a 3-local clock term like $| 1 0 0 \rangle \langle 1 1 0 | _ { t - 1 , t , t + 1 }$ by the 1-local term $| 0 \rangle \langle 1 | _ { t }$ . These one-qubit terms are no longer equivalent to the original clock terms. Indeed, it can be seen that they have unwanted transitions into illegal clock states. The main idea in [KR03] was that by giving a large penalty to illegal clock states (i.e., by multiplying $H _ { c l o c k }$ by some large number) and applying the projection lemma, we can essentially project these one-qubit terms to the subspace of legal clock states. Inside this subspace, these terms become the required clock terms.

The 2-local construction: Most of the terms that appear in the construction of [KR03] are already 2-local. The only 3-local terms are terms as in Eq. (2) that correspond to two-qubit gates (those corresponding to one-qubit gates are already 2-local). Hence, in order to prove our main theorem, it is enough to find a 2-local Hamiltonian that checks for the correct propagation of 2-qubit gates. This seems difficult because the Hamiltonian must somehow couple two computation qubits to a clock qubit. We circumvent this problem in the following manner. First, we isolate from the propagation Hamiltonian those terms that correspond to one-qubit gates and we multiply these terms by some large factor. Using the projection lemma, we can project the remaining Hamiltonians into a space where the 1-qubit-gate propagation is correct. In other words, at this stage we can assume that our space is spanned by states that correspond to legal propagation according to the 1-qubit gates. This allows us to couple clock qubits instead of computation qubits. To see this, consider the circuit in Fig. 2 at time $t$ and at time $t + 2$ . A $Z$ gate flips the phase of a qubit if its state is $| 1 \rangle$ and leaves it unchanged otherwise. Hence, the phase difference between time $t$ and time $t + 2$ corresponds to the parity of the two qubits. This phase difference can be detected by a 2-local term such as $| 0 0 \rangle \langle 1 1 | _ { t + 1 , t + 2 }$ . The crucial point here is that by using a term involving only two clock qubits, we are able to check the state of two computation qubits (in this case, their parity) at a certain time. This is the main idea in our proof.

We now present the proof of the main theorem in detail. We start by making some further assumptions on the circuit $V _ { x } ,$ all without loss of generality. First, we assume that in addition to one-qubit gates, the circuit contains only the controlled phase gate, $C _ { \phi }$ . This two-qubit gate is diagonal in the computational basis and flips the sign of the state $\left| 1 1 \right.$ ,

$$
C _ { \phi } = { C _ { \phi } } ^ { \dagger } = | 0 0 \rangle \langle 0 0 | + | 0 1 \rangle \langle 0 1 | + | 1 0 \rangle \langle 1 0 | - | 1 1 \rangle \langle 1 1 | .
$$

It is known $[ { \mathrm { B B C } } ^ { + } 9 5 $ , NC00] that quantum circuits consisting of one-qubit gates and $C _ { \phi }$ gates are universal6 and can simulate any other quantum circuit with only polynomial overhead. Second, we assume that each $C _ { \phi }$ gate is both preceded and followed by two $Z$ gates, one on each qubit, as in Figure 2. The $Z$ gate is defined by $| 0 \rangle \langle 0 | - | 1 \rangle \langle 1 | ;$ i.e., it is a diagonal one-qubit gate that flips the sign of $| 1 \rangle$ . Since both the $Z$ gate and the $C _ { \phi }$ gate are diagonal, they commute and the effect of the $Z$ -gates cancels out. This assumption makes the circuit at most five times bigger. Finally, we assume that the $C _ { \phi }$ gates are applied at regular intervals. In other words, if $T _ { 2 }$ is the number of $C _ { \phi }$ gates and $L$ is the interval length, then a $C _ { \phi }$ gate is applied at steps $L , 2 L , \dots , T _ { 2 } L $ . Before the first $C _ { \phi }$ gate, after the last $C _ { \phi }$ gate and between any two consecutive $C _ { \phi }$ gates we have $L - 1$ one-qubit gates. This makes the total number of gates in the resulting circuit $T = ( T _ { 2 } + 1 ) L - 1$ .

![](images/a4a565d665f72621a576cc2279306a65e56b4c3cf900e187db0fae48fe140c2d.jpg)  
Figure 2: A modified $C _ { \phi }$ gate applied at step $t$

We construct a Hamiltonian $H$ that operates on a space of $N + T$ qubits. The first $N$ qubits represent the computation and the last $T$ qubits represent the clock. We think of the clock as represented in unary,

$$
| \widehat { t } \rangle \stackrel { d e f } { = } | \underbrace { 1 \ldots } _ { t } \underbrace { 1 } _ { T - t } \underbrace { 0 \ldots 0 } _ { T - t } \rangle .
$$

Let $T _ { 1 }$ be the time steps in which a one-qubit gate is applied. Namely, $T _ { 1 } = \{ 1 , \dots , T \} \backslash \{ L , 2 L , \dots , T _ { 2 } L \}$ Then

$$
H = H _ { o u t } + J _ { i n } H _ { i n } + J _ { 2 } H _ { p r o p 2 } + J _ { 1 } H _ { p r o p 1 } + J _ { c l o c k } H _ { c l o c k } ,
$$

where

$$
\begin{array} { l l } { { H _ { i n } = \displaystyle \sum _ { i = m + 1 } ^ { N } | 1 \rangle \langle 1 | _ { i } \otimes | 0 \rangle \langle 0 | _ { 1 } \qquad } } & { { H _ { o u t } = ( T + 1 ) | 0 \rangle \langle 0 | _ { 1 } \otimes | 1 \rangle \langle 1 | _ { T } } } \\ { { H _ { c l o c k } = \displaystyle \sum _ { 1 \leq i < j \leq T } I \otimes | 0 1 \rangle \langle 0 1 | _ { i j } . } } & { { } } \end{array}
$$

The terms $H _ { p r o p 1 }$ and $H _ { p r o p 2 } ,$ which represent the correct propagation according to the 1-qubit gates and 2-qubit gates respectively, are defined as:

$$
H _ { p r o p 1 } = \sum _ { t \in T _ { 1 } } H _ { p r o p , t } \qquad H _ { p r o p 2 } = \sum _ { l = 1 } ^ { T _ { 2 } } ( H _ { q u b i t , l L } + H _ { t i m e , l L } )
$$

with

$$
\begin{array} { r c l } { H _ { p r o p , t } } & { = } & { \displaystyle \frac { 1 } { 2 } \left( I \otimes | 1 0 \rangle \langle 1 0 | _ { t , t + 1 } + I \otimes | 1 0 \rangle \langle 1 0 | _ { t - 1 , t } - U _ { t } \otimes | 1 \rangle \langle 0 | _ { t } - U _ { t } ^ { \dagger } \otimes | 0 \rangle \langle 1 | _ { t } \right) } \end{array}
$$

for $t \in T _ { 1 } \cap \left\{ 2 , \dots , T - 1 \right\}$ and

$$
\begin{array} { r c l } { { H _ { p r o p , 1 } } } & { { = } } & { { \displaystyle \frac { 1 } { 2 } \left( I \otimes \left| 1 0 \right. \left. 1 0 \right| _ { 1 , 2 } + I \otimes \left| 0 \right. \left. 0 \right| _ { 1 } - U _ { 1 } \otimes \left| 1 \right. \left. 0 \right| _ { 1 } - U _ { 1 } ^ { \dagger } \otimes \left| 0 \right. \left. 1 \right| _ { 1 } \right. } } \\ { { H _ { p r o p , T } } } & { { = } } & { { \displaystyle \frac { 1 } { 2 } \left( I \otimes \left| 1 \right. \left. 1 \right| _ { T } + I \otimes \left| 1 0 \right. \left. 1 0 \right| _ { T - 1 , T } - U _ { T } \otimes \left| 1 \right. \left. 0 \right| _ { T } - U _ { T } ^ { \dagger } \otimes \left| 0 \right. \left. 1 \right| _ { T } \right) } } \end{array}
$$

and, with $f _ { t }$ and $s _ { t }$ being the first and second qubit of the $C _ { \phi }$ gate at time $t$ ,

$$
\begin{array} { l } { { H _ { q u b i , t } = \displaystyle \frac { 1 } { 2 } \left( - 2 | 0 \rangle \langle 0 | _ { f _ { t } } - 2 | 0 \rangle \langle 0 | _ { s _ { t } } + | 1 \rangle \langle 1 | _ { f _ { t } } + | 1 \rangle \langle 1 | _ { s _ { t } } \right) \otimes ( | 1 \rangle \langle 0 | _ { t } + | 0 \rangle \langle 1 | _ { t } ) } } \\ { { H _ { t i m e , t } = \displaystyle \frac { 1 } { 8 } I \otimes \left( | 1 0 \rangle \langle 1 0 | _ { t , t + 1 } + 6 | 1 0 \rangle \langle 1 0 | _ { t + 1 , t + 2 } + | 1 0 \rangle \langle 1 0 | _ { t + 2 , t + 3 } \right. } } \\ { { \displaystyle \qquad + 2 | 1 \rangle \langle 0 0 | _ { t + 1 , t + 2 } + 2 | 0 0 \rangle \langle 1 1 | _ { t + 1 , t + 2 } } } \\ { { \displaystyle \qquad + | 1 \rangle \langle 0 | _ { t + 1 } + | 0 \rangle \langle 1 | _ { t + 1 } + | 1 \rangle \langle 0 | _ { t + 2 } + | 0 \rangle \langle 1 | _ { t + 2 } } } \\ { { \displaystyle \qquad + | 1 0 \rangle \langle 1 0 | _ { t - 3 , t - 2 } + 6 | 1 0 \rangle \langle 1 0 | _ { t - 2 , t - 1 } + | 1 0 \rangle \langle 1 0 | _ { t - 1 , t } } } \\ { { \displaystyle \qquad + 2 | 1 \rangle \langle 0 0 | _ { t - 2 , t - 1 } + 2 | 0 0 \rangle \langle 1 1 | _ { t - 2 , t - 1 } } } \\ { { \displaystyle \qquad + | 1 \rangle \langle 0 | _ { t - 2 } + | 0 \rangle \langle 1 | _ { t - 2 } + | 1 \rangle \langle 0 | _ { t - 1 } + | 0 \rangle \langle 1 | _ { t - 1 } ) . } } \end{array}
$$

At this point, these last two expressions might look strange. Let us say that later, when we consider their restriction to a smaller space, the reason for this definition should become clear. Note that all the above terms are at most 2-local. We will later choose $J _ { i n } \ll J _ { 2 } \ll J _ { 1 } \ll J _ { c l o c k } \leq \mathrm { p o l y } ( N )$ . As in Section 4, we have to prove the following lemma:

Lemma 3 Assume that the circuit $V _ { x }$ accepts with probability more than $1 - \varepsilon$ on some input $| \xi , 0 \rangle$ . Then $H$ has an eigenvalue smaller than $\varepsilon$ . If the circuit $V _ { x }$ accepts with probability less than $\varepsilon$ on all inputs $| \xi , 0 \rangle$ , then all eigenvalues of $H$ are larger than $\begin{array} { r l r } {  { \frac { 1 } { 2 } - \varepsilon } } \end{array}$ .

Proof: If the circuit $V _ { x }$ accepts with probability more than $1 - \varepsilon$ on some input $| \xi , 0 \rangle$ then the state

$$
| \eta \rangle = \frac { 1 } { \sqrt { T + 1 } } \sum _ { t = 0 } ^ { T } U _ { t } \cdot \cdot \cdot U _ { 1 } | \xi , 0 \rangle \otimes | \widehat { t } \rangle
$$

satisfies $\langle \eta | H | \eta \rangle \leq \varepsilon$ . In order to see this, one can check that

$$
\langle \eta | H _ { c l o c k } | \eta \rangle = \langle \eta | H _ { p r o p 1 } | \eta \rangle = \langle \eta | H _ { p r o p 2 } | \eta \rangle = \langle \eta | H _ { i n } | \eta \rangle = 0
$$

and $\langle \eta | H _ { o u t } | \eta \rangle \le \varepsilon$ . However, verifying that $\langle \eta | H _ { p r o p 2 } | \eta \rangle = 0$ can be quite tedious. Later in the proof, we will mention an easier way to see this.

In the following, we will show that if the circuit $V _ { x }$ accepts with probability less than $\varepsilon$ on all inputs $| \xi , 0 \rangle$ , then all eigenvalues of $H$ are larger than $\frac { 1 } { 2 } - \varepsilon$ . The proof of this is based on four applications of Lemma 1. Schematically, we proceed as follows:

$$
\mathcal { H } \supset S _ { l e g a l } \supset S _ { p r o p 1 } \supset S _ { p r o p } \supset S _ { i n }
$$

where $\boldsymbol { S _ { l e g a l } }$ corresponds to states with legal clock states written in unary, and $\boldsymbol { S _ { p r o p 1 } }$ is spanned by states in the legal clock space whose propagation at time steps corresponding to one-qubit gates (that is, in $T _ { 1 }$ ) is correct. Finally, $ { \boldsymbol { S } } _ { p r o p }$ and $\mathcal { S } _ { i n }$ are defined in almost the same way as in Section 4. These spaces will be described in more detail later.

Norms: Note that all relevant norms, as needed in Lemma 1, are polynomial in $N$ . Indeed, we have $\| H _ { o u t } \| = T + 1$ and $\| H _ { i n } \| \leq N$ as in Section 4, $\begin{array} { r } { \| H _ { p r o p 1 } \| \le \sum _ { t \in T _ { 1 } } \| H _ { p r o p , t } \| \le 2 T } \end{array}$ (each term in $H _ { p r o p 1 }$ has norm at most 2) and $\begin{array} { r } { \| H _ { p r o p 2 } \| \le \sum _ { t = 1 } ^ { \mathcal { T } _ { 2 } } ( \| H _ { q u b i t , l L } \| + \| H _ { t i m e , l L } \| ) \le O ( T _ { 2 } ) \le O ( T ) } \end{array}$ .

1. Restriction to legal clock states in $\boldsymbol { S _ { l e g a l } }$ : Let $\boldsymbol { S _ { l e g a l } }$ be the $( T + 1 ) 2 ^ { N }$ -dimensional space spanned by states with a legal unary representation on the $T$ clock qubits, i.e., by states of the form $\widetilde { | \xi \rangle } \otimes { \widehat { | t \rangle } }$ with $\lvert \widehat { t } \rangle$ as in Eq. (5). In this first stage we apply Lemma 1 with

$$
H _ { 1 } = H _ { o u t } + J _ { i n } H _ { i n } + J _ { 2 } H _ { p r o p 2 } + J _ { 1 } H _ { p r o p 1 } H _ { 2 } = J _ { c l o c k } H _ { c l o c k } .
$$

Notice that $\boldsymbol { S _ { l e g a l } }$ is an eigenspace of $H _ { 2 }$ of eigenvalue 0 and that states orthogonal to $\boldsymbol { S _ { l e g a l } }$ have eigenvalue at least $J _ { \mathit { c l o c k } }$ . Lemma 1 implies that we can choose $J _ { c l o c k } = \mathrm { p o l y } ( \| H _ { 1 } \| ) = \mathrm { p o l y } ( N )$ such that $\lambda ( H )$ can be lower bounded by $\lambda ( H _ { 1 } | _ { S _ { l e g a l } } ) - \frac { 1 } { 8 }$ . Hence, in the remainder of the proof, it is enough to study $H _ { 1 } | _ { \substack { \boldsymbol { S } _ { l e g a l } } }$ inside the space $\boldsymbol { S _ { l e g a l } }$ . This can be written as:

$$
H o u t | s _ { l e g a l } + J _ { i n } H _ { i n } | s _ { l e g a l } + J _ { 2 } H _ { p r o p 2 } | s _ { l e g a l } + J _ { 1 } H _ { p r o p 1 } | s _ { l e g a l }
$$

with

$$
\begin{array} { r l } & { H _ { i n } | | \mathcal { S } _ { t \rho \alpha } = \displaystyle \sum _ { i = m + 1 } ^ { N } | | \mathcal { X } | | \mathcal { S } _ { i } | | \widehat { \boldsymbol { 0 } } | \widehat { \boldsymbol { 0 } } | \widehat { \boldsymbol { 0 } } | } \\ & { \qquad \quad \mathrm { f o r o g e } | \mathcal { S } _ { t \rho \alpha , i } = \displaystyle \frac { 1 } { 2 } ( I \otimes | \widehat { \boldsymbol { t } } | \widehat { \boldsymbol { t } } | + I \otimes | \widehat { \boldsymbol { t } } | \widehat { \boldsymbol { t } } | ) | \widehat { \boldsymbol { t } } \widehat { \boldsymbol { \Lambda } } | = I _ { \ell \ell } \otimes | \widehat { \boldsymbol { t } } \widehat { \boldsymbol { t } } | \widehat { \boldsymbol { t } } | + I _ { \ell } ^ { \dagger } \otimes | \widehat { \boldsymbol { t } } \widehat { \boldsymbol { t } } | \widehat { \boldsymbol { t } } | ) } \\ & { \qquad \quad \mathrm { f o r o j e r } | \mathcal { S } _ { t \rho \alpha , i } = \displaystyle \frac { 1 } { 2 } ( I \otimes | \widehat { \boldsymbol { t } } | \widehat { \boldsymbol { t } } | + I \otimes | \widehat { \boldsymbol { t } } | ) | \widehat { \boldsymbol { t } } \widehat { \boldsymbol { t } } \widehat { \boldsymbol { \Lambda } } | + | | \mathcal { X } _ { i } \otimes | \widehat { \boldsymbol { t } } | \widehat { \boldsymbol { t } } | \widehat { \boldsymbol { t } } | + | \widehat { \boldsymbol { t } } \widehat { \boldsymbol { t } } | \widehat { \boldsymbol { t } } | \widehat { \boldsymbol { t } } | ) } \\ &  \qquad \quad \mathrm { f o r i s t } _ { i } | | \mathcal { S } _ { t \rho \alpha , i } = \displaystyle \frac { 1 } { 8 } I \otimes ( | \widehat { \boldsymbol { t } } | \widehat { \boldsymbol { t } } | + 6 | \widehat { \boldsymbol { t } } | \widehat { \boldsymbol { t } } | + | | \widehat { \boldsymbol { t } } | | \widehat { \boldsymbol { t } } | + | | \widehat { \boldsymbol { t } } | ) ( \mathrm { f i r } | \widehat { \boldsymbol { t } } | ) \otimes ( | \widehat  \boldsymbol { t }  \end{array}
$$

The above was obtained by noting that the projection of a term like, say, $| 1 0 \rangle \langle 1 0 | _ { t , t + 1 }$ on $\boldsymbol { S _ { l e g a l } }$ is exactly $| { \hat { t } } \rangle \langle { \hat { t } } |$ . Similarly, the projection of the term $| 1 \rangle \langle 0 | _ { t + 1 }$ is $\widehat { | t { + } 1 \rangle } \langle \hat { t } |$ .7 By rearranging terms, the above expression can be written as a sum of projectors:

$$
\begin{array} { r l } { \left. t i m e , t | S _ { t \in \rho a } = \frac { 1 } { 8 } I \otimes \left. 2 \left( \left. \widehat { t } \right. + \left. \widehat { t + 1 } \right. \right) \left( \left. \widehat { t } \right. + \left. \widehat { t + 1 } \right. \right) + 2 \left( \left. \widehat { t + 1 } \right. + \left. \widehat { t + 2 } \right. \right) \left( \left. \widehat { t + 1 } \right. + \left. \widehat { t + 2 } \right. \right) } & \\ { + \left( \left. \widehat { t } \right. - \left. \widehat { t + 1 } \right. \right) \left( \left. \widehat { t } \right. - \left. \widehat { t + 1 } \right. \right) + \left( \left. \widehat { t + 1 } \right. - \left. \widehat { t + 2 } \right. \right) \left( \left. \widehat { t + 1 } \right. - \left. \widehat { t + 2 } \right. \right) } & \\ { - 2 \left( \left. \widehat { t } \right. - \left. \widehat { t + 2 } \right. \right) \left( \left. \widehat { t } \right. - \left. \widehat { t + 2 } \right. \right. \right. } & \\ { \left. + 2 \left( \left. \widehat { t - 3 } \right. + \left. \widehat { t - 2 } \right. \right) \left( \left. \widehat { t - 3 } \right. + \left. \widehat { t - 2 } \right. \right. + 2 \left( \left. \widehat { t - 2 } \right. + \left. \widehat { t - 1 } \right. \right) \left( \left. \widehat { t - 2 } \right. + \left. \widehat { t - 1 } \right. \right. \right. \right. } & \\ { \left. \left. + \left( \left. \widehat { t - 3 } \right. - \left. \widehat { t - 2 } \right) \right) \left( \left. \widehat { t - 3 } \right. - \left. \widehat { t - 2 } \right. \right) + \left( \left. \widehat { t - 2 } \right. - \left. \widehat { t - 1 } \right. \right) \left( \left. \widehat { t - 2 } \right. - \left. \widehat { t - 1 } \right. \right. \right. \right. } & \end{array}
$$

Notice that the above expression is symmetric around $\begin{array} { r } { t - \frac { 1 } { 2 } } \end{array}$ (i.e., switching $t - 1$ with $t , t - 2$ with $t + 1 ,$ and $t - 3$ with $t + 2$ does not change the expression). Let us also mention that the fact that we have terms like $\widehat { | t \rangle } - \widehat { | t + 2 \rangle }$ is crucial in our proof. They allow us to compare the state at time $t$ to the state at time $t + 2$ .

2. Restriction to $\boldsymbol { S _ { p r o p 1 } }$ : We now apply Lemma 1 inside $\boldsymbol { S _ { l e g a l } }$ with

$$
H _ { 1 } = \left( H _ { o u t } + J _ { i n } H _ { i n } + J _ { 2 } H _ { p r o p 2 } \right) | _ { \mathcal { S } _ { l e g a l } } \qquad H _ { 2 } = J _ { 1 } H _ { p r o p 1 } | _ { \mathcal { S } _ { l e g a l } } .
$$

Let $\boldsymbol { S _ { p r o p 1 } }$ be the $2 ^ { N } ( T _ { 2 } \mathrm { + } 1 )$ -dimensional space given by all states that represent correct propagation on all one-qubit gates. More precisely, let

$$
\left| \eta _ { l , i } \right. \stackrel { d e f } { = } \frac { 1 } { \sqrt { L } } \sum _ { t = l L } ^ { ( l + 1 ) L - 1 } U _ { t } \cdot \cdot \cdot U _ { 1 } \vert i \rangle \otimes \vert \widehat { t } \rangle ,
$$

where $l \in \{ 0 , \ldots , T _ { 2 } \} , i \in \{ 0 , \ldots , 2 ^ { N } - 1 \}$ and $| i \rangle$ represents the $i$ th vector in the computational basis. Then these states form a basis of $\boldsymbol { S _ { p r o p 1 } }$ . It is easy to see that each $| \eta _ { l , i } \rangle$ is an eigenvector of $H _ { p r o p 1 }$ of eigenvalue 0. Hence, $\boldsymbol { S _ { p r o p 1 } }$ is an eigenspace of eigenvalue 0 of $H _ { p r o p 1 } | _ { S _ { l e g a l } }$ . Furthermore, $H _ { p r o p 1 } | _ { S _ { l e g a l } }$ decomposes into $T _ { 2 } + 1$ invariant blocks, with the $l$ th block spanned by states of the form $U _ { t } \cdot \cdot \cdot U _ { 1 } | i \rangle \otimes | \widehat { t } \rangle$ for $t = l L , \ldots , ( l { + } 1 ) L { - } 1$ . Inside such a block $H _ { p r o p 1 } | _ { S _ { l e g a l } }$ corresponds exactly to $H _ { p r o p }$ of Section 4, Eqs. (1,2). By Claim 2, its non-zero eigenvalues are at least $c / L ^ { 2 } \geq c / T ^ { 2 }$ for some constant $c > 0$ and hence the smallest non-zero eigenvalue of $H _ { p r o p 1 } | _ { S _ { l e g a l } }$ is also at least $c / T ^ { 2 }$ . Therefore, all eigenvectors of $H _ { 2 }$ orthogonal to $\boldsymbol { S _ { p r o p 1 } }$ have eigenvalue at least $J = J _ { 1 } c / T ^ { 2 }$ and Lemma 1 implies that for $J _ { 1 } \ge \mathrm { p o l y } ( N ) , \lambda ( H _ { 1 } + H _ { 2 } )$ can be lower bounded by $\lambda ( H _ { 1 } | _ { S _ { p r o p 1 } } ) - \frac { 1 } { 8 }$ . Hence, in the remainder of the proof, it is enough to study

$$
H _ { o u t } | _ { S _ { p r o p 1 } } + J _ { i n } H _ { i n } | _ { S _ { p r o p 1 } } + J _ { 2 } H _ { p r o p 2 } | _ { S _ { p r o p 1 } } .
$$

Let us find $H _ { p r o p 2 } | _ { S _ { p r o p 1 } }$ . Let $t = l L$ be the time at which the $l$ th $C _ { \phi }$ gate is applied and consider the projection of a state $| \eta _ { l , i } \rangle$ onto the space spanned by the computation qubits and $\widehat { | t \rangle , | t + 1 \rangle , | t + 2 \rangle }$ . Since at time $t + 1$ (resp., $t + 2 )$ ) a $Z$ gate is applied to qubit $f _ { t }$ (resp., $s _ { t } \big .$ ), this projection is a linear combination of the following four states:

$$
\begin{array} { r l } & { \left| 0 0 \right. _ { f _ { t } , s _ { t } } \left| \xi _ { 0 0 } \right. \otimes \left( \left| \widehat { t } \right. + \left| \widehat { t + 1 } \right. + \left| \widehat { t + 2 } \right. \right) } \\ & { \left| 0 1 \right. _ { f _ { t } , s _ { t } } \left| \xi _ { 0 1 } \right. \otimes \left( \left| \widehat { t } \right. + \left| \widehat { t + 1 } \right. - \left| \widehat { t + 2 } \right. \right) } \\ & { \left| 1 0 \right. _ { f _ { t } , s _ { t } } \left| \xi _ { 1 0 } \right. \otimes \left( \left| \widehat { t } \right. - \left| \widehat { t + 1 } \right. - \left| \widehat { t + 2 } \right. \right) } \\ & { \left| 1 1 \right. _ { f _ { t } , s _ { t } } \left| \xi _ { 1 1 } \right. \otimes \left( \left| \widehat { t } \right. - \left| \widehat { t + 1 } \right. + \left| \widehat { t + 2 } \right. \right) , } \end{array}
$$

where $| \xi _ { b _ { 1 } b _ { 2 } } \rangle$ is an arbitrary state on the remaining $N - 2$ computation qubits. This implies that the restriction to $\boldsymbol { S _ { p r o p 1 } }$ of the projector $\mathrm { o n } ,$ say, $\widehat { | t \rangle } + \widehat { | t + 1 \rangle }$ from Eq. (6) is essentially the same as the restriction to $\boldsymbol { S _ { p r o p 1 } }$ of the projector on $| 0 \rangle _ { f _ { t } } | \widehat { t } \rangle$ . More precisely, for all $l _ { 1 } , l _ { 2 } , i _ { 1 } , i _ { 2 }$ we have

$$
\frac { 1 } { 4 } \langle \eta _ { l _ { 1 } , i _ { 1 } } | \Big ( I \otimes \big ( | { \widehat t } \rangle + | \widehat { t + 1 } \rangle \big ) \big ( \langle { \widehat t } | + \widehat { \langle t + 1 | } \big ) \Big ) | \eta _ { l _ { 2 } , i _ { 2 } } \rangle = \langle \eta _ { l _ { 1 } , i _ { 1 } } | \left( | 0 \rangle \langle 0 | _ { f _ { t } } \otimes | { \widehat t } \rangle \langle { \widehat t } | \right) | \eta _ { l _ { 2 } , i _ { 2 } } \rangle .
$$

Similarly, the term involving $\widehat { | t \rangle } - \widehat { | t + 2 \rangle }$ satisfies

$$
{ } _ { 1 , i _ { 1 } } | \Big ( I \otimes \big ( | \widehat { t } \rangle - | \widehat { t + 2 } \rangle \big ) \big ( \langle \widehat { t } | - \widehat { \langle t + 2 | } \rangle \big ) \Big ) | \eta _ { l _ { 2 } , i _ { 2 } } \rangle = \langle \eta _ { l _ { 1 } , i _ { 1 } } | \Big ( \big ( | 0 1 \rangle \langle 0 1 | _ { f _ { t } , s _ { t } } + | 1 0 \rangle \langle 1 0 | _ { f _ { t } , s _ { t } } \big ) \otimes | \widehat { t } \rangle \langle \widehat { t } | \otimes \widehat { t } _ { l _ { 2 } , s _ { t } } | \Big ) | \xi \rangle ,
$$

Observe that the right-hand side involves two computation qubits and the clock register. Being able to obtain such a term from two-local terms is a crucial ingredient in this proof.

Following a similar calculation, we see that from the terms involving $| \widehat { t \mathrm { - 1 } } \rangle , | \widehat { t \mathrm { - 2 } } \rangle , | \widehat { t \mathrm { - 3 } } \rangle$ we obtain projectors involving $\widehat { | t { - } 1 \rangle }$ . To summarize, instead of considering $H _ { t i m e , t } | _ { S _ { p r o p 1 } }$ we can equivalently consider the restriction to $\boldsymbol { S _ { p r o p 1 } }$ o f

$$
\begin{array} { r l } & { \frac { 1 } { 2 } \left( 2 | 0 \rangle \langle 0 | _ { f _ { t } } + 2 | 0 \rangle \langle 0 | _ { s _ { t } } + | 1 \rangle \langle 1 | _ { f _ { t } } + | 1 \rangle \langle 1 | _ { s _ { t } } - 2 | 0 1 \rangle \langle 0 1 | _ { f _ { t } , s _ { t } } - 2 | 1 0 \rangle \langle 1 0 | _ { f _ { t } , s _ { t } } \right) } \\ & { \qquad \otimes \left( | \widehat { t - 1 } \rangle \langle \widehat { t - 1 } | + | \widehat { t } \rangle \langle \widehat { t } | \right) . } \end{array}
$$

We now add the terms in $H _ { q u b i t , t }$ . A short calculation shows that $\left( H _ { t i m e , t } + H _ { q u b i t , t } \right) | _ { S _ { p r o p 1 } }$ is the same as the restriction to $\boldsymbol { S _ { p r o p 1 } }$ of

$$
\begin{array} { r } { \begin{array} { r c l } { | 0 0   0 0 | _ { f _ { t } , s _ { t } } } & { \otimes } & { \displaystyle 2 ( | \widehat { t - 1 }  - | \widehat { t } \rangle ) ( \langle \widehat { t - 1 } | - \langle \widehat { t } | ) + } \\ { \displaystyle | 0 1 \rangle  0 1 | _ { f _ { t } , s _ { t } } } & { \otimes } & { \displaystyle \frac { 1 } { 2 } ( | \widehat { t - 1 } \rangle - | \widehat { t } \rangle ) ( \langle \widehat { t - 1 } | - \langle \widehat { t } | ) + } \\ { \displaystyle | 1 0 \rangle  1 0 | _ { f _ { t } , s _ { t } } } & { \otimes } & { \displaystyle \frac { 1 } { 2 } ( | \widehat { t - 1 } \rangle - | \widehat { t } \rangle ) ( \langle \widehat { t - 1 } | - \langle \widehat { t } | ) + } \\ { \displaystyle | 1 1 \rangle  1 1 | _ { f _ { t } , s _ { t } } } & { \otimes } & { \displaystyle ( | \widehat { t - 1 } \rangle + | \widehat { t } \rangle ) ( \langle \widehat { t - 1 } | + \langle \widehat { t } | ) . } \end{array} } \end{array}
$$

At this point, let us mention how one can show that for the state $| \eta \rangle$ described in the beginning of this proof, $\langle \eta | H _ { p r o p 2 } | \eta \rangle = 0$ . First, observe that $| \eta \rangle \in \ S _ { p r o p 1 }$ (its propagation is correct at all time steps). Next, since $| \eta \rangle$ has a $C _ { \phi }$ propagation at time $t ,$ the above Hamiltonian shows that $\langle \eta | H _ { p r o p 2 } | \eta \rangle = 0 $ .

Let us return now to the main proof. Recall that we wish to show a lower bound on the lowest eigenvalue of

$$
H _ { o u t } | _ { S _ { p r o p 1 } } + J _ { i n } H _ { i n } | _ { S _ { p r o p 1 } } + J _ { 2 } H _ { p r o p 2 } | _ { S _ { p r o p 1 } } .
$$

In the following, we show a lower bound on the lowest eigenvalue of the Hamiltonian

$$
H _ { o u t } | _ { S _ { p r o p 1 } } + J _ { i n } H _ { i n } | _ { S _ { p r o p 1 } } + J _ { 2 } H ^ { \prime }
$$

on $\boldsymbol { S _ { p r o p 1 } }$ where $H ^ { \prime }$ satisfies that $H ^ { \prime } \leq H _ { p r o p 2 } | _ { S _ { p r o p 1 } } ,$ i.e., $H _ { p r o p 2 } | _ { S _ { p r o p 1 } } - H ^ { \prime }$ is positive semidefinite. Hence, any lower bound on the lowest eigenvalue of the Hamiltonian in (9) implies the same lower bound on the lowest eigenvalue of the Hamiltonian in (8). We define $H ^ { \prime }$ as the sum over $t \in \{ L , 2 L , \ldots , T _ { 2 } L \}$ of the restriction to $\boldsymbol { S _ { p r o p 1 } }$ of

$$
\begin{array} { r } { \begin{array} { r l } { | 0 0 \rangle \langle 0 0 | _ { f _ { t } , s _ { t } } } & { \otimes } & { \frac { 1 } { 2 } \left( | \widehat { t - 1 } \rangle - | \widehat { t } \rangle \right) \left( \langle \widehat { t - 1 } | - \langle \widehat { t } | \right) + } \\ { | 0 1 \rangle \langle 0 1 | _ { f _ { t } , s _ { t } } } & { \otimes } & { \frac { 1 } { 2 } \left( | \widehat { t - 1 } \rangle - | \widehat { t } \rangle \right) \left( \langle \widehat { t - 1 } | - \langle \widehat { t } | \right) + } \\ { | 1 0 \rangle \langle 1 0 | _ { f _ { t } , s _ { t } } } & { \otimes } & { \frac { 1 } { 2 } \left( | \widehat { t - 1 } \rangle - | \widehat { t } \rangle \right) \left( \langle \widehat { t - 1 } | - \langle \widehat { t } | \right) + } \\ { | 1 1 \rangle \langle 1 1 | _ { f _ { t } , s _ { t } } } & { \otimes } & { \frac { 1 } { 2 } \left( | \widehat { t - 1 } \rangle + | \widehat { t } \rangle \right) \left( \langle \widehat { t - 1 } | + \langle \widehat { t } | \right) . } \end{array} } \end{array}
$$

Equivalently, $H ^ { \prime }$ is the sum over $t \in \{ L , 2 L , \ldots , T _ { 2 } L \}$ of

$$
\frac { 1 } { 2 } \left( I \otimes | \widehat { t } \rangle \langle \widehat { t } | + I \otimes | \widehat { t - 1 } \rangle \langle \widehat { t - 1 } | - C _ { \phi } \otimes | \widehat { t } \rangle \langle \widehat { t - 1 } | - C _ { \phi } ^ { \dagger } \otimes | \widehat { t - 1 } \rangle \langle \widehat { t } | \right) \Big | _ { S _ { p r o p 1 } } ,
$$

which resembles Eq. (2). Note that this term enforces correct propagation at time step $t = l L$ . We claim that

$$
H ^ { \prime } = \frac { 1 } { 2 L } \sum _ { i = 0 } ^ { 2 ^ { N } - 1 } \sum _ { l = 1 } ^ { T _ { 2 } } \left( \left| \eta _ { l - 1 , i } \right. - \left| \eta _ { l , i } \right. \right) \left( \left. \eta _ { l - 1 , i } \right| - \left. \eta _ { l , i } \right| \right) .
$$

The intuitive reason for this is the following. For any i, $| \eta _ { l - 1 , i } \rangle + | \eta _ { l , i } \rangle$ can be seen as a correct propagation at time $t = l L$ . In other words, consider the projection of $| \eta _ { l , i } \rangle$ on clock $\lvert \widehat { t } \rangle$ and the projection of $| \eta _ { l - 1 , i } \rangle$ on clock $\widehat { | t { - } 1 \rangle }$ . Then the first state is exactly the second state after applying the $l$ th $C _ { \phi }$ gate. This means that inside $S _ { p r o p 1 } ,$ , checking correct propagation from time $t - 1$ to time $t$ is equivalent to checking correct propagation from $| \eta _ { l - 1 , i } \rangle$ to $| \eta _ { l , i } \rangle$ .

More precisely, fix some $l$ and $t = l L$ . Then, using Eq. (7), we get that for all $l _ { 1 } , l _ { 2 } , i _ { 1 } , i _ { 2 }$ such that either ${ \mathrm { \Delta } l } _ { 1 } \neq { \mathrm { \Delta } l }$ , ${ \mathit { l } } _ { 2 } \neq { \mathit { l } } ,$ or $i _ { 1 } \neq i _ { 2 } ,$

$$
\langle \eta _ { l _ { 1 } , i _ { 1 } } \vert \left( I \otimes \vert \widehat { t } \rangle \langle \widehat { t } \vert \right) \vert \eta _ { l _ { 2 } , i _ { 2 } } \rangle = 0 .
$$

Otherwise, $l _ { 1 } = l _ { 2 } = l$ and $i _ { 1 } = i _ { 2 } = i$ for some $i$ and we have

$$
\langle \eta _ { l , i } | \left( I \otimes | \widehat { t } \rangle \langle \widehat { t } | \right) | \eta _ { l , i } \rangle = \frac { 1 } { L } .
$$

Hence we obtain

$$
I \otimes | \widehat { t } \rangle \langle \widehat { t } | | _ { S _ { p r o p 1 } } = \frac { 1 } { L } \sum _ { i = 0 } ^ { 2 ^ { N } - 1 } | \eta _ { l , i } \rangle \langle \eta _ { l , i } |
$$

and similarly,

$$
I \otimes | \widehat { t - 1 } \rangle \langle \widehat { t - 1 } | | s _ { p r o p 1 } = \frac { 1 } { L } \sum _ { i = 0 } ^ { 2 ^ { N } - 1 } | \eta _ { l - 1 , i } \rangle \langle \eta _ { l - 1 , i } | .
$$

For the off-diagonal terms we see that

$$
\langle \eta _ { l _ { 1 } , i _ { 1 } } \vert \left( C _ { \phi } \otimes \vert \widehat { t } \rangle \langle \widehat { t - 1 } \vert \right) \vert \eta _ { l _ { 2 } , i _ { 2 } } \rangle = 0
$$

if ${ \mathrm { \Delta } l } _ { 1 } \neq { \mathrm { \Delta } l }$ or $l _ { 2 } \neq l - 1$ . If ${ \mathrm { \Delta } l } _ { 1 } = l$ and $l _ { 2 } = l - 1$ then using ${ C } _ { \phi } = { U } _ { l L } ,$ we get

$$
\langle \eta _ { l , i _ { 1 } } | \left( C _ { \phi } \otimes | { \widehat { t } } \rangle \langle { \widehat { t - 1 } } | \right) | \eta _ { l - 1 , i _ { 2 } } \rangle = { \frac { 1 } { L } } \langle i _ { 1 } | \left( U _ { l L } \cdot \cdot \cdot U _ { 1 } \right) ^ { \dagger } C _ { \phi } U _ { l L - 1 } \cdot \cdot \cdot U _ { 1 } | i _ { 2 } \rangle = { \frac { 1 } { L } } \langle i _ { 1 } | i _ { 2 } \rangle
$$

which is 0 if $i _ { 1 } ~ \neq ~ i _ { 2 }$ and $\textstyle { \frac { 1 } { L } }$ otherwise. Hence $\begin{array} { r } { C _ { \phi } \otimes | \widehat { t } \rangle \langle \widehat { t } - 1 | | s _ { p r o p 1 } = \frac { 1 } { L } \sum _ { i = 0 } ^ { 2 ^ { N } - 1 } | \eta _ { l , i } \rangle \langle \eta _ { l - 1 , i } | } \end{array}$ and similarly for its Hermitian adjoint. This establishes Eq. (10).

3. Restriction to $ { \boldsymbol { S } } _ { p r o p }$ : Let $ { \boldsymbol { S } } _ { p r o p }$ be the $2 ^ { N }$ -dimensional space whose basis is given by the states

$$
| \eta _ { i } \rangle = \frac { 1 } { \sqrt { T + 1 } } \sum _ { t = 0 } ^ { T } U _ { t } \cdot \cdot \cdot U _ { 1 } | i \rangle \otimes | \widehat { t } \rangle = \frac { 1 } { \sqrt { T _ { 2 } + 1 } } \sum _ { l = 0 } ^ { T _ { 2 } } | \eta _ { l , i } \rangle ,
$$

for $i \in \{ 0 , \ldots , 2 ^ { N } - 1 \}$ . Eq. (10) shows that $ { \boldsymbol { S } } _ { p r o p }$ is an eigenspace of $H ^ { \prime }$ of eigenvalue 0. Moreover, $H ^ { \prime }$ is block-diagonal with $2 ^ { N }$ blocks of size $T _ { 2 } + 1$ . Each block is a matrix as in Eq. (4), multiplied

by $1 / L$ . As in Claim 2 we see that the smallest non-zero eigenvalue of this Hamiltonian is $c / L T _ { 2 } ^ { 2 } \geq$ $c / T ^ { 2 }$ for some constant $c$ . Now we can apply Lemma 1. This time, we apply it inside $\boldsymbol { S _ { p r o p 1 } }$ with

$$
H _ { 1 } = \left( H _ { o u t } + J _ { i n } H _ { i n } \right) | _ { S _ { p r o p 1 } } H _ { 2 } = J _ { 2 } H ^ { \prime } .
$$

Eigenvectors of $H _ { 2 }$ orthogonal to $ { \boldsymbol { S } } _ { p r o p }$ have eigenvalue at least $J = J _ { 2 } c / T ^ { 2 }$ . As before, we can choose $J _ { 2 } = \mathrm { p o l y } ( N )$ such that $\lambda ( H _ { 1 } + H _ { 2 } )$ is lower bounded by $\lambda ( H _ { 1 } | _ { S _ { p r o p } } ) - \frac { 1 } { 8 }$ . Hence, in the remainder we consider

$$
H _ { o u t } | _ { S _ { p r o p } } + J _ { i n } H _ { i n } | _ { S _ { p r o p } } .
$$

4. Restriction to $\mathcal { S } _ { i n }$ : The rest of the proof proceeds in the same way as in Section 4. Indeed, the subspace $ { \boldsymbol { S } } _ { p r o p }$ is isomorphic to the one in Section 4 and both $H _ { o u t } | _ { S _ { p r o p } }$ and $H _ { i n } | _ { S _ { p r o p } }$ are the same Hamiltonians. So by another application of Lemma 1 we get that the lowest eigenvalue of $H _ { o u t } | _ { S _ { p r o p } } + J _ { i n } H _ { i n } | _ { S _ { p r o p } }$ is lower bounded by $\begin{array} { r } { \lambda ( H _ { o u t } | _ { S _ { i n } } ) - \frac { 1 } { 8 } } \end{array}$ . As in Section 4, we have that $\lambda ( H _ { o u t } | _ { S _ { i n } } ) > 1 - \varepsilon$ if the circuit accepts with probability less than $\varepsilon$ . Hence $\lambda ( H ) .$ , the lowest Seigenvalue of the original Hamiltonian $H$ , is larger than $\textstyle 1 - \varepsilon - { \frac { 4 } { 8 } } = { \frac { 1 } { 2 } } - \varepsilon$ .

# 6 Perturbation Theory Proof

In this section we give an alternative proof of our main theorem. In Section 6.1, we develop our perturbation theory technique. Since this technique might constitute a useful tool in other Hamiltonian constructions, we keep the presentation as general as possible. Then, in Section 6.2, we present a specific application of our technique, the three-qubit gadget. Finally, in Section 6.3, we use this gadget to complete the proof of the main theorem.

# 6.1 Perturbation theory

The goal in perturbation theory is to analyze the spectrum of the sum of two Hamiltonians ${ \widetilde { H } } =$ $H + V$ in the case that $V$ has a small norm compared to the spectral gap of $H$ . One setting was described in the projection lemma. Specifically, assume $H$ has a zero eigenvalue with the associated eigenspace ${ \mathcal { S } } ,$ , whereas all other eigenvalues are greater than $\Delta \gg \| V \|$ . The projection lemma shows that in this case, the lowest eigenvalue of $\widetilde { H }$ is close to that of $V | _ { s }$ . In this section we find a better approximation to Spec $\widetilde { H }$ by considering certain correction terms that involve higher powers of $V$ . It turns out that these higher order correction terms include interesting interactions, which will allow us to create an effective 3-local Hamiltonian from 2-local terms. We remark that the projection lemma (for the entire lower part of the spectrum) can be obtained by following the development done in this section up to the first order.

Before giving a more detailed description of the technique, we need to introduce a certain amount of notation. For two Hermitian operators $H$ and $V$ , let ${ \widetilde { H } } = H + V$ . We refer to $H$ as the unperturbed Hamiltonian and to $V$ as the perturbation Hamiltonian. Let $\lambda _ { j } , | \psi _ { j } \rangle$ be the eigenvalues and eigenvectors of $H$ , whereas the eigenvalues and eigenvectors of $\widetilde { H }$ are denoted by $\widetilde { \lambda } _ { j } , | \widetilde { \psi _ { j } } \rangle$ . In case of multiplicities, some eigenvalues might appear more than once. We order the eigenvalues

in a non-decreasing order

$$
\lambda _ { 1 } \le \lambda _ { 2 } \le \cdots \le \lambda _ { \dim } \varkappa , \qquad \widetilde { \lambda } _ { 1 } \le \widetilde { \lambda } _ { 2 } \le \cdots \le \widetilde { \lambda } _ { \dim } \varkappa .
$$

In general, everything related to the perturbed Hamiltonian is marked with a tilde.

An important component in our proof is the resolvent of $\widetilde { H }$ , defined as

$$
\widetilde { G } ( z ) = \bigl ( z I - \widetilde { H } \bigr ) ^ { - 1 } = \sum _ { j } \bigl ( z - \widetilde { \lambda } _ { j } \bigr ) ^ { - 1 } \bigl | \widetilde { \psi } _ { j } \bigr \rangle \bigl \langle \widetilde { \psi } _ { j } \bigr | .
$$

It is a meromorphic8 operator-valued function of the complex variable $z$ with poles at $z = \widetilde { \lambda } _ { j }$ . In fact, for our purposes, it is sufficient to consider real $z$ .9 Its usefulness comes from the fact that poles can be preserved under projections (while eigenvalues are usually lost). Similarly, we define the resolvent of $H$ as $G ( z ) = ( z I - H ) ^ { - 1 }$ . 10

Let $\lambda _ { * } \in \mathbb { R }$ be some cutoff on the spectrum of $H$ .

Definition 6 Let $\mathcal { H } = \mathcal { L } _ { + } \oplus \mathcal { L } _ { - }$ , where $\mathcal { L } _ { + }$ is the space spanned by eigenvectors of $H$ with eigenvalues $\lambda \ge \lambda _ { * }$ and $\mathcal { L } _ { - }$ is spanned by eigenvectors of $H$ of eigenvalue $\lambda < \lambda _ { * }$ . Let $\Pi _ { \pm }$ be the corresponding projection onto $\mathcal { L } _ { \pm }$ . For an operator $X$ on $\mathcal { H }$ define the operator $X _ { + + } = X | _ { \mathcal { L } _ { + } } = \Pi _ { + } X \Pi _ { + }$ on $\mathcal { L } _ { + }$ and similarly $X _ { -- } = X | \ l _ { \mathcal { L } _ { - } } \quad$ . We also define $X _ { + - } = \Pi _ { + } X \Pi _ { - }$ as an operator from $\mathcal { L } _ { - }$ to $\mathcal { L } _ { + } ,$ , and similarly $X _ { - + }$ .

With these definitions, in a representation of $\mathcal { H } = \mathcal { L } _ { + } \oplus \mathcal { L } _ { - }$ both $H$ and $G$ are block diagonal and we will omit one index for their blocks, i.e., $H _ { + } \stackrel { d e f } { = } H _ { + + } , G _ { + } \stackrel { d e f } { = } G _ { + + }$ and so on. Note that $G _ { \pm } ^ { - 1 } = z I _ { \pm } - H _ { \pm }$ . To summarize, we have:

$$
\begin{array} { l l } { { { \widetilde { \cal H } } = \left( \begin{array} { c c } { { { \widetilde { \cal H } } _ { + + } } } & { { { \widetilde { \cal H } } _ { + - } } } \\ { { { \widetilde { \cal H } } _ { - + } } } & { { { \widetilde { \cal H } } _ { -- } } } \end{array} \right) } } & { { { \cal V } = \left( \begin{array} { c c } { { V _ { + + } } } & { { V _ { + - } } } \\ { { V _ { - + } } } & { { V _ { -- } } } \end{array} \right) } } & { { { \cal H } = \left( \begin{array} { c c } { { { \cal H } _ { + } } } & { { 0 } } \\ { { 0 } } & { { { \cal H } _ { - } } } \end{array} \right) } } \\ { { { \widetilde { \cal G } } = \left( \begin{array} { c c } { { { \widetilde { \cal G } } _ { + + } } } & { { { \widetilde { \cal G } } _ { + - } } } \\ { { { \widetilde { \cal G } } _ { - + } } } & { { { \widetilde { \cal G } } _ { -- } } } \end{array} \right) } } & { { { \cal G } = \left( \begin{array} { c c } { { { \cal G } _ { + } } } & { { 0 } } \\ { { 0 } } & { { { \cal G } _ { - } } } \end{array} \right) } } \end{array}
$$

We similarly write $\mathcal { H } = \widetilde { \mathcal { L } } _ { + } \oplus \widetilde { \mathcal { L } } _ { - }$ according to the spectrum of $\widetilde { H }$ and the cutoff $\lambda _ { * }$ . Finally, we define

$$
\Sigma _ { - } ( z ) = z I _ { - } - \widetilde { G } _ { -- } ^ { - 1 } ( z ) .
$$

This operator-valued function is called self-energy.11

With these notations in place, we can now give an overview of what follows. Our goal is to approximate the spectrum of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ . We will do this by showing that in some sense, the spectrum of $\Sigma _ { - } ( z )$ gives such an approximation. To see why this arises, notice that by definition of $\Sigma _ { - } ( z ) ,$ , we have $\tilde { \tilde { G } } _ { -- } ( z ) = \big ( z I _ { - } - \hat { \Sigma } _ { - } ( z ) \big ) ^ { - 1 }$ . In some sense, this equation is the analogue of Eq. (11) where $\Sigma _ { - } ( z )$ plays the role of a Hamiltonian for the projected resolvent $\widetilde { G } _ { -- } ( z )$ . However, $\Sigma _ { - } ( z )$ is in general $z$ -dependent and not a fixed Hamiltonian. Nonetheless, for certain choices of $H$ and $V _ { \cdot }$ , $\Sigma _ { - } ( z )$ is nearly constant in a certain range of $z$ so we can choose an effective Hamiltonian $H _ { \mathrm { e f f } }$ that approximates $\Sigma _ { - } ( z )$ in this range. Our main theorem relates the spectrum of $H _ { \mathrm { e f f } }$ to that of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ .

Theorem 3 Assume $H$ has a spectral gap $\Delta$ around the cutoff $\lambda _ { * } ,$ i.e., all its eigenvalues are in $( - \infty , \lambda _ { - } ] \cup$ $[ \lambda _ { + } , + \infty )$ , where $\lambda _ { + } = \lambda _ { * } + \Delta / 2$ and $\lambda _ { - } = \lambda _ { * } - \Delta / 2$ . Assume moreover that $\| V \| < \Delta / 2$ . Let $\varepsilon > 0$ be arbitrary. Assume there exists an operator $H _ { \mathrm { e f f } }$ such that S $\mathrm { p e c } H _ { \mathrm { e f f } } \subseteq [ c , d ]$ for some $c < d < \lambda _ { * } - \varepsilon$ and moreover, the inequality

$$
\| \Sigma _ { - } ( z ) - H _ { \mathrm { e f f } } \| \le \varepsilon
$$

holds for all $z \in [ c - \varepsilon , d + \varepsilon ]$ . Then each eigenvalue $\widetilde { \lambda } _ { j }$ of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ is $\varepsilon$ -close to the jth eigenvalue of $H _ { \mathrm { e f f } }$

The usefulness of the theorem comes from the fact that $\Sigma _ { - } ( z )$ has a natural series expansion, which can be truncated to obtain $H _ { \mathrm { e f f } }$ . This series may give rise to interesting terms; for example, in our application, 2-local terms in $H$ and $V$ lead to 3-local terms in $H _ { \mathrm { e f f } }$ . To obtain this expansion, we start by expressing $\widetilde { G }$ in terms of $G$ as

$$
\widetilde { G } = \left( G ^ { - 1 } - V \right) ^ { - 1 } = \left( \begin{array} { c c } { { G _ { + } ^ { - 1 } - V _ { + + } } } & { { - V _ { + - } } } \\ { { - V _ { - + } } } & { { G _ { - } ^ { - 1 } - V _ { -- } } } \end{array} \right) ^ { - 1 } .
$$

Then, using the block matrix identity

$$
{ \left( \begin{array} { l l } { A } & { B } \\ { C } & { D } \end{array} \right) } ^ { - 1 } = \left( { \begin{array} { c c } { \left( A - B D ^ { - 1 } C \right) ^ { - 1 } } & { - A ^ { - 1 } B { \left( D - C A ^ { - 1 } B \right) } ^ { - 1 } } \\ { - D ^ { - 1 } C { \left( A - B D ^ { - 1 } C \right) } ^ { - 1 } } & { \left( D - C A ^ { - 1 } B \right) ^ { - 1 } } \end{array} } \right)
$$

we conclude that

$$
\widetilde { G } _ { -- } = \Bigl ( G _ { - } ^ { - 1 } - V _ { -- } - V _ { - + } \bigl ( G _ { + } ^ { - 1 } - V _ { + + } \bigl ) ^ { - 1 } V _ { + - } \Bigl ) ^ { - 1 } .
$$

Finally, we can represent $\Sigma _ { - } ( z )$ using the series expansion $( I - X ) ^ { - 1 } = I + X + X ^ { 2 } + \cdot \cdot \cdot$

$$
\begin{array} { l } { { ( z ) = H _ { - } + V _ { -- } + V _ { - + } \bigl ( G _ { + } ^ { - 1 } - V _ { + + } \bigr ) ^ { - 1 } V _ { + - } } } \\ { { \mathrm { ~ } = H _ { - } + V _ { -- } + V _ { - + } G _ { + } \bigl ( I _ { + } - V _ { + + } G _ { + } \bigr ) ^ { - 1 } V _ { + - } } } \\ { { \mathrm { ~ } = H _ { - } + V _ { -- } + V _ { - + } G _ { + } V _ { + - } + V _ { - + } G _ { + } V _ { + + } G _ { + } V _ { + - } + V _ { - + } G _ { + } V _ { + + } G _ { + } V _ { + + } G _ { + } V _ { + - } . } } \end{array}
$$

Proof of Theorem 3: We start with an overview of the proof. We first notice that, by definition, the eigenvalues of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ appear as poles in $\widetilde { G }$ . In Lemma 5, we show that these poles also appear as poles of $\widetilde { G } _ { -- }$ . As mentioned before, this is the reason we work with resolvents. In Lemmas 6 and 7 we relate these poles to the eigenvalues of $\Sigma _ { - }$ by showing that $z$ is a pole of $\widetilde { G } _ { -- }$ if and only if it is an eigenvalue of $\Sigma _ { - } ( z )$ . In other words, these are values of $z$ for which $\Sigma _ { - } ( z )$ has $z$ as an eigenvalue. Finally, we complete the proof of the theorem by using the assumption that $\Sigma _ { - } ( z )$ is close to $H _ { \mathrm { e f f } } .$ , so any eigenvalue of $\Sigma _ { - } ( z )$ must be close to an eigenvalue of $H _ { \mathrm { e f f } }$ . This situation is illustrated in Figure 3.

![](images/e4157531b93a3718463c4d748e12f42be4e262f2f533073e62abd736359ec813.jpg)  
Figure 3: The spectrum of $\Sigma _ { - } ( z )$ as a function of $z$ is indicated with solid curves. The boxes correspond to the spectrum of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ ; they are those eigenvalues of $\Sigma _ { - } ( z )$ that lie on the dashed line $z = e . v$ . The dots indicate the spectrum of $H _ { \mathrm { e f f } }$ , which approximates the spectrum of $\displaystyle \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } }$ .

We start with a simple lemma that says that if two Hamiltonians $H _ { 1 } , H _ { 2 }$ are close, their spectra must also be close. It is a special case of Weyl’s inequalities (see, e.g., Section III.2 in [Bha97]).

Lemma 4 Let $H _ { 1 } , H _ { 2 }$ be two Hamiltonians with eigenvalues $\mu _ { 1 } \leq \mu _ { 2 } \leq . .$ . and $\sigma _ { 1 } \leq \sigma _ { 2 } \leq . .$ . . Then, for all $j , | \mu _ { j } - \sigma _ { j } | \leq \| H _ { 1 } - H _ { 2 } \|$ .

Proof: We will use a fact from the theory of Hermitian forms: if $X \leq Y$ (i.e., if $Y - X$ is positive semidefinite), then the operator $Y$ has at least as many positive and nonnegative eigenvalues as $X$ . Let $\varepsilon = \| H _ { 1 } - H _ { 2 } \| ;$ then

$$
( \mu _ { j } - \varepsilon ) I - H _ { 2 } \leq \mu _ { j } I - H _ { 1 } \leq ( \mu _ { j } + \varepsilon ) I - H _ { 2 } .
$$

The operator $\mu _ { \mathcal { j } } I - H _ { 1 }$ has at most $j - 1$ positive and at least $j$ nonnegative eigenvalues. Hence $( \mu _ { j } - \varepsilon ) I - H _ { 2 }$ has at most $j - 1$ positive eigenvalues, and $( \mu _ { j } + \varepsilon ) I - H _ { 2 }$ has at least $j$ nonnegative eigenvalues. It follows that $\sigma _ { j } \in [ \mu _ { j } - \varepsilon , \mu _ { j } + \varepsilon ]$ .

The next lemma asserts that the poles of $\widetilde { G } _ { -- }$ in the range $( - \infty , \lambda _ { * } )$ are in one-to-one correspondence with the eigenvalues of $\tilde { H } | _ { \tilde { \mathcal { L } } _ { - } }$ . Hence we can recover the eigenvalues of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ from the poles of $\widetilde { G } _ { -- }$ .

Lemma 5 Let $\tilde { \lambda }$ be in $( - \infty , \lambda _ { * } )$ and let $m \geq 0$ be its multiplicity as an eigenvalue of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ . Then around $\tilde { \lambda } , \tilde { G } _ { -- }$ is of the form $( z - \tilde { \lambda } ) ^ { - 1 } A + O ( 1 )$ where $A$ is a rank m operator.

Proof: We first show that $\tilde { \mathcal { L } } _ { - } \cap \mathcal { L } _ { + } = \{ 0 \}$ . Suppose the contrary, i.e., there is a nonzero vector $| \xi \rangle \in \widetilde { \mathcal { L } } _ { - } \cap \mathcal { L } _ { + }$ . W.l.o.g. $\langle \xi | \xi \rangle ~ = ~ 1$ . Then we have $\langle \xi | ( H + V ) | \xi \rangle \leq \lambda _ { * }$ (since $| \xi \rangle \in \widetilde { \mathcal { L } } _ { - } \rangle$ ) and

$\langle \xi | H | \xi \rangle \geq \lambda _ { + }$ (since $| \xi \rangle \in { \mathcal { L } } _ { + }$ ). Hence $\langle \xi | V | \xi \rangle \leq \lambda _ { * } - \lambda _ { + } = - \Delta / 2$ . But this is impossible because $\| V \| < \Delta / 2$ .

Now, since $\widetilde { \mathcal { L } } _ { - } \cap \mathcal { L } _ { + } = \{ 0 \} ,$ , we have that $\Pi _ { - } | \xi \rangle \neq 0$ for all nonzero vectors $| \xi \rangle \in \widetilde { \mathcal { L } } _ { - }$ . From Eq. (11) we obtain

$$
\widetilde { G } _ { -- } = \Pi _ { - } \widetilde { G } \Pi _ { - } = \sum _ { j } ( z - \widetilde { \lambda } _ { j } ) ^ { - 1 } \Pi _ { - } | \widetilde { \psi } _ { j } \rangle \langle \widetilde { \psi } _ { j } | \Pi _ { - } .
$$

If the multiplicity of $\tilde { \lambda }$ is $m$ then the matrix $\sum \vert \widetilde { \psi _ { j } } \rangle \langle \widetilde { \psi _ { j } } \vert$ of the corresponding eigenvectors has rank $m$ . This implies that the matrix $\sum \Pi _ { - } | \widetilde { \psi } _ { j } \rangle \langle \widetilde { \psi } _ { j } | \Pi _ { - }$ also has rank $m$ . Indeed, if there is some linear combination of $\Pi _ { - } | \widetilde { \psi _ { j } } \rangle$ that sums to zero then taking the same linear combination of $| \widetilde { \psi _ { j } } \rangle$ must also sum to zero.

The next two lemmas relate the spectrum of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ to the operator $\Sigma _ { - } ( z )$ .

Lemma 6 For any $z < \lambda _ { * } ,$ , the multiplicity of $z$ as an eigenvalue of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ is equal to the multiplicity of $z$ as an eigenvalue of $\Sigma _ { - } ( z )$ .

Proof: Fix some $z < \lambda _ { * }$ and let $m$ be its multiplicity as an eigenvalue of $\widetilde { H }$ (in particular, $m = 0$ if $z$ is not an eigenvalue of $\widetilde { H }$ ). In the neighborhood of $z$ the function $\widetilde { G } _ { -- } ( w )$ has the form

$$
\widetilde { G } _ { -- } ( w ) = ( w - z ) ^ { - 1 } A + B + O \big ( | w - z | \big ) ,
$$

where by Lemma 5, $A$ is an operator of rank $m$ . We now consider $\widetilde { G } _ { -- } ^ { - 1 } ( w )$ . For any $w < \lambda _ { + } - \| V \|$ the norm of $G _ { + } ( w )$ is strictly less than $1 / \| V \|$ . Hence, by Eq. (12) we see that all the poles of $\Sigma _ { - } ( w )$ lie on the interval $\left[ \lambda _ { + } - \left\| V \right\| , + \infty \right) .$ ; in particular $\tilde { G } _ { -- } ^ { - 1 } \bar { ( w ) } = w I _ { - } - \Sigma _ { - } ( w )$ is analytic for $w \in ( - \infty , \lambda _ { * } ]$ . Hence we can write

$$
\widetilde { G } _ { -- } ^ { - 1 } ( w ) = w I _ { - } - \Sigma _ { - } ( w ) = C + D ( w - z ) + O \big ( | w - z | ^ { 2 } \big ) .
$$

We claim that the dimension of the null-space of $C$ is exactly $m$ . Notice that this implies that $z$ is an $m$ -fold eigenvalue of $\Sigma _ { - } ( z ) = z I _ { - } - C$ . By multiplying the two equations above, we obtain

$$
I _ { - } = \widetilde { G } _ { -- } ^ { - 1 } ( w ) \widetilde { G } _ { -- } ( w ) = ( w - z ) ^ { - 1 } C A + ( D A + C B ) + O ( | w - z | ) .
$$

By equating coefficients, we obtain $C A = 0$ and $D A + C B = I _ { - }$ . On one hand, $C A = 0$ implies that the null-space of $C$ has dimension at least $m$ . On the other hand, the rank of $D A$ is at most $\operatorname { r a n k } ( A ) = m$ . Since $I _ { - }$ has full rank, the dimension of the null-space of $C B$ must be at most $m$ . This implies that the dimension of the null-space of $C$ must also be at most $m$ .

We observe that the function $\Sigma _ { - } ( z )$ is monotone decreasing in the operator sense (i.e., if $z _ { 1 } \le z _ { 2 }$ then $\Sigma _ { - } ( z _ { 1 } ) - \Sigma _ { - } ( z _ { 2 } )$ is positive semidefinite):

$$
\begin{array} { l } { \displaystyle \frac { d \Sigma _ { - } ( z ) } { d z } = \frac { d } { d z } \Big ( H _ { - } + V _ { -- } + V _ { - + } ( z I _ { + } - H _ { + } - V _ { + + } ) ^ { - 1 } V _ { + - } \Big ) } \\ { \displaystyle ~ = - V _ { - + } ( z I _ { + } - H _ { + } - V _ { + + } ) ^ { - 2 } V _ { + - } \le 0 . } \end{array}
$$

Lemma 7 Let $\widetilde { \lambda } _ { j }$ be the jth eigenvalue of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ . Then it is also the jth eigenvalue of $\Sigma _ { - } ( \widetilde { \lambda } _ { j } )$ .

Proof: For any $z \in \mathbb { R } ,$ let $f _ { 1 } ( z )$ (resp., $f _ { 2 } ( z ) )$ be the number of eigenvalues not greater than $z$ of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ (resp., $\Sigma _ { - } ( z ) )$ . When $z  - \infty ,$ $f _ { 1 } ( z )$ is clearly 0. By the monotonicity of $\Sigma _ { - }$ we see that $f _ { 2 } ( z )$ is also 0. Using Lemma 6 we see that as $z$ increases, both numbers increase together by the same amount $m$ whenever $z$ hits an eigenvalue of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ of multiplicity $m$ (here we used again the monotonicity of $\Sigma _ { - }$ ). Hence, for all $z _ { \iota }$ $f _ { 1 } ( z ) = f _ { 2 } ( z )$ and the lemma is proven.

We can now complete the proof of the theorem. By Lemma 4 and our assumption on $H _ { \mathrm { e f f } } ,$ , we have that for any $z \in [ c - \varepsilon , d + \varepsilon ] .$ , $\mathrm { S p e c } \Sigma _ { - } ( z )$ is contained in $[ c - \varepsilon , d + \varepsilon ]$ . From this and the monotonicity of $\Sigma _ { - }$ , we obtain that there is no $z \in ( d + \varepsilon , \lambda _ { * } ]$ that is an eigenvalue of $\Sigma _ { - } ( z )$ . Similarly, there is no $z < c - \varepsilon$ that is an eigenvalue of $\Sigma _ { - } ( z )$ . Hence, using Lemma 6 we see that $\mathrm { S p e c } \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } }$ is contained in $[ c - \varepsilon , d + \varepsilon ]$ . Now let $\widetilde { \lambda } _ { j } \in \left[ c - \varepsilon , d + \varepsilon \right]$ be the $j$ th eigenvalue of $\smash { \widetilde { H } | _ { \widetilde { \mathcal { L } } _ { - } } }$ . By Lemma 7 it is also the $j$ th eigenvalue of $\Sigma _ { - } ( \widetilde { \lambda } _ { j } )$ . By Lemma 4 it is $\varepsilon$ -close to the $j$ th eigenvalue of $H _ { \mathrm { e f f } }$ .

# 6.2 The Three-Qubit Gadget

In this section we demonstrate how Theorem 3 can be used to transform a 3-local Hamiltonian into a 2-local one. The complete reduction will be shown in the next section. From now we try to keep the discussion more specialized to our QMA problem rather than presenting it in full generality as was done in Section 6.1.

Let $Y$ be some arbitrary 2-local Hamiltonian acting on a space $\mathcal { M }$ of $N$ qubits. Also, let $B _ { 1 } , B _ { 2 } , B _ { 3 }$ be positive semidefinite Hamiltonians each acting on a different qubit (so they commute). We think of these four operators as having constant norm. Assume we have the 3-local Hamiltonian

$$
Y - 6 B _ { 1 } B _ { 2 } B _ { 3 } .
$$

The factor 6 is added for convenience. Recall that in the LOCAL HAMILTONIAN problem we are interested in the lowest eigenvalue of a Hamiltonian. Hence, our goal is to find a 2-local Hamiltonian whose lowest eigenvalue is very close to the lowest eigenvalue of (13).

We start by adding three qubits to our system. For $j = 1 , 2 , 3 ,$ , we denote the Pauli operators acting on the $j$ th qubit by $\sigma _ { j } ^ { \alpha }$ . Let $\delta > 0$ be a sufficiently small constant. Our 2-local Hamiltonian is $\widetilde { H } = H + V ,$ , where

$$
\begin{array} { l } { { H = - \displaystyle \frac { \delta ^ { - 3 } } { 4 } I \otimes \left( \sigma _ { 1 } ^ { z } \sigma _ { 2 } ^ { z } + \sigma _ { 1 } ^ { z } \sigma _ { 3 } ^ { z } + \sigma _ { 2 } ^ { z } \sigma _ { 3 } ^ { z } - 3 I \right) } } \\ { { V = X \otimes I - \delta ^ { - 2 } \big ( B _ { 1 } \otimes \sigma _ { 1 } ^ { x } + B _ { 2 } \otimes \sigma _ { 2 } ^ { x } + B _ { 3 } \otimes \sigma _ { 3 } ^ { x } \big ) } } \\ { { X = Y + \delta ^ { - 1 } ( B _ { 1 } ^ { 2 } + B _ { 2 } ^ { 2 } + B _ { 3 } ^ { 2 } ) } } \end{array}
$$

The unperturbed Hamiltonian $H$ has eigenvalues 0 and $\Delta \ { \stackrel { d e f } { = } } \ \delta ^ { - 3 }$ . Associated with the zero eigenvalue is the subspace

$$
\mathcal { L } _ { - } = \mathcal { M } \otimes \mathcal { C } , \qquad \mathrm { w h e r e } \quad \mathcal { C } = \left( \left. 0 0 0 \right. , \left. 1 1 1 \right. \right) .
$$

In the orthogonal subspace $\mathcal { C } ^ { \perp }$ we have the states $\left| 0 0 1 \right.$ , $\left| 0 1 0 \right.$ , etc. We may think of the subspace $\mathcal { C }$ as an effective qubit (as opposed to the three physical qubits); the corresponding Pauli operators are denoted by $\sigma _ { \mathrm { e f f } } ^ { \alpha }$ .

To obtain $H _ { \mathrm { e f f } } .$ , we now compute the self-energy $\Sigma _ { - } ( z )$ using the power expansion in Eq. (12) up to the third order. There is no zeroth order term, i.e., $H _ { - } = 0$ . For the remaining terms, notice that $G _ { + } = ( z - \Delta ) ^ { - 1 } I _ { \mathcal { L } _ { + } }$ . Hence, we have

$$
\Sigma _ { - } ( z ) = V _ { -- } + ( z - \Delta ) ^ { - 1 } V _ { - + } V _ { + - } + ( z - \Delta ) ^ { - 2 } V _ { - + } V _ { + + } V _ { + - } + ( z - \Delta ) ^ { - 3 } V _ { - + } V _ { + + } V _ { + + }
$$

The first term is $V _ { -- } = X \otimes I _ { \mathcal { C } }$ because a $\sigma ^ { x }$ term takes any state in $\mathcal { C }$ to $\mathcal { C } ^ { \perp }$ . The expressions in the following terms are of the form

$$
\begin{array} { c } { { V _ { - + } = - \delta ^ { - 2 } \Big ( B _ { 1 } \otimes | 0 0 0 \rangle \langle 1 0 0 | + B _ { 2 } \otimes | 0 0 0 \rangle \langle 0 1 0 | + B _ { 3 } \otimes | 0 0 0 \rangle \langle 0 0 1 | + } } \\ { { \qquad B _ { 1 } \otimes | 1 1 1 \rangle \langle 0 1 1 | + B _ { 2 } \otimes | 1 1 1 \rangle \langle 1 0 1 | + B _ { 3 } \otimes | 1 1 1 \rangle \langle 1 1 0 | \Big ) } } \\ { { \qquad V _ { + + } = X \otimes I _ { \mathcal { C } ^ { \perp } } - \delta ^ { - 2 } \Big ( B _ { 1 } \otimes ( | 0 0 1 \rangle \langle 1 0 1 | + | 0 1 0 \rangle \langle 1 1 0 | + | 1 0 1 \rangle \langle 0 0 1 | + | 1 1 0 \rangle \langle 0 1 0 | ) + } } \\ { { \qquad B _ { 2 } \otimes ( \ldots ) + B _ { 3 } \otimes ( \ldots ) \Big ) , } } \end{array}
$$

where the dots denote similar terms for $B _ { 2 }$ and $B _ { 3 }$ . Now, in the second term of $\Sigma _ { - } ( z ) , V _ { + - }$ flips one of the physical qubits, and $V _ { - + }$ must return it to its original state in order to return to the space $\mathcal { C }$ . Hence we have $V _ { - + } V _ { + - } = \delta ^ { - 4 } ( B _ { 1 } ^ { 2 } + B _ { 2 } ^ { 2 } + B _ { 3 } ^ { 2 } ) \otimes I c$ . The third term is slightly more involved. Here we have two possible processes. In the first process, $V _ { + - }$ flips a qubit, $V _ { + + }$ acts with $X \otimes I _ { C ^ { \perp } } ,$ , and finally $V _ { - + }$ flips the qubit back. In the second process, $V _ { \mathrm { + - } } , V _ { \mathrm { + + } } ,$ and $V _ { - + }$ flip all three qubits in succession. Thus,

$$
\begin{array} { r l } & { \Sigma _ { - } ( z ) = X \otimes I _ { \mathcal { C } } + ( z - \Delta ) ^ { - 1 } \delta ^ { - 4 } ( B _ { 1 } ^ { 2 } + B _ { 2 } ^ { 2 } + B _ { 3 } ^ { 2 } ) \otimes I _ { \mathcal { C } } } \\ & { \quad + ( z - \Delta ) ^ { - 2 } \delta ^ { - 4 } ( B _ { 1 } X B _ { 1 } + B _ { 2 } X B _ { 2 } + B _ { 3 } X B _ { 3 } ) \otimes I _ { \mathcal { C } } } \\ & { \quad - ( z - \Delta ) ^ { - 2 } \delta ^ { - 6 } \big ( B _ { 3 } B _ { 2 } B _ { 1 } + B _ { 2 } B _ { 3 } B _ { 1 } + B _ { 3 } B _ { 1 } B _ { 2 } + B _ { 1 } B _ { 3 } B _ { 2 } + B _ { 2 } B _ { 1 } B _ { 3 } + B _ { 1 } B _ { 2 } B _ { 3 } \big ) } \\ & { \quad + O \big ( \| V \| ^ { 4 } ( z - \Delta ) ^ { - 3 } \big ) . } \end{array}
$$

We now focus on the range $z = O ( 1 ) \ll \Delta$ . In this range we have

$$
( z - \Delta ) ^ { - 1 } = - \frac { 1 } { \Delta } \Big ( 1 - \frac { z } { \Delta } \Big ) ^ { - 1 } = - \frac { 1 } { \Delta } + { \cal O } ( z / \Delta ^ { 2 } ) = - \delta ^ { 3 } + { \cal O } ( \delta ^ { 6 } ) .
$$

Simplifying, we obtain

$$
\Sigma _ { - } ( z ) = \underbrace { Y \otimes I _ { { \mathcal { C } } } \mathrm { ~ - ~ } 6 B _ { 1 } B _ { 2 } B _ { 3 } \otimes \sigma _ { \mathrm { e f f } } ^ { x } } _ { H _ { \mathrm { e f f } } } + O ( \delta ) .
$$

Notice that $\| H _ { \mathrm { e f f } } \| = O ( 1 )$ and hence we obtain that for all $z$ in, say, $[ - 2 \| H _ { \mathrm { e f f } } \| , 2 \| H _ { \mathrm { e f f } } \| ]$ we have

$$
\lVert \Sigma _ { - } ( z ) - H _ { \mathrm { e f f } } \rVert = O ( \delta ) .
$$

We may now apply Theorem 3 with $c = - \| H _ { \mathrm { e f f } } \| , d = \| H _ { \mathrm { e f f } } \| ,$ and $\lambda _ { * } = \Delta / 2$ to obtain the following result: Each eigenvalue $\widetilde { \lambda } _ { j }$ from the lower part of Spec $\widetilde { H }$ is $O ( \delta )$ -close to the $j$ -th eigenvalue of

$H _ { \mathrm { e f f } }$ . In fact, for our purposes, it is enough that the lowest eigenvalue of $\widetilde { H }$ is $O ( \delta )$ -close to the lowest eigenvalue of $H _ { \mathrm { e f f } }$ . It remains to notice that the spectrum of $H _ { \mathrm { e f f } }$ consists of two parts that correspond to the effective spin states $\begin{array} { r } { | + \rangle = \frac { 1 } { \sqrt { 2 } } \big ( | 0 \rangle + | 1 \rangle \big ) } \end{array}$ and $\begin{array} { r } { | - \rangle = \frac { 1 } { \sqrt { 2 } } \big ( | 0 \rangle - | 1 \rangle \big ) } \end{array}$ . Since $B _ { 1 } B _ { 2 } B _ { 3 }$ is positive semidefinite, the smallest eigenvalue is associated with $| + \rangle$ . Hence, the lowest eigenvalue of $\widetilde { H }$ is equal to the lowest eigenvalue of (13), as required.

6.3 Reduction from 3-LOCAL HAMILTONIAN to 2-LOCAL HAMILTONIAN

In this section we reduce the 3-LOCAL HAMILTONIAN problem to the 2-LOCAL HAMILTONIAN problem. By the QMA-completeness of the 3-LOCAL HAMILTONIAN problem [KR03], this establishes Theorem 1.

Theorem 4 There is a polynomial time reduction from the 3-LOCAL HAMILTONIAN problem to the 2- LOCAL HAMILTONIAN problem.

Proof: Recall that in the 3-LOCAL HAMILTONIAN problem (see Def. 3) we are given two constants $a$ and $b$ and a local Hamiltonian $\begin{array} { r } { H ^ { ( 3 ) } = \sum _ { j } H _ { j } } \end{array}$ such that each $H _ { j }$ is a 3-qubit term whose norm is at most poly $( n )$ . Our goal in this proof is to transform $H ^ { ( 3 ) }$ into a 2-local Hamiltonian $H ^ { ( 2 ) }$ whose lowest eigenvalue is close to that of $H ^ { ( 3 ) }$ . We do this in two steps. The first is a somewhat technical step where we bring $H ^ { ( 3 ) }$ into a convenient form. In the second step, we replace each 3-local term with 2-local terms by using the gadget construction of the previous section. Before we continue with the proof, let us mention that it is crucial that we apply the gadget construction to all 3-local terms simultaneously. If instead we tried to apply the gadget construction sequentially, we would end up with an exponential blowup in the norms (since each application of the three-qubit gadget increases the norm by a multiplicative factor).

Lemma 8 The 3-local Hamiltonian $H ^ { ( 3 ) }$ can be represented as

$$
H ^ { ( 3 ) } = c _ { r } \left( Y \mathrm { ~ - ~ } 6 \sum _ { m = 1 } ^ { M } B _ { m 1 } B _ { m 2 } B _ { m 3 } \right)
$$

where $Y$ is a 2-local Hamiltonian with $\| Y \| = O ( 1 / n ^ { 6 } ) .$ , $M = { \cal { O } } ( n ^ { 3 } ) .$ , each $B _ { m i }$ is a one-qubit term of norm $O ( 1 / n ^ { 3 } )$ that satisfies $\begin{array} { r } { B _ { m i } \geq \frac { 1 } { n ^ { 3 } } I , } \end{array}$ and $c _ { r }$ is a rescaling factor satisfying $1 \leq c _ { r } \leq \mathrm { p o l y } ( n )$ . 12

Proof: First, we can assume without loss of generality that each $H _ { j }$ acts on a different triple of qubits, and hence there are at most $n ^ { 3 }$ such terms. Recall that any 3-qubit Hermitian operator can be written as a linear combination with real coefficients of the basis elements $\sigma ^ { \alpha } \otimes \sigma ^ { \beta } \otimes \sigma ^ { \gamma }$ where each of $\sigma ^ { \alpha } , \sigma ^ { \beta } , \sigma ^ { \gamma }$ ranges over the four possible Pauli matrices $\{ I , \sigma ^ { x } , \sigma ^ { y } , \sigma ^ { z } \}$ . Hence, for $M = { \cal { O } } ( n ^ { 3 } ) .$ , we can write

$$
H ^ { ( 3 ) } = c _ { r } \left( - 6 \sum _ { m = 1 } ^ { M } c _ { m } \cdot \sigma ^ { m , \alpha } \otimes \sigma ^ { m , \beta } \otimes \sigma ^ { m , \gamma } \right) ,
$$

where each $\sigma ^ { m , \alpha }$ is a Pauli matrix acting on one of the qubits, and $c _ { r } \leq \mathrm { p o l y } ( n )$ is chosen to be large enough so that $\textstyle | c _ { m } | \leq { \frac { 1 } { n ^ { 9 } } }$ for all $m = 1 , \ldots , M$ .

We can now write

$$
\mathbf { \Psi } ^ { x } \otimes \sigma ^ { m , \beta } \otimes \sigma ^ { m , \gamma } = \underbrace { \left( \frac { 2 } { n ^ { 3 } } I + n ^ { 6 } c _ { m } \sigma ^ { m , \alpha } \right) } _ { B _ { m 1 } } \otimes \underbrace { \left( \frac { 2 } { n ^ { 3 } } I + \frac { 1 } { n ^ { 3 } } \sigma ^ { m , \beta } \right) } _ { B _ { m 2 } } \otimes \underbrace { \left( \frac { 2 } { n ^ { 3 } } I + \frac { 1 } { n ^ { 3 } } \sigma ^ { m , \gamma } \right) } _ { B _ { m 3 } } + D _ { n }
$$

where $D _ { m }$ is 2-local. Since $| c _ { m } | \leq 1 / n ^ { 9 }$ we have that $\begin{array} { r } { B _ { m i } \geq \frac { 1 } { n ^ { 3 } } I } \end{array}$ and $\| D _ { m } \| = O ( 1 / n ^ { 9 } )$ .

We now replace each term $- 6 B _ { m 1 } B _ { m 2 } B _ { m 3 }$ by a three-qubit gadget. More specifically, let $\delta$ be a sufficiently small inverse polynomial in $n$ to be chosen later. We consider the Hamiltonian $H ^ { ( 2 ) } =$ $c _ { r } { \widetilde { H } } , { \widetilde { H } } = { \widetilde { H } } + V ,$ , acting on a system of $n + 3 M$ qubits, where

$$
H = - \frac { \delta ^ { - 3 } } { 4 } \sum _ { m = 1 } ^ { M } I \otimes \left( \sigma _ { m 1 } ^ { z } \sigma _ { m 2 } ^ { z } + \sigma _ { m 1 } ^ { z } \sigma _ { m 3 } ^ { z } + \sigma _ { m 2 } ^ { z } \sigma _ { m 3 } ^ { z } - 3 I \right) ,
$$

$$
\begin{array} { r l } & { \displaystyle { V = Y \otimes I + \delta ^ { - 1 } \sum _ { m = 1 } ^ { M } ( B _ { m 1 } ^ { 2 } + B _ { m 2 } ^ { 2 } + B _ { m 3 } ^ { 2 } ) \otimes I } } \\ & { \qquad \displaystyle { - \delta ^ { - 2 } \sum _ { m = 1 } ^ { M } \left( B _ { m 1 } \otimes \sigma _ { m 1 } ^ { x } + B _ { m 2 } \otimes \sigma _ { m 2 } ^ { x } + B _ { m 3 } \otimes \sigma _ { m 3 } ^ { x } \right) } . } \end{array}
$$

As before, let $\Delta = \delta ^ { - 3 }$ be the spectral gap of $H$ . Notice that the spectrum of $H$ includes not only 0 and $\Delta ,$ , but also $2 \Delta , 3 \Delta , \dots , M \Delta$ . Associated with the zero eigenvalue is the subspace spanned by all the zero-subspaces of the gadgets. Using $\| B _ { m i } \| \le { \cal { O } } ( 1 / n ^ { 3 } )$ and $M = O ( n ^ { 3 } )$ we get $\| V \| = O ( \delta ^ { - 2 } ) < \Delta / 2$ .

The calculation of $\Sigma _ { - }$ is quite similar to the one-gadget case (cf. Eq. (14)). Each gadget contributes an independent term. Terms up to the third order can only include processes that involve one gadget. Indeed, in order to involve two gadgets, one has to flip a qubit from one gadget and from another gadget, and then flip both qubits back. Moreover, since only one gadget is involved, $G _ { + }$ can be replaced by $( z - \Delta ) ^ { - 1 } I _ { \mathcal { L } _ { + } }$ as before. From the fourth order onwards, processes start to include cross-terms between different gadgets. However, we claim that their contribution is only $O ( \delta )$ , as long as $| z | = O ( 1 )$ . Indeed, in this range, the eigenvalues of $G _ { + } .$ , which are $( z - \Delta ) ^ { - 1 } .$ , $( z - 2 \Delta ) ^ { - 1 } , . . . ,$ are all at most ${ \cal O } ( \delta ^ { 3 } )$ in absolute value while the norm of each of the $V$ terms is at most $O ( \delta ^ { - 2 } )$ . To summarize, for $| z | = O ( 1 )$ ,

$$
\Sigma _ { - } ( z ) = \underbrace { Y \otimes I _ { { \mathcal { C } } } \mathrm { ~ - ~ } 6 \sum _ { m = 1 } ^ { M } B _ { m 1 } B _ { m 2 } B _ { m 3 } \otimes \left( { \sigma } _ { m } ^ { x } \right) _ { \mathrm { e f f } } } _ { H _ { \mathrm { e f f } } } + O ( \delta ) .
$$

Since $\| H _ { \mathrm { e f f } } \| \le { \cal O } ( 1 ) ,$ , we can apply Theorem 3 with $c = - \| H _ { \mathrm { e f f } } \| , d = \| H _ { \mathrm { e f f } } \|$ and $\lambda _ { * } = \Delta / 2$ . We obtain that the smallest eigenvalue of $\widetilde { H }$ is $O ( \delta )$ -close to that of $H _ { \mathrm { e f f } }$ . The spectrum of $H _ { \mathrm { e f f } }$ consists of $2 ^ { M }$ parts, corresponding to subspaces spanned by setting each effective spin state to either $| + \rangle$ or $| - \rangle$ . Since $B _ { m 1 } B _ { m 2 } B _ { m 3 } \geq 0 ,$ the smallest eigenvalue of $H _ { \mathrm { e f f } }$ is achieved in the subspace where all effective spin states are in the $| + \rangle$ state. In this subspace, $H _ { \mathrm { e f f } }$ is identical to $H ^ { ( 3 ) } / c _ { r }$ . Hence, the smallest eigenvalue of $H ^ { ( 2 ) } = c _ { r } \widetilde { H }$ is $O ( c _ { r } \delta )$ -close to that of $H ^ { ( 3 ) }$ . We complete the proof by choosing $\delta = c ^ { \prime } / c _ { r }$ for some small enough constant $c ^ { \prime }$ .

# 7 2-local Universal Adiabatic Computation

In this section we show that adiabatic computation with 2-local Hamiltonians is equivalent to “standard” quantum computation in the circuit model. In order to prove such an equivalence, one has to show that each model can simulate the other. One direction is already known: it is not too hard to show that any polynomial time adiabatic computation can be efficiently simulated by a quantum circuit [FGGS00]. Hence, it remains to show that adiabatic computation with 2-local Hamiltonians can efficiently simulate any quantum circuit. In $[ \mathrm { A v K ^ { + } 0 4 } ]$ it is shown that adiabatic computation with 3-local Hamiltonians can efficiently simulate any quantum circuit. We obtain our result by combining their result with the techniques in our second proof.

Let us briefly mention the main ideas behind adiabatic computation. For more details see $[ \mathrm { A v K ^ { + } 0 4 } ]$ and references therein. In adiabatic computation, we consider a time-dependent Hamiltonian $H ( s )$ for $s \in [ 0 , 1 ]$ acting on a quantum system. We initialize the system in the groundstate of the initial Hamiltonian $H ( 0 )$ . This groundstate is required to be some simple quantum state that is easy to create. We then slowly modify the Hamiltonian from $s = 0$ to $s = 1$ . We say that the adiabatic computation is successful if the final state of the system is close to the groundstate of $H ( 1 )$ . The adiabatic theorem (see, e.g., [Rei04, AR04]) says that if the Hamiltonian is modified slowly enough, the adiabatic computation is successful. In other words, it gives an upper bound on the running time of an adiabatic computation. For our purposes, it is enough to know that this bound is polynomial if for any $s \in [ 0 , 1 ] .$ , the norm of $H ( s )$ , as well as that of its first and second derivatives, is bounded by a polynomial, and the spectral gap of $H ( s )$ is larger than some inverse polynomial.

In $[ \mathrm { A v K ^ { + } 0 4 } ]$ it is shown how to transform an arbitrary quantum circuit into an efficient 3- local adiabatic computation. To establish this, they define a 3-local time-dependent Hamiltonian $H ^ { ( 3 ) } ( s )$ with the following properties. First, the Hamiltonian acts on a system of $n$ qubits, where $n$ is some constant times the number of gates in the circuit. Second, the groundstate of $H ^ { ( 3 ) } ( 0 )$ is very easy to create (namely, it is the all zero state), and the groundstate of $H ^ { ( 3 ) } ( 1 )$ is some state that encodes the result of the quantum circuit. Third, for all $s \in [ 0 , 1 ] ,$ the spectral gap of $H ^ { ( 3 ) } ( s )$ is bounded from below by an inverse polynomial in $n$ and the norm of $H ^ { ( 3 ) } ( s ) _ { \cdot }$ , as well as that of its first and second derivatives, is bounded by some polynomial in $n$ . Together with the adiabatic theorem, these properties imply that adiabatic computation according to $H ^ { ( 3 ) } ( s )$ is efficient. Finally, let us mention that $H ^ { ( 3 ) } ( s )$ , as defined in $[ \mathrm { A v K ^ { + } 0 4 } ] ,$ , is linear in $s _ { \iota }$ , that is, $H ^ { ( 3 ) } ( s ) = ( 1 - s ) H ^ { ( 3 ) } ( 0 ) + s H ^ { ( 3 ) } ( 1 )$ . This property will be useful in our proof.

The following is the main theorem of this section.

Theorem 5 Any quantum computation can be efficiently simulated by an adiabatic computation with 2- local Hamiltonians.

Proof: Given a quantum circuit, let $H ^ { ( 3 ) } ( s )$ be the time-dependent Hamiltonian of $[ \mathrm { A v K ^ { + } 0 4 } ]$ as described above. The idea of the proof is to apply the gadget construction of Sec. 6.3 to $H ^ { ( 3 ) } ( s )$ for any $s \in [ 0 , 1 ] ,$ , thereby creating a 2-local time-dependent Hamiltonian $H ^ { ( 2 ) } ( s )$ . Some care needs to be taken to ensure that the resulting time-dependent Hamiltonian is smooth enough as a function of $s$ . We therefore describe how this is done in more detail.

We start by writing $H ^ { ( 3 ) } ( s )$ in a form similar to that given by Lemma 8. Since $H ^ { ( 3 ) } ( s )$ is linear

in $s$ , we can write

$$
H ^ { ( 3 ) } ( s ) = c _ { r } \left( - 6 \sum _ { m = 1 } ^ { M } c _ { m } ( s ) \cdot \sigma ^ { m , \alpha } \otimes \sigma ^ { m , \beta } \otimes \sigma ^ { m , \gamma } \right) ,
$$

where $M = O ( n ^ { 3 } )$ , each $c _ { m } ( s )$ is a linear function of $s ,$ and $c _ { r } \leq \mathrm { p o l y } ( n )$ is chosen to be large enough so that $\textstyle | c _ { m } ( s ) | \leq { \frac { 1 } { n ^ { 9 } } }$ for all $m$ and all $s \in [ 0 , 1 ]$ . Notice that $c _ { r }$ is a fixed scaling factor, used for all $s \in [ 0 , 1 ]$ . Following the proof of Lemma 8, we write

$$
H ^ { ( 3 ) } ( s ) = c _ { r } \left( Y ( s ) - 6 \sum _ { m = 1 } ^ { M } B _ { m 1 } ( s ) B _ { m 2 } B _ { m 3 } \right)
$$

where by our construction, $Y ( s )$ and $B _ { m 1 } ( s )$ are linear in $s$ , whereas $B _ { m 2 }$ and $B _ { m 3 }$ are independent of $s$ . Finally, we define $H ^ { ( 2 ) } ( s ) = c _ { r } \tilde { H } ( s ) ,$ , where ${ \tilde { H } } ( s ) = H + V ( s )$ and the Hamiltonians $H$ and $V ( s )$ are defined as in Eq. (15). The parameter $\delta$ will be chosen later to be some small enough inverse polynomial in $n$ .

In the rest of the proof, we show that adiabatic computation according to $H ^ { ( 2 ) } ( s )$ can be used to simulate the given quantum circuit. We start by proving two lemmas that, together with the adiabatic theorem, imply that the running time of the adiabatic computation is polynomial in $n$ .

Lemma 9 For any $\begin{array} { r } { s \in [ 0 , 1 ] , \| H ^ { ( 2 ) } ( s ) \| , \| \frac { d } { d s } H ^ { ( 2 ) } ( s ) \| , } \end{array}$ and $\textstyle { \big \| } { \frac { d ^ { 2 } } { d s ^ { 2 } } } H ^ { ( 2 ) } ( s ) \big \|$ are upper bounded by a polynomial in $n$ .

Proof: Recall that $Y ( s )$ and $B _ { m 1 } ( s )$ are linear in $s$ . Together with the definition of $H ^ { ( 2 ) }$ , this implies that $H ^ { ( 2 ) } ( s )$ is a degree two polynomial in $s ,$ i.e., we can write $H ^ { ( 2 ) } ( s ) = A + s B + s ^ { 2 } C$ for some Hermitian matrices $A , B , C$ . It is not hard to see that the norm of each of these matrices is bounded by some polynomial in $n$ . This implies that the norm of $H ^ { ( 2 ) } ( s )$ , of its first derivative $B + 2 s C$ , and of its second derivative $2 C$ are bounded by some polynomial in $n$ .

Lemma 10 For any $s \in [ 0 , 1 ] .$ , the spectral gap of $H ^ { ( 2 ) } ( s )$ is lower bounded by an inverse polynomial in $n$

Proof: As shown in Sec. 6.3, the lower part of the spectrum of $H ^ { ( 2 ) } ( s )$ is $O ( c _ { r } \delta )$ -close to the spectrum of $c _ { r } H _ { \mathrm { e f f } } ( s )$ . Hence, by choosing $\delta$ to be a small enough inverse polynomial in $n ,$ we see that it is enough to show that the spectral gap of $c _ { r } H _ { \mathrm { e f f } } ( s )$ is at least some inverse polynomial in $n$ .

The spectrum of $c _ { r } H _ { \mathrm { e f f } } ( s )$ consists of $2 ^ { M }$ parts, corresponding to all possible settings for the effective qubits. The part corresponding to the subspace in which all effective qubits are in the $| + \rangle$ state is identical to the spectrum of $H ^ { ( 3 ) } ( s )$ . Hence, we know that in this subspace the spectral gap is at least some inverse polynomial in $n$ . We now claim that the lowest eigenvalue in all other $2 ^ { M } -$ 1 subspaces is greater than that in the all $| + \rangle$ subspace by at least some inverse polynomial in $n$ . Indeed, the restriction of $c _ { r } H _ { \mathrm { e f f } } ( s )$ to any such subspace is given by $H ^ { ( 3 ) } ( s )$ plus a nonzero number of terms of the form $1 2 c _ { r } B _ { m 1 } ( s ) B _ { m 2 } B _ { m 3 }$ . The claim follows from the fact that $B _ { m 1 } ( s ) B _ { m 2 } B _ { m 3 } \geq$ $\scriptstyle { \frac { 1 } { n ^ { 9 } } } I$ . •

To complete the proof, we need to argue about the groundstate of $H ^ { ( 2 ) } ( 0 )$ and that of $H ^ { ( 2 ) } ( 1 )$ . To this end, we use the following lemma, which essentially says that if $H _ { \mathrm { e f f } }$ has a spectral gap, then Theorem 3 not only implies closeness in spectra but also in the groundstates.

Lemma 11 Assume that $H , V , H _ { \mathrm { e f f } }$ satisfy the conditions of Theorem 3 with some $\varepsilon > 0$ . Let $\lambda _ { \mathrm { e f f } , i }$ denote the ith eigenvalue of $H _ { \mathrm { e f f } }$ and $| \widetilde v \rangle$ (resp., $| v _ { \mathrm { e f f } } \rangle _ { \mathrm { . } }$ ) denote the groundstate of $\widetilde { H }$ (resp., $H _ { \mathrm { e f f } } ,$ ). Then, under the assumption $\lambda _ { \mathrm { e f f } , 2 } > \lambda _ { \mathrm { e f f } , 1 } ,$

$$
| \langle \widetilde { v } | v _ { \mathrm { e f f } } \rangle | \geq 1 - \frac { 2 \| V \| ^ { 2 } } { ( \lambda _ { + } - \lambda _ { \mathrm { e f f } , 1 } - \varepsilon ) ^ { 2 } } - \frac { 4 \varepsilon } { \lambda _ { \mathrm { e f f } , 2 } - \lambda _ { \mathrm { e f f } , 1 } } .
$$

Before we prove the lemma, let us complete the proof of the theorem. Recall that in our case $\varepsilon = O ( \delta ) , \| V \| = O ( \delta ^ { - 2 } ) , \lambda _ { + } = \delta ^ { - 3 }$ , $| \lambda _ { \mathrm { e f f } , 1 } | \le { \cal O } ( 1 )$ and $\lambda _ { \mathrm { e f f } , 2 } - \lambda _ { \mathrm { e f f } , 1 } = 1 / \mathrm { p o l y } ( n )$ . Hence, the first error term in the above bound is $O ( \delta ^ { 2 } )$ while the second is $O ( \delta \cdot \mathrm { p o l y } ( n ) )$ . Therefore, by choosing $\delta$ to be a small enough inverse polynomial in $n ,$ we can guarantee that the groundstate of $H ^ { ( 2 ) } ( s )$ is close to the groundstate of $H _ { \mathrm { e f f } } ( s )$ . In particular, the groundstate of $H ^ { ( 2 ) } ( 1 )$ , which is the output of the adiabatic computation, is close to the groundstate of $H _ { \mathrm { e f f } } ( 1 )$ . The latter is $| v _ { 1 } \rangle \otimes | + \rangle ^ { \otimes M } .$ , where $\left| v _ { 1 } \right.$ is the groundstate of $H ^ { ( 3 ) } ( 1 )$ . By simply tracing out the $3 M$ gadget qubits, we can recover $\left| v _ { 1 } \right.$ from this groundstate, and therefore obtain the output of the quantum circuit. Similarly, the groundstate of $H ^ { ( 2 ) } ( 0 )$ , which is the state to which the system should be initialized, is close to the groundstate of $H _ { \mathrm { e f f } } ( 0 )$ . The latter is $\left| v _ { 0 } \right. \otimes \left| + \right. ^ { \otimes M } ,$ where $\left| v _ { 0 } \right.$ is the groundstate of $H ^ { ( 3 ) } ( 0 )$ . We therefore initialize the system by setting the original $n$ qubits to $\left| v _ { 0 } \right.$ and the $M$ gadgets to the effective $| + \rangle$ state. This state is close to the groundstate of $H ^ { ( 2 ) } ( 0 )$ , and since the adiabatic computation is unitary, this approximation does not affect the output by much.

It remains to prove the lemma.

Proof of Lemma 11: Let $| \widetilde { v } _ { - } \rangle = \Pi _ { - } | \widetilde { v } \rangle / \Vert \Pi _ { - } | \widetilde { v } \rangle \Vert$ be the normalized projection of $| \widetilde v \rangle$ on the space $\mathcal { L } _ { - }$ . We first show that $| \widetilde { v } _ { - } \rangle$ is close to $| \widetilde v \rangle$ . By Theorem 3, we know that $\widetilde { \lambda } _ { 1 } \leq \lambda _ { \mathrm { e f f } , 1 } + \varepsilon$ . Hence,

$$
\| \Pi _ { + } \widetilde H | \widetilde v \rangle \| = \widetilde \lambda _ { 1 } \| \Pi _ { + } | \widetilde v \rangle \| \le ( \lambda _ { \mathrm { e f f } , 1 } + \varepsilon ) \| \Pi _ { + } | \widetilde v \rangle \|
$$

and

$$
\| \Pi _ { + } \widetilde { H } | \widetilde { v } \rangle \| = \| \Pi _ { + } H | \widetilde { v } \rangle + \Pi _ { + } V | \widetilde { v } \rangle \| \ge \| \Pi _ { + } H | \widetilde { v } \rangle \| - \| V \| \ge \lambda _ { + } \| \Pi _ { + } | \widetilde { v } \rangle \| - \| V \| .
$$

By combining the two inequalities we obtain

$$
\| \Pi _ { + } | \widetilde { v } \rangle \| \leq \frac { \| V \| } { \lambda _ { + } - \lambda _ { \mathrm { e f f } , 1 } - \varepsilon } ,
$$

from which we see that

$$
\alpha \overset { d e f } { = } | \langle \widetilde { v } | \widetilde { v } _ { - } \rangle | = \| \Pi _ { - } | \widetilde { v } \rangle \| \geq \| \Pi _ { - } | \widetilde { v } \rangle \| ^ { 2 } \geq 1 - \frac { \| V \| ^ { 2 } } { ( \lambda _ { + } - \lambda _ { \mathrm { e f f } , 1 } - \varepsilon ) ^ { 2 } } .
$$

Our next step is to show that $| \widetilde { v } _ { - } \rangle$ is close to $| v _ { \mathrm { e f f } } \rangle$ . For this we need to consider the proof of Theorem 3. We start by taking Lemma 5 with $\widetilde { \lambda } = \widetilde { \lambda } _ { 1 }$ . The lemma says that $A$ is a matrix of rank 1. By looking at the proof, it is easy to see that $A$ is in fact $\Pi _ { - } | \widetilde { v } \rangle \langle \widetilde { v } | \Pi _ { - }$ . Next, Lemma 6 implies that $\widetilde { \lambda } _ { 1 }$ is an eigenvalue of multiplicity 1 of $\Sigma _ { - } ( \widetilde { \lambda } _ { 1 } )$ . In fact, from the proof it follows that the corresponding eigenvector is exactly $\Pi _ { - } | \widetilde { v } \rangle$ (since the null space of $C$ is equal to the span of $A$ ). By normalizing, this is exactly $| \widetilde { v } _ { - } \rangle$ . But by our assumption, $\| \Sigma _ { - } ( z ) - H _ { \mathrm { e f f } } \| \le \varepsilon$ for all $z \in [ c - \varepsilon , d + \varepsilon ]$ and in particular

$$
\| \Sigma _ { - } ( \widetilde { \lambda } _ { 1 } ) - H _ { \mathrm { e f f } } \| \le \varepsilon .
$$

From this we obtain that

$$
\big | \langle \widetilde { v } _ { - } | ( \Sigma _ { - } ( \widetilde { \lambda } _ { 1 } ) - H _ { \mathrm { e f f } } ) | \widetilde { v } _ { - } \rangle \big | \le \varepsilon
$$

and hence

$$
\langle \widetilde { v } _ { - } | H _ { \mathrm { e f f } } | \widetilde { v } _ { - } \rangle \le \widetilde { \lambda } _ { 1 } + \varepsilon \le \lambda _ { \mathrm { e f f } , 1 } + 2 \varepsilon
$$

where we again used that $\begin{array} { r } { \widetilde { \lambda } _ { 1 } \leq \lambda _ { \mathrm { e f f } , 1 } + \varepsilon . } \end{array}$ . Since $H _ { \mathrm { e f f } }$ has a spectral gap, this indicates that $| \widetilde { v } _ { - } \rangle$ must be close to $| v _ { \mathrm { e f f } } \rangle$ . Indeed, let $\beta = | \langle \widetilde { v } _ { - } | v _ { \mathrm { e f f } } \rangle |$ . Then,

$$
\langle \widetilde v _ { - } | H _ { \mathrm { e f f } } | \widetilde v _ { - } \rangle \ge \beta ^ { 2 } \lambda _ { \mathrm { e f f } , 1 } + ( 1 - \beta ^ { 2 } ) \lambda _ { \mathrm { e f f } , 2 } = \lambda _ { \mathrm { e f f } , 1 } + ( 1 - \beta ^ { 2 } ) ( \lambda _ { \mathrm { e f f } , 2 } - \lambda _ { \mathrm { e f f , 1 } } ) .
$$

By combining the two inequalities we obtain

$$
1 - \beta ^ { 2 } \leq \frac { 2 \varepsilon } { \lambda _ { \mathrm { e f f } , 2 } - \lambda _ { \mathrm { e f f } , 1 } } .
$$

Summarizing,

$$
\begin{array} { r l r } {  { | \langle \widetilde { v } | v _ { \mathrm { e f f } } \rangle | = | \langle \widetilde { v } | \widetilde { v } _ { - } \rangle \langle \widetilde { v } _ { - } | v _ { \mathrm { e f f } } \rangle + \langle \widetilde { v } | ( I - | \widetilde { v } _ { - } \rangle \langle \widetilde { v } _ { - } | ) | v _ { \mathrm { e f f } } \rangle | } } \\ & { } & { \ge \alpha \cdot \beta - \sqrt { ( 1 - \alpha ^ { 2 } ) ( 1 - \beta ^ { 2 } ) } \ge \alpha \cdot \beta - \frac 1 2 \big ( ( 1 - \alpha ^ { 2 } ) + ( 1 - \beta ^ { 2 } ) \big ) } \\ & { } & { \ge \big ( 1 - ( 1 - \alpha ) - ( 1 - \beta ) \big ) - \big ( ( 1 - \alpha ) + ( 1 - \beta ) \big ) = 1 - 2 ( 1 - \alpha ) - 2 ( 1 - \beta ) } \\ & { } & { \ge 1 - \frac { 2 \| V \| ^ { 2 } } { { \big ( } \lambda _ { + } - \lambda _ { \mathrm { e f f } , 1 } - \varepsilon { \big ) } ^ { 2 } } - \frac { 4 \varepsilon } { \lambda _ { \mathrm { e f f } , 2 } - \lambda _ { \mathrm { e f f } , 1 } } . } \end{array}
$$

# 8 Conclusion

Some interesting open questions remain. First, perturbation theory has allowed us to perform the first reduction inside QMA. What other problems can be solved using this technique? Second, there exists an intriguing class between NP (in fact, MA) and QMA known as QCMA. It is the class of problems that can be verified by a quantum verifier with a classical proof. Can one show a separation between QCMA and QMA? or perhaps show they are equal? Third, Kitaev’s original 5- local proof has the following desirable property. For any YES instance produced by the reduction there exists a state such that each individual 5-local term is very close to its groundstate. Note that this is a stronger property than the one required in the LOCAL HAMILTONIAN problem. Using a slight modification of Kitaev’s original construction, one can show a reduction to the 4-LOCAL HAMILTONIAN problem that has the same property. However, we do not know if this property can be achieved for the 3-local or the 2-local problem.

# Acknowledgments

Discussions with Sergey Bravyi and Frank Verstraete are gratefully acknowledged. JK is supported by ACI S´ecurit´e Informatique, 2003-n24, projet “R´eseaux Quantiques”, ACI-CR 2002-40 and EU 5th framework program RESQ IST-2001-37559, and by DARPA and Air Force Laboratory, Air Force Materiel Command, USAF, under agreement number F30602-01-2-0524, and by DARPA and the Office of Naval Research under grant number FDN-00014-01-1-0826 and during a visit supported in part by the National Science Foundation under grant EIA-0086038 through the Institute for Quantum Information at the California Institute of Technology. AK is supported in part by the National Science Foundation under grant EIA-0086038. OR is supported by an Alon Fellowship, the Binational Science Foundation, the Israel Science Foundation, and the Army Research Office grant DAAD19-03-1-0082. Part of this work was carried out during a visit of OR at LRI, Universit´e de Paris-Sud and he thanks his hosts for their hospitality and acknowledges partial support by ACI S´ecurit´e Informatique, 2003-n24, projet “R´eseaux Quantiques”.

# References

[AGD75] A. A. Abrikosov, L. P. Gorkov, and I. E. Dzyaloshinski. Methods of quantum field theory in statistical physics. Dover Publications Inc., New York, 1975.   
[AN02] D. Aharonov and T. Naveh. Quantum NP - a survey, 2002. quant-ph/0210077.   
[AR04] A. Ambainis and O. Regev. An elementary proof of the adiabatic theorem, 2004. quant-ph/0411152.   
$[ \mathrm { A v K ^ { + } 0 4 } ]$ D. Aharonov, W. van Dam, J. Kempe, Z. Landau, S. Lloyd, and O. Regev. Adiabatic quantum computation is equivalent to standard quantum computation. In Proc. 45th FOCS, pages 42–51, 2004.   
[BBC+95] D. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin, and H. Weinfurter. Elementary gates for quantum computation. Phys. Rev. A, 52:3457–3467, 1995.   
[Bha97] R. Bhatia. Matrix Analysis. Number 169 in Graduate Texts in Mathematics. Springer-Verlag, New York, 1997.   
[BV05] S. Bravyi and M. Vyalyi. Commutative version of the k-local Hamiltonian problem and non-triviality check for quantum codes. Quantum Information $\mathcal { E }$ Computation, 5(3):187– 215, 2005.   
[FGGS00] E. Farhi, J. Goldstone, S. Gutmann, and M. Sipser. Quantum computation by adiabatic evolution, 2000. quant-ph/0001106.   
[JWB03] D. Janzing, P. Wocjan, and T. Beth. Identity check is QMA-complete, 2003. quant-ph/0305050.   
[KKR04] J. Kempe, A. Kitaev, and O. Regev. The complexity of the local hamiltonian problem. In Proc. of 24th FSTTCS, pages 372–383, 2004. quant-ph/0406180.   
[Kni96] E. Knill. Quantum randomness and nondeterminism, 1996. quant-ph/9610012.   
[KR03] J. Kempe and O. Regev. 3-local Hamiltonian is QMA-complete. Quantum Information & Computation, 3(3):258–264, 2003.   
[KSV02] A. Yu. Kitaev, A. H. Shen, and M. N. Vyalyi. Classical and quantum computation, volume 47 of Graduate Studies in Mathematics. AMS, Providence, RI, 2002.   
[MW04] C. Marriott and J. Watrous. Quantum Arthur-Merlin games. In Proc. of 19th IEEE Annual Conference on Computational Complexity (CCC), 2004.   
[NC00] M.A. Nielsen and I.L. Chuang. Quantum Computation and Quantum Information. Cambridge University Press, Cambridge, UK, 2000.   
[OT05] R. Oliveira and B. Terhal. The complexity of quantum spin systems on a twodimensional square lattice, 2005. quant-ph/0504050.   
[Pap94] C. Papadimitriou. Computational Complexity. Addison Wesley, Reading, Massachusetts, 1994.   
[Rei04] B. Reichardt. The quantum adiabatic optimization algorithm and local minima. In Proc. of 36th STOC, pages 502–510, 2004.   
[Rud91] W. Rudin. Functional analysis. International Series in Pure and Applied Mathematics. McGraw-Hill Inc., New York, second edition, 1991.   
[Wat00] J. Watrous. Succinct quantum proofs for properties of finite groups. In Proc. 41st FOCS, pages 537–546, 2000.   
[WB03] P. Wocjan and T. Beth. The 2-local Hamiltonian problem encompasses NP. International J. of Quantum Info., 1(3):349–357, 2003.